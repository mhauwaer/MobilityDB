  /***********************************************************************
 *
 * This MobilityDB code is provided under The PostgreSQL License.
 * Copyright (c) 2016-2022, Université libre de Bruxelles and MobilityDB
 * contributors
 *
 * MobilityDB includes portions of PostGIS version 3 source code released
 * under the GNU General Public License (GPLv2 or later).
 * Copyright (c) 2001-2022, PostGIS contributors
 *
 * Permission to use, copy, modify, and distribute this software and its
 * documentation for any purpose, without fee, and without a written
 * agreement is hereby granted, provided that the above copyright notice and
 * this paragraph and the following two paragraphs appear in all copies.
 *
 * IN NO EVENT SHALL UNIVERSITE LIBRE DE BRUXELLES BE LIABLE TO ANY PARTY FOR
 * DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING
 * LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION,
 * EVEN IF UNIVERSITE LIBRE DE BRUXELLES HAS BEEN ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * UNIVERSITE LIBRE DE BRUXELLES SPECIFICALLY DISCLAIMS ANY WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS ON
 * AN "AS IS" BASIS, AND UNIVERSITE LIBRE DE BRUXELLES HAS NO OBLIGATIONS TO
 * PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS. 
 *
 *****************************************************************************/

/**
 * @brief Analytic functions for temporal points and temporal floats.
 */

#include "point/tpoint_analytics.h"

/* C */
#include <assert.h>
#include <float.h>
#include <math.h>
#include <limits.h>
/* PostgreSQL */
// #include <utils/float.h>
// #include <utils/timestamp.h>
/* PostGIS */
#include <liblwgeom_internal.h>
#include <lwgeodetic_tree.h>
/* MobilityDB */
#include <meos.h>
#include <meos_internal.h>
#include "general/lifting.h"
#include "point/geography_funcs.h"
#include "point/tpoint.h"
#include "point/tpoint_boxops.h"
#include "point/tpoint_spatialrels.h"
#include "point/tpoint_spatialfuncs.h"

/* Timestamps in PostgreSQL are encoded as MICROseconds since '2000-01-01'
 * while Unix epoch are encoded as MILLIseconds since '1970-01-01'.
 * Therefore the value used for conversions is computed as follows
 * select date_part('epoch', timestamp '2000-01-01' - timestamp '1970-01-01')
 * which results in 946684800 */
#define DELTA_UNIX_POSTGRES_EPOCH 946684800

/*****************************************************************************
 * Convert a temporal point into a PostGIS geometry/geography where the M
 * coordinates are
 * - either given in the second parameter
 * - or encode the timestamps of the temporal point in Unix epoch
 *****************************************************************************/

/**
 * Convert the geometry/geography point and the measure into a PostGIS point
 * with an M coordinate
 */
static LWPOINT *
point_measure_to_lwpoint(Datum point, Datum measure)
{
  GSERIALIZED *gs = DatumGetGserializedP(point);
  int32 srid = gserialized_get_srid(gs);
  double d = DatumGetFloat8(measure);
  LWPOINT *result;
  if (FLAGS_GET_Z(gs->gflags))
  {
    const POINT3DZ *point = gserialized_point3dz_p(gs);
    result = lwpoint_make4d(srid, point->x, point->y, point->z, d);
  }
  else
  {
    const POINT2D *point = gserialized_point2d_p(gs);
    result = lwpoint_make3dm(srid, point->x, point->y, d);
  }
  FLAGS_SET_GEODETIC(result->flags, FLAGS_GET_GEODETIC(gs->gflags));
  return result;
}

/**
 * Convert the temporal instant point into a PostGIS trajectory point
 * where the M coordinate encodes the timestamp in Unix epoch
 */
static LWPOINT *
tpointinst_to_lwpoint(const TInstant *inst)
{
  double epoch = ((double) inst->t / 1e6) + DELTA_UNIX_POSTGRES_EPOCH;
  return point_measure_to_lwpoint(tinstant_value(inst), Float8GetDatum(epoch));
}

/*****************************************************************************
 * Convert a temporal point into a LinestringM geometry/geography where the M
 * coordinates values are given by a temporal float.
 *****************************************************************************/

/**
 * Construct a geometry/geography with M measure from the temporal instant
 * point and the temporal float.
 *
 * @param[in] inst Temporal point
 * @param[in] measure Temporal float
 */
static Datum
tpointinst_to_geo_measure(const TInstant *inst, const TInstant *measure)
{
  LWPOINT *point = measure ?
    point_measure_to_lwpoint(tinstant_value(inst), tinstant_value(measure)) :
    tpointinst_to_lwpoint(inst);
  GSERIALIZED *result = geo_serialize((LWGEOM *) point);
  pfree(point);
  return PointerGetDatum(result);
}

/**
 * Construct a geometry/geography with M measure from the temporal instant set
 * point and the temporal float.
 *
 * @param[in] is Temporal point
 * @param[in] measure Temporal float
 */
static Datum
tpointinstset_to_geo_measure(const TInstantSet *is, const TInstantSet *measure)
{
  LWGEOM **points = palloc(sizeof(LWGEOM *) * is->count);
  for (int i = 0; i < is->count; i++)
  {
    const TInstant *inst = tinstantset_inst_n(is, i);
    if (measure)
    {
      const TInstant *m = tinstantset_inst_n(measure, i);
      points[i] = (LWGEOM *) point_measure_to_lwpoint(tinstant_value(inst),
          tinstant_value(m));
    }
    else
      points[i] = (LWGEOM *) tpointinst_to_lwpoint(inst);
  }
  GSERIALIZED *result;
  if (is->count == 1)
    result = geo_serialize(points[0]);
  else
  {
    LWGEOM *mpoint = (LWGEOM *) lwcollection_construct(MULTIPOINTTYPE,
      points[0]->srid, NULL, (uint32_t) is->count, points);
    result = geo_serialize(mpoint);
    pfree(mpoint);
  }
  for (int i = 0; i < is->count; i++)
    lwgeom_free (points[i]);
  pfree(points);
  return PointerGetDatum(result);
}

/**
 * Construct a geometry/geography with M measure from the temporal sequence
 * point and the temporal float. The function removes one point if two
 * consecutive points are equal
 *
 * @param[in] seq Temporal point
 * @param[in] measure Temporal float
 * @pre The temporal point and the measure are synchronized
 */
static LWGEOM *
tpointseq_to_geo_measure1(const TSequence *seq, const TSequence *measure)
{
  LWPOINT **points = palloc(sizeof(LWPOINT *) * seq->count);
  /* Remove two consecutive points if they are equal */
  const TInstant *inst = tsequence_inst_n(seq, 0);
  const TInstant *m = tsequence_inst_n(measure, 0);
  LWPOINT *value1 = point_measure_to_lwpoint(tinstant_value(inst),
    tinstant_value(m));
  points[0] = value1;
  int k = 1;
  for (int i = 1; i < seq->count; i++)
  {
    inst = tsequence_inst_n(seq, i);
    m = tsequence_inst_n(measure, i);
    LWPOINT *value2 = point_measure_to_lwpoint(tinstant_value(inst),
      tinstant_value(m));
    /* Add point only if previous point is diffrent from the current one */
    if (lwpoint_same(value1, value2) != LW_TRUE)
      points[k++] = value2;
    value1 = value2;
  }
  LWGEOM *result;
  if (k == 1)
  {
    result = (LWGEOM *) points[0];
    pfree(points);
  }
  else
  {
    result = MOBDB_FLAGS_GET_LINEAR(seq->flags) ?
      (LWGEOM *) lwline_from_lwgeom_array(points[0]->srid, (uint32_t) k,
        (LWGEOM **) points) :
      (LWGEOM *) lwcollection_construct(MULTIPOINTTYPE,
        points[0]->srid, NULL, (uint32_t) k, (LWGEOM **) points);
    for (int i = 0; i < k; i++)
      lwpoint_free(points[i]);
    pfree(points);
  }
  return result;
}

/**
 * Converts the temporal sequence point into a PostGIS trajectory
 * geometry/geography where the M coordinates encode the timestamps in
 * Unix epoch
 */
static LWGEOM *
tpointseq_to_geo1(const TSequence *seq)
{
  LWGEOM **points = palloc(sizeof(LWGEOM *) * seq->count);
  for (int i = 0; i < seq->count; i++)
  {
    const TInstant *inst = tsequence_inst_n(seq, i);
    points[i] = (LWGEOM *) tpointinst_to_lwpoint(inst);
  }
  LWGEOM *result;
  if (seq->count == 1)
  {
    result = points[0];
    pfree(points);
  }
  else
  {
    if (MOBDB_FLAGS_GET_LINEAR(seq->flags))
      result = (LWGEOM *) lwline_from_lwgeom_array(points[0]->srid,
        (uint32_t) seq->count, points);
    else
      result = (LWGEOM *) lwcollection_construct(MULTIPOINTTYPE,
        points[0]->srid, NULL, (uint32_t) seq->count, points);
    for (int i = 0; i < seq->count; i++)
      lwpoint_free((LWPOINT *) points[i]);
    pfree(points);
  }
  return result;
}

/**
 * Construct a geometry/geography with M measure from the temporal sequence
 * point and the temporal float.
 *
 * @param[in] seq Temporal point
 * @param[in] measure Temporal float
 */
static Datum
tpointseq_to_geo_measure(const TSequence *seq, const TSequence *measure)
{
  LWGEOM *lwgeom = measure ?
    tpointseq_to_geo_measure1(seq, measure) : tpointseq_to_geo1(seq);
  GSERIALIZED *result = geo_serialize(lwgeom);
  return PointerGetDatum(result);
}

/**
 * Construct a geometry/geography with M measure from the temporal sequence
 * point and the temporal float.
 *
 * @param[in] ss Temporal point
 * @param[in] measure Temporal float
 */
static Datum
tpointseqset_to_geo_measure(const TSequenceSet *ss, const TSequenceSet *measure)
{
  const TSequence *seq;
  const TSequence *m = NULL;

  /* Instantaneous sequence */
  if (ss->count == 1)
  {
    seq = tsequenceset_seq_n(ss, 0);
    if (measure)
      m = tsequenceset_seq_n(measure, 0);
    return tpointseq_to_geo_measure(seq, m);
  }

  uint8_t colltype = 0;
  LWGEOM **geoms = palloc(sizeof(LWGEOM *) * ss->count);
  for (int i = 0; i < ss->count; i++)
  {
    seq = tsequenceset_seq_n(ss, i);
    if (measure)
    {
      m = tsequenceset_seq_n(measure, i);
      geoms[i] = tpointseq_to_geo_measure1(seq, m);
    }
    else
      geoms[i] = tpointseq_to_geo1(seq);
    /* If output type not initialized make geom type as output type */
    if (! colltype)
      colltype = (uint8_t) lwtype_get_collectiontype(geoms[i]->type);
    /* If geom type is not compatible with current output type make output
     * type a collection */
    else if (colltype != COLLECTIONTYPE &&
      lwtype_get_collectiontype(geoms[i]->type) != colltype)
      colltype = COLLECTIONTYPE;
  }
  // TODO add the bounding box instead of ask PostGIS to compute it again
  LWGEOM *coll = (LWGEOM *) lwcollection_construct((uint8_t) colltype,
    geoms[0]->srid, NULL, (uint32_t) ss->count, geoms);
  Datum result = PointerGetDatum(geo_serialize(coll));
  /* We cannot lwgeom_free(geoms[i] or lwgeom_free(coll) */
  pfree(geoms);
  return result;
}

/*****************************************************************************/

/**
 * Construct a geometry/geography with M measure from the temporal sequence
 * point and the temporal float.
 *
 * Version that produces a Multilinestring when each composing linestring
 * corresponds to a segment of the orginal temporal point.
 *
 * @param[in] seq Temporal point
 * @param[in] measure Temporal float
 * @param[out] result Array on which the pointers of the newly constructed
 * sequences are stored
 */
static int
tpointseq_to_geo_measure_segmentize1(const TSequence *seq,
  const TSequence *measure, LWGEOM **result)
{
  const TInstant *inst = tsequence_inst_n(seq, 0);
  const TInstant *m = tsequence_inst_n(measure, 0);
  LWPOINT *points[2];

  /* Instantaneous sequence */
  if (seq->count == 1)
  {
    result[0] = (LWGEOM *) point_measure_to_lwpoint(tinstant_value(inst),
      tinstant_value(m));
    return 1;
  }

  /* General case */
  for (int i = 0; i < seq->count - 1; i++)
  {
    points[0] = point_measure_to_lwpoint(tinstant_value(inst),
      tinstant_value(m));
    inst = tsequence_inst_n(seq, i + 1);
    points[1] = point_measure_to_lwpoint(tinstant_value(inst),
      tinstant_value(m));
    result[i] = (LWGEOM *) lwline_from_lwgeom_array(points[0]->srid, 2,
      (LWGEOM **) points);
    lwpoint_free(points[0]); lwpoint_free(points[1]);
    m = tsequence_inst_n(measure, i + 1);
  }
  return seq->count - 1;
}

/**
 * Converts the temporal sequence point into a PostGIS trajectory
 * geometry/geography where the M coordinates encode the timestamps in
 * Unix epoch
 *
 * Version when the resulting value is a MultiLinestring M, where each
 * component is a segment of two points.
 *
 * @param[in] seq Temporal point
 * @param[out] result Array on which the pointers of the newly constructed
 * sequences are stored
 */
static int
tpointseq_to_geo_segmentize1(const TSequence *seq, LWGEOM **result)
{
  const TInstant *inst = tsequence_inst_n(seq, 0);
  LWPOINT *points[2];

  /* Instantaneous sequence */
  if (seq->count == 1)
  {
    result[0] = (LWGEOM *) tpointinst_to_lwpoint(inst);
    return 1;
  }

  /* General case */
  for (int i = 0; i < seq->count - 1; i++)
  {
    points[0] = tpointinst_to_lwpoint(inst);
    inst = tsequence_inst_n(seq, i + 1);
    points[1] = tpointinst_to_lwpoint(inst);
    result[i] = (LWGEOM *) lwline_from_lwgeom_array(points[0]->srid, 2,
      (LWGEOM **) points);
    lwpoint_free(points[0]); lwpoint_free(points[1]);
  }
  return seq->count - 1;
}

/**
 * Construct a geometry/geography with M measure from the temporal sequence
 * point and the temporal float.
 *
 * Version that produces a Multilinestring when each composing linestring
 * corresponds to a segment of the orginal temporal point.
 */
static Datum
tpointseq_to_geo_measure_segmentize(const TSequence *seq,
  const TSequence *measure)
{
  int count = (seq->count == 1) ? 1 : seq->count - 1;
  LWGEOM **geoms = palloc(sizeof(LWGEOM *) * count);
  if (measure)
    tpointseq_to_geo_measure_segmentize1(seq, measure, geoms);
  else
    tpointseq_to_geo_segmentize1(seq, geoms);
  Datum result;
  /* Instantaneous sequence */
  if (seq->count == 1)
    result = PointerGetDatum(geo_serialize(geoms[0]));
  else
  {
    // TODO add the bounding box instead of ask PostGIS to compute it again
    LWGEOM *segcoll = (LWGEOM *) lwcollection_construct(MULTILINETYPE,
      geoms[0]->srid, NULL, (uint32_t)(seq->count - 1), geoms);
    result = PointerGetDatum(geo_serialize(segcoll));
  }
  for (int i = 0; i < count; i++)
    lwgeom_free(geoms[i]);
  pfree(geoms);
  return result;
}

/**
 * Construct a geometry/geography with M measure from the temporal sequence set
 * point and the temporal float.
 *
 * Version that produces a Multilinestring when each composing linestring
 * corresponds to a segment of the orginal temporal point.
 */
static Datum
tpointseqset_to_geo_measure_segmentize(const TSequenceSet *ss,
  const TSequenceSet *measure)
{
  const TSequence *seq, *m = NULL;

  /* Instantaneous sequence */
  if (ss->count == 1)
  {
    seq = tsequenceset_seq_n(ss, 0);
    if (measure)
      m = tsequenceset_seq_n(measure, 0);
    return tpointseq_to_geo_measure_segmentize(seq, m);
  }

  uint8_t colltype = 0;
  LWGEOM **geoms = palloc(sizeof(LWGEOM *) * ss->totalcount);
  int k = 0;
  for (int i = 0; i < ss->count; i++)
  {

    seq = tsequenceset_seq_n(ss, i);
    if (measure)
    {
      m = tsequenceset_seq_n(measure, i);
      k += tpointseq_to_geo_measure_segmentize1(seq, m, &geoms[k]);
    }
    else
      k += tpointseq_to_geo_segmentize1(seq, &geoms[k]);
    /* Output type not initialized */
    if (! colltype)
      colltype = (uint8_t) lwtype_get_collectiontype(geoms[k - 1]->type);
      /* Input type not compatible with output */
      /* make output type a collection */
    else if (colltype != COLLECTIONTYPE &&
         lwtype_get_collectiontype(geoms[k - 1]->type) != colltype)
      colltype = COLLECTIONTYPE;
  }
  Datum result;
  // TODO add the bounding box instead of ask PostGIS to compute it again
  LWGEOM *coll = (LWGEOM *) lwcollection_construct(colltype,
    geoms[0]->srid, NULL, (uint32_t) k, geoms);
  result = PointerGetDatum(geo_serialize(coll));
  for (int i = 0; i < k; i++)
    lwgeom_free(geoms[i]);
  pfree(geoms);
  return result;
}

/*****************************************************************************/

/**
 * @ingroup libmeos_temporal_analytics
 * @brief Construct a geometry/geography with M measure from the temporal
 * point and
 * - either the temporal float given in the second argument (if any)
 * - or the time information of the temporal point where the M coordinates
 *   encode the timestamps in number of seconds since '1970-01-01'
 * @sqlfunc geoMeasure() if the second argument is not NULL
 * @sqlop @p :: if the second argument is NULL
 */
bool
tpoint_to_geo_measure(const Temporal *tpoint, const Temporal *measure,
  bool segmentize, Datum *result)
{
  ensure_tgeo_type(tpoint->temptype);
  Temporal *sync1, *sync2;
  if (measure)
  {
    ensure_tnumber_type(measure->temptype);
    /* Return false if the temporal values do not intersect in time
     * The operation is synchronization without adding crossings */
    if (! intersection_temporal_temporal(tpoint, measure, SYNCHRONIZE_NOCROSS,
        &sync1, &sync2))
      return false;
  }
  else
  {
    sync1 = (Temporal *) tpoint;
    sync2 = NULL;
  }

  ensure_valid_tempsubtype(sync1->subtype);
  if (sync1->subtype == TINSTANT)
    *result = tpointinst_to_geo_measure(
      (TInstant *) sync1, (TInstant *) sync2);
  else if (sync1->subtype == TINSTANTSET)
    *result = tpointinstset_to_geo_measure(
      (TInstantSet *) sync1, (TInstantSet *) sync2);
  else if (sync1->subtype == TSEQUENCE)
    *result = segmentize ?
      tpointseq_to_geo_measure_segmentize(
        (TSequence *) sync1, (TSequence *) sync2) :
      tpointseq_to_geo_measure(
        (TSequence *) sync1, (TSequence *) sync2);
  else /* sync1->subtype == TSEQUENCESET */
    *result = segmentize ?
      tpointseqset_to_geo_measure_segmentize(
        (TSequenceSet *) sync1, (TSequenceSet *) sync2) :
      tpointseqset_to_geo_measure(
        (TSequenceSet *) sync1, (TSequenceSet *) sync2);

  if (measure)
  {
    pfree(sync1); pfree(sync2);
  }
  return true;
}

/*****************************************************************************
 * Convert trajectory geometry/geography where the M coordinates encode the
 * timestamps in Unix epoch into a temporal point.
 *****************************************************************************/

/**
 * Converts the PostGIS trajectory geometry/geography where the M coordinates
 * encode the timestamps in Unix epoch into a temporal instant point.
 */
static TInstant *
trajpoint_to_tpointinst(LWPOINT *lwpoint)
{
  bool hasz = (bool) FLAGS_GET_Z(lwpoint->flags);
  bool geodetic = (bool) FLAGS_GET_GEODETIC(lwpoint->flags);
  LWPOINT *lwpoint1;
  TimestampTz t;
  if (hasz)
  {
    POINT4D point = getPoint4d(lwpoint->point, 0);
    t = (TimestampTz) ((point.m - DELTA_UNIX_POSTGRES_EPOCH) * 1e6);
    lwpoint1 = lwpoint_make3dz(lwpoint->srid, point.x, point.y, point.z);
  }
  else
  {
    POINT3DM point = getPoint3dm(lwpoint->point, 0);
    t = (TimestampTz) ((point.m - DELTA_UNIX_POSTGRES_EPOCH) * 1e6);
    lwpoint1 = lwpoint_make2d(lwpoint->srid, point.x, point.y);
  }
  FLAGS_SET_GEODETIC(lwpoint1->flags, geodetic);
  GSERIALIZED *gs = geo_serialize((LWGEOM *) lwpoint1);
  mobdbType temptype = geodetic ? T_TGEOGPOINT : T_TGEOMPOINT;
  TInstant *result = tinstant_make(PointerGetDatum(gs), temptype, t);
  pfree(gs);
  return result;
}

/**
 * Converts the PostGIS trajectory geometry/geography where the M coordinates
 * encode the timestamps in Unix epoch into a temporal instant point.
 */
static TInstant *
geo_to_tpointinst(const GSERIALIZED *geo)
{
  /* Geometry is a POINT */
  LWGEOM *lwgeom = lwgeom_from_gserialized(geo);
  TInstant *result = trajpoint_to_tpointinst((LWPOINT *) lwgeom);
  lwgeom_free(lwgeom);
  return result;
}

/**
 * Converts the PostGIS trajectory geometry/geography where the M coordinates
 * encode the timestamps in Unix epoch into a temporal instant set point.
 */
static TInstantSet *
geo_to_tpointinstset(const GSERIALIZED *geo)
{
  /* Geometry is a MULTIPOINT */
  LWGEOM *lwgeom = lwgeom_from_gserialized(geo);
  bool hasz = (bool) FLAGS_GET_Z(geo->gflags);
  /* Verify that is a valid set of trajectory points */
  LWCOLLECTION *lwcoll = lwgeom_as_lwcollection(lwgeom);
  double m1 = -1 * DBL_MAX, m2;
  int npoints = lwcoll->ngeoms;
  for (int i = 0; i < npoints; i++)
  {
    LWPOINT *lwpoint = (LWPOINT *) lwcoll->geoms[i];
    if (hasz)
    {
      POINT4D point = getPoint4d(lwpoint->point, 0);
      m2 = point.m;
    }
    else
    {
      POINT3DM point = getPoint3dm(lwpoint->point, 0);
      m2 = point.m;
    }
    if (m1 >= m2)
    {
      lwgeom_free(lwgeom);
      elog(ERROR, "Trajectory must be valid");
    }
    m1 = m2;
  }
  TInstant **instants = palloc(sizeof(TInstant *) * npoints);
  for (int i = 0; i < npoints; i++)
    instants[i] = trajpoint_to_tpointinst((LWPOINT *) lwcoll->geoms[i]);
  lwgeom_free(lwgeom);

  return tinstantset_make_free(instants, npoints, MERGE_NO);
}

/**
 * Converts the PostGIS trajectory geometry/geography where the M coordinates
 * encode the timestamps in Unix epoch into a temporal sequence point.
 */
static TSequence *
geo_to_tpointseq(const GSERIALIZED *geo)
{
  /* Geometry is a LINESTRING */
  bool hasz = (bool) FLAGS_GET_Z(geo->gflags);
  LWGEOM *lwgeom = lwgeom_from_gserialized(geo);
  LWLINE *lwline = lwgeom_as_lwline(lwgeom);
  int npoints = lwline->points->npoints;
  /*
   * Verify that the trajectory is valid.
   * Since calling lwgeom_is_trajectory causes discrepancies with regression
   * tests because of the error message depends on PostGIS version,
   * the verification is made here.
   */
  double m1 = -1 * DBL_MAX, m2;
  for (int i = 0; i < npoints; i++)
  {
    if (hasz)
    {
      POINT4D point = getPoint4d(lwline->points, (uint32_t) i);
      m2 = point.m;
    }
    else
    {
      POINT3DM point = getPoint3dm(lwline->points, (uint32_t) i);
      m2 = point.m;
    }
    if (m1 >= m2)
    {
      lwgeom_free(lwgeom);
      elog(ERROR, "Trajectory must be valid");
    }
    m1 = m2;
  }
  TInstant **instants = palloc(sizeof(TInstant *) * npoints);
  for (int i = 0; i < npoints; i++)
  {
    /* Return freshly allocated LWPOINT */
    LWPOINT *lwpoint = lwline_get_lwpoint(lwline, (uint32_t) i);
    instants[i] = trajpoint_to_tpointinst(lwpoint);
    lwpoint_free(lwpoint);
  }
  lwgeom_free(lwgeom);
  /* The resulting sequence assumes linear interpolation */
  return tsequence_make_free(instants, npoints, true, true,
    LINEAR, NORMALIZE);
}

/**
 * Converts the PostGIS trajectory geometry/geography where the M coordinates
 * encode the timestamps in Unix epoch into a temporal sequence set point.
 */
static TSequenceSet *
geo_to_tpointseqset(const GSERIALIZED *geo)
{
  /* Geometry is a MULTILINESTRING or a COLLECTION composed of POINT and LINESTRING */
  LWGEOM *lwgeom = lwgeom_from_gserialized(geo);
  LWCOLLECTION *lwcoll = lwgeom_as_lwcollection(lwgeom);
  int ngeoms = lwcoll->ngeoms;
  for (int i = 0; i < ngeoms; i++)
  {
    LWGEOM *lwgeom1 = lwcoll->geoms[i];
    if (lwgeom1->type != POINTTYPE && lwgeom1->type != LINETYPE)
    {
      lwgeom_free(lwgeom);
      elog(ERROR, "Component geometry/geography must be of type Point(Z)M or Linestring(Z)M");
    }
  }

  TSequence **sequences = palloc(sizeof(TSequence *) * ngeoms);
  for (int i = 0; i < ngeoms; i++)
  {
    LWGEOM *lwgeom1 = lwcoll->geoms[i];
    GSERIALIZED *gs1 = geo_serialize(lwgeom1);
    if (lwgeom1->type == POINTTYPE)
    {
      TInstant *inst = geo_to_tpointinst(gs1);
      /* The resulting sequence assumes linear interpolation */
      sequences[i] = tinstant_to_tsequence(inst, LINEAR);
      pfree(inst);
    }
    else /* lwgeom1->type == LINETYPE */
      sequences[i] = geo_to_tpointseq(gs1);
    pfree(gs1);
  }
  lwgeom_free(lwgeom);
  /* The resulting sequence set assumes linear interpolation */
  return tsequenceset_make_free(sequences, ngeoms, NORMALIZE_NO);
}

/**
 * @ingroup libmeos_temporal_analytics
 * @brief Converts the PostGIS trajectory geometry/geography where the M
 * coordinates encode the timestamps in Unix epoch into a temporal point.
 * @sqlfunc tgeompoint(), tgeogpoint()
 * @sqlop @p ::
 */
Temporal *
geo_to_tpoint(const GSERIALIZED *geo)
{
  ensure_non_empty(geo);
  ensure_has_M_gs(geo);
  Temporal *result = NULL; /* Make compiler quiet */
  int geomtype = gserialized_get_type(geo);
  if (geomtype == POINTTYPE)
    result = (Temporal *) geo_to_tpointinst(geo);
  else if (geomtype == MULTIPOINTTYPE)
    result = (Temporal *) geo_to_tpointinstset(geo);
  else if (geomtype == LINETYPE)
    result = (Temporal *) geo_to_tpointseq(geo);
  else if (geomtype == MULTILINETYPE || geomtype == COLLECTIONTYPE)
    result = (Temporal *) geo_to_tpointseqset(geo);
  else
    elog(ERROR, "Invalid geometry type for trajectory");
  return result;
}

/***********************************************************************
 * Simple Douglas-Peucker-like value simplification for temporal floats.
 ***********************************************************************/

/**
 * Finds a split when simplifying the temporal sequence point using a
 * spatio-temporal extension of the Douglas-Peucker line simplification
 * algorithm.
 *
 * @param[in] seq Temporal sequence
 * @param[in] i1,i2 Indexes of the reference instants
 * @param[out] split Location of the split
 * @param[out] dist Distance at the split
 */
static void
tfloatseq_findsplit(const TSequence *seq, int i1, int i2, int *split,
  double *dist)
{
  *split = i1;
  *dist = -1;
  if (i1 + 1 >= i2)
    return;

  const TInstant *start = tsequence_inst_n(seq, i1);
  const TInstant *end = tsequence_inst_n(seq, i2);
  double value1 = DatumGetFloat8(tinstant_value(start));
  double value2 = DatumGetFloat8(tinstant_value(end));
  double duration2 = (double) (end->t - start->t);
  /* Loop for every instant between i1 and i2 */
  const TInstant *inst1 = start;
  for (int k = i1 + 1; k < i2; k++)
  {
    const TInstant *inst2 = tsequence_inst_n(seq, k);
    double value = DatumGetFloat8(tinstant_value(inst2));
    double duration1 = (double) (inst2->t - inst1->t);
    double ratio = duration1 / duration2;
    double value_interp = value1 + (value2 - value1) * ratio;
    double d = fabs(value - value_interp);
    if (d > *dist)
    {
      /* record the maximum */
      *split = k;
      *dist = d;
    }
  }
  return;
}

/**
 * Return a negative or a positive value depending on whether the first number
 * is less than or greater than the second one
 */
static int
int_cmp(const void *a, const void *b)
{
  /* casting pointer types */
  const int *ia = (const int *) a;
  const int *ib = (const int *) b;
  /* returns negative if b > a and positive if a > b */
  return *ia - *ib;
}

/***********************************************************************
 * Simple spatio-temporal Douglas-Peucker line simplification.
 * No checks are done to avoid introduction of self-intersections.
 * No topology relations are considered.
 ***********************************************************************/

#if 0 /* not used */
/**
 * Return the speed of the temporal point in the segment in units per second
 *
 * @param[in] inst1, inst2 Instants defining the segment
 * @param[in] func Distance function (2D, 3D, or geodetic)
 */
static double
tpointinst_speed(const TInstant *inst1, const TInstant *inst2,
  datum_func2 func)
{
  Datum value1 = tinstant_value(inst1);
  Datum value2 = tinstant_value(inst2);
  return datum_point_eq(value1, value2) ? 0 :
    DatumGetFloat8(func(value1, value2)) /
      ((double)(inst2->t - inst1->t) / 1000000);
}
#endif /* not used */

/**
 * Return the 2D distance between the points
 */
static double
dist2d_pt_pt(POINT2D *p1, POINT2D *p2)
{
  return hypot(p2->x - p1->x, p2->y - p1->y);
}

/**
 * Return the 3D distance between the points
 */
static double
dist3d_pt_pt(POINT3DZ *p1, POINT3DZ *p2)
{
  return hypot3d(p2->x - p1->x, p2->y - p1->y, p2->z - p1->z);
}

/**
 * Return the 2D distance between the point the segment
 *
 * @param[in] p Point
 * @param[in] A,B Points defining the segment
 * @see http://geomalgorithms.com/a02-_lines.html
 * @note Derived from the PostGIS function lw_dist2d_pt_seg in
 * file measures.c
 */
static double
dist2d_pt_seg(POINT2D *p, POINT2D *A, POINT2D *B)
{
  POINT2D c;
  double r;
  /* If start==end, then use pt distance */
  if (A->x == B->x && A->y == B->y)
    return dist2d_pt_pt(p, A);

  r = ( (p->x-A->x) * (B->x-A->x) + (p->y-A->y) * (B->y-A->y) ) /
      ( (B->x-A->x) * (B->x-A->x) + (B->y-A->y) * (B->y-A->y) );

  if (r < 0) /* If the first vertex A is closest to the point p */
    return dist2d_pt_pt(p, A);
  if (r > 1)  /* If the second vertex B is closest to the point p */
    return dist2d_pt_pt(p, B);

  /* else if the point p is closer to some point between a and b
  then we find that point and send it to dist2d_pt_pt */
  c.x = A->x + r * (B->x - A->x);
  c.y = A->y + r * (B->y - A->y);

  return dist2d_pt_pt(p, &c);
}

/**
 * Return the 3D distance between the point the segment
 *
 * @param[in] p Point
 * @param[in] A,B Points defining the segment
 * @note Derived from the PostGIS function lw_dist3d_pt_seg in file
 * measures3d.c
 * @see http://geomalgorithms.com/a02-_lines.html
 */
static double
dist3d_pt_seg(POINT3DZ *p, POINT3DZ *A, POINT3DZ *B)
{
  POINT3DZ c;
  double r;
  /* If start==end, then use pt distance */
  if (A->x == B->x && A->y == B->y && A->z == B->z)
    return dist3d_pt_pt(p, A);

  r = ( (p->x-A->x) * (B->x-A->x) + (p->y-A->y) * (B->y-A->y) +
        (p->z-A->z) * (B->z-A->z) ) /
      ( (B->x-A->x) * (B->x-A->x) + (B->y-A->y) * (B->y-A->y) +
        (B->z-A->z) * (B->z-A->z) );

  if (r < 0) /* If the first vertex A is closest to the point p */
    return dist3d_pt_pt(p, A);
  if (r > 1) /* If the second vertex B is closest to the point p */
    return dist3d_pt_pt(p, B);

  /* else if the point p is closer to some point between a and b
  then we find that point and send it to dist3d_pt_pt */
  c.x = A->x + r * (B->x - A->x);
  c.y = A->y + r * (B->y - A->y);
  c.z = A->z + r * (B->z - A->z);

  return dist3d_pt_pt(p, &c);
}

/**
 * Finds a split when simplifying the temporal sequence point using a
 * spatio-temporal extension of the Douglas-Peucker line simplification
 * algorithm.
 *
 * @param[in] seq Temporal sequence
 * @param[in] i1,i2 Indexes of the reference instants
 * @param[in] synchronized True when using the Synchronized Euclidean Distance
 * @param[out] split Location of the split
 * @param[out] dist Distance at the split
 */
static void
tpointseq_findsplit(const TSequence *seq, int i1, int i2, bool synchronized,
  int *split, double *dist)
{
  POINT2D p2k, p2_sync, p2a, p2b;
  POINT3DZ p3k, p3_sync, p3a, p3b;
  Datum value;
  bool linear = MOBDB_FLAGS_GET_LINEAR(seq->flags);
  bool hasz = MOBDB_FLAGS_GET_Z(seq->flags);
  double d = -1;
  *split = i1;
  *dist = -1;
  if (i1 + 1 >= i2)
    return;

  /* Initialization of values wrt instants i1 and i2 */
  const TInstant *start = tsequence_inst_n(seq, i1);
  const TInstant *end = tsequence_inst_n(seq, i2);
  if (hasz)
  {
    p3a = datum_point3dz(tinstant_value(start));
    p3b = datum_point3dz(tinstant_value(end));
  }
  else
  {
    p2a = datum_point2d(tinstant_value(start));
    p2b = datum_point2d(tinstant_value(end));
  }

  /* Loop for every instant between i1 and i2 */
  for (int k = i1 + 1; k < i2; k++)
  {
    double d_tmp;
    const TInstant *inst = tsequence_inst_n(seq, k);
    if (hasz)
    {
      p3k = datum_point3dz(tinstant_value(inst));
      if (synchronized)
      {
        value = tsegment_value_at_timestamp(start, end, linear, inst->t);
        p3_sync = datum_point3dz(value);
        d_tmp = dist3d_pt_pt(&p3k, &p3_sync);
        pfree(DatumGetPointer(value));
      }
      else
        d_tmp = dist3d_pt_seg(&p3k, &p3a, &p3b);
    }
    else
    {
      p2k = datum_point2d(tinstant_value(inst));
      if (synchronized)
      {
        value = tsegment_value_at_timestamp(start, end, linear, inst->t);
        p2_sync = datum_point2d(value);
        d_tmp = dist2d_pt_pt(&p2k, &p2_sync);
        pfree(DatumGetPointer(value));
      }
      else
        d_tmp = dist2d_pt_seg(&p2k, &p2a, &p2b);
    }
    if (d_tmp > d)
    {
      /* record the maximum */
      d = d_tmp;
      *split = k;
    }
  }
  *dist = d;
  return;
}

/*****************************************************************************/

static TSequence *
tsequence_simplify(const TSequence *seq, bool synchronized, double eps_dist,
  uint32_t minpts)
{
  static size_t stack_size = 256;
  int *stack, *outlist; /* recursion stack */
  int stack_static[stack_size];
  int outlist_static[stack_size];
  int sp = -1; /* recursion stack pointer */
  int i1, split;
  uint32_t outn = 0;
  uint32_t i;
  double dist;

  assert(seq->temptype == T_TFLOAT || tgeo_type(seq->temptype));
  /* Do not try to simplify really short things */
  if (seq->count < 3)
    return tsequence_copy(seq);

  /* Only heap allocate book-keeping arrays if necessary */
  if ((unsigned int) seq->count > stack_size)
  {
    stack = palloc(sizeof(int) * seq->count);
    outlist = palloc(sizeof(int) * seq->count);
  }
  else
  {
    stack = stack_static;
    outlist = outlist_static;
  }

  i1 = 0;
  stack[++sp] = seq->count - 1;
  /* Add first point to output list */
  outlist[outn++] = 0;
  do
  {
    if (seq->temptype == T_TFLOAT)
      /* There is no synchronized distance for temporal floats */
      tfloatseq_findsplit(seq, i1, stack[sp], &split, &dist);
    else /* tgeo_type(seq->temptype) */
      tpointseq_findsplit(seq, i1, stack[sp], synchronized, &split, &dist);
    bool dosplit = (dist >= 0 &&
      (dist > eps_dist || outn + sp + 1 < minpts));
    if (dosplit)
      stack[++sp] = split;
    else
    {
      outlist[outn++] = stack[sp];
      i1 = stack[sp--];
    }
  }
  while (sp >= 0);

  /* Put list of retained points into order */
  qsort(outlist, outn, sizeof(int), int_cmp);
  /* Create new TSequence */
  const TInstant **instants = palloc(sizeof(TInstant *) * outn);
  for (i = 0; i < outn; i++)
    instants[i] = tsequence_inst_n(seq, outlist[i]);
  TSequence *result = tsequence_make((const TInstant **) instants, outn,
    seq->period.lower_inc, seq->period.upper_inc,
    MOBDB_FLAGS_GET_LINEAR(seq->flags), NORMALIZE);
  pfree(instants);

  /* Only free if arrays are on heap */
  if (stack != stack_static)
    pfree(stack);
  if (outlist != outlist_static)
    pfree(outlist);

  return result;
}

/**
 * Simplify the temporal sequence set float/point using a spatio-temporal
 * extension of the Douglas-Peucker line simplification algorithm.
 *
 * @param[in] ss Temporal point
 * @param[in] eps_dist Epsilon speed
 * @param[in] minpts Minimum number of points
 */
static TSequenceSet *
tsequenceset_simplify(const TSequenceSet *ss, bool synchronized,
  double eps_dist, uint32_t minpts)
{
  TSequence **sequences = palloc(sizeof(TSequence *) * ss->count);
  for (int i = 0; i < ss->count; i++)
  {
    const TSequence *seq = tsequenceset_seq_n(ss, i);
    sequences[i] = tsequence_simplify(seq, synchronized, eps_dist, minpts);
  }
  return tsequenceset_make_free(sequences, ss->count, NORMALIZE);
}

/**
 * @ingroup libmeos_temporal_analytics
 * @brief Simplify the temporal float/point using a spatio-temporal
 * extension of the Douglas-Peucker line simplification algorithm.
 * @sqlfunc simplify()
 */
Temporal *
temporal_simplify(const Temporal *temp, bool synchronized, double eps_dist)
{
  Temporal *result;
  ensure_valid_tempsubtype(temp->subtype);
  if (temp->subtype == TINSTANT || temp->subtype == TINSTANTSET ||
    ! MOBDB_FLAGS_GET_LINEAR(temp->flags))
    result = temporal_copy(temp);
  else if (temp->subtype == TSEQUENCE)
    result = (Temporal *) tsequence_simplify((TSequence *) temp, synchronized,
      eps_dist, 2);
  else /* temp->subtype == TSEQUENCESET */
    result = (Temporal *) tsequenceset_simplify((TSequenceSet *) temp,
      synchronized, eps_dist, 2);
  return result;
}

extern ArrayType *temporalarr_to_array(const Temporal **temporal, int count);

/**
 * Convert radians to degrees.
 * @param radian The radian
 * @return The degree
 */
double to_degrees(double radian) {
  return  radian * 180.0/M_PI;
}

/**
 * Convert degrees to radians.
 * @param degree The degree
 * @return The radian
 */
double to_radians(double degree) {
  return degree * M_PI/180;
}

/**
 * Compute the bearing from the first point to the second on a sphere.
 * @param p1 The first point
 * @param p2 The second point
 * @return The bearing
 */
double bearing(POINT2D p1, POINT2D p2) {
  double lon1 = p1.x, lat1 = p1.y, lon2 = p2.x, lat2 = p2.y;

  lon1 = to_radians(lon1);
  lat1 = to_radians(lat1);
  lon2 = to_radians(lon2);
  lat2 = to_radians(lat2);

  double x = sin(lon2-lon1) * cos(lat2);
  double y = cos(lat1) * sin(lat2) - sin(lat1) * cos(lat2) * cos(lon2-lon1);

  double b = atan2(y, x);

  return fmod(to_degrees(b) + 360, 360);
}

/**
 * Compute the shortest distance between two points on a sphere.
 * @param p1 The first point
 * @param p2 The second point
 * @return The distance
 */
double haversine_distance(POINT2D p1, POINT2D p2) {

  double lon1 = p1.x, lat1 = p1.y, lon2 = p2.x, lat2 = p2.y;
  // convert decimal degrees to radians
  lon1 = to_radians(lon1);
  lat1 = to_radians(lat1);
  lon2 = to_radians(lon2);
  lat2 = to_radians(lat2);

  // haversine formula
  double delta_lon = lon2 - lon1;
  double delta_lat = lat2 - lat1;
  double a = pow(sin(delta_lat / 2.0), 2) + cos(lat1) * cos(lat2) * pow(sin(delta_lon / 2.0), 2);
  double c = 2 * asin(sqrt(a));

  double earth_radius = 6378137.0;  //# Meters
  return c * earth_radius;
}

/**
 * Compute the point located in the middle of a great circle path between two points on a sphere.
 * @param p1 The first point
 * @param p2 The second point
 * @return The computed point
 */
POINT2D midpoint(POINT2D p1, POINT2D p2) {
  double lon1 = p1.x, lat1 = p1.y, lon2 = p2.x, lat2 = p2.y;
  lon1 = to_radians(lon1);
  lat1 = to_radians(lat1);
  lon2 = to_radians(lon2);
  lat2 = to_radians(lat2);

  double bx = cos(lat2) * cos(lon2 - lon1);
  double by = cos(lat2) * sin(lon2 - lon1);


  double lat3 = atan2(sin(lat1) + sin(lat2), sqrt(pow(cos(lat1) + bx, 2) + pow(by,2)));
  double lon3 = lon1 + atan2(by, cos(lat1) + bx);

  POINT2D point = {.x=to_degrees(lon3), .y=to_degrees(lat3)};

  return point;
}

/**
 * Compute the linear regression extrapolation.
 * @param trajectory The trajectory
 * @param i The index of the point in the middle of the window
 * @param mid The length of the window divided by two
 * @param point The point obtained from the extrapolation
 * @param t The time of the point in the middle of the window
 */
void
linear_regression_extrapolation(const TSequence *trajectory, int i, int mid, POINT2D *point, int t) {
  double sumx=0, sumx2=0, sumy=0, sumxy=0;

  for (int j=i; j < i+mid; j++) {
      double x = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, j))).x;
      int y = tsequence_inst_n(trajectory, j)->t;
      sumx += x;
      sumx2 += pow(x, 2);
      sumy += y;
      sumxy += x * y;
  }
  double b = (mid*sumxy-sumx*sumy)/(mid*sumx2-sumx*sumx);
  double a = (sumy - b*sumx)/mid;

  point->x = a + b * t;

  sumx=0, sumx2=0, sumy=0, sumxy=0;

  for (int j=i; j < i+mid; j++) {
      double x = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, j))).y;
      int y = tsequence_inst_n(trajectory, j)->t;
      sumx += x;
      sumx2 += pow(x, 2);
      sumy += y;
      sumxy += x * y;
  }
  b = (mid*sumxy-sumx*sumy)/(mid*sumx2-sumx*sumx);
  a = (sumy - b*sumx)/mid;

  point->y = a + b * t;
}

/**
 * Compute the forward and backward linear regression extrapolation.
 * @param trajectory The trajectory
 * @param i The index of the point in the middle of the window
 * @param mid The length of the window divided by two
 * @param PF The point obtained from the forward extrapolation
 * @param PB The point obtained from the backward extrapolation
 */
void
linear_regression_interpolation(const TSequence *trajectory, int i, int mid, POINT2D *PF, POINT2D *PB) {
    linear_regression_extrapolation(trajectory, i-mid, mid, PF, tsequence_inst_n(trajectory, i)->t);
    linear_regression_extrapolation(trajectory, i+1, mid, PB, tsequence_inst_n(trajectory, i)->t);
}

/**
 * Compute the forward and backward kinematic extrapolation.
 * @param trajectory The trajectory
 * @param i The index of the point in the middle of the window
 * @param PF The point obtained from the forward extrapolation
 * @param PB The point obtained from the backward extrapolation
 */
void
kinematic_interpolation(const TSequence *trajectory, int i, POINT2D *PF, POINT2D *PB) {
    POINT2D p_0 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i-3))), p_1 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i-2))), p_2 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i-1)));
    int t_0 = tsequence_inst_n(trajectory, i-3)->t, t_1 = tsequence_inst_n(trajectory, i-2)->t, t_2 = tsequence_inst_n(trajectory, i-1)->t, t_i = tsequence_inst_n(trajectory, i)->t;
    double v_x_1 = (p_1.x - p_0.x)/(t_1 - t_0), v_x_2 = (p_2.x - p_1.x)/(t_2 - t_1);
    double v_y_1 = (p_1.y - p_0.y)/(t_1 - t_0), v_y_2 = (p_2.y - p_1.y)/(t_2 - t_1);
    double a_x = (v_x_2 - v_x_1) / (t_2 - t_1);
    double a_y = (v_y_2 - v_y_1) / (t_2 - t_1);

    double x_i = (1/2 * a_x * pow(t_i-t_2, 2)) + (v_x_2 * (t_i-t_2)) + p_2.x;
    double y_i = (1/2 * a_y * pow(t_i-t_2, 2)) + (v_y_2 * (t_i-t_2)) + p_2.y;

    PF->x = x_i;
    PF->y = y_i;


    p_0 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i+3))), p_1 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i+2))), p_2 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i+1)));
    t_0 = tsequence_inst_n(trajectory, i+3)->t, t_1 = tsequence_inst_n(trajectory, i+2)->t, t_2 = tsequence_inst_n(trajectory, i+1)->t;
    v_x_1 = (p_1.x - p_0.x) / abs(t_1 - t_0), v_x_2 = (p_2.x - p_1.x) / abs(t_2 - t_1);
    v_y_1 = (p_1.y - p_0.y) / abs(t_1 - t_0), v_y_2 = (p_2.y - p_1.y) / abs(t_2 - t_1);
    a_x = (v_x_2 - v_x_1) / abs(t_2 - t_1);
    a_y = (v_y_2 - v_y_1) / abs(t_2 - t_1);

    x_i = (1/2 * a_x * pow(abs(t_i-t_2), 2)) + (v_x_2 * abs(t_i-t_2)) + p_2.x;
    y_i = (1/2 * a_y * pow(abs(t_i-t_2), 2)) + (v_y_2 * abs(t_i-t_2)) + p_2.y;

    PB->x = x_i;
    PB->y = y_i;
}

/**
 * Generate the error signal.
 * @param trajectory The trajectory
 * @param windows_length THe length of the window
 * @param kernel The kernel
 * @return The error signal
 */
double *
generate_error_signal(const TSequence *trajectory, int windows_length, char kernel) {
    int n = trajectory->count;
    double *errorSignal = palloc(sizeof(double) * n);
    assert(errorSignal);

    int mid = windows_length/2;
    for (int i = 0; i < mid; i++) {errorSignal[i] = 0.0;}

    for (int i = mid; i < n-mid; i++) {
        POINT2D PF, PB, PC;

        switch (kernel) {
            case 'K': assert(mid >= 3); kinematic_interpolation(trajectory, i, &PF, &PB); break;
            case 'L':
            default: linear_regression_interpolation(trajectory, i, mid, &PF, &PB); break;
        }

        PC = midpoint(PF, PB);

        double error = haversine_distance(PC, datum_point2d(tinstant_value(tsequence_inst_n(trajectory,i))));

        errorSignal[i] = error;
    }

    for (int i = 0; i < mid; i++) {errorSignal[n-i-1] = 0.0;}

    return errorSignal;
}

/**
 * Structure which contains the indices of the points at which the trajectory should be segmented.
 */
struct Segmentation {
      unsigned int *indices; // Array of indices
      unsigned int length;   // Length of the array
  };

/**
 * Compute the segmentation with the error signal and the threshold.
 * @param segmentation The segmentation
 * @param error_signal The error signal
 * @param threshold The threshold
 * @param n The length of the trajectory
 */
void
segment_with_sws(struct Segmentation *segmentation, double *error_signal, double threshold, unsigned int n) {
    segmentation->indices = palloc(sizeof(unsigned int)*n);
    assert(segmentation->indices);
    segmentation->length = 0;

    for (unsigned int i = 1; i < n; i++) {
        if (error_signal[i] > threshold) {
            segmentation->indices[segmentation->length] = i;
            segmentation->length++;
        }
    }
    segmentation->indices[segmentation->length] = n-1;
    segmentation->length++;
}

/**
 * Generate the array of sub-trajectories from the computed segmentation.
 * @param trajectory The trajectory
 * @param segmentation The segmentation
 * @return An array of sub-trajectories
 */
ArrayType *
generate_sub_trajectories(const TSequence *trajectory, struct Segmentation *segmentation) {
    unsigned start = 0;
    unsigned end = 0;

    Temporal **sub_trajectories = palloc(sizeof(Temporal*) * segmentation->length);
    assert(sub_trajectories);

    for (unsigned int i = 0; i < segmentation->length; i++) {
        end = segmentation->indices[i];

        TInstant **instants = palloc(sizeof(TInstant*) * (end-start+1));
        assert(instants);

        for (unsigned int j = 0; j < (end-start+1); j++) {
            instants[j] = (TInstant*) tsequence_inst_n(trajectory, start + j);
        }
        sub_trajectories[i] = (Temporal *) tsequence_make((const TInstant **) instants, end-start+1,
                                                          trajectory->period.lower_inc, trajectory->period.upper_inc, true, NORMALIZE);
        pfree(instants);

        start = end;
    }

    ArrayType *result = temporalarr_to_array((const Temporal**)sub_trajectories, segmentation->length);
    pfree(sub_trajectories);
    return result;
}

/**
 * Execute the Sliding Window Segmentation algorithm with a threshold.
 * @param temp The trajectory
 * @param threshold The threshold
 * @param windows_length The length of the window
 * @param kernel The kernel
 * @return An array of sub-trajectories
 */
ArrayType *
temporal_segmentation_sws_threshold(const Temporal *temp, double threshold, unsigned int windows_length, char kernel) {
    const TSequence *trajectory = (TSequence *) temp;

    unsigned int length = trajectory->count;

    if (length < windows_length) {
        return temporalarr_to_array(&temp, 1);
    }

    double *error_signal = generate_error_signal(trajectory, windows_length, kernel);

    struct Segmentation segmentation;
    segment_with_sws(&segmentation, error_signal, threshold, length);

    ArrayType *result = generate_sub_trajectories(trajectory, &segmentation);

    pfree(error_signal);
    pfree(segmentation.indices);

    return result;
}

/**/

/* RED BLACK TREE*/
// Implementation of red black trees taken from:
// https://github.com/prasanthmadhavan/Red-Black-Tree

  enum rbtree_node_color { RED, BLACK };

  typedef struct rbtree_node_t {
      void* key;
      struct rbtree_node_t* left;
      struct rbtree_node_t* right;
      struct rbtree_node_t* parent;
      enum rbtree_node_color color;
  } *rbtree_node;

  typedef struct rbtree_t {
      rbtree_node root;
  } *rbtree;

  typedef int (*compare_func)(void* left, void* right);

  rbtree rbtree_create();
  void* rbtree_lookup(rbtree t, void* key, compare_func compare);
  void rbtree_insert(rbtree t, void* key, compare_func compare);
  void rbtree_delete(rbtree t, void* key, compare_func compare);
  typedef rbtree_node node;
  typedef enum rbtree_node_color color;


  static node grandparent(node n);
  static node sibling(node n);
  static node uncle(node n);
  static color node_color(node n);

  static node new_node(void* key, color node_color, node left, node right);
  static node lookup_node(rbtree t, void* key, compare_func compare);
  static void rotate_left(rbtree t, node n);
  static void rotate_right(rbtree t, node n);

  static void replace_node(rbtree t, node oldn, node newn);
  static void insert_case1(rbtree t, node n);
  static void insert_case2(rbtree t, node n);
  static void insert_case3(rbtree t, node n);
  static void insert_case4(rbtree t, node n);
  static void insert_case5(rbtree t, node n);
  static node maximum_node(node root);
  static void delete_case1(rbtree t, node n);
  static void delete_case2(rbtree t, node n);
  static void delete_case3(rbtree t, node n);
  static void delete_case4(rbtree t, node n);
  static void delete_case5(rbtree t, node n);
  static void delete_case6(rbtree t, node n);


  node grandparent(node n) {
      assert (n != NULL);
      assert (n->parent != NULL);
      assert (n->parent->parent != NULL);
      return n->parent->parent;
  }

  node sibling(node n) {
      assert (n != NULL);
      assert (n->parent != NULL);
      if (n == n->parent->left)
          return n->parent->right;
      else
          return n->parent->left;
  }

  node uncle(node n) {
      assert (n != NULL);
      assert (n->parent != NULL);
      assert (n->parent->parent != NULL);
      return sibling(n->parent);
  }

  color node_color(node n) {
      return n == NULL ? BLACK : n->color;
  }


  rbtree rbtree_create() {
      rbtree t = palloc(sizeof(struct rbtree_t));
      t->root = NULL;
      return t;
  }

  node new_node(void* key , color node_color, node left, node right) {
      node result = palloc(sizeof(struct rbtree_node_t));
      assert(result);
      result->key = key;
      result->color = node_color;
      result->left = left;
      result->right = right;
      if (left  != NULL)  left->parent = result;
      if (right != NULL) right->parent = result;
      result->parent = NULL;
      return result;
  }

  node lookup_node(rbtree t, void* key, compare_func compare) {
      node n = t->root;
      while (n != NULL) {
          int comp_result = compare(key, n->key);
          if (comp_result == 0) {
              return n;
          } else if (comp_result < 0) {
              n = n->left;
          } else {
              assert(comp_result > 0);
              n = n->right;
          }
      }
      return n;
  }

  void* rbtree_lookup(rbtree t, void* key, compare_func compare) {
      node n = lookup_node(t, key, compare);
      return n == NULL ? NULL : n->key;
  }

  void rotate_left(rbtree t, node n) {
      node r = n->right;
      replace_node(t, n, r);
      n->right = r->left;
      if (r->left != NULL) {
          r->left->parent = n;
      }
      r->left = n;
      n->parent = r;
  }

  void rotate_right(rbtree t, node n) {
      node L = n->left;
      replace_node(t, n, L);
      n->left = L->right;
      if (L->right != NULL) {
          L->right->parent = n;
      }
      L->right = n;
      n->parent = L;
  }

  void replace_node(rbtree t, node oldn, node newn) {
      if (oldn->parent == NULL) {
          t->root = newn;
      } else {
          if (oldn == oldn->parent->left)
              oldn->parent->left = newn;
          else
              oldn->parent->right = newn;
      }
      if (newn != NULL) {
          newn->parent = oldn->parent;
      }
  }

  void rbtree_insert(rbtree t, void* key, compare_func compare) {
      node inserted_node = new_node(key, RED, NULL, NULL);
      if (t->root == NULL) {
          t->root = inserted_node;
      } else {
          node n = t->root;
          while (1) {
              int comp_result = compare(key, n->key);
              if (comp_result <= 0) {
                  if (n->left == NULL) {
                      n->left = inserted_node;
                      break;
                  } else {
                      n = n->left;
                  }
              } else {
                  assert (comp_result > 0);
                  if (n->right == NULL) {
                      n->right = inserted_node;
                      break;
                  } else {
                      n = n->right;
                  }
              }
          }
          inserted_node->parent = n;
      }
      insert_case1(t, inserted_node);
  }

  void insert_case1(rbtree t, node n) {
      if (n->parent == NULL)
          n->color = BLACK;
      else
          insert_case2(t, n);
  }

  void insert_case2(rbtree t, node n) {
      if (node_color(n->parent) == BLACK)
          return;
      else
          insert_case3(t, n);
  }

  void insert_case3(rbtree t, node n) {
      if (node_color(uncle(n)) == RED) {
          n->parent->color = BLACK;
          uncle(n)->color = BLACK;
          grandparent(n)->color = RED;
          insert_case1(t, grandparent(n));
      } else {
          insert_case4(t, n);
      }
  }

  void insert_case4(rbtree t, node n) {
      if (n == n->parent->right && n->parent == grandparent(n)->left) {
          rotate_left(t, n->parent);
          n = n->left;
      } else if (n == n->parent->left && n->parent == grandparent(n)->right) {
          rotate_right(t, n->parent);
          n = n->right;
      }
      insert_case5(t, n);
  }

  void insert_case5(rbtree t, node n) {
      n->parent->color = BLACK;
      grandparent(n)->color = RED;
      if (n == n->parent->left && n->parent == grandparent(n)->left) {
          rotate_right(t, grandparent(n));
      } else {
          assert (n == n->parent->right && n->parent == grandparent(n)->right);
          rotate_left(t, grandparent(n));
      }
  }

  void rbtree_delete(rbtree t, void* key, compare_func compare) {
      node child;
      node n = lookup_node(t, key, compare);
      if (n == NULL) return;
      if (n->left != NULL && n->right != NULL) {
          node pred = maximum_node(n->left);
          n->key   = pred->key;
          n = pred;
      }

      child = n->right == NULL ? n->left  : n->right;
      if (node_color(n) == BLACK) {
          n->color = node_color(child);
          delete_case1(t, n);
      }
      replace_node(t, n, child);
      if (n->parent == NULL && child != NULL)
          child->color = BLACK;
      pfree(n);

  }

  static node maximum_node(node n) {
      assert (n != NULL);
      while (n->right != NULL) {
          n = n->right;
      }
      return n;
  }

  void delete_case1(rbtree t, node n) {
      if (n->parent == NULL)
          return;
      else
          delete_case2(t, n);
  }

  void delete_case2(rbtree t, node n) {
      if (node_color(sibling(n)) == RED) {
          n->parent->color = RED;
          sibling(n)->color = BLACK;
          if (n == n->parent->left)
              rotate_left(t, n->parent);
          else
              rotate_right(t, n->parent);
      }
      delete_case3(t, n);
  }

  void delete_case3(rbtree t, node n) {
      if (node_color(n->parent) == BLACK &&
          node_color(sibling(n)) == BLACK &&
          node_color(sibling(n)->left) == BLACK &&
          node_color(sibling(n)->right) == BLACK)
      {
          sibling(n)->color = RED;
          delete_case1(t, n->parent);
      }
      else
          delete_case4(t, n);
  }

  void delete_case4(rbtree t, node n) {
      if (node_color(n->parent) == RED &&
          node_color(sibling(n)) == BLACK &&
          node_color(sibling(n)->left) == BLACK &&
          node_color(sibling(n)->right) == BLACK)
      {
          sibling(n)->color = RED;
          n->parent->color = BLACK;
      }
      else
          delete_case5(t, n);
  }

  void delete_case5(rbtree t, node n) {
      if (n == n->parent->left &&
          node_color(sibling(n)) == BLACK &&
          node_color(sibling(n)->left) == RED &&
          node_color(sibling(n)->right) == BLACK)
      {
          sibling(n)->color = RED;
          sibling(n)->left->color = BLACK;
          rotate_right(t, sibling(n));
      }
      else if (n == n->parent->right &&
               node_color(sibling(n)) == BLACK &&
               node_color(sibling(n)->right) == RED &&
               node_color(sibling(n)->left) == BLACK)
      {
          sibling(n)->color = RED;
          sibling(n)->right->color = BLACK;
          rotate_left(t, sibling(n));
      }
      delete_case6(t, n);
  }

  void delete_case6(rbtree t, node n) {
      sibling(n)->color = node_color(n->parent);
      n->parent->color = BLACK;
      if (n == n->parent->left) {
          assert (node_color(sibling(n)->right) == RED);
          sibling(n)->right->color = BLACK;
          rotate_left(t, n->parent);
      }
      else
      {
          assert (node_color(sibling(n)->left) == RED);
          sibling(n)->left->color = BLACK;
          rotate_right(t, n->parent);
      }
  }

/**
 * Free the memory taken by the tree.
 * @param n The current node
 */
void freeBinaryTree(node n) {
    if (n) {
        freeBinaryTree(n->left);
        freeBinaryTree(n->right);
        pfree(n);
    }
}

/**
 * Search the minimum double in the tree.
 * @param tree The tree
 * @return The minimum double
 */
double searchMin(rbtree tree) {
  node current = tree->root;
  if (!current) {return -1.0;}
  while (current->left) {current = current->left;}
  return *((double*) current->key);
}

/**
 * Search the maximum double in the tree.
 * @param tree The tree
 * @return The maximum double
 */
double searchMax(rbtree tree) {
  node current = tree->root;
  if (!current) {return -1.0;}
  while (current->right) {current = current->right;}
  return *((double*) current->key);
}

/**/

/**
 * Compare two integers.
 * @param leftp The left integer
 * @param rightp The right integer
 * @return 0 if = | 1 if > | -1 if <
 */
int compare_double(void* leftp, void* rightp) {
  double left = *((double*)leftp);
  double right = *((double*)rightp);
  if (left < right)
      return -1;
  else if (left > right)
      return 1;
  else {
      return 0;
  }
}

/**
 * Compute the percentile of an array of float.
 * @param array The array
 * @param length The length of the array
 * @param percentile The percentile
 * @return The computed value
 */
double get_percentile(const double* array, int length, double percentile) {
  int n = length * (100 - percentile) / 100;
  rbtree t = rbtree_create();

  for (int i = 0; i < n; i++) {
      rbtree_insert(t, (void*)(&array[i]), compare_double);
  }

  double min = searchMin(t);

  for (int i = n; i < length; i++) {
      if (array[i] > min) {
          rbtree_delete(t,(void*)(&min), compare_double);
          rbtree_insert(t, (void*)(&array[i]), compare_double);
          min = searchMin(t);
      }
  }

  double res = min;
  freeBinaryTree(t->root);
  pfree(t);
  return res;
}

/**
 * Execute the Sliding Window Segmentation algorithm with a percentile.
 * @param temp The trajectory
 * @param percentile The percentile
 * @param windows_length The length of the window
 * @param kernel The kernel
 * @return An array of sub-trajectories
 */
ArrayType *
temporal_segmentation_sws_percentile(const Temporal *temp, double percentile, unsigned int windows_length, char kernel) {
    const TSequence *trajectory = (TSequence *) temp;

    unsigned int length = trajectory->count;

    if (length < windows_length) {
        return temporalarr_to_array(&temp, 1);
    }

    double *error_signal = generate_error_signal(trajectory, windows_length, kernel);

    double threshold = get_percentile(error_signal, length, percentile);

    struct Segmentation segmentation;
    segment_with_sws(&segmentation, error_signal, threshold, length);

    ArrayType *result = generate_sub_trajectories(trajectory, &segmentation);

    pfree(error_signal);
    pfree(segmentation.indices);

    return result;
}

/**
 * Block of the run length encoding of a compressed matrix.
 */
struct Block {
    unsigned int start; // The start of the block
    unsigned int end;   // The end of the block
    struct Block *next; // The next block
};


/**
 * Compressed Start-Stop Matrix.
 */
struct CSSM {
      struct Block** blocks; // The list of blocks
      unsigned int n;        // The length of the start-stop matrix
};

/**
 * Compute the negation of a compressed start-stop matrix.
 * @param cssm The compressed start-stop matrix
 */
void negateCSSM(struct CSSM* cssm) {
      for (unsigned int i = 0; i < cssm->n; i++) {
          struct Block *current_block = cssm->blocks[i];
          if (current_block) {
              if (current_block->start != 0) {
                  current_block->end = current_block->start-1;
                  current_block->start = 0;
              }
              else { // start == 0
                  if (current_block->end != i) {
                      current_block->start = current_block->end + 1;
                      current_block->end = i;
                  }
                  else { // end = i
                      cssm->blocks[i] = NULL;
                  }
              }
          }
      }
}

/**
 * Compute the compressed start-stop matrix for the time criterion.
 * @param trajectory The trajectory
 * @param time The time threshold
 * @return The compressed start-stop matrix
 */
struct CSSM generate_CSSM_time(const TSequence *trajectory, double time) {
  struct CSSM cssm = {.n = trajectory->count, .blocks = palloc(sizeof(struct Block *)*trajectory->count)};
  assert(cssm.blocks);

  int i = trajectory->count-1;

  for (int j = trajectory->count-1; j >= 0; j--) {
      while (i >= 0 && ((double)(tsequence_inst_n(trajectory, j)->t - tsequence_inst_n(trajectory, i)->t))/1000000.0/60.0 < time) { // Minutes
          i--;
      }
      struct Block *block = palloc(sizeof(struct Block));
      assert(block);
      block->start = ((i>=0) ? (i):(0));
      block->end = j;
      block->next = NULL;
      cssm.blocks[j] = block;
  }
  negateCSSM(&cssm);

  return cssm;
}

double searchMin(rbtree tree);
double searchMax(rbtree tree);

/**
 * Compute the compressed start-stop matrix for the speed range criterion.
 * @param trajectory The trajectory
 * @param threshold The speed threshold
 * @return The compressed start-stop matrix
 */
struct CSSM generate_CSSM_speed(const TSequence *trajectory, double threshold) {
  struct CSSM cssm = {.n = trajectory->count, .blocks = palloc(sizeof(struct Block *)*trajectory->count)};
  assert(cssm.blocks);

  double *speed = palloc(sizeof(double)*trajectory->count);
  for (int i = 0; i < trajectory->count-1; i++) {
      int t_0 = tsequence_inst_n(trajectory, i)->t, t_1 = tsequence_inst_n(trajectory, i+1)->t;
      POINT2D p_0 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i))), p_1 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i+1)));
      speed[i] = (haversine_distance(p_0, p_1)/1000) / (((double)(t_1 - t_0))/1000000/3600);
  }
  speed[trajectory->count-1] = speed[trajectory->count-2];

  int i = trajectory->count-1;

  rbtree t = rbtree_create();
  rbtree_insert(t, (void*)(&speed[i]), compare_double);
  for (int j = trajectory->count-1; j >= 0; j--) {
      while (i >= 0 && (searchMax(t) - searchMin(t) <= threshold)) {
          i--;
          rbtree_insert(t, (void*)(&speed[i]), compare_double);
      }
      struct Block *block = palloc(sizeof(struct Block));

      block->start = ((i>=0) ? (i):(0));
      block->end = j;
      block->next = NULL;
      cssm.blocks[j] = block;
      rbtree_delete(t, (void*)(&speed[j]), compare_double);
  }

  return cssm;
}
/**
 * Return the absolute difference between two angles (in degrees).
 * @param angle_a The first angle
 * @param angle_b The second angle
 * @return The difference
 */
double
get_angle_diff(double angle_a, double angle_b) {
    double x = 360 - fabs(angle_a - angle_b);
    double y = fabs(angle_a - angle_b);

    if (x < y) {
        return x;
    }
    else {
        return y;
    }
}

/**
 * Compute the compressed start-stop matrix for the angular criterion.
 * @param trajectory The trajectory
 * @param threshold The angle threshold
 * @return The compressed start-stop matrix
 */
struct CSSM generate_CSSM_angular(const TSequence *trajectory, double threshold) {
  struct CSSM cssm = {.n = trajectory->count, .blocks = palloc(sizeof(struct Block *)*trajectory->count)};
  assert(cssm.blocks);

  double *angle = palloc(sizeof(double)*trajectory->count);
  for (int i = 0; i < trajectory->count-1; i++) {
      POINT2D p_0 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i))), p_1 = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, i+1)));
      angle[i] = bearing(p_0, p_1);
  }
  angle[trajectory->count-1] = angle[trajectory->count-2];

  int i = trajectory->count-1;

  for (int j = trajectory->count-1; j >= 0; j--) {
      while (i >= 0 && ((i == j) || (get_angle_diff(angle[i], angle[i-1]) <= threshold))) {
          i--;
      }
      struct Block *block = palloc(sizeof(struct Block));

      block->start = ((i>=0) ? (i):(0));
      block->end = j;
      block->next = NULL;
      cssm.blocks[j] = block;
  }

  return cssm;
}

/**
 * Compare the latitude of two points.
 * @param leftp The left point
 * @param rightp The right point
 * @return 0 if = | 1 if > | -1 if <
 */
int compare_lat(void* leftp, void* rightp) {
  POINT2D left = *((POINT2D*)leftp);
  POINT2D right = *((POINT2D*)rightp);
  if (left.y < right.y)
      return -1;
  else if (left.y > right.y)
      return 1;
  else {
      return 0;
  }
}

/**
 * Compare the longitude of two points.
 * @param leftp The left point
 * @param rightp The right point
 * @return 0 if = | 1 if > | -1 if <
 */
int compare_lon(void* leftp, void* rightp) {
  POINT2D left = *((POINT2D*)leftp);
  POINT2D right = *((POINT2D*)rightp);
  if (left.x < right.x)
      return -1;
  else if (left.x > right.x)
      return 1;
  else {
      return 0;
  }
}

/**
 * Search left most point.
 * @param tree The tree
 * @return The left most point
 */
POINT2D*
search_min_point(rbtree tree) {
  node current = tree->root;
  if (!current) {return NULL;}
  while (current->left) {current = current->left;}
  return (POINT2D*) current->key;
}

/**
 * Search right most point.
 * @param tree The tree
 * @return The right most point
 */
POINT2D*
search_max_point(rbtree tree) {
  node current = tree->root;
  if (!current) {return NULL;}
  while (current->right) {current = current->right;}
  return (POINT2D*) current->key;
}

/**
 * A circle
 */
struct Circle_c {
  POINT2D center; // The center of the circle
  double radius;  // the radius of the circle
};

/**
 * Compute the circle given the fact that the points are located on its edge.
 * @param R The points
 * @param n The number of points
 * @return The circle
 */
struct Circle_c
get_trivial_circle(POINT2D **R, unsigned int n) {
    POINT2D p = {.x=0, .y=0};
    struct Circle_c circle = {.center=p, .radius=0.0};
    if (n == 0) {
        return circle;
    }
    else if (n == 1) {
        circle.center.x = R[0]->x;
        circle.center.y = R[0]->y;
        return circle;
    }
    else if (n == 2) {
        POINT2D temp = midpoint(*R[0], *R[1]);
        circle.center.x = temp.x;
        circle.center.y = temp.y;
        circle.radius = haversine_distance(circle.center, *R[1]);
        return circle;
    }
    else {
        double bx = R[1]->x - R[0]->x, by = R[1]->y - R[0]->y, cx = R[2]->x - R[0]->x, cy = R[2]->y - R[0]->y;

        double B = pow(bx, 2) + pow(by, 2), C = pow(cx, 2) + pow(cy, 2), D = bx * cy - by * cx;

        circle.center.x = R[0]->x + ((cy * B - by * C) / (2 * D));
        circle.center.y = R[0]->y + ((bx * C - cx * B) / (2 * D));

        double max = -1;
        for (int i = 0; i < 3; i++) {
            double temp = haversine_distance(*R[i], circle.center);
            if (temp > max) {
                max = temp;
            }
        }
        circle.radius = max;
        return circle;
    }
}

/**
 * Execute the welzl algorithm
 * @param P The points
 * @param R The points to form a circle
 * @param n_p The number of points in P
 * @param n_r The number of points in R
 * @return The circle
 */
struct Circle_c
welzl(POINT2D** P, POINT2D** R, unsigned int n_p, unsigned int n_r) { // Based on https://www.geeksforgeeks.org/minimum-enclosing-circle-set-2-welzls-algorithm/
  if (n_p == 0 || n_r == 3) {
      return get_trivial_circle(R, n_r);
  }

  int i = rand() % n_p;

  POINT2D *temp = P[i];
  P[i] = P[n_p-1];
  P[n_p-1] = temp;

  struct Circle_c circle = welzl(P, R, n_p-1, n_r);

  if (haversine_distance(circle.center, *P[n_p-1]) <= circle.radius) {
      return circle;
  }

  R[n_r] = P[n_p-1];
  n_r++;

  return welzl(P, R, n_p-1, n_r);
}

/**
 * Get the diameter of the minimum enclosing circle of four points.
 * @param points The four points
 * @return
 */
double
get_mec_diameter(POINT2D** points) {
  unsigned int nb = 4;
  POINT2D* R[nb];

  struct Circle_c circle = welzl(points, R, nb, 0);

  return circle.radius * 2;
}

/**
 * Compute the compressed start-stop matrix for the disk criterion.
 * @param trajectory The trajectory
 * @param distance The maximum length of the disk
 * @return The compressed start-stop matrix
 */
struct CSSM generate_CSSM_disk(const TSequence *trajectory, double distance) {
  struct CSSM cssm = {.n = trajectory->count, .blocks = palloc(sizeof(struct Block *)*trajectory->count)};
  assert(cssm.blocks);

  int i = trajectory->count-1;

  rbtree t_lat = rbtree_create();
  rbtree t_lon = rbtree_create();

  POINT2D *points_array = palloc(sizeof(POINT2D)*trajectory->count);

  for (int x = 0; x < trajectory->count; x++) {
      points_array[x] = datum_point2d(tinstant_value(tsequence_inst_n(trajectory, x)));
  }

  POINT2D *p = &points_array[i];
  rbtree_insert(t_lat, (void*)(p), compare_lat);
  rbtree_insert(t_lon, (void*)(p), compare_lon);
  POINT2D *points[4] = {p, p, p, p};

  for (int j = trajectory->count-1; j >= 0; j--) {
      while (i >= 0 && ( i == j || get_mec_diameter(points) <= distance)) {
          i--;
          p = &points_array[i];
          rbtree_insert(t_lat, (void*)(p), compare_lat);
          rbtree_insert(t_lon, (void*)(p), compare_lon);
          points[0] = search_min_point(t_lat); points[1] = search_min_point(t_lon);
          points[2] = search_max_point(t_lat); points[3] = search_max_point(t_lon);
      }
      struct Block *block = palloc(sizeof(struct Block));

      block->start = ((i>=0) ? (i):(0));
      block->end = j;
      block->next = NULL;
      cssm.blocks[j] = block;

      p = &points_array[j];
      rbtree_delete(t_lat, (void*)(p), compare_lat);
      rbtree_delete(t_lon, (void*)(p), compare_lon);
      points[0] = search_min_point(t_lat); points[1] = search_min_point(t_lon);
      points[2] = search_max_point(t_lat); points[3] = search_max_point(t_lon);
  }
  pfree(points_array);
  return cssm;

}

/**
 * Verify if the ranges of the first and second block intersect.
 * @param a The first block
 * @param b The second block
 * @return True if they intersect else False
 */
bool
block_intersect(struct Block *a, struct Block *b) {
  return (a->end >= b->start) && (b->end >= a->start);
}

/**
 * Compute the conjunction of two compressed start-stop matrices.
 * @param a The first compressed start-stop matrix
 * @param b The second compressed start-stop matrix
 */
void
conjunction_cssm(struct CSSM *a, struct CSSM *b) {
    struct Block **blocks = palloc(sizeof(struct Block*)*a->n);

    for (unsigned int i = 0; i < a->n; i++) {
        struct Block *block_a = a->blocks[i];
        struct Block *block_b = b->blocks[i];

        struct Block *last_block = NULL;
        blocks[i] = NULL;

        while (block_a != NULL && block_b != NULL) {
            if (block_intersect(block_a, block_b)) {
                struct Block *new_block = palloc(sizeof(struct Block));
                new_block->next=NULL;
                new_block->start = (block_a->start > block_b->start) ? block_a->start : block_b->start;
                new_block->end = (block_a->end > block_b->end) ? block_b->end : block_a->end;
                if (last_block == NULL) {
                    blocks[i] = new_block;
                }
                else {
                    last_block->next = new_block;
                }
                last_block = new_block;
            }

            if (block_a->end < block_b->end) {
                block_a = block_a->next;
            }
            else {
                block_b = block_b->next;
            }
        }
    }
    a->blocks = blocks;

}

/**
 * Compute the disjunction of two compressed start-stop matrices.
 * @param a The first compressed start-stop matrix
 * @param b The second compressed start-stop matrix
 */
void
disjunction_cssm(struct CSSM *a, struct CSSM *b) {
    struct Block **blocks = palloc(sizeof(struct Block*)*a->n);

    for (unsigned int i = 0; i < a->n; i++) {
        struct Block *block_a = a->blocks[i];
        struct Block *block_b = b->blocks[i];
        struct Block *last_block = NULL;

        blocks[i] = NULL;

        while (block_a != NULL || block_b != NULL) {
            struct Block *new_block = palloc(sizeof(struct Block));
            new_block->next = NULL;
            bool still_intersect = true;

            if (block_a != NULL && block_b != NULL) {
                if (block_a->start <= block_b->start) {
                    new_block->start = block_a->start;
                    new_block->end = block_a->end;
                    block_a = block_a->next;
                }
                else {
                    new_block->start = block_b->start;
                    new_block->end = block_b->end;
                    block_b = block_b->next;
                }
            }

            else if (block_a != NULL) {
                new_block->start = block_a->start;
                new_block->end = block_a->end;
                block_a = block_a->next;
            }
            else {
                new_block->start = block_b->start;
                new_block->end = block_b->end;
                block_b = block_b->next;
            }
            while (still_intersect) {
                still_intersect = false;
                if (block_a != NULL && block_intersect(block_a, new_block)) {
                    still_intersect = true;
                    new_block->start = (new_block->start > block_a->start) ? block_a->start:new_block->start;
                    new_block->end = (new_block->end < block_a->end) ? block_a->end : new_block->end;
                    block_a = block_a->next;
                }
                else if (block_b != NULL && block_intersect(block_b, new_block)) {
                    still_intersect = true;
                    new_block->start = (new_block->start > block_b->start) ? block_b->start:new_block->start;
                    new_block->end = (new_block->end < block_b->end) ? block_b->end : new_block->end;
                    block_b = block_b->next;
                }

            }

            if (last_block != NULL) {
                last_block->next = new_block;
            }
            else {
                blocks[i] = new_block;
            }

            last_block = new_block;
        }
    }
    a->blocks = blocks;
}

/**
 * Node of a segmentation tree.
 */
 struct CNode {
     unsigned int count, index;
     struct CNode *last, *argmin;

     enum rbtree_node_color color;
     struct CNode *parent, *left, *right;
 };

/**
 * Compare two nodes of a segmentation tree.
 * @param leftp The left node
 * @param rightp The right node
 * @return 0 if = | 1 if > | -1 if <
 */
int compare_cnode(void* leftp, void* rightp) {
  struct CNode* left = (struct CNode*)leftp;
  struct CNode* right = (struct CNode*)rightp;
  if (left->index < right->index)
      return -1;
  else if (left->index > right->index)
      return 1;
  else {
      return 0;
  }
}

/**
 * Search the previous node of a node.
 * @param n The node
 * @return The previous node
 */
node
rbtree_get_previous(node n) {
    if (n->left != NULL) {
        n = n->left;
        while (n->right != NULL) {
            n = n->right;
        }
        return n;
    }
    else if (n->parent!=NULL) {
        if (n->parent->right == n) {
            return n->parent;
        }
        else {
            while (n->parent->right != n) {
                if (n->parent->parent == NULL) {
                    return NULL;
                }
                n = n->parent;
            }
            return n->parent;
        }
    }
    return NULL;
}

/**
 * Search the next node of a node.
 * @param n The node
 * @return The next node
 */
node
rbtree_get_next(node n) {
  if (n->right != NULL) {
      n = n->right;
      while (n->left != NULL) {
          n = n->left;
      }
      return n;
  }
  else if (n->parent!=NULL) {
      if (n->parent->left == n) {
          return n->parent;
      }
      else {
          while (n->parent->left != n) {
              if (n->parent->parent == NULL) {
                  return NULL;
              }
              n = n->parent;
          }
          return n->parent;
      }
  }
  return NULL;
}

/*Segmentation tree*/
struct segmentation_tree {
  struct CNode *root;
};

    void insert_case1_segmentation(struct segmentation_tree *t, struct CNode *n);
    void insert_case2_segmentation(struct segmentation_tree *t, struct CNode *n);
    void insert_case3_segmentation(struct segmentation_tree *t, struct CNode *n);
    void insert_case4_segmentation(struct segmentation_tree *t, struct CNode *n);
    void insert_case5_segmentation(struct segmentation_tree *t, struct CNode *n);


      void rbtree_insert_segmentation(struct segmentation_tree *t, struct CNode *inserted_node) {
      inserted_node->left = NULL;
      inserted_node->right = NULL;
      inserted_node->parent = NULL;
      inserted_node->color = RED;
      inserted_node->argmin = inserted_node;

      if (t->root == NULL) {
          t->root = inserted_node;
      } else {
          struct CNode *n = t->root;
          while (1) {
              if (n->argmin->count > inserted_node->count) {
                  n->argmin = inserted_node;
              }
              if (inserted_node->index <= n->index) {
                  if (n->left == NULL) {
                      n->left = inserted_node;
                      break;
                  } else {
                      n = n->left;
                  }
              } else {
                  if (n->right == NULL) {
                      n->right = inserted_node;
                      break;
                  } else {
                      n = n->right;
                  }
              }
          }
          inserted_node->parent = n;
      }
      insert_case1_segmentation(t, inserted_node);
  }

  color node_color_segmentation(struct CNode *n) {
      return n == NULL ? BLACK : n->color;
  }
  struct CNode *grandparent_segmentation(struct CNode *n) {
      return n->parent->parent;
  }

  struct CNode *sibling_segmentation(struct CNode *n) {
      if (n == n->parent->left)
          return n->parent->right;
      else
          return n->parent->left;
  }

  struct CNode *uncle_segmentation(struct CNode *n) {
      return sibling_segmentation(n->parent);
  }

  void replace_node_segmentation(struct segmentation_tree *t, struct CNode *oldn, struct CNode *newn) {
      if (oldn->parent == NULL) {
          t->root = newn;
      } else {
          if (oldn == oldn->parent->left)
              oldn->parent->left = newn;
          else
              oldn->parent->right = newn;
      }
      if (newn != NULL) {
          newn->parent = oldn->parent;
      }
  }


  void rotate_left_segmentation(struct segmentation_tree *t, struct CNode *n) {
      struct CNode *r = n->right;
      replace_node_segmentation(t, n, r);
      n->right = r->left;
      if (r->left != NULL) {
          r->left->parent = n;
      }
      r->left = n;
      n->parent = r;

      r->argmin = n->argmin;
      n->argmin = n;
      if (n->left != NULL && n->argmin->count > n->left->argmin->count) {n->argmin = n->left->argmin;}
      if (n->right != NULL && n->argmin->count > n->right->argmin->count) {n->argmin = n->right->argmin;}
  }

  void rotate_right_segmentation(struct segmentation_tree *t, struct CNode *n) {
      struct CNode *L = n->left;
      replace_node_segmentation(t, n, L);
      n->left = L->right;
      if (L->right != NULL) {
          L->right->parent = n;
      }
      L->right = n;
      n->parent = L;

      L->argmin = n->argmin;
      n->argmin = n;
      if (n->left != NULL && n->argmin->count > n->left->argmin->count) {n->argmin = n->left->argmin;}
      if (n->right != NULL && n->argmin->count > n->right->argmin->count) {n->argmin = n->right->argmin;}
  }


  void insert_case1_segmentation(struct segmentation_tree *t, struct CNode *n) {
      if (n->parent == NULL)
          n->color = BLACK;
      else
          insert_case2_segmentation(t, n);
  }


  void insert_case2_segmentation(struct segmentation_tree *t, struct CNode *n) {
      if (node_color_segmentation(n->parent) == BLACK)
          return;
      else
          insert_case3_segmentation(t, n);
  }

  void insert_case3_segmentation(struct segmentation_tree *t, struct CNode *n) {
      if (node_color_segmentation(uncle_segmentation(n)) == RED) {
          n->parent->color = BLACK;
          uncle_segmentation(n)->color = BLACK;
          grandparent_segmentation(n)->color = RED;
          insert_case1_segmentation(t, grandparent_segmentation(n));
      } else {
          insert_case4_segmentation(t, n);
      }
  }

  void insert_case4_segmentation(struct segmentation_tree *t, struct CNode *n) {
      if (n == n->parent->right && n->parent == grandparent_segmentation(n)->left) {
          rotate_left_segmentation(t, n->parent);
          n = n->left;
      } else if (n == n->parent->left && n->parent == grandparent_segmentation(n)->right) {
          rotate_right_segmentation(t, n->parent);
          n = n->right;
      }
      insert_case5_segmentation(t, n);
  }

  void insert_case5_segmentation(struct segmentation_tree *t, struct CNode *n) {
      n->parent->color = BLACK;
      grandparent_segmentation(n)->color = RED;
      if (n == n->parent->left && n->parent == grandparent_segmentation(n)->left) {
          rotate_right_segmentation(t, grandparent_segmentation(n));
      } else {
          rotate_left_segmentation(t, grandparent_segmentation(n));
      }
  }


/**/

/**
 * Return the last common node from the search paths to b->start and the one to b->end
 * @param t The tree
 * @param b The block
 * @return The split node
 */
struct CNode *
get_split_node(struct segmentation_tree *t, struct Block * b) {

    if (!t->root) return NULL;

    struct CNode *node_x = t->root;
    struct CNode *node_y = t->root;

    while (node_x == node_y && node_x->index != b->start && node_y->index != b->end) {
        if (node_x->index < b->start) {
            node_x = node_x->right;
        }
        else {
            node_x = node_x->left;
        }

        if (node_y->index < b->end) {
            node_y = node_y->right;
        }
        else {
            node_y = node_y->left;
        }
    }

    if (node_x == node_y) {
        return node_x;
    }
    else {
        return node_x->parent;
    }
}

/**
 * Search the node with the minimal count which is contained in the range of the block in the tree.
 * @param t The tree
 * @param b The block
 * @return The minimal count node
 */
struct CNode *
get_minimal_count(struct segmentation_tree *t, struct Block *b) {

      struct CNode *v_split = get_split_node(t, b);
      struct CNode *v_min = v_split;

      struct CNode *v_current = v_split->left;

      while (v_current && v_current->index != b->start) {

          if (v_current->index >= b->start && v_min->count > v_current->count) {v_min = v_current;}

          if (v_current->index > b->start) {
              if (v_current->right && v_min->count > v_current->right->argmin->count) {v_min = v_current->right->argmin;}
              v_current = v_current->left;
          }
          else {
              v_current = v_current->right;
          }
      }

      if (v_current && v_min->count >= v_current->count) {
          v_min = v_current;
      }

      v_current = v_split->right;

      while (v_current && v_current->index != b->end) {

          if (v_current->index <= b->end && v_min->count > v_current->count) {v_min = v_current;}

          if (v_current->index > b->end) {
              v_current = v_current->left;
          }
          else {
              if (v_current->left && v_min->count > v_current->left->argmin->count) {v_min = v_current->left->argmin;}
              v_current = v_current->right;
          }
      }

      if (v_current && v_min->count >= v_current->count) {
          v_min = v_current;
      }

      return v_min;
}


/**
 * Compute the segmentation tree from the compressed start-stop matrix.
 * @param cssm The compressed start-stop matrix
 * @return The segmentation tree
 */
struct segmentation_tree*
  compute_segmentation_tree(struct CSSM *cssm) {
    struct segmentation_tree *t = palloc(sizeof(struct segmentation_tree));
    t->root = NULL;

      struct CNode *v = palloc(sizeof(struct CNode));
      v->index = 0;
      v->count = 0;
      rbtree_insert_segmentation(t, v);

      for (unsigned int i = 1; i < cssm->n; i++) {
          v = palloc(sizeof(struct CNode));
          v->index = i;
          v->count = INT_MAX;
          v->last = NULL;
          struct Block *b = cssm->blocks[i];
          while (b != NULL) {
              struct CNode *vp = get_minimal_count(t, b);

              if (vp->count != INT_MAX && vp->count+1 < v->count) {
                  v->count = vp->count+1;
                  v->last = vp;
              }
              b = b->next;
          }
          rbtree_insert_segmentation(t, v);
      }

      return t;
  }

/**
 * Search the node which contains the index in the tree.
 * @param t The tree
 * @param index The index
 * @return The node
 */
struct CNode*
rbtree_find(struct segmentation_tree *t, unsigned int index) {

  struct CNode *current = t->root;

  if (!current) return NULL;

  while (current->index != index) {
      if (current->index < index) {
          current = current->right;
      }
      else {
          current = current->left;
      }
      assert(current);
  }

  return current;
}

/**
 * Compute the segmentation with the segmentation tree.
 * @param segmentation The segmentation
 * @param t The tree
 * @param n The length of the trajectory
 */
void
segment_with_stable_criteria(struct Segmentation *segmentation, struct segmentation_tree *t, unsigned int n) {
    segmentation->indices = palloc(sizeof(unsigned int)*n);
    assert(segmentation->indices);
    segmentation->length = 0;

    unsigned int *temp_segmentation = palloc(sizeof(unsigned int)*n);
    unsigned int temp_number = 1;
    temp_segmentation[0] = n-1;

    struct CNode *v = rbtree_find(t, n-1);

    int a = n-2;
    while (a > 0 && v->count == INT_MAX) {
        v = rbtree_find(t, a);
        a--;
    }

    if (a == 0) {
        pfree(temp_segmentation);
        segmentation->indices[0] = n-1;
        segmentation->length = 1;
        return;
    }


    int k = v->count;
    while (k > 1) {
        // [v->last->index, v->index)]
        temp_segmentation[temp_number] = v->last->index;
        temp_number++;

        v = v->last;
        k--;
    }

    for (int i = temp_number-1; i >= 0; i--) {
        segmentation->indices[segmentation->length] = temp_segmentation[i];
        segmentation->length++;
    }

    pfree(temp_segmentation);
}

/**
 * The types of token
 */
enum token_type {function_t, number_t, open_t, close_t, eof_t, not_t};


/**
 * A token
 */
struct c_token {
    enum token_type type; // Type
    char* value;          // The pointer to its value
  };


/**
 * Parse the string and return the next token
 * @param token The next token
 * @param criteria The string
 * @param offset The offset
 * @return The new offset
 */
unsigned int
get_next_token(struct c_token *token, char *criteria, unsigned int offset) {
    char c = criteria[offset];

    while (c == ' ') {
        offset++;
        c = criteria[offset];
    }

    if (isalpha(c)) {
        token->type = function_t;
        token->value = &criteria[offset];
        offset += 1;
    }
    else if (c == '[') {
        token->type = number_t;
        token->value = &criteria[offset+1];

        int i = 1;
        c = criteria[offset+i];
        while ((isdigit(c) || c == '.')) {
            i++;
            c = criteria[offset+i];
        }
        offset += i+1;
    }
    else if (c == '!') {
        token->type = not_t;
        token->value = &criteria[offset];
        offset += 1;
    }
    else if (c == '(') {
        token->type = open_t;
        token->value = &criteria[offset];
        offset += 1;
    }

    else if (c == ')') {
        token->type = close_t;
        token->value = &criteria[offset];
        offset += 1;
    }
    else {
        token->type = eof_t;
        token->value = &criteria[offset];
        offset += 1;
    }

    return offset;
}

/**
 * Compute the disjunction of all the compressed start-stop matrix contained the parenthesis.
 * @param trajectory The trajectory
 * @param criteria The string of criteria
 * @param cssm The compressed start-stop matrix
 * @param offset The offset
 * @return The new offset
 */
unsigned int
parse_disjunction(const TSequence *trajectory, char *criteria, struct CSSM* cssm, unsigned int offset) { // Conjunctive normal form (and of or)
    bool first = true;
    struct CSSM temp;
    bool negate = false;
    struct c_token token;
    offset = get_next_token(&token, criteria, offset);

    while (token.type != close_t && token.type != eof_t) {
        if (token.type == not_t) negate = true;

        else if (token.type == function_t) {
            char f = *token.value;
            offset = get_next_token(&token, criteria, offset);
            switch (f) {
                case 's': temp = generate_CSSM_speed(trajectory, strtod(token.value, NULL)); break;
                case 't': temp = generate_CSSM_time(trajectory, strtod(token.value, NULL)); break;
                case 'd': temp = generate_CSSM_disk(trajectory, strtod(token.value, NULL)); break;
                case 'a': temp = generate_CSSM_angular(trajectory, strtod(token.value, NULL)); break;
                default: assert(false); break;
            }
            if (negate) {
                negateCSSM(&temp);
            }
            if (first) {
                cssm->blocks = temp.blocks;
                cssm->n = temp.n;
                first = false;
            }
            else {
                disjunction_cssm(cssm, &temp);
            }

        }
        offset = get_next_token(&token, criteria, offset);
    }
    if (token.type == eof_t) {
        offset--;
    }
    return offset;
}

/**
 * Compute the conjunction of all the compressed start-stop matrix computed.
 * @param trajectory THe trajectory
 * @param criteria The string of criteria
 * @param cssm The compressed start-stop matrix
 */
void parse_conjunction(const TSequence *trajectory, char *criteria, struct CSSM* cssm) { // Conjunctive normal form (and of or)
    bool first = true;
    struct CSSM temp;
    unsigned int offset = 0;
    struct c_token token;
    offset = get_next_token(&token, criteria, offset);

    while (token.type != eof_t) {
        if (token.type == open_t) {
            offset = parse_disjunction(trajectory, criteria, &temp, offset);
            if (first) {
                cssm->blocks = temp.blocks;
                cssm->n = temp.n;
                first = false;
            }
            else {
                conjunction_cssm(cssm, &temp);
            }
        }
        offset = get_next_token(&token, criteria, offset);
    }
}

/**
 * Execute the stable criteria segmentation algorithm.
 * @param temp The trajectory
 * @param criteria The criteria
 * @return An array of sub-trajectories
 */
ArrayType *
temporal_segmentation_stable_criteria(const Temporal *temp, char *criteria) {
    const TSequence *trajectory = (TSequence *) temp;

    unsigned int length = trajectory->count;

    struct CSSM cssm;

    parse_conjunction(trajectory, criteria, &cssm);

    struct segmentation_tree *t = compute_segmentation_tree(&cssm);

    struct Segmentation segmentation;

    segment_with_stable_criteria(&segmentation, t, length);

    ArrayType *result = generate_sub_trajectories(trajectory, &segmentation);

    pfree(segmentation.indices);

    return result;
}


/*****************************************************************************
 * Mapbox Vector Tile functions for temporal points.
 *****************************************************************************/

/**
 * Return a temporal point with consecutive equal points removed.
 * Equality test only on x and y dimensions of input.
 */
static TInstantSet *
tpointinstset_remove_repeated_points(const TInstantSet *is, double tolerance,
  int min_points)
{
  /* No-op on short inputs */
  if (is->count <= min_points)
    return tinstantset_copy(is);

  double tolsq = tolerance * tolerance;
  double dsq = FLT_MAX;

  const TInstant **instants = palloc(sizeof(TInstant *) * is->count);
  instants[0] = tinstantset_inst_n(is, 0);
  const POINT2D *last = datum_point2d_p(tinstant_value(instants[0]));
  int k = 1;
  for (int i = 1; i < is->count; i++)
  {
    bool last_point = (i == is->count - 1);
    const TInstant *inst = tinstantset_inst_n(is, i);
    const POINT2D *pt = datum_point2d_p(tinstant_value(inst));

    /* Don't drop points if we are running short of points */
    if (is->count - k > min_points + i)
    {
      if (tolerance > 0.0)
      {
        /* Only drop points that are within our tolerance */
        dsq = distance2d_sqr_pt_pt(last, pt);
        /* Allow any point but the last one to be dropped */
        if (! last_point && dsq <= tolsq)
          continue;
      }
      else
      {
        /* At tolerance zero, only skip exact dupes */
        if (FP_EQUALS(pt->x, last->x) && FP_EQUALS(pt->y, last->y))
          continue;
      }

      /* Got to last point, and it's not very different from
       * the point that preceded it. We want to keep the last
       * point, not the second-to-last one, so we pull our write
       * index back one value */
      if (last_point && k > 1 && tolerance > 0.0 && dsq <= tolsq)
      {
        k--;
      }
    }

    /* Save the point */
    instants[k++] = inst;
    last = pt;
  }
  /* Construct the result */
  TInstantSet *result = tinstantset_make(instants, is->count, MERGE_NO);
  pfree(instants);
  return result;
}

/**
 * Return a temporal point with consecutive equal points removed.
 * Equality test only on x and y dimensions of input.
 */
static TSequence *
tpointseq_remove_repeated_points(const TSequence *seq, double tolerance,
  int min_points)
{
  /* No-op on short inputs */
  if (seq->count <= min_points)
    return tsequence_copy(seq);

  double tolsq = tolerance * tolerance;
  double dsq = FLT_MAX;

  const TInstant **instants = palloc(sizeof(TInstant *) * seq->count);
  instants[0] = tsequence_inst_n(seq, 0);
  const POINT2D *last = datum_point2d_p(tinstant_value(instants[0]));
  int k = 1;
  for (int i = 1; i < seq->count; i++)
  {
    bool last_point = (i == seq->count - 1);
    const TInstant *inst = tsequence_inst_n(seq, i);
    const POINT2D *pt = datum_point2d_p(tinstant_value(inst));

    /* Don't drop points if we are running short of points */
    if (seq->count - i > min_points - k)
    {
      if (tolerance > 0.0)
      {
        /* Only drop points that are within our tolerance */
        dsq = distance2d_sqr_pt_pt(last, pt);
        /* Allow any point but the last one to be dropped */
        if (! last_point && dsq <= tolsq)
          continue;
      }
      else
      {
        /* At tolerance zero, only skip exact dupes */
        if (FP_EQUALS(pt->x, last->x) && FP_EQUALS(pt->y, last->y))
          continue;
      }

      /* Got to last point, and it's not very different from
       * the point that preceded it. We want to keep the last
       * point, not the second-to-last one, so we pull our write
       * index back one value */
      if (last_point && k > 1 && tolerance > 0.0 && dsq <= tolsq)
      {
        k--;
      }
    }

    /* Save the point */
    instants[k++] = inst;
    last = pt;
  }
  /* Construct the result */
  TSequence *result = tsequence_make(instants, k, seq->period.lower_inc,
    seq->period.upper_inc, MOBDB_FLAGS_GET_LINEAR(seq->flags), NORMALIZE);
  pfree(instants);
  return result;
}

/**
 * Return a temporal point with consecutive equal points removed.
 * Equality test only on x and y dimensions of input.
 */
static TSequenceSet *
tpointseqset_remove_repeated_points(const TSequenceSet *ss, double tolerance,
  int min_points)
{
  const TSequence *seq;

  /* Singleton sequence set */
  if (ss->count == 1)
  {
    seq = tsequenceset_seq_n(ss, 0);
    TSequence *seq1 = tpointseq_remove_repeated_points(seq, tolerance,
      min_points);
    TSequenceSet *result = tsequence_to_tsequenceset(seq1);
    pfree(seq1);
    return result;
  }

  /* No-op on short inputs */
  if (ss->totalcount <= min_points)
    return tsequenceset_copy(ss);

  /* General case */
  TSequence **sequences = palloc(sizeof(TSequence *) * ss->count);
  int npoints = 0;
  for (int i = 0; i < ss->count; i++)
  {
    seq = tsequenceset_seq_n(ss, i);
    /* Don't drop sequences if we are running short of points */
    if (ss->totalcount - npoints > min_points)
    {
      /* Minimum number of points set to 2 */
      sequences[i] = tpointseq_remove_repeated_points(seq, tolerance, 2);
      npoints += sequences[i]->count;
    }
    else
    {
      /* Save the sequence */
      sequences[i] = tsequence_copy(seq);
    }
  }
  return tsequenceset_make_free(sequences, ss->count, NORMALIZE);
}

/**
 * Return a temporal point with consecutive equal points removed.
 * Equality test only on x and y dimensions of input.
 */
static Temporal *
tpoint_remove_repeated_points(const Temporal *temp, double tolerance,
  int min_points)
{
  Temporal *result;
  ensure_valid_tempsubtype(temp->subtype);
  if (temp->subtype == TINSTANT)
    result = (Temporal *) tinstant_copy((TInstant *) temp);
  else if (temp->subtype == TINSTANTSET)
    result = (Temporal *) tpointinstset_remove_repeated_points(
      (TInstantSet *) temp, tolerance, min_points);
  else if (temp->subtype == TSEQUENCE)
    result = (Temporal *) tpointseq_remove_repeated_points(
      (TSequence *) temp, tolerance, min_points);
  else /* temp->subtype == TSEQUENCESET */
    result = (Temporal *) tpointseqset_remove_repeated_points(
      (TSequenceSet *) temp, tolerance, min_points);
  return result;
}

/*****************************************************************************
 * Affine functions
 *****************************************************************************/

/**
 * Affine transform a temporal point (iterator function)
 */
static void
tpointinst_affine1(const TInstant *inst, const AFFINE *a, int srid,
  bool hasz, TInstant **result)
{
  Datum value = tinstant_value(inst);
  double x, y;
  LWPOINT *lwpoint;
  if (hasz)
  {
    POINT3DZ p3d = datum_point3dz(value);
    x = p3d.x;
    y = p3d.y;
    double z = p3d.z;
    p3d.x = a->afac * x + a->bfac * y + a->cfac * z + a->xoff;
    p3d.y = a->dfac * x + a->efac * y + a->ffac * z + a->yoff;
    p3d.z = a->gfac * x + a->hfac * y + a->ifac * z + a->zoff;
    lwpoint = lwpoint_make3dz(srid, p3d.x, p3d.y, p3d.z);
  }
  else
  {
    POINT2D p2d = datum_point2d(value);
    x = p2d.x;
    y = p2d.y;
    p2d.x = a->afac * x + a->bfac * y + a->xoff;
    p2d.y = a->dfac * x + a->efac * y + a->yoff;
    lwpoint = lwpoint_make2d(srid, p2d.x, p2d.y);
  }
  GSERIALIZED *gs = geo_serialize((LWGEOM *) lwpoint);
  *result = tinstant_make(PointerGetDatum(gs), T_TGEOMPOINT, inst->t);
  lwpoint_free(lwpoint);
  pfree(gs);
  return;
}

/**
 * Affine transform a temporal point.
 */
static TInstant *
tpointinst_affine(const TInstant *inst, const AFFINE *a)
{
  int srid = tpointinst_srid(inst);
  bool hasz = MOBDB_FLAGS_GET_Z(inst->flags);
  TInstant *result;
  tpointinst_affine1(inst, a, srid, hasz, &result);
  return result;
}

/**
 * Affine transform a temporal point.
 */
static TInstantSet *
tpointinstset_affine(const TInstantSet *is, const AFFINE *a)
{
  int srid = tpointinstset_srid(is);
  bool hasz = MOBDB_FLAGS_GET_Z(is->flags);
  TInstant **instants = palloc(sizeof(TInstant *) * is->count);
  for (int i = 0; i < is->count; i++)
  {
    const TInstant *inst = tinstantset_inst_n(is, i);
    tpointinst_affine1(inst, a, srid, hasz, &instants[i]);
  }
  TInstantSet *result = tinstantset_make_free(instants, is->count, MERGE_NO);
  return result;
}

/**
 * Affine transform a temporal point.
 */
static TSequence *
tpointseq_affine(const TSequence *seq, const AFFINE *a)
{
  int srid = tpointseq_srid(seq);
  bool hasz = MOBDB_FLAGS_GET_Z(seq->flags);
  TInstant **instants = palloc(sizeof(TInstant *) * seq->count);
  for (int i = 0; i < seq->count; i++)
  {
    const TInstant *inst = tsequence_inst_n(seq, i);
    tpointinst_affine1(inst, a, srid, hasz, &instants[i]);
  }
  /* Construct the result */
  return tsequence_make_free(instants, seq->count, seq->period.lower_inc,
    seq->period.upper_inc, MOBDB_FLAGS_GET_LINEAR(seq->flags), NORMALIZE);
}

/**
 * Affine transform a temporal point.
 *
 * @param[in] ss Temporal point
 * @param[in] a Affine transformation
 */
static TSequenceSet *
tpointseqset_affine(const TSequenceSet *ss, const AFFINE *a)
{
  TSequence **sequences = palloc(sizeof(TSequence *) * ss->count);
  for (int i = 0; i < ss->count; i++)
    sequences[i] = tpointseq_affine(tsequenceset_seq_n(ss, i), a);
  return tsequenceset_make_free(sequences, ss->count, NORMALIZE);
}

/**
 * Affine transform a temporal point.
 */
static Temporal *
tpoint_affine(const Temporal *temp, const AFFINE *a)
{
  Temporal *result;
  ensure_valid_tempsubtype(temp->subtype);
  if (temp->subtype == TINSTANT)
    result = (Temporal *) tpointinst_affine((TInstant *) temp, a);
  else if (temp->subtype == TINSTANTSET)
    result = (Temporal *) tpointinstset_affine((TInstantSet *) temp, a);
  else if (temp->subtype == TSEQUENCE)
    result = (Temporal *) tpointseq_affine((TSequence *) temp, a);
  else /* temp->subtype == TSEQUENCESET */
    result = (Temporal *) tpointseqset_affine((TSequenceSet *) temp, a);
  return result;
}

/*****************************************************************************
 * Grid functions
 *****************************************************************************/

static void
point_grid(Datum value, bool hasz, const gridspec *grid, POINT4D *p)
{
  /* Read and round point */
  datum_point4d(value, p);
  if (grid->xsize > 0)
    p->x = rint((p->x - grid->ipx) / grid->xsize) * grid->xsize + grid->ipx;
  if (grid->ysize > 0)
    p->y = rint((p->y - grid->ipy) / grid->ysize) * grid->ysize + grid->ipy;
  if (hasz && grid->zsize > 0)
    p->z = rint((p->z - grid->ipz) / grid->zsize) * grid->zsize + grid->ipz;
}

/**
 * Stick a temporal point to the given grid specification.
 */
static TInstant *
tpointinst_grid(const TInstant *inst, const gridspec *grid)
{
  bool hasz = MOBDB_FLAGS_GET_Z(inst->flags);
  if (grid->xsize == 0 && grid->ysize == 0 && (hasz ? grid->zsize == 0 : 1))
    return tinstant_copy(inst);

  int srid = tpointinst_srid(inst);
  Datum value = tinstant_value(inst);
  POINT4D p;
  point_grid(value, hasz, grid, &p);
  /* Write rounded values into the next instant */
  LWPOINT *lwpoint = hasz ?
    lwpoint_make3dz(srid, p.x, p.y, p.z) : lwpoint_make2d(srid, p.x, p.y);
  GSERIALIZED *gs = geo_serialize((LWGEOM *) lwpoint);
  lwpoint_free(lwpoint);
  /* Construct the result */
  TInstant *result = tinstant_make(PointerGetDatum(gs), T_TGEOMPOINT, inst->t);
  /* We cannot lwpoint_free(lwpoint) */
  pfree(gs);
  return result;
}

/**
 * Stick a temporal point to the given grid specification.
 */
static TInstantSet *
tpointinstset_grid(const TInstantSet *is, const gridspec *grid)
{
  bool hasz = MOBDB_FLAGS_GET_Z(is->flags);
  int srid = tpointinstset_srid(is);
  TInstant **instants = palloc(sizeof(TInstant *) * is->count);
  int k = 0;
  for (int i = 0; i < is->count; i++)
  {
    POINT4D p, prev_p;
    const TInstant *inst = tinstantset_inst_n(is, i);
    Datum value = tinstant_value(inst);
    point_grid(value, hasz, grid, &p);
    /* Skip duplicates */
    if (i > 1 && prev_p.x == p.x && prev_p.y == p.y &&
      (hasz ? prev_p.z == p.z : 1))
      continue;

    /* Write rounded values into the next instant */
    LWPOINT *lwpoint = hasz ?
      lwpoint_make3dz(srid, p.x, p.y, p.z) : lwpoint_make2d(srid, p.x, p.y);
    GSERIALIZED *gs = geo_serialize((LWGEOM *) lwpoint);
    instants[k++] = tinstant_make(PointerGetDatum(gs), T_TGEOMPOINT, inst->t);
    lwpoint_free(lwpoint);
    pfree(gs);
    memcpy(&prev_p, &p, sizeof(POINT4D));
  }
  /* Construct the result */
  return tinstantset_make_free(instants, k, MERGE_NO);
}

/**
 * Stick a temporal point to the given grid specification.
 */
static TSequence *
tpointseq_grid(const TSequence *seq, const gridspec *grid, bool filter_pts)
{
  bool hasz = MOBDB_FLAGS_GET_Z(seq->flags);
  int srid = tpointseq_srid(seq);
  TInstant **instants = palloc(sizeof(TInstant *) * seq->count);
  int k = 0;
  for (int i = 0; i < seq->count; i++)
  {
    POINT4D p, prev_p;
    const TInstant *inst = tsequence_inst_n(seq, i);
    Datum value = tinstant_value(inst);
    point_grid(value, hasz, grid, &p);
    /* Skip duplicates */
    if (i > 1 && prev_p.x == p.x && prev_p.y == p.y &&
      (hasz ? prev_p.z == p.z : 1))
      continue;

    /* Write rounded values into the next instant */
    LWPOINT *lwpoint = hasz ?
      lwpoint_make3dz(srid, p.x, p.y, p.z) : lwpoint_make2d(srid, p.x, p.y);
    GSERIALIZED *gs = geo_serialize((LWGEOM *) lwpoint);
    instants[k++] = tinstant_make(PointerGetDatum(gs), T_TGEOMPOINT, inst->t);
    lwpoint_free(lwpoint);
    pfree(gs);
    memcpy(&prev_p, &p, sizeof(POINT4D));
  }
  if (filter_pts && k == 1)
  {
    pfree_array((void **) instants, 1);
    return NULL;
  }

  /* Construct the result */
  return tsequence_make_free(instants, k, k > 1 ? seq->period.lower_inc : true,
    k > 1 ? seq->period.upper_inc : true, MOBDB_FLAGS_GET_LINEAR(seq->flags),
    NORMALIZE);
}

/**
 * Stick a temporal point to the given grid specification.
 */
static TSequenceSet *
tpointseqset_grid(const TSequenceSet *ss, const gridspec *grid, bool filter_pts)
{
  int k = 0;
  TSequence **sequences = palloc(sizeof(TSequence *) * ss->count);
  for (int i = 0; i < ss->count; i++)
  {
    TSequence *seq = tpointseq_grid(tsequenceset_seq_n(ss, i), grid, filter_pts);
    if (seq != NULL)
      sequences[k++] = seq;
  }
  return tsequenceset_make_free(sequences, k, NORMALIZE);
}

/**
 * Stick a temporal point to the given grid specification.
 *
 * Only the x, y, and possible z dimensions are gridded, the timestamp is
 * kept unmodified. Two consecutive instants falling on the same grid cell
 * are collapsed into one single instant.
 */
static Temporal *
tpoint_grid(const Temporal *temp, const gridspec *grid, bool filter_pts)
{
  Temporal *result;
  ensure_valid_tempsubtype(temp->subtype);
  if (temp->subtype == TINSTANT)
    result = (Temporal *) tpointinst_grid((TInstant *) temp, grid);
  else if (temp->subtype == TINSTANTSET)
    result = (Temporal *) tpointinstset_grid((TInstantSet *) temp, grid);
  else if (temp->subtype == TSEQUENCE)
    result = (Temporal *) tpointseq_grid((TSequence *) temp, grid, filter_pts);
  else /* temp->subtype == TSEQUENCESET */
    result = (Temporal *) tpointseqset_grid((TSequenceSet *) temp, grid,
      filter_pts);
  return result;
}

/*****************************************************************************/

/**
 * Transform a temporal point into vector tile coordinate space.
 *
 * @param[in] tpoint Temporal point
 * @param[in] box Geometric bounds of the tile contents without buffer
 * @param[in] extent Tile extent in tile coordinate space
 * @param[in] buffer Buffer distance in tile coordinate space
 * @param[in] clip_geom True if temporal point should be clipped
 */
static Temporal *
tpoint_mvt(const Temporal *tpoint, const STBOX *box, uint32_t extent,
  uint32_t buffer, bool clip_geom)
{
  AFFINE affine = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  gridspec grid = {0, 0, 0, 0, 1, 1, 0, 0};
  double width = box->xmax - box->xmin;
  double height = box->ymax - box->ymin;
  double resx, resy, res, fx, fy;

  resx = width / extent;
  resy = height / extent;
  res = (resx < resy ? resx : resy) / 2;
  fx = extent / width;
  fy = -(extent / height);

  /* Remove all non-essential points (under the output resolution) */
  Temporal *tpoint1 = tpoint_remove_repeated_points(tpoint, res, 2);

  /* Euclidean (not synchronized) distance, i.e., parameter set to false */
  Temporal *tpoint2 = temporal_simplify(tpoint1, res, false);
  pfree(tpoint1);

  /* Transform to tile coordinate space */
  affine.afac = fx;
  affine.efac = fy;
  affine.ifac = 1;
  affine.xoff = -box->xmin * fx;
  affine.yoff = -box->ymax * fy;
  Temporal *tpoint3 = tpoint_affine(tpoint2, &affine);
  pfree(tpoint2);

  /* Snap to integer precision, removing duplicate and single points */
  Temporal *tpoint4 = tpoint_grid(tpoint3, &grid, true);
  pfree(tpoint3);
  if (tpoint4 == NULL || !clip_geom)
    return tpoint4;

  /* Clip temporal point taking into account the buffer */
  double max = (double) extent + (double) buffer;
  double min = -(double) buffer;
  int srid = tpoint_srid(tpoint);
  STBOX clip_box;
  stbox_set(true, false, false, false, srid, min, max, min, max,
    0, 0, 0, 0, &clip_box);
  Temporal *tpoint5 = tpoint_at_stbox1(tpoint4, &clip_box, UPPER_INC);
  pfree(tpoint4);
  if (tpoint5 == NULL)
    return NULL;
  /* We need to grid again the result of the clipping */
  Temporal *result = tpoint_grid(tpoint5, &grid, true);
  pfree(tpoint5);
  return result;
}

/*****************************************************************************/

/**
 * Decouple the points and the timestamps of a temporal point.
 *
 * @note The function does not remove consecutive points/instants that are equal.
 * @param[in] inst Temporal point
 * @param[out] timesarr Array of timestamps encoded in Unix epoch
 * @param[out] count Number of elements in the output array
 */
static Datum
tpointinst_decouple(const TInstant *inst, int64 **timesarr, int *count)
{
  int64 *times = palloc(sizeof(int64));
  times[0] = (inst->t / 1e6) + DELTA_UNIX_POSTGRES_EPOCH;
  *timesarr = times;
  *count = 1;
  return tinstant_value_copy(inst);
}

/**
 * Decouple the points and the timestamps of a temporal point.
 *
 * @note The function does not remove consecutive points/instants that are equal.
 * @param[in] is Temporal point
 * @param[out] timesarr Array of timestamps encoded in Unix epoch
 * @param[out] count Number of elements in the output array
 */
static Datum
tpointinstset_decouple(const TInstantSet *is, int64 **timesarr, int *count)
{
  /* Instantaneous sequence */
  if (is->count == 1)
    return tpointinst_decouple(tinstantset_inst_n(is, 0), timesarr, count);

  /* General case */
  LWGEOM **points = palloc(sizeof(LWGEOM *) * is->count);
  int64 *times = palloc(sizeof(int64) * is->count);
  for (int i = 0; i < is->count; i++)
  {
    const TInstant *inst = tinstantset_inst_n(is, i);
    Datum value = tinstant_value(inst);
    GSERIALIZED *gs = DatumGetGserializedP(value);
    points[i] = lwgeom_from_gserialized(gs);
    times[i] = (inst->t / 1e6) + DELTA_UNIX_POSTGRES_EPOCH;
  }
  LWGEOM *lwgeom = lwpointarr_make_trajectory(points, is->count,
    MOBDB_FLAGS_GET_LINEAR(is->flags));
  Datum result = PointerGetDatum(geo_serialize(lwgeom));
  pfree(lwgeom);
  *timesarr = times;
  *count = is->count;
  for (int i = 0; i < is->count; i++)
    lwpoint_free((LWPOINT *) points[i]);
  pfree(points);
  return result;
}

/**
 * Decouple the points and the timestamps of a temporal point.
 *
 * @note The function does not remove consecutive points/instants that are equal.
 * @param[in] seq Temporal point
 * @param[out] times Array of timestamps
 * @note The timestamps are returned in Unix epoch
 */
static LWGEOM *
tpointseq_decouple1(const TSequence *seq, int64 *times)
{
  /* General case */
  LWGEOM **points = palloc(sizeof(LWGEOM *) * seq->count);
  for (int i = 0; i < seq->count; i++)
  {
    const TInstant *inst = tsequence_inst_n(seq, i);
    Datum value = tinstant_value(inst);
    GSERIALIZED *gs = DatumGetGserializedP(value);
    points[i] = lwgeom_from_gserialized(gs);
    times[i] = (inst->t / 1e6) + DELTA_UNIX_POSTGRES_EPOCH;
  }
  LWGEOM *result = lwpointarr_make_trajectory(points, seq->count,
    MOBDB_FLAGS_GET_LINEAR(seq->flags));
  for (int i = 0; i < seq->count; i++)
    lwpoint_free((LWPOINT *) points[i]);
  pfree(points);
  return result;
}

/**
 * Decouple the points and the timestamps of a temporal point.
 *
 * @note The function does not remove consecutive points/instants that are equal.
 * @param[in] seq Temporal point
 * @param[out] timesarr Array of timestamps encoded in Unix epoch
 * @param[out] count Number of elements in the output array
 */
static Datum
tpointseq_decouple(const TSequence *seq, int64 **timesarr, int *count)
{
  int64 *times = palloc(sizeof(int64) * seq->count);
  LWGEOM *lwgeom = tpointseq_decouple1(seq, times);
  Datum result = PointerGetDatum(geo_serialize(lwgeom));
  pfree(lwgeom);
  *timesarr = times;
  *count = seq->count;
  return result;
}

/**
 * Decouple the points and the timestamps of a temporal point.
 *
 * @note The function does not remove consecutive points/instants that are equal.
 * @param[in] ss Temporal point
 * @param[out] timesarr Array of timestamps encoded in Unix epoch
 * @param[out] count Number of elements in the output array
 */
static Datum
tpointseqset_decouple(const TSequenceSet *ss, int64 **timesarr, int *count)
{
  /* Singleton sequence set */
  if (ss->count == 1)
    return tpointseq_decouple(tsequenceset_seq_n(ss, 0), timesarr, count);

  /* General case */
  uint32_t colltype = 0;
  LWGEOM **geoms = palloc(sizeof(LWGEOM *) * ss->count);
  int64 *times = palloc(sizeof(int64) * ss->totalcount);
  int k = 0;
  for (int i = 0; i < ss->count; i++)
  {
    const TSequence *seq = tsequenceset_seq_n(ss, i);
    geoms[i] = tpointseq_decouple1(seq, &times[k]);
    k += seq->count;
    /* If output type not initialized make geom type as output type */
    if (! colltype)
      colltype = lwtype_get_collectiontype(geoms[i]->type);
    /* If geom type is not compatible with current output type
     * make output type a collection */
    else if (colltype != COLLECTIONTYPE &&
      lwtype_get_collectiontype(geoms[i]->type) != colltype)
      colltype = COLLECTIONTYPE;
  }
  LWGEOM *coll = (LWGEOM *) lwcollection_construct((uint8_t) colltype,
    geoms[0]->srid, NULL, (uint32_t) ss->count, geoms);
  Datum result = PointerGetDatum(geo_serialize(coll));
  *timesarr = times;
  *count = ss->totalcount;
  /* We cannot lwgeom_free(geoms[i] or lwgeom_free(coll) */
  pfree(geoms);
  return result;
}

/**
 * Decouple the points and the timestamps of a temporal point.
 *
 * @param[in] temp Temporal point
 * @param[out] timesarr Array of timestamps encoded in Unix epoch
 * @param[out] count Number of elements in the output array
 */
static Datum
tpoint_decouple(const Temporal *temp, int64 **timesarr, int *count)
{
  Datum result;
  ensure_valid_tempsubtype(temp->subtype);
  if (temp->subtype == TINSTANT)
    result = tpointinst_decouple((TInstant *) temp, timesarr, count);
  else if (temp->subtype == TINSTANTSET)
    result = tpointinstset_decouple((TInstantSet *) temp, timesarr, count);
  else if (temp->subtype == TSEQUENCE)
    result = tpointseq_decouple((TSequence *) temp, timesarr, count);
  else /* temp->subtype == TSEQUENCESET */
    result = tpointseqset_decouple((TSequenceSet *) temp, timesarr, count);
  return result;
}

/*****************************************************************************/

/**
 * @ingroup libmeos_temporal_analytics
 * @brief Transform the temporal point to Mapbox Vector Tile format
 * @sqlfunc AsMVTGeom()
 */
bool
tpoint_AsMVTGeom(const Temporal *temp, const STBOX *bounds, int32_t extent,
  int32_t buffer, bool clip_geom, Datum *geom, int64 **timesarr,
  int *count)
{
  if (bounds->xmax - bounds->xmin <= 0 || bounds->ymax - bounds->ymin <= 0)
    elog(ERROR, "%s: Geometric bounds are too small", __func__);
  if (extent <= 0)
    elog(ERROR, "%s: Extent must be greater than 0", __func__);

  /* Contrary to what is done in PostGIS we do not use the following filter
   * to enable the visualization of temporal points with instant subtype.
   * PostGIS filtering adapted to MobilityDB would be as follows.

  / * Bounding box test to drop geometries smaller than the resolution * /
  STBOX box;
  temporal_set_bbox(temp, &box);
  double tpoint_width = box.xmax - box.xmin;
  double tpoint_height = box.ymax - box.ymin;
  / * We use half of the square height and width as limit: We use this
   * and not area so it works properly with lines * /
  double bounds_width = ((bounds->xmax - bounds->xmin) / extent) / 2.0;
  double bounds_height = ((bounds->ymax - bounds->ymin) / extent) / 2.0;
  if (tpoint_width < bounds_width && tpoint_height < bounds_height)
  {
    PG_FREE_IF_COPY(temp, 0);
    PG_RETURN_NULL();
  }
  */

  Temporal *temp1 = tpoint_mvt(temp, bounds, extent, buffer, clip_geom);
  if (temp1 == NULL)
    return false;

  /* Decouple the geometry and the timestamps */
  *geom = tpoint_decouple(temp1, timesarr, count);

  pfree(temp1);
  return true;
}

/*****************************************************************************/
