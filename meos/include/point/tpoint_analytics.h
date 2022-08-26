/*****************************************************************************
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
 * @brief Analytics functions for temporal points.
 */

#ifndef __TPOINT_ANALYTICS_H__
#define __TPOINT_ANALYTICS_H__

/* PostgreSQL */
#include <postgres.h>
#include <utils/array.h>
/* MobilityDB */
#include "general/temporaltypes.h"

/*****************************************************************************/

/* Convert a temporal point from/to a trajectory geometry/geography */

extern Datum tpoint_to_geo(const Temporal *temp, bool segmentize);
extern Temporal *geo_to_tpoint(const GSERIALIZED *gs);
extern bool tpoint_to_geo_measure(const Temporal *tpoint,
  const Temporal *measure, bool segmentize, Datum *result);

/* Douglas-Peucker-like value simplification for temporal floats and points. */

extern Temporal *temporal_simplify(const Temporal *temp, bool synchronized,
  double eps_dist);

/* Segmentation */

extern ArrayType *temporal_segmentation_sws_threshold(const Temporal *temp, double threshold, unsigned int windows_length, char kernel);
extern ArrayType *temporal_segmentation_sws_percentile(const Temporal *temp, double percentile, unsigned int windows_length, char kernel);

extern ArrayType *temporal_segmentation_stable_criteria(const Temporal *temp, char *criteria);

/* Transform the temporal point to Mapbox Vector Tile format */

extern bool tpoint_AsMVTGeom(const Temporal *temp, const STBOX *bounds,
  int32_t extent, int32_t buffer, bool clip_geom, Datum *geom,
  TimestampTz **timesarr, int *count);

/*****************************************************************************/

#endif
