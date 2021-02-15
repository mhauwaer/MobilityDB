/*****************************************************************************
 *
 * tpoint_spatialfuncs.sql
 * Spatial functions for temporal points.
 *
 * This MobilityDB code is provided under The PostgreSQL License.
 *
 * Copyright (c) 2020, Université libre de Bruxelles and MobilityDB
 * contributors
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

CREATE FUNCTION srid(stbox)
  RETURNS int
  AS 'MODULE_PATHNAME', 'stbox_srid'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION setSRID(stbox, srid integer)
  RETURNS stbox
  AS 'MODULE_PATHNAME', 'stbox_set_srid'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION transform(stbox, srid integer)
  RETURNS stbox
  AS 'MODULE_PATHNAME', 'stbox_transform'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION setPrecision(stbox, int)
  RETURNS stbox
  AS 'MODULE_PATHNAME', 'stbox_set_precision'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

/*****************************************************************************/

CREATE FUNCTION SRID(tgeompoint)
  RETURNS integer
  AS 'MODULE_PATHNAME', 'tpoint_srid'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION SRID(tgeogpoint)
  RETURNS integer
  AS 'MODULE_PATHNAME', 'tpoint_srid'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION setSRID(tgeompoint, srid integer)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tpoint_set_srid'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION setSRID(tgeogpoint, srid integer)
  RETURNS tgeogpoint
  AS 'MODULE_PATHNAME', 'tpoint_set_srid'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION transform(tgeompoint, srid integer)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tpoint_transform'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

-- Gauss Kruger transformation

CREATE FUNCTION transform_gk(tgeompoint)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tgeompoint_transform_gk'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION transform_gk(geometry)
  RETURNS geometry
  AS 'MODULE_PATHNAME', 'geometry_transform_gk'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

/*****************************************************************************/
-- Transformation from tgeompoint <-> tgeogpoint
-- Two versions are currently kept to show the performance gain by having
-- access to the C API

CREATE FUNCTION tgeogpointOld(tgeompoint)
  RETURNS tgeogpoint
  AS 'MODULE_PATHNAME', 'tgeompoint_to_tgeogpoint_old'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION tgeompointOld(tgeogpoint)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tgeogpoint_to_tgeompoint_old'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION tgeogpoint(tgeompoint)
  RETURNS tgeogpoint
  AS 'MODULE_PATHNAME', 'tgeompoint_to_tgeogpoint'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION tgeompoint(tgeogpoint)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tgeogpoint_to_tgeompoint'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE CAST (tgeompoint AS tgeogpoint) WITH FUNCTION tgeogpoint(tgeompoint);
CREATE CAST (tgeogpoint AS tgeompoint) WITH FUNCTION tgeompoint(tgeogpoint);

CREATE FUNCTION setprecision(tgeompoint, int)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tpoint_set_precision'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION setprecision(tgeogpoint, int)
  RETURNS tgeogpoint
  AS 'MODULE_PATHNAME', 'tpoint_set_precision'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION trajectory(tgeompoint)
  RETURNS geometry
  AS 'MODULE_PATHNAME', 'tpoint_trajectory'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION trajectory(tgeogpoint)
  RETURNS geography
  AS 'MODULE_PATHNAME', 'tpoint_trajectory'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

/*****************************************************************************/

CREATE FUNCTION length(tgeompoint)
  RETURNS float
  AS 'MODULE_PATHNAME', 'tpoint_length'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION length(tgeogpoint)
  RETURNS float
  AS 'MODULE_PATHNAME', 'tpoint_length'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION cumulativeLength(tgeompoint)
  RETURNS tfloat
  AS 'MODULE_PATHNAME', 'tpoint_cumulative_length'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION cumulativeLength(tgeogpoint)
  RETURNS tfloat
  AS 'MODULE_PATHNAME', 'tpoint_cumulative_length'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION speed(tgeompoint)
  RETURNS tfloat
  AS 'MODULE_PATHNAME', 'tpoint_speed'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION speed(tgeogpoint)
  RETURNS tfloat
  AS 'MODULE_PATHNAME', 'tpoint_speed'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION twcentroid(tgeompoint)
  RETURNS geometry
  AS 'MODULE_PATHNAME', 'tgeompoint_twcentroid'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION azimuth(tgeompoint)
  RETURNS tfloat
  AS 'MODULE_PATHNAME', 'tpoint_azimuth'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION azimuth(tgeogpoint)
  RETURNS tfloat
  AS 'MODULE_PATHNAME', 'tpoint_azimuth'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

/*****************************************************************************/

CREATE FUNCTION isSimple(tgeompoint)
  RETURNS bool
  AS 'MODULE_PATHNAME', 'tgeompoint_is_simple'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
  
CREATE FUNCTION makeSimple(tgeompoint)
  RETURNS tgeompoint[]
  AS 'MODULE_PATHNAME', 'tgeompoint_make_simple'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

/*****************************************************************************/

CREATE FUNCTION atGeometry(tgeompoint, geometry)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tpoint_at_geometry'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION minusGeometry(tgeompoint, geometry)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tpoint_minus_geometry'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION atStbox(tgeompoint, stbox)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tpoint_at_stbox'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION atStbox(tgeogpoint, stbox)
  RETURNS tgeogpoint
  AS 'MODULE_PATHNAME', 'tpoint_at_stbox'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION minusStbox(tgeompoint, stbox)
  RETURNS tgeompoint
  AS 'MODULE_PATHNAME', 'tpoint_minus_stbox'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION minusStbox(tgeogpoint, stbox)
  RETURNS tgeogpoint
  AS 'MODULE_PATHNAME', 'tpoint_minus_stbox'
  LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

/*****************************************************************************/
