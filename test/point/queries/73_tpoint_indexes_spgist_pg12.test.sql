-------------------------------------------------------------------------------
--
-- This MobilityDB code is provided under The PostgreSQL License.
--
-- Copyright (c) 2016-2021, Université libre de Bruxelles and MobilityDB
-- contributors
--
-- Permission to use, copy, modify, and distribute this software and its
-- documentation for any purpose, without fee, and without a written 
-- agreement is hereby granted, provided that the above copyright notice and
-- this paragraph and the following two paragraphs appear in all copies.
--
-- IN NO EVENT SHALL UNIVERSITE LIBRE DE BRUXELLES BE LIABLE TO ANY PARTY FOR
-- DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING
-- LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION,
-- EVEN IF UNIVERSITE LIBRE DE BRUXELLES HAS BEEN ADVISED OF THE POSSIBILITY 
-- OF SUCH DAMAGE.
--
-- UNIVERSITE LIBRE DE BRUXELLES SPECIFICALLY DISCLAIMS ANY WARRANTIES, 
-- INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY
-- AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS ON
-- AN "AS IS" BASIS, AND UNIVERSITE LIBRE DE BRUXELLES HAS NO OBLIGATIONS TO 
-- PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS. 
--
-------------------------------------------------------------------------------

ANALYZE tbl_tgeompoint;
DROP INDEX IF EXISTS tbl_tgeompoint_spgist_idx;
CREATE INDEX tbl_tgeompoint_spgist_idx ON tbl_tgeompoint USING SPGIST(temp);

SELECT k FROM tbl_tgeompoint ORDER BY temp |=| geometry 'Point empty' LIMIT 3;
SELECT k FROM tbl_tgeompoint ORDER BY temp |=| tgeompoint '[Point(1 1)@2001-06-01, Point(2 2)@2001-06-02]' LIMIT 3;
SELECT k FROM tbl_tgeompoint3D ORDER BY temp |=| tgeompoint '[Point(-1 -1 -1)@2001-06-01, Point(-2 -2 -2)@2001-06-02]' LIMIT 3;

DROP INDEX tbl_tgeompoint_spgist_idx;

-------------------------------------------------------------------------------

ANALYZE tbl_tgeompoint3D;
DROP INDEX IF EXISTS tbl_tgeompoint3D_spgist_idx;
CREATE INDEX tbl_tgeompoint3D_spgist_idx ON tbl_tgeompoint3D USING SPGIST(temp);

SELECT k FROM tbl_tgeompoint3D ORDER BY temp |=| tgeompoint '[Point(1 1 1)@2001-06-01, Point(2 2 2)@2001-06-02]' LIMIT 3;

DROP INDEX tbl_tgeompoint3D_spgist_idx;

-------------------------------------------------------------------------------