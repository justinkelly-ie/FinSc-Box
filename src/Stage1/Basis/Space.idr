module Stage1.Basis.Space

import Data.Nat
import Stage0.BoxInt
import Stage0.Interfaces
import Stage0.Box
import Stage0.Multiset

%default total

------------------------------------------------------------------------
-- 1. INDUCTIVE D-DIMENSIONAL SPATIAL COORDINATES (SpaceCoord dim)
------------------------------------------------------------------------

||| Inductive D-dimensional discrete spatial coordinate site.
public export
data SpaceCoord : (dim : Nat) -> Type where
  PointSite : SpaceCoord 0
  ConsSite  : Nat -> SpaceCoord dim -> SpaceCoord (S dim)

-- Canonical Wildberger Coordinate Aliases:
public export
Unixel : Type
Unixel = SpaceCoord 1

public export
Pixel : Type
Pixel = SpaceCoord 2

public export
VoxelSite : Type
VoxelSite = SpaceCoord 3

public export
BoxelSite : Type
BoxelSite = SpaceCoord 4

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS
------------------------------------------------------------------------

public export
mkUnixel : Nat -> Unixel
mkUnixel x = ConsSite x PointSite

public export
mkPixel : Nat -> Nat -> Pixel
mkPixel r c = ConsSite r (ConsSite c PointSite)

public export
mkVoxelSite : Nat -> Nat -> Nat -> VoxelSite
mkVoxelSite x y z = ConsSite x (ConsSite y (ConsSite z PointSite))

public export
mkBoxelSite : Nat -> Nat -> Nat -> Nat -> BoxelSite
mkBoxelSite x y z t = ConsSite x (ConsSite y (ConsSite z (ConsSite t PointSite)))

------------------------------------------------------------------------
-- 3. COORDINATE ACCESSORS & OPERATIONS
------------------------------------------------------------------------

public export
voxelX : VoxelSite -> Nat
voxelX (ConsSite x _) = x

public export
voxelY : VoxelSite -> Nat
voxelY (ConsSite _ (ConsSite y _)) = y

public export
voxelZ : VoxelSite -> Nat
voxelZ (ConsSite _ (ConsSite _ (ConsSite z _))) = z

public export
addVoxelSite : VoxelSite -> VoxelSite -> VoxelSite
addVoxelSite (ConsSite x1 (ConsSite y1 (ConsSite z1 PointSite)))
             (ConsSite x2 (ConsSite y2 (ConsSite z2 PointSite))) =
  mkVoxelSite (x1 + x2) (y1 + y2) (z1 + z2)

public export
dotVoxelSite : VoxelSite -> VoxelSite -> Nat
dotVoxelSite v1 v2 =
  (voxelX v1 * voxelX v2) + (voxelY v1 * voxelY v2) + (voxelZ v1 * voxelZ v2)

public export
quadranceVoxelSite : VoxelSite -> Nat
quadranceVoxelSite v = dotVoxelSite v v

------------------------------------------------------------------------
-- 4. EQUALITY & ORDERING
------------------------------------------------------------------------

public export
{dim : Nat} -> Eq (SpaceCoord dim) where
  PointSite == PointSite = True
  (ConsSite x1 r1) == (ConsSite x2 r2) = x1 == x2 && r1 == r2

public export
{dim : Nat} -> Ord (SpaceCoord dim) where
  compare PointSite PointSite = EQ
  compare (ConsSite x1 r1) (ConsSite x2 r2) =
    case compare x1 x2 of
      EQ => compare r1 r2
      other => other

public export
{dim : Nat} -> DiscreteCoord (SpaceCoord dim) where

------------------------------------------------------------------------
-- 5. D-DIMENSIONAL SPATIAL MULTISETS (Space dim)
------------------------------------------------------------------------

||| D-dimensional discrete space multiset:
||| An MSetBox over spatial sites in SpaceCoord dim.
public export
Space : (dim : Nat) -> Type
Space dim = MSetBox (SpaceCoord dim)

-- Canonical Wildberger Dimensional Multiset Aliases:
public export
PointMSet : Type
PointMSet = Space 0

public export
Vexel : Type
Vexel = Space 1

public export
PixelMSet : Type
PixelMSet = Space 2

public export
Voxel : Type
Voxel = Space 3

public export
Boxel : Type
Boxel = Space 4

------------------------------------------------------------------------
-- 6. INDUCTIVE DIMENSIONAL LIFTER
------------------------------------------------------------------------

||| Inductive site lift: injects a D-dimensional site into (D + 1) dimensions.
public export
liftSite : Nat -> SpaceCoord dim -> SpaceCoord (S dim)
liftSite x s = ConsSite x s

||| Inductive spatial multiset pushforward:
||| Lifts a multiset from Space D to Space (D + 1) along a new axis.
public export
liftSpace : {dim : Nat} -> Nat -> Space dim -> Space (S dim)
liftSpace nextAxis m =
  pushforwardMSet (\s => ConsSite nextAxis s) m
