module Stage1.Basis.CoordCell

import Data.Nat
import Stage0.BoxInt
import Stage0.Interfaces

%default total

------------------------------------------------------------------------
-- 1. INDUCTIVE D-DIMENSIONAL COORDINATE CELLS
------------------------------------------------------------------------

||| Inductive D-dimensional coordinate basis cell.
||| Avoids heap arrays or dynamic dimension checks.
public export
data CoordCell : (dim : Nat) -> Type where
  ZeroCell : CoordCell 0
  ConsCell : Nat -> CoordCell dim -> CoordCell (S dim)

public export
Unixel : Type
Unixel = CoordCell 1

public export
Pixel : Type
Pixel = CoordCell 2

public export
Voxel : Type
Voxel = CoordCell 3

public export
Tesseract : Type
Tesseract = CoordCell 4

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS
------------------------------------------------------------------------

public export
mkUnixel : Nat -> Unixel
mkUnixel x = ConsCell x ZeroCell

public export
mkPixel : Nat -> Nat -> Pixel
mkPixel r c = ConsCell r (ConsCell c ZeroCell)

public export
mkVoxel : Nat -> Nat -> Nat -> Voxel
mkVoxel x y z = ConsCell x (ConsCell y (ConsCell z ZeroCell))

public export
mkTesseract : Nat -> Nat -> Nat -> Nat -> Tesseract
mkTesseract x y z t = ConsCell x (ConsCell y (ConsCell z (ConsCell t ZeroCell)))

------------------------------------------------------------------------
-- 3. COORDINATE ACCESSORS
------------------------------------------------------------------------

public export
voxelX : Voxel -> Nat
voxelX (ConsCell x _) = x

public export
voxelY : Voxel -> Nat
voxelY (ConsCell _ (ConsCell y _)) = y

public export
voxelZ : Voxel -> Nat
voxelZ (ConsCell _ (ConsCell _ (ConsCell z _))) = z

------------------------------------------------------------------------
-- 4. EQUALITY & ORDERING
-- ---------------------------------------------------------------------

public export
{dim : Nat} -> Eq (CoordCell dim) where
  ZeroCell == ZeroCell = True
  (ConsCell x1 r1) == (ConsCell x2 r2) = x1 == x2 && r1 == r2

public export
{dim : Nat} -> Ord (CoordCell dim) where
  compare ZeroCell ZeroCell = EQ
  compare (ConsCell x1 r1) (ConsCell x2 r2) =
    case compare x1 x2 of
      EQ => compare r1 r2
      other => other

public export
{dim : Nat} -> DiscreteCoord (CoordCell dim) where

------------------------------------------------------------------------
-- 5. VOXEL GEOMETRIC OPERATIONS
------------------------------------------------------------------------

public export
addVoxel : Voxel -> Voxel -> Voxel
addVoxel (ConsCell x1 (ConsCell y1 (ConsCell z1 ZeroCell)))
         (ConsCell x2 (ConsCell y2 (ConsCell z2 ZeroCell))) =
  mkVoxel (x1 + x2) (y1 + y2) (z1 + z2)

public export
dotVoxel : Voxel -> Voxel -> Nat
dotVoxel v1 v2 =
  (voxelX v1 * voxelX v2) + (voxelY v1 * voxelY v2) + (voxelZ v1 * voxelZ v2)

public export
quadranceVoxel : Voxel -> Nat
quadranceVoxel v = dotVoxel v v
