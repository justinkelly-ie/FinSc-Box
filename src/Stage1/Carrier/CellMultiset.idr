module Stage1.Carrier.CellMultiset

import Stage0.BoxInt
import Stage0.Multiset
import public Stage1.Basis.CoordCell

%default total

------------------------------------------------------------------------
-- 1. D-DIMENSIONAL SPATIAL CELLMULTISET
------------------------------------------------------------------------

||| A CellMultiset is a Carrier over D-dimensional coordinate basis cells (CoordCell dim).
public export
CellMultiset : (dim : Nat) -> Type
CellMultiset dim = Carrier (CoordCell dim)

||| 1D Vector Multiset (Vexel).
public export
Vexel : Type
Vexel = CellMultiset 1

||| 2D Matrix Multiset (Maxel).
public export
Maxel : Type
Maxel = CellMultiset 2

||| 3D Volume Multiset (Boxel).
public export
Boxel : Type
Boxel = CellMultiset 3

||| 4D Spacetime Multiset (HyperBoxel).
public export
HyperBoxel : Type
HyperBoxel = CellMultiset 4
