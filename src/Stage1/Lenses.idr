module Stage1.Lenses

import Data.Vect
import public Stage0.BoxInt
import public Stage0.Box
import public Stage0.Multiset
import public Stage0.HereditaryMSet
import public Stage1.Views
import public Stage1.ProjectiveRotation

%default total

------------------------------------------------------------------------
-- 1. RELATIVISTIC MASS DEFECT UNDER DUAL-CHANNEL VIEWS
------------------------------------------------------------------------

||| Relativistic Mass Defect Decomposition:
||| Separates the positive kinetic/valence rest mass from motion
||| from the negative internal binding defect from dipole collisions.
public export
record MassDefectReport where
  constructor MkMassDefectReport
  valenceRestMass : BoxInt
  bindingDefect   : BoxInt
  effectiveMass   : BoxInt

||| Evaluates the exact mass defect of a dual-channel multiset:
||| decomposes state into (M_+, M_-), computes positive valence mass,
||| internal binding defect from M_-, and effective physical mass.
public export
massDefectOf : PureMultiset -> MassDefectReport
massDefectOf m =
  let ch  = splitChannels m
      vM  = sumHMSet ch.posChannel
      bM  = sumHMSet ch.negChannel
      eff = subBox vM bM
  in MkMassDefectReport vM bM eff

------------------------------------------------------------------------
-- 2. GEOMETRIC ROTATION LENS (EXTERNAL OBSERVER FRAME)
------------------------------------------------------------------------

||| External Geometric Rotation Lens:
||| Encapsulates an observer reference frame under a Wildberger projective rotation proportion.
||| Keeps spatial orientation completely decoupled from the underlying multiset storage.
public export
record RotationLens where
  constructor MkRotationLens
  proportion : ProjectiveProportion

public export
Eq RotationLens where
  (MkRotationLens p1) == (MkRotationLens p2) = p1 == p2

public export
Show RotationLens where
  show (MkRotationLens p) = "RotationLens " ++ show p

||| Canonical unrotated identity observer frame.
public export
identityLens : RotationLens
identityLens = MkRotationLens idProportion

||| O(1) Composition of two rotation lenses via projective quaternion proportion multiplication:
||| lens2 * lens1 (applies lens1 first, then lens2).
public export
composeLens : RotationLens -> RotationLens -> RotationLens
composeLens (MkRotationLens p2) (MkRotationLens p1) =
  MkRotationLens (composeProportion p2 p1)

||| O(1) Inverse observer lens: [x : -t : -r : -s].
public export
inverseLens : RotationLens -> RotationLens
inverseLens (MkRotationLens p) =
  MkRotationLens (inverseProportion p)

||| Passive Zero-Allocation Coordinate Query:
||| Samples field density at point v through the observer frame in O(log N)
||| by querying the underlying multiset at the inverse-rotated coordinate R^{-1}(v).
public export
lookupWithLens : RotationLens -> Vect 3 BoxInt -> Carrier (Vect 3 BoxInt) -> BoxInt
lookupWithLens (MkRotationLens p) v m =
  lookupBox (rotateVectorScaled (inverseProportion p) v) m

||| Deferred Active Materialization:
||| Pushes the underlying multiset forward into a new canonical Carrier
||| when, and only when, an actual physical state or particle freeze-out is required.
public export
materializeWithLens : RotationLens -> Carrier (Vect 3 BoxInt) -> Carrier (Vect 3 BoxInt)
materializeWithLens (MkRotationLens p) m =
  pushforwardRotation3 p m

