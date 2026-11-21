module Stage1.Lenses

import Data.Vect
import public Stage0.BoxInt
import public Stage0.Box
import public Stage0.Multiset
import public Stage0.HereditaryMSet
import public Stage1.ProjectiveRotation
import public Stage1.BlackRedZoom
import public Stage1.Basis.Time

%default total

------------------------------------------------------------------------
-- 1. GEOMETRIC ROTATION LENS (EXTERNAL OBSERVER FRAME)
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
lookupWithLens : RotationLens -> Vect 3 BoxInt -> MSetBox (Vect 3 BoxInt) -> BoxInt
lookupWithLens (MkRotationLens p) v m =
  lookupBox (rotateVectorScaled (inverseProportion p) v) m

||| Deferred Active Materialization:
||| Pushes the underlying multiset forward into a new canonical MSetBox
||| when, and only when, an actual physical state or particle freeze-out is required.
public export
materializeWithLens : RotationLens -> MSetBox (Vect 3 BoxInt) -> MSetBox (Vect 3 BoxInt)
materializeWithLens (MkRotationLens p) m =
  pushforwardRotation3 p m

------------------------------------------------------------------------
-- 3. NON-PERTURBING EXTERNAL OBSERVATION & SPACE/TIME ZOOM LENSES
------------------------------------------------------------------------

||| Compile-time non-interference witness for external observation of a linear state `1 uIn`:
||| returns the linear handle `1 uOut`, an unrestricted external projection `val : out`,
||| and an erased `QTT 0` identity proof `0 same : uOut = uIn` forbidding mutation.
public export
data PureObservation : {0 a : Type} -> (0 uIn : a) -> (out : Type) -> Type where
  MkPureObs : (1 uOut : a) -> (val : out) -> (0 same : uOut = uIn) -> PureObservation uIn out

||| Passive external lens supporting Space zoom (`zoomSpace`), Time zoom (`zoomTime`),
||| and `Time` horizon tagging without ever modifying the observed universe.
public export
record ExternalLens (src : Type) (out : Type) where
  constructor MkExternalLens
  focus       : src -> PureMultiset
  spaceShift  : BlackRedMSet
  timeShift   : BlackRedMSet
  timeHorizon : Time
  project     : PureMultiset -> out

||| Evaluates an `ExternalLens` strictly on a passive focus projection (`src` untouched).
||| Short-circuits `zoomTime` and `zoomSpace` when shifts equal `zeroShift`.
public export
applyExternalLens : ExternalLens src out -> src -> out
applyExternalLens lens s =
  let focused  = lens.focus s
      tShifted = if lens.timeShift == zeroShift then focused else zoomTime lens.timeShift focused
      sShifted = if lens.spaceShift == zeroShift then tShifted else zoomSpace lens.spaceShift tShifted
  in lens.project sShifted

||| Identity-zoom external lens over a `PureMultiset` focus.
public export
directPureLens : (PureMultiset -> out) -> ExternalLens PureMultiset out
directPureLens proj = MkExternalLens (\m => m) zeroShift zeroShift OpenFuture proj

||| Space/Time-zoomed external lens targeting a custom focus extractor.
public export
zoomedExternalLens :
  (src -> PureMultiset) ->
  (spaceShift : BlackRedMSet) ->
  (timeShift  : BlackRedMSet) ->
  (horizon    : Time) ->
  (PureMultiset -> out) ->
  ExternalLens src out
zoomedExternalLens = MkExternalLens

public export
0 prfExternalLensZeroShiftIsId :
  Stage1.Lenses.applyExternalLens (Stage1.Lenses.directPureLens (\m => m)) Stage1.BlackRedZoom.sampleUnitPairMSet
  = Stage1.BlackRedZoom.sampleUnitPairMSet
prfExternalLensZeroShiftIsId = Refl

public export
0 prfExternalLensSpaceZoomMatches :
  Stage1.Lenses.applyExternalLens
    (MkExternalLens (\m => m) (blackShift 1) Stage1.BlackRedZoom.zeroShift (RetroTime 1) (\m => m))
    Stage1.BlackRedZoom.sampleUnitPairMSet
  = zoomSpace (blackShift 1) Stage1.BlackRedZoom.sampleUnitPairMSet
prfExternalLensSpaceZoomMatches = Refl

