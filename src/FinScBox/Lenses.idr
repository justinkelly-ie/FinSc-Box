module FinScBox.Lenses

import FinScBox.BoxInt
import FinScBox.Box
import FinScBox.HereditaryMSet
import FinScBox.BlackRedZoom

%default total

------------------------------------------------------------------------
-- EXTERNAL NON-PERTURBING OBSERVATION (`PureObservation` & `ExternalLens`)
------------------------------------------------------------------------

||| Compile-time non-interference witness for external observation of a linear state `1 uIn`:
||| returns the linear handle `1 uOut`, an unrestricted external projection `val : out`,
||| and an erased `QTT 0` identity proof `0 same : uOut = uIn` forbidding mutation.
public export
data PureObservation : {0 a : Type} -> (0 uIn : a) -> (out : Type) -> Type where
  MkPureObs : (1 uOut : a) -> (val : out) -> (0 same : uOut = uIn) -> PureObservation uIn out

||| Passive external lens supporting Space zoom (`zoomSpace`) and Time zoom (`zoomTime`)
||| without ever modifying the observed state.
public export
record ExternalLens (src : Type) (out : Type) where
  constructor MkExternalLens
  focus      : src -> PureMultiset
  spaceShift : PureMultiset
  timeShift  : PureMultiset
  project    : PureMultiset -> out

||| Evaluates an `ExternalLens` strictly on a passive focus projection (`src` untouched).
||| Short-circuits `zoomTime` and `zoomSpace` when shifts equal `emptyHMSet`.
public export
applyExternalLens : ExternalLens src out -> src -> out
applyExternalLens lens s =
  let focused  = lens.focus s
      tShifted = if lens.timeShift == emptyHMSet then focused else zoomTime lens.timeShift focused
      sShifted = if lens.spaceShift == emptyHMSet then tShifted else zoomSpace lens.spaceShift tShifted
  in lens.project sShifted

||| Identity-zoom external lens over a `PureMultiset` focus.
public export
directPureLens : (PureMultiset -> out) -> ExternalLens PureMultiset out
directPureLens proj = MkExternalLens (\m => m) emptyHMSet emptyHMSet proj

public export
0 prfExternalLensZeroShiftIsId :
  FinScBox.Lenses.applyExternalLens (FinScBox.Lenses.directPureLens (\m => m)) FinScBox.BlackRedZoom.sampleUnitPairMSet
  = FinScBox.BlackRedZoom.sampleUnitPairMSet
prfExternalLensZeroShiftIsId = Refl

public export
0 prfExternalLensSpaceZoomMatches :
  FinScBox.Lenses.applyExternalLens
    (MkExternalLens (\m => m) (blackShift 1) FinScBox.HereditaryMSet.emptyHMSet (\m => m))
    FinScBox.BlackRedZoom.sampleUnitPairMSet
  = zoomSpace (blackShift 1) FinScBox.BlackRedZoom.sampleUnitPairMSet
prfExternalLensSpaceZoomMatches = Refl
