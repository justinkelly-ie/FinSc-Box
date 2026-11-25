module FinScBox.BlackRedZoom

import Data.Nat
import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.HereditaryMSet
import FinScBox.Views

%default total

--------------------------------------------------------------------------------
-- 1. BLACK / RED SHIFT MULTISETS (`[+1, -1] = []`)
--------------------------------------------------------------------------------

||| Constructs `n` Black (`+1`) shift quanta at the origin `[]`.
public export
blackShift : Nat -> PureMultiset
blackShift n = scalarKeyHMSet (cast n)

||| Constructs `n` Red (`-1`) shift quanta at the origin `[]`.
public export
redShift : Nat -> PureMultiset
redShift n = scalarKeyHMSet (- cast n)

--------------------------------------------------------------------------------
-- 2. MULTISET-NATIVE `zoomTime` (HORIZONTAL LAURENT SHIFT VIA `mulHMSet`)
--------------------------------------------------------------------------------

||| Horizontal scale/time shift via Laurent Cauchy multiplication (`alpha^shift * m`).
||| Adding `blackShift 1` and `redShift 1` yields `emptyHMSet = []`, so
||| `zoomTime (blackShift 1 + redShift 1) m == m` holds identically!
public export
zoomTime : (shift : PureMultiset) -> PureMultiset -> PureMultiset
zoomTime shift m =
  mulHMSet (MkHMSet (singletonBox shift (MkBoxInt 1))) m

--------------------------------------------------------------------------------
-- 3. MULTISET-NATIVE `zoomSpace` (VERTICAL NESTING / CONTRACTION VIA ANTI-BOX)
--------------------------------------------------------------------------------

||| Wraps a `PureMultiset` one hereditary bracket deeper: `M -> { M : [1] }`.
public export
wrapBox : PureMultiset -> PureMultiset
wrapBox m = MkHMSet (singletonBox m (MkBoxInt 1))

||| Contracts one hereditary bracket level: `{ k_i : [w_i] } -> \sum w_i * k_i`.
||| Exact left-inverse of `wrapBox`: `unwrapBoxLevel (wrapBox m) == m` for all `m`!
public export
unwrapBoxLevel : PureMultiset -> PureMultiset
unwrapBoxLevel (MkHMSet b) =
  foldBox (\k, w, acc => addHMSet acc (scaleHMSet w k)) emptyHMSet b

public export
zoomSpaceLoop : Nat -> PureMultiset -> PureMultiset -> PureMultiset
zoomSpaceLoop Z _ m = m
zoomSpaceLoop (S fuel) shift m =
  case viewAsAntiBox shift of
    EmptyVacuum        => m
    PopBlackBox _ rest => zoomSpaceLoop fuel rest (wrapBox m)
    PopRedBox   _ rest => zoomSpaceLoop fuel rest (unwrapBoxLevel m)

||| Vertical hereditary space shift driven strictly by a Black/Red multiset `shift`:
||| Each `+1` Black quantum in `shift` wraps `m` one structural level deeper (`wrapBox`);
||| each `-1` Red quantum unwraps `m` one structural level coarser (`unwrapBoxLevel`).
public export
zoomSpace : (shift : PureMultiset) -> PureMultiset -> PureMultiset
zoomSpace shift@(MkHMSet b) m =
  let fuel = S (collectSupportStats b).totalMass
  in zoomSpaceLoop fuel shift m

--------------------------------------------------------------------------------
-- 4. COMPILE-TIME QTT 0 ALGEBRAIC LAWS ON `zoomTime` & `zoomSpace`
--------------------------------------------------------------------------------

||| Canonical balanced unit pair `alpha^{+1} - alpha^{-1}` inside `PureMultiset`.
public export
sampleUnitPairMSet : PureMultiset
sampleUnitPairMSet =
  subHMSet (MkHMSet (singletonBox (scalarKeyHMSet 1) (MkBoxInt 1)))
           (MkHMSet (singletonBox (scalarKeyHMSet (-1)) (MkBoxInt 1)))

public export
0 prfBlackRedAnnihilates :
  addHMSet (FinScBox.BlackRedZoom.blackShift 1) (FinScBox.BlackRedZoom.redShift 1) =
  FinScBox.HereditaryMSet.emptyHMSet
prfBlackRedAnnihilates = Refl

public export
0 prfZoomTimeRoundTrip :
  (zoomTime (redShift 1) (zoomTime (blackShift 1) FinScBox.BlackRedZoom.sampleUnitPairMSet)
   == FinScBox.BlackRedZoom.sampleUnitPairMSet) = True
prfZoomTimeRoundTrip = Refl

public export
0 prfZoomTimeAnnihilatedShiftIsId :
  (zoomTime (addHMSet (blackShift 1) (redShift 1)) FinScBox.BlackRedZoom.sampleUnitPairMSet
   == FinScBox.BlackRedZoom.sampleUnitPairMSet) = True
prfZoomTimeAnnihilatedShiftIsId = Refl

public export
0 prfZoomSpaceRoundTrip :
  (zoomSpace (redShift 1) (zoomSpace (blackShift 1) FinScBox.BlackRedZoom.sampleUnitPairMSet)
   == FinScBox.BlackRedZoom.sampleUnitPairMSet) = True
prfZoomSpaceRoundTrip = Refl

public export
0 prfZoomSpaceAnnihilatedShiftIsId :
  (zoomSpace (addHMSet (blackShift 1) (redShift 1)) FinScBox.BlackRedZoom.sampleUnitPairMSet
   == FinScBox.BlackRedZoom.sampleUnitPairMSet) = True
prfZoomSpaceAnnihilatedShiftIsId = Refl
