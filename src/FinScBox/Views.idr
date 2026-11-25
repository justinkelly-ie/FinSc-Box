module FinScBox.Views

import Data.Nat
import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.HereditaryMSet

%default total

------------------------------------------------------------------------
-- 1. ANTI-BOX VIEW (BLACK +1 / RED -1 QUANTUM STEPPING)
------------------------------------------------------------------------

||| View exposing Wildberger's Black (`+1`) and Red (`-1`) box quanta
||| one single unit at a time directly over `HereditaryMSet c`.
public export
data AntiBoxView : (c : Type) -> Type where
  EmptyVacuum : AntiBoxView c
  PopBlackBox : (term : HereditaryMSet c) -> (rest : HereditaryMSet c) -> AntiBoxView c
  PopRedBox   : (term : HereditaryMSet c) -> (rest : HereditaryMSet c) -> AntiBoxView c

public export
antiBoxLoop : QuantumCarrier c => Nat -> HereditaryMSet c -> AntiBoxView c
antiBoxLoop Z _ = EmptyVacuum
antiBoxLoop (S rem) (MkHMSet BoxLeaf) = EmptyVacuum
antiBoxLoop (S rem) (MkHMSet tree@(BoxNode _ _ _ _ _)) =
  case extractMinBox tree of
    Nothing => EmptyVacuum
    Just (term, weight, tailTree) =>
      case peelQuantum weight of
        Nothing => antiBoxLoop rem (MkHMSet tailTree)
        Just (Left remW) =>
          let restBox = if isZero remW then tailTree else setBox term remW tailTree
          in PopBlackBox term (MkHMSet restBox)
        Just (Right remW) =>
          let restBox = if isZero remW then tailTree else setBox term remW tailTree
          in PopRedBox term (MkHMSet restBox)

||| Total covering function peeling one `+1` Black or `-1` Red quantum from the minimum key.
public export
viewAsAntiBox : QuantumCarrier c => HereditaryMSet c -> AntiBoxView c
viewAsAntiBox m@(MkHMSet tree) = antiBoxLoop (S (boxNodeCount tree)) m

------------------------------------------------------------------------
-- 2. DUAL-CHANNEL VIEW (DISJOINT POSITIVE & NEGATIVE CHANNELS)
------------------------------------------------------------------------

||| Splits a signed `HereditaryMSet c` into two disjoint positive-magnitude channels.
public export
record DualChannelView (c : Type) where
  constructor MkDualChannels
  posChannel : HereditaryMSet c
  negChannel : HereditaryMSet c

||| Projects a signed multiset into `(M_+, M_-)` using `compare weight zeroWeight`.
public export
splitChannels : MultisetWeight c => HereditaryMSet c -> DualChannelView c
splitChannels (MkHMSet box) =
  let (pBox, nBox) = splitBoxChannels box
  in MkDualChannels (MkHMSet pBox) (MkHMSet nBox)

||| Recombines `(M_+, M_-)` via `subHMSet`, annihilating any overlapping keys.
public export
interactChannels : MultisetWeight c => DualChannelView c -> HereditaryMSet c
interactChannels (MkDualChannels posM negM) = subHMSet posM negM

public export
isHMBoxLeaf : HereditaryMSet c -> Bool
isHMBoxLeaf (MkHMSet BoxLeaf) = True
isHMBoxLeaf _                 = False

||| Boolean check that `posChannel` and `negChannel` share zero active keys.
public export
disjointDualSupports : MultisetWeight c => DualChannelView c -> Bool
disjointDualSupports (MkDualChannels p n) = isHMBoxLeaf (hadamardHMSet p n)

------------------------------------------------------------------------
-- 3. STREAMING PEEL-WORK REDUCTIONS (`Time = Peeling Work`)
------------------------------------------------------------------------

||| Work executed by streaming quantum-by-quantum reduction over a multiset:
||| - `workSteps`     : Quantum-peeling steps (`PopBlackBox`/`PopRedBox` across nesting levels)
||| - `annihilations` : Paired opposite quanta cancelled (`[+1, -1] = []`)
||| - `residualL1`    : Remaining L1 magnitude after zero-pruning
public export
record StreamWorkReport where
  constructor MkStreamWorkReport
  workSteps     : Nat
  annihilations : Nat
  residualL1    : Nat

public export
Eq StreamWorkReport where
  a == b = a.workSteps == b.workSteps && a.annihilations == b.annihilations && a.residualL1 == b.residualL1

public export
Show StreamWorkReport where
  show w =
    "StreamWork(steps=" ++ show w.workSteps ++
    ", annih=" ++ show w.annihilations ++
    ", L1=" ++ show w.residualL1 ++ ")"

mutual
  ||| Peels every outer quantum of a `HereditaryMSet c` via `viewAsAntiBox`,
  ||| recursively charging nested key peels so `zoomSpace (blackShift k)` increases stream work.
  public export
  peelQuantaWorkLoop : QuantumCarrier c => Nat -> Nat -> HereditaryMSet c -> Nat
  peelQuantaWorkLoop _         Z         _ = 0
  peelQuantaWorkLoop depthFuel (S qFuel) m =
    case viewAsAntiBox m of
      EmptyVacuum => 0
      PopBlackBox term rest =>
        S (peelNestedWork depthFuel term + peelQuantaWorkLoop depthFuel qFuel rest)
      PopRedBox term rest =>
        S (peelNestedWork depthFuel term + peelQuantaWorkLoop depthFuel qFuel rest)

  public export
  peelNestedWork : QuantumCarrier c => Nat -> HereditaryMSet c -> Nat
  peelNestedWork Z         _                 = 0
  peelNestedWork _         (MkHMSet BoxLeaf) = 0
  peelNestedWork (S dFuel) m@(MkHMSet b)     =
    peelQuantaWorkLoop dFuel (S (collectSupportStats b).totalMass) m

||| Evaluates streaming quantum-peeling work on any `QuantumCarrier c => HereditaryMSet c`.
||| Empty vacuum `[]` requires strictly `0` work steps.
public export
streamPeelWorkHMSet : QuantumCarrier c => HereditaryMSet c -> StreamWorkReport
streamPeelWorkHMSet (MkHMSet BoxLeaf) = MkStreamWorkReport 0 0 0
streamPeelWorkHMSet m@(MkHMSet b) =
  let resL1 = (collectSupportStats b).totalMass
      steps = peelNestedWork (hmDepth m) m
  in MkStreamWorkReport steps 0 resL1

||| Exact `O(tree-size)` structural peel-step counter matching `streamPeelWorkHMSet` without
||| unary quantum-by-quantum loops.
public export
fastPeelWorkLoop : MultisetWeight c => Nat -> HereditaryMSet c -> Nat
fastPeelWorkLoop Z _ = 0
fastPeelWorkLoop _ (MkHMSet BoxLeaf) = 0
fastPeelWorkLoop (S dFuel) (MkHMSet b) =
  foldBox (\k, w, acc => acc + weightMagnitude w * S (fastPeelWorkLoop dFuel k)) 0 b

||| Computes the exact nested peel-work step count of any `HereditaryMSet c` in `O(nodes)`.
public export
fastPeelWorkHMSet : MultisetWeight c => HereditaryMSet c -> Nat
fastPeelWorkHMSet m = fastPeelWorkLoop (hmDepth m) m

||| Merges two `HereditaryMSet c` operands via `addHMSet`, recording
||| total peeling work steps and annihilated Black/Red pairs (`[+1, -1] = []`).
public export
streamMergeWorkHMSet : QuantumCarrier c =>
                       HereditaryMSet c ->
                       HereditaryMSet c ->
                       (HereditaryMSet c, StreamWorkReport)
streamMergeWorkHMSet a b =
  let rA     = streamPeelWorkHMSet a
      rB     = streamPeelWorkHMSet b
      merged = addHMSet a b
      rM     = streamPeelWorkHMSet merged
      rawL1  = rA.residualL1 + rB.residualL1
      diff   = if rawL1 >= rM.residualL1 then minus rawL1 rM.residualL1 else 0
  in (merged, MkStreamWorkReport (rA.workSteps + rB.workSteps) (half diff) rM.residualL1)
