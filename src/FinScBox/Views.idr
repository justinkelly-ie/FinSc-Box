module FinScBox.Views

import public FinScBox.HereditaryMSet

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
antiBoxLoop : QuantumMultiplicity c => Nat -> HereditaryMSet c -> AntiBoxView c
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
viewAsAntiBox : QuantumMultiplicity c => HereditaryMSet c -> AntiBoxView c
viewAsAntiBox m@(MkHMSet tree) = antiBoxLoop (S (boxNodeCount tree)) m

------------------------------------------------------------------------
-- 2. DUAL-CHANNEL VIEW (DISJOINT MATTER M_+ & ANTIMATTER M_- CHANNELS)
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

||| Boolean check that  () and  () share zero active keys.
public export
disjointDualSupports : MultisetWeight c => DualChannelView c -> Bool
disjointDualSupports (MkDualChannels p n) = isHMBoxLeaf (hadamardHMSet p n)
