module FinScBox.Multiset

import Data.Fin
import Data.Nat
import Data.List
import public FinScBox.Interfaces
import public FinScBox.BoxInt
import public FinScBox.Box

%default total

------------------------------------------------------------------------
-- FIRST-CLASS AVL MULTISETS (`MSet m k = Box m k`, `MSetBox k = MSet BoxInt k`)
------------------------------------------------------------------------

||| Canonical multiplicity-parameterised coordinate multiset (`MSet m k = Box m k`)
||| backed by height-cached AVL trees in `FinScBox.Box`.
public export
MSet : (m : Type) -> (k : Type) -> Type
MSet m k = Box m k

||| Canonical coordinate-indexed multiset with signed `BoxInt` multiplicities (`MSet BoxInt k`).
public export
MSetBox : Type -> Type
MSetBox k = MSet BoxInt k

||| Empty multiset over coordinate domain `k`.
public export
emptyMSet : MSetBox k
emptyMSet = BoxLeaf

||| Canonical empty `MSetBox a` (`Box BoxInt a`), preserving the `{a}` implicit name.
public export
emptyBox : {0 a : Type} -> MSetBox a
emptyBox = BoxLeaf

||| Direct O(1) singleton construction of an `MSetBox k` without intermediate List allocation.
public export
singletonMSet : k -> BoxInt -> MSetBox k
singletonMSet = singletonBox

||| Creates a singleton multiset in O(1) without Ord constraint.
public export
unixelBox : a -> BoxInt -> MSetBox a
unixelBox = singletonMSet

||| Lookups the signed BoxInt multiplicity at coordinate `c` in O(log N) time.
public export
lookupMSet : DiscreteCoord k => k -> MSetBox k -> BoxInt
lookupMSet = lookupBox

||| Pointwise multiset addition (AddM) over MSetBox k in O(N log N) time.
public export
addMSet : DiscreteCoord k => MSetBox k -> MSetBox k -> MSetBox k
addMSet = unionBox

||| Pointwise multiset subtraction (SubM) over MSetBox k in O(N log N) time.
public export
subMSet : DiscreteCoord k => MSetBox k -> MSetBox k -> MSetBox k
subMSet = subBox

||| Scalar multiplication of an MSetBox k by a BoxInt factor.
public export
scaleMSet : BoxInt -> MSetBox k -> MSetBox k
scaleMSet = scaleBox

||| Pointwise Hadamard product (HadamardM) over MSetBox k in O(N log N) time.
public export
hadamardMSet : DiscreteCoord k => MSetBox k -> MSetBox k -> MSetBox k
hadamardMSet = hadamardBox

||| Multiset Symmetric Difference Information Distance.
public export
boxSymmetricDifference : Ord a => MSetBox a -> MSetBox a -> Nat
boxSymmetricDifference a b =
  let diff = subBox a b
  in foldBoxTreeL (\acc, (_, w) => acc + boxToNat (absBox w)) 0 diff

||| Canonical inner product (DotStatic) between two MSetBox k multisets in O(N log N) time.
public export
dotMSet : DiscreteCoord k => MSetBox k -> MSetBox k -> BoxInt
dotMSet = dotBox

||| Cartesian outer product (OuterM): MSetBox k1 -> MSetBox k2 -> MSetBox (k1, k2).
public export
outerMSet : (DiscreteCoord k1, DiscreteCoord k2) => MSetBox k1 -> MSetBox k2 -> MSetBox (k1, k2)
outerMSet = tensorBox

||| Right index contraction / marginalization (ContractR):
||| Sums out k2 to project MSetBox (k1, k2) -> MSetBox k1 (relational GROUP BY k1).
public export
contractR : PairCoord k1 k2 => MSetBox (k1, k2) -> MSetBox k1
contractR = contractRBox

||| Left index contraction / marginalization (ContractL):
||| Sums out k1 to project MSetBox (k1, k2) -> MSetBox k2 (relational GROUP BY k2).
public export
contractL : PairCoord k1 k2 => MSetBox (k1, k2) -> MSetBox k2
contractL = contractLBox

||| Coordinate pushforward (f_* / aggregate): re-indexes an MSetBox k1 along f : k1 -> k2,
||| summing multiplicities of colliding coordinates in k2.
public export
pushforwardMSet : DiscreteCoord k2 => (k1 -> k2) -> MSetBox k1 -> MSetBox k2
pushforwardMSet = mapBox

||| Coordinate pullback (f^* / zoomInMSet): expands each coarse coordinate k1 into a fine
||| multiset fiber MSetBox k2, scaling each fiber by the coarse site's multiplicity and summing.
public export
pullbackMSet : DiscreteCoord k2 => (k1 -> MSetBox k2) -> MSetBox k1 -> MSetBox k2
pullbackMSet fiberFn m =
  foldBox (\k1, w1, acc => addMSet acc (scaleMSet w1 (fiberFn k1))) emptyMSet m

public export
zoomOutMSet : DiscreteCoord k2 => (k1 -> k2) -> MSetBox k1 -> MSetBox k2
zoomOutMSet = pushforwardMSet

public export
zoomInMSet : DiscreteCoord k2 => (k1 -> MSetBox k2) -> MSetBox k1 -> MSetBox k2
zoomInMSet = pullbackMSet

||| Pair coordinate transposition: swaps (a, b) -> (b, a).
public export
transposeMSet : (DiscreteCoord a, DiscreteCoord b) => MSetBox (a, b) -> MSetBox (b, a)
transposeMSet = transposeBox

||| Pixel-fusion multiset contraction: [a, b1] * [b2, c] -> [a, c] where b1 == b2.
public export
composeMSet : (DiscreteCoord a, DiscreteCoord b, DiscreteCoord c) =>
              MSetBox (a, b) -> MSetBox (b, c) -> MSetBox (a, c)
composeMSet = composeBox

||| Trace of a square 2D multiset: sums multiplicities on the diagonal a1 == a2.
public export
traceMSet : DiscreteCoord a => MSetBox (a, a) -> BoxInt
traceMSet = traceBox

||| Diagonal projection mask: retains only entries on the coincidence diagonal a1 == a2.
public export
diagMaskMSet : DiscreteCoord a => MSetBox (a, a) -> MSetBox (a, a)
diagMaskMSet = diagMaskBox

||| Partial contraction / reduced composite multiset: M * M^T.
public export
maxelReducedDensity : (DiscreteCoord a, DiscreteCoord b) =>
                      MSetBox (a, b) -> MSetBox (a, a)
maxelReducedDensity m = composeMSet m (transposeMSet m)

||| Bipartite contraction norms: returns (Tr((M * M^T)^2), ||M||_2^4).
public export
maxelTraceSquare : (DiscreteCoord a, DiscreteCoord b) =>
                   MSetBox (a, b) -> (BoxInt, BoxInt)
maxelTraceSquare m =
  let q2     = dotMSet m m
      rho    = maxelReducedDensity m
      trRho2 = dotMSet rho rho
  in (trRho2, q2 * q2)

public export
buildOneMSet : {0 k : Type} -> FiniteCoord k
            => (rem : Nat) -> (acc : MSetBox k) -> MSetBox k
buildOneMSet Z     acc = acc
buildOneMSet (S r) acc = case isLT r (cardinality {k}) of
  Yes lt => buildOneMSet r (setBox (fromIndex (natToFinLT r @{lt})) (intToBoxInt 1) acc)
  No _   => acc

||| Universal identity mask (OneM) assigning multiplicity 1 to every coordinate in `FiniteCoord k`.
public export
oneMSet : {0 k : Type} -> FiniteCoord k => MSetBox k
oneMSet = buildOneMSet (cardinality {k}) BoxLeaf

||| Cauchy convolution (MulStatic) on MSetBox k over any MonoidCoord k.
public export
mulMSet : MonoidCoord k => MSetBox k -> MSetBox k -> MSetBox k
mulMSet = mulBoxWith

public export
convMSet : MonoidCoord k => MSetBox k -> MSetBox k -> MSetBox k
convMSet = mulMSet

------------------------------------------------------------------------
-- CANONICAL MULTISET STOICHIOMETRIC REACTIONS & DIFFERENCES
------------------------------------------------------------------------

||| Bounded Multiset Difference (Monus): (M1 \ M2)(x) = max(0, M1(x) - M2(x)).
public export
boundedDiffMSet : DiscreteCoord k => MSetBox k -> MSetBox k -> MSetBox k
boundedDiffMSet m1 m2 =
  foldBoxTreeL (\acc, (x, w1) =>
    let w2 = lookupMSet x m2
        remW = FinScBox.BoxInt.subBox w1 w2
    in if remW > intToBoxInt 0 then setBox x remW acc else acc) BoxLeaf m1

||| Multiset Symmetric Difference: (M1 Δ M2)(x) = |M1(x) - M2(x)|.
public export
symmetricDiffMSet : DiscreteCoord k => MSetBox k -> MSetBox k -> MSetBox k
symmetricDiffMSet m1 m2 = mapBoxWeight absBox (subBox m1 m2)

||| Computes the stoichiometric reaction quotient on indexed multisets:
||| maximum number of times `reactants` is contained in `state`.
public export
reactionQuotientMSet : DiscreteCoord k => (reactants : MSetBox k) -> MSetBox k -> BoxInt
reactionQuotientMSet BoxLeaf _ = intToBoxInt 0
reactionQuotientMSet _ BoxLeaf = intToBoxInt 0
reactionQuotientMSet reactants state =
  let res = foldBoxTreeL (\mMin, (x, w) =>
              if w <= intToBoxInt 0
                then mMin
                else let q = divBox (lookupMSet x state) w
                         qClamped = if q < intToBoxInt 0 then intToBoxInt 0 else q
                     in case mMin of
                          Nothing => Just qClamped
                          Just cur => Just (if qClamped < cur then qClamped else cur))
              Nothing reactants
  in case res of
       Nothing => intToBoxInt 0
       Just q => q

||| Executes up to `maxReactions` stoichiometric reactions (`reactants -> products`)
||| on an indexed `MSetBox k` state: `state' = (state \ (k * reactants)) <+> (k * products)`.
||| Returns `(updatedState, actualReactionsExecuted)`.
public export
reactMSetBox :
  DiscreteCoord k =>
  (maxReactions : BoxInt) ->
  (reactants : MSetBox k) ->
  (products : MSetBox k) ->
  MSetBox k ->
  (MSetBox k, BoxInt)
reactMSetBox maxReactions reactants products state =
  if maxReactions <= intToBoxInt 0
    then (state, intToBoxInt 0)
    else case state of
           BoxLeaf => (state, intToBoxInt 0)
           _ =>
             let avail = reactionQuotientMSet reactants state
                 k = if maxReactions < avail then maxReactions else avail
             in if k <= intToBoxInt 0
                  then (state, intToBoxInt 0)
                  else let consumed = scaleMSet k reactants
                           produced = scaleMSet k products
                           remState = boundedDiffMSet state consumed
                           nextState = addMSet remState produced
                       in (nextState, k)

||| Cross-tier stoichiometric transmutation (`reactants` in `MSetBox k1` -> `products` in `MSetBox k2`):
||| Consumes `k * reactants` from `sourceState` and adds `k * products` to `targetState`.
||| Returns `(nextSourceState, nextTargetState, actualReactionsExecuted)`.
public export
transmuteMSet :
  (DiscreteCoord k1, DiscreteCoord k2) =>
  (maxReactions : BoxInt) ->
  (reactants : MSetBox k1) ->
  (products : MSetBox k2) ->
  MSetBox k1 ->
  MSetBox k2 ->
  (MSetBox k1, MSetBox k2, BoxInt)
transmuteMSet maxReactions reactants products sourceState targetState =
  if maxReactions <= intToBoxInt 0
    then (sourceState, targetState, intToBoxInt 0)
    else case sourceState of
           BoxLeaf => (sourceState, targetState, intToBoxInt 0)
           _ =>
             let avail = reactionQuotientMSet reactants sourceState
                 k = if maxReactions < avail then maxReactions else avail
             in if k <= intToBoxInt 0
                  then (sourceState, targetState, intToBoxInt 0)
                  else let consumed = scaleMSet k reactants
                           produced = scaleMSet k products
                           nextSource = boundedDiffMSet sourceState consumed
                           nextTarget = addMSet targetState produced
                       in (nextSource, nextTarget, k)

||| Splits a signed `MSetBox k` into disjoint positive (`M_+`) and negative (`M_-`) channels,
||| with positive multiplicities in each channel: `posBox` has entries with `w > 0`, `negBox` has `-w` for `w < 0`.
public export
splitMSetChannels : DiscreteCoord k => MSetBox k -> (MSetBox k, MSetBox k)
splitMSetChannels = splitBoxChannels

||| Sum of signed multiplicities in an `MSetBox k`: \sum w_i
public export
multiplicitySignedSum : MSetBox k -> Integer
multiplicitySignedSum = foldBox (\_, w, acc => acc + unwrapBox w) 0

public export
msetSignedSum : MSetBox k -> Integer
msetSignedSum = multiplicitySignedSum

||| L1 norm (total absolute multiplicity) in an `MSetBox k`: \sum |w_i|
public export
multiplicityL1 : MSetBox k -> Integer
multiplicityL1 = foldBox (\_, w, acc => acc + abs (unwrapBox w)) 0

public export
msetL1 : MSetBox k -> Integer
msetL1 = multiplicityL1

