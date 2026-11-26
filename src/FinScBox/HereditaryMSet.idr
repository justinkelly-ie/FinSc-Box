module FinScBox.HereditaryMSet

import Data.Nat
import public Data.DPair
import public Data.Maybe
import public Decidable.Equality
import public FinScBox.Box

%default total

------------------------------------------------------------------------
-- 1. RECURSIVE HEREDITARY MULTISET (`HereditaryMSet c` & `PureMultiset`)
------------------------------------------------------------------------

||| Unified recursive multiset container where every node is a height-cached AVL
||| `Box c (HereditaryMSet c)` of sub-multisets weighted by carrier `c`
||| (`BoxInt`, `SignedBit`, or `MultisetBit`), enforcing canonical zero-pruning (`[M, M^a] = []`).
public export
data HereditaryMSet : (c : Type) -> Type where
  MkHMSet : Box c (HereditaryMSet c) -> HereditaryMSet c

||| Canonical default alias backed by exact signed `BoxInt` multiplicities.
public export
PureMultiset : Type
PureMultiset = HereditaryMSet BoxInt

public export
emptyHMSet : HereditaryMSet c
emptyHMSet = MkHMSet BoxLeaf

||| Constructs a zero-pruned singleton `HereditaryMSet c` (`{ k : w }`, or `[]` when `isZero w`).
public export
singletonHMSet : MultisetWeight c => HereditaryMSet c -> c -> HereditaryMSet c
singletonHMSet k w = MkHMSet (singletonBox k w)

||| Canonical signed scalar Laurent key `alpha^k` inside `PureMultiset`:
||| - `0` -> `emptyHMSet` (`[]`)
||| - `k` -> `{ [] -> k }` (`singletonHMSet emptyHMSet (MkBoxInt k)`)
public export
scalarKeyHMSet : Integer -> PureMultiset
scalarKeyHMSet k = singletonHMSet emptyHMSet (MkBoxInt k)

------------------------------------------------------------------------
-- 2. TOTAL STRUCTURAL EQUALITY, BOUNDED-ZIPPER ORDERING & SHOW
------------------------------------------------------------------------

-- Structural nesting-depth counter providing an exact upper bound for `Ord` and `Show` totality.
mutual
  public export
  hmDepth : HereditaryMSet c -> Nat
  hmDepth (MkHMSet b) = S (boxNestedDepth b)

  public export
  boxNestedDepth : Box c (HereditaryMSet c) -> Nat
  boxNestedDepth BoxLeaf             = 0
  boxNestedDepth (BoxNode _ l k _ r) =
    max (max (boxNestedDepth l) (boxNestedDepth r)) (hmDepth k)

-- Incremental left-spine comparison avoiding per-comparison `List` flattening.
-- Uses lexicographic function order defaulting missing keys to `zeroWeight`,
-- ensuring signed total order across Laurent keys (`... < -2 < -1 < 0 < +1 < +2 < ...`).
mutual
  public export
  compareHMSetFuel : MultisetWeight c => Nat -> HereditaryMSet c -> HereditaryMSet c -> Ordering
  compareHMSetFuel depthFuel (MkHMSet b1) (MkHMSet b2) =
    compareZipperHM depthFuel (S (boxNodeCount b1 + boxNodeCount b2)) (pushLeftBox b1 []) (pushLeftBox b2 [])

  public export
  compareZipperHM : MultisetWeight c =>
                    Nat ->
                    Nat ->
                    BoxZipper c (HereditaryMSet c) ->
                    BoxZipper c (HereditaryMSet c) ->
                    Ordering
  compareZipperHM _ _ [] []             = EQ
  compareZipperHM _ Z _ _               = EQ
  compareZipperHM depthFuel (S stepRem) [] ((_, w2, r2) :: ys) =
    case compare zeroWeight w2 of
      EQ  => compareZipperHM depthFuel stepRem [] (pushLeftBox r2 ys)
      ord => ord
  compareZipperHM depthFuel (S stepRem) ((_, w1, r1) :: xs) [] =
    case compare w1 zeroWeight of
      EQ  => compareZipperHM depthFuel stepRem (pushLeftBox r1 xs) []
      ord => ord
  compareZipperHM Z (S stepRem) ((_, w1, r1) :: xs) ((_, w2, r2) :: ys) =
    case compare w1 w2 of
      EQ  => compareZipperHM Z stepRem (pushLeftBox r1 xs) (pushLeftBox r2 ys)
      ord => ord
  compareZipperHM (S rem) (S stepRem) ((k1, w1, r1) :: xs) ((k2, w2, r2) :: ys) =
    case compareHMSetFuel rem k1 k2 of
      LT => case compare w1 zeroWeight of
              EQ  => compareZipperHM (S rem) stepRem (pushLeftBox r1 xs) ((k2, w2, r2) :: ys)
              ord => ord
      GT => case compare zeroWeight w2 of
              EQ  => compareZipperHM (S rem) stepRem ((k1, w1, r1) :: xs) (pushLeftBox r2 ys)
              ord => ord
      EQ => case compare w1 w2 of
              EQ  => compareZipperHM (S rem) stepRem (pushLeftBox r1 xs) (pushLeftBox r2 ys)
              ord => ord

public export
compareHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> Ordering
compareHMSet m1 m2 = compareHMSetFuel (min (hmDepth m1) (hmDepth m2)) m1 m2

public export
MultisetWeight c => Eq (HereditaryMSet c) where
  a == b = compareHMSet a b == EQ

public export
MultisetWeight c => Ord (HereditaryMSet c) where
  compare = compareHMSet

||| Looks up the multiplicity of key `k` in an arbitrary `HereditaryMSet c`.
public export
lookupKeyHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> c
lookupKeyHMSet k (MkHMSet b) = lookupBox k b

mutual
  public export
  showHMSetFuel : Show c => Nat -> HereditaryMSet c -> String
  showHMSetFuel _ (MkHMSet BoxLeaf) = "[]"
  showHMSetFuel Z _                 = "[...]"
  showHMSetFuel (S rem) (MkHMSet b) =
    "{" ++ go (toAscListBox b) ++ "}"
    where
      go : List (HereditaryMSet c, c) -> String
      go []             = ""
      go [(k, w)]       = showHMSetFuel rem k ++ ":" ++ show w
      go ((k, w) :: xs) = showHMSetFuel rem k ++ ":" ++ show w ++ ", " ++ go xs

public export
Show c => Show (HereditaryMSet c) where
  show m = showHMSetFuel (hmDepth m) m

------------------------------------------------------------------------
-- 3. CORE CALCULUS OPERATORS ON `HereditaryMSet c`
------------------------------------------------------------------------

||| Superposition (`+` / `<+>`): merges two `HereditaryMSet c` structures with automatic annihilation.
public export
addHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
addHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (unionBox b1 b2)

||| Reflection / Anti-Multiset (`-x`): negates every top-level weight quantum (`M^a`).
public export
negHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c
negHMSet (MkHMSet b) = MkHMSet (negateBox b)

||| Difference / Interference (`subM` / `-`): `a + (-b)` with exact zero pruning.
public export
subHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
subHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (subBox b1 b2)

||| Scalar scaling (`scaleM`): scales all top-level multiplicities by `s : c`.
public export
scaleHMSet : MultisetWeight c => c -> HereditaryMSet c -> HereditaryMSet c
scaleHMSet s (MkHMSet b) = MkHMSet (scaleBox s b)

||| Pointwise Hadamard Masking (`.*.`): intersects shared keys, multiplying their weights.
public export
hadamardHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
hadamardHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (hadamardBox b1 b2)

||| Inner Product / Weight Projection (`<.>`): sums `mulWeight w1 w2` over matching keys into `c`.
public export
dotHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> c
dotHMSet (MkHMSet b1) (MkHMSet b2) = dotBox b1 b2

||| Total Weight / Cardinality (`sumHMSet`): sums all active weights in `c`.
public export
sumHMSet : MultisetWeight c => HereditaryMSet c -> c
sumHMSet (MkHMSet b) = totalMassBox b

||| Multiset linear combination (`flattenHMSetBox`): sums `scaleHMSet w k` over all `(k, w)` in `b`.
public export
flattenHMSetBox : MultisetWeight c => Box c (HereditaryMSet c) -> HereditaryMSet c
flattenHMSetBox =
  foldBox (\k, w, acc => addHMSet acc (scaleHMSet w k)) emptyHMSet

||| Wraps a `HereditaryMSet c` one hereditary bracket deeper: `M -> { M : oneWeight }`.
public export
wrapBox : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c
wrapBox m = singletonHMSet m oneWeight

||| Contracts one hereditary bracket level: `{ k_i : w_i } -> \sum w_i * k_i`.
||| Exact left-inverse of `wrapBox`: `unwrapBoxLevel (wrapBox m) == m` for all `m`.
public export
unwrapBoxLevel : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c
unwrapBoxLevel (MkHMSet b) = flattenHMSetBox b

||| Pairwise box convolution parameterized by an inner key-combining operation.
public export
convolveWith : MultisetWeight c =>
               (HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c) ->
               HereditaryMSet c ->
               HereditaryMSet c ->
               HereditaryMSet c
convolveWith innerOp (MkHMSet b1) (MkHMSet b2) =
  MkHMSet (pairBoxWith innerOp b1 b2)

||| Level-indexed hyper-operation tower (`0 = +`, `1 = *`, `2 = ^`, ...):
||| preserves vertical nesting depth while combining sub-multiset keys at `level`.
public export
hyperOp : MultisetWeight c =>
          (level : Nat) ->
          HereditaryMSet c ->
          HereditaryMSet c ->
          HereditaryMSet c
hyperOp Z         = addHMSet
hyperOp (S level) = convolveWith (hyperOp level)

||| Wildberger Structural Multiplication (`*`):
||| Bilinearly combines elements via Level-1 `hyperOp` (`addHMSet` on keys),
||| weighted by `mulWeight w1 w2`.
public export
mulHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
mulHMSet = hyperOp 1

||| Kuratowski Cartesian Outer Product (`><`):
||| Forms pure multiset pairs `{{k1}, {k1, k2}} = [[k1], [k1, k2]]` internally,
||| weighted by `mulWeight w1 w2`.
public export
outerHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
outerHMSet (MkHMSet b1) (MkHMSet b2) =
  let one : c
      one = oneWeight {c}
      pairKey : HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
      pairKey a b =
        let sa  = wrapBox a
            sab = MkHMSet (setBox b one (singletonBox a one))
        in MkHMSet (setBox sab one (singletonBox sa one))
  in MkHMSet (pairBoxWith pairKey b1 b2)

------------------------------------------------------------------------
-- 4. CANONICAL SYMBOLIC ALGEBRA INSTANCES ON `HereditaryMSet c`
------------------------------------------------------------------------

public export
MultisetWeight c => MonoidCoord (HereditaryMSet c) where
  combine = addHMSet
  origin  = emptyHMSet

public export
MultisetWeight c => GroupCoord (HereditaryMSet c) where
  inverse = negHMSet

public export
MultisetWeight c => Semigroup (HereditaryMSet c) where
  (<+>) = addHMSet

public export
MultisetWeight c => Monoid (HereditaryMSet c) where
  neutral = emptyHMSet

public export
MultisetWeight c => MultisetAlgebra c (HereditaryMSet c) where
  zeroM  = emptyHMSet
  addM   = addHMSet
  negM   = negHMSet
  subM   = subHMSet
  scaleM = scaleHMSet
  dotM   = dotHMSet

public export
MultisetWeight c => MultisetHadamard (HereditaryMSet c) (HereditaryMSet c) (HereditaryMSet c) where
  (.*.) = hadamardHMSet

public export
MultisetWeight c => MultisetOuter (HereditaryMSet c) (HereditaryMSet c) (HereditaryMSet c) where
  (><) = outerHMSet

public export
Num PureMultiset where
  (+) = addHMSet
  (*) = mulHMSet
  fromInteger n = singletonHMSet emptyHMSet (MkBoxInt n)

public export
Neg PureMultiset where
  negate = negHMSet
  (-) = subHMSet

------------------------------------------------------------------------
-- 5. PUREMULTISET SPREAD POLYNUMBERS & GOH CYCLOTOMIC FACTORS
------------------------------------------------------------------------

||| Monomial indeterminate `x = { { [] : 1 } : 1 }` inside `PureMultiset`.
||| Because `Num PureMultiset` defines `(+)` = `addHMSet`, `(*)` = `mulHMSet` (Cauchy convolution),
||| and `fromInteger c` = `{ [] : c }` (degree-0 constant `c * x^0`), every polynomial in `Z[x]`
||| is natively a `PureMultiset` with zero extra types.
public export
polyX : PureMultiset
polyX = wrapBox (scalarKeyHMSet 1)

||| 3-term Cigler-Herbig scaled spread polynomial recurrence directly in `PureMultiset`:
|||   `Z_{n+3}(x) = (3 - x) * Z_{n+2}(x) + (x - 3) * Z_{n+1}(x) + Z_n(x)`
public export
stepSpreadZHMSet : PureMultiset -> PureMultiset -> PureMultiset -> PureMultiset
stepSpreadZHMSet zn zn1 zn2 =
  (3 - polyX) * zn2 + (polyX - 3) * zn1 + zn

public export
spreadZHMSet : Nat -> PureMultiset
spreadZHMSet Z               = emptyHMSet
spreadZHMSet (S Z)           = polyX
spreadZHMSet (S (S Z))       = 4 * polyX - polyX * polyX
spreadZHMSet (S (S (S Z)))   = 9 * polyX - 6 * polyX * polyX + polyX * polyX * polyX
spreadZHMSet (S (S (S (S k)))) =
  go k polyX (4 * polyX - polyX * polyX) (9 * polyX - 6 * polyX * polyX + polyX * polyX * polyX)
  where
    go : Nat -> PureMultiset -> PureMultiset -> PureMultiset -> PureMultiset
    go Z       zn zn1 zn2 = stepSpreadZHMSet zn zn1 zn2
    go (S rem) zn zn1 zn2 = go rem zn1 zn2 (stepSpreadZHMSet zn zn1 zn2)

||| O(1) degree extractor for univariate polynomial keys `scalarKeyHMSet d` (`[]` -> `0`, `{[]:d}` -> `d`).
public export
polyMonomialDeg : PureMultiset -> Nat
polyMonomialDeg (MkHMSet (BoxNode _ BoxLeaf (MkHMSet BoxLeaf) w BoxLeaf)) = boxToNat w
polyMonomialDeg _ = 0

||| Extracts `(leadDeg, leadCoeff)` of a non-zero `PureMultiset` polynomial in `Z[x]`.
public export
polyLeadTerm : PureMultiset -> Maybe (Nat, BoxInt)
polyLeadTerm (MkHMSet b) =
  foldBox (\k, c, best =>
             if boxIsZero c then best
             else let d = polyMonomialDeg k
                  in case best of
                       Nothing      => Just (d, c)
                       Just (bd, _) => if d >= bd then Just (d, c) else best)
          Nothing b

||| Exact Euclidean polynomial division in `Z[x]` over `PureMultiset` when leading terms divide cleanly:
||| returns `(quotient, remainder)` satisfying `num == quotient * den + remainder`.
public export
divModPolyHMSet : PureMultiset -> PureMultiset -> (PureMultiset, PureMultiset)
divModPolyHMSet num den =
  case (polyLeadTerm num, polyLeadTerm den) of
    (Nothing, _) => (emptyHMSet, emptyHMSet)
    (_, Nothing) => (emptyHMSet, num)
    (Just (dNum, _), Just (dDen, MkBoxInt cDen)) =>
      go (S dNum) dDen cDen emptyHMSet num
  where
    go : Nat -> Nat -> Integer -> PureMultiset -> PureMultiset -> (PureMultiset, PureMultiset)
    go Z        _    _    qAcc rem = (qAcc, rem)
    go (S remF) dDen cDen qAcc rem =
      case polyLeadTerm rem of
        Nothing => (qAcc, emptyHMSet)
        Just (dRem, MkBoxInt cRem) =>
          if dRem < dDen
            then (qAcc, rem)
            else
              let (q, r) = divModIntegerEuclid cRem cDen
              in if r /= 0 || q == 0
                   then (qAcc, rem)
                   else
                     let shift = minus dRem dDen
                         term  = singletonHMSet (scalarKeyHMSet (natToInteger shift)) (MkBoxInt q)
                     in go remF dDen cDen (qAcc + term) (rem - term * den)

public export
divExactPolyHMSet : PureMultiset -> PureMultiset -> PureMultiset
divExactPolyHMSet num den = fst (divModPolyHMSet num den)

public export
dividesNatPos : Nat -> Nat -> Bool
dividesNatPos Z _ = False
dividesNatPos d n = go n n
  where
    go : Nat -> Nat -> Bool
    go _     Z     = True
    go Z     (S _) = False
    go (S f) remN  = if remN < d then False else go f (minus remN d)

||| Builds `[(n, Psi_n), ..., (1, Psi_1)]` for any `n` via exact polynomial division
||| `Psi_k(x) = Z_k(x) / prod_{d | k, d < k} Psi_d(x)` with zero hardcoded lookup tables.
public export
gohPsiTableUpTo : Nat -> List (Nat, PureMultiset)
gohPsiTableUpTo n = go n 1 []
  where
    stripDivisors : Nat -> PureMultiset -> List (Nat, PureMultiset) -> PureMultiset
    stripDivisors _ cur [] = cur
    stripDivisors k cur ((d, psiD) :: rest) =
      let nxt = if dividesNatPos d k then divExactPolyHMSet cur psiD else cur
      in stripDivisors k nxt rest

    go : Nat -> Nat -> List (Nat, PureMultiset) -> List (Nat, PureMultiset)
    go Z       _ acc = acc
    go (S rem) k acc =
      let psiK = stripDivisors k (spreadZHMSet k) acc
      in go rem (S k) ((k, psiK) :: acc)

||| Computes the `n`-th irreducible Cigler-Herbig spread polynomial factor `Psi_n(x)` for any `n >= 1`
||| (`gohPsiFactor 0 = 1`).
public export
gohPsiFactor : Nat -> PureMultiset
gohPsiFactor Z = 1
gohPsiFactor n =
  case gohPsiTableUpTo n of
    ((_, psiN) :: _) => psiN
    []               => 1

public export
powNatNum : Num a => a -> Nat -> a
powNatNum _ Z     = fromInteger 1
powNatNum x (S k) = x * powNatNum x k

||| Polymorphic `PureMultiset` polynomial evaluator:
||| - When `a = Integer`, evaluates `P(x0) in Z`.
||| - When `a = PureMultiset`, evaluates symbolic polynomial composition `(P o Q)(x) = P(Q(x))` in `PureMultiset`.
public export
evalPolyHMSetAt : Num a => PureMultiset -> a -> a
evalPolyHMSetAt (MkHMSet b) x =
  foldBox (\k, (MkBoxInt c), acc =>
             let deg = polyMonomialDeg k
             in acc + fromInteger c * powNatNum x deg)
          (fromInteger 0)
          b

||| Evaluates the degree-`deg` homogenization `den^deg * P(num / den)` of a `PureMultiset` polynomial `P`,
||| connecting rational spread evaluation `Z_y(4 * B_1^2 / R_1^2)` to integer Pythagorean powers `4 * B_y^2`.
public export
evalHomogPolyHMSet : (deg : Nat) -> PureMultiset -> (num, den : Integer) -> Integer
evalHomogPolyHMSet deg (MkHMSet b) num den =
  foldBox (\k, (MkBoxInt c), acc =>
             let d = polyMonomialDeg k
             in acc + c * powNatNum num d * powNatNum den (minus deg d))
          0
          b


||| Recursive unit-weight support projection between any two multiplicity carriers `c -> d`:
||| strips all multiplicities and signs down to `oneWeight {c=d}` at every hereditary level.
public export
castSupportLoop : (MultisetWeight c, MultisetWeight d) => Nat -> HereditaryMSet c -> HereditaryMSet d
castSupportLoop Z _ = emptyHMSet
castSupportLoop (S rem) (MkHMSet b) =
  MkHMSet (foldBox (\k, w, acc =>
                     if isZero w then acc else setBox (castSupportLoop rem k) oneWeight acc)
                   BoxLeaf b)

public export
castSupportHMSet : (MultisetWeight c, MultisetWeight d) => HereditaryMSet c -> HereditaryMSet d
castSupportHMSet m = castSupportLoop (hmDepth m) m

------------------------------------------------------------------------
-- CONSTRUCTIVIST HEREDITARY MULTISET RECOGNIZER (`recognition-rule.md`)
------------------------------------------------------------------------

public export
checkHMSetFuel : MultisetWeight c => Nat -> HereditaryMSet c -> Bool
checkHMSetFuel Z     (MkHMSet BoxLeaf) = True
checkHMSetFuel Z     _                 = False
checkHMSetFuel (S rem) (MkHMSet b) =
  case checkBoxBoundsBy (checkHMSetFuel rem) b of
    Nothing => False
    Just _  => True

||| Checks recursively (bounded by cached `hmDepth`) that every AVL node at every
||| hereditary level satisfies strict BST ordering, exact `boxHeight` caches,
||| AVL balance `<= 1`, and zero-pruned weights (`[M, M^a] = []`).
public export
isCanonicalHMSet : MultisetWeight c => HereditaryMSet c -> Bool
isCanonicalHMSet m = checkHMSetFuel (hmDepth m) m

||| Total `Dec` recognizer verifying external or deserialized `HereditaryMSet c` candidates.
public export
recognizeCanonicalHMSet : MultisetWeight c => (m : HereditaryMSet c) -> Dec (isCanonicalHMSet m = True)
recognizeCanonicalHMSet m = decideBoolTrue (isCanonicalHMSet m)

||| Smart constructor packing a verified `HereditaryMSet c` into a certified `Subset`.
public export
toCanonicalHMSet : MultisetWeight c => (m : HereditaryMSet c) -> Maybe (Subset (HereditaryMSet c) (\x => isCanonicalHMSet x = True))
toCanonicalHMSet m =
  case recognizeCanonicalHMSet m of
    Yes prf => Just (Element m prf)
    No _    => Nothing

------------------------------------------------------------------------
-- 6. INTRINSIC `GohBound` DERIVATION & SELF-BOUNDING ON `HereditaryMSet c`
------------------------------------------------------------------------

||| Backward-or-stay half-step dipole (`alpha^(-1) + 1`) as a `PureMultiset`.
public export
halfStepBackward : PureMultiset
halfStepBackward = wrapBox (scalarKeyHMSet (-1)) + 1

||| Forward-or-stay half-step dipole (`alpha^(+1) + 1`) as a `PureMultiset`.
public export
halfStepForward : PureMultiset
halfStepForward = polyX + 1

||| Full symmetric motion tick (`(alpha^(-1) + 1) * (alpha^(+1) + 1) = alpha^(-1) + 2*alpha^0 + alpha^(+1)`).
public export
symmetricMotionTick : PureMultiset
symmetricMotionTick = halfStepBackward * halfStepForward

||| Fundamental binary polarity count (`2`) extracted directly as pure Peano `Nat`
||| from the two opposing non-origin poles (`-1` and `+1`) of `symmetricMotionTick`
||| inside the multiset algebra—zero `integerToNat` / `assert_total`, pure `Refl` reduction.
public export
elementaryPolarityCount : Nat
elementaryPolarityCount =
  let (MkHMSet box) = symmetricMotionTick
  in boxNodeCount (deleteBox emptyHMSet box)

||| Compile-time audit verifying `elementaryPolarityCount` reduces definitionally to `2`.
public export
0 prfElementaryPolarityTwo : FinScBox.HereditaryMSet.elementaryPolarityCount = 2
prfElementaryPolarityTwo = Refl

||| Helper to calculate `2^n` for `Nat` buffer depth from `elementaryPolarityCount`.
public export
fastNatPower2 : Nat -> Nat
fastNatPower2 Z     = S Z
fastNatPower2 (S k) = elementaryPolarityCount * fastNatPower2 k

||| Division by `2` via structural recursion.
public export
half : Nat -> Nat
half Z         = Z
half (S Z)     = Z
half (S (S k)) = S (half k)

||| Monomorphic maximum on inductive Peano `Nat` for horizon bounds.
public export
boundMax : Nat -> Nat -> Nat
boundMax Z b         = b
boundMax a Z         = a
boundMax (S a) (S b) = S (boundMax a b)

||| Canonical Goh factorisation formula computing exact bound steps natively in `Nat`:
||| `Bound(S k) = S k + floor(k/2) + elementaryPolarityCount` (e.g. `Bound(210) = 316`).
public export
gohBoundNat : Nat -> Nat
gohBoundNat Z     = S Z
gohBoundNat (S k) = S k + half k + elementaryPolarityCount

||| First-class constructivist Goh bound indexed directly by model capacity.
public export
record GohBound (0 capacity : Nat) where
  constructor MkGohBound
  boundSteps : Nat

public export
Eq (GohBound cap) where
  (MkGohBound s1) == (MkGohBound s2) = s1 == s2

public export
Show (GohBound cap) where
  show (MkGohBound s) = "GohBound(" ++ show s ++ " steps)"

||| Existential model-indexed `GohBound` envelope for streams whose active capacity is
||| derived dynamically from a `HereditaryMSet c` support summary.
public export
data AnyGohBound : Type where
  MkAnyGohBound : (capacity : Nat) -> GohBound capacity -> AnyGohBound

public export
Eq AnyGohBound where
  (MkAnyGohBound c1 b1) == (MkAnyGohBound c2 b2) = c1 == c2 && b1.boundSteps == b2.boundSteps

public export
Show AnyGohBound where
  show (MkAnyGohBound cap gb) = "AnyGohBound(cap=" ++ show cap ++ ", steps=" ++ show gb.boundSteps ++ ")"

||| Single-pass invariants extracted polymorphically from any `HereditaryMSet c`:
||| - `nnz`       : Support cardinality `chi_Supp(1)` (non-zero entries)
||| - `totalMass` : Absolute multiplicity magnitude sum via `weightMagnitude`
||| - `maxDeg`    : Maximum structural degree / nesting height encountered
public export
record SupportStats where
  constructor MkSupportStats
  nnz       : Nat
  totalMass : Nat
  maxDeg    : Nat

public export
emptySupportStats : SupportStats
emptySupportStats = MkSupportStats 0 0 0

||| Extracts the maximum nested `weightMagnitude` inside a hereditary box
||| bounded cleanly by remaining hereditary nesting depth `fuel`.
public export
maxWeightInBox : MultisetWeight c => Nat -> Box c (HereditaryMSet c) -> Nat
maxWeightInBox Z _ = 0
maxWeightInBox (S rem) box = goBox box
  where
    goBox : Box c (HereditaryMSet c) -> Nat
    goBox BoxLeaf = 0
    goBox (BoxNode _ l (MkHMSet sub) w r) =
      let here = boundMax (weightMagnitude w) (maxWeightInBox rem sub)
      in boundMax (goBox l) (boundMax here (goBox r))

||| Polymorphic single-pass AVL fold updating `nnz`, `totalMass`, and `maxDeg` across
||| any `MultisetWeight c` carrier (`BoxInt`, `SignedBit`, or `MultisetBit`).
public export
collectSupportStats : MultisetWeight c => Box c (HereditaryMSet c) -> SupportStats
collectSupportStats BoxLeaf = emptySupportStats
collectSupportStats (BoxNode _ left (MkHMSet innerBox) w right) =
  let lStats     = collectSupportStats left
      rStats     = collectSupportStats right
      absW       = weightMagnitude w
      childDeg   = case innerBox of
                     BoxLeaf => 0
                     BoxNode _ BoxLeaf (MkHMSet BoxLeaf) expW BoxLeaf =>
                       weightMagnitude expW
                     _ => boundMax (boxHeight innerBox) (maxWeightInBox (boxNestedDepth innerBox) innerBox)
      selfNnz    = the Nat (if isZero w then 0 else 1)
      mergedNnz  = lStats.nnz + selfNnz + rStats.nnz
      mergedMass = lStats.totalMass + absW + rStats.totalMass
      mergedMax  = boundMax lStats.maxDeg (boundMax childDeg rStats.maxDeg)
  in MkSupportStats mergedNnz mergedMass mergedMax

||| Uncapped intrinsic self-bound extractor deriving `cap = nnz + S maxDeg` directly
||| from a `HereditaryMSet c` without requiring an external capacity ceiling.
public export
selfBoundOfHMSet : MultisetWeight c => HereditaryMSet c -> (AnyGohBound, Nat)
selfBoundOfHMSet (MkHMSet rootBox) =
  let treeBound  = fastNatPower2 (boxHeight rootBox)
      stats      = collectSupportStats rootBox
      cap        = stats.nnz + S stats.maxDeg
      ySteps     = gohBoundNat cap
      yieldBound = MkGohBound ySteps
      stepBudget = ySteps + treeBound + stats.nnz
  in (MkAnyGohBound cap yieldBound, stepBudget)

------------------------------------------------------------------------
-- 7. TIME HORIZONS OVER THE INTEGER AXIS Z
------------------------------------------------------------------------

||| Exhaustive classification of Time & Scale horizons over the integer axis Z:
public export
data Time : Type where
  ||| 1. Fixed compact interval [low, high] known at compile time
  StaticTime     : (low : Integer) -> (high : Integer) -> Time
  ||| 2. Forward causal ray [0, cap] governed by runtime `GohBound`
  BoundedTime    : (cap : Nat) -> Time
  ||| 3. Backward UV ray [-cap, 0] governed by runtime `GohBound`
  RetroTime      : (cap : Nat) -> Time
  ||| 4. Sliding causal interval [t - win, t] of fixed width `win`
  WindowedTime   : (win : Nat) -> Time
  ||| 5. Causal ray starting at Tick 0 with no preset upper bound (productive on demand)
  OpenFuture     : Time
  ||| 6. Two-sided stream with no preset lower or upper bound (productive in both directions)
  BilateralTime  : Time

public export
Eq Time where
  (StaticTime l1 h1)     == (StaticTime l2 h2)     = l1 == l2 && h1 == h2
  (BoundedTime c1)       == (BoundedTime c2)       = c1 == c2
  (RetroTime c1)         == (RetroTime c2)         = c1 == c2
  (WindowedTime w1)      == (WindowedTime w2)      = w1 == w2
  OpenFuture             == OpenFuture             = True
  BilateralTime          == BilateralTime          = True
  _                      == _                      = False

public export
Show Time where
  show (StaticTime l h) = "StaticTime(" ++ show l ++ ", " ++ show h ++ ")"
  show (BoundedTime c)  = "BoundedTime(" ++ show c ++ ")"
  show (RetroTime g)    = "RetroTime(" ++ show g ++ ")"
  show (WindowedTime w) = "WindowedTime(" ++ show w ++ ")"
  show OpenFuture       = "OpenFuture"
  show BilateralTime    = "BilateralTime"

------------------------------------------------------------------------
-- 8. STREAM STEP, TIME STREAM & LOCAL BRESENHAM PACING
------------------------------------------------------------------------

||| What happens at a single tick `n` of a TimeStream:
||| - `StreamDone`  : Stream has naturally terminated (quiescent completion)
||| - `StreamSkip`  : Vacuum annihilation (`[+1, -1] = []`) or silent tick
|||                   (consumes 1 `stepBudget`, 0 `GohBound`)
||| - `StreamYield` : Emits an active multiset term/delta
|||                   (consumes 1 `stepBudget` and `yieldCost` of `GohBound`)
public export
data StreamStep : (a : Type) -> Type where
  StreamDone  : StreamStep a
  StreamSkip  : StreamStep a
  StreamYield : (term : a) -> StreamStep a

public export
Eq a => Eq (StreamStep a) where
  StreamDone      == StreamDone      = True
  StreamSkip      == StreamSkip      = True
  (StreamYield x) == (StreamYield y) = x == y
  _               == _               = False

public export
Show a => Show (StreamStep a) where
  show StreamDone      = "StreamDone"
  show StreamSkip      = "StreamSkip"
  show (StreamYield x) = "StreamYield(" ++ show x ++ ")"

||| A Time-indexed ongoing sequence / stream starting at `startTick`.
||| (Wildberger's `OnSeq` indexed by `Time` with `StreamStep` transitions).
public export
record TimeStream (0 t : Time) (a : Type) where
  constructor MkTimeStream
  startTick : Nat
  stepAt    : Nat -> StreamStep a

||| Local exact integer Bresenham pacing step with base tick budget `budget > 0`,
||| nonnegative local load `load`, and signed pacing balance `bal` (`MkBoxInt 0` at zero load).
||| - `budget <= 0`         : unpaced pass-through `(StreamYield (), MkBoxInt 0)`.
||| - `bal + c <= budget`   : emits `StreamYield ()` with `nextBal = max 0 (bal + c)` (`c = max 0 load`).
||| - `bal + c > budget`    : emits `StreamSkip` with `nextBal = bal - budget`.
||| Over `budget + c` ticks from `MkBoxInt 0` at constant load `c >= 0`, this emits
||| exact `budget` yields and `c` skips, returning cleanly to `MkBoxInt 0`.
public export
paceStreamStep : (budget : Integer) -> (load : Integer) -> (bal : BoxInt) -> (StreamStep (), BoxInt)
paceStreamStep budget load (MkBoxInt b) =
  if budget <= 0
    then (StreamYield (), MkBoxInt 0)
    else
      let c     = if load < 0 then 0 else load
          nextB = b + c
      in if nextB <= budget
           then (StreamYield (), MkBoxInt (if nextB < 0 then 0 else nextB))
           else (StreamSkip, MkBoxInt (b - budget))

------------------------------------------------------------------------
-- 9. BOUND EXHAUSTION & TIME-HORIZON FREEZE-OUT
------------------------------------------------------------------------

||| Termination classification when a `TimeStream` halts and freezes out into `StaticTime`:
||| - `YieldExhausted`     : Yield quota (`GohBound cap`) reached 0
||| - `StepHorizonReached` : Step horizon (`stepBudget`) reached 0 while yield remained
||| - `NaturalCompletion`  : Stream emitted `StreamDone` before exhausting either budget
public export
data StreamFreezeReason : Type where
  YieldExhausted     : StreamFreezeReason
  StepHorizonReached : StreamFreezeReason
  NaturalCompletion  : StreamFreezeReason

public export
Eq StreamFreezeReason where
  YieldExhausted     == YieldExhausted     = True
  StepHorizonReached == StepHorizonReached = True
  NaturalCompletion  == NaturalCompletion  = True
  _                  == _                  = False

public export
Show StreamFreezeReason where
  show YieldExhausted     = "YieldExhausted"
  show StepHorizonReached = "StepHorizonReached"
  show NaturalCompletion  = "NaturalCompletion"

||| Certified static relic produced when a dynamic `TimeStream` exhausts its bound
||| or completes at retrograde depth `g` (`RetroTime g`) and capacity `cap` (`BoundedTime cap`).
||| Its phantom Time index transitions to `StaticTime (- cast g) (cast cap)`.
public export
record SolidifiedStream (0 frozenTime : Time) (0 cap : Nat) (a : Type) where
  constructor MkSolidifiedStream
  relicState     : a
  freezeReason   : StreamFreezeReason
  freezeTick     : Nat
  yieldsConsumed : Nat
  stepsConsumed  : Nat
  remainingYield : GohBound cap
  remainingSteps : Nat

public export
(Eq a) => Eq (SolidifiedStream t cap a) where
  s1 == s2 =
    s1.relicState == s2.relicState &&
    s1.freezeReason == s2.freezeReason &&
    s1.freezeTick == s2.freezeTick &&
    s1.yieldsConsumed == s2.yieldsConsumed &&
    s1.stepsConsumed == s2.stepsConsumed

||| Stateful Streaming Freeze-Out Evaluator over an initial state `initA : a` populated at `t = 0`:
||| At each tick, `stepFn acc` emits `(StreamStep a, yieldCost, skipsSaved)`:
||| - `StreamDone`      : natural termination (`NaturalCompletion`)
||| - `StreamSkip`      : consumes `0` `yieldBound` and `1` `stepBudget`, banking `skipsSaved`
||| - `StreamYield nxt` : if `remYield < yieldCost`, freezes out with `YieldExhausted`;
|||                       otherwise consumes `yieldCost` of `yieldBound` and `1` `stepBudget`.
public export
freezeStateStreamWith :
  {0 cap     : Nat} ->
  (g          : Nat) ->
  (yieldBound : GohBound cap) ->
  (stepBudget : Nat) ->
  (stepFn     : a -> (StreamStep a, Nat, Nat)) ->
  (initA      : a) ->
  (SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a, Nat)
freezeStateStreamWith g yieldBound stepBudget stepFn initA =
  loop yieldBound.boundSteps stepBudget 0 0 0 0 initA
  where
    loop : (yRem, sRem, currTick, yUsed, sUsed, skAcc : Nat) ->
           (acc : a) ->
           (SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a, Nat)
    loop yRem Z currTick yUsed sUsed skAcc acc =
      (MkSolidifiedStream acc StepHorizonReached currTick yUsed sUsed (MkGohBound yRem) 0, skAcc)
    loop yRem (S sRem) currTick yUsed sUsed skAcc acc =
      case stepFn acc of
        (StreamDone, _, sk) =>
          (MkSolidifiedStream acc NaturalCompletion currTick yUsed sUsed (MkGohBound yRem) (S sRem), skAcc + sk)
        (StreamSkip, _, sk) =>
          loop yRem sRem (S currTick) yUsed (S sUsed) (skAcc + sk) acc
        (StreamYield nxt, yCost, sk) =>
          if yRem < yCost
            then (MkSolidifiedStream acc YieldExhausted currTick yUsed sUsed (MkGohBound yRem) (S sRem), skAcc)
            else loop (minus yRem yCost) sRem (S currTick) (yUsed + yCost) (S sUsed) (skAcc + sk) nxt

||| Decoupled Yield/Step Freeze-Out Evaluator over any `TimeStream t a`,
||| expressed directly as a thin specialization of `freezeStateStreamWith`.
public export
freezeTimeStreamWith :
  {0 t   : Time} ->
  {0 cap : Nat} ->
  (g          : Nat) ->
  (yieldBound : GohBound cap) ->
  (stepBudget : Nat) ->
  (combine    : a -> a -> a) ->
  (initAcc    : a) ->
  TimeStream t a ->
  SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a
freezeTimeStreamWith g yieldBound stepBudget combine initAcc (MkTimeStream start at) =
  let (r, _) = freezeStateStreamWith g yieldBound stepBudget
                 (\(tk, acc) =>
                    case at tk of
                      StreamDone       => (StreamDone, 0, 0)
                      StreamSkip       => (StreamYield (S tk, acc), 0, 1)
                      StreamYield term => (StreamYield (S tk, combine term acc), 1, 0))
                 (start, initAcc)
  in MkSolidifiedStream (snd r.relicState) r.freezeReason (fst r.relicState)
                        r.yieldsConsumed r.stepsConsumed r.remainingYield r.remainingSteps

