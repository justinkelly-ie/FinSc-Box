module Stage0.BoxInt

import Data.Nat
import Data.Linear
import public Data.DPair

%default total

------------------------------------------------------------------------
-- 1. BOXINT SCALAR TYPE & MONOMORPHIC ARITHMETIC
------------------------------------------------------------------------

||| A BoxInt is a signed integer wrapped in a discrete box.
||| It represents concrete particle counts, quadrances, and metric entries
||| in Wildberger's Box Arithmetic.
|||
||| 2LTT Staging Operation: Lifting (⇑Int) - Lifts raw integer scalars into 0-defect discrete scalar space.
public export
record BoxInt where
  constructor MkBoxInt
  value : Integer

||| 2LTT Staging Operation: Splicing (~t) - Extracts raw underlying Integer term from boxed representation.
%inline public export
unwrapBox : BoxInt -> Integer
unwrapBox (MkBoxInt v) = v

||| 2LTT Staging Operation: Lifting (⇑Int) - Lifts integer value into boxed discrete representation.
||| Builds descending `(powerOfTwo, shiftedDenominator)` pairs for O(log N) binary division.
public export
buildPow2Pairs : Nat -> Integer -> Integer -> Integer -> List (Integer, Integer) -> List (Integer, Integer)
buildPow2Pairs Z _ _ _ acc = acc
buildPow2Pairs (S fuel) num bit curDen acc =
  if curDen > num
    then acc
    else buildPow2Pairs fuel num (bit + bit) (curDen + curDen) ((bit, curDen) :: acc)

||| Consumes `(powerOfTwo, shiftedDenominator)` pairs to yield exact `(quotient, remainder)`.
public export
consumePow2Pairs : Integer -> Integer -> List (Integer, Integer) -> (Integer, Integer)
consumePow2Pairs rem q [] = (q, rem)
consumePow2Pairs rem q ((bit, d) :: xs) =
  if rem >= d
    then consumePow2Pairs (rem - d) (q + bit) xs
    else consumePow2Pairs rem q xs

||| Total O(log N) binary integer division and remainder on positive integers (`assert_total`-free).
public export
divModIntegerPos : Integer -> Integer -> (Integer, Integer)
divModIntegerPos num den =
  if den <= 0 || num <= 0
    then (0, if num <= 0 then 0 else num)
    else consumePow2Pairs num 0 (buildPow2Pairs 128 num 1 den [])

||| Total O(log N) binary integer quotient on positive integers (`assert_total`-free).
public export
divIntegerPos : Integer -> Integer -> Integer
divIntegerPos num den = fst (divModIntegerPos num den)

||| Total O(log N) Euclidean integer division and remainder (`a = q * b + r`, `0 <= r < |b|`,
||| returning `(0, 0)` when `b == 0`; `assert_total`-free).
public export
divModIntegerEuclid : Integer -> Integer -> (Integer, Integer)
divModIntegerEuclid a b =
  if b == 0
    then (0, 0)
    else
      let absA      = if a < 0 then -a else a
          absB      = if b < 0 then -b else b
          (q0, r0)  = divModIntegerPos absA absB
          (qPos, r) = if a >= 0
                        then (q0, r0)
                        else if r0 == 0
                          then (-q0, 0)
                          else (-(q0 + 1), absB - r0)
      in if b > 0 then (qPos, r) else (-qPos, r)

public export
intToBoxInt : Integer -> BoxInt
intToBoxInt n = MkBoxInt n

public export
natToBoxInt : Nat -> BoxInt
natToBoxInt n = MkBoxInt (natToInteger n)

||| Total binary quotient and remainder by 4 directly on non-negative `BoxInt` (`assert_total`-free).
public export
divMod4Box : BoxInt -> (BoxInt, BoxInt)
divMod4Box (MkBoxInt v) =
  if v <= 0
    then (MkBoxInt 0, MkBoxInt 0)
    else let (q, r) = divModIntegerPos v 4
         in (MkBoxInt q, MkBoxInt r)

||| Symmetric truncating division by 4 directly on signed `BoxInt` (`assert_total`-free).
public export
tdiv4Box : BoxInt -> BoxInt
tdiv4Box (MkBoxInt v) =
  if v >= 0
    then MkBoxInt (divIntegerPos v 4)
    else MkBoxInt (-(divIntegerPos (-v) 4))

||| Symmetric truncating division by a strictly positive integer denominator (`assert_total`-free).
public export
tdivPosBox : BoxInt -> Integer -> BoxInt
tdivPosBox (MkBoxInt v) den =
  if den <= 0
    then MkBoxInt 0
    else if v >= 0
      then MkBoxInt (divIntegerPos v den)
      else MkBoxInt (-(divIntegerPos (-v) den))

||| Symmetric nearest-integer division (half toward zero for even denominators,
||| exact nearest integer for odd denominators) by a strictly positive integer (`assert_total`-free).
public export
rdivPosBox : BoxInt -> Integer -> BoxInt
rdivPosBox (MkBoxInt v) den =
  if den <= 0
    then MkBoxInt 0
    else let half = divIntegerPos (den - 1) 2
         in if v >= 0
              then MkBoxInt (divIntegerPos (v + half) den)
              else MkBoxInt (-(divIntegerPos ((-v) + half) den))

||| Symmetric truncating division by 2 directly on signed `BoxInt` (`assert_total`-free).
public export
tdiv2Box : BoxInt -> BoxInt
tdiv2Box b = tdivPosBox b 2

||| Total O(log |v|) odd-parity predicate directly on signed `BoxInt` (`assert_total`-free).
public export
isOddBox : BoxInt -> Bool
isOddBox (MkBoxInt v) =
  let a = if v < 0 then -v else v
  in snd (divModIntegerPos a 2) == 1

%inline public export
addBox : BoxInt -> BoxInt -> BoxInt
addBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

%inline public export
subBox : BoxInt -> BoxInt -> BoxInt
subBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

public export
addBoxLinear : (1 a : BoxInt) -> (1 b : BoxInt) -> BoxInt
addBoxLinear (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

public export
subBoxLinear : (1 a : BoxInt) -> (1 b : BoxInt) -> BoxInt
subBoxLinear (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

%inline public export
mulBox : BoxInt -> BoxInt -> BoxInt
mulBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)

%inline public export
boxEq : BoxInt -> BoxInt -> Bool
boxEq (MkBoxInt a) (MkBoxInt b) = case a == b of True => True; False => False

%inline public export
boxLTE : BoxInt -> BoxInt -> Bool
boxLTE (MkBoxInt a) (MkBoxInt b) = case a <= b of True => True; False => False

%inline public export
Num BoxInt where
  (+) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)
  (*) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)
  fromInteger n = MkBoxInt n

%inline public export
negBox : BoxInt -> BoxInt
negBox (MkBoxInt a) = MkBoxInt (-a)

%inline public export
Neg BoxInt where
  negate (MkBoxInt a) = MkBoxInt (-a)
  (-) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

%inline public export
divBox : BoxInt -> BoxInt -> BoxInt
divBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (fst (divModIntegerEuclid a b))

%inline public export
modBox : BoxInt -> BoxInt -> BoxInt
modBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (snd (divModIntegerEuclid a b))

public export
Integral BoxInt where
  div = divBox
  mod = modBox

public export
Abs BoxInt where
  abs (MkBoxInt v) = MkBoxInt (case v < 0 of True => -v; False => v)

public export
Cast Nat BoxInt where
  cast = natToBoxInt

public export
Cast Integer BoxInt where
  cast = intToBoxInt

||| Returns True if the BoxInt value is exactly zero.
%inline public export
boxIsZero : BoxInt -> Bool
boxIsZero (MkBoxInt v) = v == 0

||| Returns True if the BoxInt value is non-zero.
%inline public export
boxIsNonZero : BoxInt -> Bool
boxIsNonZero (MkBoxInt v) = v /= 0

||| Converts BoxInt to a strictly positive Nat (minimum 1), clamping values <= 0 to 1.
||| Eliminates division-by-zero risks in physical denominator scales.
public export
boxIntToPositiveNat : BoxInt -> Nat
boxIntToPositiveNat (MkBoxInt v) = if v <= 0 then 1 else integerToNat v

||| Converts BoxInt to Nat, clamping negative values to 0.
||| For absolute-value conversion use absBox first.
public export
boxToNat : BoxInt -> Nat
boxToNat (MkBoxInt v) = if v <= 0 then 0 else integerToNat v

public export
Cast BoxInt Nat where
  cast = boxToNat

||| Returns the absolute value of a BoxInt as a BoxInt.
||| Does not go through boxToNat — safe for negative inputs.
%inline public export
absBox : BoxInt -> BoxInt
absBox (MkBoxInt v) = MkBoxInt (if v < 0 then -v else v)

%inline public export
Eq BoxInt where
  (MkBoxInt a) == (MkBoxInt b) = a == b

public export
Ord BoxInt where
  compare (MkBoxInt a) (MkBoxInt b) = compare a b

public export
Show BoxInt where
  show (MkBoxInt a) = "[" ++ show a ++ "]"

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE NON-ZERO RECOGNIZER (`Dec`)
------------------------------------------------------------------------

||| Constructive predicate witnessing that a `BoxInt` is non-zero.
public export
data IsNonZeroBox : BoxInt -> Type where
  MkIsNonZero : {v : Integer} -> (0 prf : (v == 0) = False) -> IsNonZeroBox (MkBoxInt v)

||| Constructive `Dec` recognizer replacing `Maybe`-returning `toNonZeroBoxInt`
||| (per `recognition-rule.md`), yielding `Yes prf` or `No contra`.
public export
recognizeNonZeroBox : (b : BoxInt) -> Dec (IsNonZeroBox b)
recognizeNonZeroBox (MkBoxInt v) with (v == 0) proof eq
  recognizeNonZeroBox (MkBoxInt v) | False = Yes (MkIsNonZero eq)
  recognizeNonZeroBox (MkBoxInt v) | True  =
    No (\(MkIsNonZero prf) => absurd (trans (sym eq) prf))

||| Erased-proof `Subset` alias for zero-overhead runtime storage of non-zero scalars.
public export
NonZeroBoxInt : Type
NonZeroBoxInt = Subset BoxInt IsNonZeroBox

||| Smart constructor returning `Maybe NonZeroBoxInt` backed by the `Dec` witness.
public export
toNonZeroBoxInt : (b : BoxInt) -> Maybe NonZeroBoxInt
toNonZeroBoxInt b =
  case recognizeNonZeroBox b of
    Yes prf => Just (Element b prf)
    No _    => Nothing
