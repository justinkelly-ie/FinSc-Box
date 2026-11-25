module FinScBox.Interfaces

import public Data.Linear
import Data.Nat
import FinScBox.BoxInt

%default total

-----------------------------------------------------------------------
-- 1. COORDINATE ALGEBRA (`MonoidCoord` & `GroupCoord`)
-----------------------------------------------------------------------

||| Translation-invariant coordinate space supporting additive Cauchy convolution.
public export
interface Ord k => MonoidCoord k where
  combine : k -> k -> k
  origin  : k
  0 assoc : (x, y, z : k) -> combine x (combine y z) = combine (combine x y) z

||| Reversible coordinate space with exact additive inverses.
public export
interface MonoidCoord k => GroupCoord k where
  inverse  : k -> k
  0 invLaw : (x : k) -> combine x (inverse x) = FinScBox.Interfaces.origin

public export
MonoidCoord Nat where
  combine = (+)
  origin  = 0
  assoc x y z = plusAssociative x y z

public export
MonoidCoord () where
  combine _ _ = ()
  origin = ()
  assoc _ _ _ = Refl

public export
GroupCoord () where
  inverse _ = ()
  invLaw _ = Refl

public export
(MonoidCoord a, MonoidCoord b) => MonoidCoord (a, b) where
  combine (x1, y1) (x2, y2) = (combine x1 x2, combine y1 y2)
  origin = (origin, origin)
  assoc (x1, y1) (x2, y2) (x3, y3) =
    rewrite assoc x1 x2 x3 in
    rewrite assoc y1 y2 y3 in
    Refl

public export
(GroupCoord a, GroupCoord b) => GroupCoord (a, b) where
  inverse (x, y) = (inverse x, inverse y)
  invLaw (x, y) =
    rewrite invLaw x in
    rewrite invLaw y in
    Refl

-----------------------------------------------------------------------
-- 2. MULTIPLICITY WEIGHTS & CORE MULTISET ALGEBRA OPERATORS
-----------------------------------------------------------------------

||| Core multiplicity weight ring interface shared by `Box c k`, `HereditaryMSet c`,
||| and `Maxel c a b form`.
public export
interface Ord c => MultisetWeight c where
  zeroWeight : c
  oneWeight  : c
  isZero     : c -> Bool
  addWeight  : c -> c -> c
  negWeight  : c -> c
  mulWeight  : c -> c -> c
  weightMagnitude : c -> Nat
  weightMagnitude w = if isZero w then 0 else 1

public export
MultisetWeight BoxInt where
  zeroWeight = MkBoxInt 0
  oneWeight  = MkBoxInt 1
  isZero     = boxIsZero
  addWeight  = addBox
  negWeight  = negBox
  mulWeight  = mulBox
  weightMagnitude (MkBoxInt w) = integerToNat (abs w)

||| Defines how a multiplicity `c` peels off one positive (`Left`)
||| or negative (`Right`) quantum at a time.
public export
interface MultisetWeight c => QuantumCarrier c where
  peelQuantum : c -> Maybe (Either c c)

public export
QuantumCarrier BoxInt where
  peelQuantum (MkBoxInt w) =
    if w > 0 then Just (Left (MkBoxInt (w - 1)))
    else if w < 0 then Just (Right (MkBoxInt (w + 1)))
    else Nothing

||| Unified core multiset algebra shared by `Box c k`, `HereditaryMSet c`,
||| and `Maxel c a b form`: additive group (`0`, `+`, `neg`, `-`), scalar
||| scaling, and bilinear inner product (`<.>`).
public export
interface MultisetWeight c => MultisetAlgebra c a | a where
  zeroM  : a
  addM   : a -> a -> a
  negM   : a -> a
  subM   : a -> a -> a
  scaleM : c -> a -> a
  dotM   : a -> a -> c
  subM x y = addM x (negM y)

public export
infixl 7 <.>

||| Inner / Dot product: `<.>`.
public export
(<.>) : MultisetAlgebra c a => a -> a -> c
(<.>) = dotM

public export
infixl 8 .*.

||| Pointwise Hadamard product (`.*.`), supporting both closed forms (`Box`, `HereditaryMSet`)
||| and symmetry-tracked `Maxel` parity.
public export
interface MultisetHadamard a b out | a, b where
  (.*.) : a -> b -> out

public export
infixl 7 ><

||| Polymorphic outer product interface shared by Cartesian coordinates (`Box c`)
||| and Kuratowski pairing (`HereditaryMSet c`).
public export
interface MultisetOuter a b out | a, b where
  (><) : a -> b -> out

-----------------------------------------------------------------------
-- 3. CONSTRUCTIVE SIGNED INTEGER COORDINATE (`SignedCoord`)
-----------------------------------------------------------------------

||| Canonical inductive signed integer coordinate with unique zero (`ZeroZ`).
||| Supports total constructive `Ord`, `MonoidCoord`, and `GroupCoord`.
public export
data SignedCoord : Type where
  ZeroZ : SignedCoord
  PosZ  : Nat -> SignedCoord
  NegZ  : Nat -> SignedCoord

public export
Eq SignedCoord where
  ZeroZ  == ZeroZ  = True
  PosZ a == PosZ b = a == b
  NegZ a == NegZ b = a == b
  _      == _      = False

public export
Ord SignedCoord where
  compare ZeroZ    ZeroZ    = EQ
  compare ZeroZ    (PosZ _) = LT
  compare ZeroZ    (NegZ _) = GT
  compare (PosZ _) ZeroZ    = GT
  compare (PosZ a) (PosZ b) = compare a b
  compare (PosZ _) (NegZ _) = GT
  compare (NegZ _) ZeroZ    = LT
  compare (NegZ _) (PosZ _) = LT
  compare (NegZ a) (NegZ b) = compare b a

public export
Show SignedCoord where
  show ZeroZ    = "0"
  show (PosZ k) = "+" ++ show (S k)
  show (NegZ k) = "-" ++ show (S k)

public export
succZ : SignedCoord -> SignedCoord
succZ ZeroZ        = PosZ Z
succZ (PosZ k)     = PosZ (S k)
succZ (NegZ Z)     = ZeroZ
succZ (NegZ (S k)) = NegZ k

public export
predZ : SignedCoord -> SignedCoord
predZ ZeroZ        = NegZ Z
predZ (PosZ Z)     = ZeroZ
predZ (PosZ (S k)) = PosZ k
predZ (NegZ k)     = NegZ (S k)

0 succPredInv : (z : SignedCoord) -> succZ (predZ z) = z
succPredInv ZeroZ        = Refl
succPredInv (PosZ Z)     = Refl
succPredInv (PosZ (S _)) = Refl
succPredInv (NegZ _)     = Refl

0 predSuccInv : (z : SignedCoord) -> predZ (succZ z) = z
predSuccInv ZeroZ        = Refl
predSuccInv (PosZ _)     = Refl
predSuccInv (NegZ Z)     = Refl
predSuccInv (NegZ (S _)) = Refl

||| Compute `(S a) - (S b)` canonically as a `SignedCoord`.
public export
subS : Nat -> Nat -> SignedCoord
subS Z     Z     = ZeroZ
subS (S a) Z     = PosZ a
subS Z     (S b) = NegZ b
subS (S a) (S b) = subS a b

0 subSDiag : (k : Nat) -> subS k k = ZeroZ
subSDiag Z     = Refl
subSDiag (S k) = subSDiag k

0 subSSuccL : (a, b : Nat) -> subS (S a) b = succZ (subS a b)
subSSuccL Z     Z         = Refl
subSSuccL (S _) Z         = Refl
subSSuccL Z     (S Z)     = Refl
subSSuccL Z     (S (S _)) = Refl
subSSuccL (S a) (S b)     = subSSuccL a b

0 subSSuccR : (a, b : Nat) -> subS a (S b) = predZ (subS a b)
subSSuccR Z     Z         = Refl
subSSuccR Z     (S _)     = Refl
subSSuccR (S Z) Z         = Refl
subSSuccR (S (S _)) Z     = Refl
subSSuccR (S a) (S b)     = subSSuccR a b

public export
addSigned : SignedCoord -> SignedCoord -> SignedCoord
addSigned ZeroZ    y        = y
addSigned x        ZeroZ    = x
addSigned (PosZ a) (PosZ b) = PosZ (S (a + b))
addSigned (NegZ a) (NegZ b) = NegZ (S (a + b))
addSigned (PosZ a) (NegZ b) = subS a b
addSigned (NegZ a) (PosZ b) = subS b a

public export
negSigned : SignedCoord -> SignedCoord
negSigned ZeroZ    = ZeroZ
negSigned (PosZ k) = NegZ k
negSigned (NegZ k) = PosZ k

0 addSignedSuccL : (x, y : SignedCoord) -> addSigned (succZ x) y = succZ (addSigned x y)
addSignedSuccL ZeroZ ZeroZ        = Refl
addSignedSuccL ZeroZ (PosZ _)     = Refl
addSignedSuccL ZeroZ (NegZ Z)     = Refl
addSignedSuccL ZeroZ (NegZ (S _)) = Refl
addSignedSuccL (PosZ _) ZeroZ     = Refl
addSignedSuccL (PosZ _) (PosZ _)  = Refl
addSignedSuccL (PosZ a) (NegZ b)  = subSSuccL a b
addSignedSuccL (NegZ Z) ZeroZ     = Refl
addSignedSuccL (NegZ Z) (PosZ Z)  = Refl
addSignedSuccL (NegZ Z) (PosZ (S _)) = Refl
addSignedSuccL (NegZ Z) (NegZ _)  = Refl
addSignedSuccL (NegZ (S _)) ZeroZ = Refl
addSignedSuccL (NegZ (S a)) (PosZ b) =
  rewrite subSSuccR b a in sym (succPredInv (subS b a))
addSignedSuccL (NegZ (S _)) (NegZ _) = Refl

0 addSignedPredL : (x, y : SignedCoord) -> addSigned (predZ x) y = predZ (addSigned x y)
addSignedPredL x y =
  let h : (addSigned (succZ (predZ x)) y = succZ (addSigned (predZ x) y))
      h = addSignedSuccL (predZ x) y
      h' : (addSigned x y = succZ (addSigned (predZ x) y))
      h' = replace {p = \t => addSigned t y = succZ (addSigned (predZ x) y)} (succPredInv x) h
  in sym (trans (cong predZ h') (predSuccInv (addSigned (predZ x) y)))

0 assocPos : (k : Nat) -> (y, z : SignedCoord)
        -> addSigned (PosZ k) (addSigned y z) = addSigned (addSigned (PosZ k) y) z
assocPos Z y z =
  rewrite addSignedSuccL ZeroZ (addSigned y z) in
  rewrite addSignedSuccL ZeroZ y in
  rewrite addSignedSuccL y z in Refl
assocPos (S k) y z =
  rewrite addSignedSuccL (PosZ k) (addSigned y z) in
  rewrite addSignedSuccL (PosZ k) y in
  rewrite addSignedSuccL (addSigned (PosZ k) y) z in
  cong succZ (assocPos k y z)

0 assocNeg : (k : Nat) -> (y, z : SignedCoord)
        -> addSigned (NegZ k) (addSigned y z) = addSigned (addSigned (NegZ k) y) z
assocNeg Z y z =
  rewrite addSignedPredL ZeroZ (addSigned y z) in
  rewrite addSignedPredL ZeroZ y in
  rewrite addSignedPredL y z in Refl
assocNeg (S k) y z =
  rewrite addSignedPredL (NegZ k) (addSigned y z) in
  rewrite addSignedPredL (NegZ k) y in
  rewrite addSignedPredL (addSigned (NegZ k) y) z in
  cong predZ (assocNeg k y z)

0 addSignedAssoc : (x, y, z : SignedCoord)
              -> addSigned x (addSigned y z) = addSigned (addSigned x y) z
addSignedAssoc ZeroZ    _ _ = Refl
addSignedAssoc (PosZ k) y z = assocPos k y z
addSignedAssoc (NegZ k) y z = assocNeg k y z

0 addSignedInvLaw : (x : SignedCoord) -> addSigned x (negSigned x) = ZeroZ
addSignedInvLaw ZeroZ    = Refl
addSignedInvLaw (PosZ k) = subSDiag k
addSignedInvLaw (NegZ k) = subSDiag k

public export
MonoidCoord SignedCoord where
  combine = addSigned
  origin  = ZeroZ
  assoc   = addSignedAssoc

public export
GroupCoord SignedCoord where
  inverse = negSigned
  invLaw  = addSignedInvLaw

public export
signedToBoxInt : SignedCoord -> BoxInt
signedToBoxInt ZeroZ    = MkBoxInt 0
signedToBoxInt (PosZ k) = MkBoxInt (natToInteger (S k))
signedToBoxInt (NegZ k) = MkBoxInt (negate (natToInteger (S k)))

public export
boxIntToSigned : BoxInt -> SignedCoord
boxIntToSigned (MkBoxInt v) =
  if v == 0 then ZeroZ
  else if v > 0 then PosZ (cast (v - 1))
  else NegZ (cast ((-v) - 1))

public export
intToSigned : Integer -> SignedCoord
intToSigned v =
  if v == 0 then ZeroZ
  else if v > 0 then PosZ (integerToNat (v - 1))
  else NegZ (integerToNat ((-v) - 1))

public export
isOddSigned : SignedCoord -> Bool
isOddSigned ZeroZ    = False
isOddSigned (PosZ k) = isOddBox (MkBoxInt (natToInteger (S k)))
isOddSigned (NegZ k) = isOddBox (MkBoxInt (natToInteger (S k)))
