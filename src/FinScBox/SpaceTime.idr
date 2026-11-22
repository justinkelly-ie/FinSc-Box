module FinScBox.SpaceTime

import Data.Nat
import public Data.Maybe
import public Decidable.Equality
import public FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.Multiset

%default total

------------------------------------------------------------------------
-- 1. INDUCTIVE D-DIMENSIONAL SPATIAL COORDINATES (SpaceCoord dim)
------------------------------------------------------------------------

||| Inductive D-dimensional discrete spatial coordinate site.
public export
data SpaceCoord : (dim : Nat) -> Type where
  PointSite : SpaceCoord 0
  ConsSite  : Nat -> SpaceCoord dim -> SpaceCoord (S dim)

-- Canonical Wildberger Coordinate Aliases:
public export
Unixel : Type
Unixel = SpaceCoord 1

public export
Pixel : Type
Pixel = SpaceCoord 2

public export
VoxelSite : Type
VoxelSite = SpaceCoord 3

public export
BoxelSite : Type
BoxelSite = SpaceCoord 4

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS
------------------------------------------------------------------------

public export
mkUnixel : Nat -> Unixel
mkUnixel x = ConsSite x PointSite

public export
mkPixel : Nat -> Nat -> Pixel
mkPixel r c = ConsSite r (ConsSite c PointSite)

public export
mkVoxelSite : Nat -> Nat -> Nat -> VoxelSite
mkVoxelSite x y z = ConsSite x (ConsSite y (ConsSite z PointSite))

public export
mkBoxelSite : Nat -> Nat -> Nat -> Nat -> BoxelSite
mkBoxelSite x y z t = ConsSite x (ConsSite y (ConsSite z (ConsSite t PointSite)))

------------------------------------------------------------------------
-- 3. COORDINATE ACCESSORS & OPERATIONS
------------------------------------------------------------------------

public export
voxelX : VoxelSite -> Nat
voxelX (ConsSite x _) = x

public export
voxelY : VoxelSite -> Nat
voxelY (ConsSite _ (ConsSite y _)) = y

public export
voxelZ : VoxelSite -> Nat
voxelZ (ConsSite _ (ConsSite _ (ConsSite z _))) = z

public export
addVoxelSite : VoxelSite -> VoxelSite -> VoxelSite
addVoxelSite (ConsSite x1 (ConsSite y1 (ConsSite z1 PointSite)))
             (ConsSite x2 (ConsSite y2 (ConsSite z2 PointSite))) =
  mkVoxelSite (x1 + x2) (y1 + y2) (z1 + z2)

public export
dotVoxelSite : VoxelSite -> VoxelSite -> Nat
dotVoxelSite v1 v2 =
  (voxelX v1 * voxelX v2) + (voxelY v1 * voxelY v2) + (voxelZ v1 * voxelZ v2)

public export
quadranceVoxelSite : VoxelSite -> Nat
quadranceVoxelSite v = dotVoxelSite v v

------------------------------------------------------------------------
-- 4. EQUALITY & ORDERING
------------------------------------------------------------------------

public export
{dim : Nat} -> Eq (SpaceCoord dim) where
  PointSite == PointSite = True
  (ConsSite x1 r1) == (ConsSite x2 r2) = x1 == x2 && r1 == r2

public export
{dim : Nat} -> Ord (SpaceCoord dim) where
  compare PointSite PointSite = EQ
  compare (ConsSite x1 r1) (ConsSite x2 r2) =
    case compare x1 x2 of
      EQ => compare r1 r2
      other => other

public export
{dim : Nat} -> DiscreteCoord (SpaceCoord dim) where

------------------------------------------------------------------------
-- 5. D-DIMENSIONAL SPATIAL MULTISETS (Space dim)
------------------------------------------------------------------------

||| D-dimensional discrete space multiset:
||| An MSetBox over spatial sites in SpaceCoord dim.
public export
Space : (dim : Nat) -> Type
Space dim = MSetBox (SpaceCoord dim)

-- Canonical Wildberger Dimensional Multiset Aliases:
public export
PointMSet : Type
PointMSet = Space 0

public export
Vexel : Type
Vexel = Space 1

public export
PixelMSet : Type
PixelMSet = Space 2

public export
Voxel : Type
Voxel = Space 3

public export
Boxel : Type
Boxel = Space 4

------------------------------------------------------------------------
-- 6. INDUCTIVE DIMENSIONAL LIFTER
------------------------------------------------------------------------

||| Inductive site lift: injects a D-dimensional site into (D + 1) dimensions.
public export
liftSite : Nat -> SpaceCoord dim -> SpaceCoord (S dim)
liftSite x s = ConsSite x s

||| Inductive spatial multiset pushforward:
||| Lifts a multiset from Space D to Space (D + 1) along a new axis.
public export
liftSpace : {dim : Nat} -> Nat -> Space dim -> Space (S dim)
liftSpace nextAxis m =
  pushforwardMSet (\s => ConsSite nextAxis s) m


------------------------------------------------------------------------
-- 1. TIME HORIZONS & CAUSAL REGIMES OVER THE INTEGER AXIS Z
------------------------------------------------------------------------

||| Exhaustive classification of Time & Scale horizons over the integer axis Z:
public export
data Time : Type where
  ||| 1. Fixed compact interval [low, high] known at Stage 1 compile time
  StaticTime     : (low : Integer) -> (high : Integer) -> Time
  ||| 2. Forward causal ray [0, cap] governed by runtime `GohFuel`
  BoundedTime    : (cap : Nat) -> Time
  ||| 3. Backward UV ray [-cap, 0] governed by runtime `GohFuel`
  RetroTime      : (cap : Nat) -> Time
  ||| 4. Sliding causal interval [t - win, t] of fixed width `win`
  WindowedTime   : (win : Nat) -> Time
  ||| 5. Causal ray starting at Tick 0 with no preset upper bound (productive on demand)
  OpenFuture     : Time
  ||| 6. Two-sided stream with no preset lower or upper bound (productive in both directions)
  BilateralTime  : Time

-- Backward-compatible aliases for LaurentRegime terminology:
public export
LaurentRegime : Type
LaurentRegime = Time

public export
StaticHorizon : (low : Integer) -> (high : Integer) -> Time
StaticHorizon = StaticTime

public export
BoundedHorizon : (cap : Nat) -> Time
BoundedHorizon = BoundedTime

public export
RetroBoundedHorizon : (cap : Nat) -> Time
RetroBoundedHorizon = RetroTime

public export
WindowedHorizon : (win : Nat) -> Time
WindowedHorizon = WindowedTime

public export
BilateralOpen : Time
BilateralOpen = BilateralTime

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
DecEq Time where
  decEq (StaticTime l1 h1) (StaticTime l2 h2) =
    case (decEq l1 l2, decEq h1 h2) of
      (Yes Refl, Yes Refl) => Yes Refl
      (No contra, _)       => No (\case Refl => contra Refl)
      (_, No contra)       => No (\case Refl => contra Refl)
  decEq (BoundedTime c1) (BoundedTime c2) =
    case decEq c1 c2 of
      Yes Refl  => Yes Refl
      No contra => No (\case Refl => contra Refl)
  decEq (RetroTime c1) (RetroTime c2) =
    case decEq c1 c2 of
      Yes Refl  => Yes Refl
      No contra => No (\case Refl => contra Refl)
  decEq (WindowedTime w1) (WindowedTime w2) =
    case decEq w1 w2 of
      Yes Refl  => Yes Refl
      No contra => No (\case Refl => contra Refl)
  decEq OpenFuture          OpenFuture          = Yes Refl
  decEq BilateralTime       BilateralTime       = Yes Refl
  decEq (StaticTime _ _)    (BoundedTime _)     = No (\case Refl impossible)
  decEq (StaticTime _ _)    (RetroTime _)       = No (\case Refl impossible)
  decEq (StaticTime _ _)    (WindowedTime _)    = No (\case Refl impossible)
  decEq (StaticTime _ _)    OpenFuture          = No (\case Refl impossible)
  decEq (StaticTime _ _)    BilateralTime       = No (\case Refl impossible)
  decEq (BoundedTime _)     (StaticTime _ _)    = No (\case Refl impossible)
  decEq (BoundedTime _)     (RetroTime _)       = No (\case Refl impossible)
  decEq (BoundedTime _)     (WindowedTime _)    = No (\case Refl impossible)
  decEq (BoundedTime _)     OpenFuture          = No (\case Refl impossible)
  decEq (BoundedTime _)     BilateralTime       = No (\case Refl impossible)
  decEq (RetroTime _)       (StaticTime _ _)    = No (\case Refl impossible)
  decEq (RetroTime _)       (BoundedTime _)     = No (\case Refl impossible)
  decEq (RetroTime _)       (WindowedTime _)    = No (\case Refl impossible)
  decEq (RetroTime _)       OpenFuture          = No (\case Refl impossible)
  decEq (RetroTime _)       BilateralTime       = No (\case Refl impossible)
  decEq (WindowedTime _)    (StaticTime _ _)    = No (\case Refl impossible)
  decEq (WindowedTime _)    (BoundedTime _)     = No (\case Refl impossible)
  decEq (WindowedTime _)    (RetroTime _)       = No (\case Refl impossible)
  decEq (WindowedTime _)    OpenFuture          = No (\case Refl impossible)
  decEq (WindowedTime _)    BilateralTime       = No (\case Refl impossible)
  decEq OpenFuture          (StaticTime _ _)    = No (\case Refl impossible)
  decEq OpenFuture          (BoundedTime _)     = No (\case Refl impossible)
  decEq OpenFuture          (RetroTime _)       = No (\case Refl impossible)
  decEq OpenFuture          (WindowedTime _)    = No (\case Refl impossible)
  decEq OpenFuture          BilateralTime       = No (\case Refl impossible)
  decEq BilateralTime       (StaticTime _ _)    = No (\case Refl impossible)
  decEq BilateralTime       (BoundedTime _)     = No (\case Refl impossible)
  decEq BilateralTime       (RetroTime _)       = No (\case Refl impossible)
  decEq BilateralTime       (WindowedTime _)    = No (\case Refl impossible)
  decEq BilateralTime       OpenFuture          = No (\case Refl impossible)

||| Non-recursive helper combining a compact `[x, y]` `StaticTime` with any `Time`.
public export
convolveWithStatic : Integer -> Integer -> Time -> Time
convolveWithStatic x y (StaticTime a b)     = StaticTime (x + a) (y + b)
convolveWithStatic x y (BoundedTime c)      =
  let span = cast {to = Nat} (abs (y - x))
      posShift = if x >= 0 then cast {to = Nat} x else 0
  in BoundedTime (span + posShift + c)
convolveWithStatic x y (RetroTime c)        =
  let span = cast {to = Nat} (abs (y - x))
      negShift = if y <= 0 then cast {to = Nat} (-y) else 0
  in RetroTime (span + negShift + c)
convolveWithStatic x y (WindowedTime w)     = WindowedTime (cast (abs (y - x)) + w)
convolveWithStatic _ _ OpenFuture           = OpenFuture
convolveWithStatic _ _ BilateralTime        = BilateralTime

||| Compile-time Cauchy Convolution Admissibility Matrix:
||| Returns `Just outputTime` when convolution `A * B` has guaranteed finite fiber sums
||| at every degree `n`, and `Nothing` when the fiber accumulation lacks a finite bound.
||| Strictly non-recursive so `%default total` verifies coverage and termination trivially.
public export
admissibleConvolution : Time -> Time -> Maybe Time
-- 1. Compact `StaticTime` convolves cleanly with every time horizon:
admissibleConvolution (StaticTime x y) r                = Just (convolveWithStatic x y r)
admissibleConvolution r                (StaticTime a b) = Just (convolveWithStatic a b r)

-- 2. Same-direction `BoundedTime` and `OpenFuture` rays (causal power series):
admissibleConvolution (BoundedTime c1) (BoundedTime c2) = Just (BoundedTime (c1 + c2))
admissibleConvolution (RetroTime c1)   (RetroTime c2)   = Just (RetroTime (c1 + c2))
admissibleConvolution (BoundedTime _)  OpenFuture       = Just OpenFuture
admissibleConvolution OpenFuture       (BoundedTime _)  = Just OpenFuture
admissibleConvolution OpenFuture       OpenFuture       = Just OpenFuture

-- 3. Mixed forward/backward finite rays `[0, c1] * [-c2, 0] = [-c2, c1]` (compact `StaticTime`):
admissibleConvolution (BoundedTime c1) (RetroTime c2)   = Just (StaticTime (- cast c2) (cast c1))
admissibleConvolution (RetroTime c1)   (BoundedTime c2) = Just (StaticTime (- cast c1) (cast c2))

-- 4. `WindowedTime` local causal patches (finite sliding buffer bounds overlap):
admissibleConvolution (WindowedTime w1) (WindowedTime w2) = Just (WindowedTime (min w1 w2))
admissibleConvolution (WindowedTime w)  (BoundedTime c)   = Just (WindowedTime (min w c))
admissibleConvolution (BoundedTime c)   (WindowedTime w)  = Just (WindowedTime (min w c))
admissibleConvolution (WindowedTime w)  (RetroTime c)     = Just (WindowedTime (min w c))
admissibleConvolution (RetroTime c)     (WindowedTime w)  = Just (WindowedTime (min w c))
admissibleConvolution (WindowedTime w)  OpenFuture        = Just (WindowedTime w)
admissibleConvolution OpenFuture        (WindowedTime w)  = Just (WindowedTime w)
admissibleConvolution (WindowedTime w)  BilateralTime     = Just (WindowedTime w)
admissibleConvolution BilateralTime     (WindowedTime w)  = Just (WindowedTime w)

-- 5. Unbounded opposite-ray / bilateral overlaps (statically disallowed):
admissibleConvolution (RetroTime _)     OpenFuture        = Nothing
admissibleConvolution OpenFuture        (RetroTime _)     = Nothing
admissibleConvolution (BoundedTime _)   BilateralTime     = Nothing
admissibleConvolution BilateralTime     (BoundedTime _)   = Nothing
admissibleConvolution (RetroTime _)     BilateralTime     = Nothing
admissibleConvolution BilateralTime     (RetroTime _)     = Nothing
admissibleConvolution OpenFuture        BilateralTime     = Nothing
admissibleConvolution BilateralTime     OpenFuture        = Nothing
admissibleConvolution BilateralTime     BilateralTime     = Nothing

||| Analytical fiber capacity at origin key 0 (\alpha^0) when convolving
||| forward ray `BoundedTime c1` with backward ray `RetroTime c2`.
public export
originFiberCapacity : (c1, c2 : Nat) -> Nat
originFiberCapacity c1 c2 = min c1 c2

public export
minInt4 : Integer -> Integer -> Integer -> Integer -> Integer
minInt4 a b c d =
  let ab = if a <= b then a else b
      cd = if c <= d then c else d
  in if ab <= cd then ab else cd

public export
maxInt4 : Integer -> Integer -> Integer -> Integer -> Integer
maxInt4 a b c d =
  let ab = if a >= b then a else b
      cd = if c >= d then c else d
  in if ab >= cd then ab else cd

||| Tight static lower exponent bound under Level-2 caretation (`[l1, h1] * [l2, h2]`).
public export
caretStaticLow : Integer -> Integer -> Integer -> Integer -> Integer
caretStaticLow l1 h1 l2 h2 = minInt4 (l1 * l2) (l1 * h2) (h1 * l2) (h1 * h2)

||| Tight static upper exponent bound under Level-2 caretation (`[l1, h1] * [l2, h2]`).
public export
caretStaticHigh : Integer -> Integer -> Integer -> Integer -> Integer
caretStaticHigh l1 h1 l2 h2 = maxInt4 (l1 * l2) (l1 * h2) (h1 * l2) (h1 * h2)

||| Compile-time admissibility and time horizon transformation for Level-2+ Dirichlet Caretation (`^`).
||| Static intervals multiply corners, bounded positive/retrograde rays scale degree products,
||| and open unwindowed streams are statically disallowed.
public export
caretTime : Time -> Time -> Maybe Time
caretTime (StaticTime l1 h1)     (StaticTime l2 h2)     =
  Just (StaticTime (caretStaticLow l1 h1 l2 h2) (caretStaticHigh l1 h1 l2 h2))
caretTime (BoundedTime c1)       (BoundedTime c2)       = Just (BoundedTime (c1 * c2))
caretTime (RetroTime c1)         (RetroTime c2)         = Just (BoundedTime (c1 * c2))
caretTime (WindowedTime w1)      (WindowedTime w2)      = Just (WindowedTime (min w1 w2))
caretTime _                      _                      = Nothing

public export
caretRegime : Time -> Time -> Maybe Time
caretRegime = caretTime

||| Tightens a `Time` horizon upon promotion to the zero-free positive `Poly*` (`e >= 1`) domain.
public export
polyStarTime : Time -> Time
polyStarTime (StaticTime l h) = StaticTime (if l >= 1 then l else 1) (if h >= 1 then h else 1)
polyStarTime (RetroTime _)    = StaticTime 1 1
polyStarTime t                = t

public export
polyStarRegime : Time -> Time
polyStarRegime = polyStarTime

||| Proof alias unlocking type-safe `*` only when `admissibleConvolution tA tB` succeeds.
public export
CanConvolve : Time -> Time -> Type
CanConvolve tA tB = IsJust (admissibleConvolution tA tB)

||| Constructive `Dec` recognizer deciding Cauchy convolution admissibility (`recognition-rule.md`).
public export
recognizeCanConvolve : (tA, tB : Time) -> Dec (CanConvolve tA tB)
recognizeCanConvolve tA tB with (admissibleConvolution tA tB)
  recognizeCanConvolve tA tB | Just x  = Yes ItIsJust
  recognizeCanConvolve tA tB | Nothing = No (\prf => absurd prf)

||| Proof witness holding strictly for compact or bounded Time horizons,
||| statically blocking global reductions on open `OpenFuture` and `BilateralTime` rays (`Rule 08` §1 & §5).
public export
data IsBoundedTime : Time -> Type where
  BoundedStatic   : {l, h : Integer} -> IsBoundedTime (StaticTime l h)
  BoundedForward  : {c : Nat} -> IsBoundedTime (BoundedTime c)
  BoundedRetro    : {c : Nat} -> IsBoundedTime (RetroTime c)
  BoundedWindowed : {w : Nat} -> IsBoundedTime (WindowedTime w)

public export
BoundedRegime : Time -> Type
BoundedRegime = IsBoundedTime

public export
Uninhabited (IsBoundedTime OpenFuture) where
  uninhabited BoundedStatic   impossible
  uninhabited BoundedForward  impossible
  uninhabited BoundedRetro    impossible
  uninhabited BoundedWindowed impossible

public export
Uninhabited (IsBoundedTime BilateralTime) where
  uninhabited BoundedStatic   impossible
  uninhabited BoundedForward  impossible
  uninhabited BoundedRetro    impossible
  uninhabited BoundedWindowed impossible

||| Constructive `Dec` recognizer certifying a `Time` horizon is bounded prior to global
||| `sumHMSet`, `totalMass`, or free-energy reductions (`recognition-rule.md`).
public export
recognizeBoundedTime : (t : Time) -> Dec (IsBoundedTime t)
recognizeBoundedTime (StaticTime _ _)   = Yes BoundedStatic
recognizeBoundedTime (BoundedTime _)    = Yes BoundedForward
recognizeBoundedTime (RetroTime _)      = Yes BoundedRetro
recognizeBoundedTime (WindowedTime _)   = Yes BoundedWindowed
recognizeBoundedTime OpenFuture         = No absurd
recognizeBoundedTime BilateralTime      = No absurd

public export
recognizeBoundedRegime : (t : Time) -> Dec (IsBoundedTime t)
recognizeBoundedRegime = recognizeBoundedTime
