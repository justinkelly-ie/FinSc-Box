module FinScBox.Time

import Data.Nat
import public Data.Maybe
import public Decidable.Equality
import public FinScBox.BoxInt
import FinScBox.HereditaryMSet

%default total

------------------------------------------------------------------------
-- 1. TIME HORIZONS OVER THE INTEGER AXIS Z
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


------------------------------------------------------------------------
-- 2. STREAM STEP, TIME STREAM & LOCAL BRESENHAM PACING
------------------------------------------------------------------------

||| What happens at a single tick `n` of a TimeStream:
||| - `StreamDone`  : Stream has naturally terminated (ground-state relaxation)
||| - `StreamSkip`  : Vacuum annihilation (`[+1, -1] = []`) or silent tick
|||                   (consumes 1 causal `stepBudget`, 0 `GohFuel`!)
||| - `StreamYield` : Emits an active multiset term/delta
|||                   (consumes 1 causal `stepBudget` AND 1 `GohFuel`)
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

public export
Functor StreamStep where
  map _ StreamDone      = StreamDone
  map _ StreamSkip      = StreamSkip
  map f (StreamYield x) = StreamYield (f x)

||| A Time-indexed ongoing sequence / stream starting at `startTick`.
||| (Wildberger's `OnSeq` indexed by `Time` with `StreamStep` transitions).
public export
record TimeStream (0 t : Time) (a : Type) where
  constructor MkTimeStream
  startTick : Nat
  stepAt    : Nat -> StreamStep a


public export
Functor (TimeStream t) where
  map f (MkTimeStream s at) = MkTimeStream s (\n => map f (at n))

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
-- 3. FUEL EXHAUSTION & TIME-HORIZON FREEZE-OUT
------------------------------------------------------------------------

||| Termination classification when a `TimeStream` halts and freezes out into `StaticTime`:
||| - `YieldExhausted`     : Energy/yield quota (`GohFuel cap`) reached 0 (crystal / particle freeze-out)
||| - `StepHorizonReached` : Causal search horizon (`stepBudget`) reached 0 while yield remained (kinematic decoupling)
||| - `NaturalCompletion`  : Stream emitted `StreamDone` before exhausting either budget (ground-state relaxation)
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

||| Certified static relic produced when a dynamic `TimeStream` runs out of fuel
||| or completes at retrograde depth `g` (`RetroTime g`) and capacity `cap` (`BoundedTime cap`).
||| Its phantom Time index transitions to `StaticTime (- cast g) (cast cap)`!
public export
record SolidifiedStream (0 frozenTime : Time) (cap : Nat) (a : Type) where
  constructor MkSolidifiedStream
  relicState     : a
  freezeReason   : StreamFreezeReason
  freezeTick     : Nat
  yieldsConsumed : Nat
  stepsConsumed  : Nat
  remainingYield : GohFuel cap
  remainingSteps : Nat

public export
(Eq a) => Eq (SolidifiedStream t cap a) where
  s1 == s2 =
    s1.relicState == s2.relicState &&
    s1.freezeReason == s2.freezeReason &&
    s1.freezeTick == s2.freezeTick &&
    s1.yieldsConsumed == s2.yieldsConsumed &&
    s1.stepsConsumed == s2.stepsConsumed

||| Decoupled Yield/Step Freeze-Out Evaluator over any `TimeStream t a`:
||| - `StreamSkip` consumes ONLY 1 unit of `stepBudget` (`sRem`), never draining `yieldFuel` (`yRem`)!
||| - `StreamYield term` consumes BOTH 1 unit of `yieldFuel` and 1 unit of `stepBudget`,
|||   accumulating `combine term acc`.
||| - Freezes into `SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a`.
public export
freezeTimeStreamWith :
  {0 t : Time} ->
  (g          : Nat) ->
  (cap        : Nat) ->
  (yieldFuel  : GohFuel cap) ->
  (stepBudget : Nat) ->
  (combine    : a -> a -> a) ->
  (initAcc    : a) ->
  TimeStream t a ->
  SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a
freezeTimeStreamWith g cap yieldFuel stepBudget combine initAcc (MkTimeStream start at) =
  loop (gohSteps yieldFuel) stepBudget start 0 0 initAcc
  where
    loop : (yRem : Nat) ->
           (sRem : Nat) ->
           (currTick : Nat) ->
           (yUsed : Nat) ->
           (sUsed : Nat) ->
           (acc : a) ->
           SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a
    loop Z sRem currTick yUsed sUsed acc =
      MkSolidifiedStream acc YieldExhausted currTick yUsed sUsed (MkGohFuel 0) sRem
    loop yRem Z currTick yUsed sUsed acc =
      MkSolidifiedStream acc StepHorizonReached currTick yUsed sUsed (MkGohFuel yRem) 0
    loop (S yRem) (S sRem) currTick yUsed sUsed acc =
      case at currTick of
        StreamDone =>
          MkSolidifiedStream acc NaturalCompletion currTick yUsed sUsed (MkGohFuel (S yRem)) (S sRem)
        StreamSkip =>
          loop (S yRem) sRem (S currTick) yUsed (S sUsed) acc
        StreamYield term =>
          loop yRem sRem (S currTick) (S yUsed) (S sUsed) (combine term acc)

||| Stateful Streaming Freeze-Out Evaluator over an initial state `initA : a` populated at `t = 0`:
||| At each tick, `stepFn acc` emits `(StreamStep a, yieldCost, skipsSaved)`:
||| - `StreamDone`      : ground-state relaxation (`NaturalCompletion`)
||| - `StreamSkip`      : consumes `0` `yieldFuel` and `1` `stepBudget`, banking `skipsSaved`
||| - `StreamYield nxt` : if `remYield < yieldCost`, freezes out with `YieldExhausted`;
|||                       otherwise consumes `yieldCost` of `yieldFuel` and `1` `stepBudget`.
public export
freezeStateStreamWith :
  (g          : Nat) ->
  (cap        : Nat) ->
  (yieldFuel  : GohFuel cap) ->
  (stepBudget : Nat) ->
  (stepFn     : a -> (StreamStep a, Nat, Nat)) ->
  (initA      : a) ->
  (SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a, Nat)
freezeStateStreamWith g cap yieldFuel stepBudget stepFn initA =
  loop (gohSteps yieldFuel) stepBudget 0 0 0 0 initA
  where
    loop : (yRem, sRem, currTick, yUsed, sUsed, skAcc : Nat) ->
           (acc : a) ->
           (SolidifiedStream (StaticTime (- cast g) (cast cap)) cap a, Nat)
    loop yRem Z currTick yUsed sUsed skAcc acc =
      (MkSolidifiedStream acc StepHorizonReached currTick yUsed sUsed (MkGohFuel yRem) 0, skAcc)
    loop yRem (S sRem) currTick yUsed sUsed skAcc acc =
      case stepFn acc of
        (StreamDone, _, sk) =>
          (MkSolidifiedStream acc NaturalCompletion currTick yUsed sUsed (MkGohFuel yRem) (S sRem), skAcc + sk)
        (StreamSkip, _, sk) =>
          loop yRem sRem (S currTick) yUsed (S sUsed) (skAcc + sk) acc
        (StreamYield nxt, yCost, sk) =>
          if yRem < yCost
            then (MkSolidifiedStream acc YieldExhausted currTick yUsed sUsed (MkGohFuel yRem) (S sRem), skAcc)
            else loop (minus yRem yCost) sRem (S currTick) (yUsed + yCost) (S sUsed) (skAcc + sk) nxt

