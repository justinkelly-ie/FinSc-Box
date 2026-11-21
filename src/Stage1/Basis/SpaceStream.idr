module Stage1.Basis.SpaceStream

import Data.Nat
import Stage0.BoxInt
import Stage0.Interfaces
import Stage0.Box
import Stage0.Multiset
import Stage0.Multiplicity
import Stage0.HereditaryMSet
import Stage1.Basis.Space
import Stage1.Basis.Time

%default total

------------------------------------------------------------------------
-- 1. STREAM STEP & TIME-INDEXED ONGOING STREAM (`TimeStream t a`)
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

||| Wildberger `OnSeq` alias for `TimeStream`.
public export
OnSeq : (0 t : Time) -> (a : Type) -> Type
OnSeq = TimeStream

public export
Functor (TimeStream t) where
  map f (MkTimeStream s at) = MkTimeStream s (\n => map f (at n))

------------------------------------------------------------------------
-- 2. STREAMING VARIANTS OF BASE TYPES (ALPHABETICALLY ALIGNED `*Stream`)
------------------------------------------------------------------------

||| Streaming Multiplicity-parameterised coordinate multiset (`MSet m k`).
public export
MSetStream : (0 t : Time) -> (m : Type) -> (k : Type) -> Type
MSetStream t m k = TimeStream t (MSet m k)

||| Streaming signed `BoxInt` coordinate multiset (`MSetBox k`).
public export
MSetBoxStream : (0 t : Time) -> (k : Type) -> Type
MSetBoxStream t k = TimeStream t (MSetBox k)

||| Streaming D-dimensional discrete space multiset (`Space dim`).
public export
SpaceStream : (0 t : Time) -> (dim : Nat) -> Type
SpaceStream t dim = TimeStream t (Space dim)

||| Streaming 0D point space multiset (`PointMSet = Space 0`).
public export
PointMSetStream : (0 t : Time) -> Type
PointMSetStream t = SpaceStream t 0

||| Streaming 1D line unixel multiset (`Vexel = Space 1`).
public export
VexelStream : (0 t : Time) -> Type
VexelStream t = SpaceStream t 1

||| Streaming 2D planar pixel multiset (`PixelMSet = Space 2`).
public export
PixelMSetStream : (0 t : Time) -> Type
PixelMSetStream t = SpaceStream t 2

||| Streaming 3D spatial volume multiset (`Voxel = Space 3`).
public export
VoxelStream : (0 t : Time) -> Type
VoxelStream t = SpaceStream t 3

||| Streaming 4D spacetime multiset (`Boxel = Space 4`).
public export
BoxelStream : (0 t : Time) -> Type
BoxelStream t = SpaceStream t 4

||| Streaming recursive hereditary multiset (`HereditaryMSet m`).
public export
HereditaryMSetStream : (0 t : Time) -> (m : Type) -> Type
HereditaryMSetStream t m = TimeStream t (HereditaryMSet m)

||| Streaming pure signed `BoxInt` hereditary multiset (`PureMultiset`).
public export
PureMultisetStream : (0 t : Time) -> Type
PureMultisetStream t = HereditaryMSetStream t BoxInt

------------------------------------------------------------------------
-- 3. SMART CONSTRUCTORS & VACUUM-SKIP PROMOTION
------------------------------------------------------------------------

||| Promotes a tick generator `Nat -> MSet m k` into an `MSetStream OpenFuture m k`:
||| Any tick that annihilates to `BoxLeaf` (`[]`, e.g., `[+1, -1] = []`) is automatically
||| promoted to `StreamSkip` so vacuum ticks consume zero `GohFuel`!
public export
mkMSetStream : (start : Nat) -> (Nat -> MSet m k) -> MSetStream OpenFuture m k
mkMSetStream start gen =
  MkTimeStream start (\n =>
    if n < start
      then StreamSkip
      else case gen n of
             BoxLeaf => StreamSkip
             mset    => StreamYield mset)

||| Promotes a bounded tick generator `(tick : Nat) -> MSet m k` active on `[start, start + cap)`
||| into a `BoundedTime cap` stream that emits `StreamDone` once `tick >= start + cap`.
public export
mkBoundedMSetStream : (cap : Nat) -> (start : Nat) -> (Nat -> MSet m k) -> MSetStream (BoundedTime cap) m k
mkBoundedMSetStream cap start gen =
  MkTimeStream start (\n =>
    if n < start
      then StreamSkip
      else if n >= start + cap
        then StreamDone
        else case gen n of
               BoxLeaf => StreamSkip
               mset    => StreamYield mset)

||| Constant ongoing multiset stream repeating `m` at every tick `>= start`.
||| If `m` is `BoxLeaf` (vacuum), every tick emits `StreamSkip`.
public export
constantMSetStream : (start : Nat) -> MSet m k -> MSetStream OpenFuture m k
constantMSetStream start m = mkMSetStream start (\_ => m)

||| Pointwise superposition of two `MSetBoxStream`s:
||| If two yielded multisets at tick `n` annihilate to `BoxLeaf` (`[+1, -1] = []`),
||| the combined step automatically becomes `StreamSkip` (zero `GohFuel` cost!).
public export
addMSetBoxStream : DiscreteCoord k =>
                   MSetBoxStream t k ->
                   MSetBoxStream t k ->
                   MSetBoxStream t k
addMSetBoxStream (MkTimeStream s1 at1) (MkTimeStream s2 at2) =
  MkTimeStream (max s1 s2) (\n =>
    case (at1 n, at2 n) of
      (StreamDone, StreamDone) => StreamDone
      (StreamDone, other)      => other
      (other,      StreamDone) => other
      (StreamSkip, StreamSkip) => StreamSkip
      (StreamSkip, StreamYield m2) =>
        case m2 of
          BoxLeaf => StreamSkip
          _       => StreamYield m2
      (StreamYield m1, StreamSkip) =>
        case m1 of
          BoxLeaf => StreamSkip
          _       => StreamYield m1
      (StreamYield m1, StreamYield m2) =>
        let merged = addMSet m1 m2
        in case merged of
             BoxLeaf => StreamSkip
             _       => StreamYield merged)

||| Lifts a `SpaceStream t dim` to `SpaceStream t (S dim)` along a new coordinate axis.
public export
liftSpaceStream : {dim : Nat} -> Nat -> SpaceStream t dim -> SpaceStream t (S dim)
liftSpaceStream nextAxis = map (liftSpace nextAxis)

||| Coordinate pushforward across a live `MSetBoxStream`:
||| Re-indexes every yielded multiset along `f : k1 -> k2` (`pushforwardMSet f`),
||| summing colliding multiplicities and automatically promoting any annihilated
||| `BoxLeaf` tick to `StreamSkip` so it consumes zero `GohFuel`!
public export
pushforwardMSetStream : DiscreteCoord k2 =>
                        (k1 -> k2) ->
                        MSetBoxStream t k1 ->
                        MSetBoxStream t k2
pushforwardMSetStream f (MkTimeStream start at) =
  MkTimeStream start (\n =>
    case at n of
      StreamDone    => StreamDone
      StreamSkip    => StreamSkip
      StreamYield m =>
        let pushed = pushforwardMSet f m
        in case pushed of
             BoxLeaf => StreamSkip
             _       => StreamYield pushed)

||| 120-degree / equilateral spread s = 3/4 cyclic 3D rotation of a `VoxelSite` (`(x, y, z) -> (z, x, y)`)
||| around the diagonal axis `(1, 1, 1)` (Wildberger's projective proportion `[1 : 1 : 1 : 1]`).
public export
CycleVoxelSite : VoxelSite -> VoxelSite
CycleVoxelSite (ConsSite x (ConsSite y (ConsSite z PointSite))) =
  mkVoxelSite z x y

public export
cycleVoxelSite : VoxelSite -> VoxelSite
cycleVoxelSite = CycleVoxelSite

||| Active 3D rotational pushforward across a live `VoxelStream`.
public export
rotateVoxelStream : (VoxelSite -> VoxelSite) -> VoxelStream t -> VoxelStream t
rotateVoxelStream = pushforwardMSetStream

||| Temporal Pullback (f^*): unfolds a tick-fiber generator into an `MSetStream OpenFuture m k`,
||| automatically promoting any annihilated `BoxLeaf` tick to `StreamSkip`.
public export
pullbackToStream : (start : Nat) -> (Nat -> MSet m k) -> MSetStream OpenFuture m k
pullbackToStream = mkMSetStream

------------------------------------------------------------------------
-- 4. FUEL EXHAUSTION & TIME-HORIZON FREEZE-OUT (`SolidifiedStream`)
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

||| Specialised freeze-out runner for `MSetBoxStream t k` (and `SpaceStream t dim`)
||| using explicit yield capacity `yieldBudget` and causal search horizon `stepBudget`.
public export
freezeMSetBoxStream :
  DiscreteCoord k =>
  {0 t : Time} ->
  (g           : Nat) ->
  (cap         : Nat) ->
  (yieldBudget : Nat) ->
  (stepBudget  : Nat) ->
  MSetBoxStream t k ->
  SolidifiedStream (StaticTime (- cast g) (cast cap)) cap (MSetBox k)
freezeMSetBoxStream g cap yieldBudget stepBudget strm =
  freezeTimeStreamWith g cap (MkGohFuel yieldBudget) stepBudget addMSet emptyMSet strm

||| Specialised freeze-out runner for `SpaceStream t dim` (`PointMSetStream`, `VexelStream`,
||| `PixelMSetStream`, `VoxelStream`, `BoxelStream`) at retrograde layer depth `g` and capacity `cap`.
public export
freezeSpaceStream :
  {dim : Nat} ->
  {0 t : Time} ->
  (g           : Nat) ->
  (cap         : Nat) ->
  (yieldBudget : Nat) ->
  (stepBudget  : Nat) ->
  SpaceStream t dim ->
  SolidifiedStream (StaticTime (- cast g) (cast cap)) cap (Space dim)
freezeSpaceStream g cap yieldBudget stepBudget strm =
  freezeMSetBoxStream g cap yieldBudget stepBudget strm

||| Temporal Pushforward (f_*): collapses/freezes a `SpaceStream t dim` across time
||| into a static `SolidifiedStream (StaticTime (- cast g) (cast cap)) cap (Space dim)`.
public export
pushforwardFromStream :
  {dim : Nat} ->
  {0 t : Time} ->
  (g           : Nat) ->
  (cap         : Nat) ->
  (yieldBudget : Nat) ->
  (stepBudget  : Nat) ->
  SpaceStream t dim ->
  SolidifiedStream (StaticTime (- cast g) (cast cap)) cap (Space dim)
pushforwardFromStream = freezeSpaceStream

||| Pushes a solidified relic multiset forward along a spatial map `f : k1 -> k2` (`R_*`).
public export
pushforwardRelicBy :
  DiscreteCoord k2 =>
  (k1 -> k2) ->
  SolidifiedStream t cap (MSetBox k1) ->
  SolidifiedStream t cap (MSetBox k2)
pushforwardRelicBy f s = { relicState $= pushforwardMSet f } s

||| Rotates a solidified spatial relic multiset along a coordinate symmetry `f` (`R_*`).
public export
rotateRelicBy :
  {dim : Nat} ->
  (SpaceCoord dim -> SpaceCoord dim) ->
  SolidifiedStream t cap (Space dim) ->
  SolidifiedStream t cap (Space dim)
rotateRelicBy = pushforwardRelicBy

||| Final Sentence Verb (`YieldParticle` / `yieldParticle`):
||| Extracts the solidified spatial multiset particle directly from a `SolidifiedStream`.
||| Usage: `VacuumRoot |> unfoldAtLayer g |> freezeAtHorizon 12 |> YieldParticle`
public export
YieldParticle : SolidifiedStream t cap a -> a
YieldParticle s = s.relicState

public export
yieldParticle : SolidifiedStream t cap a -> a
yieldParticle = YieldParticle
