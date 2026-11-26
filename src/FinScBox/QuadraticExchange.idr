module FinScBox.QuadraticExchange

import FinScBox.BoxInt

%default total

------------------------------------------------------------------------
-- LOCAL 2-BODY QUADRATIC CONSERVATION EXCHANGE
-- Conserves `pA + pB` identically and monotonically bounds `2*(pA^2 + pB^2) + u^2`
-- via Wildberger's parametric Pythagorean triples `(m^2 - 1, 2m, m^2 + 1)`.
------------------------------------------------------------------------

||| Result of a local 2-body conservative quadratic exchange on `(pA, pB, u)`.
public export
record QuadraticPairResult where
  constructor MkQuadraticPairResult
  valA : BoxInt
  valB : BoxInt
  valU : BoxInt

public export
Eq QuadraticPairResult where
  a == b = a.valA == b.valA && a.valB == b.valB && a.valU == b.valU

public export
Show QuadraticPairResult where
  show r =
    "QuadraticPairResult(" ++ show r.valA ++ ", " ++ show r.valB ++ ", " ++ show r.valU ++ ")"

public export
sqPairBox : BoxInt -> BoxInt -> Integer
sqPairBox (MkBoxInt d) (MkBoxInt v) = d * d + v * v

public export
pythOddTieStep : (dDiff, numD : BoxInt) -> BoxInt
pythOddTieStep dDiff numD =
  if numD > MkBoxInt 0 || (boxIsZero numD && dDiff >= MkBoxInt 0)
    then MkBoxInt 1
    else MkBoxInt (-1)

public export
pythFallbackPair : (sSum, dDiff, numD, numU : BoxInt) -> (rDen : Integer) -> (BoxInt, BoxInt)
pythFallbackPair sSum dDiff numD numU rDen =
  let dRaw        = tdivPosBox numD rDen
      uRaw        = tdivPosBox numU rDen
      oddMismatch = isOddBox dRaw /= isOddBox sSum
  in if not oddMismatch
       then (dRaw, uRaw)
       else if dRaw > MkBoxInt 0
         then (subBox dRaw (MkBoxInt 1), uRaw)
         else if dRaw < MkBoxInt 0
           then (addBox dRaw (MkBoxInt 1), uRaw)
           else
             let dNew = pythOddTieStep dDiff numD
                 uNew = if boxIsZero numD
                          then if uRaw > MkBoxInt 0 then subBox uRaw (MkBoxInt 1)
                               else if uRaw < MkBoxInt 0 then addBox uRaw (MkBoxInt 1)
                               else uRaw
                          else uRaw
             in (dNew, uNew)

public export
pythChoosePair : (sSum, dDiff, numD, numU : BoxInt) -> (rDen, eOld : Integer) -> (BoxInt, BoxInt)
pythChoosePair sSum dDiff numD numU rDen eOld =
  let dR          = rdivPosBox numD rDen
      uR          = rdivPosBox numU rDen
      oddMismatch = isOddBox dR /= isOddBox sSum
  in if not oddMismatch
       then if sqPairBox dR uR <= eOld
              then (dR, uR)
              else pythFallbackPair sSum dDiff numD numU rDen
       else
         let MkBoxInt dRV = dR
             MkBoxInt nDV = numD
             prod         = dRV * rDen
         in if prod < nDV
              then let d1 = addBox dR (MkBoxInt 1)
                   in if sqPairBox d1 uR <= eOld
                        then (d1, uR)
                        else let d2 = subBox dR (MkBoxInt 1)
                             in if sqPairBox d2 uR <= eOld
                                  then (d2, uR)
                                  else pythFallbackPair sSum dDiff numD numU rDen
              else if prod > nDV
                then let d1 = subBox dR (MkBoxInt 1)
                     in if sqPairBox d1 uR <= eOld
                          then (d1, uR)
                          else let d2 = addBox dR (MkBoxInt 1)
                               in if sqPairBox d2 uR <= eOld
                                    then (d2, uR)
                                    else pythFallbackPair sSum dDiff numD numU rDen
                else
                  let dC = if dRV > 0 then subBox dR (MkBoxInt 1)
                           else if dRV < 0 then addBox dR (MkBoxInt 1)
                           else pythOddTieStep dDiff numD
                  in if sqPairBox dC uR <= eOld
                       then (dC, uR)
                       else pythFallbackPair sSum dDiff numD numU rDen

||| Parametric integer Pythagorean / Gaussian triple `(qtA, qtB, qtR)` (`qtA^2 + qtB^2 = qtR^2`),
||| forming a commutative `Monoid` under Gaussian composition with neutral `(1, 0, 1)`.
public export
record QuadraticTriple where
  constructor MkQuadraticTriple
  qtA : Integer
  qtB : Integer
  qtR : Integer

public export
Eq QuadraticTriple where
  x == y = x.qtA == y.qtA && x.qtB == y.qtB && x.qtR == y.qtR

public export
Show QuadraticTriple where
  show t = "QuadraticTriple(" ++ show t.qtA ++ ", " ++ show t.qtB ++ ", " ++ show t.qtR ++ ")"

||| Sterling recognition predicate certifying `qtR > 0` and `qtA^2 + qtB^2 == qtR^2`.
public export
isQuadraticTriple : QuadraticTriple -> Bool
isQuadraticTriple t = t.qtR > 0 && (t.qtA * t.qtA + t.qtB * t.qtB == t.qtR * t.qtR)

||| Generates the elementary Pythagorean triple `(m^2 - 1, 2m, m^2 + 1)` for `m >= 2`.
public export
pythGeneratorTriple : BoxInt -> QuadraticTriple
pythGeneratorTriple (MkBoxInt mIn) =
  let mVal = if mIn < 2 then 2 else mIn
      m2   = mVal * mVal
  in MkQuadraticTriple (m2 - 1) (2 * mVal) (m2 + 1)

||| Exact Gaussian composition `(a1 + i b1) * (a2 + i b2)` of two Pythagorean triples,
||| preserving `A^2 + B^2 = R^2` and multiplying rational spreads via spread polynomial composition.
public export
pythComposeTriple : QuadraticTriple -> QuadraticTriple -> QuadraticTriple
pythComposeTriple (MkQuadraticTriple a1 b1 r1) (MkQuadraticTriple a2 b2 r2) =
  MkQuadraticTriple (a1 * a2 - b1 * b2) (a1 * b2 + b1 * a2) (r1 * r2)

public export
Semigroup QuadraticTriple where
  (<+>) = pythComposeTriple

public export
Monoid QuadraticTriple where
  neutral = MkQuadraticTriple 1 0 1

||| Raises any `QuadraticTriple` to the `y`-th Gaussian power in the `QuadraticTriple` `Monoid`.
public export
powQuadraticTriple : Nat -> QuadraticTriple -> QuadraticTriple
powQuadraticTriple Z           _    = neutral
powQuadraticTriple (S Z)       base = base
powQuadraticTriple (S (S rem)) base = go rem base base
  where
    go : Nat -> QuadraticTriple -> QuadraticTriple -> QuadraticTriple
    go Z     step acc = acc <+> step
    go (S k) step acc = go k step (acc <+> step)

||| Computes the `y`-th composite Pythagorean triple `(A_y, B_y, R_y) = (A_1 + i B_1)^y`
||| whose spread is the exact `y`-fold spread polynomial `S_y(s(m)) = Z_y(4 s(m)) / 4`.
public export
pythPowerTriple : (y : Nat) -> (m : BoxInt) -> QuadraticTriple
pythPowerTriple Z       _ = neutral
pythPowerTriple y@(S _) m = powQuadraticTriple y (pythGeneratorTriple m)

||| Applies a local 2-body integer quadratic exchange specified by `MkQuadraticTriple aCoef bCoef rDen` (`a^2 + b^2 = r^2`)
||| to `(pA, pB, u)`, preserving `pA + pB` identically and monotonically bounding `2*(pA^2 + pB^2) + u^2`.
public export
exchangeQuadraticTriple : QuadraticTriple -> (pA, pB, u : BoxInt) -> QuadraticPairResult
exchangeQuadraticTriple (MkQuadraticTriple aCoef bCoef rDen) pA pB u =
  let dDiff = subBox pB pA
  in if (boxIsZero dDiff && boxIsZero u) || bCoef == 0 || rDen <= 0
       then MkQuadraticPairResult pA pB u
       else
         let sSum        = addBox pA pB
             MkBoxInt dV = dDiff
             MkBoxInt uV = u
             numD        = MkBoxInt (aCoef * dV + bCoef * uV)
             numU        = MkBoxInt (aCoef * uV - bCoef * dV)
             eOld        = dV * dV + uV * uV
             (dN, uN)    = pythChoosePair sSum dDiff numD numU rDen eOld
         in MkQuadraticPairResult (tdiv2Box (subBox sSum dN)) (tdiv2Box (addBox sSum dN)) uN

||| Single-step (`y = 1`) parametric `(m^2 - 1, 2m, m^2 + 1)` integer quadratic exchange
||| on `(pA, pB, u)` for any `m >= 2`, preserving `pA + pB` and bounding `2*(pA^2 + pB^2) + u^2`.
public export
exchangeQuadratic : (m, pA, pB, u : BoxInt) -> QuadraticPairResult
exchangeQuadratic m = exchangeQuadraticTriple (pythGeneratorTriple m)
