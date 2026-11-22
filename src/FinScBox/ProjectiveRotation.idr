module FinScBox.ProjectiveRotation

import Data.Vect
import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.Multiset

%default total

------------------------------------------------------------------------
-- 1. 3D PROJECTIVE ROTATION PROPORTIONS (WILDBERGER SO(3; Q))
------------------------------------------------------------------------

||| A Projective Rotation Proportion (x : t : r : s):
||| Parameterizes an exact 3D rational rotation without continuous angles or square roots.
public export
record ProjectiveProportion where
  constructor MkProjectiveProportion
  xCoord : BoxInt
  tCoord : BoxInt
  rCoord : BoxInt
  sCoord : BoxInt

public export
Eq ProjectiveProportion where
  (MkProjectiveProportion x1 t1 r1 s1) == (MkProjectiveProportion x2 t2 r2 s2) =
    x1 == x2 && t1 == t2 && r1 == r2 && s1 == s2

public export
Show ProjectiveProportion where
  show (MkProjectiveProportion x t r s) =
    "(" ++ show x ++ " : " ++ show t ++ " : " ++ show r ++ " : " ++ show s ++ ")"

||| Identity rotation: [1 : 0 : 0 : 0].
public export
idProportion : ProjectiveProportion
idProportion = MkProjectiveProportion (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0)

||| Euclidean quadrance of a 3D vector: Q(v) = t^2 + r^2 + s^2.
public export
quadranceEuc3 : Vect 3 BoxInt -> BoxInt
quadranceEuc3 [t, r, s] = (t * t) + (r * r) + (s * s)

||| Exact cross product of two 3D vectors: v1 x v2.
public export
crossProduct3 : Vect 3 BoxInt -> Vect 3 BoxInt -> Vect 3 BoxInt
crossProduct3 [t1, r1, s1] [t2, r2, s2] =
  [ (r1 * s2) - (s1 * r2)
  , (s1 * t2) - (t1 * s2)
  , (t1 * r2) - (r1 * t2)
  ]

||| Exact dot product of two 3D vectors: v1 . v2.
public export
dotProduct3 : Vect 3 BoxInt -> Vect 3 BoxInt -> BoxInt
dotProduct3 [t1, r1, s1] [t2, r2, s2] =
  (t1 * t2) + (r1 * r2) + (s1 * s2)

||| Exact quaternion composition of two projective proportions: p2 * p1.
public export
composeProportion : ProjectiveProportion -> ProjectiveProportion -> ProjectiveProportion
composeProportion (MkProjectiveProportion x2 t2 r2 s2)
                  (MkProjectiveProportion x1 t1 r1 s1) =
  let v1 = [t1, r1, s1]
      v2 = [t2, r2, s2]
      xOut = (x1 * x2) - dotProduct3 v1 v2
      [tCross, rCross, sCross] = crossProduct3 v2 v1
      tOut = (x1 * t2) + (x2 * t1) + tCross
      rOut = (x1 * r2) + (x2 * r1) + rCross
      sOut = (x1 * s2) + (x2 * s1) + sCross
  in MkProjectiveProportion xOut tOut rOut sOut

||| Inverse rotation proportion: [x : -t : -r : -s].
public export
inverseProportion : ProjectiveProportion -> ProjectiveProportion
inverseProportion (MkProjectiveProportion x t r s) =
  MkProjectiveProportion x (negate t) (negate r) (negate s)

------------------------------------------------------------------------
-- 2. ROTATION MATRIX GENERATION & VECTOR ACTION
------------------------------------------------------------------------

||| Produces the exact 3x3 scaled rational rotation matrix:
||| R_scaled = (x^2 - Q(v)) I + 2 v v^T + 2 x [v]_x
public export
rotationMatrixScaled3 : ProjectiveProportion -> Vect 3 (Vect 3 BoxInt)
rotationMatrixScaled3 (MkProjectiveProportion x t r s) =
  let x2 = x * x
      t2 = t * t
      r2 = r * r
      s2 = s * s
      two = intToBoxInt 2
      row1 = [ x2 + t2 - r2 - s2
             , (two * (t * r)) - (two * (x * s))
             , (two * (t * s)) + (two * (x * r))
             ]
      row2 = [ (two * (t * r)) + (two * (x * s))
             , x2 - t2 + r2 - s2
             , (two * (r * s)) - (two * (x * t))
             ]
      row3 = [ (two * (t * s)) - (two * (x * r))
             , (two * (r * s)) + (two * (x * t))
             , x2 - t2 - r2 + s2
             ]
  in [row1, row2, row3]

||| Rotates a 3D vector by a projective proportion.
public export
rotateVectorScaled : ProjectiveProportion -> Vect 3 BoxInt -> Vect 3 BoxInt
rotateVectorScaled p [v1, v2, v3] =
  let [r1, r2, r3] = rotationMatrixScaled3 p
  in [ dotProduct3 r1 [v1, v2, v3]
     , dotProduct3 r2 [v1, v2, v3]
     , dotProduct3 r3 [v1, v2, v3]
     ]

------------------------------------------------------------------------
-- 3. GROVER REFLECTION & EQUILATERAL SPREAD
------------------------------------------------------------------------

||| The Grover G_3 Householder reflection matrix (scaled by 3):
||| G_3_scaled = 2 J_3 - 3 I_3 = [[-1, 2, 2], [2, -1, 2], [2, 2, -1]]
public export
groverReflectionScaled3 : Vect 3 (Vect 3 BoxInt)
groverReflectionScaled3 =
  let m1 = intToBoxInt (-1)
      p2 = intToBoxInt 2
  in [ [m1, p2, p2]
     , [p2, m1, p2]
     , [p2, p2, m1]
     ]

||| Applies the scaled Grover reflection to a 3-element state.
public export
applyGroverScaled3 : Vect 3 BoxInt -> Vect 3 BoxInt
applyGroverScaled3 [v1, v2, v3] =
  let [r1, r2, r3] = groverReflectionScaled3
  in [ dotProduct3 r1 [v1, v2, v3]
     , dotProduct3 r2 [v1, v2, v3]
     , dotProduct3 r3 [v1, v2, v3]
     ]

||| Equilateral triangle rational spread s = 3/4 (numerator = 3, denominator = 4).
public export
equilateralSpreadNum : Integer
equilateralSpreadNum = 3

public export
equilateralSpreadDen : Integer
equilateralSpreadDen = 4

||| Compile-time QTT 0 verification of Wildberger's Triple Spread Formula for (3/4, 3/4, 3/4):
||| (s1 + s2 + s3)^2 = 2(s1^2 + s2^2 + s3^2) + 4 s1 s2 s3
||| Over common denominator 64:
||| LHS: (9/4)^2 = 81/16 = 324/64
||| RHS: 2 * 3 * (9/16) + 4 * (27/64) = 54/16 + 108/64 = 216/64 + 108/64 = 324/64!
public export
0 prfTripleSpreadEquilateral :
  (let sNum = 3
       sDen = 4
       lhs = (3 * sNum) * (3 * sNum) * (sDen * sDen)  -- (9)^2 * 16 = 81 * 16 = 1296
       rhs1 = 2 * (3 * (sNum * sNum)) * (sDen * sDen) -- 2 * 27 * 16 = 864
       rhs2 = 4 * (sNum * sNum * sNum) * sDen         -- 4 * 27 * 4  = 432
   in lhs == rhs1 + rhs2) = True
prfTripleSpreadEquilateral = Refl

------------------------------------------------------------------------
-- 4. PUSHFORWARD ROTATION OVER 3D MULTISETS
------------------------------------------------------------------------

public export
{n : Nat} -> Ord a => DiscreteCoord (Vect n a) where

||| Active physical pushforward of a 3D coordinate multiset along a projective rotation proportion.
||| Computes M' = R_*(M) = \sum c_i [R(v_i)]. Colliding points sum their multiplicities.
public export
pushforwardRotation3 : ProjectiveProportion -> MSetBox (Vect 3 BoxInt) -> MSetBox (Vect 3 BoxInt)
pushforwardRotation3 p = pushforwardMSet (rotateVectorScaled p)

------------------------------------------------------------------------
-- 5. PASSIVE ROTATED MULTISET OBSERVER VIEW
------------------------------------------------------------------------

||| Zero-allocation coordinate lookup through the rotated frame:
||| Queries the base multiset at the inverse rotated coordinate.
public export
lookupRotatedMSet : ProjectiveProportion -> Vect 3 BoxInt -> MSetBox (Vect 3 BoxInt) -> BoxInt
lookupRotatedMSet p v m =
  lookupBox (rotateVectorScaled (inverseProportion p) v) m

------------------------------------------------------------------------
-- 6. WILDBERGER PARAMETRIC PYTHAGOREAN ROTATION `(m^2 - 1, 2m, m^2 + 1)`
------------------------------------------------------------------------

public export
record PythPairResult where
  constructor MkPythPairResult
  valA : BoxInt
  valB : BoxInt
  valU : BoxInt

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

||| Generates the elementary Pythagorean triple `(m^2 - 1, 2m, m^2 + 1)` for `m >= 2`.
public export
pythGeneratorTriple : BoxInt -> (Integer, Integer, Integer)
pythGeneratorTriple (MkBoxInt mIn) =
  let mVal = if mIn < 2 then 2 else mIn
      m2   = mVal * mVal
  in (m2 - 1, 2 * mVal, m2 + 1)

||| Exact Gaussian composition `(a1 + i b1) * (a2 + i b2)` of two Pythagorean triples,
||| preserving `A^2 + B^2 = R^2` and multiplying rational spreads via spread polynomial composition.
public export
pythComposeTriple : (Integer, Integer, Integer) -> (Integer, Integer, Integer) -> (Integer, Integer, Integer)
pythComposeTriple (a1, b1, r1) (a2, b2, r2) =
  (a1 * a2 - b1 * b2, a1 * b2 + b1 * a2, r1 * r2)

||| Computes the `y`-th composite Pythagorean triple `(A_y, B_y, R_y) = (A_1 + i B_1)^y`
||| whose spread is the exact `y`-fold spread polynomial `S_y(s(m)) = Z_y(4 s(m)) / 4`.
public export
pythPowerTriple : (y : Nat) -> (m : BoxInt) -> (Integer, Integer, Integer)
pythPowerTriple Z           _ = (1, 0, 1)
pythPowerTriple (S Z)       m = pythGeneratorTriple m
pythPowerTriple (S (S rem)) m =
  let base = pythGeneratorTriple m
  in go rem base base
  where
    go : Nat -> (Integer, Integer, Integer) -> (Integer, Integer, Integer) -> (Integer, Integer, Integer)
    go Z     step acc = pythComposeTriple acc step
    go (S k) step acc = go k step (pythComposeTriple acc step)

||| Applies an exact integer Pythagorean rotation specified by `(aCoef, bCoef, rDen)` (`a^2 + b^2 = r^2`)
||| to `(pA, pB, u)`, preserving `pA + pB` identically and monotonically bounding `2*(pA^2 + pB^2) + u^2`.
public export
rotatePythTriple : (Integer, Integer, Integer) -> (pA, pB, u : BoxInt) -> PythPairResult
rotatePythTriple (aCoef, bCoef, rDen) pA pB u =
  let dDiff = subBox pB pA
  in if (boxIsZero dDiff && boxIsZero u) || bCoef == 0 || rDen <= 0
       then MkPythPairResult pA pB u
       else
         let sSum        = addBox pA pB
             MkBoxInt dV = dDiff
             MkBoxInt uV = u
             numD        = MkBoxInt (aCoef * dV + bCoef * uV)
             numU        = MkBoxInt (aCoef * uV - bCoef * dV)
             eOld        = dV * dV + uV * uV
             (dN, uN)    = pythChoosePair sSum dDiff numD numU rDen eOld
         in MkPythPairResult (tdiv2Box (subBox sSum dN)) (tdiv2Box (addBox sSum dN)) uN

||| Applies the `y`-fold composed Pythagorean rotation `(A_1 + i B_1)^y` for generator `m >= 2`.
public export
rotatePythPow : (y : Nat) -> (m, pA, pB, u : BoxInt) -> PythPairResult
rotatePythPow Z       _ pA pB u = MkPythPairResult pA pB u
rotatePythPow y@(S _) m pA pB u = rotatePythTriple (pythPowerTriple y m) pA pB u

||| Wildberger parametric Pythagorean `(m^2 - 1, 2m, m^2 + 1)` exact integer rotation
||| on `(pA, pB, u)` for any `m >= 2` (`y = 1` specialization of `rotatePythPow`).
public export
rotatePythParam : (m, pA, pB, u : BoxInt) -> PythPairResult
rotatePythParam = rotatePythPow 1

