module Stage1.Lenses

import Data.Vect
import public Stage0.BoxInt
import public Stage0.Box
import public Stage0.HereditaryMSet
import public Stage1.Views

%default total

------------------------------------------------------------------------
-- 1. RELATIVISTIC MASS DEFECT UNDER DUAL-CHANNEL VIEWS
------------------------------------------------------------------------

||| Relativistic Mass Defect Decomposition:
||| Separates the positive kinetic/valence rest mass from motion
||| from the negative internal binding defect from dipole collisions.
public export
record MassDefectReport where
  constructor MkMassDefectReport
  valenceRestMass : BoxInt
  bindingDefect   : BoxInt
  effectiveMass   : BoxInt

||| Evaluates the exact mass defect of a dual-channel multiset:
||| decomposes state into (M_+, M_-), computes positive valence mass,
||| internal binding defect from M_-, and effective physical mass.
public export
massDefectOf : PureMultiset -> MassDefectReport
massDefectOf m =
  let ch  = splitChannels m
      vM  = sumHMSet ch.posChannel
      bM  = sumHMSet ch.negChannel
      eff = subBox vM bM
  in MkMassDefectReport vM bM eff
