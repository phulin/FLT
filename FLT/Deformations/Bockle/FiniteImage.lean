/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle
public import FLT.Deformations.FiniteImage

/-!
# Böckle presentations and finite-image arithmetic

This file joins the finite-image proof for a universal representation to Böckle's balanced
presentation.  It keeps the two final commutative-algebra implications explicit: lifting
finiteness modulo a uniformizer to module finiteness, and deriving regularity of the balanced
presentation from that finiteness.
-/

@[expose] public section

namespace Deformation

universe uK u un

variable {K : Type uK} [Field K]
variable {R D : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField R)]
  [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [Algebra R D]
  [IsLocalRing D] [IsLocalHom (algebraMap R D)]
variable {n : Type un} [Fintype n] [DecidableEq n]

/-- The decomposed arithmetic and commutative-algebra data needed in Böckle's argument.
Unlike `BockleFinitenessData`, this structure does not assume module finiteness or regularity:
both are required only as consequences of the already-derived finiteness modulo a uniformizer. -/
structure BockleArithmeticData (rho : FramedGaloisRep K D n) where
  /-- Böckle's balanced power-series presentation. -/
  presentation : BocklePresentation R D
  /-- The finite-variable presentation makes the deformation ring Noetherian. -/
  noetherian : IsNoetherianRing D
  /-- The universal deformation ring has the same finite residue field as its coefficient ring. -/
  finiteResidueField : Finite (IsLocalRing.ResidueField D)
  /-- The coefficient-ring uniformizer. -/
  uniformizer : R
  /-- Potential modularity, Carayol trace generation, and trace integrality data. -/
  finiteImage : ModScalarFiniteImageData rho uniformizer
  /-- The topological Nakayama step from `D / pi D` to module finiteness over `R`. -/
  moduleFinite_of_modScalarFinite :
    Finite (ModScalarRing (D := D) uniformizer) → Module.Finite R D
  /-- The Cohen--Macaulay/system-of-parameters step in the balanced presentation. -/
  regularAt_of_modScalarFinite :
    Finite (ModScalarRing (D := D) uniformizer) →
      presentation.IsRegularAt uniformizer

/-- Assemble the usual Böckle finiteness data after deriving finiteness modulo the uniformizer
from the finite-image criterion. -/
noncomputable def BockleArithmeticData.toBockleFinitenessData
    {rho : FramedGaloisRep K D n} (h : BockleArithmeticData (R := R) rho) :
    BockleFinitenessData R D := by
  letI : IsNoetherianRing D := h.noetherian
  letI : Finite (IsLocalRing.ResidueField D) := h.finiteResidueField
  have hmod : Finite (ModScalarRing (D := D) h.uniformizer) := h.finiteImage.finite
  exact
    { presentation := h.presentation
      uniformizer := h.uniformizer
      uniformizer_irreducible := h.finiteImage.uniformizer_irreducible
      finite := h.moduleFinite_of_modScalarFinite hmod
      regularAt := h.regularAt_of_modScalarFinite hmod }

end Deformation
