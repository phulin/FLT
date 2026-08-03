/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Deformations.Representable
public import FLT.GaloisRepresentation.HardlyRamified.Defs

/-!
# The minimal hardly ramified deformation problem

This file replaces the formerly opaque minimal-lift existential by a named deformation
problem and its universal object.  A lift belongs to the problem precisely when it reduces
to the fixed residual representation and is hardly ramified.  Thus its determinant,
ramification away from `2p`, finite-flat condition at `p`, and tame quadratic quotient at `2`
are all part of the represented functor.

Representability is classical Schlessinger--Mazur deformation theory, together with the
pre-1990 representability of the finite-flat local condition.  The later assertion that this
particular universal ring is finite flat over its coefficient DVR is the genuinely modern
Taylor--Wiles/Khare--Wintenberger step and is deliberately not asserted here.
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- The subfunctor of framed representations of `G_ℚ` that are hardly ramified.  The
`ℤ_[p]`-algebra structure on an object is the composite through the coefficient ring `𝓞`.
-/
noncomputable def hardlyRamifiedFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞] :
    Subfunctor (repnFunctor (Fin 2) (Γ ℚ) 𝓞) where
  obj A := {τ | let _ : Algebra ℤ_[p] A :=
      Algebra.compHom A (algebraMap ℤ_[p] 𝓞)
    GaloisRepresentation.IsHardlyRamified hpodd (by simp) (toFramedGaloisRep τ)}
  map {A B} f τ hτ := by
    letI : Algebra ℤ_[p] A := Algebra.compHom A (algebraMap ℤ_[p] 𝓞)
    letI : Algebra ℤ_[p] B := Algebra.compHom B (algebraMap ℤ_[p] 𝓞)
    change GaloisRepresentation.IsHardlyRamified hpodd (by simp)
      (toFramedGaloisRep τ) at hτ
    change GaloisRepresentation.IsHardlyRamified hpodd (by simp)
      (toFramedGaloisRep ((repnFunctor (Fin 2) (Γ ℚ) 𝓞).map f τ))
    let htower : let _ : Algebra A B := f.hom.toRingHom.toAlgebra;
        IsScalarTower ℤ_[p] A B := by
      letI : Algebra A B := f.hom.toRingHom.toAlgebra
      exact IsScalarTower.of_algebraMap_eq fun x => by
        exact (f.hom.commutes (algebraMap ℤ_[p] 𝓞 x)).symm
    let hres : let _ : Algebra A B := f.hom.toRingHom.toAlgebra;
        IsResidueAlgebra A B := by
      letI : Algebra A B := f.hom.toRingHom.toAlgebra
      letI : IsScalarTower 𝓞 A B := inferInstance
      exact IsResidueAlgebra.of_restrictScalars (𝓞 := 𝓞) (A := A) (B := B)
    rw [toFramedGaloisRep_map]
    exact GaloisRepresentation.IsHardlyRamified.framedBaseChange hpodd
      f.hom.toRingHom f.hom.cont htower hres (toFramedGaloisRep τ) hτ

/-- The minimal hardly ramified lift functor: a representation must both reduce to `ρ` and
satisfy all four hardly ramified local/global conditions. -/
noncomputable def hardlyRamifiedLiftFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
    (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField) :
    Subfunctor (repnFunctor (Fin 2) (Γ ℚ) 𝓞) :=
  liftFunctor (Fin 2) (Γ ℚ) 𝓞 ρ ⊓ hardlyRamifiedFunctor 𝓞 p hpodd

/-- The residual point belongs to the minimal lift functor whenever it is hardly ramified.
The lift condition at the terminal residue-field object is the identity condition. -/
theorem residual_mem_hardlyRamifiedLiftFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
    (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField)
    (hρ : ρ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj .residueField) :
    ρ ∈ (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).obj .residueField := by
  refine ⟨?_, hρ⟩
  change (repnFunctor (Fin 2) (Γ ℚ) 𝓞).map
      (ProartinianCat.isTerminalResidueField.from .residueField) ρ = ρ
  rw [Subsingleton.elim (ProartinianCat.isTerminalResidueField.from .residueField)
    (𝟙 (.residueField : ProartinianCat 𝓞))]
  rfl

/-- Transporting a hardly ramified residual representation along the chosen identification
`ResidueField R ≃ k` gives the residual point of the hardly ramified deformation functor.
-/
theorem residualRepresentation_mem_hardlyRamifiedFunctor
    {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k]
    (R : Type u) [CommRing R] [IsLocalRing R]
    [Algebra ℤ_[p] R] [Algebra R k]
    [IsScalarTower ℤ_[p] R k]
    (e : ResidueField R ≃+* k)
    (he : ∀ r, e (residue R r) = algebraMap R k r)
    (ρ : FramedGaloisRep ℚ k (Fin 2))
    (hρ : GaloisRepresentation.IsHardlyRamified hpodd (by simp) ρ) :
    residualRepresentation R e ρ ∈
      (hardlyRamifiedFunctor R p hpodd).obj .residueField := by
  let κR : ProartinianCat R := .residueField
  let f : k →+* κR :=
    (ProartinianCat.residueFieldRingEquiv R e).symm.toRingHom
  letI : IsLocalHom f := IsLocalHom.of_surjective f
    (ProartinianCat.residueFieldRingEquiv R e).symm.surjective
  letI : Algebra ℤ_[p] κR := Algebra.compHom _ (algebraMap ℤ_[p] R)
  let htower : (let _ : Algebra k κR := f.toAlgebra;
      IsScalarTower ℤ_[p] k κR) := by
    letI : Algebra k κR := f.toAlgebra
    exact IsScalarTower.of_algebraMap_eq fun z => by
      apply (ProartinianCat.residueFieldRingEquiv R e).injective
      change e (residue R (algebraMap ℤ_[p] R z)) = e (f (algebraMap ℤ_[p] k z))
      rw [show f (algebraMap ℤ_[p] k z) = e.symm (algebraMap ℤ_[p] k z) by rfl,
        e.apply_symm_apply, he]
      exact (IsScalarTower.algebraMap_apply ℤ_[p] R k z).symm
  let hres : (let _ : Algebra k κR := f.toAlgebra;
      IsResidueAlgebra k κR) := by
    letI : Algebra k κR := f.toAlgebra
    exact ⟨IsLocalRing.residue_surjective.comp
      (ProartinianCat.residueFieldRingEquiv R e).symm.surjective⟩
  change GaloisRepresentation.IsHardlyRamified hpodd (by simp)
    (toFramedGaloisRep (residualRepresentation R e ρ))
  simpa only [residualRepresentation, toFramedGaloisRep,
    FramedGaloisRep.GL.symm_apply_apply] using
    GaloisRepresentation.IsHardlyRamified.framedBaseChange hpodd
      f continuous_of_discreteTopology htower hres ρ hρ

/-- Schlessinger--Mazur corepresentability of the minimal hardly ramified deformation
problem.  This is a pre-1990 input: Mazur's deformation theory and the classical
finite-flat local deformation condition. -/
lemma isCorepresentable_hardlyRamifiedLiftFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
    [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
    (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField)
    [(toRepresentation ρ).IsAbsolutelyIrreducible]
    (_hρ : ρ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj .residueField) :
    (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).toFunctor.IsCorepresentable := by
  -- Schlessinger's criterion plus Mazur's 1989 profinite deformation framework; the
  -- finite-flat local condition is represented by the pre-1990 Fontaine--Laffaille theory.
  knownin1980s

noncomputable section Universal

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]
variable (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
variable (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField)
variable [(toRepresentation ρ).IsAbsolutelyIrreducible]
variable (hρ : ρ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj .residueField)

/-- The universal minimal hardly ramified deformation ring. -/
def hardlyRamifiedUniversalRing : ProartinianCat 𝓞 :=
  (isCorepresentable_hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ hρ).has_corepresentation.choose

/-- The corepresentation of the minimal hardly ramified lift functor. -/
def hardlyRamifiedUniversalRingCorepresentableBy :
    (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).toFunctor.CorepresentableBy
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  (isCorepresentable_hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ hρ).has_corepresentation.choose_spec.some

/-- The universal element of the minimal hardly ramified lift functor. -/
def hardlyRamifiedUniversalElement :
    (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).toFunctor.obj
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  (hardlyRamifiedUniversalRingCorepresentableBy 𝓞 p hpodd ρ hρ).homEquiv
    (𝟙 (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ))

/-- The matrix-valued universal minimal representation. -/
def hardlyRamifiedUniversalRepresentation :
    (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ).1

/-- The universal minimal representation as a framed Galois representation. -/
noncomputable def hardlyRamifiedUniversalGaloisRep :
    FramedGaloisRep ℚ (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) (Fin 2) :=
  toFramedGaloisRep (hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ)

theorem hardlyRamifiedUniversalRepresentation_mem :
    hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ ∈
      (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).obj
        (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ).2

/-- The universal element both reduces to `ρ` and is hardly ramified. -/
theorem hardlyRamifiedUniversalRepresentation_conditions :
    let τ := hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ
    let D := hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ
    τ ∈ (liftFunctor (Fin 2) (Γ ℚ) 𝓞 ρ).obj D ∧
      τ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj D := by
  simpa only [hardlyRamifiedLiftFunctor, CategoryTheory.Subfunctor.min_obj,
    Set.mem_inter_iff] using
      hardlyRamifiedUniversalRepresentation_mem 𝓞 p hpodd ρ hρ

/-- Reduction of the universal representation along its canonical residue map is exactly
the fixed residual representation. -/
theorem hardlyRamifiedUniversalRepresentation_reduces :
    (repnFunctor (Fin 2) (Γ ℚ) 𝓞).map
      (ProartinianCat.toResidueField
        (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ))
      (hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ) = ρ := by
  exact (hardlyRamifiedUniversalRepresentation_conditions 𝓞 p hpodd ρ hρ).1

end Universal

end Deformation
