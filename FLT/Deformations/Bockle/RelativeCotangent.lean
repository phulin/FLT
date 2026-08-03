/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.DualNumber
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Relative cotangent functionals from dual-number points

An algebra map `D → k[ε]` has a residue component `D → k` and an infinitesimal
component.  The latter is an `R`-derivation, hence a linear functional on the relative
cotangent space `k ⊗[D] Ω[D/R]`.  This file packages that standard passage independently
of deformation theory.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Deformation

variable {R D k : Type u} [CommRing R] [CommRing D] [Field k]
  [Algebra R D] [Algebra R k]

/-- The residue component of an algebra map to the dual numbers. -/
noncomputable def dualNumberAugmentation (f : D →ₐ[R] DualNumber k) : D →ₐ[R] k :=
  (TrivSqZeroExt.fstHom R k k).comp f

@[simp]
lemma dualNumberAugmentation_apply (f : D →ₐ[R] DualNumber k) (x : D) :
    dualNumberAugmentation f x = (f x).fst :=
  rfl

/-- The infinitesimal component of a map to the dual numbers, regarded as a derivation
relative to the coefficient ring. -/
noncomputable def dualNumberDerivation (f : D →ₐ[R] DualNumber k) :
    letI : Algebra D k := (dualNumberAugmentation f).toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' (dualNumberAugmentation f).comp_algebraMap.symm
    Derivation R D k := by
  let aug := dualNumberAugmentation f
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  refine
    { toLinearMap :=
        (TrivSqZeroExt.sndHom k k).restrictScalars R ∘ₗ f.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := ?_ }
  intro x y
  change (f (x * y)).snd = aug x * (f y).snd + aug y * (f x).snd
  rw [map_mul, TrivSqZeroExt.snd_mul]
  simp only [aug, dualNumberAugmentation_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  rw [smul_eq_mul]
  ac_rfl

@[simp]
lemma dualNumberDerivation_apply (f : D →ₐ[R] DualNumber k) (x : D) :
    letI : Algebra D k := (dualNumberAugmentation f).toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' (dualNumberAugmentation f).comp_algebraMap.symm
    dualNumberDerivation f x = (f x).snd :=
  by simp [dualNumberDerivation]

/-- The relative cotangent space at an augmentation `D → k`. -/
noncomputable abbrev RelativeCotangentSpace (aug : D →ₐ[R] k) : Type u :=
  letI : Algebra D k := aug.toAlgebra
  k ⊗[D] KaehlerDifferential R D

/-- The cotangent functional associated to a dual-number point. -/
noncomputable def dualNumberCotangentFunctional (f : D →ₐ[R] DualNumber k) :
    RelativeCotangentSpace (dualNumberAugmentation f) →ₗ[k] k := by
  let aug := dualNumberAugmentation f
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  exact (dualNumberDerivation f).liftKaehlerDifferential.liftBaseChange k

/-- Regard the cotangent functional as based at a propositionally equal chosen
augmentation.  This lets a family of dual-number points share one cotangent space. -/
noncomputable def dualNumberCotangentFunctionalAt
    (aug : D →ₐ[R] k) (f : D →ₐ[R] DualNumber k)
    (h : dualNumberAugmentation f = aug) :
    RelativeCotangentSpace aug →ₗ[k] k :=
  h ▸ dualNumberCotangentFunctional f

@[simp]
theorem dualNumberCotangentFunctional_tmul_D
    (f : D →ₐ[R] DualNumber k) (x : D) :
    let aug := dualNumberAugmentation f
    letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    dualNumberCotangentFunctional f
      (1 ⊗ₜ[D] KaehlerDifferential.D R D x) = (f x).snd :=
  let aug := dualNumberAugmentation f
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  by
    rw [dualNumberCotangentFunctional, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D, dualNumberDerivation_apply]

@[simp]
theorem dualNumberCotangentFunctionalAt_tmul_D
    (aug : D →ₐ[R] k) (f : D →ₐ[R] DualNumber k)
    (h : dualNumberAugmentation f = aug) (x : D) :
    letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    dualNumberCotangentFunctionalAt aug f h
      (1 ⊗ₜ[D] KaehlerDifferential.D R D x) = (f x).snd := by
  subst aug
  exact dualNumberCotangentFunctional_tmul_D f x

end Deformation
