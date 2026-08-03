/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle.Cohomology
public import FLT.Mathlib.LinearAlgebra.Matrix.DualNumber

/-!
# First-order deformations and adjoint cocycles

For an adjoint cocycle `c`, the familiar formula

`rhoₑ(g) = (1 + ε c(g)) rho(g)`

defines a representation over the dual numbers.  This file separates the calculation into an
endomorphism-valued square-zero extension and its matrix realization.  Trace zero, and hence the
fixed-determinant calculation, is handled separately below.
-/

@[expose] public section

universe u

open scoped DualNumber

namespace Deformation

section General

variable {k G V : Type u} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The value `(rho(g), c(g) * rho(g))` in the square-zero extension of the endomorphism ring.
It represents `(1 + ε c(g)) rho(g)`. -/
def firstOrderEndValue (rho : Representation k G V)
    (c : G → Module.End k V) (g : G) : DualNumber (Module.End k V) :=
  (rho g, c g * rho g)

@[simp]
lemma firstOrderEndValue_fst (rho : Representation k G V)
    (c : G → Module.End k V) (g : G) :
    (firstOrderEndValue rho c g).fst = rho g := rfl

@[simp]
lemma firstOrderEndValue_snd (rho : Representation k G V)
    (c : G → Module.End k V) (g : G) :
    (firstOrderEndValue rho c g).snd = c g * rho g := rfl

/-- The crossed-homomorphism identity is exactly the multiplicativity calculation for a
first-order lift. -/
lemma firstOrderEndValue_map_mul (rho : Representation k G V)
    (c : G → Module.End k V)
    (hc : ∀ g h, c (g * h) = rho g * c h * rho g⁻¹ + c g)
    (g h : G) :
    firstOrderEndValue rho c (g * h) =
      firstOrderEndValue rho c g * firstOrderEndValue rho c h := by
  apply TrivSqZeroExt.ext
  · change rho (g * h) = rho g * rho h
    rw [map_mul]
  · change c (g * h) * rho (g * h) =
      rho g * (c h * rho h) + (c g * rho g) * rho h
    rw [hc, map_mul]
    simp only [add_mul, mul_assoc]
    rw [← mul_assoc (rho g⁻¹) (rho g) (rho h), ← map_mul]
    simp

/-- An adjoint cocycle produces a monoid homomorphism into the square-zero extension of the
endomorphism ring. -/
def firstOrderEndMonoidHom (rho : Representation k G V)
    (c : G → Module.End k V) (hc_one : c 1 = 0)
    (hc_mul : ∀ g h, c (g * h) = rho g * c h * rho g⁻¹ + c g) :
    G →* DualNumber (Module.End k V) where
  toFun := firstOrderEndValue rho c
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp [firstOrderEndValue, hc_one]
  map_mul' := firstOrderEndValue_map_mul rho c hc_mul

@[simp]
lemma firstOrderEndMonoidHom_apply (rho : Representation k G V)
    (c : G → Module.End k V) (hc_one : c 1 = 0)
    (hc_mul : ∀ g h, c (g * h) = rho g * c h * rho g⁻¹ + c g) (g : G) :
    firstOrderEndMonoidHom rho c hc_one hc_mul g = firstOrderEndValue rho c g := rfl

end General

section RankTwo

variable {k G : Type u} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The endomorphism-valued first-order representation attached to a trace-zero adjoint
cocycle. -/
noncomputable def bockleFirstOrderEndMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) :
    G →* DualNumber (Module.End k (Fin 2 → k)) := by
  let c : G → Module.End k (Fin 2 → k) := fun g ↦
    Representation.traceZeroAdjointTopRepToEnd rho (σ g)
  refine firstOrderEndMonoidHom rho c ?_ ?_
  · change Representation.traceZeroAdjointTopRepToEnd rho (σ 1) = 0
    rw [ContinuousCohomology.Cocycles₁.map_one
      (Representation.traceZeroAdjointTopRep rho) σ, map_zero]
  · intro g h
    have hσ := congrArg (Representation.traceZeroAdjointTopRepToEnd rho)
      (BockleAdjointCocycles₁.map_mul rho σ g h)
    rw [map_add, Representation.traceZeroAdjointTopRepToEnd_action] at hσ
    exact hσ

@[simp]
lemma bockleFirstOrderEndMonoidHom_fst
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderEndMonoidHom rho σ g).fst = rho g := rfl

@[simp]
lemma bockleFirstOrderEndMonoidHom_snd
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderEndMonoidHom rho σ g).snd =
      Representation.traceZeroAdjointTopRepToEnd rho (σ g) * rho g := rfl

/-- The trace-zero adjoint cocycle written in the standard rank-two basis. -/
noncomputable def bockleAdjointMatrix
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    Matrix (Fin 2) (Fin 2) k :=
  LinearMap.toMatrixAlgEquiv'
    (Representation.traceZeroAdjointTopRepToEnd rho (σ g))

lemma bockleAdjointMatrix_trace
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleAdjointMatrix rho σ g).trace = 0 := by
  have htrace := Representation.trace_traceZeroAdjointTopRepToEnd rho (σ g)
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2))] at htrace
  exact htrace

/-- Apply the standard endomorphism-to-matrix equivalence coefficientwise to a dual number. -/
noncomputable def endDualNumberToMatrixMonoidHom :
    DualNumber (Module.End k (Fin 2 → k)) →*
      Matrix (Fin 2) (Fin 2) (DualNumber k) where
  toFun z := fun i j ↦
    (LinearMap.toMatrixAlgEquiv' z.fst i j, LinearMap.toMatrixAlgEquiv' z.snd i j)
  map_one' := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.fst_one, map_one]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_one, map_zero]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  map_mul' x y := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · change LinearMap.toMatrixAlgEquiv' ((x * y).fst) i j =
        ∑ l, LinearMap.toMatrixAlgEquiv' x.fst i l *
          LinearMap.toMatrixAlgEquiv' y.fst l j
      rw [TrivSqZeroExt.fst_mul, map_mul]
      rfl
    · change LinearMap.toMatrixAlgEquiv' ((x * y).snd) i j =
        ∑ l, (LinearMap.toMatrixAlgEquiv' x.fst i l *
          LinearMap.toMatrixAlgEquiv' y.snd l j +
          LinearMap.toMatrixAlgEquiv' x.snd i l *
            LinearMap.toMatrixAlgEquiv' y.fst l j)
      rw [DualNumber.snd_mul, map_add, map_mul, map_mul]
      simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

/-- Matrix realization of the first-order representation over `k[ε]`. -/
noncomputable def bockleFirstOrderMatrixMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) :
    G →* Matrix (Fin 2) (Fin 2) (DualNumber k) :=
  endDualNumberToMatrixMonoidHom.comp (bockleFirstOrderEndMonoidHom rho σ)

@[simp]
lemma bockleFirstOrderMatrixMonoidHom_dualNumberEquiv
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    Matrix.dualNumberEquiv' (R := k) (n := Fin 2)
        (bockleFirstOrderMatrixMonoidHom rho σ g) =
      ((LinearMap.toMatrixAlgEquiv' (rho g),
        LinearMap.toMatrixAlgEquiv'
          (Representation.traceZeroAdjointTopRepToEnd rho (σ g) * rho g)) :
        DualNumber (Matrix (Fin 2) (Fin 2) k)) := by
  apply TrivSqZeroExt.ext <;> rfl

/-- Constant and infinitesimal matrix coefficients of the first-order representation. -/
lemma bockleFirstOrderMatrixMonoidHom_eq_dualNumberOfParts
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    bockleFirstOrderMatrixMonoidHom rho σ g =
      Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' (rho g))
        (bockleAdjointMatrix rho σ g * LinearMap.toMatrixAlgEquiv' (rho g)) := by
  apply (Matrix.dualNumberEquiv' (R := k) (n := Fin 2)).injective
  rw [bockleFirstOrderMatrixMonoidHom_dualNumberEquiv,
    Matrix.dualNumberEquiv'_dualNumberOfParts]
  apply TrivSqZeroExt.ext
  · rfl
  · simp [bockleAdjointMatrix]

/-- The first-order representation factors as `(1 + ε c(g)) · rho(g)`. -/
lemma bockleFirstOrderMatrixMonoidHom_factor
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    bockleFirstOrderMatrixMonoidHom rho σ g =
      Matrix.dualNumberOfParts 1 (bockleAdjointMatrix rho σ g) *
        Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' (rho g)) 0 := by
  rw [bockleFirstOrderMatrixMonoidHom_eq_dualNumberOfParts,
    Matrix.dualNumberOfParts_mul]
  simp

/-- A trace-zero adjoint cocycle preserves the determinant to first order. -/
theorem bockleFirstOrderMatrixMonoidHom_det
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderMatrixMonoidHom rho σ g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)) := by
  rw [bockleFirstOrderMatrixMonoidHom_factor, Matrix.det_mul,
    Matrix.det_dualNumberOfParts_one _ (bockleAdjointMatrix_trace rho σ g),
    Matrix.det_dualNumberOfParts_zero, one_mul]
  congr 1
  simp [LinearMap.toMatrixAlgEquiv', LinearMap.det_toMatrix']

end RankTwo

end Deformation
