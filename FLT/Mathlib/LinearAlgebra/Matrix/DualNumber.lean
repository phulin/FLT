/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Matrix.DualNumber

/-!
# Universe-polymorphic matrices over dual numbers

Mathlib's `Matrix.dualNumberEquiv` currently places both the coefficient ring and index type in
`Type 0`.  Deformation rings in this project live in a shared arbitrary universe, so we provide
the identical equivalence universe-polymorphically.
-/

@[expose] public section

universe u v

variable {R : Type u} {n : Type v} [CommSemiring R] [Fintype n] [DecidableEq n]

open Matrix TrivSqZeroExt

set_option backward.isDefEq.respectTransparency.types false in
/-- Matrices over dual numbers and dual numbers over matrices, in an arbitrary universe. -/
@[simps]
def Matrix.dualNumberEquiv' : Matrix n n (DualNumber R) ≃ₐ[R] DualNumber (Matrix n n R) where
  toFun A := ⟨of fun i j ↦ (A i j).fst, of fun i j ↦ (A i j).snd⟩
  invFun d := of fun i j ↦ (d.fst i j, d.snd i j)
  map_mul' A B := by
    ext
    · dsimp [mul_apply]
      simp_rw [fst_sum]
      rfl
    · simp_rw [snd_mul, smul_eq_mul, op_smul_eq_mul]
      simp only [mul_apply, snd_sum, DualNumber.snd_mul, snd_mk, of_apply, fst_mk, add_apply]
      rw [← Finset.sum_add_distrib]
  map_add' _ _ := TrivSqZeroExt.ext rfl rfl
  commutes' r := by
    simp_rw [algebraMap_eq_inl', algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.algebraMap_self_apply, algebraMap_eq_inl, ← diagonal_map (inl_zero R), map_apply,
      fst_inl, snd_inl]
    rfl
