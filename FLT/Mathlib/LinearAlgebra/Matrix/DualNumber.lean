/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Matrix.DualNumber
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

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

namespace Matrix

/-- Assemble a matrix over dual numbers from its constant and infinitesimal coefficient
matrices. -/
def dualNumberOfParts (A B : Matrix n n R) : Matrix n n (DualNumber R) :=
  fun i j ↦ (A i j, B i j)

omit [CommSemiring R] [Fintype n] [DecidableEq n] in
@[simp]
lemma dualNumberOfParts_apply (A B : Matrix n n R) (i j : n) :
    dualNumberOfParts A B i j = (A i j, B i j) :=
  rfl

@[simp]
lemma dualNumberEquiv'_dualNumberOfParts (A B : Matrix n n R) :
    dualNumberEquiv' (dualNumberOfParts A B) = (A, B) := by
  apply TrivSqZeroExt.ext <;> rfl

omit [DecidableEq n] in
lemma dualNumberOfParts_mul (A B C D : Matrix n n R) :
    dualNumberOfParts A B * dualNumberOfParts C D =
      dualNumberOfParts (A * C) (A * D + B * C) := by
  classical
  apply (dualNumberEquiv' (R := R) (n := n)).injective
  rw [map_mul, dualNumberEquiv'_dualNumberOfParts, dualNumberEquiv'_dualNumberOfParts,
    dualNumberEquiv'_dualNumberOfParts]
  rfl

omit [Fintype n] [DecidableEq n] in
lemma dualNumberOfParts_zero_eq_map (A : Matrix n n R) :
    dualNumberOfParts A 0 = A.map (algebraMap R (DualNumber R)) := by
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext <;> rfl

lemma det_dualNumberOfParts_zero {S : Type u} [CommRing S] (A : Matrix n n S) :
    (dualNumberOfParts A 0).det = algebraMap S (DualNumber S) A.det := by
  rw [dualNumberOfParts_zero_eq_map]
  exact ((algebraMap S (DualNumber S)).map_det A).symm

/-- Exact first-order determinant formula in rank two. -/
lemma det_dualNumberOfParts_one_eq {S : Type u} [CommRing S]
    (C : Matrix (Fin 2) (Fin 2) S) :
    (dualNumberOfParts 1 C).det = ((1, C.trace) : DualNumber S) := by
  rw [Matrix.det_fin_two]
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul]
    norm_num [dualNumberOfParts, Matrix.one_apply]
  · rw [TrivSqZeroExt.snd_sub, DualNumber.snd_mul, DualNumber.snd_mul]
    change (1 * C 1 1 + C 0 0 * 1) - (0 * C 1 0 + C 0 1 * 0) = C.trace
    simp [Matrix.trace_fin_two, add_comm]

/-- The first-order factor `1 + ε C` has determinant one exactly when `C` has trace
zero. -/
lemma det_dualNumberOfParts_one_eq_one_iff {S : Type u} [CommRing S]
    (C : Matrix (Fin 2) (Fin 2) S) :
    (dualNumberOfParts 1 C).det = 1 ↔ C.trace = 0 := by
  rw [det_dualNumberOfParts_one_eq]
  constructor
  · intro h
    exact congrArg TrivSqZeroExt.snd h
  · intro h
    apply TrivSqZeroExt.ext <;> simp [h]

/-- The first-order factor `1 + ε C` has determinant one when `C` has trace zero. -/
lemma det_dualNumberOfParts_one {S : Type u} [CommRing S]
    (C : Matrix (Fin 2) (Fin 2) S) (hC : C.trace = 0) :
    (dualNumberOfParts 1 C).det = 1 :=
  (det_dualNumberOfParts_one_eq_one_iff C).2 hC

end Matrix
