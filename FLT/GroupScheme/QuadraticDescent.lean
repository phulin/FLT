/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# Quadratic descent algebras

This file packages the quadratic algebra `R[X]/(X² - tX + n)` together with its
canonical conjugation.  It is the coefficient algebra used to descend a finite-flat
group scheme along an unramified quadratic twist.
-/

@[expose] public section

open Polynomial

universe u

namespace QuadraticDescent

variable (R : Type u) [CommRing R]

/-- The monic quadratic polynomial with trace `t` and norm `n`. -/
noncomputable def polynomial (t n : R) : R[X] :=
  X ^ 2 + (-C t * X + C n)

/-- The quadratic `R`-algebra with trace parameter `t` and norm parameter `n`. -/
abbrev Algebra (t n : R) :=
  AdjoinRoot (polynomial R t n)

lemma polynomial_monic (t n : R) : (polynomial R t n).Monic := by
  rw [show polynomial R t n = X ^ 2 + (-C t * X + C n) from rfl]
  exact monic_X_pow_add (by compute_degree!)

/-- Evaluation of the quadratic polynomial, stated independently of its quotient algebra. -/
lemma eval₂_polynomial {S : Type*} [CommRing S] (f : R →+* S) (x : S) (t n : R) :
    (polynomial R t n).eval₂ f x = x ^ 2 + (-f t * x + f n) := by
  unfold polynomial
  rw [eval₂_add, eval₂_X_pow, eval₂_add, eval₂_mul, eval₂_neg,
    eval₂_C, eval₂_X, eval₂_C]

/-- The distinguished generator satisfies its quadratic equation. -/
lemma root_sq_sub_trace_mul_add_norm (t n : R) :
    (AdjoinRoot.root (polynomial R t n)) ^ 2 +
        (-AdjoinRoot.of (polynomial R t n) t * AdjoinRoot.root (polynomial R t n) +
          AdjoinRoot.of (polynomial R t n) n) = 0 := by
  have h := AdjoinRoot.eval₂_root (polynomial R t n)
  rw [eval₂_polynomial] at h
  exact h

/-- The conjugate of the distinguished quadratic generator. -/
noncomputable def conjugateRoot (t n : R) : Algebra R t n :=
  AdjoinRoot.of (polynomial R t n) t - AdjoinRoot.root (polynomial R t n)

/-- The conjugate generator satisfies the same quadratic equation. -/
lemma conjugateRoot_isRoot (t n : R) :
    (polynomial R t n).eval₂ (AdjoinRoot.of (polynomial R t n))
      (conjugateRoot R t n) = 0 := by
  have hr := root_sq_sub_trace_mul_add_norm R t n
  rw [eval₂_polynomial]
  unfold conjugateRoot
  linear_combination hr

/-- Quadratic conjugation as an algebra endomorphism. -/
noncomputable def conjugationAlgHom (t n : R) :
    Algebra R t n →ₐ[R] Algebra R t n :=
  AdjoinRoot.liftAlgHom (polynomial R t n)
    (AdjoinRoot.ofAlgHom R (polynomial R t n))
    (conjugateRoot R t n) (conjugateRoot_isRoot R t n)

@[simp]
lemma conjugationAlgHom_root (t n : R) :
    conjugationAlgHom R t n (AdjoinRoot.root (polynomial R t n)) =
      conjugateRoot R t n := by
  unfold conjugationAlgHom
  apply AdjoinRoot.liftAlgHom_root

/-- Applying quadratic conjugation twice is the identity. -/
lemma conjugationAlgHom_involutive (t n : R) :
    Function.Involutive (conjugationAlgHom R t n) := by
  have hcomp : (conjugationAlgHom R t n).comp (conjugationAlgHom R t n) =
      AlgHom.id R (Algebra R t n) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, conjugationAlgHom_root, conjugateRoot,
      map_sub]
    rw [← AdjoinRoot.algebraMap_eq,
      (conjugationAlgHom R t n).commutes,
      conjugationAlgHom_root]
    rw [conjugateRoot]
    simp only [AdjoinRoot.algebraMap_eq, AlgHom.id_apply]
    abel
  intro x
  exact DFunLike.congr_fun hcomp x

/-- Quadratic conjugation as an involutive algebra automorphism. -/
noncomputable def conjugationAlgEquiv (t n : R) :
    Algebra R t n ≃ₐ[R] Algebra R t n :=
  AlgEquiv.ofAlgHom (conjugationAlgHom R t n) (conjugationAlgHom R t n)
    (by
      apply DFunLike.ext
      exact conjugationAlgHom_involutive R t n)
    (by
      apply DFunLike.ext
      exact conjugationAlgHom_involutive R t n)

@[simp]
lemma conjugationAlgEquiv_apply (t n : R) (x : Algebra R t n) :
    conjugationAlgEquiv R t n x = conjugationAlgHom R t n x :=
  rfl

@[simp]
lemma conjugationAlgEquiv_symm (t n : R) :
    (conjugationAlgEquiv R t n).symm = conjugationAlgEquiv R t n := by
  rfl

end QuadraticDescent
