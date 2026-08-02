/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The component algebras of the finite-flat Tate--Kummer model

Suppose that a Tate parameter has been written as `q = a ^ N * u`, with `u` a unit.
The finite-flat model of the `N`-torsion is the disjoint union, indexed by
`i : Fin N`, of the Kummer covers

`X ^ N = u ^ i`.

This file constructs the coordinate algebra of each component and proves the elementary
finiteness and flatness properties. The Hopf structure, which encodes the carry in addition
of component indices, is built on top of these component algebras.
-/

@[expose] public section

open Polynomial
open scoped TensorProduct

universe u

namespace TateKummer

variable (R : Type u) [CommRing R]

/-- The equation cutting out component `i` of the Tate--Kummer model. -/
noncomputable def componentPolynomial (N i : ℕ) (u : Rˣ) : R[X] :=
  X ^ N - C ((u : R) ^ i)

/-- The coordinate algebra of component `i`: adjoining an `N`-th root of `u ^ i`. -/
abbrev Component (N i : ℕ) (u : Rˣ) :=
  AdjoinRoot (componentPolynomial R N i u)

variable {R}

lemma componentPolynomial_monic (N i : ℕ) [NeZero N] (u : Rˣ) :
    (componentPolynomial R N i u).Monic :=
  monic_X_pow_sub_C _ (NeZero.ne N)

/-- The distinguished coordinate on a Kummer component satisfies its defining equation. -/
lemma root_pow (N i : ℕ) (u : Rˣ) :
    (AdjoinRoot.root (componentPolynomial R N i u)) ^ N =
      algebraMap R (Component R N i u) ((u : R) ^ i) := by
  unfold componentPolynomial
  have h := AdjoinRoot.eval₂_root (X ^ N - C ((u : R) ^ i))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The distinguished coordinate is a unit: its `N`-th power is the image of a unit. -/
lemma isUnit_root (N i : ℕ) [NeZero N] (u : Rˣ) :
    IsUnit (AdjoinRoot.root (componentPolynomial R N i u)) := by
  rw [← isUnit_pow_iff (NeZero.ne N), root_pow]
  exact (u ^ i).isUnit.map (algebraMap R (Component R N i u))

noncomputable instance componentModuleFree (N i : ℕ) [NeZero N] (u : Rˣ) :
    Module.Free R (Component R N i u) :=
  (componentPolynomial_monic N i u).free_adjoinRoot

instance componentModuleFinite (N i : ℕ) [NeZero N] (u : Rˣ) :
    Module.Finite R (Component R N i u) :=
  (componentPolynomial_monic N i u).finite_adjoinRoot

instance componentModuleFlat (N i : ℕ) [NeZero N] (u : Rˣ) :
    Module.Flat R (Component R N i u) :=
  Module.Flat.of_free

/-- The coordinate ring underlying the Tate--Kummer model, before equipping it with its
Hopf structure. It is the finite product of its Kummer component algebras. -/
abbrev CoordinateAlgebra (N : ℕ) (u : Rˣ) :=
  ∀ i : Fin N, Component R N i.1 u

noncomputable instance algebraModuleFree (N : ℕ) [NeZero N] (u : Rˣ) :
    Module.Free R (CoordinateAlgebra (R := R) N u) :=
  Module.Free.pi R _

instance algebraModuleFinite (N : ℕ) [NeZero N] (u : Rˣ) :
    Module.Finite R (CoordinateAlgebra (R := R) N u) :=
  inferInstance

instance algebraModuleFlat (N : ℕ) [NeZero N] (u : Rˣ) :
    Module.Flat R (CoordinateAlgebra (R := R) N u) :=
  Module.Flat.of_free

/-! ## Component arithmetic -/

/-- Addition of component indices, represented in the standard range `0, ..., N - 1`. -/
def addIndex (N : ℕ) [NeZero N] (i j : Fin N) : Fin N :=
  ⟨(i.1 + j.1) % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩

/-- The number of copies of `N` carried when adding two standard component indices. -/
def addCarry (N : ℕ) (i j : Fin N) : ℕ :=
  (i.1 + j.1) / N

lemma addIndex_val_add_mul_addCarry (N : ℕ) [NeZero N] (i j : Fin N) :
    (addIndex N i j).1 + N * addCarry N i j = i.1 + j.1 :=
  Nat.mod_add_div _ _

/-- The unit identity behind multiplication in the Tate--Kummer model. The compensating
inverse power removes the carried copy of `N`. -/
lemma unit_mul_unit_mul_invCarry_pow (N : ℕ) [NeZero N] (u : Rˣ) (i j : Fin N) :
    u ^ i.1 * u ^ j.1 * ((u⁻¹) ^ addCarry N i j) ^ N =
      u ^ (addIndex N i j).1 := by
  rw [← pow_add]
  have hs := addIndex_val_add_mul_addCarry N i j
  calc
    u ^ (i.1 + j.1) * ((u⁻¹) ^ addCarry N i j) ^ N =
        u ^ ((addIndex N i j).1 + N * addCarry N i j) *
          (u⁻¹) ^ (addCarry N i j * N) := by
            rw [hs, pow_mul]
    _ = u ^ (addIndex N i j).1 *
          (u ^ (N * addCarry N i j) *
            (u⁻¹) ^ (N * addCarry N i j)) := by
          rw [pow_add, Nat.mul_comm (addCarry N i j) N, mul_assoc]
    _ = u ^ (addIndex N i j).1 := by
          rw [← mul_pow, mul_inv_cancel, one_pow, mul_one]

/-! ## Multiplication of component coordinates -/

/-- The image of the distinguished coordinate under multiplication of components `i`
and `j`. The final scalar is the inverse-unit correction for the carry. -/
noncomputable def componentMulRoot (N : ℕ) [NeZero N] (u : Rˣ) (i j : Fin N) :
    (Component R N i.1 u) ⊗[R] (Component R N j.1 u) :=
  Algebra.TensorProduct.includeLeft
      (R := R) (S := R)
      (B := Component R N j.1 u)
      (AdjoinRoot.root (componentPolynomial R N i.1 u)) *
    Algebra.TensorProduct.includeRight
      (R := R) (A := Component R N i.1 u)
      (AdjoinRoot.root (componentPolynomial R N j.1 u)) *
    algebraMap R _ ((((u⁻¹) ^ addCarry N i j : Rˣ) : R))

/-- The component multiplication coordinate satisfies the equation of the sum component. -/
lemma componentMulRoot_pow (N : ℕ) [NeZero N] (u : Rˣ) (i j : Fin N) :
    (componentMulRoot N u i j) ^ N =
      algebraMap R
        ((Component R N i.1 u) ⊗[R] (Component R N j.1 u))
        ((u : R) ^ (addIndex N i j).1) := by
  rw [componentMulRoot, mul_pow, mul_pow, ← map_pow, ← map_pow,
    root_pow, root_pow, ← map_pow]
  simp only [AlgHom.commutes]
  rw [← map_mul, ← map_mul]
  congr 1
  exact congrArg Units.val (unit_mul_unit_mul_invCarry_pow N u i j)

/-- The algebra map contravariantly encoding multiplication from components `i` and `j`
to their sum component. -/
noncomputable def componentMulAlgHom (N : ℕ) [NeZero N] (u : Rˣ) (i j : Fin N) :
    Component R N (addIndex N i j).1 u →ₐ[R]
      (Component R N i.1 u) ⊗[R] (Component R N j.1 u) :=
  AdjoinRoot.liftAlgHom
    (componentPolynomial R N (addIndex N i j).1 u)
    (Algebra.ofId R _)
    (componentMulRoot N u i j)
    (by
      rw [show componentPolynomial R N (addIndex N i j).1 u =
        X ^ N - C ((u : R) ^ (addIndex N i j).1) from rfl]
      simp [componentMulRoot_pow])

@[simp]
lemma componentMulAlgHom_root (N : ℕ) [NeZero N] (u : Rˣ) (i j : Fin N) :
    componentMulAlgHom N u i j
        (AdjoinRoot.root
          (componentPolynomial R N (addIndex N i j).1 u)) =
      componentMulRoot N u i j :=
  by
    unfold componentMulAlgHom
    apply AdjoinRoot.liftAlgHom_root

end TateKummer
