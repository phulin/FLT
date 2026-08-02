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
public import Mathlib.RingTheory.TensorProduct.Pi

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

/-- Addition of component indices is associative. -/
lemma addIndex_assoc (N : ℕ) [NeZero N] (i j k : Fin N) :
    addIndex N (addIndex N i j) k = addIndex N i (addIndex N j k) := by
  apply Fin.ext
  change (((i.1 + j.1) % N + k.1) % N) =
    ((i.1 + (j.1 + k.1) % N) % N)
  calc
    ((i.1 + j.1) % N + k.1) % N =
        (i.1 + j.1 + k.1) % N := by
      simpa [Nat.mod_eq_of_lt k.isLt] using
        (Nat.add_mod (i.1 + j.1) k.1 N).symm
    _ = (i.1 + (j.1 + k.1)) % N := by rw [add_assoc]
    _ = (i.1 + (j.1 + k.1) % N) % N := by
      simpa [Nat.mod_eq_of_lt i.isLt] using Nat.add_mod i.1 (j.1 + k.1) N

@[simp]
lemma addIndex_zero_left (N : ℕ) [NeZero N] (i : Fin N) :
    addIndex N 0 i = i := by
  apply Fin.ext
  simp [addIndex, Nat.mod_eq_of_lt i.isLt]

@[simp]
lemma addIndex_zero_right (N : ℕ) [NeZero N] (i : Fin N) :
    addIndex N i 0 = i := by
  apply Fin.ext
  simp [addIndex, Nat.mod_eq_of_lt i.isLt]

@[simp]
lemma addCarry_zero_left (N : ℕ) [NeZero N] (i : Fin N) :
    addCarry N 0 i = 0 := by
  simp [addCarry, Nat.div_eq_of_lt i.isLt]

@[simp]
lemma addCarry_zero_right (N : ℕ) [NeZero N] (i : Fin N) :
    addCarry N i 0 = 0 := by
  simp [addCarry, Nat.div_eq_of_lt i.isLt]

/-- The carry is a normalized additive two-cocycle. -/
lemma addCarry_cocycle (N : ℕ) [NeZero N] (i j k : Fin N) :
    addCarry N i j + addCarry N (addIndex N i j) k =
      addCarry N j k + addCarry N i (addIndex N j k) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hij := addIndex_val_add_mul_addCarry N i j
  have hijk := addIndex_val_add_mul_addCarry N (addIndex N i j) k
  have hjk := addIndex_val_add_mul_addCarry N j k
  have hijk' := addIndex_val_add_mul_addCarry N i (addIndex N j k)
  have hassoc := congrArg Fin.val (addIndex_assoc N i j k)
  have hleft :
      (addIndex N (addIndex N i j) k).1 +
          N * addCarry N (addIndex N i j) k +
          N * addCarry N i j = i.1 + j.1 + k.1 := by
    omega
  have hright :
      (addIndex N i (addIndex N j k)).1 +
          N * addCarry N i (addIndex N j k) +
          N * addCarry N j k = i.1 + j.1 + k.1 := by
    omega
  have hterms :
      N * addCarry N i j + N * addCarry N (addIndex N i j) k =
        N * addCarry N j k + N * addCarry N i (addIndex N j k) := by
    omega
  have hmul :
      N * (addCarry N i j + addCarry N (addIndex N i j) k) =
        N * (addCarry N j k + addCarry N i (addIndex N j k)) := by
    simpa only [Nat.mul_add] using hterms
  exact (mul_left_cancel_iff_of_pos hN).mp hmul

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

/-! ## The global comultiplication and counit maps -/

abbrev Components (N : ℕ) (u : Rˣ) (i : Fin N) :=
  Component R N i.1 u

/-- Reindex component algebras along an equality of component indices. -/
noncomputable def componentEquivOfEq
    (N : ℕ) (u : Rˣ) {i j : Fin N} (h : i = j) :
    Component R N i.1 u ≃ₐ[R] Component R N j.1 u := by
  subst j
  exact AlgEquiv.refl

@[simp]
lemma componentEquivOfEq_root
    (N : ℕ) (u : Rˣ) {i j : Fin N} (h : i = j) :
    componentEquivOfEq N u h
        (AdjoinRoot.root (componentPolynomial R N i.1 u)) =
      AdjoinRoot.root (componentPolynomial R N j.1 u) := by
  subst j
  rfl

lemma componentEquivOfEq_coordinate
    (N : ℕ) (u : Rˣ) (f : CoordinateAlgebra (R := R) N u)
    {i j : Fin N} (h : i = j) :
    componentEquivOfEq N u h (f i) = f j := by
  subst j
  rfl

/-- Decompose the tensor product of the two finite products into the product of all
componentwise tensor products. The outer index is the right component. -/
noncomputable def tensorCoordinateEquiv (N : ℕ) [NeZero N] (u : Rˣ) :
    CoordinateAlgebra (R := R) N u ⊗[R] CoordinateAlgebra (R := R) N u ≃ₐ[R]
      ∀ j : Fin N, ∀ i : Fin N,
        (Component R N i.1 u) ⊗[R] (Component R N j.1 u) :=
  (Algebra.TensorProduct.piRight R R
      (CoordinateAlgebra (R := R) N u) (Components (R := R) N u)).trans
    (AlgEquiv.piCongrRight fun j =>
      (Algebra.TensorProduct.comm R
        (CoordinateAlgebra (R := R) N u) (Component R N j.1 u)).trans
        ((Algebra.TensorProduct.piRight R R
          (Component R N j.1 u) (Components (R := R) N u)).trans
            (AlgEquiv.piCongrRight fun i =>
              Algebra.TensorProduct.comm R
                (Component R N j.1 u) (Component R N i.1 u))))

@[simp]
lemma tensorCoordinateEquiv_tmul (N : ℕ) [NeZero N] (u : Rˣ)
    (x y : CoordinateAlgebra (R := R) N u) (j i : Fin N) :
    tensorCoordinateEquiv N u (x ⊗ₜ[R] y) j i = x i ⊗ₜ[R] y j := by
  rfl

/-- The coordinate map for multiplication, after decomposing the target into pairs of
components. -/
noncomputable def comulCoordinates (N : ℕ) [NeZero N] (u : Rˣ) :
    CoordinateAlgebra (R := R) N u →ₐ[R]
      ∀ j : Fin N, ∀ i : Fin N,
        (Component R N i.1 u) ⊗[R] (Component R N j.1 u) :=
  AlgHom.pi fun j =>
    AlgHom.pi fun i =>
      (componentMulAlgHom N u i j).comp
        (Pi.evalAlgHom R (Components (R := R) N u) (addIndex N i j))

/-- Comultiplication on the coordinate algebra of the Tate--Kummer model. -/
noncomputable def comulAlgHom (N : ℕ) [NeZero N] (u : Rˣ) :
    CoordinateAlgebra (R := R) N u →ₐ[R]
      CoordinateAlgebra (R := R) N u ⊗[R] CoordinateAlgebra (R := R) N u :=
  (tensorCoordinateEquiv N u).symm.toAlgHom.comp (comulCoordinates N u)

@[simp]
lemma tensorCoordinateEquiv_comulAlgHom_apply
    (N : ℕ) [NeZero N] (u : Rˣ)
    (f : CoordinateAlgebra (R := R) N u) (j i : Fin N) :
    tensorCoordinateEquiv N u (comulAlgHom N u f) j i =
      componentMulAlgHom N u i j (f (addIndex N i j)) := by
  change tensorCoordinateEquiv N u
      ((tensorCoordinateEquiv N u).symm (comulCoordinates N u f)) j i = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- Evaluation at the identity point on component zero. -/
noncomputable def identityComponentAlgHom (N : ℕ) [NeZero N] (u : Rˣ) :
    Component R N (0 : Fin N).1 u →ₐ[R] R :=
  AdjoinRoot.liftAlgHom
    (componentPolynomial R N (0 : Fin N).1 u)
    (.id R R) 1 (by
      rw [show componentPolynomial R N (0 : Fin N).1 u =
        X ^ N - C ((u : R) ^ (0 : Fin N).1) from rfl]
      simp)

@[simp]
lemma identityComponentAlgHom_root (N : ℕ) [NeZero N] (u : Rˣ) :
    identityComponentAlgHom N u
      (AdjoinRoot.root (componentPolynomial R N (0 : Fin N).1 u)) = 1 := by
  unfold identityComponentAlgHom
  apply AdjoinRoot.liftAlgHom_root

@[simp]
lemma identityComponentAlgHom_one (N : ℕ) [NeZero N] (u : Rˣ) :
    identityComponentAlgHom N u 1 = 1 :=
  map_one _

/-- Counit on the coordinate algebra: evaluate on the identity point. -/
noncomputable def counitAlgHom (N : ℕ) [NeZero N] (u : Rˣ) :
    CoordinateAlgebra (R := R) N u →ₐ[R] R :=
  (identityComponentAlgHom N u).comp
    (Pi.evalAlgHom R (Components (R := R) N u) 0)

@[simp]
lemma counitAlgHom_apply (N : ℕ) [NeZero N] (u : Rˣ)
    (f : CoordinateAlgebra (R := R) N u) :
    counitAlgHom N u f = identityComponentAlgHom N u (f 0) :=
  rfl

/-- Evaluate the left tensor factor at the identity point. -/
noncomputable def evalLeftIdentity (N : ℕ) [NeZero N] (u : Rˣ) (j : Fin N) :
    (Component R N (0 : Fin N).1 u) ⊗[R] (Component R N j.1 u) →ₐ[R]
      Component R N j.1 u :=
  (Algebra.TensorProduct.lid R (Component R N j.1 u)).toAlgHom.comp
    (Algebra.TensorProduct.map (identityComponentAlgHom N u)
      (.id R (Component R N j.1 u)))

/-- Evaluate the right tensor factor at the identity point. -/
noncomputable def evalRightIdentity (N : ℕ) [NeZero N] (u : Rˣ) (i : Fin N) :
    (Component R N i.1 u) ⊗[R] (Component R N (0 : Fin N).1 u) →ₐ[R]
      Component R N i.1 u :=
  (Algebra.TensorProduct.rid R R (Component R N i.1 u)).toAlgHom.comp
    (Algebra.TensorProduct.map (.id R (Component R N i.1 u))
      (identityComponentAlgHom N u))

@[simp]
lemma evalLeftIdentity_tmul (N : ℕ) [NeZero N] (u : Rˣ) (j : Fin N)
    (x : Component R N (0 : Fin N).1 u) (y : Component R N j.1 u) :
    evalLeftIdentity N u j (x ⊗ₜ[R] y) = identityComponentAlgHom N u x • y := by
  rw [evalLeftIdentity, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]
  rfl

@[simp]
lemma evalRightIdentity_tmul (N : ℕ) [NeZero N] (u : Rˣ) (i : Fin N)
    (x : Component R N i.1 u) (y : Component R N (0 : Fin N).1 u) :
    evalRightIdentity N u i (x ⊗ₜ[R] y) = identityComponentAlgHom N u y • x := by
  rw [evalRightIdentity, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]
  rfl

@[simp]
lemma evalLeftIdentity_includeLeft (N : ℕ) [NeZero N] (u : Rˣ) (j : Fin N)
    (x : Component R N (0 : Fin N).1 u) :
    evalLeftIdentity N u j
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (B := Component R N j.1 u) x) =
      algebraMap R (Component R N j.1 u) (identityComponentAlgHom N u x) := by
  change evalLeftIdentity N u j (x ⊗ₜ[R] 1) = _
  rw [evalLeftIdentity_tmul]
  simp [Algebra.smul_def]

@[simp]
lemma evalLeftIdentity_includeRight (N : ℕ) [NeZero N] (u : Rˣ) (j : Fin N)
    (y : Component R N j.1 u) :
    evalLeftIdentity N u j
        (Algebra.TensorProduct.includeRight
          (R := R) (A := Component R N (0 : Fin N).1 u) y) = y := by
  change evalLeftIdentity N u j (1 ⊗ₜ[R] y) = y
  rw [evalLeftIdentity_tmul]
  rw [identityComponentAlgHom_one (R := R), one_smul]

@[simp]
lemma evalRightIdentity_includeLeft (N : ℕ) [NeZero N] (u : Rˣ) (i : Fin N)
    (x : Component R N i.1 u) :
    evalRightIdentity N u i
        (Algebra.TensorProduct.includeLeft
          (R := R) (S := R) (B := Component R N (0 : Fin N).1 u) x) = x := by
  change evalRightIdentity N u i (x ⊗ₜ[R] 1) = x
  rw [evalRightIdentity_tmul]
  rw [identityComponentAlgHom_one (R := R), one_smul]

@[simp]
lemma evalRightIdentity_includeRight (N : ℕ) [NeZero N] (u : Rˣ) (i : Fin N)
    (y : Component R N (0 : Fin N).1 u) :
    evalRightIdentity N u i
        (Algebra.TensorProduct.includeRight
          (R := R) (A := Component R N i.1 u) y) =
      algebraMap R (Component R N i.1 u) (identityComponentAlgHom N u y) := by
  change evalRightIdentity N u i (1 ⊗ₜ[R] y) = _
  rw [evalRightIdentity_tmul]
  simp [Algebra.smul_def]

/-- Multiplying a coordinate by the identity component on the left is the identity map. -/
lemma evalLeftIdentity_componentMul (N : ℕ) [NeZero N] (u : Rˣ)
    (f : CoordinateAlgebra (R := R) N u) (j : Fin N) :
    evalLeftIdentity N u j
        (componentMulAlgHom N u 0 j (f (addIndex N 0 j))) = f j := by
  let h : addIndex N 0 j = j := addIndex_zero_left N j
  let g : Component R N (addIndex N 0 j).1 u →ₐ[R] Component R N j.1 u :=
    (evalLeftIdentity N u j).comp (componentMulAlgHom N u 0 j)
  have hg : g = (componentEquivOfEq N u h).toAlgHom := by
    apply AdjoinRoot.algHom_ext
    dsimp only [g]
    rw [AlgHom.comp_apply, componentMulAlgHom_root]
    calc
      evalLeftIdentity N u j (componentMulRoot N u 0 j) =
          AdjoinRoot.root (componentPolynomial R N j.1 u) := by
        rw [componentMulRoot, map_mul, map_mul]
        rw [evalLeftIdentity_includeLeft (R := R),
          evalLeftIdentity_includeRight (R := R),
          identityComponentAlgHom_root (R := R)]
        rw [(evalLeftIdentity N u j).commutes]
        simp [addCarry_zero_left]
      _ = componentEquivOfEq N u h
          (AdjoinRoot.root
            (componentPolynomial R N (addIndex N 0 j).1 u)) :=
        (componentEquivOfEq_root (R := R) N u h).symm
  change g (f (addIndex N 0 j)) = f j
  rw [hg]
  exact componentEquivOfEq_coordinate N u f h

/-- Multiplying a coordinate by the identity component on the right is the identity map. -/
lemma evalRightIdentity_componentMul (N : ℕ) [NeZero N] (u : Rˣ)
    (f : CoordinateAlgebra (R := R) N u) (i : Fin N) :
    evalRightIdentity N u i
        (componentMulAlgHom N u i 0 (f (addIndex N i 0))) = f i := by
  let h : addIndex N i 0 = i := addIndex_zero_right N i
  let g : Component R N (addIndex N i 0).1 u →ₐ[R] Component R N i.1 u :=
    (evalRightIdentity N u i).comp (componentMulAlgHom N u i 0)
  have hg : g = (componentEquivOfEq N u h).toAlgHom := by
    apply AdjoinRoot.algHom_ext
    dsimp only [g]
    rw [AlgHom.comp_apply, componentMulAlgHom_root]
    calc
      evalRightIdentity N u i (componentMulRoot N u i 0) =
          AdjoinRoot.root (componentPolynomial R N i.1 u) := by
        rw [componentMulRoot, map_mul, map_mul]
        rw [evalRightIdentity_includeLeft (R := R),
          evalRightIdentity_includeRight (R := R),
          identityComponentAlgHom_root (R := R)]
        rw [(evalRightIdentity N u i).commutes]
        simp [addCarry_zero_right]
      _ = componentEquivOfEq N u h
          (AdjoinRoot.root
            (componentPolynomial R N (addIndex N i 0).1 u)) :=
        (componentEquivOfEq_root (R := R) N u h).symm
  change g (f (addIndex N i 0)) = f i
  rw [hg]
  exact componentEquivOfEq_coordinate N u f h

end TateKummer
