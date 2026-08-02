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

end TateKummer
