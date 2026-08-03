/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle
public import FLT.Deformations.IsProartinian
public import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-!
# Power-series parameter maps

This file supplies the topological commutative-algebra part of the parameter construction in
Böckle's presentation theorem.  A finite family in the maximal ideal of a local pro-Artinian
ring can be evaluated in convergent power series.  If the resulting map has dense range, compactness
of the source upgrades density to actual surjectivity.
-/

@[expose] public section

namespace Deformation

open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

universe u

variable {R D : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [IsLocalRing D]

/-- A finite family in the maximal ideal of a local pro-Artinian ring is a valid point at
which to evaluate multivariate power series. -/
theorem hasEval_of_finite_mem_maximalIdeal
    {n : Type*} [Finite n] [IsProartinian D]
    (x : n → D) (hx : ∀ i, x i ∈ maximalIdeal D) : MvPowerSeries.HasEval x where
  hpow i := isTopologicallyNilpotent_of_mem_maximalIdeal (hx i)
  tendsto_zero := by
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

variable [Algebra R D] [ContinuousSMul R D]

/-- Evaluate a finite-variable power-series ring at parameters in the maximal ideal of a
complete local pro-Artinian algebra. -/
noncomputable def powerSeriesMapOfParameters
    {n : Type*} [Finite n] [IsProartinian D]
    (x : n → D) (hx : ∀ i, x i ∈ maximalIdeal D) : MvPowerSeries n R →ₐ[R] D := by
  letI := IsTopologicalAddGroup.rightUniformSpace R
  letI := IsTopologicalAddGroup.rightUniformSpace D
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  letI := isUniformAddGroup_of_addCommGroup (G := D)
  exact MvPowerSeries.aeval (hasEval_of_finite_mem_maximalIdeal x hx)

@[simp]
theorem powerSeriesMapOfParameters_X
    {n : Type*} [Finite n] [IsProartinian D]
    (x : n → D) (hx : ∀ i, x i ∈ maximalIdeal D) (i : n) :
    powerSeriesMapOfParameters (R := R) x hx (MvPowerSeries.X i) = x i := by
  letI := IsTopologicalAddGroup.rightUniformSpace R
  letI := IsTopologicalAddGroup.rightUniformSpace D
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  letI := isUniformAddGroup_of_addCommGroup (G := D)
  unfold powerSeriesMapOfParameters
  rw [MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]

@[simp]
theorem powerSeriesMapOfParameters_C
    {n : Type*} [Finite n] [IsProartinian D]
    (x : n → D) (hx : ∀ i, x i ∈ maximalIdeal D) (r : R) :
    powerSeriesMapOfParameters (R := R) x hx (MvPowerSeries.C r) = algebraMap R D r := by
  letI := IsTopologicalAddGroup.rightUniformSpace R
  letI := IsTopologicalAddGroup.rightUniformSpace D
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  letI := isUniformAddGroup_of_addCommGroup (G := D)
  unfold powerSeriesMapOfParameters
  rw [MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_C]

/-- The power-series parameter map is continuous. -/
theorem continuous_powerSeriesMapOfParameters
    {n : Type*} [Finite n] [IsProartinian D]
    (x : n → D) (hx : ∀ i, x i ∈ maximalIdeal D) :
    Continuous (powerSeriesMapOfParameters (R := R) x hx) := by
  letI := IsTopologicalAddGroup.rightUniformSpace R
  letI := IsTopologicalAddGroup.rightUniformSpace D
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  letI := isUniformAddGroup_of_addCommGroup (G := D)
  exact MvPowerSeries.continuous_aeval (hasEval_of_finite_mem_maximalIdeal x hx)

/-- A continuous map from a compact space to a Hausdorff space with dense range is
surjective. -/
theorem surjective_of_compact_of_continuous_of_denseRange
    {A B : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (hf : Continuous f) (hdense : DenseRange f) :
    Function.Surjective f := by
  rw [← Set.range_eq_univ]
  have hclosed : IsClosed (Set.range f) := hf.isClosedMap.isClosed_range
  rw [← hclosed.closure_eq]
  exact hdense.closure_range

/-- A map is surjective modulo every open ideal if every target element can be approximated
to arbitrary open-ideal precision by an element of its range. -/
def IsSurjectiveModuloOpenIdeals
    {A : Type*} (f : A → D) : Prop :=
  ∀ (I : Ideal D), IsOpen (X := D) (I : Set D) →
    ∀ y : D, ∃ x : A, f x - y ∈ I

/-- Surjectivity modulo all open ideals is exactly the approximation statement needed for
density in a linearly topologized ring. -/
theorem denseRange_of_isSurjectiveModuloOpenIdeals
    {A : Type*} [IsLinearTopology D D]
    (f : A → D) (hf : IsSurjectiveModuloOpenIdeals f) : DenseRange f := by
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro y
  let hzero := IsLinearTopology.hasBasis_open_ideal (R := D)
  let hy := hzero.map (y + ·)
  rw [map_add_left_nhds_zero y] at hy
  rw [mem_closure_iff_nhds_basis hy]
  intro I hI
  obtain ⟨x, hx⟩ := hf I hI y
  refine ⟨f x, Set.mem_range_self x, ?_⟩
  exact ⟨f x - y, hx, by simp⟩

/-- For compact coefficients and finitely many variables, density of the parameter map is
equivalent to the surjectivity required by a Böckle presentation. -/
theorem powerSeriesMapOfParameters_surjective_of_denseRange
    {n : Type*} [Finite n] [IsProartinian D] [CompactSpace R]
    (x : n → D) (hx : ∀ i, x i ∈ maximalIdeal D)
    (hdense : DenseRange (powerSeriesMapOfParameters (R := R) x hx)) :
    Function.Surjective (powerSeriesMapOfParameters (R := R) x hx) := by
  letI : CompactSpace (MvPowerSeries n R) :=
    inferInstanceAs (CompactSpace ((n →₀ ℕ) → R))
  exact surjective_of_compact_of_continuous_of_denseRange _
    (continuous_powerSeriesMapOfParameters (R := R) x hx) hdense

/-- It is enough to solve the parameter problem over every discrete Artinian quotient of the
target: completeness supplies density and compactness closes the image. -/
theorem powerSeriesMapOfParameters_surjective_of_mod_openIdeals
    {n : Type*} [Finite n] [IsProartinian D] [CompactSpace R]
    (x : n → D) (hx : ∀ i, x i ∈ maximalIdeal D)
    (hmod : IsSurjectiveModuloOpenIdeals
      (powerSeriesMapOfParameters (R := R) x hx)) :
    Function.Surjective (powerSeriesMapOfParameters (R := R) x hx) :=
  powerSeriesMapOfParameters_surjective_of_denseRange x hx
    (denseRange_of_isSurjectiveModuloOpenIdeals _ hmod)

end Deformation
