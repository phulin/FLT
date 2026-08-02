/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Complements on rational p-adic valuations

This file supplies the discrete-valuation-ring instance for the valuation subring of the standard
`p`-adic valuation on `ℚ`. The valuation is surjective onto `ℤᵐ⁰`, so its value group is the full
cyclic group of units of `ℤᵐ⁰` and is nontrivial.
-/

@[expose] public section

open MonoidWithZeroHom
open scoped WithZero

namespace Rat

instance {p : ℕ} [Fact p.Prime] :
    IsDiscreteValuationRing (padicValuation p).valuationSubring := by
  let v := padicValuation p
  have hvg : valueGroup (.ofClass v) = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    rw [mem_valueGroup_iff_of_comm]
    obtain ⟨y, hy⟩ := surjective_padicValuation p x
    exact ⟨1, by simp, y, by simpa [v] using hy.symm⟩
  let _ : IsCyclic (valueGroup (.ofClass v)) := hvg.symm ▸ inferInstance
  have hvnontriv : v.IsNontrivial := by
    refine ⟨p, ?_, ?_⟩
    · simp [v]
    · simp [v]
  let _ : v.IsNontrivial := hvnontriv
  let _ : Nontrivial (valueGroup (.ofClass v)) := inferInstance
  exact Valuation.valuationSubring_isDiscreteValuationRing v

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing in
/-- The adic valuation attached to the maximal ideal of the valuation subring agrees with the
standard `p`-adic valuation on whether an integral rational number is a unit. -/
lemma adicValuation_eq_one_of_padicValuation_eq_one {p : ℕ} [Fact p.Prime]
    {x : ℚ} (hx : padicValuation p x = 1) :
    valuation ℚ (maximalIdeal (padicValuation p).valuationSubring) x = 1 := by
  let x₀ : (padicValuation p).valuationSubring := ⟨x, hx.le⟩
  rw [show x = algebraMap (padicValuation p).valuationSubring ℚ x₀ from rfl,
    valuation_eq_one_iff_notMem]
  change x₀ ∉ IsLocalRing.maximalIdeal (padicValuation p).valuationSubring
  rw [Valuation.mem_maximalIdeal_iff]
  simp [x₀, hx]

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing in
/-- The adic valuation attached to the maximal ideal of the valuation subring agrees with the
standard `p`-adic valuation on whether an integral rational number lies in the maximal ideal. -/
lemma adicValuation_lt_one_of_padicValuation_lt_one {p : ℕ} [Fact p.Prime]
    {x : ℚ} (hx : padicValuation p x < 1) :
    valuation ℚ (maximalIdeal (padicValuation p).valuationSubring) x < 1 := by
  let x₀ : (padicValuation p).valuationSubring := ⟨x, hx.le⟩
  rw [show x = algebraMap (padicValuation p).valuationSubring ℚ x₀ from rfl,
    valuation_lt_one_iff_mem]
  change x₀ ∈ IsLocalRing.maximalIdeal (padicValuation p).valuationSubring
  rw [Valuation.mem_maximalIdeal_iff]
  exact hx

end Rat
