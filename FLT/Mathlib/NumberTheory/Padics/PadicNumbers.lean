/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Complements on rational p-adic valuations

This file supplies the discrete-valuation-ring instance for the valuation subring of the standard
`p`-adic valuation on `ℚ`. The valuation is surjective onto `ℤᵐ⁰`, so its value group is the full
cyclic group of units of `ℤᵐ⁰` and is nontrivial.
-/

@[expose] public section

open MonoidWithZeroHom
open scoped WithZero

namespace Padic

open ValuativeRel

/-- The canonical valuative-relation integer subring of `ℚ_[p]` has the same carrier as
`PadicInt`: both say that the p-adic norm is at most one. -/
lemma mem_integer_iff_norm_le_one {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) :
    x ∈ (ValuativeRel.valuation ℚ_[p]).integer ↔ ‖x‖ ≤ 1 := by
  classical
  rw [Valuation.mem_integer_iff, Padic.norm_le_one_iff_val_nonneg]
  rw [(ValuativeRel.isEquiv
    (ValuativeRel.valuation ℚ_[p]) Padic.mulValuation).le_one_iff_le_one]
  by_cases hx : x = 0
  · simp [hx]
  · change (if x = 0 then 0 else WithZero.exp (-x.valuation)) ≤ 1 ↔ _
    rw [if_neg hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

/-- The canonical valuative-relation integer subring of `ℚ_[p]` is canonically equivalent
to the traditional type `ℤ_[p]` of p-adic integers. -/
noncomputable def integerEquivPadicInt (p : ℕ) [Fact p.Prime] :
    (ValuativeRel.valuation ℚ_[p]).integer ≃+* ℤ_[p] where
  toFun x := ⟨x.1, (mem_integer_iff_norm_le_one (p := p) (x : ℚ_[p])).mp x.2⟩
  invFun x := ⟨x.1, (mem_integer_iff_norm_le_one (p := p) (x : ℚ_[p])).mpr x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The canonical integer subring of the standard p-adic field is a discrete valuation
ring. This transports the existing DVR structure on `PadicInt` across the canonical
subtype equivalence. -/
noncomputable instance integer_isDiscreteValuationRing {p : ℕ} [Fact p.Prime] :
    IsDiscreteValuationRing (ValuativeRel.valuation ℚ_[p]).integer := by
  let e := (integerEquivPadicInt p).symm
  letI : IsPrincipalIdealRing (ValuativeRel.valuation ℚ_[p]).integer :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  letI : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  letI : IsLocalRing (ValuativeRel.valuation ℚ_[p]).integer :=
    IsLocalRing.of_surjective e.toRingHom e.surjective
  refine { not_a_field' := ?_ }
  intro hbot
  have hp_nonunit : ¬IsUnit (e (p : ℤ_[p])) := by
    intro hpunit
    apply PadicInt.p_nonunit (p := p)
    simpa using hpunit.map e.symm.toRingHom
  have hp_mem :
      e (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal
        (ValuativeRel.valuation ℚ_[p]).integer := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hp_nonunit
  rw [hbot, Ideal.mem_bot] at hp_mem
  have hp_ne : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply hp_ne
  apply e.injective
  simpa using hp_mem

end Padic

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
