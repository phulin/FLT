/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ModThree
public import FLT.NumberField.Chebotarev

import FLT.Deformations.CharacteristicZeroPoint
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# 3-adic hardly ramified representations

Three-adic input results for the analysis of hardly ramified families:
properties of `R`-linear representations on a finite `ℤ_[3]`-module which
are hardly ramified at 3.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

open IsLocalRing
open scoped TensorProduct

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- The mod-maximal-ideal base case of the 3-adic character congruence.  Reduce the
representation to the finite residue field, apply `mod_three_trace_eq_one_add_det`, and pull
the resulting equality back through the residue map. -/
theorem three_adic_trace_sub_one_add_det_mem_maximalIdeal
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) (g : Γ ℚ) :
    LinearMap.trace R V (ρ g) - (1 + LinearMap.det (ρ g)) ∈ maximalIdeal R := by
  letI : Finite (ResidueField ℤ_[3]) :=
    Finite.of_equiv (ZMod 3) PadicInt.residueField.symm.toEquiv
  letI : Finite (ResidueField R) :=
    ResidueField.finite_of_finite (R := ℤ_[3]) (S := R) inferInstance
  letI : IsProartinian R :=
    Deformation.isProartinian_of_finiteFree_moduleTopology ℤ_[3] R
  let k := ResidueField R
  letI : TopologicalSpace k := ⊥
  letI : DiscreteTopology k := ⟨rfl⟩
  letI : IsResidueAlgebra R k := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨r, rfl⟩
  have hrescont : Continuous (algebraMap R k) := by
    apply RingHom.continuous_iff_isOpen_ker.mpr
    rw [show RingHom.ker (algebraMap R k) = maximalIdeal R from ker_residue]
    exact isOpen_maximalIdeal_of_isProartinian
  letI : ContinuousSMul R k := continuousSMul_of_algebraMap R k hrescont
  let hVk : Module.rank k (k ⊗[R] V) = 2 := rank_two_baseChange hV
  let ρk : GaloisRep ℚ k (k ⊗[R] V) := ρ.baseChange k
  have hρk : IsHardlyRamified (show Odd 3 by decide) hVk ρk :=
    IsHardlyRamified.baseChange (show Odd 3 by decide) hV hVk ρ hρ
  have hk := mod_three_trace_eq_one_add_det (k ⊗[R] V) hVk hρk g
  dsimp only [ρk] at hk
  rw [GaloisRep.trace_baseChange] at hk
  have hdet : LinearMap.det ((ρ.baseChange k) g) =
      algebraMap R k (LinearMap.det (ρ g)) := GaloisRep.det_baseChange ρ g
  rw [hdet] at hk
  rw [← residue_eq_zero_iff]
  exact sub_eq_zero.mpr hk

/-- The arithmetic induction step for the 3-adic classification.  If the character is
congruent to `1 + det` modulo `𝔪ⁿ⁺¹`, the Schoof--Fontaine devissage of the associated finite
flat group scheme improves the congruence to `𝔪ⁿ⁺²`.  Concretely, one moves every
multiplicative Jordan--Hölder factor to the subobject and every constant factor to the quotient;
the obstruction is the nonexistence of a hardly ramified extension in the opposite order. -/
theorem three_adic_trace_deformation_step
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) (n : ℕ)
    (hprev : ∀ g : Γ ℚ,
      LinearMap.trace R V (ρ g) - (1 + LinearMap.det (ρ g)) ∈
        maximalIdeal R ^ (n + 1)) :
    ∀ g : Γ ℚ, LinearMap.trace R V (ρ g) - (1 + LinearMap.det (ρ g)) ∈
      maximalIdeal R ^ (n + 2) := by
  sorry

/-- At every positive maximal-ideal power, the finite-level devissage makes the character
congruent to `1 + det`. -/
theorem three_adic_trace_sub_one_add_det_mem_maximalIdeal_pow_succ
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) (n : ℕ) (g : Γ ℚ) :
    LinearMap.trace R V (ρ g) - (1 + LinearMap.det (ρ g)) ∈
      maximalIdeal R ^ (n + 1) := by
  induction n generalizing g with
  | zero =>
      simpa using three_adic_trace_sub_one_add_det_mem_maximalIdeal V hV hρ g
  | succ n ih =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        three_adic_trace_deformation_step V hV hρ n ih g

/-- The finite-level character congruence for every maximal-ideal power.  The zeroth power is
the unit ideal; positive powers are the arithmetic Schoof--Fontaine input. -/
theorem three_adic_trace_sub_one_add_det_mem_maximalIdeal_pow
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) (n : ℕ) (g : Γ ℚ) :
    LinearMap.trace R V (ρ g) - (1 + LinearMap.det (ρ g)) ∈
      IsLocalRing.maximalIdeal R ^ n := by
  cases n with
  | zero => simp
  | succ n =>
      simpa only [Nat.succ_eq_add_one] using
        three_adic_trace_sub_one_add_det_mem_maximalIdeal_pow_succ V hV hρ n g

/-- The finite-level Schoof--Fontaine congruences determine the 3-adic character because a
module-finite local algebra over `ℤ_[3]` is Noetherian and hence separated for its maximal-ideal
adic filtration. -/
theorem three_adic_trace_eq_one_add_det
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ g : Γ ℚ, LinearMap.trace R V (ρ g) = 1 + LinearMap.det (ρ g) := by
  letI : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  intro g
  apply sub_eq_zero.mp
  rw [← Ideal.mem_bot (R := R),
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_iInf]
  exact fun n ↦ three_adic_trace_sub_one_add_det_mem_maximalIdeal_pow V hV hρ n g

/--
A 3-adic hardly ramified representation has trace(Frob_p) = 1 + p for all p ≠ 2,3
-/
theorem three_adic {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ p (hp : Nat.Prime p) (_hp5 : 5 ≤ p),
      letI v := hp.toHeightOneSpectrumRingOfIntegersRat -- p as a finite place of ℚ
      (ρ.toLocal v (Frob v)).trace _ _ = 1 + p := by
  intro p hp _hp5
  let v := hp.toHeightOneSpectrumRingOfIntegersRat
  have h3v : (3 : NumberField.RingOfIntegers ℚ) ∉ v.asIdeal := by
    change (3 : NumberField.RingOfIntegers ℚ) ∉
      hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal
    intro h3
    have hp3 : p ∣ 3 :=
      (Field.AbsoluteGaloisGroup.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal_iff_dvd
        hp).mp h3
    have hp_le_three := Nat.le_of_dvd (by decide : 0 < 3) hp3
    omega
  rw [GaloisRep.toLocal_adicArithFrob,
    three_adic_trace_eq_one_add_det V hV hρ]
  congr 1
  change ρ.det (Field.AbsoluteGaloisGroup.globalAdicArithFrob v) = (p : R)
  rw [hρ.det,
    Field.AbsoluteGaloisGroup.cyclotomicCharacter_globalAdicArithFrob hp h3v]
  simp

end GaloisRepresentation.IsHardlyRamified
