/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ModThree
public import FLT.NumberField.Chebotarev

import FLT.Deformations.CharacteristicZeroPoint
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Ring.Compact
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

/-- Equality after passing to a quotient ring is the same as membership of the character
difference in the quotient ideal.  This lemma separates the commutative-algebra bookkeeping
from the finite-flat arithmetic input below. -/
theorem trace_sub_one_add_det_mem_ideal_iff_quotient_character
    {R : Type*} [CommRing R] (I : Ideal R) (t d : R) :
    t - (1 + d) ∈ I ↔
      algebraMap R (R ⧸ I) t = 1 + algebraMap R (R ⧸ I) d := by
  simpa only [Ideal.Quotient.algebraMap_eq, map_add, map_one] using
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := I) t (1 + d)).symm

/-- In a finite free `ℤ_[3]`-algebra with its module topology, every maximal-ideal power is
open.  The proof passes through compactness, Hausdorffness, and Noetherianity. -/
theorem isOpen_maximalIdeal_pow_of_finiteFree_moduleTopology
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R] (n : ℕ) :
    IsOpen (X := R) (↑(maximalIdeal R ^ n) : Set R) := by
  letI : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  letI : CompactSpace R := Module.Finite.compactSpace ℤ_[3] R
  letI : T2Space R := IsModuleTopology.t2Space ℤ_[3]
  exact IsLocalRing.isOpen_maximalIdeal_pow R n

/-- The coefficient map to a maximal-ideal-power quotient is continuous when the quotient is
given its discrete topology. -/
theorem continuous_algebraMap_quotient_maximalIdeal_pow
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R] (n : ℕ)
    [TopologicalSpace (R ⧸ maximalIdeal R ^ n)]
    [DiscreteTopology (R ⧸ maximalIdeal R ^ n)] :
    Continuous (algebraMap R (R ⧸ maximalIdeal R ^ n)) := by
  apply RingHom.continuous_iff_isOpen_ker.mpr
  simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using
    isOpen_maximalIdeal_pow_of_finiteFree_moduleTopology (R := R) n

/-- Maximal-ideal-power quotients of a finite free `ℤ_[3]`-algebra are finite. -/
theorem finite_quotient_maximalIdeal_pow_of_finiteFree_moduleTopology
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R] (n : ℕ) :
    Finite (R ⧸ maximalIdeal R ^ n) := by
  letI : CompactSpace R := Module.Finite.compactSpace ℤ_[3] R
  exact AddSubgroup.quotient_finite_of_isOpen _
    (isOpen_maximalIdeal_pow_of_finiteFree_moduleTopology (R := R) n)

/-- The arithmetic input for a hardly ramified representation over a finite local
`ℤ_[3]`-algebra.  Applied to its finite flat group scheme, Schoof's argument first shows that
the only simple factors are `ℤ/3ℤ` and `μ₃`.  The vanishing
`Ext¹(μ₃, ℤ/3ℤ) = 0` then reorders a composition series into a multiplicative subobject and a
constant quotient.  Their two characters give the displayed identity.

The simple-object classification is the `(ℓ,p) = (2,3)` case in the proof of Schoof,
*Abelian varieties over Q with bad reduction in one prime only*, Theorem 1.3; the reordering is
Proposition 3.2 and the required extension vanishing is Corollary 4.2. -/
theorem schoof_three_adic_finite_character
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {τ : GaloisRep ℚ A W}
    (hτ : IsHardlyRamified (show Odd 3 by decide) hW τ) :
    ∀ g : Γ ℚ, LinearMap.trace A W (τ g) = 1 + LinearMap.det (τ g) := by
  sorry

/-- Apply the finite-ring classification to the representation modulo `𝔪ⁿ⁺²`.  All structural
hypotheses on the quotient and preservation of hard ramification are discharged here; the only
arithmetic input is `schoof_three_adic_finite_character`. -/
theorem schoof_three_adic_finite_level_character_succ_succ
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) (n : ℕ) :
    let A := R ⧸ maximalIdeal R ^ (n + 2)
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : IsTopologicalRing A := ⟨⟩
    letI : ContinuousSMul R A := continuousSMul_of_algebraMap R A
      (continuous_algebraMap_quotient_maximalIdeal_pow (R := R) (n + 2))
    ∀ g : Γ ℚ, LinearMap.trace A (A ⊗[R] V) ((ρ.baseChange A) g) =
      1 + LinearMap.det ((ρ.baseChange A) g) := by
  let A := R ⧸ maximalIdeal R ^ (n + 2)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := ⟨⟩
  letI : ContinuousSMul R A := continuousSMul_of_algebraMap R A
    (continuous_algebraMap_quotient_maximalIdeal_pow (R := R) (n + 2))
  letI : Finite A :=
    finite_quotient_maximalIdeal_pow_of_finiteFree_moduleTopology (R := R) (n + 2)
  have hpowpos : 0 < n + 2 := by omega
  letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self hpowpos.ne').trans_lt
      (lt_top_iff_ne_top.mpr (maximalIdeal.isMaximal R).ne_top)).ne
  letI : IsLocalRing A := .of_surjective' _ Ideal.Quotient.mk_surjective
  letI : IsLocalHom (algebraMap R A) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsProartinian R :=
    Deformation.isProartinian_of_finiteFree_moduleTopology ℤ_[3] R
  letI : IsArtinianRing A := inferInstance
  letI : IsProartinian A := inferInstance
  let hVA : Module.rank A (A ⊗[R] V) = 2 := rank_two_baseChange hV
  have hρA : IsHardlyRamified (show Odd 3 by decide) hVA (ρ.baseChange A) :=
    IsHardlyRamified.baseChange (show Odd 3 by decide) hV hVA ρ hρ
  exact schoof_three_adic_finite_character (A ⊗[R] V) hVA hρA

/-- The scalar form of the finite-quotient character identity, obtained from the actual
quotient representation by functoriality of trace and determinant. -/
theorem three_adic_finite_level_quotient_character_succ_succ
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) (n : ℕ) :
    ∀ g : Γ ℚ,
      algebraMap R (R ⧸ maximalIdeal R ^ (n + 2)) (LinearMap.trace R V (ρ g)) =
        1 + algebraMap R (R ⧸ maximalIdeal R ^ (n + 2)) (LinearMap.det (ρ g)) := by
  let A := R ⧸ maximalIdeal R ^ (n + 2)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := ⟨⟩
  letI : ContinuousSMul R A := continuousSMul_of_algebraMap R A
    (continuous_algebraMap_quotient_maximalIdeal_pow (R := R) (n + 2))
  intro g
  have h := schoof_three_adic_finite_level_character_succ_succ V hV hρ n g
  rw [GaloisRep.trace_baseChange] at h
  have hdet : LinearMap.det (((ρ.baseChange A)) g) =
      algebraMap R A (LinearMap.det (ρ g)) :=
    GaloisRep.det_baseChange ρ g
  rw [hdet] at h
  exact h

/-- Compatibility form of the finite-level theorem.  The induction hypothesis records the
interface used by the original proof, but Schoof's classification applies directly to the
next finite quotient. -/
theorem three_adic_trace_deformation_step
    {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) (n : ℕ)
    (_hprev : ∀ g : Γ ℚ,
      LinearMap.trace R V (ρ g) - (1 + LinearMap.det (ρ g)) ∈
        maximalIdeal R ^ (n + 1)) :
    ∀ g : Γ ℚ, LinearMap.trace R V (ρ g) - (1 + LinearMap.det (ρ g)) ∈
      maximalIdeal R ^ (n + 2) := by
  intro g
  apply (trace_sub_one_add_det_mem_ideal_iff_quotient_character
    (maximalIdeal R ^ (n + 2)) _ _).mpr
  exact three_adic_finite_level_quotient_character_succ_succ V hV hρ n g

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
  cases n with
  | zero => simpa using three_adic_trace_sub_one_add_det_mem_maximalIdeal V hV hρ g
  | succ n =>
      apply (trace_sub_one_add_det_mem_ideal_iff_quotient_character
        (maximalIdeal R ^ (n + 2)) _ _).mpr
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
        three_adic_finite_level_quotient_character_succ_succ V hV hρ n g

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
