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

/-- For finite discrete coefficients, the flat-at-`3` part of hard ramification produces an
actual finite-flat Hopf-algebra model for the given local Galois module, without a residual
scalar extension. -/
theorem schoof_three_adic_hasFlatProlongationAt_three
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {τ : GaloisRep ℚ A W}
    (hτ : IsHardlyRamified (show Odd 3 by decide) hW τ) :
    τ.HasFlatProlongationAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (show Nat.Prime 3 by decide)) := by
  letI : τ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (show Nat.Prime 3 by decide)) := hτ.isFlat
  exact τ.hasFlatProlongationAt_of_discrete
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (show Nat.Prime 3 by decide))

/-- The finite Galois extension cut out by a finite three-adic representation is unramified
outside `2` and `3`, in the precise Galois-theoretic sense that local inertia acts trivially
on the extension.  This transfers the representation-level hard-ramification hypothesis to
the finite extension used in Schoof's classification argument. -/
theorem schoof_three_adic_fieldCutOut_unramified_outside_two_three
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {τ : GaloisRep ℚ A W}
    (hτ : IsHardlyRamified (show Odd 3 by decide) hW τ) :
    ∀ p (hp : p.Prime), p ≠ 2 ∧ p ≠ 3 →
      localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat ≤
        (τ.fieldCutOutLocalAction hp.toHeightOneSpectrumRingOfIntegersRat).ker := by
  intro p hp hp_ne
  letI : τ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
    hτ.isUnramified p hp hp_ne
  exact τ.localInertiaGroup_le_fieldCutOutLocalAction_ker
    hp.toHeightOneSpectrumRingOfIntegersRat

/-- At `2`, the one-dimensional tame quotient supplied by hard ramification factors through
the action on the finite field cut out by the representation.  The statement also separates
the equivariance, unramifiedness, and quadratic-character conditions that Schoof's local
analysis uses. -/
theorem schoof_three_adic_fieldCutOut_tame_quotient_at_two
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {τ : GaloisRep ℚ A W}
    (hτ : IsHardlyRamified (show Odd 3 by decide) hW τ) :
    ∃ (π : W →ₗ[A] A) (_ : Function.Surjective π) (δ : GaloisRep ℚ_[2] A A),
      (τ.fieldCutOutAction (algebraMap ℚ ℚ_[2])).ker ≤ δ.ker ∧
      (∀ g : Γ ℚ_[2], ∀ w : W,
        π (τ.map (algebraMap ℚ ℚ_[2]) g w) = δ g (π w)) ∧
      (AddSubgroup.inertia
        ((maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2]) ≤ δ.ker) ∧
      (∀ g : Γ ℚ_[2], δ g * δ g = 1) := by
  obtain ⟨π, hπ, δ, hπτ⟩ := hτ.isTameAtTwo
  have hintertwines : ∀ g : Γ ℚ_[2], ∀ w : W,
      π (τ.map (algebraMap ℚ ℚ_[2]) g w) = δ g (π w) :=
    fun g w ↦ (hπτ g w).1
  have hker : (τ.fieldCutOutAction (algebraMap ℚ ℚ_[2])).ker ≤ δ.ker := by
    rw [τ.fieldCutOutAction_ker]
    exact GaloisRep.ker_le_ker_of_surjective_intertwiner
      (τ.map (algebraMap ℚ ℚ_[2])) δ π hπ hintertwines
  exact ⟨π, hπ, δ, hker, hintertwines, (hπτ 1 0).2.1, (hπτ 1 0).2.2⟩

/-- Inertia at `2` has character `1 + det` on a finite three-adic hardly ramified
representation.  The hard-ramification hypothesis only states that a rank-one quotient is
unramified; the local-ring version of the rank-two trace lemma upgrades this to a character
identity for the entire representation. -/
theorem schoof_three_adic_inertia_trace_eq_one_add_det_at_two
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {tau : GaloisRep ℚ A W}
    (htau : IsHardlyRamified (show Odd 3 by decide) hW tau) :
    ∀ g : Γ ℚ_[2],
      g ∈ AddSubgroup.inertia
        ((maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2]) →
      LinearMap.trace A W (tau.map (algebraMap ℚ ℚ_[2]) g) =
        1 + LinearMap.det (tau.map (algebraMap ℚ ℚ_[2]) g) := by
  obtain ⟨pi, hpi, delta, hpitau⟩ := htau.isTameAtTwo
  intro g hg
  have hgdelta : g ∈ delta.ker := (hpitau 1 0).2.1 hg
  have hpitriv : ∀ w : W,
      pi (tau.map (algebraMap ℚ ℚ_[2]) g w) = pi w := by
    intro w
    rw [(hpitau g w).1, show delta g = 1 from hgdelta]
    rfl
  exact LinearMap.trace_eq_one_add_det_of_surjective_invariant_quotient
    hW (tau.map (algebraMap ℚ ℚ_[2]) g) pi hpi hpitriv

/-- If the determinant is trivial on an inertia element at `2`, its action is unipotent of
index at most two.  Together with the unramifiedness of the `3`-adic cyclotomic determinant,
this is the linear-algebra input for proving that wild inertia acts trivially. -/
theorem schoof_three_adic_inertia_unipotent_at_two
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {tau : GaloisRep ℚ A W}
    (htau : IsHardlyRamified (show Odd 3 by decide) hW tau)
    (g : Γ ℚ_[2])
    (hg : g ∈ AddSubgroup.inertia
      ((maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2]))
    (hdet : LinearMap.det (tau.map (algebraMap ℚ ℚ_[2]) g) = 1) :
    let f := tau.map (algebraMap ℚ ℚ_[2]) g
    (f - LinearMap.id).comp (f - LinearMap.id) = 0 := by
  obtain ⟨pi, hpi, delta, hpitau⟩ := htau.isTameAtTwo
  have hgdelta : g ∈ delta.ker := (hpitau 1 0).2.1 hg
  have hpitriv : ∀ w : W,
      pi (tau.map (algebraMap ℚ ℚ_[2]) g w) = pi w := by
    intro w
    rw [(hpitau g w).1, show delta g = 1 from hgdelta]
    rfl
  exact LinearMap.sub_id_comp_self_eq_zero_of_surjective_invariant_quotient_det_eq_one
    hW (tau.map (algebraMap ℚ ℚ_[2]) g) pi hpi hpitriv hdet

/-- The arithmetic filtration input for a hardly ramified representation over a finite local
`ℤ_[3]`-algebra.  Applied to its finite flat group scheme, Schoof's argument first shows that
the only simple factors are `ℤ/3ℤ` and `μ₃`.  The vanishing
`Ext¹(μ₃, ℤ/3ℤ) = 0` then reorders a composition series into a diagonalizable subobject and a
constant quotient.  On geometric points, the quotient is fixed and the subobject has the
cyclotomic character, which equals the determinant by hard ramification.  The filtration is
stable under the coefficient algebra because its scalars act by commuting endomorphisms.

The simple-object classification is the `(ℓ,p) = (2,3)` case in the proof of Schoof,
*Abelian varieties over Q with bad reduction in one prime only*, Theorem 1.3; the reordering is
Proposition 3.2 and the required extension vanishing is Corollary 4.2. -/
theorem schoof_three_adic_finite_multiplicative_constant_filtration
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {τ : GaloisRep ℚ A W}
    (hτ : IsHardlyRamified (show Odd 3 by decide) hW τ) :
    ∃ N : Submodule A W,
      (∀ g : Γ ℚ, ∀ x : W, τ g x - x ∈ N) ∧
      (∀ g : Γ ℚ, ∀ x : W, x ∈ N → τ g x = LinearMap.det (τ g) • x) := by
  sorry

/-- The character identity formally implied by Schoof's multiplicative/constant filtration.
The linear-algebra step does not require either side of the filtration to be free. -/
theorem schoof_three_adic_finite_character
    {A : Type*} [Finite A] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [IsLocalRing A] [Algebra ℤ_[3] A]
    (W : Type*) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (hW : Module.rank A W = 2) {τ : GaloisRep ℚ A W}
    (hτ : IsHardlyRamified (show Odd 3 by decide) hW τ) :
    ∀ g : Γ ℚ, LinearMap.trace A W (τ g) = 1 + LinearMap.det (τ g) := by
  obtain ⟨N, hquot, hsub⟩ :=
    schoof_three_adic_finite_multiplicative_constant_filtration W hW hτ
  intro g
  have hbij : Function.Bijective (τ g) := by
    constructor
    · intro x y hxy
      have h := congrArg (τ g⁻¹) hxy
      simpa only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul,
        inv_mul_cancel g, map_one, Module.End.one_apply] using h
    · intro y
      refine ⟨τ g⁻¹ y, ?_⟩
      simpa only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul,
        mul_inv_cancel g, map_one, Module.End.one_apply]
  exact LinearMap.trace_eq_one_add_det_of_multiplicative_constant_filtration
    hW (τ g) hbij N (hquot g) (hsub g)

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
