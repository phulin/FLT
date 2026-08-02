/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import CebotarevDensity.Main

import FLT.DedekindDomain.AdicValuation
import FLT.Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Chebotarev density for rational arithmetic Frobenius elements

This file records the precise specialization of Chebotarev density needed by the Frey-curve
reduction.  The set allows a finite collection of prime ideals and the residue characteristics
`p` and `3` to be removed, and includes every conjugate of each remaining chosen arithmetic
Frobenius element.
-/

@[expose] public section

open IsDedekindDomain NumberField

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation "Frob" => Field.AbsoluteGaloisGroup.globalAdicArithFrob

namespace IsArithFrobAt

/-- A Frobenius equality for an integral element, coerced into the ambient field. -/
lemma apply_of_pow_eq_one_integralClosure_coe
    {R K G : Type*} [CommRing R] [Field K] [Algebra R K]
    [Group G] [MulSemiringAction G K] [SMulCommClass G R K]
    {Q : Ideal (IntegralClosure R K)} {s : G}
    (H : IsArithFrobAt R s Q) {z : IntegralClosure R K} {m : ℕ}
    (hz : z ^ m = 1) (hm : (m : IntegralClosure R K) ∉ Q) :
    s • z.1 = z.1 ^ Nat.card (R ⧸ Q.under R) := by
  exact congrArg Subtype.val (H.apply_of_pow_eq_one hz hm)

end IsArithFrobAt

namespace Field.AbsoluteGaloisGroup

attribute [local instance 100000] IntermediateField.algebra'

/-- Membership in the rational height-one prime associated to `q` is divisibility by `q`. -/
lemma mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal_iff_dvd
    {p q : ℕ} (hq : q.Prime) :
    (p : NumberField.RingOfIntegers ℚ) ∈
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal ↔ q ∣ p := by
  simp only [Nat.Prime.toHeightOneSpectrumRingOfIntegersRat, RingEquiv.heightOneSpectrum,
    RingEquiv.symm_symm, Nat.Prime.toHeightOneSpectrumInt, Equiv.coe_fn_mk,
    RingEquiv.heightOneSpectrumComap, Ideal.mem_comap, map_natCast,
    Ideal.mem_span_singleton]
  exact Int.ofNat_dvd

/-- The residue field at the height-one prime of `𝒪 ℚ` associated to `q` has cardinality
`q`. -/
lemma card_quotient_toHeightOneSpectrumRingOfIntegersRat {q : ℕ} (hq : q.Prime) :
    Nat.card (NumberField.RingOfIntegers ℚ ⧸
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) = q := by
  let e := Ideal.quotientEquiv
    hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal
    (Ideal.span {(q : ℤ)}) Rat.ringOfIntegersEquiv (by
      change Ideal.span {(q : ℤ)} = Ideal.map Rat.ringOfIntegersEquiv
        (Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(q : ℤ)}))
      rw [Ideal.map_comap_of_surjective Rat.ringOfIntegersEquiv
        Rat.ringOfIntegersEquiv.surjective])
  exact (Nat.card_congr e.toEquiv).trans (Int.card_ideal_quot q)

/-- The residue field cardinality used in the local Frobenius definition at a rational prime
`q` is `q`. -/
lemma rationalFrobenius_residueCard {q : ℕ} (hq : q.Prime) :
    let w := hq.toHeightOneSpectrumRingOfIntegersRat
    let O := w.adicCompletionIntegers ℚ
    let Q := IsLocalRing.maximalIdeal
      (IntegralClosure O (AlgebraicClosure (w.adicCompletion ℚ)))
    Nat.card (O ⧸ Q.under O) = q := by
  dsimp only
  rw [Ideal.under_def, IsLocalRing.maximalIdeal_comap]
  exact (Nat.card_congr
    (IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      ℚ hq.toHeightOneSpectrumRingOfIntegersRat).toEquiv).symm.trans
        (card_quotient_toHeightOneSpectrumRingOfIntegersRat hq)

/-- If the rational prime `p` is distinct from the place `q`, none of its powers lies in the
maximal ideal used to define the local Frobenius at `q`. -/
lemma rationalFrobenius_primePow_not_mem {p q n : ℕ} (hq : q.Prime)
    (hpw : (p : NumberField.RingOfIntegers ℚ) ∉
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) :
    let w := hq.toHeightOneSpectrumRingOfIntegersRat
    let O := w.adicCompletionIntegers ℚ
    let Q := IsLocalRing.maximalIdeal
      (IntegralClosure O (AlgebraicClosure (w.adicCompletion ℚ)))
    (p ^ n : IntegralClosure O (AlgebraicClosure (w.adicCompletion ℚ))) ∉ Q := by
  dsimp only
  let w := hq.toHeightOneSpectrumRingOfIntegersRat
  let O := w.adicCompletionIntegers ℚ
  let S := IntegralClosure O (AlgebraicClosure (w.adicCompletion ℚ))
  let Q := IsLocalRing.maximalIdeal S
  have hpO : (p : O) ∉ IsLocalRing.maximalIdeal O := by
    intro hpO
    apply hpw
    change (p : NumberField.RingOfIntegers ℚ) ∈ w.asIdeal
    rw [Ideal.LiesOver.over (P := w.completionIdeal ℚ) (p := w.asIdeal),
      Ideal.mem_under]
    simpa using hpO
  have hpS : (p : S) ∉ Q := by
    intro hpS
    apply hpO
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap O S)]
    simpa only [Ideal.mem_comap, map_natCast] using hpS
  exact fun h ↦ hpS ((IsLocalRing.maximalIdeal.isMaximal S).isPrime.mem_of_pow_mem n h)

set_option maxHeartbeats 800000 in
-- The integral-closure and algebraic-closure coercions require unusually deep normalization.
/-- The local arithmetic Frobenius at `q` acts as the `q`-th power map on the image of every
`p`-power root of unity when `p` is distinct from `q`. -/
lemma adicArithFrob_map_rootOfUnity {p q n : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpw : (p : NumberField.RingOfIntegers ℚ) ∉
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
    (t : (AlgebraicClosure ℚ)ˣ) (ht : t ∈ rootsOfUnity (p ^ n) (AlgebraicClosure ℚ)) :
    adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat
      (AlgebraicClosure.map (adicEmbedding hq.toHeightOneSpectrumRingOfIntegersRat)
        (t : AlgebraicClosure ℚ)) =
      (AlgebraicClosure.map (adicEmbedding hq.toHeightOneSpectrumRingOfIntegersRat)
        (t : AlgebraicClosure ℚ)) ^ q := by
  let w := hq.toHeightOneSpectrumRingOfIntegersRat
  change adicArithFrob w
      (AlgebraicClosure.map (adicEmbedding w) (t : AlgebraicClosure ℚ)) =
      (AlgebraicClosure.map (adicEmbedding w) (t : AlgebraicClosure ℚ)) ^ q
  let O := w.adicCompletionIntegers ℚ
  let L := AlgebraicClosure (w.adicCompletion ℚ)
  let S := IntegralClosure O L
  have ht' : (t : AlgebraicClosure ℚ) ^ (p ^ n) = 1 :=
    (mem_rootsOfUnity' (p ^ n) t).mp ht
  have hmap : (AlgebraicClosure.map (adicEmbedding w)
      (t : AlgebraicClosure ℚ)) ^ (p ^ n) = 1 := by
    simpa only [map_pow, map_one] using
      congrArg (AlgebraicClosure.map (adicEmbedding w)) ht'
  have hζint : IsIntegral O
      (AlgebraicClosure.map (adicEmbedding w) (t : AlgebraicClosure ℚ)) := by
    apply IsIntegral.of_pow (n := p ^ n) (Nat.pow_pos (Fact.out : p.Prime).pos)
    rw [hmap]
    exact (isIntegral_one : IsIntegral O (1 : L))
  let ζ : S := ⟨AlgebraicClosure.map (adicEmbedding w) t, hζint⟩
  have hζpow : ζ ^ (p ^ n) = 1 := by
    apply Subtype.ext
    change (AlgebraicClosure.map (adicEmbedding w)
      (t : AlgebraicClosure ℚ)) ^ (p ^ n) = (1 : L)
    exact hmap
  have hF :=
    IsArithFrobAt.apply_of_pow_eq_one_integralClosure_coe
      (isArithFrobAt_adicArithFrob (v := w)) hζpow
      (by simpa only [Nat.cast_pow] using
        (rationalFrobenius_primePow_not_mem (n := n) hq hpw))
  simp only [AlgEquiv.smul_def] at hF
  change adicArithFrob w
      (AlgebraicClosure.map (adicEmbedding w) (t : AlgebraicClosure ℚ)) =
      (AlgebraicClosure.map (adicEmbedding w) (t : AlgebraicClosure ℚ)) ^
        Nat.card (O ⧸ (IsLocalRing.maximalIdeal S).under O) at hF
  rw [hF, rationalFrobenius_residueCard hq]

set_option maxHeartbeats 800000 in
-- Elaborating the fixed local algebraic-closure embedding requires deep normalization.
/-- The chosen global arithmetic Frobenius at `q` acts as the `q`-th power map on every
`p`-power root of unity when `p` is distinct from `q`. -/
lemma globalAdicArithFrob_apply_rootOfUnity {p q n : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpw : (p : NumberField.RingOfIntegers ℚ) ∉
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
    (t : (AlgebraicClosure ℚ)ˣ) (ht : t ∈ rootsOfUnity (p ^ n) (AlgebraicClosure ℚ)) :
    globalAdicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat t = t ^ q := by
  refine globalAdicArithFrob_eq_of_map_eq
    (K := ℚ) (v := hq.toHeightOneSpectrumRingOfIntegersRat)
      (x := (t : AlgebraicClosure ℚ)) (y := (t : AlgebraicClosure ℚ) ^ q) ?_
  rw [map_pow]
  exact adicArithFrob_map_rootOfUnity hq hpw t ht

/-- The `p`-adic cyclotomic character of arithmetic Frobenius at a rational prime `q ≠ p`
is `q`. -/
lemma cyclotomicCharacter_globalAdicArithFrob {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hpw : (p : NumberField.RingOfIntegers ℚ) ∉
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) :
    (cyclotomicCharacter (AlgebraicClosure ℚ) p
      (globalAdicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat).toRingEquiv).val =
      (q : ℤ_[p]) := by
  refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
  rw [cyclotomicCharacter.toZModPow]
  apply Eq.symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  change globalAdicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat
    (t : AlgebraicClosure ℚ) = _
  rw [globalAdicArithFrob_apply_rootOfUnity hq hpw t ht]
  simp only [map_natCast]
  change (t : AlgebraicClosure ℚ) ^ q =
    (t : AlgebraicClosure ℚ) ^ ((q : ZMod (p ^ n)).val)
  rw [ZMod.val_natCast]
  nth_rw 1 [← Nat.mod_add_div q (p ^ n)]
  have ht' : (t : AlgebraicClosure ℚ) ^ (p ^ n) = 1 :=
    (mem_rootsOfUnity' (p ^ n) t).mp ht
  rw [pow_add, pow_mul, ht', one_pow, mul_one]

/-- Conjugates of the chosen global arithmetic Frobenius elements at rational primes at least
five, after removing a finite set and the primes above `p` and `3`. -/
noncomputable def rationalFrobeniusConjugates
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : ℕ) : Set (Γ ℚ) :=
  {g | ∃ (q : ℕ) (hq : q.Prime), 5 ≤ q ∧
    let w := hq.toHeightOneSpectrumRingOfIntegersRat
    w ∉ S ∧ (p : 𝓞 ℚ) ∉ w.asIdeal ∧ (3 : 𝓞 ℚ) ∉ w.asIdeal ∧ IsConj (Frob w) g}

/-- An infinite set of prime ideals of `𝓞 ℚ` contains a nonzero prime outside the ideals
underlying any prescribed finite set of rational places. -/
lemma exists_heightOneSpectrum_not_mem_of_infinite
    (S : Set (Ideal (𝓞 ℚ))) (hS : S.Infinite)
    (hprime : ∀ 𝔭 ∈ S, 𝔭.IsPrime)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ w : HeightOneSpectrum (𝓞 ℚ), w ∉ T ∧ w.asIdeal ∈ S := by
  classical
  let U : Finset (Ideal (𝓞 ℚ)) := insert ⊥ (T.image fun w ↦ w.asIdeal)
  have hnot : ¬S ⊆ (U : Set (Ideal (𝓞 ℚ))) := by
    intro hsub
    exact hS (U.finite_toSet.subset hsub)
  obtain ⟨𝔭, h𝔭S, h𝔭U⟩ := Set.not_subset.mp hnot
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro h𝔭
    apply h𝔭U
    exact Finset.mem_insert.mpr (.inl h𝔭)
  let w : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨𝔭, hprime 𝔭 h𝔭S, h𝔭ne⟩
  have hwT : w ∉ T := by
    intro hw
    apply h𝔭U
    apply Finset.mem_insert.mpr
    right
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  exact ⟨w, hwT, h𝔭S⟩

/-- The rational-prime form of `exists_heightOneSpectrum_not_mem_of_infinite`. -/
lemma exists_rationalPrime_not_mem_of_infinite
    (S : Set (Ideal (𝓞 ℚ))) (hS : S.Infinite)
    (hprime : ∀ 𝔭 ∈ S, 𝔭.IsPrime)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (q : ℕ) (hq : q.Prime),
      let w := hq.toHeightOneSpectrumRingOfIntegersRat
      w ∉ T ∧ w.asIdeal ∈ S := by
  obtain ⟨w, hwT, hwS⟩ :=
    exists_heightOneSpectrum_not_mem_of_infinite S hS hprime T
  let q : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv w
  have hwq : q.2.toHeightOneSpectrumRingOfIntegersRat = w := by
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    rw [Rat.HeightOneSpectrum.primesEquiv_toHeightOneSpectrumRingOfIntegersRat]
    rfl
  exact ⟨q.1, q.2, by simpa only [hwq] using And.intro hwT hwS⟩

/-- Weak Chebotarev for a finite normal subextension of `AlgebraicClosure ℚ`: outside any
finite set of rational places, some arithmetic Frobenius has a conjugate agreeing with a
prescribed absolute Galois element on the subextension. -/
theorem exists_restrictNormal_rationalFrobenius_isConj_of_not_mem
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ E] [Normal ℚ E] (τ : E ≃ₐ[ℚ] E) :
    ∃ (q : ℕ) (hq : q.Prime),
      let w := hq.toHeightOneSpectrumRingOfIntegersRat
      w ∉ T ∧ IsConj ((Frob w).restrictNormal E) τ := by
  sorry

/-- Lift finite-level Chebotarev from `Gal(E/ℚ)` to the absolute Galois group.  The
conjugating automorphism of `E` extends to `AlgebraicClosure ℚ` because both extensions are
normal. -/
theorem exists_rationalFrobeniusConjugate_agreeOn_of_not_mem
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : FiniteDimensional ℚ E) (hEnormal : Normal ℚ E) (σ : Γ ℚ) :
    ∃ (q : ℕ) (hq : q.Prime),
      let w := hq.toHeightOneSpectrumRingOfIntegersRat
      w ∉ T ∧ ∃ g : Γ ℚ, IsConj (Frob w) g ∧
        ∀ x : AlgebraicClosure ℚ, x ∈ E → g x = σ x := by
  classical
  letI : FiniteDimensional ℚ E := hE
  letI : Normal ℚ (AlgebraicClosure ℚ) := normal_iff.2 fun x ↦
    ⟨((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral, IsAlgClosed.splits _⟩
  letI : Normal ℚ E := hEnormal
  obtain ⟨q, hq, hwT, hconj⟩ :=
    exists_restrictNormal_rationalFrobenius_isConj_of_not_mem T E
      (σ.restrictNormal E)
  rcases isConj_iff.mp hconj with ⟨cE, hcE⟩
  obtain ⟨c, hc⟩ :=
    AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := E) (E := AlgebraicClosure ℚ) cE
  let c' : Γ ℚ := c
  have hc' : c'.restrictNormal E = cE := hc
  have hcHom : (AlgEquiv.restrictNormalHom E) c' = cE := by
    change c'.restrictNormal E = cE
    exact hc'
  let g : Γ ℚ := c' * Frob hq.toHeightOneSpectrumRingOfIntegersRat * c'⁻¹
  refine ⟨q, hq, hwT, g, isConj_iff.mpr ⟨c', rfl⟩, ?_⟩
  intro x hx
  have hrestrict : g.restrictNormal E = σ.restrictNormal E := by
    change (AlgEquiv.restrictNormalHom E) g = (AlgEquiv.restrictNormalHom E) σ
    rw [show g = c' * Frob hq.toHeightOneSpectrumRingOfIntegersRat * c'⁻¹ by rfl,
      map_mul, map_mul, map_inv, hcHom]
    exact hcE
  have hfix : σ⁻¹ * g ∈ E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker]
    change (AlgEquiv.restrictNormalHom E) (σ⁻¹ * g) = 1
    have hrestrictHom : (AlgEquiv.restrictNormalHom E) g =
        (AlgEquiv.restrictNormalHom E) σ := by
      change g.restrictNormal E = σ.restrictNormal E
      exact hrestrict
    rw [map_mul, map_inv, hrestrictHom]
    simp
  have hfixx := (IntermediateField.mem_fixingSubgroup_iff E (σ⁻¹ * g)).mp hfix x hx
  change σ⁻¹ (g x) = x at hfixx
  calc
    g x = σ (σ⁻¹ (g x)) := (σ.apply_symm_apply (g x)).symm
    _ = σ x := congrArg σ hfixx

/-- A finite-quotient form of rational Chebotarev: every left coset of the fixing subgroup
of a finite normal subextension contains a conjugate of an allowed arithmetic Frobenius.

This is the arithmetic input in the proof of `dense_rationalFrobeniusConjugates`; the passage
from this finite-level statement to density is purely topological. -/
theorem exists_rationalFrobeniusConjugate_mem_leftCoset
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : ℕ) [Fact p.Prime]
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : FiniteDimensional ℚ E) (hEnormal : Normal ℚ E) (σ : Γ ℚ) :
    ∃ g ∈ rationalFrobeniusConjugates S p,
      ∀ x : AlgebraicClosure ℚ, x ∈ E → g x = σ x := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : Nat.Prime 2 := by decide
  have h3 : Nat.Prime 3 := by decide
  let T := insert h2.toHeightOneSpectrumRingOfIntegersRat
    (insert h3.toHeightOneSpectrumRingOfIntegersRat
      (insert hp.toHeightOneSpectrumRingOfIntegersRat S))
  obtain ⟨q, hq, hwT, g, hconj, hg⟩ :=
    exists_rationalFrobeniusConjugate_agreeOn_of_not_mem T E hE hEnormal σ
  let w := hq.toHeightOneSpectrumRingOfIntegersRat
  have hwT' : w ∉ insert h2.toHeightOneSpectrumRingOfIntegersRat
      (insert h3.toHeightOneSpectrumRingOfIntegersRat
        (insert hp.toHeightOneSpectrumRingOfIntegersRat S)) := by
    simpa only [T] using hwT
  have hw2 : w ≠ h2.toHeightOneSpectrumRingOfIntegersRat := by
    intro h
    exact hwT' (Finset.mem_insert.mpr (Or.inl h))
  have hw3 : w ≠ h3.toHeightOneSpectrumRingOfIntegersRat := by
    intro h
    exact hwT' (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h))))
  have hwp : w ≠ hp.toHeightOneSpectrumRingOfIntegersRat := by
    intro h
    exact hwT' (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h))))))
  have hwS : w ∉ S := by
    intro h
    exact hwT' (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr h))))))
  have hq2 : q ≠ 2 := by
    intro h
    apply hw2
    subst q
    rfl
  have hq3 : q ≠ 3 := by
    intro h
    apply hw3
    subst q
    rfl
  have hpw : (p : 𝓞 ℚ) ∉ w.asIdeal := by
    intro h
    have hqp : q ∣ p :=
      (mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal_iff_dvd hq).mp h
    have hqp' : q = p := ((Nat.dvd_prime hp).mp hqp).resolve_left hq.ne_one
    apply hwp
    subst q
    rfl
  have h3w : (3 : 𝓞 ℚ) ∉ w.asIdeal := by
    intro h
    have hq3dvd : q ∣ 3 :=
      (mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal_iff_dvd hq).mp h
    have hq3' : q = 3 := ((Nat.dvd_prime h3).mp hq3dvd).resolve_left hq.ne_one
    exact hq3 hq3'
  refine ⟨g, ?_, hg⟩
  change ∃ (q : ℕ) (hq : q.Prime), 5 ≤ q ∧
    let w := hq.toHeightOneSpectrumRingOfIntegersRat
    w ∉ S ∧ (p : 𝓞 ℚ) ∉ w.asIdeal ∧ (3 : 𝓞 ℚ) ∉ w.asIdeal ∧ IsConj (Frob w) g
  exact ⟨q, hq, hq.five_le_of_ne_two_of_ne_three hq2 hq3, hwS, hpw, h3w, hconj⟩

set_option backward.isDefEq.respectTransparency false in
/-- Regard an element of mathlib's wrapped absolute Galois group as the underlying algebra
automorphism used to define the Krull topology. -/
private def toKrullAutomorphism (σ : Γ ℚ) :
    AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := by
  exact σ

/-- In an absolute Galois group, a set meeting every left coset coming from a finite normal
subextension is dense. -/
theorem dense_of_intersects_finiteNormal_leftCosets
    (D : Set (Γ ℚ))
    (hD : ∀ (E : IntermediateField ℚ (AlgebraicClosure ℚ)),
      FiniteDimensional ℚ E → Normal ℚ E → ∀ σ : Γ ℚ,
        ∃ g ∈ D, ∀ x : AlgebraicClosure ℚ, x ∈ E → g x = σ x) :
    Dense D := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨σ, hσU⟩
  obtain ⟨V, hV, hVU⟩ :=
    ((galGroupBasis ℚ (AlgebraicClosure ℚ)).nhds_hasBasis σ).mem_iff.mp
      (hU.mem_nhds hσU)
  rcases hV with ⟨-, ⟨E, hE, rfl⟩, rfl⟩
  let _ : FiniteDimensional ℚ E := hE
  let E' := IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)
  have hE' : FiniteDimensional ℚ E' :=
    normalClosure.is_finiteDimensional ℚ E (AlgebraicClosure ℚ)
  let _ : Normal ℚ (AlgebraicClosure ℚ) := normal_iff.2 fun x ↦
    ⟨((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral, IsAlgClosed.splits _⟩
  have hE'normal : Normal ℚ E' :=
    normalClosure.normal ℚ E (AlgebraicClosure ℚ)
  obtain ⟨g, hgD, hg⟩ := hD E' hE' hE'normal σ
  refine ⟨g, hVU ?_, hgD⟩
  refine ⟨toKrullAutomorphism (σ⁻¹ * g), ?_, ?_⟩
  · apply (IntermediateField.mem_fixingSubgroup_iff E _).2
    intro x hx
    change σ⁻¹ (g x) = x
    rw [hg x (E.le_normalClosure hx)]
    exact σ.symm_apply_apply x
  change toKrullAutomorphism σ * toKrullAutomorphism (σ⁻¹ * g) =
    toKrullAutomorphism g
  apply AlgEquiv.ext fun x ↦ ?_
  change σ (σ⁻¹ (g x)) = g x
  exact σ.apply_symm_apply (g x)

/-- The rational Chebotarev density theorem in the form used by the FLT reduction: deleting
finitely many primes and taking all conjugates of the remaining arithmetic Frobenius elements
still gives a dense subset of the absolute Galois group. -/
theorem dense_rationalFrobeniusConjugates
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : ℕ) [Fact p.Prime] :
    Dense (rationalFrobeniusConjugates S p) := by
  exact dense_of_intersects_finiteNormal_leftCosets _ fun E hE hEnormal σ ↦
    exists_rationalFrobeniusConjugate_mem_leftCoset S p E hE hEnormal σ

end Field.AbsoluteGaloisGroup
