/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

import FLT.DedekindDomain.AdicValuation
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

/-- The rational Chebotarev density theorem in the form used by the FLT reduction: deleting
finitely many primes and taking all conjugates of the remaining arithmetic Frobenius elements
still gives a dense subset of the absolute Galois group. -/
theorem dense_rationalFrobeniusConjugates
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : ℕ) :
    Dense (rationalFrobeniusConjugates S p) := by
  sorry

end Field.AbsoluteGaloisGroup
