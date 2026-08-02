/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Basic
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.Mathlib.NumberTheory.Padics.PadicNumbers
public import FLT.Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Reduction of the Frey curve

This file proves the odd-prime semistability calculations for the Frey curve. At an odd prime `q`,
the integral Frey equation has good reduction when `q ∤ abc`, and multiplicative reduction when
`q ∣ abc`.
-/

@[expose] public section

namespace FreyCurve

open FreyPackage WeierstrassCurve WithZero

/-- In the normalization of a Frey package, the even parameter makes `abc` divisible by `2`. -/
lemma two_dvd_abc (P : FreyPackage) : (2 : ℤ) ∣ P.a * P.b * P.c := by
  have h2b : (2 : ℤ) ∣ P.b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2b P.a) P.c

/-- The integral Frey equation supplies an integral model over every intermediate ring between
`ℤ` and `ℚ`. -/
instance freyCurve_isIntegral (P : FreyPackage) (R : Type*) [CommRing R]
    [Algebra R ℚ] [IsScalarTower ℤ R ℚ] : IsIntegral R P.freyCurve where
  integral := ⟨P.freyCurveInt⁄R, by
    rw [← FreyCurve.map P]
    exact (P.freyCurveInt.map_baseChange (IsScalarTower.toAlgHom ℤ R ℚ)).symm⟩

/-- Away from `2`, the discriminant of the Frey curve is a unit at every prime not dividing
`abc`. -/
lemma padicValuation_Δ_eq_one_of_not_dvd (P : FreyPackage) {q : ℕ}
    (hqPrime : q.Prime) (hqodd : 2 < q) (hqgood : ¬(q : ℤ) ∣ P.a * P.b * P.c) :
    let _ : Fact q.Prime := ⟨hqPrime⟩
    Rat.padicValuation q P.freyCurve.Δ = 1 := by
  let _ : Fact q.Prime := ⟨hqPrime⟩
  have hval : padicValRat q P.freyCurve.Δ = 0 := by
    rw [padicValRat_Δ P hqPrime hqodd, padicValInt.eq_zero_of_not_dvd hqgood]
    norm_num
  simp [Rat.padicValuation, P.freyCurve.isUnit_Δ.ne_zero, hval]

/-- The invariant `c₄` of the Frey curve is a unit at every prime dividing `abc`. -/
lemma padicValuation_c₄_eq_one_of_dvd (P : FreyPackage) {q : ℕ}
    (hqPrime : q.Prime) (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let _ : Fact q.Prime := ⟨hqPrime⟩
    Rat.padicValuation q P.freyCurve.c₄ = 1 := by
  let _ : Fact q.Prime := ⟨hqPrime⟩
  have hc₄ne : P.freyCurve.c₄ ≠ 0 := by
    rw [FreyCurve.c₄']
    norm_cast
    intro h
    apply bad_prime_not_dvd_c₄ P hqPrime hqbad
    rw [h]
    exact dvd_zero _
  simp [Rat.padicValuation, hc₄ne, padicValRat_c₄_eq_zero_of_bad_prime P hqPrime hqbad]

/-- Away from `2`, the discriminant of the Frey curve lies in the maximal ideal at every prime
dividing `abc`. -/
lemma padicValuation_Δ_lt_one_of_dvd (P : FreyPackage) {q : ℕ}
    (hqPrime : q.Prime) (hqodd : 2 < q) (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let _ : Fact q.Prime := ⟨hqPrime⟩
    Rat.padicValuation q P.freyCurve.Δ < 1 := by
  let _ : Fact q.Prime := ⟨hqPrime⟩
  have habc0 : P.a * P.b * P.c ≠ 0 := mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
  have hvalpos : 0 < padicValInt q (P.a * P.b * P.c) := by
    apply Nat.pos_of_ne_zero
    rw [ne_eq, padicValInt.eq_zero_iff]
    push Not
    exact ⟨hqPrime.ne_one, habc0, hqbad⟩
  have hΔvalpos : 0 < padicValRat q P.freyCurve.Δ := by
    rw [padicValRat_Δ P hqPrime hqodd]
    have hpz : (0 : ℤ) < P.p := by exact_mod_cast P.hppos
    have hvz : (0 : ℤ) < padicValInt q (P.a * P.b * P.c) := by exact_mod_cast hvalpos
    exact mul_pos (mul_pos (by norm_num) hpz) hvz
  change (if P.freyCurve.Δ = 0 then 0 else exp (-padicValRat q P.freyCurve.Δ)) < 1
  simp only [P.freyCurve.isUnit_Δ.ne_zero, ↓reduceIte, ← exp_zero, exp_lt_exp]
  omega

/-- At `2`, the denominator in the normalized Frey discriminant contributes exactly eight
to the additive valuation. -/
lemma padicValRat_Δ_at_two (P : FreyPackage) :
    padicValRat 2 P.freyCurve.Δ =
      (2 * P.p : ℤ) * (padicValInt 2 (P.a * P.b * P.c) : ℤ) - 8 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [FreyCurve.Δ]
  rw [padicValRat.div
    (pow_ne_zero _ (by norm_cast; exact mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0))
    (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))]
  rw [padicValRat.pow, padicValRat.pow]
  have habcCast : (P.a * P.b * P.c : ℚ) = ((P.a * P.b * P.c : ℤ) : ℚ) := by
    norm_num
  rw [habcCast, padicValRat.of_int]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by omega)
  rw [htwo]
  norm_num

/-- The normalized integral Frey equation has nonunit discriminant at `2`. -/
lemma padicValuation_Δ_lt_one_at_two (P : FreyPackage) :
    let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
    Rat.padicValuation 2 P.freyCurve.Δ < 1 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h2abc : (2 : ℤ) ∣ P.a * P.b * P.c := two_dvd_abc P
  have habc0 : P.a * P.b * P.c ≠ 0 := mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
  have hvalpos : 0 < padicValInt 2 (P.a * P.b * P.c) := by
    rw [← Nat.ne_zero_iff_zero_lt]
    intro hzero
    rw [padicValInt.eq_zero_iff] at hzero
    rcases hzero with h | h | h
    · norm_num at h
    · exact habc0 h
    · exact h h2abc
  have hΔvalpos : 0 < padicValRat 2 P.freyCurve.Δ := by
    rw [padicValRat_Δ_at_two]
    have hp5 := P.hp5
    have hvz : (0 : ℤ) < padicValInt 2 (P.a * P.b * P.c) := by exact_mod_cast hvalpos
    have hp5z : (5 : ℤ) ≤ P.p := by exact_mod_cast hp5
    nlinarith
  change (if P.freyCurve.Δ = 0 then 0 else exp (-padicValRat 2 P.freyCurve.Δ)) < 1
  simp only [P.freyCurve.isUnit_Δ.ne_zero, ↓reduceIte, ← exp_zero, exp_lt_exp]
  omega

/-- The Frey curve has good reduction at every odd prime not dividing `abc`. -/
theorem hasGoodReduction_of_not_dvd_abc (P : FreyPackage) {q : ℕ}
    (hqPrime : q.Prime) (hqodd : 2 < q) (hqgood : ¬(q : ℤ) ∣ P.a * P.b * P.c) :
    let _ : Fact q.Prime := ⟨hqPrime⟩
    P.freyCurve.HasGoodReduction (Rat.padicValuation q).valuationSubring := by
  let _ : Fact q.Prime := ⟨hqPrime⟩
  have hΔ := Rat.adicValuation_eq_one_of_padicValuation_eq_one
    (padicValuation_Δ_eq_one_of_not_dvd P hqPrime hqodd hqgood)
  let _ : IsMinimal (Rat.padicValuation q).valuationSubring P.freyCurve :=
    isMinimal_of_valuation_Δ_eq_one _ _ hΔ
  exact { goodReduction := hΔ }

/-- The Frey curve has multiplicative reduction at every odd prime dividing `abc`. -/
theorem hasMultiplicativeReduction_of_dvd_abc (P : FreyPackage) {q : ℕ}
    (hqPrime : q.Prime) (hqodd : 2 < q) (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let _ : Fact q.Prime := ⟨hqPrime⟩
    P.freyCurve.HasMultiplicativeReduction (Rat.padicValuation q).valuationSubring := by
  let _ : Fact q.Prime := ⟨hqPrime⟩
  have hc₄ := Rat.adicValuation_eq_one_of_padicValuation_eq_one
    (padicValuation_c₄_eq_one_of_dvd P hqPrime hqbad)
  have hΔ := Rat.adicValuation_lt_one_of_padicValuation_lt_one
    (padicValuation_Δ_lt_one_of_dvd P hqPrime hqodd hqbad)
  let _ : IsMinimal (Rat.padicValuation q).valuationSubring P.freyCurve :=
    isMinimal_of_valuation_c₄_eq_one _ _ hc₄
  exact { badReduction := hΔ, multiplicativeReduction := hc₄ }

/-- The normalized Frey curve has multiplicative reduction at `2`. -/
theorem hasMultiplicativeReduction_at_two (P : FreyPackage) :
    let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
    P.freyCurve.HasMultiplicativeReduction
      (Rat.padicValuation 2).valuationSubring := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hc₄ := Rat.adicValuation_eq_one_of_padicValuation_eq_one
    (padicValuation_c₄_eq_one_of_dvd P (by decide) (two_dvd_abc P))
  have hΔ := Rat.adicValuation_lt_one_of_padicValuation_lt_one
    (padicValuation_Δ_lt_one_at_two P)
  let _ : IsMinimal (Rat.padicValuation 2).valuationSubring P.freyCurve :=
    isMinimal_of_valuation_c₄_eq_one _ _ hc₄
  exact { badReduction := hΔ, multiplicativeReduction := hc₄ }

/-! ### Reduction over completed rational local fields -/

/-- The integral Frey equation gives an integral model after base change to the completion of
`ℚ` at a rational prime. -/
theorem freyCurve_baseChange_isIntegral (P : FreyPackage) {q : ℕ} (hq : q.Prime) :
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    IsIntegral (v.adicCompletionIntegers ℚ)
      (P.freyCurve.baseChange (v.adicCompletion ℚ)) := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  refine ⟨P.freyCurveInt⁄(v.adicCompletionIntegers ℚ), ?_⟩
  rw [← FreyCurve.map P]
  exact (P.freyCurveInt.map_baseChange
    (IsScalarTower.toAlgHom ℤ (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ))).symm

/-- At an odd prime not dividing `abc`, the Frey curve has good reduction over the completed
local field. -/
theorem hasGoodReduction_at_completion_of_not_dvd_abc (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hqodd : 2 < q) (hqgood : ¬(q : ℤ) ∣ P.a * P.b * P.c) :
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    (P.freyCurve.baseChange (v.adicCompletion ℚ)).HasGoodReduction
      (v.adicCompletionIntegers ℚ) := by
  let _ : Fact q.Prime := ⟨hq⟩
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let E := P.freyCurve.baseChange K
  let _ : E.IsElliptic := inferInstance
  let _ : E.IsIntegral R := freyCurve_baseChange_isIntegral P hq
  have hΔcanonical : Valued.v E.Δ = 1 := by
    rw [show E.Δ = algebraMap ℚ K P.freyCurve.Δ from P.freyCurve.map_Δ _]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Rat.HeightOneSpectrum.valuation_apply_eq_padicValuation,
      Rat.HeightOneSpectrum.primesEquiv_toHeightOneSpectrumRingOfIntegersRat hq]
    exact padicValuation_Δ_eq_one_of_not_dvd P hq hqodd hqgood
  have hΔadic :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.Δ = 1 := by
    rw [← integralModel_Δ_eq R E] at hΔcanonical ⊢
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.adicValuation_eq_one_of_valued_eq_one
    exact hΔcanonical
  let _ : E.IsMinimal R := isMinimal_of_valuation_Δ_eq_one R E hΔadic
  exact { goodReduction := hΔadic }

/-- At an odd prime dividing `abc`, the Frey curve has multiplicative reduction over the
completed local field. -/
theorem hasMultiplicativeReduction_at_completion_of_dvd_abc (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hqodd : 2 < q) (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    (P.freyCurve.baseChange (v.adicCompletion ℚ)).HasMultiplicativeReduction
      (v.adicCompletionIntegers ℚ) := by
  let _ : Fact q.Prime := ⟨hq⟩
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let E := P.freyCurve.baseChange K
  let _ : E.IsElliptic := inferInstance
  let _ : E.IsIntegral R := freyCurve_baseChange_isIntegral P hq
  have hc₄canonical : Valued.v E.c₄ = 1 := by
    rw [show E.c₄ = algebraMap ℚ K P.freyCurve.c₄ from P.freyCurve.map_c₄ _]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Rat.HeightOneSpectrum.valuation_apply_eq_padicValuation,
      Rat.HeightOneSpectrum.primesEquiv_toHeightOneSpectrumRingOfIntegersRat hq]
    exact padicValuation_c₄_eq_one_of_dvd P hq hqbad
  have hΔcanonical : Valued.v E.Δ < 1 := by
    rw [show E.Δ = algebraMap ℚ K P.freyCurve.Δ from P.freyCurve.map_Δ _]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Rat.HeightOneSpectrum.valuation_apply_eq_padicValuation,
      Rat.HeightOneSpectrum.primesEquiv_toHeightOneSpectrumRingOfIntegersRat hq]
    exact padicValuation_Δ_lt_one_of_dvd P hq hqodd hqbad
  have hc₄adic :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.c₄ = 1 := by
    rw [← integralModel_c₄_eq R E] at hc₄canonical ⊢
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.adicValuation_eq_one_of_valued_eq_one
    exact hc₄canonical
  have hΔadic :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.Δ < 1 := by
    rw [← integralModel_Δ_eq R E] at hΔcanonical ⊢
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.adicValuation_lt_one_of_valued_lt_one
    exact hΔcanonical
  let _ : E.IsMinimal R := isMinimal_of_valuation_c₄_eq_one R E hc₄adic
  exact { badReduction := hΔadic, multiplicativeReduction := hc₄adic }

/-- The Frey curve has multiplicative reduction over the completed rational local field at `2`. -/
theorem hasMultiplicativeReduction_at_two_completion (P : FreyPackage) :
    let hq : Nat.Prime 2 := by decide
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    (P.freyCurve.baseChange (v.adicCompletion ℚ)).HasMultiplicativeReduction
      (v.adicCompletionIntegers ℚ) := by
  let hq : Nat.Prime 2 := by decide
  let _ : Fact (Nat.Prime 2) := ⟨hq⟩
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let E := P.freyCurve.baseChange K
  let _ : E.IsElliptic := inferInstance
  let _ : E.IsIntegral R := freyCurve_baseChange_isIntegral P hq
  have hc₄canonical : Valued.v E.c₄ = 1 := by
    rw [show E.c₄ = algebraMap ℚ K P.freyCurve.c₄ from P.freyCurve.map_c₄ _]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Rat.HeightOneSpectrum.valuation_apply_eq_padicValuation,
      Rat.HeightOneSpectrum.primesEquiv_toHeightOneSpectrumRingOfIntegersRat hq]
    exact padicValuation_c₄_eq_one_of_dvd P hq (two_dvd_abc P)
  have hΔcanonical : Valued.v E.Δ < 1 := by
    rw [show E.Δ = algebraMap ℚ K P.freyCurve.Δ from P.freyCurve.map_Δ _]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Rat.HeightOneSpectrum.valuation_apply_eq_padicValuation,
      Rat.HeightOneSpectrum.primesEquiv_toHeightOneSpectrumRingOfIntegersRat hq]
    exact padicValuation_Δ_lt_one_at_two P
  have hc₄adic :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.c₄ = 1 := by
    rw [← integralModel_c₄_eq R E] at hc₄canonical ⊢
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.adicValuation_eq_one_of_valued_eq_one
    exact hc₄canonical
  have hΔadic :
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.Δ < 1 := by
    rw [← integralModel_Δ_eq R E] at hΔcanonical ⊢
    apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.adicValuation_lt_one_of_valued_lt_one
    exact hΔcanonical
  let _ : E.IsMinimal R := isMinimal_of_valuation_c₄_eq_one R E hc₄adic
  exact { badReduction := hΔadic, multiplicativeReduction := hc₄adic }

end FreyCurve
