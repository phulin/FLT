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

end FreyCurve
