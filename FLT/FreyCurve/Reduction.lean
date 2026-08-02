/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Basic
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.Mathlib.NumberTheory.Padics.PadicNumbers

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

end FreyCurve
