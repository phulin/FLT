/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Reduction
public import FLT.DedekindDomain.AdicValuation
public import FLT.KnownIn1980s.EllipticCurves.LocalInertia
public import FLT.KnownIn1980s.EllipticCurves.TateCurve
public import FLT.NumberField.Completion.ValuativeRel

/-!
# Tate parameters at bad primes of the Frey curve

This file carries out the local Kummer calculation from the Frey-curve blueprint.  It relates
the valuation of the Tate parameter over the completed local field to the rational `q`-adic
valuation of the Frey curve's `j`-invariant, then uses the resulting divisible uniformizer
exponent to construct inertia-fixed roots of the Tate parameter.
-/

@[expose] public section

open IsDedekindDomain NumberField WithZero
open scoped Multiplicative

namespace FreyCurve

noncomputable section

/-- Split multiplicative reduction over the concrete integer ring of a completed number
field is the same reduction structure required by the canonical `ValuativeRel` API. -/
theorem hasSplitMultiplicativeReduction_valuativeRel_of_adicCompletion
    {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (E : WeierstrassCurve (v.adicCompletion F)) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction (v.adicCompletionIntegers F)] :
    E.HasSplitMultiplicativeReduction
      (ValuativeRel.valuation (v.adicCompletion F)).integer := by
  let B : Subring (v.adicCompletion F) := (v.adicCompletionIntegers F).toSubring
  have hB : (ValuativeRel.valuation (v.adicCompletion F)).integer = B := by
    exact HeightOneSpectrum.adicCompletion.integer_eq_adicCompletionIntegers v
  let e :
      (ValuativeRel.valuation (v.adicCompletion F)).integer ≃+* B :=
    RingEquiv.subringCongr hB
  let _ : IsDiscreteValuationRing B :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hBint :
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Integers B := by
    constructor
    · exact Subtype.coe_injective
    · exact fun x ↦ x.2
    · exact fun {_} hx ↦ ⟨⟨_, hx⟩, rfl⟩
  let _ : IsFractionRing B (v.adicCompletion F) := hBint.isFractionRing
  have hsplitB : E.HasSplitMultiplicativeReduction B := by
    exact (inferInstance : E.HasSplitMultiplicativeReduction (v.adicCompletionIntegers F))
  convert hsplitB using 1
  · exact congrArg (fun A : Subring (v.adicCompletion F) ↦ ↥A) hB
  · have hs := congrArg (fun A : Subring (v.adicCompletion F) ↦
        (⟨A, A.toCommRing⟩ : Σ A : Subring (v.adicCompletion F), CommRing (↥A))) hB
    exact (Sigma.mk.inj_iff.mp hs).2
  · have hs := congrArg (fun A : Subring (v.adicCompletion F) ↦
        (⟨A, inferInstanceAs (Algebra (↥A) (v.adicCompletion F))⟩ :
          Σ A : Subring (v.adicCompletion F), Algebra (↥A) (v.adicCompletion F))) hB
    exact (Sigma.mk.inj_iff.mp hs).2

/-- For split multiplicative reduction at `q`, the multiplicative valuation of the Tate
parameter is the exponential of the additive `q`-adic valuation of the rational
`j`-invariant.  The sign changes because the Tate parameter has the valuation of `j⁻¹`. -/
theorem valued_tateParameter_at_bad_prime (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (_hqodd : 2 < q) (_hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    let _ : Field (v.adicCompletion ℚ) :=
      HeightOneSpectrum.adicCompletion.instField ℚ v
    let _ : CommRing (v.adicCompletion ℚ) :=
      (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
    let _ : Algebra ℚ (v.adicCompletion ℚ) :=
      HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    let K := v.adicCompletion ℚ
    let E := P.freyCurve.baseChange K
    ∀ [E.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ)],
      Valued.v E.q = exp (padicValRat q P.freyCurve.j) := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro hsplit
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  -- Pin the completion structures used by the concrete valuation API.  Transitive imports
  -- provide propositionally equal alternatives, but the algebra map lemmas below require
  -- the same definitional choices as the adic completion construction.
  let _ : Field (v.adicCompletion ℚ) :=
    HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let E := P.freyCurve.baseChange K
  let _ : E.IsElliptic := inferInstance
  let _ : E.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) := by
    simpa [E, K, v] using hsplit
  have hj : 1 < ValuativeRel.valuation K E.j :=
    E.one_lt_valuation_j_of_compatible
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
      (R := v.adicCompletionIntegers ℚ) (by
        exact Valuation.valuationSubring.integers
          (Valued.v : Valuation K (WithZero (Multiplicative ℤ))))
  have hj0 : P.freyCurve.j ≠ 0 := by
    intro hj0
    have hjbase : E.j = 0 := by
      rw [show E.j = algebraMap ℚ K P.freyCurve.j from P.freyCurve.map_j _, hj0, map_zero]
    rw [hjbase, map_zero] at hj
    exact (not_lt_of_ge bot_le) hj
  rw [show E.q = WeierstrassCurve.tateParameter E.j from rfl,
    WeierstrassCurve.valuation_tateParameter_eq_of_compatible
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) hj]
  rw [show E.j = algebraMap ℚ K P.freyCurve.j from P.freyCurve.map_j _]
  change (Valued.v (algebraMap ℚ (v.adicCompletion ℚ) P.freyCurve.j))⁻¹ =
    exp (padicValRat q P.freyCurve.j)
  let jwith : WithVal (v.valuation ℚ) :=
    WithVal.toVal (v.valuation ℚ) P.freyCurve.j
  let jcoe : v.adicCompletion ℚ :=
    HeightOneSpectrum.adicCompletion.ofCompletion
      (jwith : (v.valuation ℚ).Completion)
  have halg : algebraMap ℚ (v.adicCompletion ℚ) P.freyCurve.j = jcoe := by
    apply HeightOneSpectrum.adicCompletion.ext
    rw [HeightOneSpectrum.algebraMap_adicCompletion_toCompletion]
    rfl
  have hjcoe : Valued.v jcoe = v.valuation ℚ P.freyCurve.j := by
    dsimp only [jcoe]
    rw [HeightOneSpectrum.adicCompletion.valued_ofCompletion,
      Valued.valuedCompletion_apply]
    exact WithVal.valued_toVal (v.valuation ℚ) P.freyCurve.j
  rw [halg, hjcoe,
    Rat.HeightOneSpectrum.valuation_apply_eq_padicValuation,
    Rat.HeightOneSpectrum.primesEquiv_toHeightOneSpectrumRingOfIntegersRat hq]
  change (Rat.padicValuation q P.freyCurve.j)⁻¹ = exp (padicValRat q P.freyCurve.j)
  change (if P.freyCurve.j = 0 then 0 else (exp (padicValRat q P.freyCurve.j))⁻¹)⁻¹ =
    exp (padicValRat q P.freyCurve.j)
  rw [if_neg hj0, inv_inv]

/-- At a bad odd prime where the Frey curve has split multiplicative reduction, its Tate
parameter has a uniformizer-unit factorization whose uniformizer exponent is divisible by
the Frey exponent.  The extra integral element `q0` records the Tate parameter inside the
concrete completion ring of integers, avoiding any dependence on a chosen membership proof. -/
theorem exists_tateParameter_uniformizer_factorization (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hqodd : 2 < q) (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    let _ : Field (v.adicCompletion ℚ) :=
      HeightOneSpectrum.adicCompletion.instField ℚ v
    let _ : CommRing (v.adicCompletion ℚ) :=
      (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
    let _ : Algebra ℚ (v.adicCompletion ℚ) :=
      HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    let K := v.adicCompletion ℚ
    let R := v.adicCompletionIntegers ℚ
    let E := P.freyCurve.baseChange K
    ∀ [E.HasSplitMultiplicativeReduction R],
      ∃ (q0 π : R) (m t : ℕ) (u : Rˣ),
        q0.1 = E.q ∧
        Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ) ∧
        q0 = π ^ m * (u : R) ∧ m = P.p * t := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro hsplit
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let _ : Field (v.adicCompletion ℚ) :=
    HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let E := P.freyCurve.baseChange K
  let _ : E.IsElliptic := inferInstance
  let _ : E.HasSplitMultiplicativeReduction R := hsplit
  have hj : 1 < ValuativeRel.valuation K E.j :=
    E.one_lt_valuation_j_of_compatible
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
      (R := R) (by
        exact Valuation.valuationSubring.integers
          (Valued.v : Valuation K (WithZero (Multiplicative ℤ))))
  have hqLt : Valued.v E.q < 1 := by
    rw [show E.q = WeierstrassCurve.tateParameter E.j from rfl]
    exact WeierstrassCurve.valuation_tateParameter_lt_one_of_compatible
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) hj
  let q0 : R := ⟨E.q, hqLt.le⟩
  have hq0 : q0 ≠ 0 := by
    intro hzero
    have hqzero : E.q = 0 := by
      have := congrArg Subtype.val hzero
      simpa [q0] using this
    exact WeierstrassCurve.tateParameter_ne_zero hj hqzero
  have hqval : Valued.v q0.1 = WithZero.exp (padicValRat q P.freyCurve.j) := by
    change Valued.v E.q = WithZero.exp (padicValRat q P.freyCurve.j)
    exact valued_tateParameter_at_bad_prime P hq hqodd hqbad
  have hpval : (P.p : ℤ) ∣ padicValRat q P.freyCurve.j :=
    j_valuation_of_bad_prime P hq hqbad hqodd
  obtain ⟨π, m, t, u, hπ, hfac, hm⟩ :=
    HeightOneSpectrum.adicCompletion.exists_eq_pow_uniformizer_mul_unit_of_valued_eq_exp_of_dvd
      (K := ℚ) v hq0 hqval hpval
  exact ⟨q0, π, m, t, u, rfl, hπ, hfac, hm⟩

/-- Every local inertia element fixes a `p`-th root of the Frey curve's Tate parameter at a
bad odd split-multiplicative prime.  This is the Kummer conclusion of the preceding
factorization: inertia fixes the root of the unit factor, while the remaining uniformizer
power already lies in the base field. -/
theorem exists_localInertia_fixed_pow_eq_tateParameter (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hqodd : 2 < q) (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    let _ : Field (v.adicCompletion ℚ) :=
      HeightOneSpectrum.adicCompletion.instField ℚ v
    let _ : CommRing (v.adicCompletion ℚ) :=
      (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
    let _ : Algebra ℚ (v.adicCompletion ℚ) :=
      HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    let K := v.adicCompletion ℚ
    let R := v.adicCompletionIntegers ℚ
    let E := P.freyCurve.baseChange K
    let Ω := AlgebraicClosure K
    let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
    ∀ [E.HasSplitMultiplicativeReduction R]
      [NeZero (P.p : IsLocalRing.ResidueField R)]
      (σ : Field.absoluteGaloisGroup K), σ ∈ localInertiaGroup v →
      ∃ r : Ω, r ^ P.p = algebraMap K Ω E.q ∧ σ r = r := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro hsplit hp σ hσ
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let _ : Field (v.adicCompletion ℚ) :=
    HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let E := P.freyCurve.baseChange K
  let Ω := AlgebraicClosure K
  let _ : E.IsElliptic := inferInstance
  let _ : E.HasSplitMultiplicativeReduction R := hsplit
  let _ : NeZero (P.p : IsLocalRing.ResidueField R) := hp
  let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
  obtain ⟨q0, π, m, t, u, hq0, _hπ, hfac, hm⟩ :=
    exists_tateParameter_uniformizer_factorization P hq hqodd hqbad
  obtain ⟨r, hr, hfix⟩ :=
    v.exists_localInertia_fixed_pow_eq_of_eq_pow_mul_unit
      P.p σ hσ q0 π m t u hfac hm
  refine ⟨r, hr.trans ?_, hfix⟩
  rw [IsScalarTower.algebraMap_apply R K Ω]
  change algebraMap K Ω q0.1 = algebraMap K Ω E.q
  rw [hq0]

end

end FreyCurve
