/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Reduction
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

end

end FreyCurve
