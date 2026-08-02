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

import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Tate parameters at bad primes of the Frey curve

This file carries out the local Kummer calculation from the Frey-curve blueprint.  It relates
the valuation of the Tate parameter over the completed local field to the rational `q`-adic
valuation of the Frey curve's `j`-invariant, then uses the resulting divisible uniformizer
exponent to construct inertia-fixed roots of the Tate parameter.
-/

@[expose] public section

open IsDedekindDomain NumberField WithZero
open scoped Multiplicative WeierstrassCurve.Affine

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

/-- Any split multiplicative curve over the completion whose `j`-invariant is that of the Frey
curve has Tate parameter valuation equal to the exponential of the rational `q`-adic valuation.
The sign changes because the Tate parameter has the valuation of `j⁻¹`. -/
theorem valued_tateParameter_at_bad_prime_of_j_eq (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (_hqodd : 2 < q) (_hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
    let v := hq.toHeightOneSpectrumRingOfIntegersRat
    let _ : Field (v.adicCompletion ℚ) :=
      HeightOneSpectrum.adicCompletion.instField ℚ v
    let _ : CommRing (v.adicCompletion ℚ) :=
      (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
    let _ : Algebra ℚ (v.adicCompletion ℚ) :=
      HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    let K := v.adicCompletion ℚ
    ∀ (E : WeierstrassCurve K) [E.IsElliptic]
      [E.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ)],
      E.j = algebraMap ℚ K P.freyCurve.j →
      Valued.v E.q = exp (padicValRat q P.freyCurve.j) := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro E hell hsplit hjmap
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
  let _ : E.IsElliptic := hell
  let _ : E.HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) := by
    simpa [K, v] using hsplit
  have hj : 1 < ValuativeRel.valuation K E.j :=
    E.one_lt_valuation_j_of_compatible
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
      (R := v.adicCompletionIntegers ℚ) (by
        exact Valuation.valuationSubring.integers
          (Valued.v : Valuation K (WithZero (Multiplicative ℤ))))
  have hj0 : P.freyCurve.j ≠ 0 := by
    intro hj0
    have hjbase : E.j = 0 := by
      rw [hjmap, hj0, map_zero]
    rw [hjbase, map_zero] at hj
    exact (not_lt_of_ge bot_le) hj
  rw [show E.q = WeierstrassCurve.tateParameter E.j from rfl,
    WeierstrassCurve.valuation_tateParameter_eq_of_compatible
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) hj]
  rw [hjmap]
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

/-- The Tate-parameter valuation formula for the completed Frey curve itself. -/
theorem valued_tateParameter_at_bad_prime (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hqodd : 2 < q) (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) :
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
  dsimp only
  intro hsplit
  exact valued_tateParameter_at_bad_prime_of_j_eq P hq hqodd hqbad _
    (P.freyCurve.map_j _)

/-- A split multiplicative curve with the Frey `j`-invariant has a Tate-parameter
uniformizer-unit factorization whose uniformizer exponent is divisible by the Frey exponent.
The extra integral element `q0` records the parameter inside the concrete completion ring. -/
theorem exists_tateParameter_uniformizer_factorization_of_j_eq
    (P : FreyPackage) {q : ℕ}
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
    ∀ (E : WeierstrassCurve K) [E.IsElliptic]
      [E.HasSplitMultiplicativeReduction R],
      E.j = algebraMap ℚ K P.freyCurve.j →
      ∃ (q0 π : R) (m t : ℕ) (u : Rˣ),
        q0.1 = E.q ∧
        Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ) ∧
        q0 = π ^ m * (u : R) ∧ m = P.p * t := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro E hell hsplit hjmap
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let _ : Field (v.adicCompletion ℚ) :=
    HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let _ : E.IsElliptic := hell
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
    exact valued_tateParameter_at_bad_prime_of_j_eq P hq hqodd hqbad E hjmap
  have hpval : (P.p : ℤ) ∣ padicValRat q P.freyCurve.j :=
    j_valuation_of_bad_prime P hq hqbad hqodd
  obtain ⟨π, m, t, u, hπ, hfac, hm⟩ :=
    HeightOneSpectrum.adicCompletion.exists_eq_pow_uniformizer_mul_unit_of_valued_eq_exp_of_dvd
      (K := ℚ) v hq0 hqval hpval
  exact ⟨q0, π, m, t, u, rfl, hπ, hfac, hm⟩

/-- The Tate-parameter factorization for the completed Frey curve itself. -/
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
  dsimp only
  intro hsplit
  exact exists_tateParameter_uniformizer_factorization_of_j_eq
    P hq hqodd hqbad _ (P.freyCurve.map_j _)

/-- Every local inertia element fixes a `p`-th root of the Tate parameter of a split
multiplicative curve with the Frey `j`-invariant.  Inertia fixes the root of the unit factor,
while the remaining uniformizer power already lies in the base field. -/
theorem exists_localInertia_fixed_pow_eq_tateParameter_of_j_eq
    (P : FreyPackage) {q : ℕ}
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
    let Ω := AlgebraicClosure K
    let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
    ∀ (E : WeierstrassCurve K) [E.IsElliptic]
      [E.HasSplitMultiplicativeReduction R]
      [NeZero (P.p : IsLocalRing.ResidueField R)]
      (_hj : E.j = algebraMap ℚ K P.freyCurve.j)
      (σ : Field.absoluteGaloisGroup K), σ ∈ localInertiaGroup v →
      ∃ r : Ω, r ^ P.p = algebraMap K Ω E.q ∧ σ r = r := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro E hell hsplit hp hjmap σ hσ
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let _ : Field (v.adicCompletion ℚ) :=
    HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let Ω := AlgebraicClosure K
  let _ : E.IsElliptic := hell
  let _ : E.HasSplitMultiplicativeReduction R := hsplit
  let _ : NeZero (P.p : IsLocalRing.ResidueField R) := hp
  let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
  obtain ⟨q0, π, m, t, u, hq0, _hπ, hfac, hm⟩ :=
    exists_tateParameter_uniformizer_factorization_of_j_eq
      P hq hqodd hqbad E hjmap
  obtain ⟨r, hr, hfix⟩ :=
    v.exists_localInertia_fixed_pow_eq_of_eq_pow_mul_unit
      P.p σ hσ q0 π m t u hfac hm
  refine ⟨r, hr.trans ?_, hfix⟩
  rw [IsScalarTower.algebraMap_apply R K Ω]
  change algebraMap K Ω q0.1 = algebraMap K Ω E.q
  rw [hq0]

/-- The inertia-fixed Tate root for the completed Frey curve itself. -/
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
  let _ : E.IsElliptic := inferInstance
  let _ : E.HasSplitMultiplicativeReduction R := by
    simpa [E, R, K, v] using hsplit
  let _ : NeZero (P.p : IsLocalRing.ResidueField R) := by
    simpa [R, v] using hp
  exact exists_localInertia_fixed_pow_eq_tateParameter_of_j_eq
    P hq hqodd hqbad E (P.freyCurve.map_j _) σ hσ

/-- At a bad odd prime, inertia fixes the `p`-torsion of every split multiplicative curve with
the Frey `j`-invariant.  The proof pulls a torsion point back through Tate uniformization,
represents its quotient class by a unit, and applies the fixed-root Kummer calculation above. -/
theorem torsion_fixed_by_localInertia_of_split_multiplicative_of_j_eq
    (P : FreyPackage) {q : ℕ}
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
    let Ω := AlgebraicClosure K
    let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
    ∀ (E : WeierstrassCurve K) [E.IsElliptic]
      [E.HasSplitMultiplicativeReduction R]
      [NeZero (P.p : IsLocalRing.ResidueField R)]
      [DecidableEq Ω]
      (_hj : E.j = algebraMap ℚ K P.freyCurve.j)
      (σ : Field.absoluteGaloisGroup K), σ ∈ localInertiaGroup v →
      ∀ T : AddSubgroup.torsionBy (E⁄Ω).Point (P.p : ℤ),
        E.nTorsionMap P.p σ.toAlgHom T = T := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro E hell hsplit hp hdec hjmap σ hσ T
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let _ : Field (v.adicCompletion ℚ) :=
    HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let Ω := AlgebraicClosure K
  let _ : E.IsElliptic := hell
  let _ : DecidableEq K := Classical.typeDecidableEq K
  let _ : E.HasSplitMultiplicativeReduction R := hsplit
  let _ : NeZero (P.p : IsLocalRing.ResidueField R) := hp
  let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
  let _ : DecidableEq Ω := hdec
  let _ : E.HasSplitMultiplicativeReduction
      (ValuativeRel.valuation K).integer :=
    hasSplitMultiplicativeReduction_valuativeRel_of_adicCompletion v E
  obtain ⟨r, hr, hfixr⟩ :=
    exists_localInertia_fixed_pow_eq_tateParameter_of_j_eq
      P hq hqodd hqbad E hjmap σ hσ
  have hr0 : r ≠ 0 := by
    intro hzero
    apply E.q_ne_zero
    apply (algebraMap K Ω).injective
    rw [map_zero, ← hr, hzero, zero_pow P.pp.ne_zero]
  let r0 : Ωˣ := Units.mk0 r hr0
  have hr0pow : r0 ^ P.p = E.qUnitSepClosure Ω := by
    apply Units.ext
    change r ^ P.p = algebraMap K Ω E.q
    exact hr
  have hfixr0 : Units.map σ.toAlgHom.toRingHom.toMonoidHom r0 = r0 := by
    apply Units.ext
    exact hfixr
  let f := E.tateEquivSepClosure Ω
  let x := f.symm T.1
  obtain ⟨u, hu⟩ := (QuotientGroup.mk'_surjective
    (N := Subgroup.zpowers (E.qUnitSepClosure Ω))) x.toMul
  have hux : Additive.ofMul
      (u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = x := by
    apply Additive.toMul.injective
    exact hu
  have hTu : E.tatePoint Ω u = T.1 := by
    change f (Additive.ofMul
      (u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) = T.1
    rw [hux]
    exact f.apply_symm_apply T.1
  have hTzero : P.p • T.1 = 0 := AddSubgroup.torsionBy.nsmul_iff.mp T.2
  have hxzero : P.p • x = 0 := by
    apply f.injective
    rw [map_nsmul, map_zero, show f x = T.1 from f.apply_symm_apply T.1, hTzero]
  have hxpow : x.toMul ^ P.p = 1 := by
    rw [← toMul_nsmul, hxzero]
    rfl
  have hupow :
      (u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ^ P.p = 1 := by
    change (QuotientGroup.mk' (Subgroup.zpowers (E.qUnitSepClosure Ω)) u) ^ P.p = 1
    rw [hu]
    exact hxpow
  have hfixu : Units.map σ.toAlgHom.toRingHom.toMonoidHom u = u :=
    v.localInertia_fixed_unit_of_mk_pow_eq_one P.p σ hσ
      (E.qUnitSepClosure Ω) r0 u hr0pow hfixr0 hupow
  have hpoint :
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (E.tatePoint Ω u) =
        E.tatePoint Ω u := by
    rw [E.tatePoint_galois Ω σ u, hfixu]
  apply Subtype.ext
  rw [E.nTorsionMap_coe]
  change WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom T.1 = T.1
  rw [← hTu]
  exact hpoint

/-- At a bad odd prime, local inertia also fixes the `p`-torsion of a nonsplit
multiplicative curve with the Frey `j`-invariant.  Pass to the unramified quadratic twist,
where the reduction is split and the Tate calculation applies.  Inertia fixes the twisting
extension, so its quadratic character is trivial; naturality of the twist and minimal-model
point equivalences then transports the fixed point back to the original curve. -/
theorem torsion_fixed_by_localInertia_of_nonsplit_multiplicative_of_j_eq
    (P : FreyPackage) {q : ℕ}
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
    let Ω := AlgebraicClosure K
    let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
    ∀ (E : WeierstrassCurve K) [E.IsElliptic]
      [E.HasMultiplicativeReduction R]
      [NeZero (P.p : IsLocalRing.ResidueField R)]
      [DecidableEq Ω]
      (_hnsplit : ¬ E.HasSplitMultiplicativeReduction R)
      (_hj : E.j = algebraMap ℚ K P.freyCurve.j)
      (σ : Field.absoluteGaloisGroup K), σ ∈ localInertiaGroup v →
      ∀ T : AddSubgroup.torsionBy (E⁄Ω).Point (P.p : ℤ),
        E.nTorsionMap P.p σ.toAlgHom T = T := by
  let _ : Fact q.Prime := ⟨hq⟩
  dsimp only
  intro E hell hmult hp hdec hnsplit hjmap σ hσ T
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let _ : Field (v.adicCompletion ℚ) :=
    HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let Ω := AlgebraicClosure K
  let _ : E.IsElliptic := hell
  let _ : DecidableEq K := Classical.typeDecidableEq K
  let _ : E.HasMultiplicativeReduction R := hmult
  let _ : NeZero (P.p : IsLocalRing.ResidueField R) := hp
  let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
  let _ : DecidableEq Ω := hdec
  have hd : E.UnramifiedQuadraticTwistData R :=
    E.exists_unramified_quadraticTwist_hasSplitMultiplicativeReduction R hnsplit
  unfold WeierstrassCurve.UnramifiedQuadraticTwistData at hd
  obtain ⟨L, hfield, halgebra, hquadratic, hseparable, halgebraR, htower,
      θ, t, n, hθint, hθbase, htrace, hnorm, hdisc, hsplit⟩ := hd
  let ι : L →ₐ[K] Ω := IsAlgClosed.lift
  let _ : Algebra L Ω := ι.toRingHom.toAlgebra
  have halgι : algebraMap L Ω = ι := RingHom.algebraMap_toAlgebra _
  let _ : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halgι]
    exact (ι.commutes x).symm
  have hfixL (x : L) : σ (algebraMap L Ω x) = algebraMap L Ω x := by
    rw [halgι]
    exact v.localInertia_fixed_on_unramified_quadratic_extension
      L ι θ t n hθint hθbase htrace hnorm hdisc σ hσ x
  have hchi : quadraticCharacter K L Ω σ = 1 :=
    (quadraticCharacter_eq_one_iff K L Ω σ).2 hfixL
  let Et := E.quadraticTwist L
  let C := (Et.exists_isMinimal R).choose
  let W := Et.minimal R
  have hWdef : W = C • Et := rfl
  let _ : Et.IsElliptic := inferInstance
  let _ : W.IsElliptic := by
    change (C • Et).IsElliptic
    infer_instance
  let _ : W.HasSplitMultiplicativeReduction R := hsplit
  have hjW : W.j = algebraMap ℚ K P.freyCurve.j := by
    calc
      W.j = Et.j := by
        change (C • Et).j = Et.j
        exact WeierstrassCurve.variableChange_j Et C
      _ = E.j := E.j_quadraticTwist L
      _ = algebraMap ℚ K P.freyCurve.j := hjmap
  let twistEquiv := E.quadraticTwistPointEquiv L Ω
  let minimalEquiv :=
    WeierstrassCurve.Affine.Point.variableChangePointEquiv Et C Ω
  let Qtwist := twistEquiv.symm T.1
  let Qmin := minimalEquiv.symm Qtwist
  have hTzero : P.p • T.1 = 0 := AddSubgroup.torsionBy.nsmul_iff.mp T.2
  have hQtwistzero : P.p • Qtwist = 0 := by
    apply twistEquiv.injective
    rw [map_nsmul, map_zero, twistEquiv.apply_symm_apply, hTzero]
  have hQminzero : P.p • Qmin = 0 := by
    apply minimalEquiv.injective
    rw [map_nsmul, map_zero, minimalEquiv.apply_symm_apply, hQtwistzero]
  let QminTorsion : AddSubgroup.torsionBy (W⁄Ω).Point (P.p : ℤ) := by
    refine ⟨?_, AddSubgroup.torsionBy.nsmul_iff.mpr ?_⟩
    · exact Qmin
    · exact hQminzero
  have hfixedW := torsion_fixed_by_localInertia_of_split_multiplicative_of_j_eq
    P hq hqodd hqbad W hjW σ hσ QminTorsion
  have hfixedWpoint :
      WeierstrassCurve.Affine.Point.map (W' := W) σ.toAlgHom Qmin = Qmin := by
    have h := congrArg Subtype.val hfixedW
    rw [W.nTorsionMap_coe] at h
    change WeierstrassCurve.Affine.Point.map (W' := W) σ.toAlgHom Qmin = Qmin at h
    exact h
  have hQtwistfixed :
      WeierstrassCurve.Affine.Point.map (W' := Et) σ.toAlgHom Qtwist = Qtwist := by
    calc
      WeierstrassCurve.Affine.Point.map (W' := Et) σ.toAlgHom Qtwist =
          WeierstrassCurve.Affine.Point.map (W' := Et) σ.toAlgHom
            (minimalEquiv Qmin) := by rw [minimalEquiv.apply_symm_apply]
      _ = minimalEquiv
          (WeierstrassCurve.Affine.Point.map (W' := W) σ.toAlgHom Qmin) := by
            symm
            exact WeierstrassCurve.Affine.Point.variableChangePointEquiv_map
              Et C σ.toAlgHom Qmin
      _ = minimalEquiv Qmin := congrArg minimalEquiv hfixedWpoint
      _ = Qtwist := minimalEquiv.apply_symm_apply Qtwist
  have hEpoint :
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom T.1 = T.1 := by
    have hgal := E.quadraticTwistPointEquiv_galois L Ω σ Qtwist
    have hQtwistT : twistEquiv Qtwist = T.1 := twistEquiv.apply_symm_apply T.1
    rw [hQtwistfixed, hchi, Units.val_one, one_zsmul, hQtwistT] at hgal
    exact hgal.symm
  apply Subtype.ext
  rw [E.nTorsionMap_coe]
  exact hEpoint

/-- At a bad odd split-multiplicative prime distinct from the Frey exponent, local inertia
fixes every `p`-torsion point of the completed Frey curve. -/
theorem torsion_fixed_by_localInertia_of_split_multiplicative
    (P : FreyPackage) {q : ℕ}
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
      [DecidableEq Ω]
      (σ : Field.absoluteGaloisGroup K), σ ∈ localInertiaGroup v →
      ∀ T : AddSubgroup.torsionBy (E⁄Ω).Point (P.p : ℤ),
        E.nTorsionMap P.p σ.toAlgHom T = T := by
  dsimp only
  intro hsplit hp hdec σ hσ T
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
  let _ : E.HasSplitMultiplicativeReduction R := by
    simpa [E, R, K, v] using hsplit
  let _ : NeZero (P.p : IsLocalRing.ResidueField R) := by
    simpa [R, v] using hp
  let _ : Algebra K Ω := AlgebraicClosure.instAlgebra K
  let _ : DecidableEq Ω := hdec
  exact torsion_fixed_by_localInertia_of_split_multiplicative_of_j_eq
    P hq hqodd hqbad E (P.freyCurve.map_j _) σ hσ T

end

end FreyCurve
