/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Tate
public import FLT.GroupScheme.TateKummerFlat
public import FLT.KnownIn1980s.EllipticCurves.Flat

/-!
# Flatness of the Frey torsion representation

This file connects reduction of the Frey curve at its exponent to finite-flat models of its
torsion representation.  The good-reduction branch is supplied by the finite flat group scheme
`E[p]`; the multiplicative branch is kept separate because it requires the Tate-curve extension
criterion.
-/

@[expose] public section

open IsDedekindDomain NumberField

namespace FreyCurve

noncomputable section

/-- If the Frey exponent does not divide `abc`, the Frey curve has good reduction at that
exponent, so its `p`-torsion representation is flat at `p`. -/
theorem torsion_isFlatAt_of_not_dvd_abc (P : FreyPackage)
    (hgood : ¬(P.p : ℤ) ∣ P.a * P.b * P.c) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  -- Use the canonical completion structures chosen by the rational height-one spectrum.
  let _ : Field (v.adicCompletion ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let _ : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _
  let _ : DecidableEq (AlgebraicClosure (v.adicCompletion ℚ)) :=
    Classical.typeDecidableEq _
  let _ : NeZero P.p := ⟨P.pp.ne_zero⟩
  let _ : NeZero (P.p : ℚ) := ⟨by exact_mod_cast P.pp.ne_zero⟩
  have hpodd : 2 < P.p := by
    have hp5 := P.hp5
    omega
  let _ : (P.freyCurve.baseChange (v.adicCompletion ℚ)).HasGoodReduction
      (v.adicCompletionIntegers ℚ) := by
    simpa [v] using hasGoodReduction_at_completion_of_not_dvd_abc
      P P.pp hpodd hgood
  have hmodel :=
    WeierstrassCurve.galoisRep_hasFlatProlongationAt_of_good_reduction
      v P.freyCurve P.p P.hppos
  exact hmodel.isFlatAt_of_field v _

/-- If the completed Frey curve has split multiplicative reduction at its exponent,
the divisible valuation of its Tate parameter gives a Tate--Kummer finite-flat
prolongation of the global torsion representation. -/
theorem torsion_hasFlatProlongationAt_of_split_multiplicative
    (P : FreyPackage) (hbad : (P.p : ℤ) ∣ P.a * P.b * P.c) :
    letI : Fact P.p.Prime := ⟨P.pp⟩
    let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
    let K := v.adicCompletion ℚ
    let R := v.adicCompletionIntegers ℚ
    let _ : Field K :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v
    let _ : CommRing K :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
    let _ : Algebra ℚ K :=
      IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    let E := P.freyCurve.baseChange K
    ∀ [E.HasSplitMultiplicativeReduction R],
      (P.freyCurve.galoisRep P.p P.hppos).HasFlatProlongationAt v := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  dsimp only
  intro hsplit
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let _ : Field K :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing K :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ K :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let Ω := AlgebraicClosure K
  let E := P.freyCurve.baseChange K
  let _ : E.IsElliptic := inferInstance
  let _ : E.HasSplitMultiplicativeReduction R := hsplit
  let _ : E.HasSplitMultiplicativeReduction
      (ValuativeRel.valuation K).integer :=
    hasSplitMultiplicativeReduction_valuativeRel_of_adicCompletion v E
  let _ : DecidableEq K := Classical.typeDecidableEq K
  let _ : DecidableEq Ω := Classical.typeDecidableEq Ω
  let _ : DecidableEq ℚ := Classical.typeDecidableEq ℚ
  let _ : DecidableEq (AlgebraicClosure ℚ) :=
    Classical.typeDecidableEq (AlgebraicClosure ℚ)
  let _ : NeZero P.p := ⟨P.pp.ne_zero⟩
  let _ : NeZero (P.p : ℚ) := ⟨by exact_mod_cast P.pp.ne_zero⟩
  let _ : NeZero (P.p : K) := ⟨by exact_mod_cast P.pp.ne_zero⟩
  have hpodd : 2 < P.p := by
    have hp5 := P.hp5
    omega
  obtain ⟨q₀, a, u, hq₀, hfac⟩ :=
    exists_tateParameter_eq_pow_mul_unit_of_j_eq
      P P.pp hpodd hbad E (P.freyCurve.map_j (algebraMap ℚ K))
  have hq₀' : algebraMap R K q₀ = E.q := by
    simpa [R, K] using hq₀
  have hmodel :=
    E.torsion_flat_of_split_multiplicative_factorization R K Ω
      P.p q₀ a u hq₀' hfac
  exact WeierstrassCurve.galoisRep_hasFlatProlongationAt_of_local_model
    v P.freyCurve P.p P.hppos hmodel

/-- The split-multiplicative Tate--Kummer prolongation proves flatness at the Frey
exponent. -/
theorem torsion_isFlatAt_of_split_multiplicative
    (P : FreyPackage) (hbad : (P.p : ℤ) ∣ P.a * P.b * P.c) :
    letI : Fact P.p.Prime := ⟨P.pp⟩
    let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
    let K := v.adicCompletion ℚ
    let R := v.adicCompletionIntegers ℚ
    let _ : Field K :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v
    let _ : CommRing K :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
    let _ : Algebra ℚ K :=
      IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    let E := P.freyCurve.baseChange K
    ∀ [E.HasSplitMultiplicativeReduction R],
      (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt v := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  dsimp only
  intro hsplit
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  have hmodel := torsion_hasFlatProlongationAt_of_split_multiplicative P hbad
  exact hmodel.isFlatAt_of_field v _

end

end FreyCurve
