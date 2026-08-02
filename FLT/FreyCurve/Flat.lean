/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Tate
public import FLT.GroupScheme.TateKummerFlat
public import FLT.GroupScheme.TateKummerQuadraticTwistFlat
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

/-- If the completed Frey curve has nonsplit multiplicative reduction at its exponent,
descend the Tate--Kummer model of its unramified quadratic twist. -/
theorem torsion_hasFlatProlongationAt_of_nonsplit_multiplicative
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
    ∀ [E.HasMultiplicativeReduction R],
      ¬ E.HasSplitMultiplicativeReduction R →
      (P.freyCurve.galoisRep P.p P.hppos).HasFlatProlongationAt v := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  dsimp only
  intro hmult hnsplit
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
  let _ : E.HasMultiplicativeReduction R := hmult
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
  have hd : E.UnramifiedQuadraticTwistData R :=
    E.exists_unramified_quadraticTwist_hasSplitMultiplicativeReduction R hnsplit
  unfold WeierstrassCurve.UnramifiedQuadraticTwistData at hd
  obtain ⟨L, hfield, halgebra, hquadratic, hseparable, halgebraR, htower,
      θ, t, n, _hθint, hθbase, htrace, hnorm, hdiscResidue, hsplit⟩ := hd
  let ι : L →ₐ[K] Ω := IsAlgClosed.lift
  letI : Algebra L Ω := ι.toRingHom.toAlgebra
  have halgι : algebraMap L Ω = ι := RingHom.algebraMap_toAlgebra _
  letI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halgι]
    exact (ι.commutes x).symm
  letI : IsScalarTower R L Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halgι, IsScalarTower.algebraMap_apply R K L]
    change algebraMap R Ω x = ι (algebraMap K L (algebraMap R K x))
    rw [ι.commutes]
    exact IsScalarTower.algebraMap_apply R K Ω x
  let Et := E.quadraticTwist L
  let C := (Et.exists_isMinimal R).choose
  let W := Et.minimal R
  let _ : Et.IsElliptic := inferInstance
  let _ : W.IsElliptic := by
    change (C • Et).IsElliptic
    infer_instance
  letI : W.HasSplitMultiplicativeReduction R := hsplit
  letI : (C • E.quadraticTwist L).HasSplitMultiplicativeReduction
      (ValuativeRel.valuation K).integer := by
    change W.HasSplitMultiplicativeReduction
      (ValuativeRel.valuation K).integer
    exact hasSplitMultiplicativeReduction_valuativeRel_of_adicCompletion v W
  have hjW : W.j = algebraMap ℚ K P.freyCurve.j := by
    calc
      W.j = Et.j := by
        change (C • Et).j = Et.j
        exact WeierstrassCurve.variableChange_j Et C
      _ = E.j := E.j_quadraticTwist L
      _ = algebraMap ℚ K P.freyCurve.j := by
        change (P.freyCurve.baseChange K).j = algebraMap ℚ K P.freyCurve.j
        exact P.freyCurve.map_j (algebraMap ℚ K)
  obtain ⟨q₀, a, u, hq₀, hfac⟩ :=
    exists_tateParameter_eq_pow_mul_unit_of_j_eq
      P P.pp hpodd hbad W hjW
  have hq₀' : algebraMap R K q₀ = W.q := by
    simpa [R, K] using hq₀
  let _ : NeZero (2 : IsLocalRing.ResidueField R) :=
    Rat.HeightOneSpectrum.neZero_residueField_of_not_dvd P.pp (by
      intro hdiv
      have hle := Nat.le_of_dvd (by omega : 0 < 2) hdiv
      omega)
  have h2 : IsUnit (2 : R) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (2 : R)).mp (by
      simpa only [map_ofNat] using
        (NeZero.ne (2 : IsLocalRing.ResidueField R)))
  have hdisc : IsUnit (QuadraticDescent.discriminant R t n) :=
    QuadraticDescent.discriminant_isUnit_of_residue_ne_zero (R := R) t n (by
      simpa [QuadraticDescent.discriminant] using hdiscResidue)
  have hRLO : IsScalarTower R L Ω := inferInstance
  have hmodel :=
    @WeierstrassCurve.torsion_flat_of_quadratic_twist_factorization
      R _ _ K L _ hfield _ halgebra halgebraR htower hquadratic hseparable
      Ω _ _ _ _ _ hRLO _ _ _ _ _ _ _ _ E _ C _ _
      P.p _ _ u t n θ hθbase htrace hnorm h2 hdisc q₀ a hq₀' hfac
  apply WeierstrassCurve.galoisRep_hasFlatProlongationAt_of_local_model
    v P.freyCurve P.p P.hppos
  simpa only [K, R, Ω, E] using hmodel

/-- At a bad Frey exponent, multiplicative reduction gives a flat prolongation whether
or not the node is already split. -/
theorem torsion_hasFlatProlongationAt_of_multiplicative
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
    ∀ [E.HasMultiplicativeReduction R],
      (P.freyCurve.galoisRep P.p P.hppos).HasFlatProlongationAt v := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  dsimp only
  intro hmult
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
  let _ : E.HasMultiplicativeReduction R := hmult
  by_cases hsplit : E.HasSplitMultiplicativeReduction R
  · let _ : E.HasSplitMultiplicativeReduction R := hsplit
    exact torsion_hasFlatProlongationAt_of_split_multiplicative P hbad
  · exact torsion_hasFlatProlongationAt_of_nonsplit_multiplicative
      P hbad hsplit

/-- Multiplicative reduction at a bad Frey exponent makes the torsion representation
flat at that exponent. -/
theorem torsion_isFlatAt_of_multiplicative
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
    ∀ [E.HasMultiplicativeReduction R],
      (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt v := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  dsimp only
  intro hmult
  let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
  have hmodel := torsion_hasFlatProlongationAt_of_multiplicative P hbad
  exact hmodel.isFlatAt_of_field v _

/-- The Frey `p`-torsion representation is flat at `p`: use good reduction when `p`
does not divide `abc`, and the split-or-descended Tate--Kummer model otherwise. -/
theorem torsion_isFlatAt (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  by_cases hbad : (P.p : ℤ) ∣ P.a * P.b * P.c
  · let v := P.pp.toHeightOneSpectrumRingOfIntegersRat
    let K := v.adicCompletion ℚ
    let R := v.adicCompletionIntegers ℚ
    let _ : Field K :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v
    let _ : CommRing K :=
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
    let _ : Algebra ℚ K :=
      IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    let E := P.freyCurve.baseChange K
    let _ : E.HasMultiplicativeReduction R := by
      have hpodd : 2 < P.p := by
        have hp5 := P.hp5
        omega
      exact hasMultiplicativeReduction_at_completion_of_dvd_abc
        P P.pp hpodd hbad
    exact torsion_isFlatAt_of_multiplicative P hbad
  · exact torsion_isFlatAt_of_not_dvd_abc P hbad

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
