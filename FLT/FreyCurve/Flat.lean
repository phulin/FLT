/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Reduction
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

end

end FreyCurve
