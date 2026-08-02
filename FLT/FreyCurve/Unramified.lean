/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Reduction
public import FLT.KnownIn1980s.EllipticCurves.GoodReductionUnramified

/-!
# Unramified primes of the Frey representation

This file combines completed good reduction, the prime-to-residue-characteristic
Néron--Ogg--Shafarevich direction, and the local-to-global torsion bridge.
-/

@[expose] public section

open IsDedekindDomain NumberField
open scoped WeierstrassCurve.Affine

namespace FreyCurve

noncomputable section

/-- At every odd prime `q` distinct from the Frey exponent and not dividing `abc`, the
`p`-torsion representation of the Frey curve is unramified. -/
theorem torsion_isUnramifiedAt_of_not_dvd_abc (P : FreyPackage) {q : ℕ}
    (hq : q.Prime) (hqodd : 2 < q) (hqp : q ≠ P.p)
    (hqgood : ¬(q : ℤ) ∣ P.a * P.b * P.c) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsUnramifiedAt
      hq.toHeightOneSpectrumRingOfIntegersRat := by
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  -- Pin the canonical completion instances. Some transitive imports also provide propositionally
  -- equal structures, while reduction and local inertia must use the same definitional choices.
  let _ : Field (v.adicCompletion ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v
  let _ : CommRing (v.adicCompletion ℚ) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField ℚ v).toCommRing
  let _ : Algebra ℚ (v.adicCompletion ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let K := v.adicCompletion ℚ
  let E := P.freyCurve.baseChange K
  let _ : E.IsElliptic := inferInstance
  let _ : E.HasGoodReduction (v.adicCompletionIntegers ℚ) := by
    simpa [E, K, v] using
      hasGoodReduction_at_completion_of_not_dvd_abc P hq hqodd hqgood
  let _ : NeZero (P.p : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Rat.HeightOneSpectrum.neZero_residueField_of_not_dvd hq (by
      rw [Nat.prime_dvd_prime_iff_eq hq P.pp]
      exact hqp)
  let _ : Algebra K (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  let _ : Algebra ℚ (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  let _ : DecidableEq (AlgebraicClosure K) := Classical.typeDecidableEq _
  let _ : NeZero (P.p : ℚ) := ⟨by exact_mod_cast P.pp.ne_zero⟩
  apply P.freyCurve.galoisRep_isUnramifiedAt_of_local_torsion_fixed v P.p P.hppos
  intro σ hσ T
  have hfixed := E.torsion_fixed_by_localInertia_of_good_reduction v P.p σ hσ T
  apply Subtype.ext
  have hfixed' := congrArg Subtype.val hfixed
  change WeierstrassCurve.Points.map E σ.toAlgHom T.1 = T.1 at hfixed'
  rw [P.freyCurve.nTorsionMap_coe]
  have hmaps : WeierstrassCurve.Points.map P.freyCurve
      ((σ.restrictScalars ℚ).toAlgHom) T.1 =
      WeierstrassCurve.Points.map E σ.toAlgHom T.1 := by
    rcases T.1 with (_ | ⟨x, y, h⟩) <;> rfl
  rw [hmaps]
  exact hfixed'

end

end FreyCurve
