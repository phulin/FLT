/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.KnownIn1980s.EllipticCurves.GoodReduction

/-!

# Good reduction and the local inertia group

This file identifies the valuation-theoretic inertia subgroup used by
`WeierstrassCurve.torsion_unramified_of_good_reduction` with the concrete local inertia
group attached to a height-one prime of a number field.  It thereby packages the good-reduction
criterion in the form needed by global Galois representations.

-/

@[expose] public section

open NumberField
open scoped WeierstrassCurve.Affine Pointwise

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

namespace WeierstrassCurve

variable {K : Type*} [Field K] [NumberField K]

/-- If an elliptic curve over a completed number field has good reduction, local inertia fixes
all prime-to-residue-characteristic torsion points over its algebraic closure. -/
theorem torsion_fixed_by_localInertia_of_good_reduction
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (E : WeierstrassCurve (v.adicCompletion K)) [E.IsElliptic]
    [E.HasGoodReduction (v.adicCompletionIntegers K)]
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField (v.adicCompletionIntegers K))]
    [DecidableEq (AlgebraicClosure (v.adicCompletion K))] :
    ∀ σ ∈ localInertiaGroup v,
      ∀ P : AddSubgroup.torsionBy
          (E⁄(AlgebraicClosure (v.adicCompletion K))).Point (n : ℤ),
        E.nTorsionMap n σ.toAlgHom P = P := by
  let k := v.adicCompletion K
  let R := v.adicCompletionIntegers K
  let L := AlgebraicClosure k
  let S := IntegralClosure R L
  let 𝒪 : ValuationSubring L :=
    ValuationSubring.ofSubring (integralClosure R L).toSubring
      (fun x => by
        obtain hx | hx := le_total (spectralNorm k L x) 1
        · exact .inl (isIntegral_of_spectralNorm_le_one hx)
        · exact .inr (isIntegral_of_spectralNorm_le_one (by
            rw [spectralNorm_inv]
            exact inv_le_one_of_one_le₀ hx)))
  have h𝒪 : (𝒪.comap (algebraMap k L)).toSubring = (algebraMap R k).range := by
    ext x
    change _root_.IsIntegral R (algebraMap k L x) ↔ x ∈ (algebraMap R k).range
    rw [isIntegral_algebraMap_iff (algebraMap k L).injective]
    exact IsIntegrallyClosed.isIntegral_iff
  intro σ hσ P
  let σD : 𝒪.decompositionSubgroup k := ⟨σ, by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    change x ∈ σ • (𝒪 : Set L) ↔ x ∈ (𝒪 : Set L)
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change _root_.IsIntegral R (σ⁻¹ x) ↔ _root_.IsIntegral R x
    constructor
    · intro hx
      simpa using hx.map (σ.restrictScalars R).toAlgHom
    · intro hx
      simpa using hx.map (σ⁻¹.restrictScalars R).toAlgHom⟩
  have hσD : σD ∈ 𝒪.inertiaSubgroup k := by
    change MulSemiringAction.toRingAut (𝒪.decompositionSubgroup k)
      (IsLocalRing.ResidueField 𝒪) σD = 1
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    change σD • IsLocalRing.residue 𝒪 x = IsLocalRing.residue 𝒪 x
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hx
    apply hσ (⟨x, x.2⟩ : S)
    let f : 𝒪 →+* S :=
      { toFun := fun y => ⟨y, y.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    change IsUnit (f (σD • x - x))
    exact hx.map f
  apply Subtype.ext
  exact WeierstrassCurve.torsion_unramified_of_good_reduction
    R k E n L 𝒪 h𝒪 σD hσD P P.2

end WeierstrassCurve
