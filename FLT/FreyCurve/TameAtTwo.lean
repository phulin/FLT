/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.FreyCurve.Reduction
public import FLT.GaloisRepresentation.HardlyRamified.QuadraticCharacterAtTwo
public import FLT.KnownIn1980s.EllipticCurves.TateCurveTorsion

/-!
# The tame quadratic quotient of Frey torsion at two

This file transports global torsion to the algebraic closure of `ℚ₂`, constructs the Tate
component quotient there, and proves the equivariance, inertia, and quadraticity conditions
used by `GaloisRep.HasTameQuadraticQuotientAtTwo`.
-/

@[expose] public section

open WeierstrassCurve.Affine
open ValuativeRel

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

noncomputable local instance : DecidableEq (AlgebraicClosure ℚ_[2]) :=
  Classical.typeDecidableEq _

noncomputable local instance : DecidableEq ℚ_[2] :=
  Classical.typeDecidableEq _

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The global-to-local linear equivalence from torsion over `ℚ̄` to torsion over the chosen
algebraic closure of `ℚ₂`. -/
noncomputable def twoAdicTorsionLinearEquiv (n : ℕ) [NeZero n] :
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ) ≃ₗ[ZMod n]
      AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ) := by
  letI : NeZero (n : AlgebraicClosure ℚ) := ⟨by exact_mod_cast NeZero.ne n⟩
  letI : NeZero (n : AlgebraicClosure ℚ_[2]) := ⟨by exact_mod_cast NeZero.ne n⟩
  exact nTorsionLinearEquivOfIsSepClosed
    (E := E) n (AlgebraicClosure.mapAlgHom ℚ ℚ_[2])

/-- The global-to-local torsion equivalence intertwines the action obtained by restricting
the global representation to `Γ ℚ₂` with the natural action on local torsion. -/
theorem twoAdicTorsionLinearEquiv_galois (n : ℕ) [NeZero n]
    (σ : Γ ℚ_[2])
    (P : AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    E.twoAdicTorsionLinearEquiv n
        (E.nTorsionMap n
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ).toAlgHom P) =
      E.nTorsionMap n (σ.toAlgHom.restrictScalars ℚ)
        (E.twoAdicTorsionLinearEquiv n P) := by
  letI : NeZero (n : AlgebraicClosure ℚ) := ⟨by exact_mod_cast NeZero.ne n⟩
  letI : NeZero (n : AlgebraicClosure ℚ_[2]) := ⟨by exact_mod_cast NeZero.ne n⟩
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  apply nTorsionLinearEquivOfIsSepClosed_nTorsionMap
    (E := E) n (AlgebraicClosure.mapAlgHom ℚ ℚ_[2])
  ext x
  exact Field.absoluteGaloisGroup.lift_map (algebraMap ℚ ℚ_[2]) σ x

/-- Reassociate the two successive base changes from `ℚ` to `ℚ₂` and then to `ℚ̄₂`.
The orientation sends points on the direct base change over `ℚ̄₂` to points on the local
curve over `ℚ₂`, subsequently base changed to `ℚ̄₂`. -/
noncomputable def twoAdicBaseChangePointEquiv :
    (E⁄(AlgebraicClosure ℚ_[2])).Point ≃+
      ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point :=
  (Affine.Point.equivOfEq
    (E.baseChange_map_algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))).symm

/-- Global torsion over `ℚ̄`, transported all the way to torsion on the local curve
`E / ℚ₂` over `ℚ̄₂`. -/
noncomputable def twoAdicLocalTorsionLinearEquiv (n : ℕ) [NeZero n] :
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy
          ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ) ≃ₗ[ZMod n]
      AddSubgroup.torsionBy
        ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ) := by
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy
        ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  exact (E.twoAdicTorsionLinearEquiv n).trans
    (E.twoAdicBaseChangePointEquiv.torsionByLinearEquiv n)

set_option backward.isDefEq.respectTransparency false in
/-- The global-to-local torsion equivalence intertwines the restricted global Galois action
with the natural action on the local curve over `ℚ₂`. -/
theorem twoAdicLocalTorsionLinearEquiv_galois (n : ℕ) [NeZero n]
    (σ : Γ ℚ_[2])
    (P : AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod n)
        (AddSubgroup.torsionBy
          ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    E.twoAdicLocalTorsionLinearEquiv n
        (E.nTorsionMap n
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ).toAlgHom P) =
      (E.baseChange ℚ_[2]).nTorsionMap n σ.toAlgHom
        (E.twoAdicLocalTorsionLinearEquiv n P) := by
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy
        ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  change (E.twoAdicBaseChangePointEquiv.torsionByLinearEquiv n)
      (E.twoAdicTorsionLinearEquiv n
        (E.nTorsionMap n
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ).toAlgHom P)) =
    (E.baseChange ℚ_[2]).nTorsionMap n σ.toAlgHom
      ((E.twoAdicBaseChangePointEquiv.torsionByLinearEquiv n)
        (E.twoAdicTorsionLinearEquiv n P))
  calc
    _ = (E.twoAdicBaseChangePointEquiv.torsionByLinearEquiv n)
        (E.nTorsionMap n (σ.toAlgHom.restrictScalars ℚ)
          (E.twoAdicTorsionLinearEquiv n P)) :=
      congrArg (E.twoAdicBaseChangePointEquiv.torsionByLinearEquiv n)
        (E.twoAdicTorsionLinearEquiv_galois n σ P)
    _ = _ := by
      let reassoc :
          ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point ≃+
            (E⁄(AlgebraicClosure ℚ_[2])).Point :=
        Affine.Point.equivOfEq
          (E.baseChange_map_algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))
      have hnat
          (Q : ((E.baseChange ℚ_[2])⁄(AlgebraicClosure ℚ_[2])).Point) :
          reassoc (WeierstrassCurve.Affine.Point.map σ.toAlgHom Q) =
            WeierstrassCurve.Affine.Point.map (σ.toAlgHom.restrictScalars ℚ)
              (reassoc Q) := by
        cases Q with
        | zero =>
            change reassoc (0 : ((E.baseChange ℚ_[2])⁄
                (AlgebraicClosure ℚ_[2])).Point) =
              WeierstrassCurve.Affine.Point.map (σ.toAlgHom.restrictScalars ℚ)
                (reassoc (0 : ((E.baseChange ℚ_[2])⁄
                  (AlgebraicClosure ℚ_[2])).Point))
            simp only [map_zero]
        | some x y hxy =>
            change (Affine.Point.equivOfEq
                (E.baseChange_map_algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])))
                  (WeierstrassCurve.Affine.Point.map σ.toAlgHom
                    (Affine.Point.some x y hxy)) =
              WeierstrassCurve.Affine.Point.map (σ.toAlgHom.restrictScalars ℚ)
                ((Affine.Point.equivOfEq
                  (E.baseChange_map_algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])))
                    (Affine.Point.some x y hxy))
            rw [WeierstrassCurve.Affine.Point.map_some,
              WeierstrassCurve.Affine.Point.equivOfEq_some,
              WeierstrassCurve.Affine.Point.equivOfEq_some,
              WeierstrassCurve.Affine.Point.map_some]
            exact Affine.Point.some_eq_some _ rfl rfl
      apply Subtype.ext
      change reassoc.symm
          (WeierstrassCurve.Affine.Point.map (σ.toAlgHom.restrictScalars ℚ)
            (E.twoAdicTorsionLinearEquiv n P).1) =
        WeierstrassCurve.Affine.Point.map σ.toAlgHom
          (reassoc.symm (E.twoAdicTorsionLinearEquiv n P).1)
      apply reassoc.injective
      rw [reassoc.apply_symm_apply, hnat, reassoc.apply_symm_apply]

/-- In the split-multiplicative branch, the Tate component map gives a surjective quotient
with trivial rank-one Galois action. -/
theorem twoAdicTorsion_hasTameQuadraticQuotient_of_split
    (n : ℕ) [NeZero n] [NeZero (n : ℚ)] (hn : 0 < n)
    [(E.baseChange ℚ_[2]).HasSplitMultiplicativeReduction 𝒪[ℚ_[2]]] :
    GaloisRepresentation.GaloisRep.HasTameQuadraticQuotientAtTwo
      (E.galoisRep n hn) := by
  let Ω := AlgebraicClosure ℚ_[2]
  let Elocal := E.baseChange ℚ_[2]
  letI : NeZero (n : Ω) := ⟨by exact_mod_cast NeZero.ne n⟩
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod n)
      (AddSubgroup.torsionBy (Elocal⁄Ω).Point (n : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let e := E.twoAdicLocalTorsionLinearEquiv n
  let q := Elocal.tateComponentLinearMap Ω n
  let π : AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (n : ℤ) →ₗ[ZMod n]
      ZMod n := q.comp e.toLinearMap
  let δ := trivialRankOneGaloisRep ℚ_[2] n
  refine ⟨π, ?_, δ, ?_⟩
  · exact (Elocal.tateComponentLinearMap_surjective Ω n).comp e.surjective
  · intro σ P
    refine ⟨?_, ?_, ?_⟩
    · change q (e (E.nTorsionMap n
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ).toAlgHom P)) =
        δ σ (q (e P))
      rw [E.twoAdicLocalTorsionLinearEquiv_galois n σ P]
      exact Elocal.tateComponentLinearMap_nTorsionMap Ω n σ (e P)
    · intro τ _hτ
      change δ τ = 1
      apply LinearMap.ext
      intro x
      rfl
    · intro τ
      apply LinearMap.ext
      intro x
      rfl

/-- In the nonsplit-multiplicative branch, the unramified quadratic twist supplied by
reduction theory makes the curve split. Its Tate component map descends to a quotient
carrying the associated unramified quadratic character. -/
theorem twoAdicTorsion_hasTameQuadraticQuotient_of_nonsplit
    (N : ℕ) [NeZero N] [NeZero (N : ℚ)] (hN : 0 < N)
    [(E.baseChange ℚ_[2]).HasMultiplicativeReduction 𝒪[ℚ_[2]]]
    (hnsplit : ¬(E.baseChange ℚ_[2]).HasSplitMultiplicativeReduction 𝒪[ℚ_[2]]) :
    GaloisRepresentation.GaloisRep.HasTameQuadraticQuotientAtTwo
      (E.galoisRep N hN) := by
  let Ω := AlgebraicClosure ℚ_[2]
  let Elocal := E.baseChange ℚ_[2]
  have hd : Elocal.UnramifiedQuadraticTwistData 𝒪[ℚ_[2]] :=
    Elocal.exists_unramified_quadraticTwist_hasSplitMultiplicativeReduction
      𝒪[ℚ_[2]] hnsplit
  unfold WeierstrassCurve.UnramifiedQuadraticTwistData at hd
  obtain ⟨L, hfield, halgebra, hquadratic, hseparable, halgebraR, htower,
      θ, t, n, _hθint, hθbase, htrace, hnorm, hdisc, hsplit⟩ := hd
  let ι : L →ₐ[ℚ_[2]] Ω := IsAlgClosed.lift
  letI : Algebra L Ω := ι.toRingHom.toAlgebra
  have halgι : algebraMap L Ω = ι := RingHom.algebraMap_toAlgebra _
  letI : IsScalarTower ℚ_[2] L Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halgι]
    exact (ι.commutes x).symm
  let Et := Elocal.quadraticTwist L
  let C := (Et.exists_isMinimal 𝒪[ℚ_[2]]).choose
  letI : (C • Et).HasSplitMultiplicativeReduction 𝒪[ℚ_[2]] := by
    exact hsplit
  letI : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (Elocal⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let e := E.twoAdicLocalTorsionLinearEquiv N
  let q := quadraticTwistTateComponentLinearMap (L := L) Ω Elocal C N
  let π : AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point (N : ℤ) →ₗ[ZMod N]
      ZMod N := q.comp e.toLinearMap
  let δ := quadraticCharacterGaloisRep ℚ_[2] L N
  refine ⟨π, ?_, δ, ?_⟩
  · exact (quadraticTwistTateComponentLinearMap_surjective
      (L := L) Ω Elocal C N).comp e.surjective
  · intro σ P
    refine ⟨?_, ?_, ?_⟩
    · change q (e (E.nTorsionMap N
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ).toAlgHom P)) =
        δ σ (q (e P))
      rw [E.twoAdicLocalTorsionLinearEquiv_galois N σ P]
      simpa [q, δ, quadraticCharacterGaloisRep_apply] using
        (quadraticTwistTateComponentLinearMap_nTorsionMap
          (L := L) Ω Elocal C N σ (e P))
    · intro τ hτ
      change δ τ = 1
      exact GaloisRepresentation.quadraticCharacterGaloisRep_eq_one_on_inertia
        N L θ t n hθbase htrace hnorm hdisc τ hτ
    · exact quadraticCharacterGaloisRep_mul_self ℚ_[2] L N

end WeierstrassCurve

namespace FreyCurve

/-- The `p`-torsion representation of a Frey curve has the required tame quadratic quotient
at `2`. The split branch uses the trivial character; the nonsplit branch uses the unramified
quadratic character supplied by the node polynomial. -/
theorem torsion_hasTameQuadraticQuotientAtTwo (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRepresentation.GaloisRep.HasTameQuadraticQuotientAtTwo
      (P.freyCurve.galoisRep P.p P.hppos) := by
  letI : Fact P.p.Prime := ⟨P.pp⟩
  letI : NeZero P.p := ⟨P.pp.ne_zero⟩
  letI : NeZero (P.p : ℚ) := ⟨by exact_mod_cast P.pp.ne_zero⟩
  letI hmult : (P.freyCurve.baseChange ℚ_[2]).HasMultiplicativeReduction 𝒪[ℚ_[2]] :=
    hasMultiplicativeReduction_at_two_padic P
  by_cases hsplit :
      (P.freyCurve.baseChange ℚ_[2]).HasSplitMultiplicativeReduction 𝒪[ℚ_[2]]
  · letI : (P.freyCurve.baseChange ℚ_[2]).HasSplitMultiplicativeReduction 𝒪[ℚ_[2]] :=
      hsplit
    exact P.freyCurve.twoAdicTorsion_hasTameQuadraticQuotient_of_split P.p P.hppos
  · exact P.freyCurve.twoAdicTorsion_hasTameQuadraticQuotient_of_nonsplit
      P.p P.hppos hsplit

end FreyCurve
