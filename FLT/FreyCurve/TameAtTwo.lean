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

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

noncomputable local instance : DecidableEq (AlgebraicClosure ℚ_[2]) :=
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
            simp only [map_zero, WeierstrassCurve.Affine.Point.map_zero]
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

end WeierstrassCurve
