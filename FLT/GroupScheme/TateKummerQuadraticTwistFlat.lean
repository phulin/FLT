/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.TateKummerQuadraticTwistTorsion
public import Mathlib.RingTheory.Etale.Descent

/-!
# Finite-flat quadratic twists of Tate--Kummer models

This file packages the geometric properties of the quadratic descent constructed in
`TateKummerQuadraticTwist`.  The first step is generic-fiber etaleness: after the
faithfully flat quadratic field extension, the descended algebra is the ordinary
Tate--Kummer generic fiber, so etaleness descends.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace TateKummer.QuadraticTwist

variable (R : Type u) [CommRing R]
variable (N : ℕ) [NeZero N] (u₀ : Rˣ) (t n : R)
variable (K L : Type u) [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra.IsQuadraticExtension K L]

set_option backward.isDefEq.respectTransparency false

/-- The generic fiber of the descended quadratic-twist coordinate algebra is etale.

The quadratic splitting field is faithfully flat over the generic-fiber field.  Over
that field the explicit descent equivalence identifies the algebra with the split
Tate--Kummer generic fiber, whose etaleness was proved componentwise. -/
theorem genericFiberEtale
    [NeZero (N : K)]
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    Algebra.Etale K (K ⊗[R] fixedSubalgebra R N u₀ t n) := by
  letI : NeZero (N : L) := ⟨by
    intro h
    apply NeZero.ne (N : K)
    apply (algebraMap K L).injective
    simpa using h⟩
  letI : CommRing (K ⊗[R] fixedSubalgebra R N u₀ t n) := by
    infer_instance
  letI : Algebra K (K ⊗[R] fixedSubalgebra R N u₀ t n) :=
    Algebra.TensorProduct.leftAlgebra
  letI : CommRing
      (L ⊗[K] (K ⊗[R] fixedSubalgebra R N u₀ t n)) := by
    infer_instance
  letI : Algebra L
      (L ⊗[K] (K ⊗[R] fixedSubalgebra R N u₀ t n)) :=
    Algebra.TensorProduct.leftAlgebra
  let e := genericFiberFieldExtendedCoverEquiv R N u₀ t n K L θ
    htrace hnorm h2 hdisc
  letI : Algebra.Etale L
      (L ⊗[R] TateKummer.CoordinateAlgebra (R := R) N u₀) :=
    TateKummer.coordinateGenericFiberEtale L N u₀
  letI : Algebra.Etale L
      (L ⊗[K] (K ⊗[R] fixedSubalgebra R N u₀ t n)) :=
    Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L

/-! ## Galois action on the split point -/

/-- Conjugate only the quadratic coefficient in the scalar extension of the fixed
algebra. -/
noncomputable def baseChangeCoefficientConjugation :
    (QuadraticDescent.Algebra R t n ⊗[R]
      fixedSubalgebra R N u₀ t n) ≃ₐ[R]
    (QuadraticDescent.Algebra R t n ⊗[R]
      fixedSubalgebra R N u₀ t n) :=
  Algebra.TensorProduct.congr
    (QuadraticDescent.conjugationAlgEquiv R t n) (AlgEquiv.refl)

/-- Coefficient conjugation before the splitting equivalence becomes the full descent
involution on the cover. -/
lemma baseChangeEquiv_coefficientConjugation
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : QuadraticDescent.Algebra R t n ⊗[R]
      fixedSubalgebra R N u₀ t n) :
    baseChangeEquiv R N u₀ t n h2 hdisc
        (baseChangeCoefficientConjugation R N u₀ t n z) =
      descentAlgEquiv R N u₀ t n
        (baseChangeEquiv R N u₀ t n h2 hdisc z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z =>
      rw [show baseChangeCoefficientConjugation R N u₀ t n
        (a ⊗ₜ[R] z) =
          QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R] z from rfl]
      simp only [baseChangeEquiv_apply, baseChangeToCover_tmul,
        descentAlgEquiv_algebraMap_cover, map_mul]
      rw [(mem_fixedSubalgebra R N u₀ t n z).mp z.property]

/-- On an element coming from the split Tate--Kummer factor, coefficient conjugation
becomes its antipode after transport back through the splitting equivalence. -/
lemma coefficientConjugation_baseChangeEquiv_symm_one_tmul
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (h : TateKummer.CoordinateAlgebra (R := R) N u₀) :
    baseChangeCoefficientConjugation R N u₀ t n
        ((baseChangeEquiv R N u₀ t n h2 hdisc).symm
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] h)) =
      (baseChangeEquiv R N u₀ t n h2 hdisc).symm
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          TateKummer.antipodeAlgHom N u₀ h) := by
  apply (baseChangeEquiv R N u₀ t n h2 hdisc).injective
  rw [baseChangeEquiv_coefficientConjugation,
    (baseChangeEquiv R N u₀ t n h2 hdisc).apply_symm_apply,
    (baseChangeEquiv R N u₀ t n h2 hdisc).apply_symm_apply]
  rw [descentAlgEquiv_tmul, map_one,
    TateKummer.antipodeAlgEquiv_apply]

section GaloisPoints

variable (S : Type v) [Field S]
  [Algebra R S] [Algebra K S] [Algebra L S]
  [IsScalarTower R K S] [IsScalarTower R L S]

/-- A nontrivial automorphism of a separable quadratic extension sends a generator to
its trace conjugate. -/
lemma restrictNormal_apply_quadraticGenerator
    [Algebra.IsSeparable K L] [IsScalarTower K L S]
    (θ : L) (hθ : θ ∉ Set.range (algebraMap K L))
    (σ : S ≃ₐ[K] S)
    (hσ : ¬ ∀ x : L, σ (algebraMap L S x) = algebraMap L S x) :
    σ.restrictNormal L θ =
      algebraMap K L (Algebra.trace K L θ) - θ := by
  let τ := σ.restrictNormal L
  have hτ : τ ≠ 1 := fun h ↦ hσ
    ((forall_apply_algebraMap_iff_restrictNormal_eq_one K L S σ).2 h)
  have hτθne : τ θ ≠ θ :=
    Algebra.IsQuadraticExtension.algEquiv_apply_ne K L hτ hθ
  have hθpoly := sq_sub_trace_mul_self_add_norm
    (Algebra.IsQuadraticExtension.finrank_eq_two K L) θ
  have hτpoly := congrArg τ hθpoly
  simp only [map_sub, map_pow, map_mul, map_add, map_zero, τ.commutes] at hτpoly
  have hfactor : (τ θ - θ) *
      (τ θ + θ - algebraMap K L (Algebra.trace K L θ)) = 0 := by
    linear_combination hτpoly - hθpoly
  have hz := (mul_eq_zero.mp hfactor).resolve_left
    (sub_ne_zero.mpr hτθne)
  linear_combination hz

/-- Under an automorphism not fixing the quadratic field, evaluation at the chosen
generator is changed by conjugating the integral trace--norm algebra. -/
lemma map_integralFieldAlgHom_of_not_fixed
    [Algebra.IsSeparable K L] [IsScalarTower K L S]
    (θ : L) (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (σ : S ≃ₐ[K] S)
    (hσ : ¬ ∀ x : L, σ (algebraMap L S x) = algebraMap L S x)
    (a : QuadraticDescent.Algebra R t n) :
    σ (algebraMap L S
        (QuadraticDescent.integralFieldAlgHom K L R t n θ
          htrace hnorm a)) =
      algebraMap L S
        (QuadraticDescent.integralFieldAlgHom K L R t n θ htrace hnorm
          (QuadraticDescent.conjugationAlgHom R t n a)) := by
  let f := QuadraticDescent.integralFieldAlgHom K L R t n θ htrace hnorm
  let i : QuadraticDescent.Algebra R t n →ₐ[R] S :=
    (IsScalarTower.toAlgHom R L S).comp f
  have hroot : σ (i (AdjoinRoot.root
      (QuadraticDescent.polynomial R t n))) =
      i (QuadraticDescent.conjugationAlgHom R t n
        (AdjoinRoot.root (QuadraticDescent.polynomial R t n))) := by
    change σ (algebraMap L S (f (AdjoinRoot.root
      (QuadraticDescent.polynomial R t n)))) =
      algebraMap L S (f (QuadraticDescent.conjugationAlgHom R t n
        (AdjoinRoot.root (QuadraticDescent.polynomial R t n))))
    rw [QuadraticDescent.integralFieldAlgHom_root,
      QuadraticDescent.conjugationAlgHom_root,
      QuadraticDescent.conjugateRoot, map_sub,
      QuadraticDescent.integralFieldAlgHom_root]
    rw [show f (AdjoinRoot.of (QuadraticDescent.polynomial R t n) t) =
      algebraMap R L t from f.commutes t]
    rw [← AlgEquiv.restrictNormal_commutes σ L θ,
      restrictNormal_apply_quadraticGenerator K L S θ hθ σ hσ,
      map_sub, map_sub]
    rw [htrace, IsScalarTower.algebraMap_apply R K L]
  have hm : (σ.restrictScalars R).toAlgHom.comp i =
      i.comp (QuadraticDescent.conjugationAlgHom R t n) := by
    apply AdjoinRoot.algHom_ext
    exact hroot
  exact DFunLike.congr_fun hm a

/-- If the value-field automorphism fixes the quadratic splitting field, transporting a
descended point to the split coordinate algebra commutes with that automorphism. -/
lemma genericFiberSplitAlgHomEquiv_comp_of_fixed
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (σ : S ≃ₐ[K] S)
    (hσ : ∀ x : L, σ (algebraMap L S x) = algebraMap L S x)
    (φ : K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S) :
    genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ
        htrace hnorm h2 hdisc (σ.toAlgHom.comp φ) =
      (σ.restrictScalars R).toAlgHom.comp
        (genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ
          htrace hnorm h2 hdisc φ) := by
  let f := QuadraticDescent.integralFieldAlgHom K L R t n θ htrace hnorm
  let g : QuadraticDescent.Algebra R t n →+* S :=
    (algebraMap L S).comp f.toRingHom
  letI : Algebra (QuadraticDescent.Algebra R t n) S := g.toAlgebra
  letI : IsScalarTower R (QuadraticDescent.Algebra R t n) S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R S r = algebraMap L S (f (algebraMap R
        (QuadraticDescent.Algebra R t n) r))
      rw [f.commutes, IsScalarTower.algebraMap_apply R L S]
  let eK := Algebra.TensorProduct.liftEquivRight R K
    (fixedSubalgebra R N u₀ t n) S
  let eA := Algebra.TensorProduct.liftEquivRight R
    (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u₀ t n) S
  let eH := Algebra.TensorProduct.liftEquivRight R
    (QuadraticDescent.Algebra R t n)
      (TateKummer.CoordinateAlgebra (R := R) N u₀) S
  let eCover := AlgEquiv.arrowCongr
    (baseChangeEquiv R N u₀ t n h2 hdisc)
    (AlgEquiv.refl : S ≃ₐ[QuadraticDescent.Algebra R t n] S)
  let p := eH.symm (eCover (eA (eK.symm φ)))
  have hσA (a : QuadraticDescent.Algebra R t n) :
      σ (algebraMap (QuadraticDescent.Algebra R t n) S a) =
        algebraMap (QuadraticDescent.Algebra R t n) S a := by
    change σ (algebraMap L S (f a)) = algebraMap L S (f a)
    exact hσ (f a)
  let σA : S ≃ₐ[QuadraticDescent.Algebra R t n] S :=
    { σ.toRingEquiv with commutes' := hσA }
  have heA : eA (eK.symm (σ.toAlgHom.comp φ)) =
      σA.toAlgHom.comp (eA (eK.symm φ)) := by
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
        change algebraMap (QuadraticDescent.Algebra R t n) S a *
            σ ((eK.symm φ) b) =
          σ (algebraMap (QuadraticDescent.Algebra R t n) S a *
            (eK.symm φ) b)
        rw [map_mul, hσA]
  change eH.symm (eCover (eA (eK.symm (σ.toAlgHom.comp φ)))) =
    (σ.restrictScalars R).toAlgHom.comp p
  apply AlgHom.ext
  intro h
  change _ = σ (p h)
  rw [heA]
  rfl

/-- If the automorphism conjugates the quadratic field, split transport turns it into
postcomposition by that automorphism together with inversion on Tate--Kummer points. -/
lemma genericFiberSplitAlgHomEquiv_comp_of_not_fixed
    [Algebra.IsSeparable K L] [IsScalarTower K L S]
    (θ : L) (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (σ : S ≃ₐ[K] S)
    (hσ : ¬ ∀ x : L, σ (algebraMap L S x) = algebraMap L S x)
    (φ : K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S) :
    genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ
        htrace hnorm h2 hdisc (σ.toAlgHom.comp φ) =
      (σ.restrictScalars R).toAlgHom.comp
        ((genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ
          htrace hnorm h2 hdisc φ).comp
            (TateKummer.antipodeAlgHom N u₀)) := by
  let f := QuadraticDescent.integralFieldAlgHom K L R t n θ htrace hnorm
  let g : QuadraticDescent.Algebra R t n →+* S :=
    (algebraMap L S).comp f.toRingHom
  letI : Algebra (QuadraticDescent.Algebra R t n) S := g.toAlgebra
  letI : IsScalarTower R (QuadraticDescent.Algebra R t n) S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R S r = algebraMap L S (f (algebraMap R
        (QuadraticDescent.Algebra R t n) r))
      rw [f.commutes, IsScalarTower.algebraMap_apply R L S]
  let eK := Algebra.TensorProduct.liftEquivRight R K
    (fixedSubalgebra R N u₀ t n) S
  let eA := Algebra.TensorProduct.liftEquivRight R
    (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u₀ t n) S
  let eH := Algebra.TensorProduct.liftEquivRight R
    (QuadraticDescent.Algebra R t n)
      (TateKummer.CoordinateAlgebra (R := R) N u₀) S
  let eCover := AlgEquiv.arrowCongr
    (baseChangeEquiv R N u₀ t n h2 hdisc)
    (AlgEquiv.refl : S ≃ₐ[QuadraticDescent.Algebra R t n] S)
  let p := eH.symm (eCover (eA (eK.symm φ)))
  have hσA (a : QuadraticDescent.Algebra R t n) :
      σ (algebraMap (QuadraticDescent.Algebra R t n) S a) =
        algebraMap (QuadraticDescent.Algebra R t n) S
          (QuadraticDescent.conjugationAlgHom R t n a) := by
    exact map_integralFieldAlgHom_of_not_fixed R t n K L S
      θ hθ htrace hnorm σ hσ a
  have heA (z : QuadraticDescent.Algebra R t n ⊗[R]
      fixedSubalgebra R N u₀ t n) :
      eA (eK.symm (σ.toAlgHom.comp φ)) z =
        σ (eA (eK.symm φ)
          (baseChangeCoefficientConjugation R N u₀ t n z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
        change algebraMap (QuadraticDescent.Algebra R t n) S a *
            σ ((eK.symm φ) b) =
          σ (algebraMap (QuadraticDescent.Algebra R t n) S
            (QuadraticDescent.conjugationAlgEquiv R t n a) *
              (eK.symm φ) b)
        rw [map_mul, hσA,
          QuadraticDescent.conjugationAlgEquiv_apply,
          QuadraticDescent.conjugationAlgHom_involutive]
  change eH.symm (eCover (eA (eK.symm (σ.toAlgHom.comp φ)))) =
    (σ.restrictScalars R).toAlgHom.comp
      (p.comp (TateKummer.antipodeAlgHom N u₀))
  apply AlgHom.ext
  intro h
  change eA (eK.symm (σ.toAlgHom.comp φ))
      ((baseChangeEquiv R N u₀ t n h2 hdisc).symm
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] h)) =
    σ (p (TateKummer.antipodeAlgHom N u₀ h))
  rw [heA, coefficientConjugation_baseChangeEquiv_symm_one_tmul]
  rfl

/-- In the fixed-embedding case, the Kummer point classification is Galois natural. -/
lemma genericFiberAlgHomUnitEquiv_comp_of_fixed
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (σ : S ≃ₐ[K] S)
    (hσ : ∀ x : L, σ (algebraMap L S x) = algebraMap L S x)
    (φ : K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S) :
    genericFiberAlgHomUnitEquiv R N u₀ t n K L S θ htrace hnorm h2 hdisc
        (σ.toAlgHom.comp φ) =
      TateKummer.kummerUnitPointMap R S N u₀ (σ.restrictScalars R)
        (genericFiberAlgHomUnitEquiv R N u₀ t n K L S θ
          htrace hnorm h2 hdisc φ) := by
  change TateKummer.coordinateAlgHomUnitEquiv R S N u₀
      (genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ htrace hnorm
        h2 hdisc (σ.toAlgHom.comp φ)) = _
  rw [genericFiberSplitAlgHomEquiv_comp_of_fixed R N u₀ t n K L S
    θ htrace hnorm h2 hdisc σ hσ φ]
  exact TateKummer.coordinateAlgHomUnitEquiv_comp R S N u₀
    (σ.restrictScalars R)
    (genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ
      htrace hnorm h2 hdisc φ)

/-- In the conjugate-embedding case, the Kummer point is Galois conjugated and
inverted. -/
lemma genericFiberAlgHomUnitEquiv_comp_of_not_fixed
    [Algebra.IsSeparable K L] [IsScalarTower K L S]
    (θ : L) (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (σ : S ≃ₐ[K] S)
    (hσ : ¬ ∀ x : L, σ (algebraMap L S x) = algebraMap L S x)
    (φ : K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S) :
    genericFiberAlgHomUnitEquiv R N u₀ t n K L S θ htrace hnorm h2 hdisc
        (σ.toAlgHom.comp φ) =
      TateKummer.kummerUnitPointMap R S N u₀ (σ.restrictScalars R)
        (TateKummer.coordinateAlgHomUnitEquiv R S N u₀
          ((genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ
            htrace hnorm h2 hdisc φ).comp
              (TateKummer.antipodeAlgHom N u₀))) := by
  change TateKummer.coordinateAlgHomUnitEquiv R S N u₀
      (genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ htrace hnorm
        h2 hdisc (σ.toAlgHom.comp φ)) = _
  rw [genericFiberSplitAlgHomEquiv_comp_of_not_fixed R N u₀ t n K L S
    θ hθ htrace hnorm h2 hdisc σ hσ φ]
  exact TateKummer.coordinateAlgHomUnitEquiv_comp R S N u₀
    (σ.restrictScalars R)
    ((genericFiberSplitAlgHomEquiv R N u₀ t n K L S θ
      htrace hnorm h2 hdisc φ).comp (TateKummer.antipodeAlgHom N u₀))

end GaloisPoints

end TateKummer.QuadraticTwist

namespace WeierstrassCurve

open ValuativeRel
open scoped WeierstrassCurve.Affine

section CurveTorsion

variable (R : Type u) [CommRing R] [IsDomain R]
variable (K L : Type u) [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
variable (S : Type v) [Field S]
  [Algebra R S] [Algebra K S] [Algebra L S]
  [IsScalarTower R K S] [IsScalarTower R L S] [IsScalarTower K L S]
  [IsSepClosed S] [Algebra.IsSeparable K S]
  [DecidableEq K] [DecidableEq S]
variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Geometric points of the descended Tate--Kummer model, identified with torsion on
the split quadratic twist through Tate uniformization. -/
noncomputable def quadraticTateKummerTorsionAddEquiv
    (W : WeierstrassCurve K) [W.IsElliptic]
    [W.HasSplitMultiplicativeReduction 𝒪[K]]
    (N : ℕ) [NeZero N] (u₀ : Rˣ) (t n : R)
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u₀ = W.qUnitSepClosure S) :
    letI := TateKummer.QuadraticTwist.coordinateBialgebra
      R N u₀ t n h2 hdisc
    Additive (WithConv
      (K ⊗[R] TateKummer.QuadraticTwist.fixedSubalgebra R N u₀ t n →ₐ[K] S)) ≃+
        AddSubgroup.torsionBy (W⁄S).Point (N : ℤ) := by
  letI := TateKummer.QuadraticTwist.coordinateBialgebra
    R N u₀ t n h2 hdisc
  let e := W.tateTorsionLinearEquiv S N
  let eAdd : AddSubgroup.torsionBy
        (Additive (Sˣ ⧸ Subgroup.zpowers (W.qUnitSepClosure S))) (N : ℤ) ≃+
      AddSubgroup.torsionBy (W⁄S).Point (N : ℤ) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add }
  exact (TateKummer.QuadraticTwist.genericFiberTorsionAddEquiv
    R N u₀ t n K L S θ htrace hnorm h2 hdisc
      (W.qUnitSepClosure S) a hq
      (W.qUnitSepClosure_zpow_injective S)).trans eAdd

variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (C : WeierstrassCurve.VariableChange K)
variable [((C • E.quadraticTwist L)).HasSplitMultiplicativeReduction 𝒪[K]]

/-- The descended model's geometric points, identified with torsion on the original
nonsplit-multiplicative curve.  This composes Tate uniformization on the split quadratic
twist with the quadratic-twist point equivalence. -/
noncomputable def quadraticTwistTateKummerTorsionAddEquiv
    (N : ℕ) [NeZero N] (u₀ : Rˣ) (t n : R)
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u₀ =
      (C • E.quadraticTwist L).qUnitSepClosure S) :
    letI := TateKummer.QuadraticTwist.coordinateBialgebra
      R N u₀ t n h2 hdisc
    Additive (WithConv
      (K ⊗[R] TateKummer.QuadraticTwist.fixedSubalgebra R N u₀ t n →ₐ[K] S)) ≃+
        AddSubgroup.torsionBy (E⁄S).Point (N : ℤ) := by
  letI := TateKummer.QuadraticTwist.coordinateBialgebra
    R N u₀ t n h2 hdisc
  let e := quadraticTwistTateTorsionLinearEquiv (L := L) S E C N
  let eAdd : AddSubgroup.torsionBy
        (((C • E.quadraticTwist L))⁄S).Point (N : ℤ) ≃+
      AddSubgroup.torsionBy (E⁄S).Point (N : ℤ) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add }
  exact (quadraticTateKummerTorsionAddEquiv R K L S
    (C • E.quadraticTwist L) N u₀ t n θ htrace hnorm h2 hdisc a hq).trans eAdd

end CurveTorsion

end WeierstrassCurve
