/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.DualNumber
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Relative cotangent functionals from dual-number points

An algebra map `D → k[ε]` has a residue component `D → k` and an infinitesimal
component.  The latter is an `R`-derivation, hence a linear functional on the relative
cotangent space `k ⊗[D] Ω[D/R]`.  This file packages that standard passage independently
of deformation theory.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Deformation

variable {R D k : Type u} [CommRing R] [CommRing D] [Field k]
  [Algebra R D] [Algebra R k]

/-- The residue component of an algebra map to the dual numbers. -/
noncomputable def dualNumberAugmentation (f : D →ₐ[R] DualNumber k) : D →ₐ[R] k :=
  (TrivSqZeroExt.fstHom R k k).comp f

@[simp]
lemma dualNumberAugmentation_apply (f : D →ₐ[R] DualNumber k) (x : D) :
    dualNumberAugmentation f x = (f x).fst :=
  rfl

/-- The infinitesimal component of a map to the dual numbers, regarded as a derivation
relative to the coefficient ring. -/
noncomputable def dualNumberDerivation (f : D →ₐ[R] DualNumber k) :
    letI : Algebra D k := (dualNumberAugmentation f).toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' (dualNumberAugmentation f).comp_algebraMap.symm
    Derivation R D k := by
  let aug := dualNumberAugmentation f
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  refine
    { toLinearMap :=
        (TrivSqZeroExt.sndHom k k).restrictScalars R ∘ₗ f.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := ?_ }
  intro x y
  change (f (x * y)).snd = aug x * (f y).snd + aug y * (f x).snd
  rw [map_mul, TrivSqZeroExt.snd_mul]
  simp only [aug, dualNumberAugmentation_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  rw [smul_eq_mul]
  ac_rfl

@[simp]
lemma dualNumberDerivation_apply (f : D →ₐ[R] DualNumber k) (x : D) :
    letI : Algebra D k := (dualNumberAugmentation f).toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' (dualNumberAugmentation f).comp_algebraMap.symm
    dualNumberDerivation f x = (f x).snd :=
  by simp [dualNumberDerivation]

/-- The relative cotangent space at an augmentation `D → k`. -/
noncomputable abbrev RelativeCotangentSpace (aug : D →ₐ[R] k) : Type u :=
  letI : Algebra D k := aug.toAlgebra
  k ⊗[D] KaehlerDifferential R D
/-- The universal relative derivation into the cotangent space at `aug`. -/
noncomputable def relativeCotangentDerivation (aug : D →ₐ[R] k) :
    letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    Derivation R D (RelativeCotangentSpace aug) := by
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  exact (TensorProduct.mk D k (KaehlerDifferential R D) 1).compDer
    (KaehlerDifferential.D R D)

/-- Universal differentials span the relative cotangent space over the target field. -/
theorem relativeCotangent_span_range_derivation_eq_top (aug : D →ₐ[R] k) :
    letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    Submodule.span k (Set.range (relativeCotangentDerivation aug)) = ⊤ := by
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  rw [eq_top_iff]
  intro z hz
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a omega =>
      have homega : omega ∈
          Submodule.span D (Set.range (KaehlerDifferential.D R D)) := by
        rw [KaehlerDifferential.span_range_derivation]
        trivial
      refine Submodule.span_induction
        (p := fun omega _ ↦ ∀ a : k,
          a ⊗ₜ[D] omega ∈
            Submodule.span k (Set.range (relativeCotangentDerivation aug)))
        ?_ ?_ ?_ ?_ homega a
      · rintro _ ⟨x, rfl⟩ a
        have hx : relativeCotangentDerivation aug x ∈
            Submodule.span k (Set.range (relativeCotangentDerivation aug)) :=
          Submodule.subset_span (Set.mem_range_self x)
        have heq :
            a ⊗ₜ[D] KaehlerDifferential.D R D x =
              a • (1 ⊗ₜ[D] KaehlerDifferential.D R D x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [heq]
        exact Submodule.smul_mem _ a hx
      · intro a
        simp
      · intro x y _ _ hx hy a
        simpa only [TensorProduct.tmul_add] using Submodule.add_mem _ (hx a) (hy a)
      · intro d omega _ homega a
        rw [TensorProduct.tmul_smul]
        exact homega (d • a)

/-- If the coefficient map onto `k` is surjective, every cotangent vector is represented
by the universal differential of a single element of `D`.  This is the parameter-lifting
step used after choosing vectors dual to a tangent basis. -/
theorem relativeCotangentDerivation_surjective
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k)) :
    letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    Function.Surjective (relativeCotangentDerivation aug) := by
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  intro y
  have hy : y ∈ Submodule.span k
      (Set.range (relativeCotangentDerivation aug)) := by
    rw [relativeCotangent_span_range_derivation_eq_top aug]
    trivial
  refine Submodule.span_induction (p := fun y _ ↦
    ∃ x : D, relativeCotangentDerivation aug x = y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · exact ⟨0, map_zero _⟩
  · rintro x y _ _ ⟨x', rfl⟩ ⟨y', rfl⟩
    exact ⟨x' + y', map_add _ _ _⟩
  · rintro c y _ ⟨x, rfl⟩
    obtain ⟨r, rfl⟩ := hRk c
    refine ⟨algebraMap R D r * x, ?_⟩
    rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
    change aug (algebraMap R D r) • relativeCotangentDerivation aug x =
      algebraMap R k r • relativeCotangentDerivation aug x
    rw [aug.commutes]

/-- The cotangent functional associated to a dual-number point. -/
noncomputable def dualNumberCotangentFunctional (f : D →ₐ[R] DualNumber k) :
    RelativeCotangentSpace (dualNumberAugmentation f) →ₗ[k] k := by
  let aug := dualNumberAugmentation f
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  exact (dualNumberDerivation f).liftKaehlerDifferential.liftBaseChange k

/-- Regard the cotangent functional as based at a propositionally equal chosen
augmentation.  This lets a family of dual-number points share one cotangent space. -/
noncomputable def dualNumberCotangentFunctionalAt
    (aug : D →ₐ[R] k) (f : D →ₐ[R] DualNumber k)
    (h : dualNumberAugmentation f = aug) :
    RelativeCotangentSpace aug →ₗ[k] k :=
  h ▸ dualNumberCotangentFunctional f

@[simp]
theorem dualNumberCotangentFunctional_tmul_D
    (f : D →ₐ[R] DualNumber k) (x : D) :
    let aug := dualNumberAugmentation f
    letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    dualNumberCotangentFunctional f
      (1 ⊗ₜ[D] KaehlerDifferential.D R D x) = (f x).snd :=
  let aug := dualNumberAugmentation f
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  by
    rw [dualNumberCotangentFunctional, LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D, dualNumberDerivation_apply]

@[simp]
theorem dualNumberCotangentFunctionalAt_tmul_D
    (aug : D →ₐ[R] k) (f : D →ₐ[R] DualNumber k)
    (h : dualNumberAugmentation f = aug) (x : D) :
    letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    dualNumberCotangentFunctionalAt aug f h
      (1 ⊗ₜ[D] KaehlerDifferential.D R D x) = (f x).snd := by
  subst aug
  exact dualNumberCotangentFunctional_tmul_D f x
/-- Reconstruct a dual-number point from an arbitrary functional on the relative cotangent
space.  Its infinitesimal component is the functional composed with the universal
derivation. -/
noncomputable def dualNumberAlgHomOfCotangentFunctional
    (aug : D →ₐ[R] k) (l : RelativeCotangentSpace aug →ₗ[k] k) :
    D →ₐ[R] DualNumber k := by
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  let d := relativeCotangentDerivation aug
  exact
    { toFun := fun x ↦ (aug x, l (d x))
      map_one' := by
        apply TrivSqZeroExt.ext
        · change aug 1 = 1
          exact map_one aug
        · change l (d 1) = 0
          rw [d.map_one_eq_zero, map_zero]
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · change aug (x * y) = aug x * aug y
          exact map_mul aug x y
        · change l (d (x * y)) =
            aug x * l (d y) + l (d x) * aug y
          rw [Derivation.leibniz]
          change l (aug x • d y + aug y • d x) =
            aug x * l (d y) + l (d x) * aug y
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
            mul_comm (aug y) (l (d x))]
      map_zero' := by
        apply TrivSqZeroExt.ext
        · change aug 0 = 0
          exact map_zero aug
        · change l (d 0) = 0
          rw [map_zero, map_zero]
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · change aug (x + y) = aug x + aug y
          exact map_add aug x y
        · change l (d (x + y)) = l (d x) + l (d y)
          rw [map_add, map_add]
      commutes' := by
        intro r
        apply TrivSqZeroExt.ext
        · exact aug.commutes r
        · change l (d (algebraMap R D r)) = 0
          rw [Derivation.map_algebraMap, map_zero] }

/-- The reconstructed point has the prescribed augmentation. -/
@[simp]
theorem dualNumberAugmentation_algHomOfCotangentFunctional
    (aug : D →ₐ[R] k) (l : RelativeCotangentSpace aug →ₗ[k] k) :
    dualNumberAugmentation (dualNumberAlgHomOfCotangentFunctional aug l) = aug := by
  apply AlgHom.ext
  intro x
  rfl

/-- The second coordinate of the reconstructed point is the chosen functional applied to
the universal differential. -/
@[simp]
theorem dualNumberAlgHomOfCotangentFunctional_snd
    (aug : D →ₐ[R] k) (l : RelativeCotangentSpace aug →ₗ[k] k) (x : D) :
    (dualNumberAlgHomOfCotangentFunctional aug l x).snd =
      l (relativeCotangentDerivation aug x) :=
  rfl

/-- Passing a reconstructed point back to its cotangent functional recovers the original
functional. -/
theorem dualNumberCotangentFunctionalAt_algHomOfCotangentFunctional
    (aug : D →ₐ[R] k) (l : RelativeCotangentSpace aug →ₗ[k] k) :
    dualNumberCotangentFunctionalAt aug
        (dualNumberAlgHomOfCotangentFunctional aug l)
        (dualNumberAugmentation_algHomOfCotangentFunctional aug l) = l := by
  letI : Algebra D k := aug.toAlgebra
  letI : IsScalarTower R D k :=
    IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
  apply LinearMap.ext_on_range
    (relativeCotangent_span_range_derivation_eq_top aug)
  intro x
  change dualNumberCotangentFunctionalAt aug
      (dualNumberAlgHomOfCotangentFunctional aug l)
      (dualNumberAugmentation_algHomOfCotangentFunctional aug l)
      (1 ⊗ₜ[D] KaehlerDifferential.D R D x) =
    l (1 ⊗ₜ[D] KaehlerDifferential.D R D x)
  rw [dualNumberCotangentFunctionalAt_tmul_D]
  rfl

/-- Two dual-number points over the same augmentation are equal as soon as their
cotangent functionals agree.  The first coordinates agree because both points reduce to
`aug`; the values of the functional on the universal differentials recover the second
coordinates. -/
theorem dualNumberAlgHom_ext_of_cotangentFunctionalAt_eq
    (aug : D →ₐ[R] k) (f g : D →ₐ[R] DualNumber k)
    (hf : dualNumberAugmentation f = aug)
    (hg : dualNumberAugmentation g = aug)
    (hfg : dualNumberCotangentFunctionalAt aug f hf =
      dualNumberCotangentFunctionalAt aug g hg) :
    f = g := by
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · change dualNumberAugmentation f x = dualNumberAugmentation g x
    rw [hf, hg]
  · letI : Algebra D k := aug.toAlgebra
    letI : IsScalarTower R D k :=
      IsScalarTower.of_algebraMap_eq' aug.comp_algebraMap.symm
    have hvalue := LinearMap.congr_fun hfg
      (1 ⊗ₜ[D] KaehlerDifferential.D R D x)
    simpa only [dualNumberCotangentFunctionalAt_tmul_D] using hvalue

/-- The cotangent-functional construction faithfully encodes dual-number points based at
a fixed augmentation. -/
theorem dualNumberCotangentFunctionalAt_injective (aug : D →ₐ[R] k) :
    Function.Injective fun f : {f : D →ₐ[R] DualNumber k //
        dualNumberAugmentation f = aug} ↦
      dualNumberCotangentFunctionalAt aug f.1 f.2 := by
  intro f g hfg
  apply Subtype.ext
  exact dualNumberAlgHom_ext_of_cotangentFunctionalAt_eq
    aug f.1 g.1 f.2 g.2 hfg

/-- Equality of based dual-number points is equivalent to equality of their cotangent
functionals. -/
theorem dualNumberCotangentFunctionalAt_eq_iff
    (aug : D →ₐ[R] k)
    (f g : {f : D →ₐ[R] DualNumber k // dualNumberAugmentation f = aug}) :
    dualNumberCotangentFunctionalAt aug f.1 f.2 =
        dualNumberCotangentFunctionalAt aug g.1 g.2 ↔
      f = g :=
  (dualNumberCotangentFunctionalAt_injective aug).eq_iff
/-- Based dual-number points are equivalent to the linear dual of the relative cotangent
space.  This is the algebraic tangent--cotangent correspondence used to transport linear
combinations of first-order deformations. -/
noncomputable def basedDualNumberPointCotangentEquiv (aug : D →ₐ[R] k) :
    {f : D →ₐ[R] DualNumber k // dualNumberAugmentation f = aug} ≃
      (RelativeCotangentSpace aug →ₗ[k] k) where
  toFun f := dualNumberCotangentFunctionalAt aug f.1 f.2
  invFun l :=
    ⟨dualNumberAlgHomOfCotangentFunctional aug l,
      dualNumberAugmentation_algHomOfCotangentFunctional aug l⟩
  left_inv f := by
    apply dualNumberCotangentFunctionalAt_injective aug
    exact dualNumberCotangentFunctionalAt_algHomOfCotangentFunctional aug
      (dualNumberCotangentFunctionalAt aug f.1 f.2)
  right_inv l :=
    dualNumberCotangentFunctionalAt_algHomOfCotangentFunctional aug l
/-- Transport the additive structure on cotangent functionals to based dual-number points. -/
noncomputable instance basedDualNumberPointAddCommGroup (aug : D →ₐ[R] k) :
    AddCommGroup {f : D →ₐ[R] DualNumber k // dualNumberAugmentation f = aug} :=
  Equiv.addCommGroup (basedDualNumberPointCotangentEquiv aug)

/-- Transport the residue-field scalar action along the tangent--cotangent equivalence. -/
noncomputable instance basedDualNumberPointModule (aug : D →ₐ[R] k) :
    Module k {f : D →ₐ[R] DualNumber k // dualNumberAugmentation f = aug} :=
  Equiv.module k (basedDualNumberPointCotangentEquiv aug)

/-- The tangent--cotangent correspondence as a linear equivalence. -/
noncomputable def basedDualNumberPointCotangentLinearEquiv (aug : D →ₐ[R] k) :
    {f : D →ₐ[R] DualNumber k // dualNumberAugmentation f = aug} ≃ₗ[k]
      (RelativeCotangentSpace aug →ₗ[k] k) :=
  (basedDualNumberPointCotangentEquiv aug).linearEquiv k
end Deformation
