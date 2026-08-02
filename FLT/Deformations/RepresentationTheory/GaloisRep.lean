/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Deformations.RepresentationTheory.Etale
public import FLT.Deformations.IsProartinian
public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Unique
public import FLT.Mathlib.Order.JordanHolder
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Galois representations

The type `GaloisRep K A M` of `A`-linear continuous representations of the
absolute Galois group of a field `K` on an `A`-module `M`, together with the
basic API (kernel, etc.).
-/

@[expose] public section

open NumberField

universe uK

variable {K : Type uK} {L : Type*} [Field K] [Field L]
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {B : Type*} [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

variable (K A M) in
/-- `GaloisRep K A M` are the `A`-linear galois reps of a field `K` on the `A`-module `M`. -/
def GaloisRep :=
  letI := moduleTopology A (Module.End A M)
  Γ K →ₜ* Module.End A M

noncomputable instance : FunLike (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instFunLike

instance : MonoidHomClass (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instMonoidHomClass

omit [NumberField K] in
@[ext]
lemma GaloisRep.ext {ρ ρ' : GaloisRep K A M} (H : ∀ σ, ρ σ = ρ' σ) : ρ = ρ' :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.ext H

/-- The kernel of a galois rep. -/
noncomputable nonrec
abbrev GaloisRep.ker (ρ : GaloisRep K A M) : Subgroup (Γ K) :=
  letI := moduleTopology A (Module.End A M)
  ρ.ker

omit [NumberField K] in
/-- A surjective intertwiner of Galois representations makes the kernel of the source act
trivially on the target. -/
theorem GaloisRep.ker_le_ker_of_surjective_intertwiner
    (ρ : GaloisRep K A M) (τ : GaloisRep K A N) (π : M →ₗ[A] N)
    (hπ : Function.Surjective π)
    (hcomm : ∀ g x, π (ρ g x) = τ g (π x)) : ρ.ker ≤ τ.ker := by
  intro g hg
  change τ g = 1
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  rw [← hcomm]
  change ρ g = 1 at hg
  rw [hg]
  rfl

/-- A Galois representation over a discrete coefficient ring has open kernel. Equivalently,
it factors through a finite quotient of the absolute Galois group. -/
theorem GaloisRep.isOpen_ker_of_discrete [DiscreteTopology A] (ρ : GaloisRep K A M) :
    IsOpen (ρ.ker : Set (Γ K)) := by
  letI : TopologicalSpace (Module.End A M) := moduleTopology A _
  letI : DiscreteTopology (Module.End A M) :=
    ModuleTopology.discreteTopology_of_discrete A _
  exact (isOpen_discrete {1}).preimage ρ.continuous

/-- The finite normal extension of `K` cut out by a discrete Galois representation: the
fixed field of its kernel inside the chosen algebraic closure. -/
noncomputable def GaloisRep.fieldCutOut (ρ : GaloisRep K A M) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField ρ.ker

/-- The fixing subgroup of the field cut out by a discrete representation is exactly the
kernel of the representation. -/
theorem GaloisRep.fieldCutOut_fixingSubgroup [PerfectField K] [DiscreteTopology A]
    (ρ : GaloisRep K A M) : ρ.fieldCutOut.fixingSubgroup = ρ.ker := by
  unfold GaloisRep.fieldCutOut
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨ρ.ker, Subgroup.isClosed_of_isOpen _ ρ.isOpen_ker_of_discrete⟩

/-- The field cut out by a discrete Galois representation is finite over the base field. -/
theorem GaloisRep.fieldCutOut_finiteDimensional [PerfectField K] [DiscreteTopology A]
    (ρ : GaloisRep K A M) : FiniteDimensional K ρ.fieldCutOut := by
  apply (InfiniteGalois.isOpen_iff_finite ρ.fieldCutOut).mp
  rw [ρ.fieldCutOut_fixingSubgroup]
  exact ρ.isOpen_ker_of_discrete

/-- The field cut out by a Galois representation is normal and separable over the base field. -/
noncomputable instance GaloisRep.fieldCutOut_isGalois [PerfectField K]
    (ρ : GaloisRep K A M) : IsGalois K ρ.fieldCutOut := by
  unfold GaloisRep.fieldCutOut
  infer_instance

/-- Every value of a Galois representation is a linear equivalence, with inverse given by
the value at the inverse Galois element. -/
noncomputable def GaloisRep.linearEquiv (ρ : GaloisRep K A M) (σ : Γ K) : M ≃ₗ[A] M :=
  LinearEquiv.ofLinear (ρ σ) (ρ σ⁻¹) (by
    ext x
    change ρ σ (ρ σ⁻¹ x) = x
    simpa only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]) (by
    ext x
    change ρ σ⁻¹ (ρ σ x) = x
    simpa only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply])

@[simp]
theorem GaloisRep.linearEquiv_apply (ρ : GaloisRep K A M) (σ : Γ K) (x : M) :
    ρ.linearEquiv σ x = ρ σ x := rfl

/-- The group-valued form of a Galois representation. -/
noncomputable def GaloisRep.toLinearEquivMonoidHom (ρ : GaloisRep K A M) :
    Γ K →* (M ≃ₗ[A] M) where
  toFun := ρ.linearEquiv
  map_one' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    change ρ (σ * τ) x = ρ σ (ρ τ x)
    rw [map_mul]
    rfl

/-- The faithful finite-level representation through which a discrete absolute-Galois
representation factors. -/
noncomputable def GaloisRep.finiteQuotientRepresentation [PerfectField K] [DiscreteTopology A]
    (ρ : GaloisRep K A M) :
    (ρ.fieldCutOut ≃ₐ[K] ρ.fieldCutOut) →* (M ≃ₗ[A] M) := by
  let res : Γ K →* (ρ.fieldCutOut ≃ₐ[K] ρ.fieldCutOut) :=
    AlgEquiv.restrictNormalHom ρ.fieldCutOut
  let ρlin : Γ K →* (M ≃ₗ[A] M) := ρ.toLinearEquivMonoidHom
  refine (res.liftOfSurjective (G₃ := (M ≃ₗ[A] M))
    (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K))) ⟨ρlin, ?_⟩
  change res.ker ≤ ρlin.ker
  rw [show res.ker = ρ.fieldCutOut.fixingSubgroup from
      IntermediateField.restrictNormalHom_ker ρ.fieldCutOut,
    ρ.fieldCutOut_fixingSubgroup]
  intro σ hσ
  change ρ.linearEquiv σ = 1
  ext x
  change ρ σ x = x
  change ρ σ = 1 at hσ
  rw [hσ]
  rfl

/-- Pulling the finite-level representation back to the absolute Galois group recovers the
original representation. -/
@[simp]
theorem GaloisRep.finiteQuotientRepresentation_restrict [PerfectField K] [DiscreteTopology A]
    (ρ : GaloisRep K A M) (σ : Γ K) :
  ρ.finiteQuotientRepresentation
        (AlgEquiv.restrictNormalHom ρ.fieldCutOut σ) = ρ.linearEquiv σ := by
  simp [GaloisRep.finiteQuotientRepresentation]
  rfl

/-- The representation of the finite Galois group of the field cut out by `ρ` is faithful. -/
theorem GaloisRep.finiteQuotientRepresentation_injective
    [PerfectField K] [DiscreteTopology A] (ρ : GaloisRep K A M) :
    Function.Injective ρ.finiteQuotientRepresentation := by
  letI : TopologicalSpace (Module.End A M) := moduleTopology A _
  intro σ τ hστ
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) σ
  obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) τ
  rw [ρ.finiteQuotientRepresentation_restrict,
    ρ.finiteQuotientRepresentation_restrict] at hστ
  have hστ' : ρ g = ρ h := by
    ext x
    exact DFunLike.congr_fun hστ x
  have hkerρ : g⁻¹ * h ∈ ρ.ker := by
    change ρ (g⁻¹ * h) = 1
    calc
      ρ (g⁻¹ * h) = ρ g⁻¹ * ρ h := map_mul ρ g⁻¹ h
      _ = ρ g⁻¹ * ρ g := by rw [hστ']
      _ = ρ (g⁻¹ * g) := (map_mul ρ g⁻¹ g).symm
      _ = 1 := by simp
  have hkerres : g⁻¹ * h ∈
      (AlgEquiv.restrictNormalHom ρ.fieldCutOut).ker := by
    rwa [IntermediateField.restrictNormalHom_ker, ρ.fieldCutOut_fixingSubgroup]
  have heq := MonoidHom.mem_ker.mp hkerres
  simpa only [map_mul, map_inv, inv_mul_eq_one] using heq

/-- The Galois group through which a discrete representation factors is finite. -/
noncomputable instance GaloisRep.finite_fieldCutOut_aut [PerfectField K] [DiscreteTopology A]
    (ρ : GaloisRep K A M) : Finite (ρ.fieldCutOut ≃ₐ[K] ρ.fieldCutOut) := by
  letI : FiniteDimensional K ρ.fieldCutOut := ρ.fieldCutOut_finiteDimensional
  infer_instance

/-- A field extension induces a map between galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
def GaloisRep.map (ρ : GaloisRep K A M) (f : K →+* L) : GaloisRep L A M :=
  letI := moduleTopology A (Module.End A M)
  ρ.comp (Field.absoluteGaloisGroup.map f)

-- remark: `.toMonoidHom` added in bump to v4.30.0-rc1
@[simp]
lemma GaloisRep.ker_map (ρ : GaloisRep K A M) (f : K →+* L) :
    (ρ.map f).ker = ρ.ker.comap (Field.absoluteGaloisGroup.map f).toMonoidHom := rfl

/-- The action on the field cut out by a representation, pulled back along an arbitrary field
extension. -/
noncomputable def GaloisRep.fieldCutOutAction (ρ : GaloisRep K A M) (f : K →+* L) :
    Γ L →* (ρ.fieldCutOut ≃ₐ[K] ρ.fieldCutOut) :=
  (AlgEquiv.restrictNormalHom ρ.fieldCutOut).comp
    (Field.absoluteGaloisGroup.map f).toMonoidHom

/-- Pullback along a field extension preserves the equality between the kernel of a discrete
representation and the fixing subgroup of its cutout field. -/
@[simp]
theorem GaloisRep.fieldCutOutAction_ker [PerfectField K] [DiscreteTopology A]
    (ρ : GaloisRep K A M) (f : K →+* L) :
    (ρ.fieldCutOutAction f).ker = (ρ.map f).ker := by
  ext σ
  change Field.absoluteGaloisGroup.map f σ ∈
      (AlgEquiv.restrictNormalHom ρ.fieldCutOut).ker ↔
    Field.absoluteGaloisGroup.map f σ ∈ ρ.ker
  rw [IntermediateField.restrictNormalHom_ker, ρ.fieldCutOut_fixingSubgroup]

variable (K A n) in
/-- A framed galois rep is a galois rep with a distinguished basis.
We implement it by via a galois rep on `Aⁿ`. -/
abbrev FramedGaloisRep := GaloisRep K A (n → A)

/-- A field extension induces a map between framed galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
abbrev FramedGaloisRep.map (ρ : FramedGaloisRep K A n) (f : K →+* L) : FramedGaloisRep L A n :=
  GaloisRep.map ρ f

/-- We can conjugate a galois rep by a linear isomorphism on the space. -/
noncomputable
def GaloisRep.conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) : GaloisRep K A N :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  let e' : Module.End A M ≃A[A] Module.End A N :=
    .ofIsModuleTopology <| LinearEquiv.conjAlgEquiv A e
  e'.toContinuousAlgHom.toContinuousMonoidHom.comp ρ

omit [NumberField K] in
lemma GaloisRep.conj_apply (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) :
    ρ.conj e σ = e.conj (ρ σ) := rfl

omit [NumberField K] in
@[simp]
lemma GaloisRep.conj_apply_apply (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) (x : N) :
    ρ.conj e σ x = e (ρ σ (e.symm x)) := rfl

omit [NumberField K] in
@[simp]
lemma GaloisRep.conj_trans
    {P : Type*} [AddCommGroup P] [Module A P]
    (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (f : N ≃ₗ[A] P) :
    (ρ.conj e).conj f = ρ.conj (e.trans f) := by
  ext σ x
  rfl

omit [NumberField K] in
@[simp]
lemma GaloisRep.conj_refl (ρ : GaloisRep K A M) :
    ρ.conj (LinearEquiv.refl A M) = ρ := by
  ext σ
  rfl

@[simp]
lemma GaloisRep.map_conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (f : K →+* L) :
    (ρ.conj e).map f = (ρ.map f).conj e := rfl

set_option backward.isDefEq.respectTransparency.types false in
omit [NumberField K] in
@[simp]
lemma GaloisRep.ker_conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) :
    (ρ.conj e).ker = ρ.ker := by
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  ext; simp [conj]

/-- Equivalent modules have equivalent set of galois reps. -/
noncomputable
def GaloisRep.conjEquiv (e : M ≃ₗ[A] N) : GaloisRep K A M ≃ GaloisRep K A N where
  toFun := (conj · e)
  invFun := (conj · e.symm)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- Given a basis, we may frame a galois rep into a framed galois rep. -/
noncomputable
def GaloisRep.frame (ρ : GaloisRep K A M) (b : Module.Basis n A M) : FramedGaloisRep K A n :=
  ρ.conj (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A n)

/-- Given a basis of `M`, we may realize a framed galois rep as a galois rep on `M`. -/
noncomputable
def FramedGaloisRep.unframe (ρ : FramedGaloisRep K A n) (b : Module.Basis n A M) :
    GaloisRep K A M :=
  ρ.conj (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A n).symm

-- **TODO** this should be frame_unframe maybe?
omit [DecidableEq n] [NumberField K] in
@[simp]
lemma GaloisRep.unframe_frame (ρ : GaloisRep K A M) (b : Module.Basis n A M) :
    (ρ.frame b).unframe b = ρ := by
  ext; simp [frame, FramedGaloisRep.unframe]

omit [DecidableEq n] [NumberField K] in
@[simp]
lemma FramedGaloisRep.unframe_frame (ρ : FramedGaloisRep K A n) (b : Module.Basis n A M) :
    (ρ.unframe b).frame b = ρ := by
  ext; simp [unframe, GaloisRep.frame]

variable [IsTopologicalRing A]

set_option backward.isDefEq.respectTransparency.types false in
/-- `A`-linear framed galois reps are equivalent to continuous homomorphisms into `GLₙ(A)`. -/
noncomputable
def FramedGaloisRep.GL : FramedGaloisRep K A n ≃ (Γ K →ₜ* GL n A) :=
  letI := moduleTopology A (Module.End A (n → A))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite A (Module.End A (n → A))⟩
  letI e : Module.End A (n → A) ≃A[A] Matrix n n A :=
    .ofIsModuleTopology LinearMap.toMatrixAlgEquiv'
  { toFun ρ := (e.toContinuousAlgHom.toContinuousMonoidHom.comp ρ).toHomUnits
    invFun ρ := e.symm.toContinuousAlgHom.toContinuousMonoidHom.comp ((Units.coeHomₜ _).comp ρ)
    left_inv _ := by ext; simp [GaloisRep]
    right_inv _ := by ext; simp }

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.GL_apply (ρ : FramedGaloisRep K A n) (σ) : (ρ.GL σ).1 = (ρ σ).toMatrix' := rfl

/-- Make an `A`-linear framed galois reps from a continuous hom into `GLₙ(A)`. -/
noncomputable
abbrev FramedGaloisRep.ofGL := FramedGaloisRep.GL (K := K) (A := A) (n := n).symm

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.GL_symm_apply (ρ : Γ K →ₜ* GL n A) (σ) : GL.symm ρ σ = (ρ σ).toLin := rfl

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.ofGL_apply (ρ : Γ K →ₜ* GL n A) (σ) : ofGL ρ σ = (ρ σ).toLin := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `1`-dimensional framed galois reps are equivalent to (continuous) characters. -/
noncomputable def FramedGaloisRep.equivChar {n : Type*} [Unique n] :
    FramedGaloisRep K A n ≃ (Γ K →ₜ* A) :=
  letI := moduleTopology A (Module.End A (n → A))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite A (Module.End A (n → A))⟩
  letI e : Module.End A (n → A) ≃A[A] A :=
    .ofIsModuleTopology (LinearMap.toMatrixAlgEquiv'.trans Matrix.uniqueAlgEquiv)
  { toFun ρ := e.toContinuousAlgHom.toContinuousMonoidHom.comp ρ
    invFun ρ := e.symm.toContinuousAlgHom.toContinuousMonoidHom.comp ρ
    left_inv _ := by ext; simp [GaloisRep]
    right_inv _ := by ext; simp }

/-- The determinant of a galois rep. -/
noncomputable
def GaloisRep.det (ρ : GaloisRep K A M) : Γ K →ₜ* A :=
  letI := moduleTopology A (Module.End A M)
  .comp ⟨LinearMap.det, IsModuleTopology.continuous_det⟩ ρ

open TensorProduct in
variable (B) in
/-- Make a `A`-linear galois rep on `M` into a `B`-linear rep on `B ⊗ M`. -/
noncomputable
def GaloisRep.baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) : GaloisRep K B (B ⊗[A] M) :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology B (Module.End B (B ⊗[A] M))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite B (Module.End B (B ⊗[A] M))⟩
  letI := IsModuleTopology.toContinuousAdd B (Module.End B (B ⊗[A] M))
  let F : Module.End A M →+* Module.End B (B ⊗[A] M) := Module.End.baseChangeHom A B M
  have : Continuous F := by
    have : IsTopologicalSemiring (Module.End B (B ⊗[A] M)) := ⟨⟩
    have : Continuous (algebraMap A (Module.End B (B ⊗[A] M))) := by
      rw [IsScalarTower.algebraMap_eq A B, RingHom.coe_comp]
      exact (continuous_algebraMap _ _).comp (continuous_algebraMap _ _)
    exact IsModuleTopology.continuous_of_ringHom (R := A) F (by simpa [F])
  .comp ⟨F, this⟩ ρ

omit [IsTopologicalRing A] [NumberField K] in
open TensorProduct in
@[simp]
lemma GaloisRep.baseChange_tmul [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (σ : Γ K) (r : B) (x : M) :
    ρ.baseChange B σ (r ⊗ₜ x) = r ⊗ₜ (ρ σ x) := rfl

open scoped TensorProduct

omit [NumberField K] [IsTopologicalRing A] in
/-- Conjugating a Galois representation does not change the trace of any group element. -/
lemma GaloisRep.trace_conj [Module.Free A M] [Module.Finite A M]
    [Module.Free A N] [Module.Finite A N]
    (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) :
    LinearMap.trace A N (ρ.conj e σ) = LinearMap.trace A M (ρ σ) :=
  LinearMap.trace_conj' (ρ σ) e

omit [NumberField K] in
/-- Conjugating a Galois representation does not change the determinant of any group element. -/
lemma GaloisRep.det_conj [Module.Free A M] [Module.Finite A M]
    [Module.Free A N] [Module.Finite A N]
    (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) :
    (ρ.conj e).det σ = ρ.det σ :=
  LinearMap.det_conj (ρ σ) e

omit [NumberField K] [IsTopologicalRing A] in
/-- Conjugating a Galois representation does not change characteristic polynomials. -/
lemma GaloisRep.charpoly_conj [Module.Free A M] [Module.Finite A M]
    [Module.Free A N] [Module.Finite A N]
    (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) :
    (ρ.conj e σ).charpoly = (ρ σ).charpoly :=
  e.charpoly_conj (ρ σ)

omit [NumberField K] [IsTopologicalRing A] in
/-- Trace commutes with scalar extension of a Galois representation. -/
lemma GaloisRep.trace_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Free A M] [Module.Finite A M]
    (ρ : GaloisRep K A M) (σ : Γ K) :
    LinearMap.trace B (B ⊗[A] M) (ρ.baseChange B σ) =
      algebraMap A B (LinearMap.trace A M (ρ σ)) :=
  LinearMap.trace_baseChange (ρ σ) B

omit [NumberField K] in
/-- Determinants commute with scalar extension of a Galois representation. -/
lemma GaloisRep.det_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Free A M] [Module.Finite A M]
    (ρ : GaloisRep K A M) (σ : Γ K) :
    (ρ.baseChange B).det σ = algebraMap A B (ρ.det σ) :=
  LinearMap.det_baseChange (ρ σ)

omit [NumberField K] [IsTopologicalRing A] in
/-- Characteristic polynomials commute with scalar extension of a Galois representation. -/
lemma GaloisRep.charpoly_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Free A M] [Module.Finite A M]
    (ρ : GaloisRep K A M) (σ : Γ K) :
    (ρ.baseChange B σ).charpoly = (ρ σ).charpoly.map (algebraMap A B) :=
  LinearMap.charpoly_baseChange (ρ σ) B

set_option backward.isDefEq.respectTransparency.types false in
omit [IsTopologicalRing A] [NumberField K] in
lemma GaloisRep.ker_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) :
    ρ.ker ≤ (ρ.baseChange B).ker := by
  intro _; simp +contextual [baseChange]

omit [IsTopologicalRing A] in
lemma GaloisRep.baseChange_map [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (f : K →+* L) : (ρ.baseChange B).map f = (ρ.map f).baseChange B := rfl

omit [NumberField K] [IsTopologicalRing A] in
/-- Scalar extension commutes with changing the basis of a Galois representation. -/
lemma GaloisRep.baseChange_conj [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] [Module.Finite A N] [Module.Free A N]
    (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) :
    (ρ.conj e).baseChange B = (ρ.baseChange B).conj (e.baseChange A B) := by
  ext σ
  rfl

open TensorProduct.AlgebraTensorModule in
omit [NumberField K] [IsTopologicalRing A] in
/-- Iterated coefficient extension agrees, after the canonical tensor-product change of basis,
with coefficient extension along the composite algebra map. -/
lemma GaloisRep.baseChange_baseChange
    {C : Type*} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing B] [IsTopologicalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [ContinuousSMul A B] [ContinuousSMul B C] [ContinuousSMul A C]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) :
    (ρ.baseChange B).baseChange C =
      (ρ.baseChange C).conj (cancelBaseChange A B C C M).symm := by
  apply GaloisRep.ext
  intro σ
  rw [GaloisRep.conj_apply]
  exact LinearMap.baseChange_baseChange (A := B) (B := C) (ρ σ)

/-- Make a framed `n` dimensional `A`-linear galois rep into a `B`-linear rep by composing with
`GLₙ(A) → GLₙ(B)`. -/
noncomputable
def FramedGaloisRep.baseChange [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) : FramedGaloisRep K B n :=
  .ofGL (.comp (Units.mapₜ ⟨f.mapMatrix.toMonoidHom, continuous_id.matrix_map hf⟩) ρ.GL)

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.baseChange_GL [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) {σ i j} :
    (ρ.baseChange f hf).GL σ i j = f (ρ.GL σ i j) := by
  simp [baseChange]

omit [NumberField K] in
variable (B) in
lemma GaloisRep.frame_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (b : Module.Basis n A M) :
    (ρ.baseChange B).frame (b.baseChange B) =
      (ρ.frame b).baseChange _ (continuous_algebraMap A B) := by
  apply FramedGaloisRep.GL.injective
  ext σ i j
  simp [GaloisRep.frame, Algebra.smul_def]

omit [NumberField K] in
lemma FramedGaloisRep.baseChange_def [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) :
    ρ.baseChange f hf =
      letI := f.toAlgebra
      haveI : ContinuousSMul A B := continuousSMul_of_algebraMap A B hf
      (GaloisRep.baseChange B ρ).frame ((Pi.basisFun A n).baseChange B) := by
  letI := f.toAlgebra
  haveI : ContinuousSMul A B := continuousSMul_of_algebraMap A B hf
  rw [GaloisRep.frame_baseChange]
  rfl

lemma FramedGaloisRep.baseChange_map [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f)
    (g : K →+* L) : (ρ.baseChange f hf).map g = (ρ.map g).baseChange f hf := rfl

lemma Matrix.map_det {F α β n : Type*} [CommRing β] [CommRing α] [Fintype n]
    [DecidableEq n]
    (M : Matrix n n α) (f : F) [FunLike F α β] [RingHomClass F α β] :
    (M.map f).det = f M.det :=
  (RingHom.map_det (f : α →+* β) M).symm

lemma LinearMap.trace_toLin' {R n : Type*} [CommSemiring R] [DecidableEq n]
    [Fintype n] (M : Matrix n n R) : LinearMap.trace _ _ M.toLin' = M.trace := by
  simp

set_option backward.isDefEq.respectTransparency false in
omit [NumberField K] in
lemma FramedGaloisRep.det_baseChange [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) :
    (ρ.baseChange f hf).det = .comp ⟨f, hf⟩ ρ.det := by
  ext σ
  dsimp [baseChange, GaloisRep.det]
  rw [GL_symm_apply]
  simp [← Matrix.toLin'_apply', Matrix.map_det]

/-- Given a (global) galois rep, this is the local galois rep at a finite prime `v`.
Note: this fixes an arbitrary embedding `Kᵃˡᵍ → Kᵥᵃˡᵍ`, or equivalently,
an arbitrary choice of valuation on `Kᵃˡᵍ` extending `v`. -/
noncomputable
abbrev GaloisRep.toLocal (ρ : GaloisRep K A M) (v : Ω K) : GaloisRep (v.adicCompletion K) A M :=
  ρ.map (algebraMap _ _)

omit [IsTopologicalRing A] in
@[simp]
lemma GaloisRep.toLocal_adicArithFrob (ρ : GaloisRep K A M) (v : Ω K) :
    ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v) =
      ρ (Field.AbsoluteGaloisGroup.globalAdicArithFrob v) := rfl

universe v u
variable {R : Type u} [CommRing R]

/-- The class of galois reps unramified at `v`. -/
class GaloisRep.IsUnramifiedAt (ρ : GaloisRep K A M) (v : Ω K) : Prop where
  localInertiaGroup_le :
    letI := moduleTopology A (Module.End A M)
    localInertiaGroup v ≤ (ρ.toLocal v).ker

/-- The action of a local absolute Galois group on the finite field cut out by a global
representation.  It is obtained by mapping the local Galois group into the global one and
then restricting global automorphisms to the fixed field of the representation's kernel. -/
noncomputable def GaloisRep.fieldCutOutLocalAction (ρ : GaloisRep K A M) (v : Ω K) :
    Γ (v.adicCompletion K) →* (ρ.fieldCutOut ≃ₐ[K] ρ.fieldCutOut) :=
  ρ.fieldCutOutAction (algebraMap K (v.adicCompletion K))

/-- If a discrete representation is unramified at `v`, local inertia acts trivially on the
finite extension cut out by the representation. -/
theorem GaloisRep.localInertiaGroup_le_fieldCutOutLocalAction_ker
    [PerfectField K] [DiscreteTopology A] (ρ : GaloisRep K A M) (v : Ω K)
    [ρ.IsUnramifiedAt v] :
    localInertiaGroup v ≤ (ρ.fieldCutOutLocalAction v).ker := by
  intro σ hσ
  have hρ := GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ) hσ
  change Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) σ ∈ ρ.ker at hρ
  change Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) σ ∈
    (AlgEquiv.restrictNormalHom ρ.fieldCutOut).ker
  rwa [IntermediateField.restrictNormalHom_ker, ρ.fieldCutOut_fixingSubgroup]

/-- The local action on the field cut out by a discrete representation has exactly the same
kernel as the localized representation. -/
@[simp]
theorem GaloisRep.fieldCutOutLocalAction_ker
    [PerfectField K] [DiscreteTopology A] (ρ : GaloisRep K A M) (v : Ω K) :
    (ρ.fieldCutOutLocalAction v).ker = (ρ.toLocal v).ker :=
  ρ.fieldCutOutAction_ker (algebraMap K (v.adicCompletion K))

instance (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] (e : M ≃ₗ[A] N) :
    (ρ.conj e).IsUnramifiedAt v where
  localInertiaGroup_le := (GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans (by simp)

instance [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] :
    (ρ.baseChange B).IsUnramifiedAt v :=
  ⟨(GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans
    (((ρ.toLocal v).ker_baseChange (B := B)))⟩

variable [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]

/-- The characteristic polynomial of the frobenious conjugacy class at `v` under `ρ`. -/
noncomputable
def GaloisRep.charFrob (ρ : GaloisRep K A M) : Polynomial A := (ρ.toLocal v Frobᵥ).charpoly

-- shortcut instance for next theorem: needed after mathlib #34045
noncomputable instance : CommRing Kᵥ := inferInstance

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalRing A] in
lemma GaloisRep.charFrob_eq (ρ : GaloisRep K A M) [ρ.IsUnramifiedAt v] (σ : Γ Kᵥ)
    (hσ : IsArithFrobAt 𝒪ᵥ σ (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))) :
    (ρ.toLocal v σ).charpoly = ρ.charFrob v := by
  have := IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)
    (hσ.mul_inv_mem_inertia (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob v))
  replace this := congr($this * ρ.toLocal v Frobᵥ)
  simp only [ContinuousMonoidHom.coe_toMonoidHom, ← map_mul, MonoidHom.coe_coe, one_mul,
    inv_mul_cancel_right] at this
  rw [this, charFrob]

section Flat

set_option linter.unusedVariables false in
/-- The underlying space of a galois rep. This is a type class synonym that allows `G` to act
on it via `ρ`. -/
@[nolint unusedArguments]
def GaloisRep.Space (ρ : GaloisRep K A M) : Type _ := M

instance (ρ : GaloisRep K A M) : AddCommGroup ρ.Space := inferInstanceAs (AddCommGroup M)

-- dirty hack
set_option backward.isDefEq.respectTransparency false in
noncomputable instance (ρ : GaloisRep K A M) : DistribMulAction (Γ K) ρ.Space where
  smul g v := ρ g v
  one_smul b := by unfold HSMul.hSMul; simp [instHSMul]
  mul_smul := by unfold HSMul.hSMul; simp [instHSMul]
  smul_zero := by unfold HSMul.hSMul; simp [instHSMul]
  smul_add := by unfold HSMul.hSMul; simp [instHSMul]

/-- A Galois representation over a discrete coefficient ring acts continuously on its
underlying space when that space is regarded as a discrete Galois set.  Indeed, the open
kernel of the representation is contained in the stabilizer of every vector. -/
instance [DiscreteTopology A] (ρ : GaloisRep K A M) :
    ContinuousSMulDiscrete (Γ K) ρ.Space := by
  rw [continuousSMulDiscrete_iff_isOpen_stabilizer]
  intro x
  apply Subgroup.isOpen_mono _ ρ.isOpen_ker_of_discrete
  intro σ hσ
  change ρ σ x = x
  change ρ σ = 1 at hσ
  rw [hσ]
  rfl

open TensorProduct in
/-- A galois rep `ρ : Γ K → Aut_A(M)` has a flat prolongation at `v` if `M` (when viewed as a
`Γ Kᵥ`) module is isomorphic to the geometric points of a finite etale hopf algebra over `Kᵥ`, and
there exists an finite flat hopf algebra over `𝒪ᵥ` whose generic fiber is isomorphic to it.
In particular this requires `M` (and by extension `A`) to have finite cardinality.

Note that the `Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G)` condition is redundant because `Kᵥ` has char 0
and all finite flat group schemes over `Kᵥ` are etale.
But this would be hard to prove in general, while in the applications they would come from
finite groups so it would be easy to show that they are etale. If this turns out to not be the case,
we can remove this condition and state the aforementioned result as a sorry.
-/
def GaloisRep.HasFlatProlongationAt (ρ : GaloisRep K A M) : Prop :=
  ∃ (G : Type uK) (_ : CommRing G) (_ : HopfAlgebra 𝒪ᵥ G)
    (_ : Module.Flat 𝒪ᵥ G) (_ : Module.Finite 𝒪ᵥ G) (_ : Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G))
    (f : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ) →+[Γ Kᵥ] (ρ.toLocal v).Space),
    Function.Bijective f

/-- A Galois-equivariant additive equivalence transports a finite-flat prolongation.  The
coefficient rings of the two representations may differ because the prolongation condition
only depends on the underlying finite additive Galois module. -/
lemma GaloisRep.HasFlatProlongationAt.of_addEquiv
    {C P : Type*} [CommRing C] [TopologicalSpace C] [AddCommGroup P] [Module C P]
    {ρ : GaloisRep K A M} (hρ : ρ.HasFlatProlongationAt v)
    (ρ' : GaloisRep K C P) (e : M ≃+ P)
    (heq : ∀ g x, e (ρ.toLocal v g x) = ρ'.toLocal v g (e x)) :
    ρ'.HasFlatProlongationAt v := by
  rcases hρ with ⟨G, hG, hHopf, hFlat, hFinite, hEtale, f, hf⟩
  letI : CommRing G := hG
  letI : HopfAlgebra 𝒪ᵥ G := hHopf
  letI : Module.Flat 𝒪ᵥ G := hFlat
  letI : Module.Finite 𝒪ᵥ G := hFinite
  letI : Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) := hEtale
  let X := Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ)
  let f₀ : X → M := f
  have hf₀ : Function.Bijective f₀ := hf
  have hf₀_zero : f₀ 0 = 0 := f.map_zero
  have hf₀_add (x y : X) : f₀ (x + y) = f₀ x + f₀ y := f.map_add x y
  have hf₀_smul (g : Γ Kᵥ) (x : X) :
      f₀ (g • x) = ρ.toLocal v g (f₀ x) := f.map_smul g x
  let f' : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ) →+[Γ Kᵥ] (ρ'.toLocal v).Space := {
    toFun x := e (f₀ x)
    map_zero' := by rw [hf₀_zero, e.map_zero]; rfl
    map_add' x y := by rw [hf₀_add, e.map_add]; rfl
    map_smul' g x := by
      rw [hf₀_smul]
      exact heq g (f₀ x) }
  exact ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    f', e.bijective.comp hf₀⟩

/-- A change of basis preserves the existence of a finite flat prolongation. -/
lemma GaloisRep.HasFlatProlongationAt.conj
    {ρ : GaloisRep K A M} (hρ : ρ.HasFlatProlongationAt v) (e : M ≃ₗ[A] N) :
    (ρ.conj e).HasFlatProlongationAt v := by
  rcases hρ with ⟨G, hG, hHopf, hFlat, hFinite, hEtale, f, hf⟩
  letI : CommRing G := hG
  letI : HopfAlgebra 𝒪ᵥ G := hHopf
  letI : Module.Flat 𝒪ᵥ G := hFlat
  letI : Module.Finite 𝒪ᵥ G := hFinite
  letI : Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G) := hEtale
  let X := Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ)
  let f₀ : X → M := f
  have hf₀ : Function.Bijective f₀ := hf
  have hf₀_zero : f₀ 0 = 0 := f.map_zero
  have hf₀_add (x y : X) : f₀ (x + y) = f₀ x + f₀ y := f.map_add x y
  have hf₀_smul (g : Γ Kᵥ) (x : X) :
      f₀ (g • x) = ρ.toLocal v g (f₀ x) := f.map_smul g x
  let f' : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ) →+[Γ Kᵥ]
      ((ρ.conj e).toLocal v).Space := {
    toFun x := e (f₀ x)
    map_zero' := by
      rw [hf₀_zero, e.map_zero]
      rfl
    map_add' x y := by
      rw [hf₀_add, e.map_add]
      rfl
    map_smul' g x := by
      rw [hf₀_smul]
      change e (ρ.toLocal v g (f₀ x)) =
        e (ρ.toLocal v g (e.symm (e (f₀ x))))
      rw [e.symm_apply_apply] }
  exact ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    f', e.bijective.comp hf₀⟩

/-- A galois rep `ρ : Γ K → Aut_A(M)` is flat at `v` if `A/I ⊗ M` has a flat prolongation at `v`
for all open ideals `I`. -/
class GaloisRep.IsFlatAt [IsLocalRing A] (ρ : GaloisRep K A M) : Prop where
  cond : ∀ (I : Ideal A), IsOpen (I : Set A) →
    (ρ.baseChange (A ⧸ I)).HasFlatProlongationAt v

/-- Over a discrete coefficient ring, flatness at `v` already gives a finite-flat
prolongation of the representation itself.  Apply the defining condition to the zero ideal
and identify `(A ⧸ ⊥) ⊗[A] M` with `M`. -/
theorem GaloisRep.IsFlatAt.hasFlatProlongationAt_of_discrete
    [IsLocalRing A] [DiscreteTopology A] (ρ : GaloisRep K A M) [hρ : ρ.IsFlatAt v] :
    ρ.HasFlatProlongationAt v := by
  let hflat := hρ.cond (⊥ : Ideal A)
    (isOpen_discrete (↑(⊥ : Ideal A) : Set A))
  let e : ((A ⧸ (⊥ : Ideal A)) ⊗[A] M) ≃ₗ[A] M :=
    (TensorProduct.congr (AlgEquiv.quotientBot A A).toLinearEquiv
      (LinearEquiv.refl A M)).trans (TensorProduct.lid A M)
  apply hflat.of_addEquiv v ρ e.toAddEquiv
  intro g x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      change e (((ρ.toLocal v).baseChange (A ⧸ (⊥ : Ideal A))) g (a ⊗ₜ[A] m)) =
        ρ.toLocal v g (e (a ⊗ₜ[A] m))
      rw [GaloisRep.baseChange_tmul]
      simp [e]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The finite-flat group-scheme input behind functoriality of the flat deformation
condition: finite-flat Galois modules are closed under finite products and equivariant
quotients. The product model is obtained from a finite product of group schemes; the quotient
model is obtained by schematic closure and the quotient construction for finite flat group
schemes. See de Smit--Lenstra, *Explicit construction of universal deformation rings*, §6.3,
and Conrad, *The flat deformation functor*, §1. -/
theorem GaloisRep.HasFlatProlongationAt.quotient_pi
    {C P : Type*} [CommRing C] [TopologicalSpace C]
    [AddCommGroup P] [Module C P]
    (ρ : GaloisRep K A M) (hρ : ρ.HasFlatProlongationAt v)
    (ρ' : GaloisRep K C P) (d : ℕ) (f : (Fin d → M) →+ P)
    (hf : Function.Surjective f)
    (heq : ∀ σ x, f (fun i ↦ ρ.toLocal v σ (x i)) = ρ'.toLocal v σ (f x)) :
    ρ'.HasFlatProlongationAt v := by
  sorry

/-- A module-finite extension of coefficient rings preserves the existence of a finite-flat
prolongation. Choose a finite free module surjecting onto the target coefficient ring. After
tensoring with the representation space, right exactness exhibits the scalar extension as an
equivariant quotient of a finite power of the original representation. -/
theorem GaloisRep.HasFlatProlongationAt.baseChange_of_moduleFinite [IsTopologicalRing B]
    [Algebra A B] [Module.Finite A B] [ContinuousSMul A B]
    (ρ : GaloisRep K A M) (hρ : ρ.HasFlatProlongationAt v) :
    (ρ.baseChange B).HasFlatProlongationAt v := by
  classical
  obtain ⟨d, g, hg⟩ := Module.Finite.exists_fin' A B
  let e : ((Fin d → A) ⊗[A] M) ≃ₗ[A] (Fin d → M) :=
    (TensorProduct.comm A (Fin d → A) M).trans
      (TensorProduct.piScalarRight A A M (Fin d))
  let q : (Fin d → M) →ₗ[A] B ⊗[A] M :=
    (g.rTensor M).comp e.symm.toLinearMap
  apply GaloisRep.HasFlatProlongationAt.quotient_pi v ρ hρ
    (ρ.baseChange B) d q.toAddHom
  · exact (LinearMap.rTensor_surjective M hg).comp e.symm.surjective
  · intro σ x
    change q (fun i ↦ ρ.toLocal v σ (x i)) = (ρ.baseChange B).toLocal v σ (q x)
    obtain ⟨z, rfl⟩ := e.surjective x
    have qe (z : (Fin d → A) ⊗[A] M) : q (e z) = (g.rTensor M) z := by
      simp [q]
    induction z using TensorProduct.induction_on with
    | zero =>
      have hzero : (fun _ : Fin d ↦ (0 : M)) = 0 := rfl
      simp only [map_zero, Pi.zero_apply, hzero]
    | tmul a m =>
      have hdiag :
          (fun i ↦ ρ.toLocal v σ (e (a ⊗ₜ[A] m) i)) =
            e (a ⊗ₜ[A] (ρ.toLocal v σ m)) := by
        ext i
        simp [e, GaloisRep.toLocal]
      rw [hdiag, qe, qe]
      simp only [LinearMap.rTensor_tmul]
      symm
      exact GaloisRep.baseChange_tmul (ρ.toLocal v) σ (g a) m
    | add z w hz hw =>
      simp only [map_add, Pi.add_apply]
      have hadd :
          (fun i ↦ ρ.toLocal v σ (e z i) + ρ.toLocal v σ (e w i)) =
            (fun i ↦ ρ.toLocal v σ (e z i)) +
              (fun i ↦ ρ.toLocal v σ (e w i)) := rfl
      rw [hadd, map_add, hz, hw]

/-- Finite flatness is preserved by extension of the coefficient ring along a continuous
local homomorphism.  For an open ideal `J` of `B`, the map `A → B ⧸ J` factors through the
open quotient by its kernel.  A composition series of the resulting Artinian local
coefficient algebra then reduces the assertion to stability of finite flat group schemes
under extensions.  This is the coefficient-ring base-change theorem used in the definition
of the flat deformation functor (cf. Conrad, Theorem 1.6 of CSS). -/
theorem GaloisRep.IsFlatAt.baseChange [IsTopologicalRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [ContinuousSMul A B]
    [IsLocalHom (algebraMap A B)] [IsResidueAlgebra A B]
    [IsProartinian A] [IsProartinian B]
    (ρ : GaloisRep K A M) [ρ.IsFlatAt v] :
    (ρ.baseChange B).IsFlatAt v := by
  constructor
  intro J hJ
  let I : Ideal A := J.comap (algebraMap A B)
  have hI : IsOpen (X := A) (I : Set A) :=
    hJ.preimage (continuous_algebraMap A B)
  have hflatI := GaloisRep.IsFlatAt.cond (v := v) (ρ := ρ) I hI
  let : Algebra (A ⧸ I) (B ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_refl I)
  let : IsScalarTower A (A ⧸ I) (B ⧸ J) := inferInstance
  let : DiscreteTopology (A ⧸ I) := QuotientAddGroup.discreteTopology hI
  let : DiscreteTopology (B ⧸ J) := QuotientAddGroup.discreteTopology hJ
  let : ContinuousSMul (A ⧸ I) (B ⧸ J) :=
    DiscreteTopology.instContinuousSMul (A ⧸ I) (B ⧸ J)
  let : ContinuousSMul A (B ⧸ J) :=
    continuousSMul_of_algebraMap A (B ⧸ J)
      (continuous_quot_mk.comp (continuous_algebraMap A B))
  let : IsArtinianRing (A ⧸ I) := IsProartinian.isArtinianRing_quotient I hI
  let : IsArtinianRing (B ⧸ J) := IsProartinian.isArtinianRing_quotient J hJ
  let : Module.Finite (A ⧸ I) (B ⧸ J) :=
    moduleFinite_quotient_comap_of_isResidueAlgebra (R := A) (S := B) J hJ
  have hiter :
      ((ρ.baseChange (A ⧸ I)).baseChange (B ⧸ J)).HasFlatProlongationAt v :=
    hflatI.baseChange_of_moduleFinite v
  have hdirect : (ρ.baseChange (B ⧸ J)).HasFlatProlongationAt v := by
    rw [GaloisRep.baseChange_baseChange] at hiter
    have h := hiter.conj v
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (B ⧸ J)
        (B ⧸ J) M)
    rw [GaloisRep.conj_trans] at h
    have heq :
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (B ⧸ J)
          (B ⧸ J) M).symm.trans
            (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (B ⧸ J)
              (B ⧸ J) M) = LinearEquiv.refl _ _ := by
      ext
      simp
    rw [heq, GaloisRep.conj_refl] at h
    exact h
  rw [GaloisRep.baseChange_baseChange]
  exact hdirect.conj v
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (B ⧸ J) (B ⧸ J) M).symm

/-- Flatness at a finite place is invariant under a change of basis. -/
lemma GaloisRep.IsFlatAt.conj [IsLocalRing A]
    {ρ : GaloisRep K A M} (hρ : ρ.IsFlatAt v) (e : M ≃ₗ[A] N) :
    (ρ.conj e).IsFlatAt v where
  cond I hI := by
    rw [GaloisRep.baseChange_conj]
    exact (hρ.cond I hI).conj v (e.baseChange A (A ⧸ I))

instance GaloisRep.IsFlatAt.conj_instance [IsLocalRing A]
    (ρ : GaloisRep K A M) (v : Ω K) [hρ : ρ.IsFlatAt v] (e : M ≃ₗ[A] N) :
    (ρ.conj e).IsFlatAt v :=
  hρ.conj v e

/-- The matrix-valued form of `GaloisRep.IsFlatAt.baseChange`. -/
theorem FramedGaloisRep.IsFlatAt.baseChange [IsTopologicalRing B]
    [IsLocalRing A] [IsLocalRing B] [IsProartinian A] [IsProartinian B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f)
    [IsLocalHom f] [ρ.IsFlatAt v]
    (hres : letI : Algebra A B := f.toAlgebra; IsResidueAlgebra A B) :
    (ρ.baseChange f hf).IsFlatAt v := by
  rw [FramedGaloisRep.baseChange_def]
  let : Algebra A B := f.toAlgebra
  let : ContinuousSMul A B := continuousSMul_of_algebraMap A B hf
  let : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  let : IsResidueAlgebra A B := hres
  have hbase : (GaloisRep.baseChange B ρ).IsFlatAt v :=
    GaloisRep.IsFlatAt.baseChange v ρ
  unfold GaloisRep.frame
  exact hbase.conj v
    (((Pi.basisFun A n).baseChange B).repr ≪≫ₗ Finsupp.linearEquivFunOnFinite B B n)

end Flat

namespace Subrepresentation

/-- Subrepresentations form a modular lattice because their meets and joins are the
corresponding meets and joins of their underlying submodules. -/
instance instIsModularLattice
    {R G W : Type*} [Ring R] [Monoid G] [AddCommGroup W] [Module R W]
    {ρ : Representation R G W} : IsModularLattice (Subrepresentation ρ) where
  sup_inf_le_assoc_of_le {x} y {z} hxz := by
    change x.toSubmodule ≤ z.toSubmodule at hxz
    change (x.toSubmodule ⊔ y.toSubmodule) ⊓ z.toSubmodule ≤
      x.toSubmodule ⊔ y.toSubmodule ⊓ z.toSubmodule
    exact IsModularLattice.sup_inf_le_assoc_of_le y.toSubmodule hxz

/-- A finite representation has only finitely many subrepresentations. -/
noncomputable instance instFinite
    {R G W : Type*} [Semiring R] [Monoid G] [AddCommMonoid W] [Module R W]
    {ρ : Representation R G W} [Finite W] : Finite (Subrepresentation ρ) :=
  Finite.of_injective Subrepresentation.toSubmodule
    Subrepresentation.toSubmodule_injective

end Subrepresentation

/-- A Galois representation is a representation (note that we
are forgetting topological information here). -/
def GaloisRep.toRepresentation (ρ : GaloisRep K A M) : Representation A (Γ K) M :=
  letI := moduleTopology A (Module.End A M) -- ?!
  ρ.toMonoidHom

/-- Every Galois representation on a finite module admits a composition series by invariant
submodules, starting at zero and ending at the whole representation. -/
theorem GaloisRep.exists_invariant_compositionSeries [Finite M]
    (ρ : GaloisRep K A M) :
    ∃ s : CompositionSeries (Subrepresentation ρ.toRepresentation),
      s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f₀, n, hn⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT
      (Subrepresentation ρ.toRepresentation)
  exact ⟨⟨n, fun i ↦ f i, fun i ↦ hn.2 i i.2⟩, f₀.eq_bot, hn.1.eq_top⟩

/-- Irreducibility of a Galois representation over a field. -/
def GaloisRep.IsIrreducible {k : Type*} [Field k] [TopologicalSpace k] [Module k M]
    (ρ : GaloisRep K k M) : Prop := ρ.toRepresentation.IsIrreducible

omit [NumberField K] in
/-- Conjugating a representation identifies its subrepresentations. -/
def GaloisRep.subrepresentationConjOrderIso
    {k V W : Type*} [Field k] [TopologicalSpace k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : GaloisRep K k V) (e : V ≃ₗ[k] W) :
    Subrepresentation ρ.toRepresentation ≃o
      Subrepresentation (ρ.conj e).toRepresentation where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        rintro g _ ⟨v, hv, rfl⟩
        refine ⟨ρ g v, U.apply_mem_toSubmodule g hv, ?_⟩
        change e (ρ g v) = (ρ.conj e) g (e v)
        simp }
  invFun U :=
    { toSubmodule := U.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        have h := U.apply_mem_toSubmodule g hv
        change (ρ.conj e) g (e v) ∈ U.toSubmodule at h
        change e (ρ g v) ∈ U.toSubmodule
        simpa using h }
  left_inv U := by
    ext v
    simp
  right_inv U := by
    ext w
    simp
  map_rel_iff' :=
    LinearMap.map_le_map_iff' (LinearMap.ker_eq_bot.mpr e.injective)

omit [NumberField K] in
/-- Irreducibility is unchanged by conjugating a representation by a linear equivalence. -/
theorem GaloisRep.isIrreducible_conj_iff
    {k V W : Type*} [Field k] [TopologicalSpace k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : GaloisRep K k V) (e : V ≃ₗ[k] W) :
    ρ.IsIrreducible ↔ (ρ.conj e).IsIrreducible :=
  (subrepresentationConjOrderIso ρ e).isSimpleOrder_iff

omit [NumberField K] in
/-- A two-dimensional representation with a nonzero invariant line is reducible. -/
theorem GaloisRep.not_isIrreducible_of_invariant_line
    {k V : Type*} [Field k] [TopologicalSpace k]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : GaloisRep K k V} (hV : Module.rank k V = 2)
    (v : V) (hv : v ≠ 0) (hinv : ∀ g : Γ K, ρ g v ∈ k ∙ v) :
    ¬ ρ.IsIrreducible := by
  intro hρ
  let U : Subrepresentation ρ.toRepresentation :=
    { toSubmodule := k ∙ v
      apply_mem_toSubmodule := by
        intro g w hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [map_smul]
        exact Submodule.smul_mem _ _ (hinv g) }
  let _ : ρ.toRepresentation.IsIrreducible := hρ
  obtain hU | hU := eq_bot_or_eq_top U
  · have hvbot : v ∈ (⊥ : Subrepresentation ρ.toRepresentation) :=
      hU ▸ Submodule.mem_span_singleton_self v
    have hvbot' : v ∈ (⊥ : Submodule k V) := hvbot
    exact hv (by simpa using hvbot')
  · have hsub : k ∙ v = (⊤ : Submodule k V) :=
      congrArg Subrepresentation.toSubmodule hU
    have hspan : Module.finrank k (k ∙ v) = 1 := finrank_span_singleton hv
    rw [hsub] at hspan
    have hfinV : Module.finrank k V = 2 := Module.finrank_eq_of_rank_eq hV
    simpa [hfinV] using hspan

omit [NumberField K] in
/-- A two-dimensional representation with a nonzero invariant one-dimensional quotient is
reducible.  The quotient is expressed as a surjective linear functional on which the group acts
trivially. -/
theorem GaloisRep.not_isIrreducible_of_surjective_invariant_quotient
    {k V : Type*} [Field k] [TopologicalSpace k]
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : GaloisRep K k V} (hV : Module.rank k V = 2)
    (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hπρ : ∀ g : Γ K, ∀ v : V, π (ρ g v) = π v) :
    ¬ ρ.IsIrreducible := by
  intro hρ
  let π' : Representation.IntertwiningMap ρ.toRepresentation
      (Representation.trivial k (Γ K) k) :=
    π.intertwiningMap_of_isIntertwiningMap _ _ hπρ
  let _ : ρ.toRepresentation.IsIrreducible := hρ
  have hπ' : π' ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := hπ 1
    have := congrArg (fun f : Representation.IntertwiningMap ρ.toRepresentation
      (Representation.trivial k (Γ K) k) => f v) hzero
    simp only [π', Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at this
    exact one_ne_zero (hv ▸ this)
  have hinj : Function.Injective π := by
    have hinj' := (Representation.IsIrreducible.injective_or_eq_zero π').resolve_right hπ'
    exact fun _ _ h ↦ hinj' h
  have hfinV : Module.finrank k V = 2 := Module.finrank_eq_of_rank_eq hV
  have hle : Module.finrank k V ≤ Module.finrank k k :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [hfinV, Module.finrank_self] at hle
  omega
