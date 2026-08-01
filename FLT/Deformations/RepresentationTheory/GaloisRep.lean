/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Deformations.RepresentationTheory.Etale
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Charpoly.BaseChange

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

/-- Flatness at a finite place is invariant under a change of basis. -/
instance GaloisRep.IsFlatAt.conj [IsLocalRing A]
    (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsFlatAt v] (e : M ≃ₗ[A] N) :
    (ρ.conj e).IsFlatAt v where
  cond I hI := by
    rw [GaloisRep.baseChange_conj]
    exact (GaloisRep.IsFlatAt.cond (ρ := ρ) I hI).conj v (e.baseChange A (A ⧸ I))

end Flat

/-- A Galois representation is a representation (note that we
are forgetting topological information here). -/
def GaloisRep.toRepresentation (ρ : GaloisRep K A M) : Representation A (Γ K) M :=
  letI := moduleTopology A (Module.End A M) -- ?!
  ρ.toMonoidHom

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
