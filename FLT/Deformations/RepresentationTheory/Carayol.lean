/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The linear-algebra core of Carayol descent

This file records the elementary trace-pairing mechanism used in Carayol's descent theorem.
For square matrices the pairing

`(x, y) ↦ trace (x * y)`

is nondegenerate.  Consequently its Gram matrix in a basis over a field has nonzero
determinant.  If a family of matrices over a local ring reduces to a basis over the residue
field, the determinant of its trace-pairing matrix is therefore a unit.  This is the linear
system which recovers matrix coefficients from traces.

The representation-theoretic and topological descent steps are developed separately below
these lemmas, so that the eventual use of Carayol's theorem does not conceal this mechanism.
-/

@[expose] public section

open LinearMap (BilinForm)
open Module
open scoped TensorProduct

namespace Matrix

section TracePairing

variable (R : Type*) (n : Type*) [CommSemiring R] [Fintype n]

/-- The bilinear trace pairing on the full matrix algebra. -/
def tracePairing : BilinForm R (Matrix n n R) :=
  (LinearMap.mul R (Matrix n n R)).compr₂ (Matrix.traceLinearMap n R R)

@[simp]
theorem tracePairing_apply (x y : Matrix n n R) :
    tracePairing R n x y = Matrix.trace (x * y) :=
  rfl

/-- The trace pairing on a full matrix algebra is nondegenerate. -/
theorem tracePairing_nondegenerate : (tracePairing R n).Nondegenerate := by
  constructor
  · intro x hx
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro y
    simpa using hx y
  · intro y hy
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro x
    simpa using hy x

end TracePairing

/-- The trace-pairing Gram matrix of a basis of a full matrix algebra over a field has
nonzero determinant. -/
theorem det_tracePairing_toMatrix_ne_zero
    {k : Type*} [Field k] [Fintype n] {i : Type*} [Fintype i] [DecidableEq i]
    (b : Basis i k (Matrix n n k)) :
    (LinearMap.BilinForm.toMatrix b (tracePairing k n)).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (tracePairing_nondegenerate k n)

/-- The trace-pairing matrix attached to a family of square matrices. -/
def tracePairingMatrix {A : Type*} [CommSemiring A] [Fintype n]
    {i : Type*} (b : i → Matrix n n A) : Matrix i i A :=
  fun r s ↦ Matrix.trace (b r * b s)

@[simp]
theorem tracePairingMatrix_apply {A : Type*} [CommSemiring A] [Fintype n]
    {i : Type*} (b : i → Matrix n n A) (r s : i) :
    tracePairingMatrix b r s = Matrix.trace (b r * b s) :=
  rfl

/-- Forming a trace-pairing matrix commutes with a change of coefficients. -/
theorem tracePairingMatrix_map
    {A B : Type*} [CommSemiring A] [CommSemiring B] [Fintype n]
    {i : Type*} (f : A →+* B) (b : i → Matrix n n A) :
    (tracePairingMatrix b).map f = tracePairingMatrix (fun r ↦ (b r).map f) := by
  ext r s
  change f (Matrix.trace (b r * b s)) =
    Matrix.trace ((b r).map f * (b s).map f)
  rw [AddMonoidHom.map_trace]
  exact congrArg Matrix.trace (Matrix.map_mul (f := f))

/-- If a family of matrices over a local ring reduces to a basis of the full matrix algebra,
then its trace-pairing determinant is a unit. -/
theorem isUnit_det_tracePairingMatrix_of_residue_basis
    {A : Type*} [CommRing A] [IsLocalRing A] [Fintype n]
    {i : Type*} [Fintype i] [DecidableEq i] (b : i → Matrix n n A)
    (bbar : Basis i (IsLocalRing.ResidueField A)
      (Matrix n n (IsLocalRing.ResidueField A)))
    (hbbar : ∀ r, bbar r = (b r).map (IsLocalRing.residue A)) :
    IsUnit (tracePairingMatrix b).det := by
  classical
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  rw [RingHom.map_det]
  change ((tracePairingMatrix b).map (IsLocalRing.residue A)).det ≠ 0
  rw [tracePairingMatrix_map]
  have hmatrix :
      tracePairingMatrix (fun r ↦ (b r).map (IsLocalRing.residue A)) =
        LinearMap.BilinForm.toMatrix bbar
          (tracePairing (IsLocalRing.ResidueField A) n) := by
    ext r s
    simp [tracePairingMatrix, hbbar]
  rw [hmatrix]
  exact det_tracePairing_toMatrix_ne_zero bbar

/-- A square family of matrices whose trace-pairing determinant is a unit is a basis of the
full matrix algebra.  This is the determinant form of the Nakayama step in Carayol's
argument. -/
theorem exists_basis_eq_of_isUnit_det_tracePairingMatrix
    {A : Type*} [CommRing A] [Fintype n] [DecidableEq n]
    (b : n × n → Matrix n n A) (hunit : IsUnit (tracePairingMatrix b).det) :
    ∃ bA : Basis (n × n) A (Matrix n n A), ∀ ij, bA ij = b ij := by
  classical
  let e : Basis (n × n) A (Matrix n n A) := Matrix.stdBasis A n n
  let C : Matrix (n × n) (n × n) A := e.toMatrix b
  let K : Matrix (n × n) (n × n) A :=
    LinearMap.BilinForm.toMatrix e (tracePairing A n)
  let F : Matrix n n A →ₗ[A] Matrix n n A := e.constr ℕ b
  have hFmatrix : LinearMap.toMatrix e e F = C := by
    exact (e.toMatrix_eq_toMatrix_constr b).symm
  have hgram : Cᵀ * K * C = tracePairingMatrix b := by
    calc
      Cᵀ * K * C =
          LinearMap.BilinForm.toMatrix e ((tracePairing A n).comp F F) := by
        rw [← hFmatrix]
        exact (LinearMap.BilinForm.toMatrix_comp (b := e) (c := e)
          (tracePairing A n) F F).symm
      _ = tracePairingMatrix b := by
        ext i j
        simp [F, LinearMap.BilinForm.toMatrix_apply, tracePairingMatrix,
          LinearMap.BilinForm.comp_apply]
  have hdet : IsUnit (Cᵀ * K * C).det := hgram.symm ▸ hunit
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hCunit : IsUnit C.det := isUnit_of_mul_isUnit_right hdet
  have hb := (Basis.is_basis_iff_det e).mpr hCunit
  let bA : Basis (n × n) A (Matrix n n A) := Basis.mk hb.1 hb.2.ge
  exact ⟨bA, fun ij ↦ by simp [bA]⟩

/-- The trace pairings of a matrix with the members of a matrix basis are obtained by
multiplying its coordinate row by the trace-pairing matrix. -/
theorem repr_vecMul_tracePairingMatrix
    {A : Type*} [CommRing A] [Fintype n]
    {i : Type*} [Fintype i] (b : Basis i A (Matrix n n A))
    (x : Matrix n n A) :
    (fun r ↦ b.repr x r) ᵥ* tracePairingMatrix b =
      fun s ↦ Matrix.trace (x * b s) := by
  funext s
  change (∑ r, b.repr x r * Matrix.trace (b r * b s)) = Matrix.trace (x * b s)
  calc
    _ = ∑ r, Matrix.trace ((b.repr x r • b r) * b s) := by
      apply Finset.sum_congr rfl
      intro r _
      simp
    _ = Matrix.trace ((∑ r, b.repr x r • b r) * b s) := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace (x * b s) := by rw [b.sum_repr]

/-- Coefficients with respect to a trace-nondegenerate matrix basis descend to a local
subalgebra as soon as the relevant pairwise traces do.  This is the linear-system step in
Carayol descent. -/
theorem repr_mem_localSubalgebra_of_trace_mem
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    [Fintype n] {i : Type*} [Fintype i] [DecidableEq i]
    (S : Subalgebra k A) [IsLocalRing S] [IsLocalHom S.val]
    (b : Basis i A (Matrix n n A))
    (hunit : IsUnit (tracePairingMatrix b).det)
    (hpair : ∀ r s, Matrix.trace (b r * b s) ∈ S)
    (x : Matrix n n A) (htrace : ∀ s, Matrix.trace (x * b s) ∈ S) :
    ∀ r, b.repr x r ∈ S := by
  let G : Matrix i i S := fun r s ↦ ⟨Matrix.trace (b r * b s), hpair r s⟩
  let t : i → S := fun s ↦ ⟨Matrix.trace (x * b s), htrace s⟩
  let f : S →+* A := S.val
  have hGmap : G.map f = tracePairingMatrix b := by
    ext r s
    rfl
  have hdet_map : f G.det = (tracePairingMatrix b).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det hGmap
  have hGdet : IsUnit G.det := by
    apply isUnit_of_map_unit f
    rwa [hdet_map]
  let c : i → S := t ᵥ* G⁻¹
  have hc : c ᵥ* G = t := by
    simp [c, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul G hGdet]
  have hcmap :
      (fun r ↦ f (c r)) ᵥ* tracePairingMatrix b =
        fun s ↦ Matrix.trace (x * b s) := by
    rw [← hGmap]
    funext s
    calc
      ((fun r ↦ f (c r)) ᵥ* G.map f) s = f ((c ᵥ* G) s) :=
        (RingHom.map_vecMul f G c s).symm
      _ = f (t s) := by rw [hc]
      _ = Matrix.trace (x * b s) := rfl
  have hcoeff : (fun r ↦ f (c r)) = fun r ↦ b.repr x r := by
    have hinj : Function.Injective (tracePairingMatrix b).vecMul :=
      Matrix.vecMul_injective_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det (tracePairingMatrix b)).mpr hunit)
    apply hinj
    exact hcmap.trans (repr_vecMul_tracePairingMatrix b x).symm
  intro r
  rw [← congrFun hcoeff r]
  exact (c r).2

/-! ## Extracting a matrix basis from the image of a representation -/

/-- For a monoid representation by square matrices, algebra generation by the image is the
same as linear spanning by the image: products of image matrices are again image matrices. -/
theorem span_range_eq_top_of_adjoin_range_eq_top
    {k G : Type*} [Field k] [Monoid G] [Fintype n] [DecidableEq n]
    (rho : G →* Matrix n n k)
    (h : Algebra.adjoin k (Set.range rho) = ⊤) :
    Submodule.span k (Set.range rho) = ⊤ := by
  have h' := congrArg Subalgebra.toSubmodule h
  rw [Algebra.adjoin_eq_span, MonoidHom.mclosure_range] at h'
  simpa only [MonoidHom.coe_mrange, Algebra.top_toSubmodule] using h'

/-- If the image of a matrix representation generates the full matrix algebra, one can choose
`n²` group elements whose matrices form a basis. -/
theorem exists_image_matrix_basis_of_adjoin_range_eq_top
    {k G : Type*} [Field k] [Monoid G] [Fintype n] [DecidableEq n]
    (rho : G →* Matrix n n k)
    (h : Algebra.adjoin k (Set.range rho) = ⊤) :
    ∃ (g : n × n → G) (b : Basis (n × n) k (Matrix n n k)),
      ∀ ij, b ij = rho (g ij) := by
  classical
  have hspan : ⊤ ≤ Submodule.span k (Set.range rho) :=
    (span_range_eq_top_of_adjoin_range_eq_top rho h).ge
  let I := (linearIndepOn_empty k id).extend (Set.empty_subset (Set.range rho))
  let b₀ : Basis I k (Matrix n n k) := Basis.ofSpan hspan
  let _ : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = Fintype.card (n × n) := by
    rw [← Module.finrank_eq_card_basis b₀]
    simp [Module.finrank_matrix]
  let e : I ≃ n × n := Fintype.equivOfCardEq hcard
  let b : Basis (n × n) k (Matrix n n k) := b₀.reindex e
  have hbmem (ij : n × n) : b ij ∈ Set.range rho := by
    have hmem : b₀ (e.symm ij) ∈ Set.range rho :=
      Basis.ofSpan_subset hspan (Set.mem_range_self (e.symm ij))
    simpa [b, Basis.reindex_apply] using hmem
  choose g hg using hbmem
  exact ⟨g, b, fun ij ↦ (hg ij).symm⟩

end Matrix

namespace Slop.OddRep

universe u

variable {k : Type u} {G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- Schur's lemma in the form needed for Burnside's theorem: over an algebraically closed
field, every endomorphism commuting with an irreducible representation is scalar. -/
theorem exists_smul_eq_of_isIrreducible_of_isAlgClosed
    [IsAlgClosed k] [FiniteDimensional k V]
    (rho : Representation k G V) (hirr : rho.IsIrreducible)
    (T : Module.End k V) (hT : ∀ g : G, Commute (rho g) T) :
    ∃ μ : k, T = μ • (1 : Module.End k V) := by
  let A := adjoinRange rho
  have hrho_mem : ∀ g : G, rho g ∈ A := fun g ↦
    Algebra.subset_adjoin (Set.mem_range_self g)
  letI : IsScalarTower k A V := ⟨fun _ _ _ ↦ rfl⟩
  haveI : IsSimpleModule A V := by
    have hnt : Nontrivial V := (isIrreducible_iff_forall rho).mp hirr |>.1
    letI : Nontrivial V := hnt
    haveI : Nontrivial (Submodule A V) := (Submodule.nontrivial_iff A).mpr hnt
    rw [isSimpleModule_iff]
    refine ⟨fun W ↦ ?_⟩
    have hW : ∀ g : G, ∀ v ∈ W.restrictScalars k, rho g v ∈ W.restrictScalars k :=
      fun g v hv ↦ W.smul_mem ⟨rho g, hrho_mem g⟩ hv
    simpa only [Submodule.restrictScalars_eq_bot_iff,
      Submodule.restrictScalars_eq_top_iff] using
        (isIrreducible_iff_forall rho).mp hirr |>.2 _ hW
  have hcentralizer : A ≤ Subalgebra.centralizer k ({T} : Set (Module.End k V)) := by
    apply Algebra.adjoin_le
    rintro x ⟨g, rfl⟩
    change ∀ y ∈ ({T} : Set (Module.End k V)), y * rho g = rho g * y
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (hT g).eq.symm
  have hcommute (a : A) : Commute (a.1 : Module.End k V) T := by
    have ha := hcentralizer a.2
    change ∀ y ∈ ({T} : Set (Module.End k V)), y * a.1 = a.1 * y at ha
    exact (ha T (Set.mem_singleton T)).symm
  let TA : Module.End A V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun a v ↦ by
        have h := LinearMap.congr_fun (hcommute a) v
        change T ((a.1 : Module.End k V) v) = (a.1 : Module.End k V) (T v)
        simpa only [Module.End.mul_apply] using h.symm }
  obtain ⟨μ, hμ⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
      (A := A) (V := V)).2 TA
  refine ⟨μ, LinearMap.ext fun v ↦ ?_⟩
  have hv := DFunLike.congr_fun hμ v
  change μ • v = T v at hv
  simpa only [LinearMap.smul_apply, Module.End.one_apply] using hv.symm

/-- If an irreducible scalar extension of a representation is taken to an algebraically
closed field, then every commuting endomorphism was already scalar over the original field. -/
theorem exists_smul_eq_of_isIrreducible_baseChange_of_isAlgClosed
    [FiniteDimensional k V]
    (l : Type*) [Field l] [IsAlgClosed l] [Algebra k l]
    (rho : Representation k G V)
    (hirr : (baseChange l rho).IsIrreducible)
    (T : Module.End k V) (hT : ∀ g : G, Commute (rho g) T) :
    ∃ μ : k, T = μ • (1 : Module.End k V) := by
  let Tl : Module.End l (l ⊗[k] V) := T.baseChange l
  have hTl : ∀ g : G, Commute (baseChange l rho g) Tl := by
    intro g
    change (LinearMap.baseChange l (rho g)).comp (LinearMap.baseChange l T) =
      (LinearMap.baseChange l T).comp (LinearMap.baseChange l (rho g))
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    have hcomp : (rho g).comp T = T.comp (rho g) := by
      exact (hT g).eq
    rw [hcomp]
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_isIrreducible_of_isAlgClosed (baseChange l rho) hirr Tl hTl
  have hirr₀ : rho.IsIrreducible := isIrreducible_of_baseChange rho l hirr
  letI : Nontrivial V := (isIrreducible_iff_forall rho).mp hirr₀ |>.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hc_mem : c ⊗ₜ[k] v ∈ LinearMap.range (TensorProduct.mk k l V 1) := by
    refine ⟨T v, ?_⟩
    have happ := LinearMap.congr_fun hc (1 ⊗ₜ[k] v)
    simp only [Tl, LinearMap.baseChange_tmul, LinearMap.smul_apply,
      Module.End.one_apply] at happ
    exact happ.trans (by rw [TensorProduct.smul_tmul']; simp)
  obtain ⟨μ, hμ⟩ :=
    (smul_tmul_mem_range_iff (k := k) (V := V) l hv c).mp hc_mem
  refine ⟨μ, LinearMap.ext fun w ↦ ?_⟩
  have happ := LinearMap.congr_fun hc (1 ⊗ₜ[k] w)
  simp only [Tl, LinearMap.baseChange_tmul, LinearMap.smul_apply,
    Module.End.one_apply] at happ
  rw [← hμ] at happ
  have hmove := TensorProduct.tmul_smul (R := k) μ (1 : l) w
  have hright :
      (algebraMap k l μ) • ((1 : l) ⊗ₜ[k] w) = (1 : l) ⊗ₜ[k] (μ • w) := by
    rw [IsScalarTower.algebraMap_smul l]
    exact hmove.symm
  have happ' : (1 : l) ⊗ₜ[k] T w = (1 : l) ⊗ₜ[k] (μ • w) :=
    happ.trans hright
  have hw := Module.Flat.tensorProduct_mk_injective k V l happ'
  simpa only [LinearMap.smul_apply, Module.End.one_apply] using hw

/-- Burnside's theorem over the original field, deduced from irreducibility after extension
to an algebraically closed field. -/
theorem adjoinRange_eq_top_of_isIrreducible_baseChange_of_isAlgClosed
    [FiniteDimensional k V]
    (l : Type*) [Field l] [IsAlgClosed l] [Algebra k l]
    (rho : Representation k G V)
    (hirr : (baseChange l rho).IsIrreducible) :
    adjoinRange rho = ⊤ := by
  apply adjoinRange_eq_top rho
  · exact isIrreducible_of_baseChange rho l hirr
  · exact exists_smul_eq_of_isIrreducible_baseChange_of_isAlgClosed l rho hirr

/-- Burnside's theorem for the project's notion of absolute irreducibility. -/
theorem adjoinRange_eq_top_of_isAbsolutelyIrreducible
    [FiniteDimensional k V]
    (rho : Representation k G V) [rho.IsAbsolutelyIrreducible.{u}] :
    adjoinRange rho = ⊤ := by
  apply adjoinRange_eq_top_of_isIrreducible_baseChange_of_isAlgClosed
    (AlgebraicClosure k) rho
  exact Representation.IsAbsolutelyIrreducible.absolutelyIrreducible
    (ρ := rho) (AlgebraicClosure k) inferInstance inferInstance

/-- The matrix-valued monoid homomorphism associated to a representation on coordinate
vectors. -/
def matrixMonoidHom {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Representation k G (n → k)) : G →* Matrix n n k :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp rho

@[simp]
theorem matrixMonoidHom_apply {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Representation k G (n → k)) (g : G) :
    matrixMonoidHom rho g = LinearMap.toMatrixAlgEquiv' (rho g) :=
  rfl

/-- Algebra generation by a representation is unchanged when its endomorphisms are written
as matrices in the standard basis. -/
theorem adjoin_matrixMonoidHom_range_eq_top_of_adjoinRange_eq_top
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Representation k G (n → k)) (h : adjoinRange rho = ⊤) :
    Algebra.adjoin k (Set.range (matrixMonoidHom rho)) = ⊤ := by
  let e : Module.End k (n → k) ≃ₐ[k] Matrix n n k :=
    LinearMap.toMatrixAlgEquiv'
  have hrange : Set.range (matrixMonoidHom rho) = e.toAlgHom '' Set.range rho := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨rho g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  change Algebra.adjoin k (Set.range rho) = ⊤ at h
  rw [hrange, Algebra.adjoin_image, h, Algebra.map_top]
  exact (AlgHom.range_eq_top e.toAlgHom).mpr e.surjective

/-- An absolutely irreducible representation on coordinate vectors admits a collection of
group elements whose matrices form a basis of the full matrix algebra. -/
theorem exists_image_matrix_basis_of_isAbsolutelyIrreducible
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Representation k G (n → k)) [rho.IsAbsolutelyIrreducible.{u}] :
    ∃ (g : n × n → G) (b : Basis (n × n) k (Matrix n n k)),
      ∀ ij, b ij = matrixMonoidHom rho (g ij) := by
  apply Matrix.exists_image_matrix_basis_of_adjoin_range_eq_top
  exact adjoin_matrixMonoidHom_range_eq_top_of_adjoinRange_eq_top rho
    (adjoinRange_eq_top_of_isAbsolutelyIrreducible rho)

end Slop.OddRep
