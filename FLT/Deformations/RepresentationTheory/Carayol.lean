/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

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
