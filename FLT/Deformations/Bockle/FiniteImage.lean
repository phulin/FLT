/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle
public import FLT.Deformations.FiniteImage
public import FLT.Deformations.IsProartinian
public import Mathlib.Topology.Algebra.Module.Compact

/-!
# Böckle presentations and finite-image arithmetic

This file joins the finite-image proof for a universal representation to Böckle's balanced
presentation.  It proves the topological Nakayama step from finiteness modulo a uniformizer to
module finiteness, and keeps the final regularity implication explicit.
-/

@[expose] public section

namespace Deformation

open IsLocalRing

universe uK u un

variable {K : Type uK} [Field K]
variable {R D : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField R)]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [IsLocalRing.IsAdicTopology R]
  [CommRing D] [TopologicalSpace D] [IsTopologicalRing D] [Algebra R D]
  [IsLocalRing D] [IsLocalHom (algebraMap R D)] [IsProartinian D]
variable {n : Type un} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Topological Nakayama for a pro-Artinian algebra over a compact local coefficient ring.
If reduction modulo a nonunit scalar is finite, lift all elements of that finite quotient and
span the lifts.  Successive approximation makes this finitely generated submodule dense, while
compactness makes it closed, so it is the whole algebra. -/
theorem moduleFinite_of_finite_modScalar
    (pi : R) (hpi : Irreducible pi) [Finite (ModScalarRing (D := D) pi)] :
    Module.Finite R D := by
  classical
  let I : Ideal D := scalarIdeal (D := D) pi
  let Q := D ⧸ I
  let lift : Q → D := fun q => Classical.choose (Ideal.Quotient.mk_surjective q)
  have hlift (q : Q) : Ideal.Quotient.mk I (lift q) = q :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective q)
  let N : Submodule R D := Submodule.span R (Set.range lift)
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range lift)
  have hdecomp (x : D) :
      ∃ y ∈ N, ∃ z : D, x - y = algebraMap R D pi * z := by
    let y := lift (Ideal.Quotient.mk I x)
    have hy : y ∈ N := Submodule.subset_span ⟨_, rfl⟩
    have hxy : x - y ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp [y, hlift]
    change x - y ∈ scalarIdeal (D := D) pi at hxy
    rw [scalarIdeal, Ideal.mem_span_singleton] at hxy
    exact ⟨y, hy, hxy⟩
  let a : D := algebraMap R D pi
  have happ : ∀ m : ℕ, ∀ x : D, ∃ y ∈ N, ∃ z : D, x - y = a ^ m * z := by
    intro m
    induction m with
    | zero =>
        intro x
        exact ⟨0, N.zero_mem, x, by simp⟩
    | succ m ih =>
        intro x
        obtain ⟨y, hy, z, hz⟩ := ih x
        obtain ⟨y', hy', z', hz'⟩ := hdecomp z
        refine ⟨y + a ^ m * y', N.add_mem hy ?_, z', ?_⟩
        · simpa [a, Algebra.smul_def] using N.smul_mem (pi ^ m) hy'
        · calc
            x - (y + a ^ m * y') = (x - y) - a ^ m * y' := by ring
            _ = a ^ m * z - a ^ m * y' := by rw [hz]
            _ = a ^ m * (z - y') := by ring
            _ = a ^ m * (a * z') := by rw [hz']
            _ = a ^ (m + 1) * z' := by rw [pow_succ]; ring
  have ha : a ∈ maximalIdeal D := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro haunit
    exact hpi.not_isUnit ((isUnit_map_iff (algebraMap R D) pi).mp haunit)
  have halg : Continuous (algebraMap R D) :=
    isContinuous_of_isProartinian_of_isLocalHom (algebraMap R D)
  letI : ContinuousSMul R D := continuousSMul_of_algebraMap R D halg
  have hNdense : Dense (N : Set D) := by
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro x
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    obtain ⟨J, hJopen, hJU⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hU
    obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_le_of_isProartinian J hJopen
    obtain ⟨y, hy, z, hxyz⟩ := happ m x
    refine ⟨y, hy, hJU ?_⟩
    have hpow : a ^ m ∈ maximalIdeal D ^ m := Ideal.pow_mem_pow ha m
    have hdiff : x - y ∈ J := hxyz ▸ J.mul_mem_right z (hm hpow)
    change y - x ∈ J
    simpa only [neg_sub] using J.neg_mem hdiff
  have hNclosed : IsClosed (N : Set D) :=
    (Submodule.isCompact_of_fg hNfg).isClosed
  have hNtop : N = ⊤ := by
    apply top_unique
    intro x _
    have hx : x ∈ closure (N : Set D) := hNdense x
    rwa [hNclosed.closure_eq] at hx
  exact Module.Finite.of_fg_top (hNtop ▸ hNfg)

/-- The decomposed arithmetic and commutative-algebra data needed in Böckle's argument.
Unlike `BockleFinitenessData`, this structure does not assume module finiteness or regularity:
module finiteness is derived topologically, and regularity is required only as a consequence of
the already-derived finiteness modulo a uniformizer. -/
structure BockleArithmeticData (rho : FramedGaloisRep K D n) where
  /-- Böckle's balanced power-series presentation. -/
  presentation : BocklePresentation R D
  /-- The universal deformation ring has the same finite residue field as its coefficient ring. -/
  finiteResidueField : Finite (IsLocalRing.ResidueField D)
  /-- The coefficient-ring uniformizer. -/
  uniformizer : R
  /-- Potential modularity and Carayol trace generation data. -/
  finiteImage : ModScalarFiniteImageData rho uniformizer
  /-- The Cohen--Macaulay/system-of-parameters step in the balanced presentation. -/
  regularAt_of_modScalarFinite :
    Finite (ModScalarRing (D := D) uniformizer) →
      presentation.IsRegularAt uniformizer

/-- Assemble the usual Böckle finiteness data after deriving finiteness modulo the uniformizer
from the finite-image criterion. -/
noncomputable def BockleArithmeticData.toBockleFinitenessData
    {rho : FramedGaloisRep K D n} (h : BockleArithmeticData (R := R) rho) :
    BockleFinitenessData R D := by
  letI : IsNoetherianRing D := h.presentation.isNoetherianRing
  letI : Finite (IsLocalRing.ResidueField D) := h.finiteResidueField
  have hmod : Finite (ModScalarRing (D := D) h.uniformizer) := h.finiteImage.finite
  exact
    { presentation := h.presentation
      uniformizer := h.uniformizer
      uniformizer_irreducible := h.finiteImage.uniformizer_irreducible
      finite := moduleFinite_of_finite_modScalar h.uniformizer
        h.finiteImage.uniformizer_irreducible
      regularAt := h.regularAt_of_modScalarFinite hmod }

end Deformation
