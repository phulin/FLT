/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle
public import FLT.Deformations.Bockle.Cohomology
public import FLT.Deformations.FiniteImage
public import FLT.Deformations.IsProartinian
public import FLT.KnownIn1980s.CommutativeAlgebra.PowerSeries
public import FLT.Mathlib.RingTheory.MvPowerSeries.KrullDimension
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.MvPowerSeries.Inverse
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
  [IsLocalRing D] [IsLocalHom (algebraMap R D)] [IsResidueAlgebra R D]
  [IsProartinian D]
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

/-- Reduction modulo a coefficient scalar can be computed before passing through a Böckle
presentation: it is the quotient of the power-series ring by the relations together with the
image of that scalar. -/
noncomputable def BocklePresentation.modScalarRingEquiv
    (P : BocklePresentation R D) (pi : R) :
    let A := MvPowerSeries (Fin P.numVariables) R
    (A ⧸ Ideal.ofList (P.relations ++ [algebraMap R A pi])) ≃+*
      ModScalarRing (D := D) pi := by
  let A := MvPowerSeries (Fin P.numVariables) R
  let I : Ideal A := Ideal.ofList P.relations
  let J : Ideal A := Ideal.span {algebraMap R A pi}
  let e := Classical.choice P.quotientEquiv
  have hsource : Ideal.ofList (P.relations ++ [algebraMap R A pi]) = I ⊔ J := by
    rw [Ideal.ofList_append, Ideal.ofList_singleton]
  have htarget : scalarIdeal (D := D) pi =
      (J.map (Ideal.Quotient.mk I)).map e.toRingEquiv := by
    have hJmap : J.map (Ideal.Quotient.mk I) =
        Ideal.span {algebraMap R (A ⧸ I) pi} := by
      change (Ideal.span {algebraMap R A pi}).map (Ideal.Quotient.mk I) = _
      rw [Ideal.map_span]
      simp
    rw [hJmap, Ideal.map_span]
    simp only [scalarIdeal, Set.image_singleton]
    congr 1
    simpa using e.commutes pi
  exact
    ((Ideal.quotEquivOfEq hsource).trans
      (DoubleQuot.quotQuotEquivQuotSup I J).symm).trans
        (Ideal.quotientEquivAlg (J.map (Ideal.Quotient.mk I))
          (scalarIdeal (D := D) pi) e htarget).toRingEquiv

/-- If reduction modulo a nonunit coefficient scalar is finite, the relations together with
that scalar generate an ideal of definition in the power-series ring. -/
theorem BocklePresentation.radical_relationScalarIdeal_eq_maximalIdeal
    (P : BocklePresentation R D) (pi : R) (hpi : Irreducible pi)
    [Finite (ModScalarRing (D := D) pi)] :
    let A := MvPowerSeries (Fin P.numVariables) R
    (Ideal.ofList (P.relations ++ [algebraMap R A pi])).radical =
      IsLocalRing.maximalIdeal A := by
  let A := MvPowerSeries (Fin P.numVariables) R
  let J : Ideal A := Ideal.ofList (P.relations ++ [algebraMap R A pi])
  let Q := A ⧸ J
  have hproperD : scalarIdeal (D := D) pi ≠ ⊤ := by
    rw [scalarIdeal]
    apply Ideal.span_singleton_eq_top.not.mpr
    rw [isUnit_map_iff (algebraMap R D)]
    exact hpi.not_isUnit
  letI : Nontrivial (ModScalarRing (D := D) pi) :=
    Ideal.Quotient.nontrivial_iff.mpr hproperD
  let e := P.modScalarRingEquiv pi
  letI : Nontrivial Q := e.toEquiv.nontrivial_congr.mpr inferInstance
  letI : Finite Q := Finite.of_equiv (ModScalarRing (D := D) pi) e.symm.toEquiv
  letI : IsArtinianRing Q := isArtinian_of_finite
  letI : Ring.KrullDimLE 0 Q := isArtinianRing_iff_krullDimLE_zero.mp inferInstance
  have hJne : J ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hall : ∀ p ∈ J.minimalPrimes, p = IsLocalRing.maximalIdeal A := by
    intro p hp
    haveI := hp.isPrime
    have hpmax : p.IsMaximal :=
      (Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mp
        (show Ring.KrullDimLE 0 Q from inferInstance)) p hp
    exact hpmax.eq_of_le (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (IsLocalRing.le_maximalIdeal hpmax.ne_top)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hJne
  change J.radical = IsLocalRing.maximalIdeal A
  rw [← Ideal.sInf_minimalPrimes,
    Set.eq_singleton_iff_unique_mem.mpr ⟨hall p hp ▸ hp, hall⟩, sInf_singleton]

/-- In a balanced Böckle presentation, finite reduction modulo a uniformizer forces the number
of relations to equal the number of power-series variables.  The lower dimension bound comes
from the iterated power-series description; the upper bound is Krull's height theorem applied
to the finite-colength ideal generated by the relations and the uniformizer. -/
theorem BocklePresentation.relations_length_eq_numVariables_of_finite_modScalar
    (P : BocklePresentation R D) (pi : R) (hpi : Irreducible pi)
    [Finite (ModScalarRing (D := D) pi)] :
    P.relations.length = P.numVariables := by
  classical
  let A := MvPowerSeries (Fin P.numVariables) R
  let rs : List A := P.relations ++ [algebraMap R A pi]
  let J : Ideal A := Ideal.ofList rs
  have hrad : J.radical = IsLocalRing.maximalIdeal A :=
    P.radical_relationScalarIdeal_eq_maximalIdeal pi hpi
  have hmmin : IsLocalRing.maximalIdeal A ∈ J.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hheight : (IsLocalRing.maximalIdeal A).height ≤ rs.toFinset.card := by
    apply Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    simpa [J, Ideal.ofList] using hmmin
  have hupper : ringKrullDim A ≤ (rs.length : WithBot ℕ∞) := by
    calc
      ringKrullDim A =
          ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
      _ ≤ ((rs.toFinset.card : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr hheight
      _ ≤ (rs.length : WithBot ℕ∞) := by
        exact_mod_cast List.toFinset_card_le rs
  have hlower : (1 + P.numVariables : ℕ) ≤ rs.length := by
    have hdim :=
      (ringKrullDim_add_nat_le_ringKrullDim_mvPowerSeries_fin R P.numVariables).trans hupper
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one R] at hdim
    exact_mod_cast hdim
  simp only [rs, List.length_append, List.length_singleton] at hlower
  apply Nat.le_antisymm P.relations_le_variables
  omega

/-- Finite reduction modulo a uniformizer turns the relations together with the uniformizer
into a system of parameters.  The classical Cohen--Macaulay theorem for power-series rings over
a DVR therefore makes this list weakly regular. -/
theorem BocklePresentation.isRegularAt_of_finite_modScalar
    (P : BocklePresentation R D) (pi : R) (hpi : Irreducible pi)
    [Finite (ModScalarRing (D := D) pi)] :
    P.IsRegularAt pi := by
  let A := MvPowerSeries (Fin P.numVariables) R
  let rs : List A := P.relations ++ [algebraMap R A pi]
  apply MvPowerSeries.isWeaklyRegular_of_length_eq_dimension_of_radical_eq_maximalIdeal
    R P.numVariables rs
  · simp only [rs, List.length_append, List.length_singleton]
    rw [P.relations_length_eq_numVariables_of_finite_modScalar pi hpi]
  · exact P.radical_relationScalarIdeal_eq_maximalIdeal pi hpi

/-- The decomposed arithmetic and commutative-algebra data needed in Böckle's argument.
Unlike `BockleFinitenessData`, this structure does not assume module finiteness or regularity:
module finiteness is derived topologically, and regularity follows from the finite scalar
reduction by the classical system-of-parameters theorem. -/
structure BockleArithmeticData (rho : FramedGaloisRep K D n) where
  /-- Böckle's balanced power-series presentation. -/
  presentation : BocklePresentation R D
  /-- The coefficient-ring uniformizer. -/
  uniformizer : R
  /-- Potential modularity and Carayol trace generation data. -/
  finiteImage : ModScalarFiniteImageData rho uniformizer

/-- Assemble the full arithmetic package from adjoint tangent--obstruction parameters and
the finite-image-after-restriction input.  Trace generation is deliberately supplied before
scalar reduction; the general quotient theorem performs that formal step here. -/
theorem BockleAdjointParameterInput.exists_bockleArithmeticData
    {k G : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {rhoBar : Representation k G (Fin 2 → k)}
    [Module.Finite k (BockleObstructionSpace rhoBar)]
    [ContinuousSMul R D]
    {residueEquiv : IsLocalRing.ResidueField R ≃+* k}
    (P : BockleAdjointParameterInput (R := R) (D := D) residueEquiv rhoBar)
    (rho : FramedGaloisRep K D n) (pi : R) (hpi : Irreducible pi)
    (hfinite : (rho.quotient (scalarIdeal (D := D) pi)).FiniteImageAfterRestriction)
    (htrace : rho.IsTopologicallyTraceGenerated (k := R)) :
    Nonempty (BockleArithmeticData (R := R) rho) := by
  obtain ⟨presentation⟩ := P.exists_bocklePresentation
  letI : IsNoetherianRing D := presentation.isNoetherianRing
  letI : Finite (IsLocalRing.ResidueField D) :=
    Finite.of_equiv (IsLocalRing.ResidueField R)
      (IsResidueAlgebra.algEquiv R D).toEquiv
  exact ⟨{
    presentation := presentation
    uniformizer := pi
    finiteImage := {
      uniformizer_irreducible := hpi
      afterRestriction := hfinite
      traceGenerated :=
        FramedGaloisRep.IsTopologicallyTraceGenerated.quotientScalar rho htrace pi } }⟩

/-- Assemble the usual Böckle finiteness data after deriving finiteness modulo the uniformizer
from the finite-image criterion. -/
noncomputable def BockleArithmeticData.toBockleFinitenessData
    {rho : FramedGaloisRep K D n} (h : BockleArithmeticData (R := R) rho) :
    BockleFinitenessData R D := by
  letI : IsNoetherianRing D := h.presentation.isNoetherianRing
  letI : Finite (IsLocalRing.ResidueField D) :=
    Finite.of_equiv (IsLocalRing.ResidueField R)
      (IsResidueAlgebra.algEquiv R D).toEquiv
  have hmod : Finite (ModScalarRing (D := D) h.uniformizer) := h.finiteImage.finite
  exact
    { presentation := h.presentation
      uniformizer := h.uniformizer
      uniformizer_irreducible := h.finiteImage.uniformizer_irreducible
      finite := moduleFinite_of_finite_modScalar h.uniformizer
        h.finiteImage.uniformizer_irreducible
      regularAt := h.presentation.isRegularAt_of_finite_modScalar h.uniformizer
        h.finiteImage.uniformizer_irreducible }

end Deformation
