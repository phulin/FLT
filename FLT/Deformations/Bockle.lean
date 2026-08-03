/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Regular.RegularSequence
public import FLT.Mathlib.RingTheory.Flat.TorsionFree

/-!
# Böckle presentations of deformation rings

This file packages the commutative-algebra data used in the Böckle step of the
hardly ramified lifting theorem.  A balanced presentation has the form

`R⟦X₁, ..., Xᵣ⟧ / (f₁, ..., fₛ)` with `s ≤ r`.

Once the relation sequence followed by a uniformizer is weakly regular, the
uniformizer acts regularly on the quotient.  Over a DVR this implies flatness.
-/

@[expose] public section

namespace Deformation

open RingTheory

universe u

/-- A balanced power-series presentation of an `R`-algebra.  The inequality between the
number of relations and variables is the output of Böckle's obstruction-theory argument. -/
structure BocklePresentation
    (R D : Type u) [CommRing R] [CommRing D] [Algebra R D] where
  /-- The number of power-series variables. -/
  numVariables : ℕ
  /-- The relations defining the quotient. -/
  relations : List (MvPowerSeries (Fin numVariables) R)
  /-- There are no more relations than variables. -/
  relations_le_variables : relations.length ≤ numVariables
  /-- The presented quotient is the deformation ring. -/
  quotientEquiv : Nonempty
    ((MvPowerSeries (Fin numVariables) R ⧸ Ideal.ofList relations) ≃ₐ[R] D)

/-- A finite-variable Böckle presentation over a Noetherian coefficient ring makes the
presented deformation ring Noetherian. -/
noncomputable def BocklePresentation.isNoetherianRing
    {R D : Type u} [CommRing R] [IsNoetherianRing R] [CommRing D] [Algebra R D]
    (P : BocklePresentation R D) : IsNoetherianRing D := by
  let A := MvPowerSeries (Fin P.numVariables) R
  let e := Classical.choice P.quotientEquiv
  haveI : IsNoetherianRing A := inferInstance
  haveI : IsNoetherianRing (A ⧸ Ideal.ofList P.relations) := inferInstance
  exact isNoetherianRing_of_ringEquiv (A ⧸ Ideal.ofList P.relations) e.toRingEquiv

/-- The regular-sequence conclusion used at the end of Böckle's argument: the defining
relations followed by `π` form a weakly regular sequence in the power-series ring. -/
def BocklePresentation.IsRegularAt
    {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]
    (P : BocklePresentation R D) (π : R) : Prop :=
  let A := MvPowerSeries (Fin P.numVariables) R
  RingTheory.Sequence.IsWeaklyRegular A
    (P.relations ++ [algebraMap R A π])

/-- The last term of a regular Böckle presentation acts regularly on the presented algebra. -/
theorem BocklePresentation.isSMulRegular_of_isRegularAt
    {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]
    (P : BocklePresentation R D) {π : R} (hπ : P.IsRegularAt π) :
    IsSMulRegular D π := by
  let A := MvPowerSeries (Fin P.numVariables) R
  let e := Classical.choice P.quotientEquiv
  have htail :=
    (RingTheory.Sequence.isWeaklyRegular_append_iff A P.relations
      [algebraMap R A π]).mp hπ |>.2
  have hquotA : IsSMulRegular
      (A ⧸ (Ideal.ofList P.relations • (⊤ : Submodule A A)))
      (algebraMap R A π) :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mp htail
  have heq : (Ideal.ofList P.relations • (⊤ : Submodule A A)) =
      Ideal.ofList P.relations := by
    simpa using Ideal.smul_top_eq_map (M := A) (Ideal.ofList P.relations)
  let qlin : (A ⧸ (Ideal.ofList P.relations • (⊤ : Submodule A A))) ≃ₗ[R]
      (A ⧸ Ideal.ofList P.relations) :=
    (Submodule.quotEquivOfEq _ _ heq).restrictScalars R
  have hquotR : IsSMulRegular (A ⧸ Ideal.ofList P.relations) π := by
    rw [← qlin.isSMulRegular_congr π]
    intro x y hxy
    apply hquotA
    simpa [Algebra.smul_def] using hxy
  exact (e.toLinearEquiv.isSMulRegular_congr π).mp hquotR

/-- The precise output needed from finiteness plus Böckle's balanced-presentation argument. -/
structure BockleFinitenessData
    (R D : Type u) [CommRing R] [CommRing D] [Algebra R D] where
  /-- A balanced presentation of the deformation ring. -/
  presentation : BocklePresentation R D
  /-- A uniformizer of the coefficient DVR. -/
  uniformizer : R
  /-- The chosen uniformizer is irreducible. -/
  uniformizer_irreducible : Irreducible uniformizer
  /-- The deformation ring is finite over the coefficient ring. -/
  finite : Module.Finite R D
  /-- The defining relations followed by the uniformizer form a regular sequence. -/
  regularAt : presentation.IsRegularAt uniformizer

/-- The uniformizer supplied by Böckle finiteness data acts regularly on the deformation ring. -/
theorem BockleFinitenessData.uniformizer_isSMulRegular
    {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]
    (h : BockleFinitenessData R D) : IsSMulRegular D h.uniformizer :=
  h.presentation.isSMulRegular_of_isRegularAt h.regularAt

/-- Böckle finiteness data make the presented algebra flat over a coefficient DVR. -/
theorem BockleFinitenessData.flat
    {R D : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing D] [Algebra R D] (h : BockleFinitenessData R D) :
    Module.Flat R D :=
  Module.Flat.of_isSMulRegular_irreducible
    h.uniformizer_irreducible h.uniformizer_isSMulRegular

end Deformation
