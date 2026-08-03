/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.ModScalar
public import FLT.Deformations.RepresentationTheory.FiniteImage
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Finite-image criterion after reduction modulo a scalar

This file packages the two precise inputs in the difficult direction of the Carayol
finite-image criterion for a representation reduced modulo a DVR uniformizer:

* finite image after restriction to a finite-index subgroup;
* generation of the coefficient algebra by traces.

The roots-of-unity integrality argument and the conclusion that the reduced coefficient ring is
finite are derived from these inputs.
-/

@[expose] public section

namespace Deformation

universe uK uR uD un

variable {K : Type uK} [Field K]
variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField R)]
variable {D : Type uD} [CommRing D] [TopologicalSpace D] [IsTopologicalRing D]
  [Algebra R D] [IsLocalRing D] [IsLocalHom (algebraMap R D)] [IsNoetherianRing D]
  [Finite (IsLocalRing.ResidueField D)]
variable {n : Type un} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The arithmetic data in the finite-image proof for a representation modulo a DVR
uniformizer.  The conclusion that `D / pi D` is finite is deliberately not a field. -/
structure ModScalarFiniteImageData (rho : FramedGaloisRep K D n) (pi : R) where
  /-- The chosen scalar generates the maximal ideal of the DVR. -/
  uniformizer_irreducible : Irreducible pi
  /-- Potential modularity and an `R = T` theorem give finite image after restriction. -/
  afterRestriction :
    (rho.quotient (scalarIdeal (D := D) pi)).FiniteImageAfterRestriction
  /-- Carayol's theorem says that an absolutely irreducible universal deformation is generated
  by its traces. -/
  traceGenerated :
    (rho.quotient (scalarIdeal (D := D) pi)).IsTraceGenerated
      (k := ModScalarCoefficient (D := D) pi)

/-- Carayol's criterion, finite-index descent, and local commutative algebra make the
coefficient ring modulo a uniformizer finite. -/
theorem ModScalarFiniteImageData.finite
    {rho : FramedGaloisRep K D n} {pi : R}
    (h : ModScalarFiniteImageData rho pi) : Finite (ModScalarRing (D := D) pi) := by
  have hproper : scalarIdeal (D := D) pi ≠ ⊤ := by
    rw [scalarIdeal]
    apply Ideal.span_singleton_eq_top.not.mpr
    rw [isUnit_map_iff (algebraMap R D)]
    exact h.uniformizer_irreducible.not_isUnit
  letI : Nontrivial (ModScalarRing (D := D) pi) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  letI : IsLocalRing (ModScalarRing (D := D) pi) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk (scalarIdeal (D := D) pi)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  letI : Finite (IsLocalRing.ResidueField (ModScalarRing (D := D) pi)) :=
    Finite.of_surjective
      (IsLocalRing.ResidueField.map (Ideal.Quotient.mk (scalarIdeal (D := D) pi)))
      (IsLocalRing.ResidueField.map_surjective _ Ideal.Quotient.mk_surjective)
  letI : Finite (ModScalarCoefficient (D := D) pi) :=
    finite_modScalarCoefficient pi h.uniformizer_irreducible
  exact
    FramedGaloisRep.finite_of_hasFiniteImage_of_isTraceGenerated
      (rho.quotient (scalarIdeal (D := D) pi)) h.afterRestriction.finite
        h.traceGenerated

end Deformation
