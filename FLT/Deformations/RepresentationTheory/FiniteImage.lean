/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.Mathlib.GroupTheory.Index

/-!
# Finite images of framed Galois representations

This file contains the elementary group-theoretic and coefficient-change steps in the
finite-image argument for universal deformation rings.  In particular, it separates the
arithmetic assertion that a representation has finite image after restriction to a
finite-index subgroup from the formal deduction that its original image is finite.
-/

@[expose] public section

open scoped Pointwise

namespace FramedGaloisRep

universe uK uA un

variable {K : Type uK} [Field K]
variable {A : Type uA} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {n : Type un} [Fintype n] [DecidableEq n]

/-- Reduce a framed representation entrywise modulo an ideal of its coefficient ring. -/
noncomputable def quotient (rho : FramedGaloisRep K A n) (I : Ideal A) :
    FramedGaloisRep K (A ⧸ I) n :=
  rho.baseChange (Ideal.Quotient.mk I) continuous_quot_mk

/-- A framed representation has finite image if its associated homomorphism to `GL` does. -/
def HasFiniteImage (rho : FramedGaloisRep K A n) : Prop :=
  Finite rho.GL.toMonoidHom.range

/-- The exact elementary output needed from a potential-modularity restriction argument:
there is a finite-index subgroup on which the representation has finite image. -/
structure FiniteImageAfterRestriction (rho : FramedGaloisRep K A n) where
  /-- The subgroup to which the representation is restricted. -/
  subgroup : Subgroup (Field.absoluteGaloisGroup K)
  /-- The restriction subgroup has finite index. -/
  finiteIndex : subgroup.FiniteIndex
  /-- The restricted representation has finite image. -/
  restrictedFinite : Finite (rho.GL.toMonoidHom.comp subgroup.subtype).range

/-- Finite image after restriction to a finite-index subgroup implies finite image globally. -/
theorem FiniteImageAfterRestriction.finite
    {rho : FramedGaloisRep K A n} (h : rho.FiniteImageAfterRestriction) :
    rho.HasFiniteImage := by
  letI := h.finiteIndex
  exact rho.GL.toMonoidHom.finite_range_of_finiteIndex_restrict
    h.subgroup h.restrictedFinite

end FramedGaloisRep
