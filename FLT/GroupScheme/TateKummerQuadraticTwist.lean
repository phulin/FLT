/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.QuadraticDescent
public import FLT.GroupScheme.TateKummer

/-!
# Quadratic twists of Tate--Kummer coordinate algebras

This file starts the explicit descent of a Tate--Kummer finite-flat group scheme along
`R[X] / (X² - tX + n)`.  Quadratic conjugation on the cover is paired with inversion on
the group scheme.  Their tensor product is the descent involution, and its fixed subalgebra
is the coordinate algebra of the quadratic twist.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace TateKummer.QuadraticTwist

variable (R : Type u) [CommRing R]
variable (N : ℕ) [NeZero N] (u : Rˣ) (t n : R)

/-- The Tate--Kummer coordinate algebra after extension to the quadratic cover. -/
abbrev CoverCoordinateAlgebra :=
  QuadraticDescent.Algebra R t n ⊗[R] TateKummer.CoordinateAlgebra (R := R) N u

/-- Quadratic conjugation on the cover paired with inversion on the Tate--Kummer group. -/
noncomputable def descentAlgEquiv :
    CoverCoordinateAlgebra R N u t n ≃ₐ[R] CoverCoordinateAlgebra R N u t n :=
  Algebra.TensorProduct.congr
    (QuadraticDescent.conjugationAlgEquiv R t n)
    (TateKummer.antipodeAlgEquiv N u)

@[simp]
lemma descentAlgEquiv_tmul
    (a : QuadraticDescent.Algebra R t n)
    (h : TateKummer.CoordinateAlgebra (R := R) N u) :
    descentAlgEquiv R N u t n (a ⊗ₜ[R] h) =
      QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R]
        TateKummer.antipodeAlgEquiv N u h := by
  rfl

/-- The descent automorphism has order two. -/
@[simp]
lemma descentAlgEquiv_symm :
    (descentAlgEquiv R N u t n).symm = descentAlgEquiv R N u t n := by
  unfold descentAlgEquiv
  rw [← Algebra.TensorProduct.congr_symm]
  simp only [QuadraticDescent.conjugationAlgEquiv_symm,
    TateKummer.antipodeAlgEquiv_symm]

lemma descentAlgEquiv_involutive :
    Function.Involutive (descentAlgEquiv R N u t n) := by
  intro z
  have h := (descentAlgEquiv R N u t n).symm_apply_apply z
  rwa [descentAlgEquiv_symm] at h

/-- The fixed algebra for the conjugation--inversion descent datum. -/
noncomputable def fixedSubalgebra :
    Subalgebra R (CoverCoordinateAlgebra R N u t n) :=
  AlgHom.equalizer (descentAlgEquiv R N u t n).toAlgHom
    (AlgHom.id R (CoverCoordinateAlgebra R N u t n))

@[simp]
lemma mem_fixedSubalgebra (z : CoverCoordinateAlgebra R N u t n) :
    z ∈ fixedSubalgebra R N u t n ↔ descentAlgEquiv R N u t n z = z :=
  Iff.rfl

/-- The coordinate ring of the quadratic twist, realized as fixed points on the cover. -/
noncomputable abbrev CoordinateAlgebra := fixedSubalgebra R N u t n

end TateKummer.QuadraticTwist
