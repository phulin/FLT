/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Finiteness criteria for local rings

This file contains the final commutative-algebra step of the finite-image
criterion used for universal deformation rings.
-/

@[expose] public section

/-- A Noetherian local ring with finite residue field is finite if all of its prime
quotients are finite.  Indeed every prime is then maximal, so the ring is zero-dimensional
and Artinian; finiteness follows from the finite residue field. -/
theorem IsLocalRing.finite_of_finite_prime_quotients
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Finite (IsLocalRing.ResidueField A)]
    (h : ∀ P : Ideal A, [P.IsPrime] → Finite (A ⧸ P)) : Finite A := by
  have hdim : Ring.KrullDimLE 0 A :=
    (Ring.krullDimLE_zero_iff).mpr fun P hP => by
      letI : P.IsPrime := hP
      letI : Finite (A ⧸ P) := h P
      have hfield : IsField (A ⧸ P) := Finite.isField_of_domain (A ⧸ P)
      exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mpr hfield
  letI : IsArtinianRing A :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  obtain ⟨n, hn⟩ :=
    IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient (⊥ : Ideal A)
  have : Finite (A ⧸ (⊥ : Ideal A)) :=
    (IsLocalRing.finite_quotient_iff (R := A)).mpr ⟨n, hn⟩
  exact Finite.of_equiv (A ⧸ (⊥ : Ideal A)) (RingEquiv.quotientBot A)

