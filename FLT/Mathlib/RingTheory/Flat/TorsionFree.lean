/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness over a discrete valuation ring

This file records the one-uniformizer criterion used in the Böckle step of the
hardly ramified lifting argument.  Over a DVR every nonzero scalar is a unit
times a power of any irreducible element.  Consequently it is enough to check
that one irreducible element acts regularly on a module.
-/

@[expose] public section

namespace Module

variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M]

/-- A module over a DVR is torsion-free if one irreducible element acts regularly. -/
theorem IsTorsionFree.of_isSMulRegular_irreducible {π : R} (hπ : Irreducible π)
    (hregular : IsSMulRegular M π) : IsTorsionFree R M := by
  constructor
  intro r hr
  obtain ⟨n, u, hru⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr.ne_zero hπ
  rw [hru]
  exact (u.isSMulRegular M).mul (IsSMulRegular.pow n hregular)

/-- A module over a DVR is flat if one irreducible element acts regularly. -/
theorem Flat.of_isSMulRegular_irreducible {π : R} (hπ : Irreducible π)
    (hregular : IsSMulRegular M π) : Flat R M := by
  letI : IsTorsionFree R M :=
    IsTorsionFree.of_isSMulRegular_irreducible hπ hregular
  infer_instance

end Module
