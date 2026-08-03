/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Krull dimension of multivariate power-series rings

This file records the lower bound obtained by viewing a finite-variable multivariate
power-series ring as an iterated one-variable power-series ring.
-/

@[expose] public section

/-- Adjoining `n` formal power-series variables raises Krull dimension by at least `n`. -/
lemma ringKrullDim_add_nat_le_ringKrullDim_mvPowerSeries_fin
    (R : Type*) [CommRing R] (n : ℕ) :
    ringKrullDim R + n ≤ ringKrullDim (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
      simpa using
        (ringKrullDim_eq_of_ringEquiv
          (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv).ge
  | succ n ih =>
      calc
        ringKrullDim R + (n + 1) = (ringKrullDim R + n) + 1 := by
          simp [add_assoc]
        _ ≤ ringKrullDim (MvPowerSeries (Fin n) R) + 1 :=
          add_le_add ih le_rfl
        _ ≤ ringKrullDim (PowerSeries (MvPowerSeries (Fin n) R)) :=
          ringKrullDim_succ_le_ringKrullDim_powerseries
        _ = ringKrullDim (MvPowerSeries (Fin (n + 1)) R) :=
          (ringKrullDim_eq_of_ringEquiv
            (MvPowerSeries.finSuccEquiv R n).toRingEquiv).symm
