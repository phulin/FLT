/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Assumptions.KnownIn1980s
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Systems of parameters in power-series rings over a DVR

This file isolates the classical Cohen--Macaulay input in Böckle's balanced-presentation
argument.  It belongs behind the project's `knownin1980s` boundary because the complete proof
requires a general development of Cohen--Macaulay local rings which is not yet present in
Mathlib.
-/

@[expose] public section

open IsLocalRing

universe u

/-- A system of parameters in a finite-variable power-series ring over a DVR is a regular
sequence.

Here the hypotheses say exactly that `rs` has the dimension of
`R⟦X₁, ..., Xₙ⟧` and generates an ideal primary to the maximal ideal.  A pre-1990 proof is:

1. a DVR is a one-dimensional regular local ring;
2. adjoining a formal power-series variable preserves regular locality and raises dimension
   by one;
3. every regular local ring is Cohen--Macaulay;
4. every system of parameters in a Cohen--Macaulay local ring is a regular sequence.

These are standard results in Matsumura, *Commutative Algebra*, second edition (1980),
Chapter 6, especially the sections on regular local and Cohen--Macaulay rings.  A modern
step-by-step account is Stacks Project, tags `00NQ` (regular local rings are Cohen--Macaulay)
and `00N6` (systems of parameters in Cohen--Macaulay modules are regular). -/
theorem MvPowerSeries.isWeaklyRegular_of_length_eq_dimension_of_radical_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (n : ℕ) (rs : List (MvPowerSeries (Fin n) R))
    (hlen : rs.length = n + 1)
    (hrad : (Ideal.ofList rs).radical =
      maximalIdeal (MvPowerSeries (Fin n) R)) :
    RingTheory.Sequence.IsWeaklyRegular (MvPowerSeries (Fin n) R) rs := by
  knownin1980s

