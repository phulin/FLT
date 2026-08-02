/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.FreyCurve.Basic
public import FLT.KnownIn1980s.EllipticCurves.WeilPairing
import FLT.FreyCurve.Flat
import FLT.FreyCurve.Unramified
import FLT.GaloisRepresentation.HardlyRamified.Reduction
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Frey curve gives a hardly ramified representation

We prove that the `ℓ`-torsion of the Frey curve attached to a Frey package
is a hardly ramified Galois representation, and that this representation is
irreducible.
-/

@[expose] public section

variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

/-- The determinant of the Galois action on the `p`-torsion of the Frey curve is the
mod-`p` cyclotomic character.  This is the determinant branch of the hardly-ramified
criterion, separated from the three reduction-theoretic branches. -/
theorem FreyCurve.torsion_det (g : Field.absoluteGaloisGroup ℚ) :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)).det g =
      algebraMap ℤ_[P.p] (ZMod P.p)
        (cyclotomicCharacter (AlgebraicClosure ℚ) P.p g.toRingEquiv) := by
  letI : Fact (P.p.Prime) := ⟨P.pp⟩
  rw [show algebraMap ℤ_[P.p] (ZMod P.p) = PadicInt.toZMod from rfl]
  exact (P.freyCurve.weilPairingData P.p).galoisRep_det_eq_cyclotomic g

/-- Assemble the Frey hardly-ramified representation once its two genuinely local inputs have
been supplied: finite flatness at the exponent and the tame quadratic quotient at `2`.
The determinant and all odd-prime unramifiedness fields are discharged by the global theorems
proved above. -/
theorem FreyCurve.torsion_isHardlyRamified_of_local_conditions :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
        P.pp.toHeightOneSpectrumRingOfIntegersRat →
      GaloisRep.HasTameQuadraticQuotientAtTwo
        (P.freyCurve.galoisRep P.p P.hppos) →
      IsHardlyRamified P.hp_odd (by
        apply WeierstrassCurve.n_torsion_rank
        · exact P.pp
        · exact_mod_cast P.pp.ne_zero)
        (P.freyCurve.galoisRep P.p P.hppos) := by
  letI : Fact (P.p.Prime) := ⟨P.pp⟩
  intro hflat htame
  refine {
    det := FreyCurve.torsion_det P
    isUnramified := ?_
    isFlat := hflat
    isTameAtTwo := htame }
  intro q hq hqne
  have hqge := hq.two_le
  exact FreyCurve.torsion_isUnramifiedAt_of_odd_ne_exponent
    P hq (by omega) hqne.2

/-- In the good-reduction case at the Frey exponent, only the local quotient at `2` remains
to obtain the full hardly-ramified conclusion. -/
theorem FreyCurve.torsion_isHardlyRamified_of_not_dvd_abc
    (hgood : ¬(P.p : ℤ) ∣ P.a * P.b * P.c) :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    GaloisRep.HasTameQuadraticQuotientAtTwo
        (P.freyCurve.galoisRep P.p P.hppos) →
      IsHardlyRamified P.hp_odd (by
        apply WeierstrassCurve.n_torsion_rank
        · exact P.pp
        · exact_mod_cast P.pp.ne_zero)
        (P.freyCurve.galoisRep P.p P.hppos) := by
  letI : Fact (P.p.Prime) := ⟨P.pp⟩
  intro htame
  exact FreyCurve.torsion_isHardlyRamified_of_local_conditions P
    (FreyCurve.torsion_isFlatAt_of_not_dvd_abc P hgood) htame

theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd (by
      apply WeierstrassCurve.n_torsion_rank
      · exact P.pp
      · exact_mod_cast P.pp.ne_zero)
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

theorem FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  by
    let _ : Fact (P.p.Prime) := ⟨P.pp⟩
    exact (FreyCurve.torsion_isHardlyRamified P).not_isIrreducible
