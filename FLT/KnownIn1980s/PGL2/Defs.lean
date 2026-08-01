/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import FLT.KnownIn1980s.PGL2.Base
import FLT.Slop.PGL2.FiniteSubgroups.DicksonClassification

/-!
# Public statements for Dickson's classification in `PGL₂`

This file contains the non-slop API for the PGL2 classification statements.  The
proofs live in `FLT.KnownIn1980s.PGL2.Proofs`, which imports the AI-generated
development in `FLT.Slop.PGL2`.
-/

@[expose] public section

namespace Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]

variable [h_odd : Fact (p > 2)]

theorem classification_tame (G : Subgroup (PGL p)) [Finite G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (hG_nontrivial : Nontrivial G) :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  exact @classification_tame_slop p ‹_› ‹_› G (Fintype.ofFinite G)
    hG_tame hG_nontrivial

theorem classification_wild (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  exact @classification_wild_slop p ‹_› ‹_› G ‹Finite G› hG_p

end Dickson
