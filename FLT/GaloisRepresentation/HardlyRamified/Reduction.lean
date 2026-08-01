/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Lift
public import FLT.GaloisRepresentation.HardlyRamified.Family
public import FLT.GaloisRepresentation.HardlyRamified.Threeadic

/-!
# Reduction of hardly ramified representations

This file assembles lifting, compatible families, and the 3-adic classification to identify the
Frobenius traces of an irreducible hardly ramified residual representation.  The last remaining
step is the Chebotarev--Brauer--Nesbitt argument turning those trace identities into reducibility.
-/

@[expose] public section

open GaloisRepresentation IsDedekindDomain NumberField
open scoped TensorProduct

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

namespace GaloisRepresentation.IsHardlyRamified

universe u v

/-- If a hardly ramified residual representation were irreducible, lifting it and moving it to
the 3-adic member of a compatible family would force its Frobenius trace to be `1 + q` away from
a finite exceptional set and the residue characteristics. -/
@[nolint unusedArguments]
theorem frobenius_trace_of_isIrreducible
    {p : ℕ} (hpodd : Odd p) [hp : Fact p.Prime]
    {k : Type u} [Finite k] [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[p] k] [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hρ : IsHardlyRamified hpodd hV ρ) (hρirred : ρ.IsIrreducible) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)),
      ∀ (q : ℕ) (hq : q.Prime) (_hq5 : 5 ≤ q),
        let w := hq.toHeightOneSpectrumRingOfIntegersRat
        w ∉ S → (p : 𝓞 ℚ) ∉ w.asIdeal → (3 : 𝓞 ℚ) ∉ w.asIdeal →
          LinearMap.trace k V (ρ.toLocal w (Frob w)) = 1 + (q : k) := by
  obtain ⟨R, _, _, _, _, _, _, _, _, _, _, _, _, _,
      W, _, _, _, _, hW, σ, r, hσ, hσred⟩ := lifts hpodd V hV ρ hρirred hρ
  obtain ⟨E, _, _, fam, hfam, hmembers, _, _, _, ψ, rψ, hψ⟩ :=
    mem_isCompatible hpodd hW hσ
  let h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  let φ3 : E →+* AlgebraicClosure ℚ_[3] :=
    (IsAlgClosed.lift (R := ℚ) (S := E) (M := AlgebraicClosure ℚ_[3])).toRingHom
  obtain ⟨A3, _, _, _, _, _, _, _, _, _, _, _, _, _,
      W3, _, _, _, _, hW3, σ3, r3, hσ3, hσ3fam⟩ :=
    hmembers h3 (show Odd 3 by decide) φ3
  obtain ⟨S, hS⟩ := hfam.common_trace
  refine ⟨S, ?_⟩
  intro q hq hq5
  dsimp only
  intro hwS hpw h3w
  let w := hq.toHeightOneSpectrumRingOfIntegersRat
  obtain ⟨a, _, htrace3a, _, htracepa⟩ := hS h3 hp φ3 ψ w hwS h3w hpw
  have htrace3 : LinearMap.trace (AlgebraicClosure ℚ_[3]) (Fin 2 → AlgebraicClosure ℚ_[3])
      ((fam h3 φ3).toLocal w (Frob w)) = 1 + q := by
    have heval := congrArg (fun τ : GaloisRep ℚ (AlgebraicClosure ℚ_[3])
        (Fin 2 → AlgebraicClosure ℚ_[3]) => τ.toLocal w (Frob w)) hσ3fam
    simp only [GaloisRep.toLocal] at heval ⊢
    rw [← heval, GaloisRep.map_conj, GaloisRep.trace_conj,
      GaloisRep.baseChange_map, GaloisRep.trace_baseChange,
      three_adic W3 hW3 hσ3 q hq hq5]
    simp
  have ha : a = (1 + q : E) := by
    apply φ3.injective
    rw [← htrace3a, htrace3]
    simp
  have htracep : LinearMap.trace (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p]) ((fam hp ψ).toLocal w (Frob w)) = 1 + q := by
    rw [htracepa, ha]
    simp
  have htraceσAC : algebraMap R (AlgebraicClosure ℚ_[p])
      (LinearMap.trace R W (σ.toLocal w (Frob w))) = 1 + q := by
    have heval := congrArg (fun τ : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
        (Fin 2 → AlgebraicClosure ℚ_[p]) => τ.toLocal w (Frob w)) hψ
    simp only [GaloisRep.toLocal] at heval ⊢
    rw [← htracep, ← heval, GaloisRep.map_conj, GaloisRep.trace_conj,
      GaloisRep.baseChange_map, GaloisRep.trace_baseChange]
  have htraceσ : LinearMap.trace R W (σ.toLocal w (Frob w)) = 1 + q := by
    apply FaithfulSMul.algebraMap_injective R (AlgebraicClosure ℚ_[p])
    rw [htraceσAC]
    simp
  have hevalred := congrArg (fun τ : GaloisRep ℚ k V => τ.toLocal w (Frob w)) hσred
  simp only [GaloisRep.toLocal] at hevalred ⊢
  rw [← hevalred, GaloisRep.map_conj, GaloisRep.trace_conj,
    GaloisRep.baseChange_map, GaloisRep.trace_baseChange, htraceσ]
  simp

/-- The Chebotarev--Brauer--Nesbitt step: a hardly ramified residual representation whose
Frobenius traces agree almost everywhere with `1 ⊕ cyclotomic` is reducible. -/
theorem not_isIrreducible_of_frobenius_trace
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type u} [Finite k] [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[p] k] [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hρ : IsHardlyRamified hpodd hV ρ)
    (htrace : ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)),
      ∀ (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q),
        let w := hq.toHeightOneSpectrumRingOfIntegersRat
        w ∉ S → (p : 𝓞 ℚ) ∉ w.asIdeal → (3 : 𝓞 ℚ) ∉ w.asIdeal →
          LinearMap.trace k V (ρ.toLocal w (Frob w)) = 1 + (q : k)) :
    ¬ ρ.IsIrreducible := by
  sorry

/-- Every hardly ramified residual representation is reducible, assuming the lifting,
compatible-family, 3-adic, and Chebotarev--Brauer--Nesbitt inputs assembled above. -/
theorem not_isIrreducible
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type u} [Finite k] [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[p] k] [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ¬ ρ.IsIrreducible := by
  intro hρirred
  exact (not_isIrreducible_of_frobenius_trace hpodd V hV ρ hρ
    (frobenius_trace_of_isIrreducible hpodd V hV ρ hρ hρirred)) hρirred

end GaloisRepresentation.IsHardlyRamified
