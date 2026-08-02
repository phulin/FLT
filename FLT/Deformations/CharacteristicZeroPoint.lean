/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import FLT.Deformations.IsProartinian

import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Characteristic-zero components of flat local algebras

This file isolates the commutative-algebra step used to extract a characteristic-zero point
from a finite flat deformation ring.  Flatness of a local algebra is faithful, so the structure
map is injective.  Consequently a nonzero element of the coefficient domain is not nilpotent in
the deformation ring, and some minimal prime avoids it.
-/

@[expose] public section

namespace Deformation

/-- A finite free local algebra with the module topology over a compact Hausdorff totally
disconnected Noetherian ring is pro-Artinian. -/
theorem isProartinian_of_finiteFree_moduleTopology
    (A B : Type*) [CommRing A] [Nontrivial A] [IsNoetherianRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [CompactSpace A] [T2Space A]
    [TotallyDisconnectedSpace A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B] : IsProartinian B := by
  letI : CompactSpace B := Module.Finite.compactSpace A B
  letI : T2Space B := IsModuleTopology.t2Space A
  let e : B ≃ₗ[A] (Fin (Module.finrank A B) → A) := Module.Finite.equivPi A B
  let eTop : B ≃L[A] (Fin (Module.finrank A B) → A) :=
    IsModuleTopology.continuousLinearEquiv e
  letI : TotallyDisconnectedSpace B :=
    eTop.toHomeomorph.symm.totallyDisconnectedSpace
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  letI : IsLocalRing.IsAdicTopology B := inferInstance
  infer_instance

/-- Let `B` be a flat local algebra over a local domain `A`.  Every nonzero `a : A` is avoided
by a minimal prime of `B`.  Applied to a uniformizer of a coefficient DVR, this is the
commutative-algebra step in Khare--Wintenberger's deduction of their minimal-lift theorem
(Theorem 3.3) from finite flatness of the universal deformation ring (Theorem 3.7). -/
theorem exists_minimalPrime_avoiding_algebraMap
    (A B : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Flat A B] [IsLocalHom (algebraMap A B)]
    (a : A) (ha : a ≠ 0) :
    ∃ P ∈ minimalPrimes B, algebraMap A B a ∉ P := by
  letI : Module.FaithfullyFlat A B :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap A B) :=
    FaithfulSMul.algebraMap_injective A B
  have hdisj : Disjoint ((⊥ : Ideal B) : Set B)
      (Submonoid.powers (algebraMap A B a)) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    change x ∈ (⊥ : Ideal B) at hx
    rw [Ideal.mem_bot] at hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hxp
    have hpow := hinj.ne (pow_ne_zero n ha)
    rw [map_zero] at hpow
    exact hpow (by simpa only [map_pow] using hx)
  obtain ⟨P, hPprime, -, hPdisj⟩ :=
    Ideal.exists_le_prime_disjoint (I := (⊥ : Ideal B))
      (Submonoid.powers (algebraMap A B a)) hdisj
  letI : P.IsPrime := hPprime
  obtain ⟨Q, hQmin, hQP⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := P) bot_le
  refine ⟨Q, hQmin, ?_⟩
  intro haQ
  exact Set.disjoint_left.mp hPdisj (hQP haQ)
    (Submonoid.mem_powers (algebraMap A B a))

/-- A flat local algebra over a discrete valuation ring has a minimal-prime quotient on
which the coefficient map is injective. -/
theorem exists_characteristicZero_minimalPrime_of_dvr
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Flat A B] [IsLocalHom (algebraMap A B)] :
    ∃ P ∈ minimalPrimes B,
      Function.Injective ((Ideal.Quotient.mk P).comp (algebraMap A B)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨P, hPmin, hϖP⟩ :=
    exists_minimalPrime_avoiding_algebraMap A B ϖ hϖ.ne_zero
  have hPprime : P.IsPrime := hPmin.1.1
  letI : P.IsPrime := hPprime
  have hcomap : P.comap (algebraMap A B) = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
    have hpow : ϖ ^ n ∈ P.comap (algebraMap A B) := by
      rw [hn]
      exact Ideal.subset_span (Set.mem_singleton _)
    change algebraMap A B (ϖ ^ n) ∈ P at hpow
    rw [map_pow] at hpow
    exact hϖP (hPprime.mem_of_pow_mem n hpow)
  refine ⟨P, hPmin, ?_⟩
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot,
    ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk P),
    Ideal.mk_ker, hcomap]

/-- The characteristic-zero minimal-prime quotient of a finite flat local algebra over a DVR
is finite free over the DVR. -/
theorem exists_finiteFree_characteristicZero_minimalPrime_of_dvr
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Finite A B] [Module.Flat A B] [IsLocalHom (algebraMap A B)] :
    ∃ P ∈ minimalPrimes B,
      Function.Injective ((Ideal.Quotient.mk P).comp (algebraMap A B)) ∧
      Module.Finite A (B ⧸ P) ∧ Module.Free A (B ⧸ P) := by
  obtain ⟨P, hPmin, hinj⟩ := exists_characteristicZero_minimalPrime_of_dvr A B
  letI : P.IsPrime := hPmin.1.1
  have hfinite : Module.Finite A (B ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A P).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite A (B ⧸ P) := hfinite
  letI : Module.IsTorsionFree A (B ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hfree : Module.Free A (B ⧸ P) :=
    Module.free_of_finite_type_torsion_free'
  exact ⟨P, hPmin, hinj, hfinite, hfree⟩

/-- A flat local `ℤ_[p]`-algebra has a minimal-prime quotient of characteristic zero.  The
quotient map is not included in the conclusion as an extra datum: it is canonically
`Ideal.Quotient.mk P`, and the stated composite is its coefficient map. -/
theorem exists_characteristicZero_minimalPrime
    (p : ℕ) [Fact p.Prime]
    (B : Type*) [CommRing B] [IsLocalRing B] [Algebra ℤ_[p] B]
    [Module.Flat ℤ_[p] B] [IsLocalHom (algebraMap ℤ_[p] B)] :
    ∃ P ∈ minimalPrimes B,
      Function.Injective ((Ideal.Quotient.mk P).comp (algebraMap ℤ_[p] B)) :=
  exists_characteristicZero_minimalPrime_of_dvr ℤ_[p] B

end Deformation
