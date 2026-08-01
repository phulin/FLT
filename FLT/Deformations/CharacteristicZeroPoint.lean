/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Characteristic-zero components of flat local algebras

This file isolates the commutative-algebra step used to extract a characteristic-zero point
from a finite flat deformation ring.  Flatness of a local algebra is faithful, so the structure
map is injective.  Consequently a nonzero element of the coefficient domain is not nilpotent in
the deformation ring, and some minimal prime avoids it.
-/

@[expose] public section

namespace Deformation

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

/-- A flat local `ℤ_[p]`-algebra has a minimal-prime quotient of characteristic zero.  The
quotient map is not included in the conclusion as an extra datum: it is canonically
`Ideal.Quotient.mk P`, and the stated composite is its coefficient map. -/
theorem exists_characteristicZero_minimalPrime
    (p : ℕ) [Fact p.Prime]
    (B : Type*) [CommRing B] [IsLocalRing B] [Algebra ℤ_[p] B]
    [Module.Flat ℤ_[p] B] [IsLocalHom (algebraMap ℤ_[p] B)] :
    ∃ P ∈ minimalPrimes B,
      Function.Injective ((Ideal.Quotient.mk P).comp (algebraMap ℤ_[p] B)) := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨P, hPmin, hpP⟩ :=
    exists_minimalPrime_avoiding_algebraMap ℤ_[p] B (p : ℤ_[p]) hp0
  have hPprime : P.IsPrime := hPmin.1.1
  letI : P.IsPrime := hPprime
  have hcomap : P.comap (algebraMap ℤ_[p] B) = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hne
    have hpow : (p : ℤ_[p]) ^ n ∈ P.comap (algebraMap ℤ_[p] B) := by
      rw [hn]
      exact Ideal.subset_span (Set.mem_singleton _)
    change algebraMap ℤ_[p] B ((p : ℤ_[p]) ^ n) ∈ P at hpow
    rw [map_pow] at hpow
    exact hpP (hPprime.mem_of_pow_mem n hpow)
  refine ⟨P, hPmin, ?_⟩
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot,
    ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk P),
    Ideal.mk_ker, hcomap]

end Deformation
