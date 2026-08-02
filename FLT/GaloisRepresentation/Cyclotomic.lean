/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import FLT.Data.QHat
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The cyclotomic character

The cyclotomic character of the absolute Galois group of `ℚ`, with values
in the units of `ZHat`, together with the auxiliary lemmas needed to
construct it.
-/

@[expose] public section

variable (K : Type) [Field K]
variable (L : Type) [Field L] [Algebra K L] [CharZero L] [IsAlgClosed L]
  -- not even sure if i need it to be the alg closure at this point

lemma IsAlgClosed.card_rootsOfUnity (N : ℕ) [NeZero N] : Nat.card (rootsOfUnity N L) = N := by
  obtain ⟨z, hz⟩ : ∃ z : L, IsPrimitiveRoot z N :=
    IsCyclotomicExtension.exists_isPrimitiveRoot L _ (show _ ∈ ⊤ by simp) (NeZero.ne N)
  exact IsPrimitiveRoot.card_rootsOfUnity hz

@[norm_cast]
lemma PNat.coe_dvd_iff (A B : ℕ+) : (A : ℕ) ∣ B ↔ A ∣ B := by exact Iff.symm dvd_iff

lemma rootsOfUnity.pow_eq_pow {a b c : ℕ} {G : Type} [Group G] {t : G} (h : t ^ a = 1)
    (h2 : b ≡ c [MOD a]) : t ^ b = t ^ c := by
  rw [pow_eq_pow_mod b h, pow_eq_pow_mod c h]
  exact congr_arg _ h2

lemma PNat.castHom_val_modEq {D : ℕ} {N : ℕ+} (h : D ∣ N) (e : ZMod N) :
    (ZMod.castHom h _ e : ZMod D).val ≡ e.val [MOD D] := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  exact Nat.mod_modEq e.val D

/-! ### Reduction of the `p`-adic character on `p`-th roots of unity -/

/-- Reduction modulo `p` agrees with reduction modulo `p ^ 1`, after transporting
along the canonical equality `p ^ 1 = p`. -/
theorem PadicInt.ringEquivCongr_toZModPow_one {p : ℕ} [Fact p.Prime] :
    (ZMod.ringEquivCongr (pow_one p)).toRingHom.comp (PadicInt.toZModPow 1) =
      PadicInt.toZMod := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [RingHom.ker_comp_of_injective _ (ZMod.ringEquivCongr (pow_one p)).injective,
    PadicInt.ker_toZModPow, pow_one, PadicInt.ker_toZMod,
    ← PadicInt.maximalIdeal_eq_span_p]

/-- On `p`-th roots of unity, a field automorphism acts by the reduction modulo `p`
of its `p`-adic cyclotomic character. -/
theorem cyclotomicCharacter.toZMod_spec
    {L₀ : Type*} [Field L₀] {p : ℕ} [Fact p.Prime]
    [∀ i, HasEnoughRootsOfUnity L₀ (p ^ i)]
    (g : L₀ ≃+* L₀) (t : rootsOfUnity p L₀) :
    g (((t : L₀ˣ) : L₀)) = ((t : L₀ˣ) : L₀) ^
      (PadicInt.toZMod ((cyclotomicCharacter L₀ p g).val)).val := by
  have hmaps := PadicInt.ringEquivCongr_toZModPow_one (p := p)
  have happ := DFunLike.congr_fun hmaps ((cyclotomicCharacter L₀ p g).val)
  change (ZMod.ringEquivCongr (pow_one p))
      (PadicInt.toZModPow 1 ((cyclotomicCharacter L₀ p g).val)) = _ at happ
  have hval :
      (PadicInt.toZModPow 1 ((cyclotomicCharacter L₀ p g).val)).val =
        (PadicInt.toZMod ((cyclotomicCharacter L₀ p g).val)).val := by
    rw [← ZMod.ringEquivCongr_val (pow_one p), happ]
  have ht : ((t : L₀ˣ) : L₀) ^ p ^ 1 = 1 := by
    have htunit : (t : L₀ˣ) ^ p = 1 := by
      simpa only [mem_rootsOfUnity] using t.prop
    simpa only [pow_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg Units.val htunit
  rw [cyclotomicCharacter.spec p g (((t : L₀ˣ) : L₀)) ht, hval]

/-- In any additive coordinates on the group of `p`-th roots of unity, the Galois
action is scalar multiplication by the mod-`p` cyclotomic character. -/
theorem rootsOfUnity.addEquiv_restrictRootsOfUnity_cyclotomic
    {L₀ : Type*} [Field L₀] {p : ℕ} [Fact p.Prime]
    [∀ i, HasEnoughRootsOfUnity L₀ (p ^ i)]
    (e : Additive (rootsOfUnity p L₀) ≃+ ZMod p)
    (g : L₀ ≃+* L₀) (z : Additive (rootsOfUnity p L₀)) :
    e (Additive.ofMul (g.toMulEquiv.restrictRootsOfUnity p (Additive.toMul z))) =
      PadicInt.toZMod ((cyclotomicCharacter L₀ p g).val) * e z := by
  let c : ZMod p := PadicInt.toZMod ((cyclotomicCharacter L₀ p g).val)
  have hrestrict :
      g.toMulEquiv.restrictRootsOfUnity p (Additive.toMul z) =
        (Additive.toMul z) ^ c.val := by
    apply Subtype.ext
    apply Units.ext
    exact show
      g ((((Additive.toMul z) : rootsOfUnity p L₀) : L₀ˣ) : L₀) =
        ((((Additive.toMul z) : rootsOfUnity p L₀) : L₀ˣ) : L₀) ^ c.val from by
          dsimp only [c]
          exact cyclotomicCharacter.toZMod_spec g (Additive.toMul z)
  rw [hrestrict]
  change e (c.val • z) = c * e z
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- The cyclotomic character -/
noncomputable def CyclotomicCharacterAux : (L ≃+* L) →* ZHat where
  toFun g := ⟨fun N ↦ modularCyclotomicCharacter L (IsAlgClosed.card_rootsOfUnity L N) g, by
    intros D M h
    apply modularCyclotomicCharacter.unique
    intros t htD
--    norm_cast at h
    rw [modularCyclotomicCharacter.spec L (IsAlgClosed.card_rootsOfUnity L M) g <|
          rootsOfUnity_le_of_dvd h htD]
    norm_cast
    apply rootsOfUnity.pow_eq_pow htD
    dsimp only
    symm
    apply PNat.castHom_val_modEq⟩
  map_one' := by ext; simp only [map_one]; rfl
  map_mul' _ _ := by ext; simp only [map_mul]; rfl

/-- The Zhat-adic cyclotomic character. -/
noncomputable def CyclotomicCharacterZHat : (L ≃+* L) →* ZHatˣ :=
  (CyclotomicCharacterAux L).toHomUnits
