/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Deformations.Representable
public import FLT.Deformations.RepresentationTheory.Irreducible
public import FLT.GaloisRepresentation.HardlyRamified.Defs

/-!
# The minimal hardly ramified deformation problem

This file replaces the formerly opaque minimal-lift existential by a named deformation
problem and its universal object.  A lift belongs to the problem precisely when it reduces
to the fixed residual representation and is hardly ramified.  Thus its determinant,
ramification away from `2p`, finite-flat condition at `p`, and tame quadratic quotient at `2`
are all part of the represented functor.

Representability is classical Schlessinger--Mazur deformation theory, together with the
pre-1990 representability of the finite-flat local condition.  The later assertion that this
particular universal ring is finite flat over its coefficient DVR is the genuinely modern
Taylor--Wiles/Khare--Wintenberger step and is deliberately not asserted here.
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- The subfunctor of framed representations of `G_ℚ` that are hardly ramified.  The
`ℤ_[p]`-algebra structure on an object is the composite through the coefficient ring `𝓞`.
-/
noncomputable def hardlyRamifiedFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞] :
    Subfunctor (repnFunctor (Fin 2) (Γ ℚ) 𝓞) where
  obj A := {τ | let _ : Algebra ℤ_[p] A :=
      Algebra.compHom A (algebraMap ℤ_[p] 𝓞)
    GaloisRepresentation.IsHardlyRamified hpodd (by simp) (toFramedGaloisRep τ)}
  map {A B} f τ hτ := by
    letI : Algebra ℤ_[p] A := Algebra.compHom A (algebraMap ℤ_[p] 𝓞)
    letI : Algebra ℤ_[p] B := Algebra.compHom B (algebraMap ℤ_[p] 𝓞)
    change GaloisRepresentation.IsHardlyRamified hpodd (by simp)
      (toFramedGaloisRep τ) at hτ
    change GaloisRepresentation.IsHardlyRamified hpodd (by simp)
      (toFramedGaloisRep ((repnFunctor (Fin 2) (Γ ℚ) 𝓞).map f τ))
    let htower : let _ : Algebra A B := f.hom.toRingHom.toAlgebra;
        IsScalarTower ℤ_[p] A B := by
      letI : Algebra A B := f.hom.toRingHom.toAlgebra
      exact IsScalarTower.of_algebraMap_eq fun x => by
        exact (f.hom.commutes (algebraMap ℤ_[p] 𝓞 x)).symm
    let hres : let _ : Algebra A B := f.hom.toRingHom.toAlgebra;
        IsResidueAlgebra A B := by
      letI : Algebra A B := f.hom.toRingHom.toAlgebra
      letI : IsScalarTower 𝓞 A B := inferInstance
      exact IsResidueAlgebra.of_restrictScalars (𝓞 := 𝓞) (A := A) (B := B)
    rw [toFramedGaloisRep_map]
    exact GaloisRepresentation.IsHardlyRamified.framedBaseChange hpodd
      f.hom.toRingHom f.hom.cont htower hres (toFramedGaloisRep τ) hτ

/-- The minimal hardly ramified lift functor: a representation must both reduce to `ρ` and
satisfy all four hardly ramified local/global conditions. -/
noncomputable def hardlyRamifiedLiftFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
    (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField) :
    Subfunctor (repnFunctor (Fin 2) (Γ ℚ) 𝓞) :=
  liftFunctor (Fin 2) (Γ ℚ) 𝓞 ρ ⊓ hardlyRamifiedFunctor 𝓞 p hpodd

/-- The unframed minimal hardly ramified deformation functor.  Its points are strict-conjugacy
classes which admit a representative reducing to `ρ` and satisfying the hardly ramified
conditions.  Böckle's presentation theorem and Carayol's trace theorem apply to this quotient
functor, not to the framed lift functor. -/
noncomputable def hardlyRamifiedDeformationFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
    (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField) :
    Subfunctor (repnQuotFunctor (Fin 2) (Γ ℚ) 𝓞) :=
  (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).imageUnder
    (toRepnQuot (Fin 2) (Γ ℚ) 𝓞)

/-- The residual point belongs to the minimal lift functor whenever it is hardly ramified.
The lift condition at the terminal residue-field object is the identity condition. -/
theorem residual_mem_hardlyRamifiedLiftFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
    (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField)
    (hρ : ρ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj .residueField) :
    ρ ∈ (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).obj .residueField := by
  refine ⟨?_, hρ⟩
  change (repnFunctor (Fin 2) (Γ ℚ) 𝓞).map
      (ProartinianCat.isTerminalResidueField.from .residueField) ρ = ρ
  rw [Subsingleton.elim (ProartinianCat.isTerminalResidueField.from .residueField)
    (𝟙 (.residueField : ProartinianCat 𝓞))]
  rfl

/-- Transporting a hardly ramified residual representation along the chosen identification
`ResidueField R ≃ k` gives the residual point of the hardly ramified deformation functor.
-/
theorem residualRepresentation_mem_hardlyRamifiedFunctor
    {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k]
    (R : Type u) [CommRing R] [IsLocalRing R]
    [Algebra ℤ_[p] R] [Algebra R k]
    [IsScalarTower ℤ_[p] R k]
    (e : ResidueField R ≃+* k)
    (he : ∀ r, e (residue R r) = algebraMap R k r)
    (ρ : FramedGaloisRep ℚ k (Fin 2))
    (hρ : GaloisRepresentation.IsHardlyRamified hpodd (by simp) ρ) :
    residualRepresentation R e ρ ∈
      (hardlyRamifiedFunctor R p hpodd).obj .residueField := by
  let κR : ProartinianCat R := .residueField
  let f : k →+* κR :=
    (ProartinianCat.residueFieldRingEquiv R e).symm.toRingHom
  letI : IsLocalHom f := IsLocalHom.of_surjective f
    (ProartinianCat.residueFieldRingEquiv R e).symm.surjective
  letI : Algebra ℤ_[p] κR := Algebra.compHom _ (algebraMap ℤ_[p] R)
  let htower : (let _ : Algebra k κR := f.toAlgebra;
      IsScalarTower ℤ_[p] k κR) := by
    letI : Algebra k κR := f.toAlgebra
    exact IsScalarTower.of_algebraMap_eq fun z => by
      apply (ProartinianCat.residueFieldRingEquiv R e).injective
      change e (residue R (algebraMap ℤ_[p] R z)) = e (f (algebraMap ℤ_[p] k z))
      rw [show f (algebraMap ℤ_[p] k z) = e.symm (algebraMap ℤ_[p] k z) by rfl,
        e.apply_symm_apply, he]
      exact (IsScalarTower.algebraMap_apply ℤ_[p] R k z).symm
  let hres : (let _ : Algebra k κR := f.toAlgebra;
      IsResidueAlgebra k κR) := by
    letI : Algebra k κR := f.toAlgebra
    exact ⟨IsLocalRing.residue_surjective.comp
      (ProartinianCat.residueFieldRingEquiv R e).symm.surjective⟩
  change GaloisRepresentation.IsHardlyRamified hpodd (by simp)
    (toFramedGaloisRep (residualRepresentation R e ρ))
  simpa only [residualRepresentation, toFramedGaloisRep,
    FramedGaloisRep.GL.symm_apply_apply] using
    GaloisRepresentation.IsHardlyRamified.framedBaseChange hpodd
      f continuous_of_discreteTopology htower hres ρ hρ

/-- Irreducibility is preserved when a framed residual representation is transported from
an explicitly chosen residue field `k` to the canonical residue-field object of `R`. -/
theorem residualRepresentation_isIrreducible
    {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    (R : Type u) [CommRing R] [IsLocalRing R]
    (e : ResidueField R ≃+* k)
    (rho : FramedGaloisRep ℚ k (Fin 2)) (hrho : rho.IsIrreducible) :
    (toRepresentation (residualRepresentation R e rho)).IsIrreducible := by
  let kappaR : ProartinianCat R := .residueField
  let rhoRes : FramedGaloisRep ℚ kappaR (Fin 2) :=
    toFramedGaloisRep (residualRepresentation R e rho)
  let ek : kappaR ≃+* k := ProartinianCat.residueFieldRingEquiv R e
  letI : Algebra kappaR k := ek.toRingHom.toAlgebra
  letI : ContinuousSMul kappaR k :=
    continuousSMul_of_algebraMap kappaR k continuous_of_discreteTopology
  have hback :
      rhoRes.baseChange ek.toRingHom continuous_of_discreteTopology = rho :=
    toFramedGaloisRep_residualRepresentation_baseChange R e rho
  have hbackIrred :
      (rhoRes.baseChange ek.toRingHom continuous_of_discreteTopology).IsIrreducible := by
    rw [hback]
    exact hrho
  rw [FramedGaloisRep.baseChange_def] at hbackIrred
  have hbaseChangeIrred :
      (GaloisRep.baseChange k
        (rhoRes : GaloisRep ℚ kappaR (Fin 2 → kappaR))).IsIrreducible :=
    (GaloisRep.isIrreducible_conj_iff _ _).mpr hbackIrred
  exact Slop.OddRep.isIrreducible_of_baseChange _ k hbaseChangeIrred

/-- Schlessinger--Mazur corepresentability of the minimal hardly ramified deformation
problem.  This is a pre-1990 input: Mazur's deformation theory and the classical
finite-flat local deformation condition. -/
lemma isCorepresentable_hardlyRamifiedDeformationFunctor
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
    [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
    (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField)
    [(toRepresentation ρ).IsAbsolutelyIrreducible]
    (_hρ : ρ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj .residueField) :
    (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.IsCorepresentable := by
  -- Schlessinger's criterion plus Mazur's 1989 profinite deformation framework; the
  -- finite-flat local condition is represented by the pre-1990 Fontaine--Laffaille theory.
  knownin1980s

noncomputable section Universal

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]
variable (p : ℕ) [Fact p.Prime] (hpodd : Odd p) [Algebra ℤ_[p] 𝓞]
variable (ρ : (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj .residueField)
variable [(toRepresentation ρ).IsAbsolutelyIrreducible]
variable (hρ : ρ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj .residueField)

/-- The universal minimal hardly ramified deformation ring. -/
def hardlyRamifiedUniversalRing : ProartinianCat 𝓞 :=
  (isCorepresentable_hardlyRamifiedDeformationFunctor
    𝓞 p hpodd ρ hρ).has_corepresentation.choose

/-- The corepresentation of the minimal hardly ramified deformation functor. -/
def hardlyRamifiedUniversalRingCorepresentableBy :
    (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.CorepresentableBy
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  (isCorepresentable_hardlyRamifiedDeformationFunctor
    𝓞 p hpodd ρ hρ).has_corepresentation.choose_spec.some

/-- The universal strict-equivalence class in the minimal hardly ramified deformation functor. -/
def hardlyRamifiedUniversalElement :
    (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.obj
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  (hardlyRamifiedUniversalRingCorepresentableBy 𝓞 p hpodd ρ hρ).homEquiv
    (𝟙 (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ))

/-- The unique classifying morphism attached to a hardly ramified deformation class over a
pro-Artinian coefficient algebra. -/
def hardlyRamifiedClassifyingMap {A : ProartinianCat 𝓞}
    (x : (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.obj A) :
    hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ ⟶ A :=
  (hardlyRamifiedUniversalRingCorepresentableBy 𝓞 p hpodd ρ hρ).homEquiv.symm x

/-- Mapping the universal deformation class along its classifying morphism recovers the
prescribed class. -/
theorem hardlyRamifiedUniversalElement_map_classifyingMap {A : ProartinianCat 𝓞}
    (x : (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.obj A) :
    (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.map
        (hardlyRamifiedClassifyingMap 𝓞 p hpodd ρ hρ x)
        (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ) = x := by
  unfold hardlyRamifiedClassifyingMap hardlyRamifiedUniversalElement
  rw [← (hardlyRamifiedUniversalRingCorepresentableBy
    𝓞 p hpodd ρ hρ).homEquiv_eq]
  exact (hardlyRamifiedUniversalRingCorepresentableBy
    𝓞 p hpodd ρ hρ).homEquiv.apply_symm_apply x

/-- The classifying morphism is the only morphism carrying the universal deformation class to
the prescribed class. -/
theorem hardlyRamifiedClassifyingMap_unique {A : ProartinianCat 𝓞}
    (x : (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.obj A)
    (f : hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ ⟶ A)
    (hf : (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.map f
      (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ) = x) :
    f = hardlyRamifiedClassifyingMap 𝓞 p hpodd ρ hρ x := by
  apply (hardlyRamifiedUniversalRingCorepresentableBy
    𝓞 p hpodd ρ hρ).homEquiv.injective
  calc
    (hardlyRamifiedUniversalRingCorepresentableBy
        𝓞 p hpodd ρ hρ).homEquiv f =
        (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.map f
          (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ) := by
            rw [(hardlyRamifiedUniversalRingCorepresentableBy
              𝓞 p hpodd ρ hρ).homEquiv_eq]
            rfl
    _ = x := hf
    _ = (hardlyRamifiedUniversalRingCorepresentableBy
        𝓞 p hpodd ρ hρ).homEquiv
          (hardlyRamifiedClassifyingMap 𝓞 p hpodd ρ hρ x) :=
      ((hardlyRamifiedUniversalRingCorepresentableBy
        𝓞 p hpodd ρ hρ).homEquiv.apply_symm_apply x).symm

/-- Rigidity of the universal object: an endomorphism that fixes the universal deformation
class is the identity.  This is the Yoneda step used after descending the universal
representation to its closed trace algebra. -/
theorem hardlyRamifiedUniversalEndomorphism_eq_id
    (f : hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ ⟶
      hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ)
    (hf : (hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.map f
      (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ) =
        hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ) :
    f = 𝟙 (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) := by
  apply (hardlyRamifiedClassifyingMap_unique 𝓞 p hpodd ρ hρ
    (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ) f hf).trans
  symm
  apply hardlyRamifiedClassifyingMap_unique
  exact ConcreteCategory.congr_hom
    ((hardlyRamifiedDeformationFunctor 𝓞 p hpodd ρ).toFunctor.map_id
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ))
    (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ)

/-- A matrix-valued representative of the universal unframed minimal deformation.  Membership
in `hardlyRamifiedDeformationFunctor` supplies a representative which already satisfies both
the residual and hardly ramified conditions. -/
noncomputable def hardlyRamifiedUniversalRepresentation :
    (repnFunctor (Fin 2) (Γ ℚ) 𝓞).obj
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  Classical.choose (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ).2

/-- The universal minimal representation as a framed Galois representation. -/
noncomputable def hardlyRamifiedUniversalGaloisRep :
    FramedGaloisRep ℚ (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) (Fin 2) :=
  toFramedGaloisRep (hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ)

theorem hardlyRamifiedUniversalRepresentation_mem :
    hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ ∈
      (hardlyRamifiedLiftFunctor 𝓞 p hpodd ρ).obj
        (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ) :=
  (Classical.choose_spec
    (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ).2).1

/-- The chosen representative maps to the universal strict-equivalence class. -/
theorem hardlyRamifiedUniversalRepresentation_toRepnQuot :
    (toRepnQuot (Fin 2) (Γ ℚ) 𝓞).app
      (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ)
      (hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ) =
        (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ).1 :=
  (Classical.choose_spec
    (hardlyRamifiedUniversalElement 𝓞 p hpodd ρ hρ).2).2

/-- The universal element both reduces to `ρ` and is hardly ramified. -/
theorem hardlyRamifiedUniversalRepresentation_conditions :
    let τ := hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ
    let D := hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ
    τ ∈ (liftFunctor (Fin 2) (Γ ℚ) 𝓞 ρ).obj D ∧
      τ ∈ (hardlyRamifiedFunctor 𝓞 p hpodd).obj D := by
  simpa only [hardlyRamifiedLiftFunctor, CategoryTheory.Subfunctor.min_obj,
    Set.mem_inter_iff] using
      hardlyRamifiedUniversalRepresentation_mem 𝓞 p hpodd ρ hρ

/-- Reduction of the universal representation along its canonical residue map is exactly
the fixed residual representation. -/
theorem hardlyRamifiedUniversalRepresentation_reduces :
    (repnFunctor (Fin 2) (Γ ℚ) 𝓞).map
      (ProartinianCat.toResidueField
        (hardlyRamifiedUniversalRing 𝓞 p hpodd ρ hρ))
      (hardlyRamifiedUniversalRepresentation 𝓞 p hpodd ρ hρ) = ρ := by
  exact (hardlyRamifiedUniversalRepresentation_conditions 𝓞 p hpodd ρ hρ).1

end Universal

end Deformation
