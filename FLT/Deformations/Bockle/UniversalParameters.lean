/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle.FirstOrder
public import FLT.Deformations.Bockle.RelativeCotangent
public import FLT.Deformations.Carayol

/-!
# Universal maps associated to first-order deformations

The universal unrestricted deformation ring classifies the dual-number deformations built
from adjoint cocycles.  This file records their classifying morphisms and the corresponding
specialization identities.  These maps are the cotangent functionals from which Böckle's
power-series parameters are selected.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Deformation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Finite (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable (K : Type u) [Field K] [NumberField K]
variable (rhoRes : (repnFunctor (Fin 2) (Γ K) R).obj .residueField)
variable [Representation.IsAbsolutelyIrreducible.{u} (toRepresentation rhoRes)]

/-- The morphism from the unrestricted universal deformation ring to the dual numbers
which classifies the first-order deformation attached to an adjoint cocycle. -/
noncomputable def bockleFirstOrderClassifyingMap
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    unrestrictedUniversalRing R K (Fin 2) rhoRes ⟶ ProartinianCat.dualNumber R :=
  unrestrictedClassifyingMap R K (Fin 2) rhoRes
    (bockleFirstOrderDeformationClass rhoRes σ)


/-- The universal dual-number classifying morphism attached to an arbitrary adjoint tangent
class, using a chosen cocycle representative. -/
noncomputable def bockleTangentClassifyingMap
    (x : BockleTangentSpace (toRepresentation rhoRes)) :
    unrestrictedUniversalRing R K (Fin 2) rhoRes ⟶ ProartinianCat.dualNumber R :=
  bockleFirstOrderClassifyingMap R K rhoRes
    (bockleTangentClassCocycleRepresentative (toRepresentation rhoRes) x)

/-- Specializing the universal deformation class along its first-order classifying map
recovers the deformation class defined by the cocycle. -/
theorem unrestrictedUniversalElement_map_bockleFirstOrderClassifyingMap
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    (deformationFunctor (Fin 2) (Γ K) R rhoRes).toFunctor.map
        (bockleFirstOrderClassifyingMap R K rhoRes σ)
        (unrestrictedUniversalElement R K (Fin 2) rhoRes) =
      bockleFirstOrderDeformationClass rhoRes σ :=
  unrestrictedUniversalElement_map_classifyingMap R K (Fin 2) rhoRes
    (bockleFirstOrderDeformationClass rhoRes σ)

/-- Distinct adjoint tangent classes give distinct universal dual-number classifying maps. -/
theorem bockleTangentClassifyingMap_injective
    [NeZero (2 : ProartinianCat.residueFieldType R)] :
    Function.Injective (bockleTangentClassifyingMap R K rhoRes) := by
  intro x y hxy
  let σ := bockleTangentClassCocycleRepresentative (toRepresentation rhoRes) x
  let τ := bockleTangentClassCocycleRepresentative (toRepresentation rhoRes) y
  have hmaps :
      bockleFirstOrderClassifyingMap R K rhoRes σ =
        bockleFirstOrderClassifyingMap R K rhoRes τ := by
    simpa only [bockleTangentClassifyingMap, σ, τ] using hxy
  have hclass :
      bockleFirstOrderDeformationClass rhoRes σ =
        bockleFirstOrderDeformationClass rhoRes τ := by
    rw [← unrestrictedUniversalElement_map_bockleFirstOrderClassifyingMap R K rhoRes σ,
      ← unrestrictedUniversalElement_map_bockleFirstOrderClassifyingMap R K rhoRes τ,
      hmaps]
  have htangent :=
    bockleTangentπ_eq_of_firstOrderDeformationClass_eq rhoRes σ τ hclass
  dsimp only [σ, τ] at htangent
  calc
    x = bockleTangentπ (toRepresentation rhoRes)
        (bockleTangentClassCocycleRepresentative (toRepresentation rhoRes) x) :=
      (bockleTangentπ_classCocycleRepresentative (toRepresentation rhoRes) x).symm
    _ = bockleTangentπ (toRepresentation rhoRes)
        (bockleTangentClassCocycleRepresentative (toRepresentation rhoRes) y) := htangent
    _ = y :=
      bockleTangentπ_classCocycleRepresentative (toRepresentation rhoRes) y


/-- On chosen representatives, specialization of the universal representation agrees with
the cocycle deformation up to strict equivalence. -/
theorem unrestrictedUniversalRepresentation_map_bockleFirstOrderClassifyingMap_toRepnQuot
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    (toRepnQuot (Fin 2) (Γ K) R).app (ProartinianCat.dualNumber R)
        ((repnFunctor (Fin 2) (Γ K) R).map
          (bockleFirstOrderClassifyingMap R K rhoRes σ)
          (unrestrictedUniversalRepresentation R K (Fin 2) rhoRes)) =
      (toRepnQuot (Fin 2) (Γ K) R).app (ProartinianCat.dualNumber R)
        (bockleFirstOrderRepnFunctor rhoRes σ) := by
  have hclass := congrArg Subtype.val
    (unrestrictedUniversalElement_map_bockleFirstOrderClassifyingMap R K rhoRes σ)
  change (repnQuotFunctor (Fin 2) (Γ K) R).map
      (bockleFirstOrderClassifyingMap R K rhoRes σ)
        (unrestrictedUniversalElement R K (Fin 2) rhoRes).1 =
      (bockleFirstOrderDeformationClass rhoRes σ).1 at hclass
  calc
    (toRepnQuot (Fin 2) (Γ K) R).app (ProartinianCat.dualNumber R)
        ((repnFunctor (Fin 2) (Γ K) R).map
          (bockleFirstOrderClassifyingMap R K rhoRes σ)
          (unrestrictedUniversalRepresentation R K (Fin 2) rhoRes)) =
      (repnQuotFunctor (Fin 2) (Γ K) R).map
        (bockleFirstOrderClassifyingMap R K rhoRes σ)
          ((toRepnQuot (Fin 2) (Γ K) R).app
            (unrestrictedUniversalRing R K (Fin 2) rhoRes)
            (unrestrictedUniversalRepresentation R K (Fin 2) rhoRes)) :=
      ((toRepnQuot (Fin 2) (Γ K) R).naturality_apply
        (bockleFirstOrderClassifyingMap R K rhoRes σ)
        (unrestrictedUniversalRepresentation R K (Fin 2) rhoRes)).symm
    _ = (repnQuotFunctor (Fin 2) (Γ K) R).map
        (bockleFirstOrderClassifyingMap R K rhoRes σ)
          (unrestrictedUniversalElement R K (Fin 2) rhoRes).1 := by
      rw [unrestrictedUniversalRepresentation_toRepnQuot R K (Fin 2) rhoRes]
    _ = (bockleFirstOrderDeformationClass rhoRes σ).1 := hclass
    _ = (toRepnQuot (Fin 2) (Γ K) R).app (ProartinianCat.dualNumber R)
        (bockleFirstOrderRepnFunctor rhoRes σ) := rfl

/-- A chosen tangent-basis vector determines a classifying morphism from the unrestricted
universal ring to the dual numbers. -/
noncomputable def bockleTangentBasisClassifyingMap
    [Module.Finite (ProartinianCat.residueFieldType R)
      (BockleTangentSpace (toRepresentation rhoRes))]
    (i : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    unrestrictedUniversalRing R K (Fin 2) rhoRes ⟶ ProartinianCat.dualNumber R :=
  bockleFirstOrderClassifyingMap R K rhoRes
    (bockleTangentCocycleRepresentative (toRepresentation rhoRes) i)

/-- The universal deformation class specializes along the `i`-th tangent map to the
strict-equivalence class representing the `i`-th tangent-basis vector. -/
theorem unrestrictedUniversalElement_map_bockleTangentBasisClassifyingMap
    [Module.Finite (ProartinianCat.residueFieldType R)
      (BockleTangentSpace (toRepresentation rhoRes))]
    (i : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    (deformationFunctor (Fin 2) (Γ K) R rhoRes).toFunctor.map
        (bockleTangentBasisClassifyingMap R K rhoRes i)
        (unrestrictedUniversalElement R K (Fin 2) rhoRes) =
      bockleTangentBasisDeformationClass rhoRes i :=
  unrestrictedUniversalElement_map_bockleFirstOrderClassifyingMap R K rhoRes _

/-- The canonical augmentation of the unrestricted universal deformation ring to the
coefficient residue field. -/
noncomputable def unrestrictedUniversalAugmentation :
    unrestrictedUniversalRing R K (Fin 2) rhoRes →ₐ[R]
      ProartinianCat.residueFieldType R :=
  (ProartinianCat.toResidueField
    (unrestrictedUniversalRing R K (Fin 2) rhoRes)).hom.toAlgHom

/-- Every first-order classifying map has the canonical residue component.  Categorically,
this is just uniqueness of the map to the terminal residue-field object. -/
theorem bockleFirstOrderClassifyingMap_augmentation
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    dualNumberAugmentation
        (bockleFirstOrderClassifyingMap R K rhoRes σ).hom.toAlgHom =
      unrestrictedUniversalAugmentation R K rhoRes := by
  have hterminal :
      bockleFirstOrderClassifyingMap R K rhoRes σ ≫
          ProartinianCat.dualNumberToResidueField R =
        ProartinianCat.toResidueField
          (unrestrictedUniversalRing R K (Fin 2) rhoRes) :=
    Subsingleton.elim _ _
  have hhom := congrArg
    (fun f : unrestrictedUniversalRing R K (Fin 2) rhoRes ⟶
        ProartinianCat.residueField =>
      f.hom.toAlgHom) hterminal
  exact hhom


/-- Bundle the classifying map of an arbitrary tangent class as a dual-number point over the
universal augmentation. -/
noncomputable def bockleTangentClassBasedPoint
    (x : BockleTangentSpace (toRepresentation rhoRes)) :
    {f : unrestrictedUniversalRing R K (Fin 2) rhoRes →ₐ[R]
        DualNumber (ProartinianCat.residueFieldType R) //
      dualNumberAugmentation f =
        unrestrictedUniversalAugmentation R K rhoRes} :=
  ⟨(bockleTangentClassifyingMap R K rhoRes x).hom.toAlgHom,
    bockleFirstOrderClassifyingMap_augmentation R K rhoRes _⟩

/-- The universal based dual-number point faithfully records the adjoint tangent class. -/
theorem bockleTangentClassBasedPoint_injective
    [NeZero (2 : ProartinianCat.residueFieldType R)] :
    Function.Injective (bockleTangentClassBasedPoint R K rhoRes) := by
  intro x y hxy
  apply bockleTangentClassifyingMap_injective R K rhoRes
  have hAlg := congrArg Subtype.val hxy
  change (bockleTangentClassifyingMap R K rhoRes x).hom.toAlgHom =
    (bockleTangentClassifyingMap R K rhoRes y).hom.toAlgHom at hAlg
  ext z
  exact DFunLike.congr_fun hAlg z

/-- The cotangent functional determined by an arbitrary adjoint tangent class. -/
noncomputable def bockleTangentClassCotangentFunctional
    (x : BockleTangentSpace (toRepresentation rhoRes)) :
    RelativeCotangentSpace (unrestrictedUniversalAugmentation R K rhoRes) →ₗ[
      ProartinianCat.residueFieldType R] ProartinianCat.residueFieldType R :=
  dualNumberCotangentFunctionalAt
    (unrestrictedUniversalAugmentation R K rhoRes)
    (bockleTangentClassBasedPoint R K rhoRes x).1
    (bockleTangentClassBasedPoint R K rhoRes x).2

/-- Cotangent functionals obtained from the universal deformation separate all adjoint tangent
classes. -/
theorem bockleTangentClassCotangentFunctional_injective
    [NeZero (2 : ProartinianCat.residueFieldType R)] :
    Function.Injective (bockleTangentClassCotangentFunctional R K rhoRes) := by
  intro x y hxy
  apply bockleTangentClassBasedPoint_injective R K rhoRes
  apply dualNumberCotangentFunctionalAt_injective
    (unrestrictedUniversalAugmentation R K rhoRes)
  exact hxy

/-- A tangent-basis classifying map, bundled together with the fact that it lies over the
canonical augmentation. -/
noncomputable def bockleTangentBasisBasedPoint
    [Module.Finite (ProartinianCat.residueFieldType R)
      (BockleTangentSpace (toRepresentation rhoRes))]
    (i : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    {f : unrestrictedUniversalRing R K (Fin 2) rhoRes →ₐ[R]
        DualNumber (ProartinianCat.residueFieldType R) //
      dualNumberAugmentation f =
        unrestrictedUniversalAugmentation R K rhoRes} :=
  ⟨(bockleTangentBasisClassifyingMap R K rhoRes i).hom.toAlgHom,
    bockleFirstOrderClassifyingMap_augmentation R K rhoRes _⟩

/-- The cotangent functional associated to the chosen `i`-th tangent-basis deformation. -/
noncomputable def bockleTangentBasisCotangentFunctional
    [Module.Finite (ProartinianCat.residueFieldType R)
      (BockleTangentSpace (toRepresentation rhoRes))]
    (i : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    RelativeCotangentSpace (unrestrictedUniversalAugmentation R K rhoRes) →ₗ[
      ProartinianCat.residueFieldType R] ProartinianCat.residueFieldType R :=
  dualNumberCotangentFunctionalAt
    (unrestrictedUniversalAugmentation R K rhoRes)
    (bockleTangentBasisBasedPoint R K rhoRes i).1
    (bockleTangentBasisBasedPoint R K rhoRes i).2
end Deformation
