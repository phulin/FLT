/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle.FirstOrder
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

end Deformation
