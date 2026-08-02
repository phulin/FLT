/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.NumberField.Completion.Finite
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# The valuative relation on completed number fields

The adic completion API currently supplies Mathlib's older `Valued` structure, whereas the
local-field and Tate-curve APIs use `ValuativeRel`.  This file installs the canonical bridge:
the relation is induced by the existing discrete valuation, and the existing topology is shown
to be its valuative topology.  The completed number field is consequently a
`IsNonarchimedeanLocalField` in the newer interface as well.
-/

@[expose] public section

open NumberField

namespace IsDedekindDomain.HeightOneSpectrum.adicCompletion

variable {K : Type*} [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The canonical valuative relation induced by the existing adic valuation. -/
noncomputable instance instValuativeRel : ValuativeRel (v.adicCompletion K) :=
  .ofValuation (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))

/-- The original adic valuation is compatible with the induced valuative relation. -/
instance instValuationCompatible :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
  .ofValuation _

/-- The pre-existing topology of the adic completion is induced by its canonical valuative
relation. -/
instance instIsValuativeTopology : IsValuativeTopology (v.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))) (fun {_} ↦ by
      simpa only [true_and] using
        (Valued.hasBasis_nhds_zero (v.adicCompletion K)
          (WithZero (Multiplicative ℤ))).mem_iff)

/-- The original discrete valuation on an adic completion is nontrivial. -/
instance instValuationIsNontrivial :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).IsNontrivial := by
  constructor
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective K (WithZero.exp (-1 : ℤ))
  refine ⟨x, ?_, ?_⟩
  · rw [hx]
    exact WithZero.exp_ne_zero
  · rw [hx]
    simp

/-- The canonical valuative relation on an adic completion is nontrivial. -/
instance instIsNontrivial : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))).mpr inferInstance

/-- A completed number field at a finite place, in the `ValuativeRel` local-field interface. -/
instance instIsNonarchimedeanLocalField :
    IsNonarchimedeanLocalField (v.adicCompletion K) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

/-- The integer subring defined through `ValuativeRel` is the original valuation subring of the
adic completion. -/
theorem integer_eq_adicCompletionIntegers :
    (ValuativeRel.valuation (v.adicCompletion K)).integer =
      (v.adicCompletionIntegers K).toSubring := by
  ext x
  rw [Valuation.mem_integer_iff]
  change ValuativeRel.valuation (v.adicCompletion K) x ≤ 1 ↔ Valued.v x ≤ 1
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

end IsDedekindDomain.HeightOneSpectrum.adicCompletion
