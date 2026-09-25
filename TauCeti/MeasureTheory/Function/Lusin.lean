/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Lusin's theorem

A measurable map from a finite weakly regular measure space into a second-countable topological
space is continuous off a set of arbitrarily small measure: for every `ε > 0` there is a closed set
`F` with `μ Fᶜ < ε` on which the map is continuous. This is **Lusin's theorem**. Its usual
formulation with a compact set is the closed one followed by inner regularity by compact sets,
and its usual hypothesis, a finite Borel measure on a Polish or metrizable space, is one of the
regimes in which finite measures are weakly regular (Mathlib's
`MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`).

The proof approximates the preimage of each member of a countable basis of the target, and the
preimage of its complement, from inside by closed sets, and intersects the resulting unions; on
the intersection every basic preimage is relatively open. For an almost-everywhere measurable map,
the closed set is taken inside a closed subset of the complement of the null set on which the map
differs from a measurable one.

The theorem is the bridge from measurability to topology in arguments about weak convergence of
measures: it lets a Borel map be treated as a continuous one on a closed set carrying almost all
of the mass, so that the portmanteau theorem, which only sees closed and open sets, applies to
sets defined through the map. The almost-everywhere measurable version is included because the
maps produced by `ProbabilityTheory.HasLaw` are only almost-everywhere measurable.

## Main statements

* `TauCeti.exists_isClosed_measure_compl_lt_continuousOn` — **Lusin's theorem**: a measurable
  map into a second-countable space is continuous on a closed set whose complement has measure
  less than any prescribed `ε > 0`;
* `TauCeti.exists_isClosed_measure_compl_lt_continuousOn_of_aemeasurable` — the same for an
  almost-everywhere measurable map.

## References

* W. Rudin, *Real and Complex Analysis*, third edition, McGraw-Hill 1987, Theorem 2.24, the
  classical statement for locally compact Hausdorff spaces.
* D. H. Fremlin, *Measure Theory*, Volume 4, Torres Fremlin 2003, §418, Lusin's theorem for
  measurable functions into second-countable spaces from the inner regularity of the measure.
-/

public section

open MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {μ : Measure X} [μ.WeaklyRegular] [IsFiniteMeasure μ] {f : X → Y} {ε : ℝ≥0∞}

/-- **Lusin's theorem.** A measurable map `f` from a finite weakly regular measure space into a
second-countable topological space is continuous on a closed set `F` with `μ Fᶜ < ε`, for every
`ε > 0`. -/
theorem exists_isClosed_measure_compl_lt_continuousOn (hf : Measurable f) (hε : ε ≠ 0) :
    ∃ F : Set X, IsClosed F ∧ μ Fᶜ < ε ∧ ContinuousOn f F := by
  set B := TopologicalSpace.countableBasis Y
  have : Countable B := (TopologicalSpace.countable_countableBasis Y).to_subtype
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε B
  have hδ2 : ∀ U : B, δ U / 2 ≠ 0 := fun U ↦ (ENNReal.half_pos (hδ U).ne').ne'
  have hmeas : ∀ U : B, MeasurableSet (f ⁻¹' U) := fun U ↦
    hf (TopologicalSpace.isOpen_of_mem_countableBasis U.2).measurableSet
  choose F hFsub hFclosed hFμ using fun U : B ↦
    (hmeas U).exists_isClosed_sdiff_lt (measure_ne_top μ _) (hδ2 U)
  choose G hGsub hGclosed hGμ using fun U : B ↦
    (hmeas U).compl.exists_isClosed_sdiff_lt (measure_ne_top μ _) (hδ2 U)
  refine ⟨⋂ U, F U ∪ G U, isClosed_iInter fun U ↦ (hFclosed U).union (hGclosed U), ?_, ?_⟩
  · calc μ (⋂ U, F U ∪ G U)ᶜ
        = μ (⋃ U, (F U ∪ G U)ᶜ) := by rw [compl_iInter]
      _ ≤ ∑' U, μ (F U ∪ G U)ᶜ := measure_iUnion_le _
      _ ≤ ∑' U, δ U := ENNReal.tsum_le_tsum fun U ↦ ?_
      _ < ε := hδε
    have hsub : (F U ∪ G U)ᶜ ⊆ (f ⁻¹' U \ F U) ∪ ((f ⁻¹' U)ᶜ \ G U) := fun x hx ↦ by
      simp only [mem_compl_iff, mem_union, not_or] at hx
      by_cases hxU : x ∈ f ⁻¹' U
      · exact Or.inl ⟨hxU, hx.1⟩
      · exact Or.inr ⟨hxU, hx.2⟩
    calc μ (F U ∪ G U)ᶜ
        ≤ μ (f ⁻¹' U \ F U) + μ ((f ⁻¹' U)ᶜ \ G U) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ δ U / 2 + δ U / 2 := add_le_add (hFμ U).le (hGμ U).le
      _ = δ U := ENNReal.add_halves _
  · rw [continuousOn_iff_continuous_domRestrict]
    refine (TopologicalSpace.isBasis_countableBasis Y).continuous_iff.2 fun U hU ↦ ?_
    have hpre : (⋂ U, F U ∪ G U).domRestrict f ⁻¹' U = Subtype.val ⁻¹' (G ⟨U, hU⟩)ᶜ := by
      ext ⟨x, hx⟩
      simp only [mem_preimage, domRestrict_apply, mem_compl_iff]
      refine ⟨fun hxU hxG ↦ hGsub ⟨U, hU⟩ hxG hxU, fun hxG ↦ ?_⟩
      rcases mem_iInter.1 hx ⟨U, hU⟩ with hxF | hxG'
      · exact hFsub ⟨U, hU⟩ hxF
      · exact absurd hxG' hxG
    rw [hpre]
    exact (hGclosed _).isOpen_compl.preimage continuous_subtype_val

/-- **Lusin's theorem** for an almost-everywhere measurable map: it is continuous on a closed set
`F` with `μ Fᶜ < ε`, for every `ε > 0`. -/
theorem exists_isClosed_measure_compl_lt_continuousOn_of_aemeasurable (hf : AEMeasurable f μ)
    (hε : ε ≠ 0) : ∃ F : Set X, IsClosed F ∧ μ Fᶜ < ε ∧ ContinuousOn f F := by
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨F₁, hF₁, hF₁μ, hF₁f⟩ :=
    exists_isClosed_measure_compl_lt_continuousOn (μ := μ) hf.measurable_mk hε2
  set N := toMeasurable μ {x | f x ≠ hf.mk f x} with hN
  have hNμ : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hf.ae_eq_mk
  obtain ⟨F₂, hF₂N, hF₂, hF₂μ⟩ := (measurableSet_toMeasurable μ _).compl.exists_isClosed_sdiff_lt
    (measure_ne_top μ Nᶜ) hε2
  refine ⟨F₁ ∩ F₂, hF₁.inter hF₂, ?_, ?_⟩
  · have hsub : F₂ᶜ ⊆ (Nᶜ \ F₂) ∪ N := fun x hx ↦ by
      by_cases hxN : x ∈ N
      · exact Or.inr hxN
      · exact Or.inl ⟨hxN, hx⟩
    calc μ (F₁ ∩ F₂)ᶜ
        ≤ μ F₁ᶜ + μ F₂ᶜ := by rw [compl_inter]; exact measure_union_le _ _
      _ ≤ μ F₁ᶜ + (μ (Nᶜ \ F₂) + μ N) := by
          gcongr
          exact (measure_mono hsub).trans (measure_union_le _ _)
      _ = μ F₁ᶜ + μ (Nᶜ \ F₂) := by rw [hNμ, add_zero]
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hF₁μ hF₂μ
      _ = ε := ENNReal.add_halves ε
  · refine (hF₁f.mono inter_subset_left).congr fun x hx ↦ ?_
    have hxN : x ∉ N := hF₂N hx.2
    by_contra hne
    exact hxN (subset_toMeasurable μ _ hne)

end TauCeti
