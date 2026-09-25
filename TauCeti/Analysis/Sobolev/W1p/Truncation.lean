/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.LevelSet

import Mathlib.MeasureTheory.Function.UnifTight

/-!
# Continuity of positive truncation

For `1 ≤ p < ∞`, taking the positive part is continuous in `W^{1,p}(Ω)` and preserves
`W^{1,p}_0(Ω)`. Neither assertion requires boundedness or boundary regularity of `Ω`.

Positive parts of functions with zero boundary values are therefore admissible Sobolev test
functions. In particular, this applies to the difference of two functions with the same
Dirichlet boundary data, as needed in weak comparison arguments.

* `TauCeti.W1p.continuous_posPart`: continuity in the full Sobolev norm.
* `TauCeti.W1p.posPart_mem_w1p0Submodule`: preservation of the homogeneous Dirichlet condition.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E]

private def posPartJet (z : Sobolev1Jet E) : Sobolev1Jet E :=
  if 0 < z.fst then z else 0

private theorem norm_posPartJet_le (z : Sobolev1Jet E) :
    ‖posPartJet z‖ ≤ ‖z‖ := by
  by_cases hz : 0 < z.fst <;> simp [posPartJet, hz]

private theorem continuousAt_posPartJet {z : Sobolev1Jet E}
    (hzero : z.fst = 0 → z = 0) : ContinuousAt posPartJet z := by
  rcases lt_trichotomy 0 z.fst with hpos | heq | hneg
  · have he : ∀ᶠ w in 𝓝 z, 0 < w.fst :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_gt_nhds hpos)
    change Tendsto posPartJet (𝓝 z) (𝓝 (posPartJet z))
    rw [show posPartJet z = z by simp [posPartJet, hpos]]
    exact tendsto_id.congr' (he.mono fun w hw ↦ by simp [posPartJet, hw])
  · have hz := hzero heq.symm
    subst z
    simpa only [ContinuousAt, posPartJet, WithLp.zero_fst, lt_self_iff_false,
      ite_false] using squeeze_zero_norm norm_posPartJet_le tendsto_norm_zero
  · have he : ∀ᶠ w in 𝓝 z, w.fst < 0 :=
      ((WithLp.continuous_fst 2 ℝ E).tendsto z).eventually (eventually_lt_nhds hneg)
    change Tendsto posPartJet (𝓝 z) (𝓝 (posPartJet z))
    rw [show posPartJet z = 0 by simp [posPartJet, not_lt_of_gt hneg]]
    exact tendsto_const_nhds.congr' (he.mono fun w hw ↦ by
      simp [posPartJet, not_lt_of_gt hw])

variable [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem posPart_coe_ae (hp : p ≠ ∞) (u : W1p mu Omega p) :
    ⇑(W1p.posPart hp u : Sobolev1JetLp mu Omega p) =ᵐ[mu.restrict Omega]
      fun x ↦ posPartJet ((u : Sobolev1JetLp mu Omega p) x) := by
  filter_upwards [W1p.value_apply_ae (W1p.posPart hp u),
    W1p.gradient_apply_ae (W1p.posPart hp u), W1p.value_apply_ae u,
    W1p.gradient_apply_ae u, Lp.coeFn_posPart (W1p.value u),
    W1p.gradient_posPart_ae hp u] with x hv hg huv hug hvp hgp
  rw [W1p.value_posPart] at hv
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change WithLp.fst _ = WithLp.fst _
    rw [← hv, hvp]
    by_cases hx : 0 < W1p.value u x
    · simp [posPartJet, ← huv, hx, max_eq_left hx.le]
    · simp [posPartJet, ← huv, hx, max_eq_right (le_of_not_gt hx)]
  · change WithLp.snd _ = WithLp.snd _
    rw [← hg, hgp]
    by_cases hx : 0 < W1p.value u x <;> simp [posPartJet, ← huv, ← hug, hx]

/-- Taking the positive part is continuous in the Sobolev norm for finite exponents. -/
theorem W1p.continuous_posPart (hp : p ≠ ∞) :
    Continuous (W1p.posPart (mu := mu) (Omega := Omega) hp) := by
  rw [continuous_iff_seqContinuous]
  intro a u ha
  apply tendsto_subtype_rng.mpr
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hsrc : Tendsto (fun n ↦ (a (ns n) : Sobolev1JetLp mu Omega p)) atTop
      (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    (tendsto_subtype_rng.mp ha).comp hns
  -- An almost-everywhere convergent subsequence identifies the truncated limit.
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hsrc).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  let f : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ a (ns (ms n))
  let g : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ W1p.posPart hp (a (ns (ms n)))
  have hf : Tendsto f atTop (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    hsrc.comp hms.tendsto_atTop
  have hvitali := (tendstoInMeasure_iff_tendsto_Lp (Fact.out : 1 ≤ p) hp
    (fun n ↦ Lp.memLp (f n)) (Lp.memLp (u : Sobolev1JetLp mu Omega p))).mpr
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hf)
  have hnorm (n : ℕ) : ∀ᵐ x ∂mu.restrict Omega, ‖g n x‖ ≤ ‖f n x‖ := by
    filter_upwards [posPart_coe_ae hp (a (ns (ms n)))] with x hx
    change ‖(W1p.posPart hp (a (ns (ms n))) : Sobolev1JetLp mu Omega p) x‖ ≤ _
    rw [hx]
    exact norm_posPartJet_le _
  have hui : UnifIntegrable (fun n x ↦ g n x) p (mu.restrict Omega) :=
    hvitali.2.1.ae_mono fun n ↦ (hnorm n).mono fun x hx ↦ by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
  have hut : UnifTight (fun n x ↦ g n x) p (mu.restrict Omega) := by
    intro ε hε
    obtain ⟨s, hs, hbound⟩ := hvitali.2.2 ε hε
    refine ⟨s, hs, fun n ↦ (eLpNorm_mono_ae ?_).trans (hbound n)⟩
    filter_upwards [hnorm n] with x hx
    by_cases hxs : x ∈ sᶜ
    · simpa only [Set.indicator_of_mem hxs] using hx
    · simp only [Set.indicator_of_notMem hxs, norm_zero, le_refl]
  -- The only discontinuity of the jet truncation disappears on Sobolev level sets.
  have hzero : ∀ᵐ x ∂mu.restrict Omega,
      ((u : Sobolev1JetLp mu Omega p) x).fst = 0 →
        (u : Sobolev1JetLp mu Omega p) x = 0 := by
    filter_upwards [W1p.value_apply_ae u, W1p.gradient_apply_ae u,
      W1p.gradient_ae_eq_zero_on_level_set hp u 0] with x hv hg hz
    intro hx
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact hx
    · change ((u : Sobolev1JetLp mu Omega p) x).snd = 0
      rw [← hg]
      exact hz (hv.trans hx)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply tendsto_Lp_of_tendsto_ae (Fact.out : 1 ≤ p) hp
    (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable)
    (Lp.memLp (W1p.posPart hp u : Sobolev1JetLp mu Omega p)) hui hut
  filter_upwards [hae, hzero, ae_all_iff.mpr (fun n ↦ posPart_coe_ae hp (a (ns (ms n)))),
    posPart_coe_ae hp u] with x hx hz hg hu
  rw [hu]
  exact ((continuousAt_posPartJet hz).tendsto.comp hx).congr'
    (Eventually.of_forall fun n ↦ (hg n).symm)

/-- Positive truncation preserves the homogeneous Dirichlet boundary condition. -/
theorem W1p.posPart_mem_w1p0Submodule (hp : p ≠ ∞) {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.posPart hp u ∈ w1p0Submodule mu Omega p := by
  refine w1p0Submodule_subset_of_isClosed
    ((w1p0Submodule mu Omega p).isClosed.preimage (W1p.continuous_posPart hp)) ?_ hu
  intro phi
  apply W1p.mem_w1p0Submodule_of_isCompact hp phi.hasCompactSupport phi.tsupport_subset
  filter_upwards [Lp.coeFn_posPart (W1p.value (W1p.ofTestFunctionₗ mu Omega p phi)),
    testFunctionLp_apply_ae (mu := mu) p phi] with x hx hphi
  intro hxK
  rw [W1p.value_posPart, hx, W1p.value_ofTestFunctionₗ, hphi,
    image_eq_zero_of_notMem_tsupport hxK, max_self]

end TauCeti
