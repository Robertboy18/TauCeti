/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Y
public import TauCeti.RingTheory.WittVector.GaussNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
import TauCeti.RingTheory.Valuation.Integers
import TauCeti.RingTheory.Valuation.SpanPow

/-!
# The Gauss points of `𝒴 ⊆ Spa(A_inf, A_inf)`

Let `R` be a perfect ring of characteristic `p` with a valuation `v : R → ℝ≥0` bounded by `1`, give
the Witt vectors `𝕎 R` the `(p, [ϖ])`-adic topology for some `ϖ : R` with `0 < v ϖ < 1`, and let
`ρ < 1`. The **Gauss point** of radius `ρ` is the point of `Spv (𝕎 R)` of the Gauss norm
`|x|_ρ = sup_n v (x_n) ρ ^ n` (`TauCeti.WittVector.gaussValuation`). It is bounded by `1` on all of
`𝕎 R`, it is continuous because `|p|_ρ = ρ` and `|[ϖ]|_ρ = v ϖ` are both below `1`, and for
`ρ ≠ 0` neither `p` nor `[ϖ]` vanishes at it. It therefore lies in the open subset

```text
𝒴 = {v ∈ Spa(𝕎 R, 𝕎 R) : v(p [ϖ]) ≠ 0}
```

of `TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Y`, which is in particular nonempty. For
`R = 𝒪_F` the ring of integers of a perfect nonarchimedean field `F` of characteristic `p`, these
are the Gauss points of `𝒴 ⊆ Spa(A_inf, A_inf)` at which the adic Fargues–Fontaine curve is
usually drawn. In the radius convention of `Y.lean`, reading `κ(v) ≥ a / b` as
`v([ϖ]) ^ b ≤ v(p) ^ a`, the Gauss point of radius `ρ` has `κ ≥ a / b` exactly when
`(v ϖ) ^ b ≤ ρ ^ a`; for `ρ = v ϖ` this is the point of radius `κ = 1`.

## Main definitions

* `TauCeti.FarguesFontaine.gaussPoint`: the Gauss point of radius `ρ`, as a point of `Spv (𝕎 R)`.

## Main results

* `TauCeti.FarguesFontaine.gaussPoint_mem_spaY`: the Gauss point lies in `𝒴`.
* `TauCeti.FarguesFontaine.spaY_nonempty`: `𝒴` is nonempty.
* `Valuation.Integers.spaY_nonempty`: `𝒴` is nonempty for `A_inf = W(𝒪_F)`, `𝒪_F` the ring of
  integers of a perfect nonarchimedean field of characteristic `p` with a pseudouniformiser `ϖ`.
* `TauCeti.FarguesFontaine.gaussPoint_teichmuller_pow_vle_natCast_pow_iff`: the radius of the
  Gauss point.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §1.4.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017, §3.1.
-/

public section

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum TauCeti.WittVector _root_.WittVector
open scoped NNReal

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
  (v : Valuation R ℝ≥0) {ρ : ℝ≥0} (hv : ∀ r, v r ≤ 1) (hρ₁ : ρ < 1)

/-- The **Gauss point** of radius `ρ` of the Witt vectors of a perfect valued ring `(R, v)`: the
point of `Spv (𝕎 R)` of the Gauss norm `|x|_ρ = sup_n v (x_n) ρ ^ n`. -/
noncomputable def gaussPoint : Spv (WittVector p R) :=
  ofValuation (gaussValuation v ρ hv hρ₁)

/-- The Gauss point compares elements by their Gauss norms. -/
theorem gaussPoint_vle_iff (a b : WittVector p R) :
    (gaussPoint p v hv hρ₁).toValuativeRel.vle a b ↔ gaussNorm v ρ a ≤ gaussNorm v ρ b := by
  rw [gaussPoint, vle_ofValuation, gaussValuation_apply, gaussValuation_apply]

/-- The Gauss point of a nonzero radius has trivial support when `v` does. -/
theorem supp_gaussPoint (hρ₀ : 0 < ρ) (hsupp : v.supp = ⊥) : (gaussPoint p v hv hρ₁).supp = ⊥ := by
  rw [gaussPoint, supp_ofValuation, supp_gaussValuation hv hρ₀ hρ₁ hsupp]

/-- `p` does not vanish at the Gauss point of a nonzero radius: `|p|_ρ = ρ ≠ 0`. -/
theorem natCast_notMem_supp_gaussPoint (hρ₀ : 0 < ρ) :
    (p : WittVector p R) ∉ (gaussPoint p v hv hρ₁).supp := by
  rw [gaussPoint, supp_ofValuation, Valuation.mem_supp_iff, gaussValuation_apply,
    gaussNorm_natCast hv hρ₁.le]
  exact hρ₀.ne'

/-- `[ϖ]` does not vanish at the Gauss point when `v ϖ ≠ 0`: `|[ϖ]|_ρ = v ϖ`. -/
theorem teichmuller_notMem_supp_gaussPoint {ϖ : R} (hϖ : v ϖ ≠ 0) :
    teichmuller p ϖ ∉ (gaussPoint p v hv hρ₁).supp := by
  rw [gaussPoint, supp_ofValuation, Valuation.mem_supp_iff, gaussValuation_apply,
    gaussNorm_teichmuller hv hρ₁.le]
  exact hϖ

/-- **The radius of the Gauss point, from below.** Reading `κ(w) ≥ a / b` as
`w([ϖ]) ^ b ≤ w(p) ^ a`, the Gauss point of radius `ρ` has `κ ≥ a / b` exactly when
`(v ϖ) ^ b ≤ ρ ^ a`. -/
theorem gaussPoint_teichmuller_pow_vle_natCast_pow_iff (ϖ : R) (a b : ℕ) :
    (gaussPoint p v hv hρ₁).toValuativeRel.vle (teichmuller p ϖ ^ b)
      ((p : WittVector p R) ^ a) ↔ v ϖ ^ b ≤ ρ ^ a := by
  rw [gaussPoint_vle_iff, ← gaussValuation_apply hv hρ₁, ← gaussValuation_apply hv hρ₁,
    map_pow, map_pow, gaussValuation_apply, gaussValuation_apply, gaussNorm_natCast hv hρ₁.le,
    gaussNorm_teichmuller hv hρ₁.le]

/-- **The radius of the Gauss point, from above.** Reading `κ(w) ≤ a / b` as
`w(p) ^ a ≤ w([ϖ]) ^ b`, the Gauss point of radius `ρ` has `κ ≤ a / b` exactly when
`ρ ^ a ≤ (v ϖ) ^ b`. -/
theorem gaussPoint_natCast_pow_vle_teichmuller_pow_iff (ϖ : R) (a b : ℕ) :
    (gaussPoint p v hv hρ₁).toValuativeRel.vle ((p : WittVector p R) ^ a)
      (teichmuller p ϖ ^ b) ↔ ρ ^ a ≤ v ϖ ^ b := by
  rw [gaussPoint_vle_iff, ← gaussValuation_apply hv hρ₁, ← gaussValuation_apply hv hρ₁,
    map_pow, map_pow, gaussValuation_apply, gaussValuation_apply, gaussNorm_natCast hv hρ₁.le,
    gaussNorm_teichmuller hv hρ₁.le]

variable [TopologicalSpace (WittVector p R)] {ϖ : R}

/-- **The Gauss valuation is continuous** for the `(p, [ϖ])`-adic topology when `v ϖ < 1`: it is
bounded by `1`, and `|p|_ρ = ρ` and `|[ϖ]|_ρ = v ϖ` are both below `1`, so the powers of the ideal
`(p, [ϖ])` have arbitrarily small Gauss norm. -/
theorem isContinuous_gaussValuation
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) (hϖ : v ϖ < 1) :
    (gaussValuation v ρ hv hρ₁).IsContinuous := by
  have : IsTopologicalRing (WittVector p R) :=
    hI ▸ (Ideal.span {(p : WittVector p R), teichmuller p ϖ}).nonarchimedean.toIsTopologicalRing
  set w := gaussValuation v ρ hv hρ₁ with hw
  rw [Valuation.isContinuous_iff_forall_ne_zero]
  intro b hb
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr hb) (max_lt hρ₁ hϖ)
  -- the `(n + 1)`-st power of `(p, [ϖ])` lies in the sublevel set `{a | w a < w b}`
  have hsub : ((Ideal.span {(p : WittVector p R), teichmuller p ϖ} ^ (n + 1) :
      Ideal (WittVector p R)) : Set (WittVector p R)) ⊆ {a | w a < w b} := fun a ha ↦ by
    refine (w.map_le_pow_of_mem_span_pow_succ (δ := max ρ (v ϖ)) ?_ (fun a _ ↦ ?_) ha).trans_lt hn
    · intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · rw [hw, gaussValuation_apply, gaussNorm_natCast hv hρ₁.le]; exact le_max_left _ _
      · rw [hw, gaussValuation_apply, gaussNorm_teichmuller hv hρ₁.le]; exact le_max_right _ _
    · rw [hw, gaussValuation_apply]; exact gaussNorm_le_one hv hρ₁.le a
  -- so the sublevel set, an additive subgroup, is a neighbourhood of `0`, hence open
  rw [← w.coe_ltAddSubgroupOfNeZero hb]
  refine AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset
    (((isAdic_iff.mp hI).1 (n + 1)).mem_nhds (Ideal.zero_mem _)) ?_)
  rwa [w.coe_ltAddSubgroupOfNeZero hb]

/-- **The Gauss point is a point of `Spa(𝕎 R, 𝕎 R)`** for the `(p, [ϖ])`-adic topology when
`v ϖ < 1`: it is continuous and bounded by `1`. -/
theorem gaussPoint_mem_spa (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hϖ : v ϖ < 1) : gaussPoint p v hv hρ₁ ∈ spa (⊤ : Subring (WittVector p R)) := by
  rw [mem_spa_iff, gaussPoint, isContinuous_ofValuation_iff]
  refine ⟨isContinuous_gaussValuation p v hv hρ₁ hI hϖ,
    fun a _ ↦ (vle_ofValuation _ _ _).mpr ?_⟩
  rw [map_one, gaussValuation_apply]
  exact gaussNorm_le_one hv hρ₁.le a

/-- **The Gauss point of a nonzero radius lies in `𝒴`**, for the `(p, [ϖ])`-adic topology and
`0 < v ϖ < 1`. -/
theorem gaussPoint_mem_spaY (hρ₀ : 0 < ρ)
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hϖ₀ : v ϖ ≠ 0) (hϖ₁ : v ϖ < 1) : gaussPoint p v hv hρ₁ ∈ spaY p ϖ :=
  (mem_spaY_iff p ϖ _).mpr ⟨gaussPoint_mem_spa p v hv hρ₁ hI hϖ₁,
    natCast_notMem_supp_gaussPoint p v hv hρ₁ hρ₀,
    teichmuller_notMem_supp_gaussPoint p v hv hρ₁ hϖ₀⟩

include hv in
/-- **`𝒴` is nonempty**: for a perfect ring `R` of characteristic `p` with a valuation `v ≤ 1` and
`0 < v ϖ < 1`, the Gauss point of radius `v ϖ` lies in `𝒴 ⊆ Spa(𝕎 R, 𝕎 R)`. -/
theorem spaY_nonempty (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hϖ₀ : 0 < v ϖ) (hϖ₁ : v ϖ < 1) : (spaY p ϖ).Nonempty :=
  ⟨_, gaussPoint_mem_spaY p v hv hϖ₁ hϖ₀ hI hϖ₀.ne' hϖ₁⟩

end TauCeti.FarguesFontaine

namespace Valuation.Integers

variable {p : ℕ} [Fact p.Prime] {K O : Type*} [NormedField K] [IsUltrametricDist K] [CharP K p]
  [PerfectRing K p] [CommRing O] [Algebra O K] [TopologicalSpace (WittVector p O)]

/-- **`𝒴 ⊆ Spa(A_inf, A_inf)` is nonempty.** Let `O = 𝒪_F` be the ring of integers of a perfect
nonarchimedean field `F` of characteristic `p`, let `ϖ ∈ O` be a nonzero element of norm less than
one, and give `A_inf = W(O)` its `(p, [ϖ])`-adic topology. Then `𝒴 = D(p) ∩ D([ϖ])` contains the
Gauss point of radius `‖ϖ‖`. -/
theorem spaY_nonempty (hv : (NormedField.valuation (K := K)).Integers O) {ϖ : O}
    (hϖ₀ : algebraMap O K ϖ ≠ 0) (hϖ₁ : ‖algebraMap O K ϖ‖ < 1)
    (hI : IsAdic (Ideal.span {(p : WittVector p O), WittVector.teichmuller p ϖ})) :
    (TauCeti.FarguesFontaine.spaY p ϖ).Nonempty :=
  -- `O` inherits the characteristic of `K` along the injection `O → K`, and is perfect.
  have : CharP O p := ⟨fun n ↦ by
    rw [← CharP.cast_eq_zero_iff K p, ← map_natCast (algebraMap O K), map_eq_zero_iff _ hv.hom_inj]⟩
  have : PerfectRing O p := hv.perfectRing p
  TauCeti.FarguesFontaine.spaY_nonempty p ((NormedField.valuation (K := K)).comap (algebraMap O K))
    (fun r ↦ by simpa using hv.map_le_one r) hI (by simpa using hϖ₀)
    (by rw [Valuation.comap_apply, NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm,
      NNReal.coe_one]; exact hϖ₁)

end Valuation.Integers

end
