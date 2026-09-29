/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.NumberTheory.Padics.PrincipalUnits
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic

/-!
# Pro-`p` groups and the unit group `ℤ_pˣ`

Every open normal subgroup of `ℤ_2ˣ` contains a principal unit group `U^(f) = 1 + 2^f ℤ_2`,
whose index is `2 ^ (f - 1)`, so every continuous finite quotient of `ℤ_2ˣ` is a `2`-group. This
is what makes `ℤ_2ˣ` an admissible target for continuous characters of pro-`2` groups, such as
the orientation character of a dyadic Demushkin group. For odd `p` the unit group `ℤ_pˣ` is not
pro-`p`, since it contains the roots of unity of order `p - 1`. In the other direction, a
continuous character of a pro-`p` group into `ℤ_pˣ` has pro-`p` range, so it takes values in the
principal units `1 + pℤ_p`.

Since `ℤ_2ˣ` is pro-`2`, its elements have `2`-adic powers. The sign `-1` has order two, so
`(-1) ^ s` depends only on `s mod 2`, and a relation `v ^ s u ^ t = 1` between a unit `v` of sign
`-1` and a unit `u ∈ 1 + 4ℤ_2` forces `s` to be even: this is how the two marked values of a
character with image `{±1} × U^(f)` are separated. In that situation `v ^ 2 = (-v) ^ 2 ∈ U^(f)` is a
`2`-adic power of a topological generator `u` of `U^(f)`.

## Main results

* `TauCeti.isProP_units_padicInt_two`: `ℤ_2ˣ` is a pro-`2` group.
* `TauCeti.padicPow_neg_one`, `TauCeti.two_dvd_of_padicPow_mul_padicPow_eq_one`: `(-1) ^ s` is
  `(-1) ^ (s mod 2)`, and a relation `v ^ s u ^ t = 1` with `-v, u ∈ 1 + 4ℤ_2` has `s` even.
* `TauCeti.exists_padicPow_eq_sq_of_neg_mem_unitsPrincipal`: if `-v ∈ U^(f)` and `u` has exact
  level `f ≥ 2`, then `v ^ 2` is a `2`-adic power of `u`.
* `TauCeti.IsProP.mem_unitsPrincipal_one`: a continuous character of a pro-`p` group into `ℤ_pˣ`
  takes values in the principal units `1 + pℤ_p`.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]

/-- A continuous character of a pro-`p` group takes values in the principal units `1 + pℤ_p`: its
range is a pro-`p` subgroup of `ℤ_pˣ`. -/
theorem IsProP.mem_unitsPrincipal_one (hG : IsProP p G) (χ : G →ₜ* ℤ_[p]ˣ) (g : G) :
    χ g ∈ unitsPrincipal p 1 :=
  have : IsProP p χ.toMonoidHom.range :=
    hG.of_surjective χ.toMonoidHom.rangeRestrict (continuous_induced_rng.mpr χ.continuous)
      χ.toMonoidHom.rangeRestrict_surjective
  this.le_unitsPrincipal_one ⟨g, rfl⟩

/-- **`ℤ_2ˣ` is pro-`2`**: every open normal subgroup contains a principal unit group `U^(f)`, of
index `2 ^ (f - 1)`. -/
theorem isProP_units_padicInt_two : IsProP 2 ℤ_[2]ˣ := by
  refine isProP_iff.mpr fun U ↦ ?_
  obtain ⟨f, -, hf⟩ := (hasBasis_nhds_one_unitsPrincipal 2).mem_iff.mp
    (U.isOpen.mem_nhds (one_mem _))
  refine IsPGroup.of_card_dvd_pow (n := f - 1) ?_
  rw [← Subgroup.index_eq_card, ← index_unitsPrincipal_two f]
  exact Subgroup.index_dvd_of_le hf

/-! ### `2`-adic powers in `ℤ_2ˣ` -/

/-- In `ℤ_2ˣ`, the `2`-adic power `(-1) ^ s` is `(-1) ^ (s mod 2)`. -/
theorem padicPow_neg_one (s : ℤ_[2]) :
    isProP_units_padicInt_two.padicPow (-1 : ℤ_[2]ˣ) s = (-1) ^ s.appr 1 := by
  obtain ⟨k, hk⟩ : (2 : ℤ_[2]) ∣ s - s.appr 1 := by
    have := PadicInt.appr_spec 1 s
    rwa [pow_one, Ideal.mem_span_singleton, Nat.cast_ofNat] at this
  have hs : s = (s.appr 1 : ℤ_[2]) + 2 * k := by rw [← hk]; ring
  calc isProP_units_padicInt_two.padicPow (-1 : ℤ_[2]ˣ) s
      = isProP_units_padicInt_two.padicPow (-1 : ℤ_[2]ˣ) ((s.appr 1 : ℤ_[2]) + 2 * k) := by
        rw [← hs]
    _ = (-1) ^ s.appr 1 := by
        rw [IsProP.padicPow_add, IsProP.padicPow_natCast, IsProP.padicPow_mul,
          IsProP.padicPow_ofNat, neg_one_sq, IsProP.one_padicPow, mul_one]

/-- If `(-1) ^ s ∈ 1 + 4ℤ_2` for a `2`-adic exponent `s`, then `s` is even. -/
theorem two_dvd_of_padicPow_neg_one_mem_unitsPrincipal {s : ℤ_[2]}
    (h : isProP_units_padicInt_two.padicPow (-1 : ℤ_[2]ˣ) s ∈ unitsPrincipal 2 2) :
    (2 : ℤ_[2]) ∣ s := by
  have hspec : (2 : ℤ_[2]) ∣ s - s.appr 1 := by
    have := PadicInt.appr_spec 1 s
    rwa [pow_one, Ideal.mem_span_singleton, Nat.cast_ofNat] at this
  rw [padicPow_neg_one] at h
  have hlt : s.appr 1 < 2 := PadicInt.appr_lt s 1
  interval_cases hr : s.appr 1
  · simpa using hspec
  · exact absurd (neg_one_mem_unitsPrincipal_two_iff.mp (by simpa using h)) (by norm_num)

/-- **The sign of a relation between two dyadic units.** If `-v` and `u` lie in `1 + 4ℤ_2` and
`v ^ s u ^ t = 1` for `2`-adic exponents, then `s` is even: modulo `1 + 4ℤ_2` the relation reads
`(-1) ^ s = 1`. -/
theorem two_dvd_of_padicPow_mul_padicPow_eq_one {v u : ℤ_[2]ˣ} (hv : -v ∈ unitsPrincipal 2 2)
    (hu : u ∈ unitsPrincipal 2 2) {s t : ℤ_[2]}
    (h : isProP_units_padicInt_two.padicPow v s * isProP_units_padicInt_two.padicPow u t = 1) :
    (2 : ℤ_[2]) ∣ s := by
  have hv' : v = -1 * -v := by rw [neg_one_mul, neg_neg]
  refine two_dvd_of_padicPow_neg_one_mem_unitsPrincipal (s := s) ?_
  have h1 := isProP_units_padicInt_two.padicPow_mem (isClosed_unitsPrincipal 2 2) hv s
  have h2 := isProP_units_padicInt_two.padicPow_mem (isClosed_unitsPrincipal 2 2) hu t
  have hinv : isProP_units_padicInt_two.padicPow (-1) s =
      (isProP_units_padicInt_two.padicPow (-v) s * isProP_units_padicInt_two.padicPow u t)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc,
      ← isProP_units_padicInt_two.mul_padicPow (-1) (-v) (Commute.all _ _) s, ← hv', h]
  rw [hinv]
  exact (unitsPrincipal 2 2).inv_mem (mul_mem h1 h2)

/-- If `-v ∈ U^(f)` and `u` has exact level `f ≥ 2`, then `v ^ 2` is a `2`-adic power of `u`:
`v ^ 2 = (-v) ^ 2` lies in `U^(f)`, which `u` topologically generates. -/
theorem exists_padicPow_eq_sq_of_neg_mem_unitsPrincipal {f : ℕ} (hf : 2 ≤ f) {v u : ℤ_[2]ˣ}
    (hv : -v ∈ unitsPrincipal 2 f) (hu : u ∈ unitsPrincipal 2 f)
    (hu' : u ∉ unitsPrincipal 2 (f + 1)) :
    ∃ m : ℤ_[2], isProP_units_padicInt_two.padicPow u m = v ^ 2 := by
  have hv2 : v ^ 2 ∈ unitsPrincipal 2 f := by
    have := (unitsPrincipal 2 f).pow_mem hv 2
    rwa [neg_sq] at this
  rw [← topologicalClosure_zpowers_eq_unitsPrincipal (by omega) (fun _ ↦ hf) hu hu',
    Subgroup.zpowers_eq_closure] at hv2
  exact isProP_units_padicInt_two.mem_topologicalClosure_closure_singleton_iff.mp hv2

end TauCeti
