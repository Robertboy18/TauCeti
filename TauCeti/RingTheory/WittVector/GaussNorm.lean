/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.NNReal.Basic
public import TauCeti.RingTheory.Valuation.WeightedHomogeneous
public import TauCeti.RingTheory.WittVector.TeichmullerCoord
public import TauCeti.RingTheory.WittVector.WeightedHomogeneous

/-!
# Gauss norms on Witt vectors of a perfect valued ring

Let `R` be a perfect ring of characteristic `p` with a valuation `v : R → ℝ≥0` bounded by `1`, for
instance the ring of integers `𝒪_F` of a perfect nonarchimedean field `F` of characteristic `p`,
and let `0 < ρ < 1`. Writing a Witt vector in Teichmüller coordinates, `x = ∑ [x_n] p ^ n`
(`TauCeti.WittVector.teichmullerCoord`), its **Gauss norm** of radius `ρ` is

```text
|x|_ρ = sup_n v (x_n) ρ ^ n.
```

This file proves that `|·|_ρ` is a valuation on `𝕎 R` with values in `ℝ≥0`
(`TauCeti.WittVector.gaussValuation`): it is ultrametric and multiplicative, takes the value `ρ` at
`p` and the value `v r` at a Teichmüller representative `[r]`, and is bounded by `1`. These are
the Gauss norms of Fargues–Fontaine and Kedlaya on `A_inf = W(𝒪_F)`; they are the points of the
Fargues–Fontaine space `𝒴 ⊆ Spa(A_inf, A_inf)` with `v (p) = ρ` and `v ([ϖ]) = v ϖ`.

The two inequalities come from the shape of the Teichmüller expansion.

* *Ultrametricity.* The `n`-th component of `x + y` is a polynomial in the components of `x` and
  `y` that is weighted homogeneous of weight `p ^ n` when the `i`-th component has weight `p ^ i`
  (`TauCeti.WittVector.isWeightedHomogeneous_wittAdd`), so `v ((x + y).coeff n) ≤ C ^ (p ^ n)` as
  soon as `v (x.coeff i), v (y.coeff i) ≤ C ^ (p ^ i)` for `i ≤ n`
  (`TauCeti.WittVector.map_coeff_add_le`). In Teichmüller coordinates this is the ultrametric bound
  `v ((x + y)_n) ≤ max_{i ≤ n} (v (x_i), v (y_i))`, and `ρ ≤ 1` turns it into
  `|x + y|_ρ ≤ max (|x|_ρ, |y|_ρ)`.
* *Multiplicativity.* Modulo `p ^ (N + 1)`, the product `x y` is the Teichmüller series
  `∑_{a, b ≤ N} [x_a y_b] p ^ (a + b)`. The ultrametric bound on its `N`-th coordinate gives
  `|x y|_ρ ≤ |x|_ρ |y|_ρ`. For the reverse inequality, let `i` and `j` be the largest indices at
  which `|x|_ρ` and `|y|_ρ` are attained; they exist because `ρ < 1`. In the `(i + j)`-th
  coordinate the term `[x_i y_j] p ^ (i + j)` contributes exactly `x_i y_j`, with no carry
  (`TauCeti.WittVector.teichmullerCoord_add_of_pow_dvd`), while every other term of the series
  contributes strictly less than `v (x_i y_j)`, so `v ((x y)_{i + j}) = v (x_i) v (y_j)` and
  `|x y|_ρ ≥ |x|_ρ |y|_ρ`.

## Main definitions

* `TauCeti.WittVector.gaussNorm v ρ x`: the Gauss norm `sup_n v (x_n) ρ ^ n`.
* `TauCeti.WittVector.gaussValuation v ρ`: the Gauss norm as a valuation on `𝕎 R`, for `v ≤ 1`
  and `ρ < 1`.

## Main results

* `TauCeti.WittVector.map_coeff_add_le`: the ultrametric bound on the components of a sum of Witt
  vectors over any valued ring.
* `TauCeti.WittVector.gaussNorm_add_le`, `TauCeti.WittVector.gaussNorm_mul`: the Gauss norm is
  ultrametric and multiplicative.
* `TauCeti.WittVector.gaussNorm_teichmuller`, `TauCeti.WittVector.gaussNorm_natCast`: its values
  `|[r]|_ρ = v r` and `|p|_ρ = ρ`.
* `TauCeti.WittVector.gaussNorm_eq_zero_iff`: when `v` has trivial support, so does `|·|_ρ`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §1.4, the Gauss norms on `W(𝒪_F)`.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors*, Nagoya Math. J. 209 (2013), §4, and
  *Sheaves, stacks, and shtukas*, Arizona Winter School 2017, §3.1.
-/

public section

namespace TauCeti.WittVector

open _root_.WittVector Finset Filter
open scoped NNReal

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

local notation "𝕎" => _root_.WittVector p

section Component

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- **Ultrametric bound on the components of a sum of Witt vectors.** If the `i`-th components of
`x` and `y` have valuation at most `C ^ (p ^ i)` for all `i ≤ n`, then so does the `n`-th component
of `x + y`: the addition polynomial `wittAdd p n` is weighted homogeneous of weight `p ^ n` for the
weights `p ^ i`. -/
theorem map_coeff_add_le (x y : 𝕎 R) {n : ℕ} {C : Γ₀}
    (hx : ∀ m ≤ n, v (x.coeff m) ≤ C ^ p ^ m) (hy : ∀ m ≤ n, v (y.coeff m) ≤ C ^ p ^ m) :
    v ((x + y).coeff n) ≤ C ^ p ^ n := by
  rw [add_coeff, peval]
  refine v.map_aeval_le_pow_of_isWeightedHomogeneous (isWeightedHomogeneous_wittAdd p n) ?_
  rintro ⟨b, i⟩ hbi
  have hi : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp (wittAdd_vars p n hbi)).2)
  rw [wittWeight_apply]
  fin_cases b
  · exact hx i hi
  · exact hy i hi

end Component

variable [CharP R p] [PerfectRing R p] (v : Valuation R ℝ≥0)

/-- **Ultrametric bound on the Teichmüller coordinates of a sum.** -/
theorem map_teichmullerCoord_add_le (x y : 𝕎 R) {n : ℕ} {C : ℝ≥0}
    (hx : ∀ m ≤ n, v (teichmullerCoord x m) ≤ C) (hy : ∀ m ≤ n, v (teichmullerCoord y m) ≤ C) :
    v (teichmullerCoord (x + y) n) ≤ C := by
  have hpn : p ^ n ≠ 0 := pow_ne_zero n hp.out.ne_zero
  rw [← pow_le_pow_iff_left₀ zero_le zero_le hpn, ← map_pow, teichmullerCoord_pow]
  refine map_coeff_add_le v x y (fun m hm ↦ ?_) fun m hm ↦ ?_
  · rw [← teichmullerCoord_pow, map_pow]; exact pow_le_pow_left' (hx m hm) _
  · rw [← teichmullerCoord_pow, map_pow]; exact pow_le_pow_left' (hy m hm) _

/-- **Ultrametric bound on the Teichmüller coordinates of a finite sum.** -/
theorem map_teichmullerCoord_sum_le {ι : Type*} (s : Finset ι) (f : ι → 𝕎 R) {n : ℕ} {C : ℝ≥0}
    (h : ∀ k ∈ s, ∀ m ≤ n, v (teichmullerCoord (f k) m) ≤ C) :
    v (teichmullerCoord (∑ k ∈ s, f k) n) ≤ C := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact map_teichmullerCoord_add_le v _ _ (h a (mem_insert_self a s))
      fun m hm ↦ ih fun k hk m' hm' ↦ h k (mem_insert_of_mem hk) m' (hm'.trans hm)

/-- Modulo `p ^ (N + 1)`, a product of Witt vectors is the Teichmüller series
`∑_{a, b ≤ N} [x_a y_b] p ^ (a + b)`, so its `N`-th Teichmüller coordinate is that of the series. -/
theorem teichmullerCoord_mul_eq_teichmullerCoord_sum (x y : 𝕎 R) (N : ℕ) :
    teichmullerCoord (x * y) N =
      teichmullerCoord (∑ ab ∈ Iic N ×ˢ Iic N,
        teichmuller p (teichmullerCoord x ab.1 * teichmullerCoord y ab.2) *
          (p : 𝕎 R) ^ (ab.1 + ab.2)) N := by
  apply teichmullerCoord_eq_of_pow_succ_dvd_sub
  obtain ⟨c, hc⟩ := pow_succ_dvd_sub_sum_teichmuller_teichmullerCoord x N
  obtain ⟨d, hd⟩ := pow_succ_dvd_sub_sum_teichmuller_teichmullerCoord y N
  set X := ∑ i ∈ Iic N, teichmuller p (teichmullerCoord x i) * (p : 𝕎 R) ^ i
  set Y := ∑ i ∈ Iic N, teichmuller p (teichmullerCoord y i) * (p : 𝕎 R) ^ i
  have hXY : X * Y = ∑ ab ∈ Iic N ×ˢ Iic N,
      teichmuller p (teichmullerCoord x ab.1 * teichmullerCoord y ab.2) *
        (p : 𝕎 R) ^ (ab.1 + ab.2) := by
    rw [sum_product, sum_mul_sum]
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    rw [map_mul, pow_add]; ring
  rw [← hXY, show x * y - X * Y = (x - X) * y + X * (y - Y) by ring, hc, hd]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
    (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)

variable (ρ : ℝ≥0)

/-- The **Gauss norm** of radius `ρ` of a Witt vector `x = ∑ [x_n] p ^ n`, in terms of its
Teichmüller coordinates: `|x|_ρ = sup_n v (x_n) ρ ^ n`. For `v ≤ 1` and `0 < ρ < 1` it is a
valuation on `𝕎 R` (`TauCeti.WittVector.gaussValuation`). -/
noncomputable def gaussNorm (x : 𝕎 R) : ℝ≥0 :=
  ⨆ n, v (teichmullerCoord x n) * ρ ^ n

variable {v ρ}

/-- A bound on every term `v (x_n) ρ ^ n` bounds the Gauss norm. -/
theorem gaussNorm_le {x : 𝕎 R} {C : ℝ≥0} (h : ∀ n, v (teichmullerCoord x n) * ρ ^ n ≤ C) :
    gaussNorm v ρ x ≤ C :=
  ciSup_le h

@[simp]
theorem gaussNorm_zero : gaussNorm v ρ 0 = 0 := by
  simp [gaussNorm]

variable (hv : ∀ r, v r ≤ 1) (hρ : ρ ≤ 1)
include hv hρ

/-- Each term `v (x_n) ρ ^ n` is bounded by the Gauss norm. -/
theorem le_gaussNorm (x : 𝕎 R) (n : ℕ) : v (teichmullerCoord x n) * ρ ^ n ≤ gaussNorm v ρ x := by
  have hbdd : BddAbove (Set.range fun m ↦ v (teichmullerCoord x m) * ρ ^ m) :=
    ⟨1, by
      rintro _ ⟨m, rfl⟩
      exact mul_le_one' (hv _) (pow_le_one₀ zero_le hρ)⟩
  exact le_ciSup hbdd n

/-- The Gauss norm is bounded by `1` when `v` and `ρ` are. -/
theorem gaussNorm_le_one (x : 𝕎 R) : gaussNorm v ρ x ≤ 1 :=
  gaussNorm_le fun _ ↦ mul_le_one' (hv _) (pow_le_one₀ zero_le hρ)

/-- The Gauss norm of a Teichmüller representative `[r]` is `v r`. -/
theorem gaussNorm_teichmuller (r : R) : gaussNorm v ρ (teichmuller p r) = v r := by
  refine le_antisymm (gaussNorm_le fun n ↦ ?_)
    (by simpa using le_gaussNorm hv hρ (teichmuller p r) 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [teichmullerCoord_teichmuller_of_pos r hn]

theorem gaussNorm_one : gaussNorm v ρ 1 = 1 := by
  simpa using gaussNorm_teichmuller hv hρ (1 : R)

/-- Multiplying by `p ^ k` multiplies the Gauss norm by `ρ ^ k`. -/
theorem gaussNorm_mul_pow (x : 𝕎 R) (k : ℕ) :
    gaussNorm v ρ (x * (p : 𝕎 R) ^ k) = ρ ^ k * gaussNorm v ρ x := by
  refine le_antisymm (gaussNorm_le fun m ↦ ?_) ?_
  · rcases lt_or_ge m k with h | h
    · simp [teichmullerCoord_mul_pow_of_lt x h]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
      rw [teichmullerCoord_mul_pow, pow_add, ← mul_assoc, mul_comm]
      exact mul_le_mul_right (le_gaussNorm hv hρ x n) _
  · rw [gaussNorm, NNReal.mul_iSup]
    refine ciSup_le fun n ↦ ?_
    calc ρ ^ k * (v (teichmullerCoord x n) * ρ ^ n)
        = v (teichmullerCoord (x * (p : 𝕎 R) ^ k) (n + k)) * ρ ^ (n + k) := by
          rw [teichmullerCoord_mul_pow, pow_add]; ring
      _ ≤ _ := le_gaussNorm hv hρ _ _

/-- The Gauss norm of radius `ρ` takes the value `ρ` at `p`. -/
theorem gaussNorm_natCast : gaussNorm v ρ (p : 𝕎 R) = ρ := by
  have := gaussNorm_mul_pow hv hρ (1 : 𝕎 R) 1
  rwa [one_mul, pow_one, pow_one, gaussNorm_one hv hρ, mul_one] at this

/-- **The Gauss norm is ultrametric.** -/
theorem gaussNorm_add_le (x y : 𝕎 R) :
    gaussNorm v ρ (x + y) ≤ max (gaussNorm v ρ x) (gaussNorm v ρ y) := by
  refine gaussNorm_le fun n ↦ ?_
  rcases eq_or_ne (ρ ^ n) 0 with hn | hn
  · rw [hn, mul_zero]; exact zero_le
  have hn' : 0 < ρ ^ n := pos_iff_ne_zero.mpr hn
  rw [← le_div_iff₀ hn']
  refine map_teichmullerCoord_add_le v x y (fun m hm ↦ ?_) fun m hm ↦ ?_
  · rw [le_div_iff₀ hn']
    exact (mul_le_mul_right (pow_le_pow_of_le_one zero_le hρ hm) _).trans
      ((le_gaussNorm hv hρ x m).trans (le_max_left _ _))
  · rw [le_div_iff₀ hn']
    exact (mul_le_mul_right (pow_le_pow_of_le_one zero_le hρ hm) _).trans
      ((le_gaussNorm hv hρ y m).trans (le_max_right _ _))

/-- **The Gauss norm is submultiplicative.** -/
theorem gaussNorm_mul_le (x y : 𝕎 R) :
    gaussNorm v ρ (x * y) ≤ gaussNorm v ρ x * gaussNorm v ρ y := by
  refine gaussNorm_le fun N ↦ ?_
  rcases eq_or_ne (ρ ^ N) 0 with hN | hN
  · rw [hN, mul_zero]; exact zero_le
  have hN' : 0 < ρ ^ N := pos_iff_ne_zero.mpr hN
  rw [teichmullerCoord_mul_eq_teichmullerCoord_sum, ← le_div_iff₀ hN']
  refine map_teichmullerCoord_sum_le v _ _ fun ab _ m hm ↦ ?_
  rcases eq_or_ne m (ab.1 + ab.2) with rfl | hne
  · rw [teichmullerCoord_teichmuller_mul_pow, map_mul, le_div_iff₀ hN']
    calc v (teichmullerCoord x ab.1) * v (teichmullerCoord y ab.2) * ρ ^ N
        ≤ v (teichmullerCoord x ab.1) * v (teichmullerCoord y ab.2) * ρ ^ (ab.1 + ab.2) :=
          mul_le_mul_right (pow_le_pow_of_le_one zero_le hρ hm) _
      _ = (v (teichmullerCoord x ab.1) * ρ ^ ab.1) * (v (teichmullerCoord y ab.2) * ρ ^ ab.2) := by
          rw [pow_add]; ring
      _ ≤ _ := mul_le_mul' (le_gaussNorm hv hρ x _) (le_gaussNorm hv hρ y _)
  · rw [teichmullerCoord_teichmuller_mul_pow_of_ne _ hne, map_zero]
    exact zero_le

omit hρ in
/-- **The Gauss norm is attained, at a largest index.** For `ρ < 1` and `|x|_ρ ≠ 0`, there is an
index `i` with `v (x_i) ρ ^ i = |x|_ρ` and `v (x_n) ρ ^ n < |x|_ρ` for all `n > i`: the terms
`v (x_n) ρ ^ n ≤ ρ ^ n` tend to zero, so the supremum is a maximum over finitely many indices. -/
theorem exists_eq_gaussNorm_and_forall_lt (hρ₁ : ρ < 1) {x : 𝕎 R} (hx : gaussNorm v ρ x ≠ 0) :
    ∃ i, v (teichmullerCoord x i) * ρ ^ i = gaussNorm v ρ x ∧
      ∀ n, i < n → v (teichmullerCoord x n) * ρ ^ n < gaussNorm v ρ x := by
  classical
  have hρ : ρ ≤ 1 := hρ₁.le
  -- beyond some index `N`, every term lies strictly below `|x|_ρ`
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hρ₁).eventually_lt_const
      (pos_iff_ne_zero.mpr hx))
  have hlt : ∀ n, N ≤ n → v (teichmullerCoord x n) * ρ ^ n < gaussNorm v ρ x := fun n hn ↦
    (mul_le_of_le_one_left zero_le (hv _)).trans_lt (hN n hn)
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact absurd (hN 0 le_rfl) (not_lt.mpr (by simpa using gaussNorm_le_one hv hρ x))
  -- so `|x|_ρ` is the maximum of the terms with index below `N`
  obtain ⟨i₀, hi₀, hmax⟩ := (range N).exists_max_image
    (fun n ↦ v (teichmullerCoord x n) * ρ ^ n) (nonempty_range_iff.mpr hN0)
  have h1 : gaussNorm v ρ x ≤ max (v (teichmullerCoord x i₀) * ρ ^ i₀) (ρ ^ N) :=
    gaussNorm_le fun n ↦ by
      rcases lt_or_ge n N with h | h
      · exact (hmax n (mem_range.mpr h)).trans (le_max_left _ _)
      · exact ((mul_le_of_le_one_left zero_le (hv _)).trans
          (pow_le_pow_of_le_one zero_le hρ h)).trans (le_max_right _ _)
  have hi₀eq : v (teichmullerCoord x i₀) * ρ ^ i₀ = gaussNorm v ρ x := by
    refine le_antisymm (le_gaussNorm hv hρ x i₀) ?_
    rcases le_max_iff.mp h1 with h | h
    · exact h
    · exact absurd h (not_le.mpr (hN N le_rfl))
  -- take the largest index below `N` attaining `|x|_ρ`
  set P : ℕ → Prop := fun n ↦ v (teichmullerCoord x n) * ρ ^ n = gaussNorm v ρ x
  refine ⟨Nat.findGreatest P N, Nat.findGreatest_spec (P := P) (mem_range.mp hi₀).le hi₀eq,
    fun n hn ↦ ?_⟩
  rcases lt_or_ge n N with h | h
  · exact lt_of_le_of_ne (le_gaussNorm hv hρ x n) (Nat.findGreatest_is_greatest hn h.le)
  · exact hlt n h

omit hρ in
/-- In the product expansion `x y = ∑ [x_a y_b] p ^ (a + b)`, every term other than the one at the
leading indices `(i, j)` of `x` and `y` has `v (x_a) v (y_b) ρ ^ (i + j) < |x|_ρ |y|_ρ`, provided
`a + b ≤ i + j`. Only the maximality of `i` and `j` enters. -/
private theorem map_mul_map_mul_pow_lt_of_ne (hρ₁ : ρ < 1) {x y : 𝕎 R} {i j : ℕ}
    (hi' : ∀ n, i < n → v (teichmullerCoord x n) * ρ ^ n < gaussNorm v ρ x)
    (hj' : ∀ n, j < n → v (teichmullerCoord y n) * ρ ^ n < gaussNorm v ρ y)
    (hx : gaussNorm v ρ x ≠ 0) (hy : gaussNorm v ρ y ≠ 0) {a b : ℕ} (hab : (a, b) ≠ (i, j))
    (hle : a + b ≤ i + j) :
    v (teichmullerCoord x a) * v (teichmullerCoord y b) * ρ ^ (i + j) <
      gaussNorm v ρ x * gaussNorm v ρ y := by
  have hρ : ρ ≤ 1 := hρ₁.le
  have hxpos : 0 < gaussNorm v ρ x := pos_iff_ne_zero.mpr hx
  have hypos : 0 < gaussNorm v ρ y := pos_iff_ne_zero.mpr hy
  rcases hle.lt_or_eq with hlt | heq
  · -- `a + b < i + j`: the extra factor `ρ ^ (i + j - a - b)` is strictly below `1`
    calc v (teichmullerCoord x a) * v (teichmullerCoord y b) * ρ ^ (i + j)
        = (v (teichmullerCoord x a) * ρ ^ a) * (v (teichmullerCoord y b) * ρ ^ b) *
            ρ ^ (i + j - (a + b)) := by
          rw [← Nat.add_sub_cancel' hlt.le, pow_add, pow_add, Nat.add_sub_cancel_left]; ring
      _ ≤ gaussNorm v ρ x * gaussNorm v ρ y * ρ ^ (i + j - (a + b)) :=
          mul_le_mul_left (mul_le_mul' (le_gaussNorm hv hρ x a) (le_gaussNorm hv hρ y b)) _
      _ < gaussNorm v ρ x * gaussNorm v ρ y * 1 :=
          mul_lt_mul_of_pos_left (pow_lt_one₀ zero_le hρ₁ (Nat.sub_ne_zero_of_lt hlt))
            (mul_pos hxpos hypos)
      _ = _ := mul_one _
  · -- `a + b = i + j` with `(a, b) ≠ (i, j)`: one of the two factors is strictly below its norm
    have hsplit : v (teichmullerCoord x a) * v (teichmullerCoord y b) * ρ ^ (i + j) =
        (v (teichmullerCoord x a) * ρ ^ a) * (v (teichmullerCoord y b) * ρ ^ b) := by
      rw [← heq, pow_add]; ring
    rw [hsplit]
    have hai : a ≠ i := fun h ↦ hab (by subst h; exact Prod.ext rfl (by omega))
    rcases lt_or_gt_of_ne hai with h | h
    · exact (mul_le_mul_left (le_gaussNorm hv hρ x a) _).trans_lt
        (mul_lt_mul_of_pos_left (hj' b (by omega)) hxpos)
    · exact (mul_le_mul_right (le_gaussNorm hv hρ y b) _).trans_lt
        (mul_lt_mul_of_pos_right (hi' a h) hypos)

omit hρ in
/-- Away from the leading indices `(i, j)`, the terms of the product expansion
`∑_{a, b ≤ i + j} [x_a y_b] p ^ (a + b)` contribute strictly less than `v (x_i) v (y_j)` to the
`(i + j)`-th Teichmüller coordinate. -/
private theorem map_teichmullerCoord_sum_erase_lt (hρ₁ : ρ < 1) {x y : 𝕎 R} {i j : ℕ}
    (hi : v (teichmullerCoord x i) * ρ ^ i = gaussNorm v ρ x)
    (hi' : ∀ n, i < n → v (teichmullerCoord x n) * ρ ^ n < gaussNorm v ρ x)
    (hj : v (teichmullerCoord y j) * ρ ^ j = gaussNorm v ρ y)
    (hj' : ∀ n, j < n → v (teichmullerCoord y n) * ρ ^ n < gaussNorm v ρ y)
    (hx : gaussNorm v ρ x ≠ 0) (hy : gaussNorm v ρ y ≠ 0) :
    v (teichmullerCoord (∑ ab ∈ (Iic (i + j) ×ˢ Iic (i + j)).erase (i, j),
        teichmuller p (teichmullerCoord x ab.1 * teichmullerCoord y ab.2) *
          (p : 𝕎 R) ^ (ab.1 + ab.2)) (i + j)) <
      v (teichmullerCoord x i) * v (teichmullerCoord y j) := by
  classical
  set c := v (teichmullerCoord x i) * v (teichmullerCoord y j) with hc
  have hcρ : c * ρ ^ (i + j) = gaussNorm v ρ x * gaussNorm v ρ y := by
    rw [hc, ← hi, ← hj, pow_add]; ring
  have hcpos : 0 < c := pos_iff_ne_zero.mpr fun h ↦
    mul_ne_zero hx hy (by rw [← hcρ, h, zero_mul])
  -- a uniform bound strictly below `c` for the other terms
  set g : ℕ × ℕ → ℝ≥0 := fun ab ↦
    if ab.1 + ab.2 ≤ i + j then v (teichmullerCoord x ab.1) * v (teichmullerCoord y ab.2) else 0
    with hg
  have hlt : ((Iic (i + j) ×ˢ Iic (i + j)).erase (i, j)).sup g < c :=
    (Finset.sup_lt_iff (by simpa using hcpos)).mpr fun ab hab ↦ by
      rw [hg]; dsimp only
      split_ifs with h
      · exact lt_of_mul_lt_mul_right ((map_mul_map_mul_pow_lt_of_ne hv hρ₁ hi' hj' hx hy
          (mem_erase.mp hab).1 h).trans_eq hcρ.symm) zero_le
      · exact hcpos
  refine (map_teichmullerCoord_sum_le v _ _ fun ab hab m hm ↦ ?_).trans_lt hlt
  rcases eq_or_ne m (ab.1 + ab.2) with rfl | hne
  · rw [teichmullerCoord_teichmuller_mul_pow, map_mul]
    refine le_trans ?_ (Finset.le_sup (f := g) hab)
    rw [hg]; dsimp only
    rw [ite_eq_left hm]
  · rw [teichmullerCoord_teichmuller_mul_pow_of_ne _ hne, map_zero]
    exact zero_le

omit hρ in
/-- **The Gauss norm is supermultiplicative.** With `i` and `j` the largest indices at which `|x|_ρ`
and `|y|_ρ` are attained, the `(i + j)`-th Teichmüller coordinate of `x y` has valuation exactly
`v (x_i) v (y_j)`. -/
theorem gaussNorm_mul_gaussNorm_le (hρ₁ : ρ < 1) (x y : 𝕎 R) :
    gaussNorm v ρ x * gaussNorm v ρ y ≤ gaussNorm v ρ (x * y) := by
  classical
  rcases eq_or_ne (gaussNorm v ρ x) 0 with hx | hx
  · simp [hx]
  rcases eq_or_ne (gaussNorm v ρ y) 0 with hy | hy
  · simp [hy]
  obtain ⟨i, hi, hi'⟩ := exists_eq_gaussNorm_and_forall_lt hv hρ₁ hx
  obtain ⟨j, hj, hj'⟩ := exists_eq_gaussNorm_and_forall_lt hv hρ₁ hy
  have hmem : (i, j) ∈ Iic (i + j) ×ˢ Iic (i + j) :=
    mem_product.mpr ⟨mem_Iic.mpr (Nat.le_add_right i j), mem_Iic.mpr (Nat.le_add_left j i)⟩
  -- the `(i + j)`-th coordinate of `x * y` is `x_i y_j`: no carry, and the other terms are smaller
  have hlead : v (teichmullerCoord (x * y) (i + j)) =
      v (teichmullerCoord x i) * v (teichmullerCoord y j) := by
    rw [teichmullerCoord_mul_eq_teichmullerCoord_sum, ← add_sum_erase _ _ hmem,
      teichmullerCoord_add_of_pow_dvd (dvd_mul_left _ _), v.map_add_eq_of_lt_left]
    · rw [teichmullerCoord_teichmuller_mul_pow, map_mul]
    · rw [teichmullerCoord_teichmuller_mul_pow, map_mul]
      exact map_teichmullerCoord_sum_erase_lt hv hρ₁ hi hi' hj hj' hx hy
  calc gaussNorm v ρ x * gaussNorm v ρ y
      = v (teichmullerCoord (x * y) (i + j)) * ρ ^ (i + j) := by
        rw [hlead, ← hi, ← hj, pow_add]; ring
    _ ≤ gaussNorm v ρ (x * y) := le_gaussNorm hv hρ₁.le _ _

omit hρ in
/-- **The Gauss norm is multiplicative.** -/
theorem gaussNorm_mul (hρ₁ : ρ < 1) (x y : 𝕎 R) :
    gaussNorm v ρ (x * y) = gaussNorm v ρ x * gaussNorm v ρ y :=
  le_antisymm (gaussNorm_mul_le hv hρ₁.le x y) (gaussNorm_mul_gaussNorm_le hv hρ₁ x y)

/-- When `v` has trivial support, `|x|_ρ = 0` only for `x = 0`. -/
theorem gaussNorm_eq_zero_iff (hρ₀ : 0 < ρ) (hsupp : v.supp = ⊥) {x : 𝕎 R} :
    gaussNorm v ρ x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ WittVector.ext fun n ↦ ?_, fun h ↦ h ▸ gaussNorm_zero⟩
  have h1 := le_gaussNorm hv hρ x n
  rw [h, nonpos_iff_eq_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · have hmem : teichmullerCoord x n ∈ v.supp := (Valuation.mem_supp_iff v _).mpr h1
    rw [hsupp, Ideal.mem_bot, teichmullerCoord_eq_zero_iff] at hmem
    simpa using hmem
  · exact absurd h1 (pow_ne_zero n hρ₀.ne')

omit hρ in
variable (v ρ) in
/-- The **Gauss norm of radius `ρ` as a valuation** on `𝕎 R`, for a valuation `v ≤ 1` on the
perfect ring `R` of characteristic `p` and `ρ < 1`: `x ↦ sup_n v (x_n) ρ ^ n`. -/
noncomputable def gaussValuation (hρ₁ : ρ < 1) : Valuation (𝕎 R) ℝ≥0 where
  toFun := gaussNorm v ρ
  map_zero' := gaussNorm_zero
  map_one' := gaussNorm_one hv hρ₁.le
  map_mul' := gaussNorm_mul hv hρ₁
  map_add_le_max' := gaussNorm_add_le hv hρ₁.le

omit hρ in
@[simp]
theorem gaussValuation_apply (hρ₁ : ρ < 1) (x : 𝕎 R) :
    gaussValuation v ρ hv hρ₁ x = gaussNorm v ρ x := (rfl)

omit hρ in
/-- When `v` has trivial support and `ρ ≠ 0`, the Gauss valuation has trivial support. -/
theorem supp_gaussValuation (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (hsupp : v.supp = ⊥) :
    (gaussValuation v ρ hv hρ₁).supp = ⊥ := by
  ext x
  rw [Valuation.mem_supp_iff, gaussValuation_apply, gaussNorm_eq_zero_iff hv hρ₁.le hρ₀ hsupp,
    Ideal.mem_bot]

end TauCeti.WittVector

end
