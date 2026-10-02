/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.RingTheory.WittVector.TeichmullerSeries

/-!
# Teichmüller coordinates of Witt vectors over a perfect ring

Let `R` be a perfect ring of characteristic `p`. Every Witt vector `x : 𝕎 R` has a Teichmüller
expansion `x = ∑ [x_n] p ^ n`, where `[r] = teichmuller p r` and the *Teichmüller coordinate*
`x_n` is the `p ^ n`-th root of the `n`-th Witt component `x.coeff n`: Mathlib's
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` gives the congruence
`x ≡ ∑_{i ≤ n} [x_i] p ^ i (mod p ^ (n + 1))`. This file names the coordinates and records how they
behave under the operations that preserve the shape of the expansion: multiplication by `p ^ k`
shifts them, a Teichmüller series `∑ [f i] p ^ i` has coordinates `f i`, and the `N`-th
component of a sum `u + z` with `p ^ N ∣ u` is the sum of the `N`-th components, because the
carries of Witt-vector addition into the `N`-th component only come from lower components.

The coordinates are the variables of the Gauss norms `|x|_ρ = sup_n |x_n| ρ ^ n` on `𝕎 R`, for
which see `TauCeti.RingTheory.WittVector.GaussNorm`.

## Main definitions

* `TauCeti.WittVector.teichmullerCoord`: the `n`-th Teichmüller coordinate of a Witt vector.

## Main results

* `TauCeti.WittVector.teichmullerCoord_pow`: `x_n ^ (p ^ n) = x.coeff n`.
* `TauCeti.WittVector.pow_succ_dvd_sub_sum_teichmuller_teichmullerCoord`: the Teichmüller
  expansion `x ≡ ∑_{i ≤ n} [x_i] p ^ i (mod p ^ (n + 1))`.
* `TauCeti.WittVector.teichmullerCoord_mul_pow`: multiplication by `p ^ k` shifts the coordinates.
* `TauCeti.WittVector.teichmullerCoord_sum_teichmuller_mul_pow`: the coordinates of a Teichmüller
  series.
* `TauCeti.WittVector.teichmullerCoord_add_of_pow_dvd`: `(u + z)_N = u_N + z_N` when `p ^ N ∣ u`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §1.4, for the Teichmüller expansion of Witt vectors over a perfect ring.
-/

public section

namespace TauCeti.WittVector

open _root_.WittVector Finset

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

local notation "𝕎" => _root_.WittVector p

/-- The `n`-th component of a Teichmüller series `∑ [f i] p ^ i` is `f n ^ (p ^ n)` when `n` is in
the index set, and `0` otherwise: the term `[f i] p ^ i` only has an `i`-th component. -/
theorem coeff_sum_teichmuller_mul_pow (f : ℕ → R) (s : Finset ℕ) (n : ℕ) :
    (∑ i ∈ s, teichmuller p (f i) * p ^ i).coeff n = if n ∈ s then f n ^ p ^ n else 0 := by
  rw [sum_coeff_eq_coeff_sum]
  · rw [← sum_ite_eq s n fun i ↦ f i ^ p ^ i]
    refine sum_congr rfl fun i _ ↦ ?_
    split_ifs with h
    · subst h; exact teichmuller_mul_pow_coeff n (f n)
    · exact teichmuller_mul_pow_coeff_of_ne _ h
  · refine fun n ↦ ⟨fun ⟨a, _, ha⟩ ⟨b, _, hb⟩ ↦ Subtype.ext ?_⟩
    exact (Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) ha).symm.trans
      (Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hb)

variable [PerfectRing R p]

/-- The `n`-th **Teichmüller coordinate** `x_n` of a Witt vector `x` over a perfect ring of
characteristic `p`: the `p ^ n`-th root of the `n`-th Witt component of `x`, so that
`x ≡ ∑_{i ≤ n} [x_i] p ^ i (mod p ^ (n + 1))`
(`TauCeti.WittVector.pow_succ_dvd_sub_sum_teichmuller_teichmullerCoord`). -/
noncomputable def teichmullerCoord (x : 𝕎 R) (n : ℕ) : R :=
  (iterateFrobeniusEquiv R p n).symm (x.coeff n)

theorem teichmullerCoord_pow (x : 𝕎 R) (n : ℕ) : teichmullerCoord x n ^ p ^ n = x.coeff n := by
  rw [teichmullerCoord, ← iterateFrobeniusEquiv_def R p n, RingEquiv.apply_symm_apply]

@[simp]
theorem teichmullerCoord_eq_zero_iff {x : 𝕎 R} {n : ℕ} :
    teichmullerCoord x n = 0 ↔ x.coeff n = 0 :=
  (iterateFrobeniusEquiv R p n).symm.map_eq_zero_iff

@[simp]
theorem teichmullerCoord_zero (n : ℕ) : teichmullerCoord (0 : 𝕎 R) n = 0 := by
  simp [teichmullerCoord]

@[simp]
theorem teichmullerCoord_one_zero : teichmullerCoord (1 : 𝕎 R) 0 = 1 := by
  simp [teichmullerCoord]

theorem teichmullerCoord_one_of_pos {n : ℕ} (hn : 0 < n) : teichmullerCoord (1 : 𝕎 R) n = 0 := by
  simp [teichmullerCoord, hn]

/-- The Teichmüller representative `[r]` has `0`-th Teichmüller coordinate `r`. -/
@[simp]
theorem teichmullerCoord_teichmuller_zero (r : R) : teichmullerCoord (teichmuller p r) 0 = r := by
  simp [teichmullerCoord]

/-- The Teichmüller representative `[r]` has no positive Teichmüller coordinates. -/
theorem teichmullerCoord_teichmuller_of_pos (r : R) {n : ℕ} (hn : 0 < n) :
    teichmullerCoord (teichmuller p r) n = 0 := by
  simp [teichmullerCoord, teichmuller_coeff_pos p r n hn]

/-- The Teichmüller expansion: `x ≡ ∑_{i ≤ n} [x_i] p ^ i (mod p ^ (n + 1))`. -/
theorem pow_succ_dvd_sub_sum_teichmuller_teichmullerCoord (x : 𝕎 R) (n : ℕ) :
    (p : 𝕎 R) ^ (n + 1) ∣ x - ∑ i ∈ Iic n, teichmuller p (teichmullerCoord x i) * p ^ i := by
  simpa only [teichmullerCoord, iterateFrobeniusEquiv_symm] using
    dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n

/-- Two Witt vectors congruent modulo `p ^ (N + 1)` have the same `N`-th component. -/
theorem coeff_eq_of_pow_succ_dvd_sub {x y : 𝕎 R} {N : ℕ} (h : (p : 𝕎 R) ^ (N + 1) ∣ x - y) :
    x.coeff N = y.coeff N :=
  le_coeff_eq_iff_le_sub_coeff_eq_zero.mpr
    ((mem_span_p_pow_iff_le_coeff_eq_zero (x - y) (N + 1)).mp (Ideal.mem_span_singleton.mpr h))
    N (Nat.lt_succ_self N)

/-- Two Witt vectors congruent modulo `p ^ (N + 1)` have the same `N`-th Teichmüller coordinate. -/
theorem teichmullerCoord_eq_of_pow_succ_dvd_sub {x y : 𝕎 R} {N : ℕ}
    (h : (p : 𝕎 R) ^ (N + 1) ∣ x - y) : teichmullerCoord x N = teichmullerCoord y N := by
  rw [teichmullerCoord, teichmullerCoord, coeff_eq_of_pow_succ_dvd_sub h]

/-- Multiplication by `p ^ k` shifts the Teichmüller coordinates up by `k`. -/
theorem teichmullerCoord_mul_pow (x : 𝕎 R) (k n : ℕ) :
    teichmullerCoord (x * (p : 𝕎 R) ^ k) (n + k) = teichmullerCoord x n := by
  rw [teichmullerCoord, teichmullerCoord, mul_pow_charP_coeff_succ,
    iterateFrobeniusEquiv_symm_add_apply, ← iterateFrobeniusEquiv_def R p k,
    RingEquiv.symm_apply_apply]

/-- A multiple of `p ^ k` has no Teichmüller coordinates below `k`. -/
theorem teichmullerCoord_mul_pow_of_lt (x : 𝕎 R) {m k : ℕ} (h : m < k) :
    teichmullerCoord (x * (p : 𝕎 R) ^ k) m = 0 := by
  rw [teichmullerCoord, mul_pow_charP_coeff_zero x h, map_zero]

/-- The Teichmüller coordinates of a Teichmüller series `∑ [f i] p ^ i` are the `f i`. -/
theorem teichmullerCoord_sum_teichmuller_mul_pow (f : ℕ → R) (s : Finset ℕ) (n : ℕ) :
    teichmullerCoord (∑ i ∈ s, teichmuller p (f i) * (p : 𝕎 R) ^ i) n =
      if n ∈ s then f n else 0 := by
  rw [teichmullerCoord, coeff_sum_teichmuller_mul_pow]
  split_ifs
  · rw [← iterateFrobeniusEquiv_def R p n, RingEquiv.symm_apply_apply]
  · exact map_zero _

/-- The `k`-th Teichmüller coordinate of `[r] p ^ k` is `r`. -/
@[simp]
theorem teichmullerCoord_teichmuller_mul_pow (r : R) (k : ℕ) :
    teichmullerCoord (teichmuller p r * (p : 𝕎 R) ^ k) k = r := by
  simpa using teichmullerCoord_sum_teichmuller_mul_pow (fun _ ↦ r) {k} k

/-- The term `[r] p ^ k` has no Teichmüller coordinate besides the `k`-th. -/
theorem teichmullerCoord_teichmuller_mul_pow_of_ne (r : R) {m k : ℕ} (h : m ≠ k) :
    teichmullerCoord (teichmuller p r * (p : 𝕎 R) ^ k) m = 0 := by
  simpa [h] using teichmullerCoord_sum_teichmuller_mul_pow (fun _ ↦ r) {k} m

/-- **No carry into the `N`-th component from a multiple of `p ^ N`.** If `p ^ N ∣ u`, then the
`N`-th component of `u + z` is the sum of the `N`-th components: the carries of Witt-vector
addition into the `N`-th component come from the components below `N`, which vanish for `u`. -/
theorem coeff_add_of_pow_dvd {u z : 𝕎 R} {N : ℕ} (hu : (p : 𝕎 R) ^ N ∣ u) :
    (u + z).coeff N = u.coeff N + z.coeff N := by
  obtain ⟨w, rfl⟩ := hu
  cases N with
  | zero => exact add_coeff_zero _ _
  | succ M =>
    -- Split `z` into its Teichmüller expansion below `p ^ (M + 1)` and a multiple of `p ^ (M + 1)`,
    -- whose supports are disjoint from each other and from that of `p ^ (M + 1) * w`.
    set z' := ∑ i ∈ Iic M, teichmuller p (teichmullerCoord z i) * p ^ i with hz'
    obtain ⟨c, hc⟩ := pow_succ_dvd_sub_sum_teichmuller_teichmullerCoord z M
    have hz : z = p ^ (M + 1) * c + z' := by rw [← hc, sub_add_cancel]
    have hdisj (y : 𝕎 R) (n : ℕ) : ((p : 𝕎 R) ^ (M + 1) * y).coeff n = 0 ∨ z'.coeff n = 0 := by
      rcases lt_or_ge n (M + 1) with h | h
      · exact Or.inl (by rw [mul_comm]; exact mul_pow_charP_coeff_zero y h)
      · exact Or.inr (by rw [hz', coeff_sum_teichmuller_mul_pow, ite_eq_right (by simpa using h)])
    have hcoeff (y : 𝕎 R) :
        ((p : 𝕎 R) ^ (M + 1) * y).coeff (M + 1) = y.coeff 0 ^ p ^ (M + 1) := by
      rw [mul_comm]; simpa using mul_pow_charP_coeff_succ y (m := 0) (n := M + 1)
    rw [hz, ← add_assoc, ← mul_add, coeff_add_of_disjoint _ _ _ (hdisj _),
      coeff_add_of_disjoint _ _ _ (hdisj _), hcoeff, hcoeff, hcoeff, add_coeff_zero,
      add_pow_char_pow, add_assoc]

/-- **No carry into the `N`-th Teichmüller coordinate from a multiple of `p ^ N`.** -/
theorem teichmullerCoord_add_of_pow_dvd {u z : 𝕎 R} {N : ℕ} (hu : (p : 𝕎 R) ^ N ∣ u) :
    teichmullerCoord (u + z) N = teichmullerCoord u N + teichmullerCoord z N := by
  rw [teichmullerCoord, coeff_add_of_pow_dvd hu, map_add, teichmullerCoord, teichmullerCoord]

end TauCeti.WittVector

end
