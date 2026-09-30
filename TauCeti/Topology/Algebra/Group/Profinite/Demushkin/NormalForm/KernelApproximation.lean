/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.GradedFunctional
public import TauCeti.Topology.Algebra.Group.Profinite.Free.SuccessiveApproximation.Basic

/-!
# Successive approximation inside the kernel of the orientation

Let `F = freeProP p (Fin n)` with `n` even, let `w = x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` be
the normal-form word `TauCeti.demushkinWordNeTwo q n` with `p ∣ q`, and let `χ : F → ℤ_pˣ` be a
continuous character with the values of the orientation of this normal form, `χ(x₂) (1 - q) = 1`
and `χ(x_i) = 1` for `i ≠ 2`. Let `X` be the kernel of the exponent sum at `x₂`, so that
`X ≤ ker χ`, and `X = ker χ` when `χ(x₂)` has infinite order
(`ContinuousMonoidHom.exponentSumKer_eq_ker`, in
`TauCeti.Topology.Algebra.Group.Profinite.Free.ExponentSumKernel`).

Labute's proof of his Theorem 5 approximates a relator `r ≡ w mod λ_2(F)` by `w` through basis
modifications `x_i ↦ x_i w_i` with `w_i ∈ X`, which do not change the values of `χ` on the
generators. The deviation `(φ w)⁻¹ * r` after any such modification `φ` lies in `X` and is killed
by every continuous crossed homomorphism `D : F → ℤ_p` for `χ`, provided `r` is: `D (φ w) = 0`
because the word is killed at the tabulated character values
(`TauCeti.IsCrossedHom.map_demushkinWordNeTwo_eq_zero`). Labute's Lemma 4
(`TauCeti.freeProP.mem_map_basisModificationDelta_iff_forall_gradedFunctional_crossedHom_eq_zero`)
then writes the class of such a deviation in `gr_{m+1}(X)` as `δ_ρ(ω)` with `ω ∈ gr_m(X)^n`, so
the constrained successive-approximation theorem
`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq` applies with `Z` the set of elements of
`X` killed by the Kronecker crossed homomorphisms and `C i = X`: an automorphism of `F` moving
each generator inside `X` carries `w` to `r`, which is
`TauCeti.freeProP.exists_continuousMulEquiv_apply_demushkinWordNeTwo_eq_of_isCrossedHom_eq_zero`.

The second half of the file reads the character values modulo `p²` off the relator. If every
continuous crossed homomorphism for a character `χ` kills a relator `r ≡ w mod λ_2(F)`, then
`χ(x_i) ≡ 1 mod p²` for every `i ≠ 2`
(`TauCeti.freeProP.apply_of_mem_unitsPrincipal_two_of_isCrossedHom_eq_zero`): the
Kronecker crossed homomorphism `D_k` with `D_k(x_j) = δ_{kj}` takes on `r` the value
`D_k(w) mod p²`, and on the commutator factor `(x_k, x_{k'})` of `w` containing `x_k` it reads off
`χ(x_{k'}) - 1`. This is what pins the values of the canonical character of a Demushkin group to
the coset of the normal form, before the exact values are arranged by a basis modification.

## Main results

* `TauCeti.IsCrossedHom.map_apply_demushkinWordNeTwo_eq_zero`: a crossed homomorphism for `χ`
  kills the image of the normal-form word under an endomorphism preserving `χ`.
* `TauCeti.freeProP.apply_of_mem_unitsPrincipal_two_of_isCrossedHom_eq_zero`: a
  character all of whose crossed homomorphisms kill a relator in the class of the normal form
  takes the generators `x_i`, `i ≠ 2`, into `1 + p²ℤ_p`.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_demushkinWordNeTwo_eq_of_isCrossedHom_eq_zero`:
  **the successive approximation inside `X`**: a relator `r ∈ X` in the class of the normal form,
  killed by every continuous crossed homomorphism for `χ`, is the image of the normal-form word
  under a continuous automorphism of `F` moving each generator inside `X`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  proof of Theorem 5.
-/

public section

namespace TauCeti

open Subgroup

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {n q : ℕ} {χ : freeProP p (Fin n) →ₜ* ℤ_[p]ˣ}

/-! ### The Kronecker crossed homomorphisms on the normal-form word -/

/-- **A crossed homomorphism for the orientation kills the image of the normal-form word under an
endomorphism preserving the character**: the word on the tuple `(φ x_i)` is killed at the same
character values. -/
theorem _root_.TauCeti.IsCrossedHom.map_apply_demushkinWordNeTwo_eq_zero (hn1 : 1 < n)
    (h₁ : (χ (of ⟨1, hn1⟩) : ℤ_[p]) * (1 - q) = 1) (h : ∀ j, j ≠ ⟨1, hn1⟩ → χ (of j) = 1)
    {f : freeProP p (Fin n) → ℤ_[p]} (hf : IsCrossedHom χ f)
    (φ : freeProP p (Fin n) →ₜ* freeProP p (Fin n)) (hφ : ∀ g, χ (φ g) = χ g) :
    f (φ (demushkinWordNeTwo q n (freeProPGen p n))) = 0 := by
  rw [TauCeti.map_demushkinWordNeTwo]
  refine hf.map_demushkinWordNeTwo_eq_zero hn1 ?_ fun i hi ↦ ?_
  · rw [Function.comp_apply, hφ, freeProPGen_of_lt p hn1]
    exact h₁
  · rw [Function.comp_apply, hφ]
    by_cases hi' : i < n
    · rw [freeProPGen_of_lt p hi']
      exact h _ fun e ↦ hi (congrArg Fin.val e)
    · rw [freeProPGen_eq_one_of_le p (not_lt.1 hi'), _root_.map_one]

/-- The normal-form word lies in the kernel of the exponent sum at `x₂`. -/
theorem demushkinWordNeTwo_freeProPGen_mem_exponentSumKer (hn1 : 1 < n) (q : ℕ) :
    demushkinWordNeTwo q n (freeProPGen p n) ∈ exponentSumKer p (Fin n) ⟨1, hn1⟩ := by
  refine demushkinWordNeTwo_mem q n (pow_mem ?_ q) fun i hi ↦ ?_
  · rw [freeProPGen_of_lt p (by omega)]
    exact of_mem_exponentSumKer fun e ↦ absurd (congrArg Fin.val e) (by simp)
  · rw [freeProPGen_of_lt p (by omega)]
    exact of_mem_exponentSumKer fun e ↦ absurd (congrArg Fin.val e) (by simp)

/-! ### The character values modulo `p²` -/

/-- For a relator `r ≡ w mod λ_2(F)` killed by the Kronecker crossed homomorphism `D_k` with
`k ≠ 1`, `p²` divides the sum of the values of `D_k` on the commutator factors of `w`: `D_k` is
divisible by `p²` on `λ_2(F)`, so `p² ∣ D_k(w)`, and the power factor `x₁^q` contributes
nothing since `D_k(x₁) = 0`. -/
private theorem pow_two_dvd_sum_crossedHom_labuteComm (hq : p ∣ q)
    (r : pLowerCentralSeries p (freeProP p (Fin n)) 1)
    (hr : gradedMk p (freeProP p (Fin n)) 1 r = gradedMk p (freeProP p (Fin n)) 1
      ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)
    {k : Fin n} (hk : (k : ℕ) ≠ 0) (hD : crossedHom χ (Pi.single k 1) r = 0) :
    (p : ℤ_[p]) ^ 2 ∣ ∑ a ∈ Finset.range (n / 2), crossedHom χ (Pi.single k 1)
      (labuteComm (freeProPGen p n (2 * a)) (freeProPGen p n (2 * a + 1))) := by
  have hD' : IsCrossedHom χ (crossedHom χ (Pi.single k 1)) := isCrossedHom_crossedHom χ _
  -- The relator is `w * z` with `z ∈ λ_2(F)`, on which `D_k` is divisible by `p²`.
  have hz : (demushkinWordNeTwo q n (freeProPGen p n))⁻¹ * (r : freeProP p (Fin n)) ∈
      pLowerCentralSeries p (freeProP p (Fin n)) 2 := by
    rw [gradedMk_eq_gradedMk_iff] at hr
    exact QuotientGroup.eq.1 hr.symm
  have hDw : (p : ℤ_[p]) ^ 2 ∣ crossedHom χ (Pi.single k 1)
      (demushkinWordNeTwo q n (freeProPGen p n)) := by
    have h1 : crossedHom χ (Pi.single k 1) (demushkinWordNeTwo q n (freeProPGen p n)) +
        (χ (demushkinWordNeTwo q n (freeProPGen p n)) : ℤ_[p]) *
          crossedHom χ (Pi.single k 1)
            ((demushkinWordNeTwo q n (freeProPGen p n))⁻¹ * (r : freeProP p (Fin n))) =
          crossedHom χ (Pi.single k 1) r := by
      conv_rhs => rw [← mul_inv_cancel_left (demushkinWordNeTwo q n (freeProPGen p n))
        (r : freeProP p (Fin n)), hD'.map_mul]
      exact add_comm _ _
    rw [hD] at h1
    rw [eq_neg_of_add_eq_zero_left h1]
    exact (dvd_mul_of_dvd_right (hD'.pow_dvd_apply_of_mem_pLowerCentralSeries
      ((isProP_freeProP p (Fin n)).mem_unitsPrincipal_one χ) (continuous_crossedHom χ _) hz)
        _).neg_right
  rw [hD'.map_demushkinWordNeTwo, crossedHom_single_freeProPGen, ite_eq_right fun h ↦ hk h.symm,
    mul_zero, add_zero, ← Units.val_pow_eq_pow_val, Units.dvd_mul_left] at hDw
  exact hDw

/-- **The character values forced by the relator, modulo `p²`** (Labute, proof of Theorem 5).
Let `n` be even, `p ∣ q`, and let `r ∈ λ_1(F)` be a relator in the class of
`w = x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` modulo `λ_2(F)`. If every continuous crossed homomorphism
`F → ℤ_p` for a continuous character `χ` kills `r`, then `χ(x_j) ∈ 1 + p²ℤ_p` for every
`j ≠ 2`: the Kronecker crossed homomorphism `D_k` at the partner `x_k` of `x_j` in the commutator
factor `(x_j, x_k)` or `(x_k, x_j)` of `w` takes on `r` the value `D_k(w) ≡ ±(χ(x_j) - 1)` modulo
`p²`. -/
theorem apply_of_mem_unitsPrincipal_two_of_isCrossedHom_eq_zero (hn : Even n)
    (hn1 : 1 < n) (hq : p ∣ q) (r : pLowerCentralSeries p (freeProP p (Fin n)) 1)
    (hr : gradedMk p (freeProP p (Fin n)) 1 r = gradedMk p (freeProP p (Fin n)) 1
      ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)
    (hD : ∀ D : freeProP p (Fin n) → ℤ_[p], Continuous D → IsCrossedHom χ D → D r = 0)
    {j : Fin n} (hj : j ≠ ⟨1, hn1⟩) : χ (of j) ∈ unitsPrincipal p 2 := by
  obtain ⟨N, hN⟩ := hn
  -- `p²` divides `D_k` on the commutator factor containing `x_k`, for `k ≠ 1`.
  have key : ∀ (k : Fin n) (a : ℕ), (k : ℕ) ≠ 0 → 2 * a + 1 < n →
      ((k : ℕ) = 2 * a ∨ (k : ℕ) = 2 * a + 1) →
      (p : ℤ_[p]) ^ 2 ∣ crossedHom χ (Pi.single k 1)
        (labuteComm (freeProPGen p n (2 * a)) (freeProPGen p n (2 * a + 1))) := by
    intro k a hk ha hka
    have h := pow_two_dvd_sum_crossedHom_labuteComm hq r hr hk
      (hD _ (continuous_crossedHom χ _) (isCrossedHom_crossedHom χ _))
    rwa [Finset.sum_eq_single a (fun b _ hb ↦
      (isCrossedHom_crossedHom χ _).map_labuteComm_eq_zero_of_eq_zero
        (by rw [crossedHom_single_freeProPGen, ite_eq_right]; omega)
        (by rw [crossedHom_single_freeProPGen, ite_eq_right]; omega))
      fun ha' ↦ absurd (Finset.mem_range.2 (by omega)) ha'] at h
  rw [mem_unitsPrincipal_iff]
  obtain ⟨a, ha | ha⟩ := Nat.even_or_odd' (j : ℕ)
  · -- `x_j = x_{2a}`, with partner `x_{2a+1}`.
    have hlt : 2 * a + 1 < n := by omega
    have h := key ⟨2 * a + 1, hlt⟩ a (by simp) hlt (Or.inr rfl)
    have hid := IsCrossedHom.mul_mul_map_labuteComm
      (isCrossedHom_crossedHom χ (Pi.single (⟨2 * a + 1, hlt⟩ : Fin n) 1))
      (freeProPGen p n (2 * a)) (freeProPGen p n (2 * a + 1))
    rw [crossedHom_single_freeProPGen, crossedHom_single_freeProPGen, ite_eq_right (by simp),
      ite_eq_left rfl] at hid
    have hj' : of j = freeProPGen p n (2 * a) := by
      rw [freeProPGen_of_lt p (by omega)]
      exact congrArg of (Fin.ext ha)
    rw [hj', show (χ (freeProPGen p n (2 * a)) : ℤ_[p]) - 1 =
      (χ (freeProPGen p n (2 * a)) : ℤ_[p]) * χ (freeProPGen p n (2 * a + 1)) *
        crossedHom χ (Pi.single (⟨2 * a + 1, hlt⟩ : Fin n) 1)
          (labuteComm (freeProPGen p n (2 * a)) (freeProPGen p n (2 * a + 1))) by
      linear_combination -hid]
    exact h.mul_left _
  · -- `x_j = x_{2a+1}` with `a ≥ 1`, with partner `x_{2a}`.
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hj (Fin.ext (by simpa using ha))
    have hlt : 2 * a + 1 < n := by omega
    have h := key ⟨2 * a, by omega⟩ a (by simpa using ha0) hlt (Or.inl rfl)
    have hid := IsCrossedHom.mul_mul_map_labuteComm
      (isCrossedHom_crossedHom χ (Pi.single (⟨2 * a, by omega⟩ : Fin n) 1))
      (freeProPGen p n (2 * a)) (freeProPGen p n (2 * a + 1))
    rw [crossedHom_single_freeProPGen, crossedHom_single_freeProPGen, ite_eq_left rfl,
      ite_eq_right (by simp)] at hid
    have hj' : of j = freeProPGen p n (2 * a + 1) := by
      rw [freeProPGen_of_lt p hlt]
      exact congrArg of (Fin.ext ha)
    rw [hj', show (χ (freeProPGen p n (2 * a + 1)) : ℤ_[p]) - 1 =
      -((χ (freeProPGen p n (2 * a)) : ℤ_[p]) * χ (freeProPGen p n (2 * a + 1)) *
        crossedHom χ (Pi.single (⟨2 * a, by omega⟩ : Fin n) 1)
          (labuteComm (freeProPGen p n (2 * a)) (freeProPGen p n (2 * a + 1)))) by
      linear_combination hid]
    exact (h.mul_left _).neg_right

/-! ### The successive approximation inside `X` -/

/-- **The successive approximation inside the kernel of the orientation** (Labute, proof of
Theorem 5). Let `n` be even, `p ∣ q`, `w = x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`, and let
`χ : F → ℤ_pˣ` be a continuous character with `χ(x₂) (1 - q) = 1` and `χ(x_i) = 1` for `i ≠ 2`.
Let `r ∈ λ_1(F)` be a relator in the class of `w` modulo `λ_2(F)`, lying in the kernel `X` of
the exponent sum at `x₂`, and killed by every continuous crossed homomorphism `F → ℤ_p` for `χ`.
Then a continuous automorphism of `F` moving every generator inside `X` carries `w` to `r`.

The deviations `(φ w)⁻¹ * r` of the approximations lie in `X` and are killed by the Kronecker
crossed homomorphisms `D_i`, `i ≠ 2`, and Labute's Lemma 4 writes their classes as `δ_ρ(ω)` with
`ω ∈ gr_m(X)^n`, which is the constrained span statement of
`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq`. -/
theorem exists_continuousMulEquiv_apply_demushkinWordNeTwo_eq_of_isCrossedHom_eq_zero
    (hn : Even n) (hn1 : 1 < n) (hq : p ∣ q)
    (h₁ : (χ (of ⟨1, hn1⟩) : ℤ_[p]) * (1 - q) = 1) (h : ∀ j, j ≠ ⟨1, hn1⟩ → χ (of j) = 1)
    (r : pLowerCentralSeries p (freeProP p (Fin n)) 1)
    (hr : gradedMk p (freeProP p (Fin n)) 1 r = gradedMk p (freeProP p (Fin n)) 1
      ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)
    (hrX : (r : freeProP p (Fin n)) ∈ exponentSumKer p (Fin n) ⟨1, hn1⟩)
    (hD : ∀ D : freeProP p (Fin n) → ℤ_[p], Continuous D → IsCrossedHom χ D → D r = 0) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      (∀ i, (of i)⁻¹ * e (of i) ∈ exponentSumKer p (Fin n) ⟨1, hn1⟩) ∧
        e (demushkinWordNeTwo q n (freeProPGen p n)) = r := by
  have hXker : exponentSumKer p (Fin n) ⟨1, hn1⟩ ≤ χ.toMonoidHom.ker := χ.exponentSumKer_le_ker h
  refine exists_continuousMulEquiv_apply_eq
    {g | g ∈ exponentSumKer p (Fin n) ⟨1, hn1⟩ ∧
      ∀ i, i ≠ ⟨1, hn1⟩ → crossedHom χ (Pi.single i 1) g = 0}
    (fun _ ↦ exponentSumKer p (Fin n) ⟨1, hn1⟩) (fun _ ↦ isClosed_exponentSumKer _) ?_
    ⟨_, demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩ r hr.symm ?_ ?_
  · -- Stability: a basis modification by elements of `X` preserves `X`.
    intro ω hω i c hc
    exact (apply_mem_exponentSumKer_iff_of_forall_inv_mul_apply_mem (basisModification ω)
      (fun j ↦ by rw [basisModification_of, inv_mul_cancel_left]; exact hω j) c).2 hc
  · -- The invariant: the deviation lies in `X` and is killed by every `D_i`.
    intro φ _ hφ
    have hχφ : ∀ g, χ (φ g) = χ g := fun g ↦ by
      have := DFunLike.congr_fun
        (χ.comp_eq_of_forall_inv_mul_apply_mem_ker φ fun j ↦ hXker (hφ j)) g
      rwa [ContinuousMonoidHom.coe_comp, Function.comp_apply] at this
    refine ⟨mul_mem (inv_mem ((apply_mem_exponentSumKer_iff_of_forall_inv_mul_apply_mem φ hφ _).2
      (demushkinWordNeTwo_freeProPGen_mem_exponentSumKer hn1 q))) hrX, fun i _ ↦ ?_⟩
    have hDi : IsCrossedHom χ (crossedHom χ (Pi.single i 1)) := isCrossedHom_crossedHom χ _
    rw [hDi.map_mul, hD _ (continuous_crossedHom χ _) hDi, mul_zero, zero_add, hDi.map_inv,
      hDi.map_apply_demushkinWordNeTwo_eq_zero hn1 h₁ h φ hχφ, mul_zero]
  · -- The constrained span statement: Labute's Lemma 4.
    intro m hm z hz
    obtain ⟨hzX, hzD⟩ := hz
    have hε : gradedMk p (freeProP p (Fin n)) (m + 1) z ∈
        gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) (m + 1) :=
      mem_gradedPieceOf_iff.2 ⟨z, hzX, rfl⟩
    have hmem := (mem_map_basisModificationDelta_iff_forall_gradedFunctional_crossedHom_eq_zero hn
      hn1 hq hm h₁ h hε).2 fun i hi ↦ by
        rw [IsCrossedHom.gradedFunctional_gradedMk_eq_zero_iff, hzD i hi]
        exact dvd_zero _
    obtain ⟨v, hv, hvz⟩ := Submodule.mem_map.1 hmem
    choose ω hωX hωv using fun i ↦
      mem_gradedPieceOf_iff.1 (Submodule.mem_pi.1 hv i (Set.mem_univ i))
    refine ⟨ω, hωX, ?_⟩
    rw [← hvz]
    congr 1
    exact funext hωv

end freeProP

end TauCeti
