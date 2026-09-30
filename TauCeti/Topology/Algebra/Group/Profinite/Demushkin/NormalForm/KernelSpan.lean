/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ExponentSumKernel

/-!
# The constrained span statement at the normal form `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)`

Let `F = freeProP p (Fin n)` with `n` even, let `r = x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` with
`p ∣ q` be the alternating normal-form word, and let `ρ ∈ gr_1(F)` be its class. The partial
derivatives of `ρ` are `∂_{2a+1} ρ = -ξ_{2a}` and `∂_{2a} ρ = ξ_{2a+1}` for `a ≥ 1`, while
`∂_0 ρ = (p choose 2)(q / p) ξ₁ + ξ₂`
(`TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd`,
`TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_even`). So the derivatives at the
generators other than `x₁` span exactly the classes `ξ_j` with `j ≠ 2`, which is the hypothesis of
the constrained span statement of `Free/ExponentSumKernel.lean`, with `i₀ = x₁` and `i₁ = x₂`. The
conclusion is Labute's Lemma 3: for the kernel `X` of the exponent sum at `x₂` and every `m ≥ 1`,

  `gr_{m+1}(X) = δ_ρ(gr_m(X)^n) + T_{m+1}`,

where `T_{m+1}` is spanned by the `π^{m+1} ξ_j` with `j ≠ 2`. This is the span statement that the
uniqueness argument for the dyadic even-rank Demushkin groups with orientation image `U^[f]` runs
on: the relator `x₁^{2+2^f} (x₁, x₂)(x₃, x₄) ⋯` is this word at `p = 2` and `q = 2 + 2^f`, the
orientation is the exponent sum at `x₂` composed with `γ ↦ χ(x₂)^γ`, and the basis corrections must
be taken inside its kernel.

## Main results

* `TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd`,
  `TauCeti.freeProP.degreeOneDeriv_gradedMk_demushkinWordNeTwo_even`: the partial derivatives of
  the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` at the generators other than `x₁`.
* `gradedPieceOf_exponentSumKer_demushkinWordNeTwo_eq_map_basisModificationDelta_sup` (in
  `TauCeti.freeProP`): the constrained span statement at this normal form.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Lemmas 1–3 and the proof of Theorem 5.
-/

public section

namespace TauCeti

open Subgroup Submodule

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

omit [Fact p.Prime] in
/-- The class of the `ℕ`-indexed generator `x_j` of `freeProP p (Fin n)`, for `j < n`. -/
private theorem gradedMkZero_freeProPGen_eq (j : ℕ) (hj : j < n) :
    gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n j) =
      gradedMkZero p (freeProP p (Fin n)) (of ⟨j, hj⟩) := by
  rw [freeProPGen_of_lt p hj]

/-- The derivative `∂_k` of the class of the commutator part `(x₁, x₂) ⋯ (x_{n-1}, x_n)` at a
bracket `[ξ_{2b}, ξ_{2b+1}]` whose two indices differ from `k`. -/
private theorem degreeOneDeriv_gradedBracket_freeProPGen_of_ne (k : Fin n) {b : ℕ}
    (hb : 2 * b + 1 < n) (h₁ : (k : ℕ) ≠ 2 * b) (h₂ : (k : ℕ) ≠ 2 * b + 1) :
    degreeOneDeriv p (Fin n) k (gradedBracket p (freeProP p (Fin n)) 0 0
      (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * b)))
      (gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * b + 1)))) = 0 := by
  rw [gradedMkZero_freeProPGen_eq _ (by omega), gradedMkZero_freeProPGen_eq _ hb]
  exact degreeOneDeriv_gradedBracket_gradedMkZero_of_of_ne (Fin.mk_lt_mk.2 (Nat.lt_succ_self _))
    (fun h ↦ h₁ (congrArg Fin.val h).symm) fun h ↦ h₂ (congrArg Fin.val h).symm

/-- **The derivative of the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` at an even-indexed generator**
`x_{2a+1}` (the generator `x_{2a}` in `0`-based indexing) for `a ≥ 1`: `∂_{2a} ρ = ξ_{2a+1}`. -/
theorem degreeOneDeriv_gradedMk_demushkinWordNeTwo_even {q : ℕ} (hq : p ∣ q) {a : ℕ} (ha₀ : 0 < a)
    (ha : 2 * a + 1 < n) :
    degreeOneDeriv p (Fin n) ⟨2 * a, by omega⟩ (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * a + 1)) := by
  rw [gradedMk_demushkinWordNeTwo hq, map_add, map_nsmul, map_sum,
    gradedMkZero_freeProPGen_eq 0 (by omega),
    degreeOneDeriv_gradedPow_gradedMkZero_of_of_ne (fun h ↦ by
      have := congrArg Fin.val h
      simp only at this
      omega),
    nsmul_zero, zero_add,
    Finset.sum_eq_single a (fun b hb hba ↦ degreeOneDeriv_gradedBracket_freeProPGen_of_ne _
      (by rw [Finset.mem_range] at hb; omega) (by simp only; omega)
      (by simp only; omega))
      (fun h ↦ (h (Finset.mem_range.2 (by omega))).elim),
    gradedMkZero_freeProPGen_eq _ (by omega), gradedMkZero_freeProPGen_eq _ ha,
    degreeOneDeriv_gradedBracket_gradedMkZero_of_left (Fin.mk_lt_mk.2 (Nat.lt_succ_self _))]

/-- **The derivative of the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` at an odd-indexed generator**
`x_{2a+2}` (the generator `x_{2a+1}` in `0`-based indexing): `∂_{2a+1} ρ = -ξ_{2a}`. -/
theorem degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd {q : ℕ} (hq : p ∣ q) {a : ℕ}
    (ha : 2 * a + 1 < n) :
    degreeOneDeriv p (Fin n) ⟨2 * a + 1, ha⟩ (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      -gradedMkZero p (freeProP p (Fin n)) (freeProPGen p n (2 * a)) := by
  rw [gradedMk_demushkinWordNeTwo hq, map_add, map_nsmul, map_sum,
    gradedMkZero_freeProPGen_eq 0 (by omega),
    degreeOneDeriv_gradedPow_gradedMkZero_of_of_ne (fun h ↦ by
      have := congrArg Fin.val h
      simp only at this
      omega),
    nsmul_zero, zero_add,
    Finset.sum_eq_single a (fun b hb hba ↦ degreeOneDeriv_gradedBracket_freeProPGen_of_ne _
      (by rw [Finset.mem_range] at hb; omega) (by simp only; omega)
      (by simp only; omega))
      (fun h ↦ (h (Finset.mem_range.2 (by omega))).elim),
    gradedMkZero_freeProPGen_eq _ (by omega), gradedMkZero_freeProPGen_eq _ ha,
    degreeOneDeriv_gradedBracket_gradedMkZero_of_right (Fin.mk_lt_mk.2 (Nat.lt_succ_self _))]

/-- **Every generator class other than `ξ₂` is a combination of the derivatives at the generators
other than `x₁`**, for the class of `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)` with `n` even. -/
theorem exists_sum_smul_degreeOneDeriv_gradedMk_demushkinWordNeTwo_eq (hn : Even n) {q : ℕ}
    (hq : p ∣ q) (hn1 : 1 < n) (j : Fin n) (hj : j ≠ ⟨1, hn1⟩) :
    ∃ b : Fin n → ZMod p, b ⟨0, by omega⟩ = 0 ∧
      ∑ k, b k • degreeOneDeriv p (Fin n) k (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
        gradedMkZero p (freeProP p (Fin n)) (of j) := by
  classical
  obtain ⟨N, hN⟩ := hn
  have hj' : (j : ℕ) ≠ 1 := fun h ↦ hj (Fin.ext h)
  -- A single derivative, up to sign, gives `ξ_j`.
  have key (k : Fin n) (c : ZMod p) (hk : k ≠ ⟨0, by omega⟩)
      (h : c • degreeOneDeriv p (Fin n) k (gradedMk p (freeProP p (Fin n)) 1
        ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
        gradedMkZero p (freeProP p (Fin n)) (of j)) :
      ∃ b : Fin n → ZMod p, b ⟨0, by omega⟩ = 0 ∧
        ∑ k, b k • degreeOneDeriv p (Fin n) k (gradedMk p (freeProP p (Fin n)) 1
          ⟨demushkinWordNeTwo q n (freeProPGen p n),
            demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
          gradedMkZero p (freeProP p (Fin n)) (of j) :=
    ⟨Pi.single k c, Pi.single_eq_of_ne (Ne.symm hk) _, by
      simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, h]⟩
  rcases Nat.even_or_odd (j : ℕ) with ⟨a, ha⟩ | ⟨a, ha⟩
  · -- `ξ_{2a} = -∂_{2a+1} ρ`.
    have ha' : 2 * a + 1 < n := by omega
    refine key ⟨2 * a + 1, ha'⟩ ((-1 : ℤ) : ZMod p) (fun h ↦ by simp [Fin.ext_iff] at h) ?_
    rw [degreeOneDeriv_gradedMk_demushkinWordNeTwo_odd hq ha', Int.cast_smul_eq_zsmul,
      neg_one_zsmul, neg_neg, gradedMkZero_freeProPGen_eq _ (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  · -- `ξ_{2a+1} = ∂_{2a} ρ`, where `a ≥ 1` since `j ≠ 1`.
    have ha₀ : 0 < a := by omega
    have ha' : 2 * a + 1 < n := by omega
    refine key ⟨2 * a, by omega⟩ 1 (fun h ↦ by simp [Fin.ext_iff] at h; omega) ?_
    rw [degreeOneDeriv_gradedMk_demushkinWordNeTwo_even hq ha₀ ha', one_smul,
      gradedMkZero_freeProPGen_eq _ ha']
    congr 2
    exact Fin.ext (by simp only; omega)

/-- **The constrained span statement at the normal form `x₁^q (x₁, x₂) ⋯ (x_{n-1}, x_n)`**
(Labute, §4, Lemma 3). For `n` even, `p ∣ q`, the class `ρ` of the word, `X` the kernel of the
exponent sum at `x₂` and every `m ≥ 1`,

  `gr_{m+1}(X) = δ_ρ(gr_m(X)^n) + T_{m+1}`,

where the tail `T_{m+1}` is spanned by the `p`-powers `π^{m+1} ξ_j` with `j ≠ 2`. At `p = 2` and
`q = 2 + 2^f` this is the span statement for the relators `x₁^{2+2^f} (x₁, x₂)(x₃, x₄) ⋯` whose
basis corrections must respect the orientation. -/
theorem gradedPieceOf_exponentSumKer_demushkinWordNeTwo_eq_map_basisModificationDelta_sup
    (hn : Even n) (hn1 : 1 < n) {q : ℕ} (hq : p ∣ q) {m : ℕ} (hm : 1 ≤ m) :
    gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) (m + 1) =
      (Submodule.pi Set.univ
          fun _ : Fin n ↦ gradedPieceOf p (exponentSumKer p (Fin n) ⟨1, hn1⟩) m).map
        (basisModificationDelta p (Fin n) hm (gradedMk p (freeProP p (Fin n)) 1
          ⟨demushkinWordNeTwo q n (freeProPGen p n),
            demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩)) ⊔
      span (ZMod p) (Set.range fun a : {a : Fin n // a ≠ ⟨1, hn1⟩} ↦
        gradedPowIter p (freeProP p (Fin n)) (m + 1)
          (gradedMkZero p (freeProP p (Fin n)) (of a))) :=
  gradedPieceOf_exponentSumKer_eq_map_basisModificationDelta_sup_span_gradedPowIter hm
    ((span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm _).2
      (nondegenerate_degreeOneForm_demushkinWordNeTwo hn hq))
    (i₀ := ⟨0, by omega⟩) (fun k hk ↦ by
      rw [degreeOneBasis_repr_gradedMk_demushkinWordNeTwo_inl hq k,
        ite_eq_right fun h ↦ hk (Fin.ext h)])
    fun j hj ↦ exists_sum_smul_degreeOneDeriv_gradedMk_demushkinWordNeTwo_eq hn hq hn1 j hj

end freeProP

end TauCeti
