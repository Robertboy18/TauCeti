/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Orientation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationModule

/-!
# The relator classes of the Demushkin normal forms in Labute's module

Let `G` be a pro-`p` group, `N` a closed normal subgroup, and `N^{ab} = N ⧸ (N, N)` its topological
abelianization, a compact module over the completed group algebra `Λ = ℤ_p[[G ⧸ N]]` through the
conjugation action `[g] • [x] = [g x g⁻¹]` (`TauCeti.IsProP.completedGroupAlgebraModule`). This
file computes the classes in `N^{ab}` of the three Demushkin normal-form relator words of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic`, read on a tuple `x` whose
entries other than the marked generators lie in `N`, as explicit `Λ`-combinations of the classes
of the entries lying in `N`.

The computation rests on two facts about classes in `N^{ab}`. Labute's commutator
`(x, g) = x⁻¹ (g⁻¹ x g)` of `x ∈ N` with `g ∈ G` has class `([g]⁻¹ - 1) • [x]`
(`TauCeti.IsProP.ofMul_mk_labuteComm`), and a commutator of two elements of `N` has class zero
(`TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator`). Hence, writing `[x_i]` for the
class of a generator and `[x_i]` inside a coefficient for its image in `Λ`, the words have the
classes

* `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n) ↦ (q - 1 + [x₂]⁻¹) • [x₁]`, for `x_i ∈ N` when `i ≠ 2`;
* `x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n) ↦ [x₁²] + (2^f - 1 + [x₃]⁻¹) • [x₂]`, for
  `x₁² ∈ N` and `x_i ∈ N` when `i ≠ 1, 3`;
* `x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n) ↦ (1 + a + [x₂]⁻¹) • [x₁] +
  (2^f - 1 + [x₄]⁻¹) • [x₃]`, for `x_i ∈ N` when `i ≠ 2, 4` and `n ≥ 4`; for `n ≤ 3` the
  second coefficient is `2^f`.

The case of interest is `N = X = ker χ` for a continuous character `χ : G → ℤ_pˣ`, with the
membership hypotheses read as `χ (x_i) = 1`; the second half of the file states the three
computations in that form. For `G` free pro-`p` on `x₁, …, x_n` and `χ` the standard orientation
of a normal form, which is trivial on the unmarked generators
(`TauCeti.orientationNeTwo_presentedProPGen_of_ne` and its companions, composed with the
presentation map), `X^{ab}` is Labute's module `E = X ⧸ (X, X)` (§4 Definition, p. 121), and the
third formula is his expression `⟦r⟧ = (1 + a + (1 + T)^a) ⟦y₁⟧ + (2^g + (1 + T)^{ab} - 1) ⟦y₃⟧`
of the relator class in the dyadic even-rank case (p. 122), once the images `[x₂]`, `[x₄]` of the
marked generators in `Γ = Im χ` are written as powers of a topological generator `1 + T` of
`Λ = ℤ₂[[Γ]]`.

**Conventions.** Labute lets `Γ` act by `[y] · [x] = [y⁻¹ x y]`, the inverse of the conjugation
action used here (see `TopologicalAbelianization.mk_inv_smul_mk`); accordingly, every coefficient
below carries `[g]⁻¹` where Labute writes `[g]`. The exponents `q`, `2 + a` and `2^f` are natural
numbers, as in the definitions of the words.

## Main results

* `TauCeti.IsProP.ofMul_mk_labuteComm`: the class of Labute's commutator `(x, g)`, `x ∈ N`, is
  `([g]⁻¹ - 1) • [x]`.
* `TauCeti.IsProP.ofMul_mk_demushkinWordNeTwo`, `TauCeti.IsProP.ofMul_mk_demushkinWordTwoOdd`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven_of_le_three`: the relator classes of the three
  normal-form words in `N^{ab}`, for a tuple whose unmarked entries lie in `N`.
* `TauCeti.IsProP.ofMul_mk_demushkinWordNeTwo_ker`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoOdd_ker`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven_ker`,
  `TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven_ker_of_le_three`: the same in the abelianized
  kernel of a continuous character trivial on the unmarked generators.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  pp. 121–122.
-/

public section

namespace TauCeti

open scoped commutatorElement

/-! ### The relator classes over the completed group algebra -/

namespace IsProP

section Module

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP p G) {N : Subgroup G} [N.Normal]
  [IsClosed (N : Set G)]
include hG

/-- **The class of Labute's commutator `(x, g)`, for `x ∈ N`**, in `N^{ab}` as a module over
`ℤ_p[[G ⧸ N]]`: it is `([g]⁻¹ - 1) • [x]`, for the conjugation action `[g] • [x] = [g x g⁻¹]`
of `TauCeti.IsProP.completedGroupAlgebraModule`. In Labute's convention `[g] · [x] = [g⁻¹ x g]`
the coefficient reads `[g] - 1`. -/
theorem ofMul_mk_labuteComm {x : G} (hx : x ∈ N) (g : G) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨labuteComm x g, labuteComm_mem_of_mem_left hx g⟩ : N) :
        TopologicalAbelianization N) =
      (completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (g : G ⧸ N)⁻¹ - 1) •
        Additive.ofMul ((⟨x, hx⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have h : (⟨labuteComm x g, labuteComm_mem_of_mem_left hx g⟩ : N) =
      (⟨x, hx⟩ : N)⁻¹ * ⟨g⁻¹ * ((⟨x, hx⟩ : N) : G) * g, ‹N.Normal›.conj_mem' _ hx g⟩ :=
    Subtype.ext (by simp [labuteComm_def, mul_assoc])
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ofMul_mul, ofMul_inv, neg_add_eq_sub,
    sub_smul, one_smul, (hG.topologicalAbelianization N).completedGroupAlgebraModule_of_smul,
    ← Additive.ofMul_smul, TopologicalAbelianization.mk_inv_smul_mk]

/-- **The relator class of the `q ≠ 2` normal form.** For a tuple `x` all of whose entries other
than `x₂ = x 1` lie in `N`, the class of `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` in `N^{ab}` is
`(q - 1 + [x₂]⁻¹) • [x₁]` over `ℤ_p[[G ⧸ N]]`. -/
theorem ofMul_mk_demushkinWordNeTwo (q : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → x i ∈ N) (hr : demushkinWordNeTwo q n x ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, hr⟩ : N) : TopologicalAbelianization N) =
      ((q : completedGroupAlgebra ℤ_[p] (G ⧸ N)) - 1 +
          completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
        Additive.ofMul ((⟨x 0, hx 0 zero_ne_one⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  obtain ⟨m, hm⟩ : ∃ m, n / 2 = m + 1 := ⟨n / 2 - 1, by omega⟩
  -- The commutators after `(x₁, x₂)` pair elements of `N`, so their product lies in `⁅N, N⁆`.
  have ht : ((List.range m).map fun i ↦ labuteComm (x (2 * (i + 1))) (x (2 * (i + 1) + 1))).prod ∈
      ⁅N, N⁆ :=
    list_prod_map_labuteComm_range_mem_commutator m (fun i _ ↦ hx _ (by omega))
      (fun i _ ↦ hx _ (by omega))
  have h : (⟨_, hr⟩ : N) = (⟨x 0, hx 0 zero_ne_one⟩ : N) ^ q *
      (⟨labuteComm (x 0) (x 1), labuteComm_mem_of_mem_left (hx 0 zero_ne_one) _⟩ *
        ⟨_, Subgroup.commutator_le_left N N ht⟩) := by
    ext
    simp [demushkinWordNeTwo_def, hm, List.range_succ_eq_map, Function.comp_def]
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_mul,
    ofMul_pow, hG.ofMul_mk_labuteComm (hx 0 zero_ne_one) (x 1),
    TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator _ ht, add_zero,
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N)), ← add_smul]
  congr 1
  abel

/-- **The relator class of the `q = 2`, `n` odd normal form.** For a tuple `x` with `x₁² ∈ N`
and all entries other than `x₁ = x 0` and `x₃ = x 2` in `N`, the class of
`x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)` in `N^{ab}` is
`[x₁²] + (2^f - 1 + [x₃]⁻¹) • [x₂]` over `ℤ_p[[G ⧸ N]]`. -/
theorem ofMul_mk_demushkinWordTwoOdd (f : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx₀ : x 0 ^ 2 ∈ N) (hx : ∀ i, i ≠ 0 → i ≠ 2 → x i ∈ N)
    (hr : demushkinWordTwoOdd f n x ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, hr⟩ : N) : TopologicalAbelianization N) =
      Additive.ofMul ((⟨x 0 ^ 2, hx₀⟩ : N) : TopologicalAbelianization N) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ N)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 2 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 1, hx 1 one_ne_zero (by decide)⟩ : N) :
            TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  obtain ⟨m, hm⟩ : ∃ m, n / 2 = m + 1 := ⟨n / 2 - 1, by omega⟩
  have h1 : x 1 ∈ N := hx 1 one_ne_zero (by decide)
  -- The commutators after `(x₂, x₃)` pair elements of `N`, so their product lies in `⁅N, N⁆`.
  have ht : ((List.range m).map fun i ↦
      labuteComm (x (2 * (i + 1) + 1)) (x (2 * (i + 1) + 2))).prod ∈ ⁅N, N⁆ :=
    list_prod_map_labuteComm_range_mem_commutator m (fun i _ ↦ hx _ (by omega) (by omega))
      (fun i _ ↦ hx _ (by omega) (by omega))
  have h : (⟨_, hr⟩ : N) = ⟨x 0 ^ 2, hx₀⟩ * ((⟨x 1, h1⟩ : N) ^ 2 ^ f *
      (⟨labuteComm (x 1) (x 2), labuteComm_mem_of_mem_left h1 _⟩ *
        ⟨_, Subgroup.commutator_le_left N N ht⟩)) := by
    ext
    simp [demushkinWordTwoOdd_def, hm, List.range_succ_eq_map, Function.comp_def, mul_assoc]
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
    ofMul_mul, ofMul_mul, ofMul_mul, ofMul_pow, hG.ofMul_mk_labuteComm h1 (x 2),
    TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator _ ht, add_zero,
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N)), ← add_smul, Nat.cast_pow,
    Nat.cast_ofNat]
  congr 2
  abel

/-- **The relator class of the `q = 2`, `n` even normal form**, for `n ≥ 4`. For a tuple `x` all
of whose entries other than `x₂ = x 1` and `x₄ = x 3` lie in `N`, the class of
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` in `N^{ab}` is
`(1 + a + [x₂]⁻¹) • [x₁] + (2^f - 1 + [x₄]⁻¹) • [x₃]` over `ℤ_p[[G ⧸ N]]`. This is the expression
Labute computes on p. 122, up to the inversion of the acting group. -/
theorem ofMul_mk_demushkinWordTwoEven (a f : ℕ) {n : ℕ} (hn : 3 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i ≠ 3 → x i ∈ N) (hr : demushkinWordTwoEven a f n x ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, hr⟩ : N) : TopologicalAbelianization N) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ N)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 0, hx 0 zero_ne_one (by decide)⟩ : N) :
            TopologicalAbelianization N) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ N)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 3 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 2, hx 2 (by decide) (by decide)⟩ : N) :
            TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  obtain ⟨m, hm⟩ : ∃ m, n / 2 - 1 = m + 1 := ⟨n / 2 - 2, by omega⟩
  have h0 : x 0 ∈ N := hx 0 zero_ne_one (by decide)
  have h2 : x 2 ∈ N := hx 2 (by decide) (by decide)
  -- The commutators after `(x₃, x₄)` pair elements of `N`, so their product lies in `⁅N, N⁆`.
  have ht : ((List.range m).map fun i ↦
      labuteComm (x (2 * (i + 1) + 2)) (x (2 * (i + 1) + 3))).prod ∈ ⁅N, N⁆ :=
    list_prod_map_labuteComm_range_mem_commutator m (fun i _ ↦ hx _ (by omega) (by omega))
      (fun i _ ↦ hx _ (by omega) (by omega))
  have h : (⟨_, hr⟩ : N) = (⟨x 0, h0⟩ : N) ^ (2 + a) *
      (⟨labuteComm (x 0) (x 1), labuteComm_mem_of_mem_left h0 _⟩ * ((⟨x 2, h2⟩ : N) ^ 2 ^ f *
        (⟨labuteComm (x 2) (x 3), labuteComm_mem_of_mem_left h2 _⟩ *
          ⟨_, Subgroup.commutator_le_left N N ht⟩))) := by
    ext
    simp [demushkinWordTwoEven_def, hm, List.range_succ_eq_map, Function.comp_def, mul_assoc]
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_pow, QuotientGroup.mk_pow, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_mul,
    ofMul_pow, ofMul_pow, hG.ofMul_mk_labuteComm h0 (x 1), hG.ofMul_mk_labuteComm h2 (x 3),
    TopologicalAbelianization.ofMul_mk_eq_zero_of_mem_commutator _ ht, add_zero,
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N)),
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N)), ← add_assoc, ← add_smul,
    ← add_smul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat]
  congr 2
  · rw [← one_add_one_eq_two]
    abel
  · abel

/-- **The relator class of the `q = 2`, `n` even normal form**, for `n ≤ 3`, where the word is
`x₁^{2+a} (x₁, x₂) x₃^{2^f}` and, at `n = 2`, `x₃ = 1`. For `x₁, x₃ ∈ N` the class in `N^{ab}` is
`(1 + a + [x₂]⁻¹) • [x₁] + 2^f • [x₃]` over `ℤ_p[[G ⧸ N]]`. -/
theorem ofMul_mk_demushkinWordTwoEven_of_le_three (a f : ℕ) {n : ℕ} (hn : n ≤ 3) {x : ℕ → G}
    (h0 : x 0 ∈ N) (h2 : x 2 ∈ N) (hr : demushkinWordTwoEven a f n x ∈ N) :
    letI := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
    Additive.ofMul ((⟨_, hr⟩ : N) : TopologicalAbelianization N) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ N)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ N) (x 1 : G ⧸ N)⁻¹) •
          Additive.ofMul ((⟨x 0, h0⟩ : N) : TopologicalAbelianization N) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ N)) ^ f) •
          Additive.ofMul ((⟨x 2, h2⟩ : N) : TopologicalAbelianization N) := by
  let _ := (hG.topologicalAbelianization N).completedGroupAlgebraModule (G ⧸ N)
  have hm : n / 2 - 1 = 0 := by omega
  have h : (⟨_, hr⟩ : N) = (⟨x 0, h0⟩ : N) ^ (2 + a) *
      (⟨labuteComm (x 0) (x 1), labuteComm_mem_of_mem_left h0 _⟩ * (⟨x 2, h2⟩ : N) ^ 2 ^ f) := by
    ext
    simp [demushkinWordTwoEven_def, hm, mul_assoc]
  rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
    ofMul_mul, ofMul_mul, ofMul_pow, ofMul_pow, hG.ofMul_mk_labuteComm h0 (x 1),
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N)),
    ← Nat.cast_smul_eq_nsmul (completedGroupAlgebra ℤ_[p] (G ⧸ N)), ← add_assoc, ← add_smul,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat]
  congr 2
  rw [← one_add_one_eq_two]
  abel

/-! ### The relator classes in the abelianized kernel of a character -/

section Kernel

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [T1Space A] (χ : G →ₜ* A)

/-- **The relator class of the `q ≠ 2` normal form in the abelianized kernel of a character.**
For a continuous character `χ` of a pro-`p` group `G` to a commutative `T1` group and a tuple `x`
with `χ (x i) = 1` for `i ≠ 1`, the class of `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` in
`X^{ab}`, `X = ker χ`, is `(q - 1 + [x₂]⁻¹) • [x₁]` over `ℤ_p[[G ⧸ X]]`. For `G` free pro-`p` on
`x₁, …, x_n` and `χ` the standard orientation, `X^{ab}` is Labute's module `E`. -/
theorem ofMul_mk_demushkinWordNeTwo_ker (q : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → χ (x i) = 1) :
    haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
      χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordNeTwo_mem_ker χ.toMonoidHom q n hx⟩ : χ.toMonoidHom.ker) :
        TopologicalAbelianization χ.toMonoidHom.ker) =
      ((q : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) - 1 +
          completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
            (x 1 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
        Additive.ofMul ((⟨x 0, MonoidHom.mem_ker.mpr (hx 0 zero_ne_one)⟩ : χ.toMonoidHom.ker) :
          TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
    χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  hG.ofMul_mk_demushkinWordNeTwo q hn (fun i hi ↦ MonoidHom.mem_ker.mpr (hx i hi)) _

/-- **The relator class of the `q = 2`, `n` odd normal form in the abelianized kernel of a
character.** For a continuous character `χ` of a pro-`p` group `G` to a commutative `T1` group and
a tuple `x` with `χ (x 0) ^ 2 = 1` and `χ (x i) = 1` for `i ≠ 0, 2`, the class of
`x₁² x₂^{2^f} (x₂, x₃)(x₄, x₅) ⋯ (x_{n-1}, x_n)` in `X^{ab}`, `X = ker χ`, is
`[x₁²] + (2^f - 1 + [x₃]⁻¹) • [x₂]` over `ℤ_p[[G ⧸ X]]`. -/
theorem ofMul_mk_demushkinWordTwoOdd_ker (f : ℕ) {n : ℕ} (hn : 1 < n) {x : ℕ → G}
    (hx₀ : χ (x 0) ^ 2 = 1) (hx : ∀ i, i ≠ 0 → i ≠ 2 → χ (x i) = 1) :
    haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
      χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordTwoOdd_mem_ker χ.toMonoidHom f n hx₀ hx⟩ :
        χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) =
      Additive.ofMul ((⟨x 0 ^ 2, MonoidHom.mem_ker.mpr ((map_pow χ.toMonoidHom _ _).trans hx₀)⟩ :
          χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 2 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 1, MonoidHom.mem_ker.mpr (hx 1 one_ne_zero (by decide))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
    χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  hG.ofMul_mk_demushkinWordTwoOdd f hn _ (fun i hi₀ hi₂ ↦ MonoidHom.mem_ker.mpr (hx i hi₀ hi₂)) _

/-- **The relator class of the `q = 2`, `n` even normal form in the abelianized kernel of a
character**, for `n ≥ 4`. For a continuous character `χ` of a pro-`p` group `G` to a commutative
`T1` group and a tuple `x` with `χ (x i) = 1` for `i ≠ 1, 3`, the class of
`x₁^{2+a} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` in `X^{ab}`, `X = ker χ`, is
`(1 + a + [x₂]⁻¹) • [x₁] + (2^f - 1 + [x₄]⁻¹) • [x₃]` over `ℤ_p[[G ⧸ X]]`. For `G` free pro-`2` on
`x₁, …, x_n` and `χ` the standard orientation, this is the expression of Labute, p. 122, up to
the inversion of the acting group. -/
theorem ofMul_mk_demushkinWordTwoEven_ker (a f : ℕ) {n : ℕ} (hn : 3 < n) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i ≠ 3 → χ (x i) = 1) :
    haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
      χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordTwoEven_mem_ker χ.toMonoidHom a f n hx⟩ :
        χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 1 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 0, MonoidHom.mem_ker.mpr (hx 0 zero_ne_one (by decide))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) ^ f - 1 +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 3 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 2, MonoidHom.mem_ker.mpr (hx 2 (by decide) (by decide))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
    χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  hG.ofMul_mk_demushkinWordTwoEven a f hn (fun i hi₁ hi₃ ↦ MonoidHom.mem_ker.mpr (hx i hi₁ hi₃)) _

/-- **The relator class of the `q = 2`, `n` even normal form in the abelianized kernel of a
character**, for `n ≤ 3`, where the word is `x₁^{2+a} (x₁, x₂) x₃^{2^f}` and, at `n = 2`,
`x₃ = 1`. For a continuous character `χ` of a pro-`p` group `G` to a commutative `T1` group and a
tuple `x` with `χ (x i) = 1` for `i ≠ 1, 3`, the class in `X^{ab}`, `X = ker χ`, is
`(1 + a + [x₂]⁻¹) • [x₁] + 2^f • [x₃]` over `ℤ_p[[G ⧸ X]]`. -/
theorem ofMul_mk_demushkinWordTwoEven_ker_of_le_three (a f : ℕ) {n : ℕ} (hn : n ≤ 3) {x : ℕ → G}
    (hx : ∀ i, i ≠ 1 → i ≠ 3 → χ (x i) = 1) :
    haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
      χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
    letI := (hG.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
      (G ⧸ χ.toMonoidHom.ker)
    Additive.ofMul ((⟨_, demushkinWordTwoEven_mem_ker χ.toMonoidHom a f n hx⟩ :
        χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) =
      (1 + (a : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) +
            completedGroupAlgebra.of ℤ_[p] (G ⧸ χ.toMonoidHom.ker)
              (x 1 : G ⧸ χ.toMonoidHom.ker)⁻¹) •
          Additive.ofMul ((⟨x 0, MonoidHom.mem_ker.mpr (hx 0 zero_ne_one (by decide))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) +
        ((2 : completedGroupAlgebra ℤ_[p] (G ⧸ χ.toMonoidHom.ker)) ^ f) •
          Additive.ofMul ((⟨x 2, MonoidHom.mem_ker.mpr (hx 2 (by decide) (by decide))⟩ :
            χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker) :=
  haveI : IsClosed (χ.toMonoidHom.ker : Set G) :=
    χ.toMonoidHom.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  hG.ofMul_mk_demushkinWordTwoEven_of_le_three a f hn _ _ _

end Kernel

end Module

end IsProP

end TauCeti
