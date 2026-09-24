/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Filtration

/-!
# Additive invariants of finite primary modules

An integer-valued invariant of finite discrete `p`-primary `G`-modules that is additive on
short exact sequences is determined, for pro-`p` groups, by its value on the trivial module
of order `p`. The coefficient group need not be killed by `p`.

The trivial module is supplied in the same universe as the coefficient groups, together with
an additive equivalence to `ZMod p`. In particular, it can be `ULift (ZMod p)`.
-/

public section

universe u v

namespace TauCeti

variable {p : ℕ} {G : Type v} [Group G] [TopologicalSpace G]

private theorem restrictDistribMulAction_continuousSMul {M : Type u} [AddCommGroup M]
    [TopologicalSpace M] [DistribMulAction G M] [ContinuousSMul G M]
    (N : AddSubgroup M) (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) :
    letI := N.restrictDistribMulAction hN
    ContinuousSMul G N := by
  let _ := N.restrictDistribMulAction hN
  exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

private theorem invariantSubgroup_torsion {M : Type u} [AddCommGroup M]
    (hM : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0) (N : AddSubgroup M) :
    ∀ x : N, ∃ k : ℕ, p ^ k • x = 0 := by
  intro x
  obtain ⟨k, hk⟩ := hM x
  exact ⟨k, Subtype.ext hk⟩

variable
  (I : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
    (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → ℤ)
  (hExact : ∀ {A B C : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0)
    (hC : ∀ c : C, ∃ k : ℕ, p ^ k • c = 0)
    (f : A →+ B) (q : B →+ C),
    (∀ (g : G) (a : A), f (g • a) = g • f a) →
    (∀ (g : G) (b : B), q (g • b) = g • q b) →
    Function.Injective f → Function.Surjective q →
    f.range = q.ker → I B hB = I A hA + I C hC)

include hExact in
private theorem invariant_eq_zero_of_subsingleton {A : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A] [Subsingleton A]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : I A hA = 0 := by
  have h := hExact hA hA hA 0 0
    (by intro g a; simp) (by intro g a; simp)
    (fun _ _ _ ↦ Subsingleton.elim _ _)
    (fun a ↦ ⟨0, Subsingleton.elim _ _⟩)
    (by
      ext a
      constructor
      · intro _
        rfl
      · intro _
        exact ⟨0, Subsingleton.elim _ _⟩)
  omega

include hExact in
private theorem invariant_eq_of_equiv {A B Z : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    [AddCommGroup Z] [TopologicalSpace Z] [DiscreteTopology Z]
    [DistribMulAction G Z] [ContinuousSMul G Z] [Finite Z] [Subsingleton Z]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0)
    (hZ : ∀ z : Z, ∃ k : ℕ, p ^ k • z = 0)
    (e : A ≃+ B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    I A hA = I B hB := by
  have h := hExact hA hB hZ e.toAddMonoidHom 0 he
    (by intro g b; simp) e.injective
    (fun z ↦ ⟨0, Subsingleton.elim _ _⟩)
    (by
      ext b
      constructor
      · intro _
        rfl
      · intro _
        exact e.surjective b)
  rw [invariant_eq_zero_of_subsingleton I hExact hZ, add_zero] at h
  exact h.symm

variable [Fact p.Prime]
  {M P : Type u}
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
  [DistribMulAction G P] [ContinuousSMul G P] [Finite P]

include hExact in
/-- An integer-valued invariant additive on equivariant short exact sequences of finite
discrete `p`-primary modules is its value on a trivial module of order `p`, multiplied by
the `p`-adic valuation of the cardinality. The trivial model `P` lies in the same universe
as `M`; no exponent-`p` assumption on `M` is needed. -/
theorem invariant_eq_padicValNat_mul_of_isProP
    (hG : IsProP p G)
    (hM : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0)
    (hP : ∀ x : P, ∃ k : ℕ, p ^ k • x = 0)
    (eP : P ≃+ ZMod p)
    (hPsmul : ∀ (g : G) (x : P), g • x = x) :
    I M hM = (padicValNat p (Nat.card M) : ℤ) * I P hP := by
  obtain ⟨N, hN, h0, hmono, htop, _, hfactors⟩ :=
    exists_filtration_with_trivial_factors_of_isProP hG hM
  let _ (i : ℕ) := (N i).restrictDistribMulAction (hN i)
  let _ (i : ℕ) := restrictDistribMulAction_continuousSMul (N i) (hN i)
  have hprim := fun i ↦ invariantSubgroup_torsion hM (N i)
  let _ : Subsingleton (N 0) := by rw [h0]; infer_instance
  have hzero := invariant_eq_zero_of_subsingleton I hExact (hprim 0)
  have hind : ∀ i, i ≤ padicValNat p (Nat.card M) →
      I (N i) (hprim i) = (i : ℤ) * I P hP := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.cast_zero, zero_mul] using hzero
    | succ i ih =>
      intro hi
      have hi' : i < padicValNat p (Nat.card M) :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
      have hprev := ih (Nat.le_trans (Nat.le_succ i) hi)
      let Q := N (i + 1) ⧸ (N i).addSubgroupOf (N (i + 1))
      let _ : DistribMulAction G Q :=
        (N i).subquotientDistribMulAction (N (i + 1)) (hN i) (hN (i + 1))
      obtain ⟨⟨eQ⟩, htriv⟩ := hfactors i hi'
      let _ : TopologicalSpace Q := ⊥
      let _ : DiscreteTopology Q := ⟨rfl⟩
      let _ : ContinuousSMul G Q :=
        ⟨by simpa only [htriv] using (continuous_snd : Continuous fun z : G × Q ↦ z.2)⟩
      let e : Q ≃+ P := eQ.trans eP.symm
      have hQ : ∀ y : Q, ∃ k : ℕ, p ^ k • y = 0 := by
        intro y
        obtain ⟨k, hk⟩ := hP (e y)
        refine ⟨k, e.injective ?_⟩
        simpa only [map_nsmul, map_zero] using hk
      have heq : I Q hQ = I P hP :=
        invariant_eq_of_equiv I hExact hQ hP (hprim 0) e
          (by intro g y; rw [htriv, hPsmul])
      have hstep := hExact (hprim i) (hprim (i + 1)) hQ
        (AddSubgroup.inclusion (hmono (Nat.le_succ i)))
        (QuotientAddGroup.mk' ((N i).addSubgroupOf (N (i + 1))))
        (AddSubgroup.restrictDistribMulAction_inclusion_smul (hN i) (hN (i + 1)) _)
        (fun g x ↦ (AddSubgroup.quotientDistribMulAction_smul_mk _ _ g x).symm)
        (AddSubgroup.inclusion_injective _) (QuotientAddGroup.mk'_surjective _)
        (by
          rw [QuotientAddGroup.ker_mk']
          ext x
          constructor
          · rintro ⟨y, rfl⟩
            exact y.property
          · intro hx
            exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩)
      rw [hprev, heq] at hstep
      simpa only [Nat.cast_succ, add_mul, one_mul] using hstep
  -- the top term of the filtration is all of `M`, so its inclusion is an equivariant
  -- isomorphism; feed it to `hExact` with a subsingleton quotient
  have hsurj : Function.Surjective (N (padicValNat p (Nat.card M))).subtype := fun m ↦
    ⟨⟨m, by rw [htop _ le_rfl]; exact AddSubgroup.mem_top m⟩,
      (AddSubgroup.subtype_apply _).trans (AddSubgroup.coe_mk _ _ _)⟩
  have htopStep := hExact (hprim _) hM (hprim 0) (N (padicValNat p (Nat.card M))).subtype
    (0 : M →+ N 0)
    (fun g x ↦ by
      rw [AddSubgroup.subtype_apply, AddSubgroup.subtype_apply,
        AddSubgroup.restrictDistribMulAction_coe_smul])
    (by intro g m; simp) (N (padicValNat p (Nat.card M))).subtype_injective
    (fun z ↦ ⟨0, Subsingleton.elim _ _⟩)
    (by rw [AddMonoidHom.range_eq_top.mpr hsurj, AddMonoidHom.ker_zero])
  rw [invariant_eq_zero_of_subsingleton I hExact (hprim 0), add_zero] at htopStep
  exact htopStep.trans (hind _ le_rfl)

end TauCeti
