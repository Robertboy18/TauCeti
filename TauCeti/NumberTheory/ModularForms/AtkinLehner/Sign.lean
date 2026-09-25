/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.OldSpace
public import TauCeti.NumberTheory.ModularForms.Newforms.Fricke
public import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Hecke
import TauCeti.NumberTheory.ModularForms.Newforms.Nebentypus
import TauCeti.NumberTheory.ModularForms.Petersson.AtkinLehner

/-!
# The Atkin–Lehner signs of a newform of trivial nebentypus

For a newform `f` of level `N`, weight `k` and trivial nebentypus and an exact divisor `Q ∥ N`,
the normalized Atkin–Lehner operator `𝒲_Q` on `S_k(Γ₀(N))` satisfies `𝒲_Q f = ε_Q(f) · f` for a
sign `ε_Q(f) ∈ {1, -1}`, the **Atkin–Lehner sign** (or Atkin–Lehner eigenvalue) of `f` at `Q`.
The signs are multiplicative on coprime exact divisors, `ε_1(f) = 1`, and `ε_N(f)` is the Fricke
sign of `f`, so that the signs at the maximal prime powers `p ^ v_p(N)` of `N` multiply to the
Fricke sign, the sign entering the functional equation of `L(s, f)`.

The argument is the one that gives the Fricke sign, run on the `Γ₀(N)` carrier the Atkin–Lehner
operators live on.

* `𝒲_Q` preserves the new subspace at trivial nebentypus. It preserves the old subspace
  (`TauCeti.Nat.IsExactDivisor.ofLe_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsOld`) and is
  Petersson self-adjoint on `S_k(Γ₀(N))`. Newness of a form of trivial nebentypus is tested
  against the old forms of trivial nebentypus alone, and the Petersson product of two such forms
  at level `Γ₁(N)` is a fixed positive multiple of their product at level `Γ₀(N)`
  (`CuspForm.peterssonInnerCosets_ofLe_ofLe`), so the two pairings detect the same orthogonality.
* On `S_k(N, 1)` the operator `𝒲_Q` commutes with the Hecke operators `Tₙ` for `n` prime to `Q`:
  it commutes with the action of every double coset of determinant prime to `Q`
  (`TauCeti.commute_atkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd`), and those `Tₙ` lie in
  the subring such cosets generate
  (`HeckeRing.GL2.heckeTCompositeGamma0_mem_closure_coprimeDetCoset`).
* Multiplicity one
  (`HeckeRing.GL2.exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew`): `𝒲_Q f`
  is a good Hecke eigenvector in the new part with the eigenvalues of `f`, hence a multiple
  `ε • f`, and `𝒲_Q ∘ 𝒲_Q = 1` forces `ε ^ 2 = 1`.

For a nontrivial nebentypus `χ` the operator `W_Q` conjugates the `Q`-part of the character, so
it does not preserve `S_k(N, χ)` and a newform is carried to a multiple of a different newform;
the sign statement is specific to trivial nebentypus.

## Main definitions

* `TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerCharCuspOneEnd`: `𝒲_Q` on the
  trivial-nebentypus space `S_k(N, 1)`, transported from `S_k(Γ₀(N))`.
* `HeckeRing.GL2.Newform.toCuspFormGamma0`: a newform of trivial nebentypus, as a cusp form on
  `Γ₀(N)`.
* `HeckeRing.GL2.Newform.atkinLehnerSign`: the Atkin–Lehner sign `ε_Q(f)` of a newform of
  trivial nebentypus.

## Main results

* `TauCeti.Nat.IsExactDivisor.ofLe_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew`: `𝒲_Q`
  preserves the new subspace at trivial nebentypus.
* `commute_normalizedAtkinLehnerCharCuspOneEnd_heckeRingHomCuspCharSpace` (in the namespace
  `TauCeti.Nat.IsExactDivisor`): on `S_k(N, 1)`, `𝒲_Q` commutes with `Tₙ` for every `n` prime
  to `Q`.
* `exists_normalizedAtkinLehnerOperatorCusp_eq_smul_of_mem_cuspFormsNew` (same namespace):
  a nonzero form in the new part of `S_k(N, 1)` that is an eigenvector of every good `Tₚ`
  satisfies `𝒲_Q f = ε • f` with `ε = 1` or `ε = -1`.
* `normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul` and
  `atkinLehnerSign_eq_one_or_neg_one` (in the namespace `HeckeRing.GL2.Newform`): the eigenvalue
  equation and the sign law of `ε_Q(f)`.
* `HeckeRing.GL2.Newform.atkinLehnerSign_mul`, `HeckeRing.GL2.Newform.atkinLehnerSign_self`,
  `HeckeRing.GL2.Newform.prod_atkinLehnerSign_primePow_eq_frickeSign`: the signs are
  multiplicative on coprime exact divisors, `ε_N(f)` is the Fricke sign, and the signs at the
  maximal prime powers of `N` multiply to it.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.15.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.10.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GLn
  HeckeRing.GL2

open scoped MatrixGroups ModularForm HeckeCosetModule TauCeti.ExactDivisor

namespace TauCeti

variable {N Q R : ℕ} [NeZero N] {k : ℤ}

namespace Nat.IsExactDivisor

/-! ### `𝒲_Q` preserves the new subspace at trivial nebentypus -/

/-- **The normalized Atkin–Lehner operator preserves the new subspace at trivial nebentypus.**
For a cusp form `f` on `Γ₀(N)` whose restriction to `Γ₁(N)` is new, the restriction of `𝒲_Q f`
is again new, for every exact divisor `Q ∥ N`.

Newness of a form of trivial nebentypus is orthogonality to the old forms of trivial nebentypus,
which are the restrictions of forms `g` on `Γ₀(N)`; there the `Γ₁(N)`-Petersson product is a
multiple of the `Γ₀(N)`-one, for which `𝒲_Q` is self-adjoint and preserves oldness. -/
theorem ofLe_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew (h : Q ∥ N)
    {f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k}
    (hf : CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f ∈ cuspFormsNew N k) :
    CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) (h.normalizedAtkinLehnerOperatorCusp k f) ∈
      cuspFormsNew N k := by
  rw [mem_cuspFormsNew_iff_of_mem_cuspFormCharSpace (ofLe_mem_cuspFormCharSpace_one _),
    CuspForm.mem_peterssonOrthogonal_iff]
  rintro G ⟨hGold, hG⟩
  -- an old form of trivial nebentypus is the restriction of a cusp form `g` on `Γ₀(N)`
  rw [cuspFormCharSpace_one_eq_range] at hG
  obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hG
  rw [CuspForm.ofLeₗ_apply] at hGold ⊢
  rw [CuspForm.peterssonInnerCosets_ofLe_ofLe,
    ← h.peterssonInnerCosets_normalizedAtkinLehnerOperatorCusp_left,
    ← CuspForm.peterssonInnerCosets_ofLe_ofLe (Gamma1_map_le_Gamma0_map N)]
  rw [cuspFormsNew_def] at hf
  exact CuspForm.mem_peterssonOrthogonal_iff.mp hf _
    (h.ofLe_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsOld hGold)

/-! ### `𝒲_Q` on `S_k(N, 1)` and its commutation with the good Hecke operators -/

/-- **The normalized Atkin–Lehner operator on the trivial-nebentypus space** `S_k(N, 1)`: the
operator `𝒲_Q` of `S_k(Γ₀(N))`, transported along the identification
`cuspFormCharSpaceOneEquiv : S_k(N, 1) ≃ S_k(Γ₀(N))`. -/
noncomputable def normalizedAtkinLehnerCharCuspOneEnd (h : Q ∥ N) (k : ℤ) :
    Module.End ℂ (cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :=
  (cuspFormCharSpaceOneEquiv N k).symm.conj (h.normalizedAtkinLehnerOperatorCusp k)

/-- Defining equation for the sealed `normalizedAtkinLehnerCharCuspOneEnd`: it is the conjugate
of `𝒲_Q` by the identification `S_k(N, 1) ≃ S_k(Γ₀(N))`. -/
theorem normalizedAtkinLehnerCharCuspOneEnd_def (h : Q ∥ N) (k : ℤ) :
    h.normalizedAtkinLehnerCharCuspOneEnd k =
      (cuspFormCharSpaceOneEquiv N k).symm.conj (h.normalizedAtkinLehnerOperatorCusp k) := (rfl)

/-- `normalizedAtkinLehnerCharCuspOneEnd` moves a form to `S_k(Γ₀(N))`, applies `𝒲_Q` and moves
back. -/
theorem normalizedAtkinLehnerCharCuspOneEnd_apply (h : Q ∥ N) (k : ℤ)
    (f : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    h.normalizedAtkinLehnerCharCuspOneEnd k f = (cuspFormCharSpaceOneEquiv N k).symm
      (h.normalizedAtkinLehnerOperatorCusp k (cuspFormCharSpaceOneEquiv N k f)) := by
  rw [normalizedAtkinLehnerCharCuspOneEnd_def, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_symm]

/-- Read on `S_k(Γ₀(N))`, `normalizedAtkinLehnerCharCuspOneEnd` is `𝒲_Q`. -/
@[simp]
theorem cuspFormCharSpaceOneEquiv_normalizedAtkinLehnerCharCuspOneEnd_apply (h : Q ∥ N) (k : ℤ)
    (f : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    cuspFormCharSpaceOneEquiv N k (h.normalizedAtkinLehnerCharCuspOneEnd k f) =
      h.normalizedAtkinLehnerOperatorCusp k (cuspFormCharSpaceOneEquiv N k f) := by
  rw [normalizedAtkinLehnerCharCuspOneEnd_apply, LinearEquiv.apply_symm_apply]

/-- On underlying cusp forms of level `Γ₁(N)`, `normalizedAtkinLehnerCharCuspOneEnd` is the
restriction of `𝒲_Q` applied on `S_k(Γ₀(N))`. -/
@[simp]
theorem coe_normalizedAtkinLehnerCharCuspOneEnd_apply (h : Q ∥ N) (k : ℤ)
    (f : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    ((h.normalizedAtkinLehnerCharCuspOneEnd k f : cuspFormCharSpace k 1) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.ofLe (Gamma1_map_le_Gamma0_map N)
        (h.normalizedAtkinLehnerOperatorCusp k (cuspFormCharSpaceOneEquiv N k f)) := by
  rw [normalizedAtkinLehnerCharCuspOneEnd_apply, coe_cuspFormCharSpaceOneEquiv_symm_apply]

/-- `𝒲_Q` commutes with the Hecke action of a single double coset of determinant prime to `Q` on
`S_k(N, 1)`: the `Γ₀(N)` commutation, read through `S_k(N, 1) ≃ S_k(Γ₀(N))`. -/
private lemma commute_normalizedAtkinLehnerCharCuspOneEnd_single (h : Q ∥ N)
    {D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))}
    (hD : CoprimeDetCoset N Q D) (c : ℤ) :
    Commute (h.normalizedAtkinLehnerCharCuspOneEnd k)
      (heckeRingHomCuspCharSpace k 1 (HeckeCosetModule.single ℤ D c)) := by
  refine LinearMap.ext fun f ↦ ?_
  -- the `Γ₀(N)` commutation, on the underlying function of `f`
  have hΓ₀ := congrArg DFunLike.coe (LinearMap.congr_fun
    (h.commute_normalizedAtkinLehnerOperatorCusp_heckeSlashGamma0CuspFormEnd hD).eq
    (cuspFormCharSpaceOneEquiv N k f))
  simp only [Module.End.mul_apply, coe_normalizedAtkinLehnerOperatorCusp,
    coe_heckeSlashGamma0CuspFormEnd, coe_cuspFormCharSpaceOneEquiv_apply] at hΓ₀
  have key : h.normalizedAtkinLehnerCharCuspOneEnd k (twistedHeckeSlashCuspFormCharEnd k 1 D f) =
      twistedHeckeSlashCuspFormCharEnd k 1 D (h.normalizedAtkinLehnerCharCuspOneEnd k f) := by
    refine Subtype.ext (DFunLike.coe_injective ?_)
    simp only [coe_normalizedAtkinLehnerCharCuspOneEnd_apply, CuspForm.coe_ofLe,
      coe_normalizedAtkinLehnerOperatorCusp, coe_cuspFormCharSpaceOneEquiv_apply,
      coe_twistedHeckeSlashCuspFormCharEnd, twistedHeckeSlashSum_eq_heckeSlashSum]
    exact hΓ₀
  simp [key]

/-- **The normalized Atkin–Lehner operator commutes with the Hecke operators away from `Q` on
`S_k(N, 1)`**: for `n` prime to `Q`, `𝒲_Q Tₙ = Tₙ 𝒲_Q`. Such `Tₙ` lie in the subring generated
by the double cosets of determinant prime to `Q`, each of which commutes with `𝒲_Q`. In
particular `𝒲_Q` commutes with every good Hecke operator, `n` prime to `N`. -/
theorem commute_normalizedAtkinLehnerCharCuspOneEnd_heckeRingHomCuspCharSpace (h : Q ∥ N)
    {n : ℕ} (hn : Nat.Coprime n Q) :
    Commute (h.normalizedAtkinLehnerCharCuspOneEnd k)
      (heckeRingHomCuspCharSpace k 1 (heckeTCompositeGamma0 N n)) := by
  have hS : Subring.closure {x : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ |
      ∃ D, CoprimeDetCoset N Q D ∧ x = HeckeCosetModule.single ℤ D 1} ≤
        (Subring.centralizer {h.normalizedAtkinLehnerCharCuspOneEnd (N := N) k}).comap
          (heckeRingHomCuspCharSpace k 1) := by
    refine Subring.closure_le.mpr ?_
    rintro x ⟨D, hD, rfl⟩
    simpa [Subring.mem_centralizer_iff, Set.mem_centralizer_iff, Commute, SemiconjBy] using
      h.commute_normalizedAtkinLehnerCharCuspOneEnd_single hD 1
  simpa [Subring.mem_centralizer_iff, Set.mem_centralizer_iff, Commute, SemiconjBy] using
    hS (heckeTCompositeGamma0_mem_closure_coprimeDetCoset N hn)

/-! ### The Atkin–Lehner sign -/

/-- **The Atkin–Lehner sign**: a nonzero cusp form in the new part of `S_k(N, 1)` that is an
eigenvector of `Tₚ` at every prime `p ∤ N` is, read on `S_k(Γ₀(N))`, an eigenvector of the
normalized Atkin–Lehner operator `𝒲_Q`, with eigenvalue `1` or `-1`. -/
theorem exists_normalizedAtkinLehnerOperatorCusp_eq_smul_of_mem_cuspFormsNew (h : Q ∥ N)
    {f : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)}
    (ha : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k 1 (heckeTCompositeGamma0 N p) f = c • f)
    (hf : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k)
    (hf0 : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      h.normalizedAtkinLehnerOperatorCusp k (cuspFormCharSpaceOneEquiv N k f) =
        ε • cuspFormCharSpaceOneEquiv N k f := by
  set g := cuspFormCharSpaceOneEquiv N k f with hg
  have hofLe : CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) g =
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    rw [← coe_cuspFormCharSpaceOneEquiv_symm_apply, hg, LinearEquiv.symm_apply_apply]
  -- `𝒲_Q f` has the good Hecke eigenvalues of `f`, and lies in the new part
  have heig (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) : ∃ c : ℂ,
      heckeRingHomCuspCharSpace k 1 (heckeTCompositeGamma0 N p) f = c • f ∧
        heckeRingHomCuspCharSpace k 1 (heckeTCompositeGamma0 N p)
          (h.normalizedAtkinLehnerCharCuspOneEnd k f) =
            c • h.normalizedAtkinLehnerCharCuspOneEnd k f := by
    obtain ⟨c, hc⟩ := ha p hp hpN
    refine ⟨c, hc, ?_⟩
    rw [← Module.End.mul_apply,
      ← (h.commute_normalizedAtkinLehnerCharCuspOneEnd_heckeRingHomCuspCharSpace
        (hpN.coprime_dvd_right h.dvd)).eq,
      Module.End.mul_apply, hc, map_smul]
  have hnew : ((h.normalizedAtkinLehnerCharCuspOneEnd k f : cuspFormCharSpace k 1) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k := by
    rw [coe_normalizedAtkinLehnerCharCuspOneEnd_apply]
    exact h.ofLe_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew (hofLe ▸ hf)
  -- so multiplicity one makes it a multiple of `f`
  obtain ⟨ε, hε⟩ :=
    exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew heig hf hnew hf0
  have hε' : h.normalizedAtkinLehnerOperatorCusp k g = ε • g := by
    rw [hg, ← cuspFormCharSpaceOneEquiv_normalizedAtkinLehnerCharCuspOneEnd_apply, ← map_smul]
    exact congrArg _ (Subtype.ext hε)
  refine ⟨ε, ?_, hε'⟩
  -- and `𝒲_Q ∘ 𝒲_Q = 1` forces `ε * ε = 1`
  have hg0 : g ≠ 0 := fun h0 ↦
    hf0 (by simpa using congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff _).mp h0))
  have h2 := h.normalizedAtkinLehnerOperatorCusp_normalizedAtkinLehnerOperatorCusp_self k g
  rw [hε', map_smul, hε', smul_smul] at h2
  exact mul_self_eq_one_iff.1 (smul_left_injective ℂ hg0 (h2.trans (one_smul ℂ g).symm))

end Nat.IsExactDivisor

end TauCeti

namespace HeckeRing.GL2

open TauCeti

variable {N Q R : ℕ} [NeZero N] {k : ℤ}

namespace Newform

/-! ### A newform of trivial nebentypus on `Γ₀(N)` -/

/-- **A newform of trivial nebentypus, as a cusp form on `Γ₀(N)`**: the same function on `ℍ`,
re-read as a form for the bare group `Γ₀(N)` under the identification `S_k(N, 1) ≃ S_k(Γ₀(N))`.
This is the carrier on which the Atkin–Lehner operators act. -/
noncomputable def toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k :=
  cuspFormCharSpaceOneEquiv N k ⟨f.toCuspForm, hχ ▸ f.mem_charSpace⟩

/-- `toCuspFormGamma0` does not change the underlying function on `ℍ`. -/
@[simp]
theorem coe_toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) :
    ⇑(f.toCuspFormGamma0 hχ) = ⇑f.toCuspForm :=
  coe_cuspFormCharSpaceOneEquiv_apply _

/-- Restricting `toCuspFormGamma0` back to `Γ₁(N)` recovers the newform. -/
@[simp]
theorem ofLe_toCuspFormGamma0 (f : Newform N k) (hχ : f.χ = 1) :
    CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) (f.toCuspFormGamma0 hχ) = f.toCuspForm :=
  CuspForm.ext fun τ ↦ by simp [CuspForm.coe_ofLe]

/-- A newform of trivial nebentypus is nonzero on `Γ₀(N)`. -/
theorem toCuspFormGamma0_ne_zero (f : Newform N k) (hχ : f.χ = 1) :
    f.toCuspFormGamma0 hχ ≠ 0 := fun h0 ↦
  f.ne_zero (DFunLike.coe_injective (by rw [← f.coe_toCuspFormGamma0 hχ, h0]; rfl))

/-! ### The Atkin–Lehner signs -/

/-- **The Atkin–Lehner sign of a newform of trivial nebentypus exists**: `𝒲_Q f = ε • f` with
`ε = 1` or `ε = -1`, for every exact divisor `Q ∥ N`. -/
theorem exists_normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_smul (f : Newform N k)
    (hχ : f.χ = 1) (h : Q ∥ N) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      h.normalizedAtkinLehnerOperatorCusp k (f.toCuspFormGamma0 hχ) =
        ε • f.toCuspFormGamma0 hχ := by
  revert hχ
  obtain ⟨⟨F, χ, hmem, a, heig, hne⟩, hnew, hnorm⟩ := f
  intro hχ
  obtain rfl : χ = 1 := hχ
  exact h.exists_normalizedAtkinLehnerOperatorCusp_eq_smul_of_mem_cuspFormsNew (f := ⟨F, hmem⟩)
    (fun p hp hpN ↦ ⟨a ⟨p, hp.pos⟩ hpN, heig ⟨p, hp.pos⟩ hpN⟩) hnew hne

/-- **The Atkin–Lehner sign** `ε_Q(f)` of a newform of trivial nebentypus at an exact divisor
`Q ∥ N`: the eigenvalue of the normalized Atkin–Lehner operator `𝒲_Q` on `f`. -/
noncomputable def atkinLehnerSign (f : Newform N k) (hχ : f.χ = 1) (h : Q ∥ N) : ℂ :=
  (f.exists_normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_smul hχ h).choose

/-- The normalized Atkin–Lehner operator acts on a trivial-nebentypus newform by its
Atkin–Lehner sign. -/
theorem normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul
    (f : Newform N k) (hχ : f.χ = 1) (h : Q ∥ N) :
    h.normalizedAtkinLehnerOperatorCusp k (f.toCuspFormGamma0 hχ) =
      f.atkinLehnerSign hχ h • f.toCuspFormGamma0 hχ :=
  (f.exists_normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_smul hχ h).choose_spec.2

/-- The Atkin–Lehner sign of a trivial-nebentypus newform is `1` or `-1`. -/
theorem atkinLehnerSign_eq_one_or_neg_one (f : Newform N k) (hχ : f.χ = 1) (h : Q ∥ N) :
    f.atkinLehnerSign hχ h = 1 ∨ f.atkinLehnerSign hχ h = -1 :=
  (f.exists_normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_smul hχ h).choose_spec.1

/-- A scalar satisfying the normalized Atkin–Lehner eigenvalue equation is the Atkin–Lehner
sign. -/
theorem atkinLehnerSign_eq_of_normalizedAtkinLehnerOperatorCusp_eq_smul (f : Newform N k)
    (hχ : f.χ = 1) (h : Q ∥ N) {ε : ℂ}
    (hε : h.normalizedAtkinLehnerOperatorCusp k (f.toCuspFormGamma0 hχ) =
      ε • f.toCuspFormGamma0 hχ) :
    f.atkinLehnerSign hχ h = ε :=
  smul_left_injective ℂ (f.toCuspFormGamma0_ne_zero hχ)
    ((f.normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul hχ h).symm.trans
      hε)

/-- The Atkin–Lehner sign depends only on the divisor, not on the proof that it is exact. -/
theorem atkinLehnerSign_congr (f : Newform N k) (hχ : f.χ = 1) {Q' : ℕ} (h : Q ∥ N)
    (h' : Q' ∥ N) (e : Q = Q') : f.atkinLehnerSign hχ h = f.atkinLehnerSign hχ h' := by
  subst e
  rfl

/-- **The sign at `Q = 1` is `1`**, `𝒲_1` being the identity. -/
@[simp]
theorem atkinLehnerSign_one (f : Newform N k) (hχ : f.χ = 1) (h : 1 ∥ N) :
    f.atkinLehnerSign hχ h = 1 :=
  f.atkinLehnerSign_eq_of_normalizedAtkinLehnerOperatorCusp_eq_smul hχ h
    (by rw [h.normalizedAtkinLehnerOperatorCusp_one, one_smul])

/-- **The signs are multiplicative on coprime exact divisors**: `ε_{Q R}(f) = ε_Q(f) ε_R(f)`
when `Q` and `R` are coprime, since `𝒲_R ∘ 𝒲_Q = 𝒲_{Q R}`. -/
theorem atkinLehnerSign_mul (f : Newform N k) (hχ : f.χ = 1) (hQ : Q ∥ N) (hR : R ∥ N)
    (hQR : Nat.Coprime Q R) :
    f.atkinLehnerSign hχ (hQ.mul hR hQR) = f.atkinLehnerSign hχ hQ * f.atkinLehnerSign hχ hR := by
  refine f.atkinLehnerSign_eq_of_normalizedAtkinLehnerOperatorCusp_eq_smul hχ _ ?_
  rw [← hQ.normalizedAtkinLehnerOperatorCusp_normalizedAtkinLehnerOperatorCusp_of_coprime hR hQR,
    f.normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul hχ hQ, map_smul,
    f.normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul hχ hR, smul_smul,
    mul_comm]

/-- **The sign at `Q = N` is the Fricke sign**: `𝒲_N` is the normalized Fricke operator, read
on `Γ₀(N)`. -/
theorem atkinLehnerSign_self (f : Newform N k) (hχ : f.χ = 1) (h : N ∥ N) :
    f.atkinLehnerSign hχ h = f.frickeSign hχ := by
  refine f.atkinLehnerSign_eq_of_normalizedAtkinLehnerOperatorCusp_eq_smul hχ h
    (DFunLike.coe_injective ?_)
  rw [h.coe_normalizedAtkinLehnerOperatorCusp_self, coe_toCuspFormGamma0,
    ← coe_normalizedFrickeOperatorCusp, f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ]
  simp

/-- **The sign at an exact divisor is the product of the signs at its maximal prime powers**:
for `s ⊆ N.primeFactors`, `ε_{∏ p ∈ s, p ^ v_p(N)}(f) = ∏ p ∈ s, ε_{p ^ v_p(N)}(f)`. -/
theorem atkinLehnerSign_prodPrimePow (f : Newform N k) (hχ : f.χ = 1) {s : Finset ℕ}
    (hs : s ⊆ N.primeFactors) :
    f.atkinLehnerSign hχ (TauCeti.Nat.isExactDivisor_prodPrimePow (s := s)) =
      ∏ p ∈ s, f.atkinLehnerSign hχ (TauCeti.Nat.isExactDivisor_primePow (p := p)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, f.atkinLehnerSign_congr hχ _ TauCeti.Nat.isExactDivisor_one
      TauCeti.Nat.prodPrimePow_empty, atkinLehnerSign_one]
  | insert p s hps ih =>
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (hs (Finset.mem_insert_self p s))
    have hs' : s ⊆ N.primeFactors := (Finset.subset_insert p s).trans hs
    -- `p ^ v_p(N)` is coprime to the product over `s`, whose primes are those of `s`
    have hcop : Nat.Coprime (p ^ N.factorization p) (TauCeti.Nat.prodPrimePow N s) := by
      refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd ↦ hps ?_)
      rw [← TauCeti.Nat.primeFactors_prodPrimePow hs']
      exact Nat.mem_primeFactors.2 ⟨hp, hdvd, TauCeti.Nat.isExactDivisor_prodPrimePow.ne_zero⟩
    rw [Finset.prod_insert hps, ← ih hs',
      ← f.atkinLehnerSign_mul hχ (TauCeti.Nat.isExactDivisor_primePow (p := p))
        TauCeti.Nat.isExactDivisor_prodPrimePow hcop]
    exact f.atkinLehnerSign_congr hχ _ _ (TauCeti.Nat.prodPrimePow_insert hps)

/-- **The Atkin–Lehner signs multiply to the Fricke sign**:
`∏_{p ∣ N} ε_{p ^ v_p(N)}(f) = ε_N(f)`. -/
theorem prod_atkinLehnerSign_primePow_eq_frickeSign (f : Newform N k) (hχ : f.χ = 1) :
    ∏ p ∈ N.primeFactors, f.atkinLehnerSign hχ (TauCeti.Nat.isExactDivisor_primePow (p := p)) =
      f.frickeSign hχ := by
  rw [← f.atkinLehnerSign_prodPrimePow hχ subset_rfl,
    f.atkinLehnerSign_congr hχ _ (TauCeti.Nat.isExactDivisor_self (NeZero.ne N))
      (TauCeti.Nat.isExactDivisor_self (NeZero.ne N)).prodPrimePow_primeFactors,
    f.atkinLehnerSign_self]

end Newform

end HeckeRing.GL2
