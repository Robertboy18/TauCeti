/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector
public import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform

/-!
# Newforms are full Hecke eigenforms

A newform is, by definition, a normalised good Hecke eigenform in the new subspace (Miyake's
*primitive form*): eigen-ness is demanded only at the indices coprime to the level. This file
proves that it is an eigenvector of `T_n` at *every* positive index, including the primes dividing
the level, with eigenvalue the Fourier coefficient `a_n` (Diamond–Shurman, Theorem 5.8.2; Miyake,
Theorem 4.6.13). This is the bridge between the two definitions of "newform" in the literature:
Diamond–Shurman *define* a newform as a normalised full eigenform in the new subspace, and their
Theorem 5.8.2 is exactly the statement that Miyake's primitive forms are such.

The textbook route passes through the stability of the new subspace under the bad-prime
operators `U_p`. The argument here avoids it and runs in the whole nebentypus space `S_k(N, χ)`:

* **No normalised good eigenform of a proper divisor level shares the good eigensystem of a
  newform of level `N`** (`Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`). If `g` had
  proper divisor level `M`, the difference `f - V₁ g` would be a good Hecke eigenvector of
  `S_k(N, χ)` with `a₁ = 0`, hence old by the Main Lemma, while `V₁ g` is old outright; so `f`
  would be old and new, hence zero.
* **The good eigensystem of a newform `f` spans a line in `S_k(N, χ)`**
  (`Newform.exists_eq_smul_of_forall_prime_heckeTCuspNat_eq_smul`). A good eigenvector with the
  eigenvalues of `f` is a combination of level-raised newforms with those eigenvalues; those
  whose nebentypus induces `χ` have level `N` by the first point, hence are `f` by strong
  multiplicity one, and the others lie in the other nebentypus spaces, which meet `S_k(N, χ)`
  only in `0`.
* **`U_p f = a_p(f) f` for `p ∣ N`** (`Newform.heckeUCuspNat_eq_qExpansion_coeff_smul`): `U_p`
  commutes with the good `T_q`, so `U_p f` is a good eigenvector with the eigenvalues of `f`,
  hence a multiple of `f`; the multiple is read off the first coefficient.

The first point is also the divisor-level case of strong multiplicity one across levels: a
newform is not determined by its good eigensystem alone at *larger* levels, but among the levels
dividing a given one no two newforms share it.

## Main definitions

* `HeckeRing.GL2.Newform.toEigenform`: a newform as a full Hecke eigenform.

## Main results

* `HeckeRing.GL2.Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`: a normalised good Hecke
  eigenform of a divisor level `M ∣ N` sharing the nebentypus and the good eigensystem of a newform
  of level `N` has `M = N`.
* `HeckeRing.GL2.Newform.exists_eq_smul_of_forall_prime_heckeTCuspNat_eq_smul`: a good Hecke
  eigenvector of `S_k(N, χ)` with the eigenvalues of a newform `f` is a multiple of `f`.
* `HeckeRing.GL2.Newform.heckeUCuspNat_eq_qExpansion_coeff_smul`: `U_p f = a_p(f) • f` for a
  newform `f` and a prime `p ∣ N`.
* `HeckeRing.GL2.Newform.heckeTCuspNat_eq_qExpansion_coeff_smul`: `T_p f = a_p(f) • f` at every
  prime `p`.
* `HeckeRing.GL2.Newform.toEigenform_eigenvalue`: the eigenvalue of a newform at every positive
  index is its Fourier coefficient there.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### No newform of a proper divisor level shares the good eigensystem -/

/-- **A normalised good Hecke eigenform of a divisor level sharing the nebentypus and the good
eigensystem of a newform of level `N` has level `N`.** If `g` is a normalised good Hecke eigenform
of level `M ∣ N` whose nebentypus induces that of the newform `f` of level `N` and whose
eigenvalue agrees with that of `f` at every prime not dividing `N`, then `M = N`. Otherwise
`f - V₁ g` is a good Hecke eigenvector of `S_k(N, χ)` with `a₁ = 0`, hence old by the Main Lemma,
while `V₁ g` is old outright; so `f` would be old and new at once, hence zero. Nothing requires
`g` to be new; for a newform `g` the normalisation is `Newform.isNorm`. This is the divisor-level
case of strong multiplicity one across levels. -/
theorem level_eq_of_dvd_of_forall_prime_eigenvalue_eq {M : ℕ} [NeZero M] (f : Newform N k)
    (g : EigenformAwayFromLevel M k) (hg₁ : (qExpansion 1 g.toCuspForm).coeff 1 = 1)
    (hMN : M ∣ N) (hχ : g.χ.comp (ZMod.unitsMap hMN) = f.χ)
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN) = f.eigenvalue ⟨p, hp.pos⟩ hpN) :
    M = N := by
  by_contra hne
  have h1 : 1 * M ∣ N := by rwa [one_mul]
  -- `V₁ g`, viewed at level `N`: old, of nebentypus `χ`, normalised, and a good eigenvector
  -- with the eigenvalues of `f`
  set G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd h1) g.toCuspForm with hG
  have hGold : G ∈ cuspFormsOld N k := levelRaise_mem_cuspFormsOld h1 hne k g.toCuspForm
  have hGχ : G ∈ cuspFormCharSpace k f.χ := by
    have := CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h1 g.χ g.mem_charSpace
    rwa [hχ] at this
  have hG1 : (qExpansion 1 G).coeff 1 = 1 := by
    rw [hG, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _)
      (one_mem_strictPeriods_Gamma1_map _)]
    simp [hg₁]
  have hGeig : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) G = f.eigenvalue ⟨p, hp.pos⟩ hpN • G := by
    intro p hp hpN
    have : NeZero p := ⟨hp.ne_zero⟩
    rw [hG, heckeTCuspNat_levelRaise k h1 hp hpN,
      g.heckeTCuspNat_eq_eigenvalue_smul hp (hpN.coprime_dvd_right hMN), h p hp hpN,
      ← CuspForm.levelRaiseₗ_apply, map_smul, CuspForm.levelRaiseₗ_apply]
  -- the difference `f - V₁ g` is a good Hecke eigenvector of `S_k(N, χ)` with `a₁ = 0`
  set d : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := f.toCuspForm - G with hd
  have hdχ : d ∈ cuspFormCharSpace k f.χ := Submodule.sub_mem _ f.mem_charSpace hGχ
  have hdeig : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N p) ⟨d, hdχ⟩ = c • ⟨d, hdχ⟩ := by
    intro p hp hpN
    have : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨f.eigenvalue ⟨p, hp.pos⟩ hpN, Subtype.ext ?_⟩
    rw [heckeTCompositeGamma0_prime N hp,
      coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k f.χ hp, Submodule.coe_smul]
    simp only [hd, map_sub, f.heckeTCuspNat_eq_eigenvalue_smul hp hpN, hGeig p hp hpN, smul_sub]
  have hd1 : (qExpansion 1 d).coeff 1 = 0 := by
    rw [hd, FunLike.coe_sub,
      ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub, f.isNorm,
      hG1, sub_self]
  -- so it is old by the Main Lemma, and then so is `f = (f - V₁ g) + V₁ g`
  have hdold : d ∈ cuspFormsOld N k :=
    mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero hdχ fun n hn ↦
      qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime
        dvd_rfl hdeig hd1 n hn
  have hfold : f.toCuspForm ∈ cuspFormsOld N k := by
    have := Submodule.add_mem _ hdold hGold
    rwa [hd, sub_add_cancel] at this
  -- but `f` is new and nonzero
  exact f.ne_zero
    ((Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k)) _ hfold f.isNew)

/-! ### The good eigensystem of a newform spans a line in its nebentypus space -/

/-- **A good Hecke eigenvector of `S_k(N, χ)` with the eigenvalues of a newform `f` is a
multiple of `f`** (Diamond–Shurman, Theorem 5.8.2, on the whole nebentypus space rather than its
new part): if `F ∈ S_k(N, χ_f)` satisfies `Tₚ F = λₚ(f) • F` at every prime `p ∤ N`, then
`F = c • f` for some scalar `c`. Such an `F` is a combination of level-raised newforms with the
eigenvalues of `f`; those whose nebentypus induces `χ_f` have level `N`
(`level_eq_of_dvd_of_forall_prime_eigenvalue_eq`), hence are `f` by strong multiplicity one; the
others lie in the other nebentypus spaces, which meet `S_k(N, χ_f)` only in `0`. -/
theorem exists_eq_smul_of_forall_prime_heckeTCuspNat_eq_smul (f : Newform N k)
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hF : F ∈ cuspFormCharSpace k f.χ)
    (h : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = f.eigenvalue ⟨p, hp.pos⟩ hpN • F) :
    ∃ c : ℂ, F = c • f.toCuspForm := by
  classical
  -- `V₁` at a level is the identity
  have hV : ∀ (L : ℕ) [NeZero L] (hL : 1 * L ∣ L) (G : CuspForm ((Gamma1 L).map (mapGL ℝ)) k),
      CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) G = G :=
    fun L _ hL G ↦ _root_.CuspForm.ext fun τ ↦ by simp
  -- `F` is a combination of level-raised newforms with the eigenvalues of `f`
  have hspan := mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul (a := fun p ↦
    if hp : p.Prime ∧ Nat.Coprime p N then f.eigenvalue ⟨p, hp.1.pos⟩ hp.2 else 0)
    fun p hp hpN ↦ by rw [h p hp hpN, dite_eq_left ⟨hp, hpN⟩]
  -- each generator is a multiple of `f`, or lies in another nebentypus space
  have hFmem : F ∈ (ℂ ∙ f.toCuspForm) ⊔
      ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ f.χ), cuspFormCharSpace k ψ := by
    refine Submodule.span_le.mpr ?_ hspan
    rintro _ ⟨M, d, _, _, hdM, g, hg, rfl⟩
    have hMN : M ∣ N := dvd_of_mul_left_dvd hdM
    by_cases hgχ : g.χ.comp (ZMod.unitsMap hMN) = f.χ
    · -- compatible nebentypus: `g` has level `N`, so `g = f` and the generator is `V₁ f = f`
      refine Submodule.mem_sup_left ?_
      have hg' : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
          g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN) = f.eigenvalue ⟨p, hp.pos⟩ hpN :=
        fun p hp hpN ↦ by rw [hg p hp hpN, dite_eq_left ⟨hp, hpN⟩]
      obtain rfl := f.level_eq_of_dvd_of_forall_prime_eigenvalue_eq g.toEigenformAwayFromLevel
        g.isNorm hMN hgχ hg'
      obtain rfl : d = 1 :=
        (mul_left_eq_self₀.mp (Nat.dvd_antisymm hdM (dvd_mul_left _ _))).resolve_right
          (NeZero.ne _)
      rw [ZMod.unitsMap_self, MonoidHom.comp_id] at hgχ
      rw [hV _ hdM, Newform.eq_of_forall_prime_eigenvalue_eq hgχ hg']
      exact Submodule.mem_span_singleton_self _
    · -- otherwise the generator lies in the nebentypus space of `g`, which is not `χ_f`
      exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
        (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace)))
  -- the component in the other nebentypus spaces is `F - c • f ∈ S_k(N, χ)`, hence zero
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hFmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  refine ⟨c, ?_⟩
  have htχ : t ∈ cuspFormCharSpace k f.χ := by
    have := Submodule.sub_mem _ hF (Submodule.smul_mem _ c f.mem_charSpace)
    rwa [add_sub_cancel_left] at this
  have ht0 : t = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) f.χ)) t htχ ht
  rw [ht0, add_zero]

/-! ### The bad-prime eigenvalues -/

/-- **A newform is an eigenvector of `U_p` at every prime `p` dividing the level, with eigenvalue
`a_p(f)`** (Atkin–Lehner–Li; Diamond–Shurman, Theorem 5.8.2; Miyake, Theorem 4.6.13). The
operator `U_p = T_p` commutes with the good `T_q`, so `U_p f` is a good eigenvector of `S_k(N, χ)`
with the eigenvalues of `f`, hence a multiple of `f`; the multiple is the first coefficient
`a₁(U_p f) = a_p(f)`. -/
theorem heckeUCuspNat_eq_qExpansion_coeff_smul (f : Newform N k) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) :
    heckeUCuspNat k p hp hpN f.toCuspForm =
      (qExpansion 1 f.toCuspForm).coeff p • f.toCuspForm := by
  have : NeZero p := ⟨hp.ne_zero⟩
  -- `U_p f`, in `S_k(N, χ)`
  set G : cuspFormCharSpace k f.χ :=
    heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N p) ⟨f.toCuspForm, f.mem_charSpace⟩
    with hG
  have hGcoe : (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeUCuspNat k p hp hpN f.toCuspForm := by
    rw [hG, heckeTCompositeGamma0_prime N hp,
      coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k f.χ hp]
  -- `U_p f` is an eigenvector of every good `T_q`, with the eigenvalues of `f`
  have hGeig : ∀ (q : ℕ) (hq : q.Prime) (hqN : Nat.Coprime q N),
      heckeTCuspNat k q (_hn := ⟨hq.ne_zero⟩) (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        f.eigenvalue ⟨q, hq.pos⟩ hqN • (G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    intro q hq hqN
    have : NeZero q := ⟨hq.ne_zero⟩
    refine heckeTCuspNat_eq_smul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul hq ?_
    have hqp : Nat.Coprime q p :=
      (Nat.coprime_primes hq hp).mpr fun hqp ↦ (hq.coprime_iff_not_dvd.mp hqN) (hqp ▸ hpN)
    have hq' := f.isEigen ⟨q, hq.pos⟩ hqN
    simp only [PNat.mk_coe] at hq'
    -- `T_q T_p = T_{qp} = T_{pq} = T_p T_q` in the Hecke ring
    rw [hG, ← Module.End.mul_apply, ← map_mul, ← heckeTCompositeGamma0_mul_of_coprime N hqp,
      mul_comm q p, heckeTCompositeGamma0_mul_of_coprime N hqp.symm, map_mul,
      Module.End.mul_apply, hq', map_smul]
  obtain ⟨c, hc⟩ := f.exists_eq_smul_of_forall_prime_heckeTCuspNat_eq_smul G.2 hGeig
  rw [hGcoe] at hc
  -- the scalar is `a_p(f)`: read the first coefficient of `U_p f = c • f`
  have hc' := (heckeUCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul k hp hpN c).mp hc 1
  rw [mul_one, f.isNorm, mul_one] at hc'
  rw [hc, hc']

/-! ### The full eigenform -/

/-- **A newform is a full Hecke eigenform** (Diamond–Shurman, Theorem 5.8.2; Miyake, Theorem
4.6.13): the eigenvector equations `U_p f = a_p(f) • f` at the primes dividing the level upgrade
the good eigensystem of a newform to one at every positive index. This is the bridge between
Miyake's *primitive form*, the definition of `Newform` here, and Diamond–Shurman's *newform*,
defined as a normalised full eigenform in the new subspace. -/
noncomputable def toEigenform (f : Newform N k) : Eigenform N k :=
  f.toEigenformAwayFromLevel.toEigenform fun _ hp hpN ↦
    ⟨_, f.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN⟩

@[simp]
theorem toEigenform_toCuspForm (f : Newform N k) : f.toEigenform.toCuspForm = f.toCuspForm :=
  EigenformAwayFromLevel.toEigenform_toCuspForm _ _

@[simp]
theorem toEigenform_χ (f : Newform N k) : f.toEigenform.χ = f.χ :=
  EigenformAwayFromLevel.toEigenform_χ _ _

@[simp]
theorem toEigenform_toEigenformAwayFromLevel (f : Newform N k) :
    f.toEigenform.toEigenformAwayFromLevel = f.toEigenformAwayFromLevel :=
  EigenformAwayFromLevel.toEigenform_toEigenformAwayFromLevel _ _

/-- **The Hecke eigenvalues of a newform are its Fourier coefficients, at every positive index**:
`T_n f = a_n(f) • f` for all `n ≥ 1`, the primes dividing the level included. -/
@[simp]
theorem toEigenform_eigenvalue (f : Newform N k) (n : ℕ+) :
    f.toEigenform.eigenvalue n = (qExpansion 1 f.toCuspForm).coeff n := by
  have h₁ : (qExpansion 1 f.toEigenform.toCuspForm).coeff 1 = 1 := by
    rw [toEigenform_toCuspForm]
    exact f.isNorm
  have h := f.toEigenform.qExpansion_coeff_eq_eigenvalue h₁ n
  rw [toEigenform_toCuspForm] at h
  exact h.symm

/-- **`Tₚ f = aₚ(f) • f` at every prime `p`**, whether or not `p` divides the level. -/
theorem heckeTCuspNat_eq_qExpansion_coeff_smul (f : Newform N k) {p : ℕ} (hp : p.Prime) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f.toCuspForm =
      (qExpansion 1 f.toCuspForm).coeff p • f.toCuspForm := by
  have h := f.toEigenform.heckeTCuspNat_eq_eigenvalue_smul hp
  rw [toEigenform_toCuspForm] at h
  exact h.trans (congrArg (· • f.toCuspForm) (f.toEigenform_eigenvalue ⟨p, hp.pos⟩))

end HeckeRing.GL2.Newform

end
