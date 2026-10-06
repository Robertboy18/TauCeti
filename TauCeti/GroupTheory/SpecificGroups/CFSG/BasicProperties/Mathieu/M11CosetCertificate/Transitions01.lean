/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits1
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions0
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership00

/-!
# M11 coset deductions: transition group 01

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible008 : deductions008.all eligible = true := by
  simp only [deductions008, List.all_cons, List.all_nil, eligible, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_008 :
    deductions008.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits008 =
      bits009 := by
  decide +kernel

theorem eligible009 : deductions009.all eligible = true := by
  simp only [deductions009, List.all_cons, List.all_nil, eligible, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_009 :
    deductions009.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits009 =
      bits010 := by
  decide +kernel

theorem eligible010 : deductions010.all eligible = true := by
  simp only [deductions010, List.all_cons, List.all_nil, eligible, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_010 :
    deductions010.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits010 =
      bits011 := by
  decide +kernel

theorem eligible011 : deductions011.all eligible = true := by
  simp only [deductions011, List.all_cons, List.all_nil, eligible, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_011 :
    deductions011.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits011 =
      bits012 := by
  decide +kernel

theorem eligible012 : deductions012.all eligible = true := by
  simp only [deductions012, List.all_cons, List.all_nil, eligible, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_012 :
    deductions012.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits012 =
      bits013 := by
  decide +kernel

theorem eligible013 : deductions013.all eligible = true := by
  simp only [deductions013, List.all_cons, List.all_nil, eligible, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_013 :
    deductions013.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits013 =
      bits014 := by
  decide +kernel

theorem eligible014 : deductions014.all eligible = true := by
  simp only [deductions014, List.all_cons, List.all_nil, eligible, r1_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_014 :
    deductions014.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits014 =
      bits015 := by
  decide +kernel

theorem eligible015 : deductions015.all eligible = true := by
  simp only [deductions015, List.all_cons, List.all_nil, eligible, r1_mem, r2_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_015 :
    deductions015.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits015 =
      bits016 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
