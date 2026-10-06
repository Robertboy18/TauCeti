/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits5
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions5
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership07
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership08

/-!
# M11 coset deductions: transition group 10

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible080 : deductions080.all eligible = true := by
  simp only [deductions080, List.all_cons, List.all_nil, eligible, r506_mem, r507_mem, r508_mem,
    r509_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_080 :
    deductions080.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits080 =
      bits081 := by
  decide +kernel

theorem eligible081 : deductions081.all eligible = true := by
  simp only [deductions081, List.all_cons, List.all_nil, eligible, r509_mem, r510_mem, r511_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_081 :
    deductions081.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits081 =
      bits082 := by
  decide +kernel

theorem eligible082 : deductions082.all eligible = true := by
  simp only [deductions082, List.all_cons, List.all_nil, eligible, r511_mem, r512_mem, r513_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_082 :
    deductions082.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits082 =
      bits083 := by
  decide +kernel

theorem eligible083 : deductions083.all eligible = true := by
  simp only [deductions083, List.all_cons, List.all_nil, eligible, r513_mem, r514_mem, r515_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_083 :
    deductions083.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits083 =
      bits084 := by
  decide +kernel

theorem eligible084 : deductions084.all eligible = true := by
  simp only [deductions084, List.all_cons, List.all_nil, eligible, r515_mem, r516_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_084 :
    deductions084.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits084 =
      bits085 := by
  decide +kernel

theorem eligible085 : deductions085.all eligible = true := by
  simp only [deductions085, List.all_cons, List.all_nil, eligible, r516_mem, r517_mem, r518_mem,
    r519_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_085 :
    deductions085.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits085 =
      bits086 := by
  decide +kernel

theorem eligible086 : deductions086.all eligible = true := by
  simp only [deductions086, List.all_cons, List.all_nil, eligible, r520_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_086 :
    deductions086.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits086 =
      bits087 := by
  decide +kernel

theorem eligible087 : deductions087.all eligible = true := by
  simp only [deductions087, List.all_cons, List.all_nil, eligible, r520_mem, r521_mem, r522_mem,
    r523_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_087 :
    deductions087.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits087 =
      bits088 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
