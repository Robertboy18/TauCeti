/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits3
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Deductions2
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Eligibility
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership00
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership01
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership02
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership03
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelatorMembership04

/-!
# M11 coset deductions: transition group 05

Each block proves word eligibility and a transition between two literal bit states.
The individual computations remain separate so each kernel check covers at most
32 deductions. Their composition is proved in `M11CosetCertificate`.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem eligible040 : deductions040.all eligible = true := by
  simp only [deductions040, List.all_cons, List.all_nil, eligible, r30_mem, r32_mem, r34_mem,
    r36_mem, r37_mem, r38_mem, r39_mem, r41_mem, r42_mem, r43_mem, r44_mem, r45_mem, r48_mem,
    r49_mem, r50_mem, r51_mem, r52_mem, r53_mem, r57_mem, r58_mem, r61_mem, r63_mem, r67_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_040 :
    deductions040.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits040 =
      bits041 := by
  decide +kernel

theorem eligible041 : deductions041.all eligible = true := by
  simp only [deductions041, List.all_cons, List.all_nil, eligible, r67_mem, r68_mem, r69_mem,
    r70_mem, r71_mem, r72_mem, r73_mem, r74_mem, r75_mem, r76_mem, r78_mem, r79_mem, r80_mem,
    r81_mem, r82_mem, r83_mem, r84_mem, r85_mem, r86_mem, r87_mem, r91_mem, r92_mem, r93_mem,
    r94_mem, r95_mem, r97_mem, r98_mem, r99_mem, r100_mem, r101_mem, decide_true, Bool.true_or,
    Bool.true_and]

theorem transition_041 :
    deductions041.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits041 =
      bits042 := by
  decide +kernel

theorem eligible042 : deductions042.all eligible = true := by
  simp only [deductions042, List.all_cons, List.all_nil, eligible, r102_mem, r103_mem, r104_mem,
    r105_mem, r106_mem, r107_mem, r108_mem, r109_mem, r110_mem, r112_mem, r114_mem, r115_mem,
    r116_mem, r117_mem, r118_mem, r119_mem, r120_mem, r122_mem, r123_mem, r124_mem, r125_mem,
    r126_mem, r127_mem, r128_mem, r129_mem, r130_mem, r131_mem, decide_true, Bool.true_or,
    Bool.true_and]

theorem transition_042 :
    deductions042.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits042 =
      bits043 := by
  decide +kernel

theorem eligible043 : deductions043.all eligible = true := by
  simp only [deductions043, List.all_cons, List.all_nil, eligible, r132_mem, r133_mem, r134_mem,
    r135_mem, r136_mem, r137_mem, r138_mem, r139_mem, r140_mem, r141_mem, r142_mem, r144_mem,
    r145_mem, r146_mem, r147_mem, r148_mem, r149_mem, r150_mem, r151_mem, r152_mem, r153_mem,
    r154_mem, r155_mem, r156_mem, r157_mem, r158_mem, r159_mem, r160_mem, r161_mem, r162_mem,
    decide_true, Bool.true_or, Bool.true_and]

theorem transition_043 :
    deductions043.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits043 =
      bits044 := by
  decide +kernel

theorem eligible044 : deductions044.all eligible = true := by
  simp only [deductions044, List.all_cons, List.all_nil, eligible, r163_mem, r164_mem, r165_mem,
    r166_mem, r167_mem, r168_mem, r169_mem, r170_mem, r171_mem, r172_mem, r173_mem, r174_mem,
    r175_mem, r176_mem, r177_mem, r178_mem, r179_mem, r180_mem, r181_mem, r182_mem, r183_mem,
    r184_mem, r185_mem, r186_mem, r187_mem, r188_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_044 :
    deductions044.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits044 =
      bits045 := by
  decide +kernel

theorem eligible045 : deductions045.all eligible = true := by
  simp only [deductions045, List.all_cons, List.all_nil, eligible, r189_mem, r190_mem, r191_mem,
    r192_mem, r193_mem, r194_mem, r195_mem, r196_mem, r197_mem, r198_mem, r199_mem, r200_mem,
    r201_mem, r203_mem, r204_mem, r205_mem, r206_mem, r207_mem, r208_mem, r209_mem, r210_mem,
    r211_mem, r212_mem, r213_mem, r214_mem, r215_mem, r216_mem, r217_mem, decide_true,
    Bool.true_or, Bool.true_and]

theorem transition_045 :
    deductions045.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits045 =
      bits046 := by
  decide +kernel

theorem eligible046 : deductions046.all eligible = true := by
  simp only [deductions046, List.all_cons, List.all_nil, eligible, r218_mem, r219_mem, r220_mem,
    r221_mem, r222_mem, r223_mem, r224_mem, r225_mem, r226_mem, r227_mem, r228_mem, r229_mem,
    r230_mem, r231_mem, r232_mem, r233_mem, r234_mem, r235_mem, r236_mem, r237_mem, r238_mem,
    r239_mem, r241_mem, r242_mem, r243_mem, r244_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_046 :
    deductions046.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits046 =
      bits047 := by
  decide +kernel

theorem eligible047 : deductions047.all eligible = true := by
  simp only [deductions047, List.all_cons, List.all_nil, eligible, r245_mem, r246_mem, r247_mem,
    r248_mem, r249_mem, r250_mem, r251_mem, r252_mem, r253_mem, r254_mem, r255_mem, r256_mem,
    r257_mem, r258_mem, r259_mem, r260_mem, r261_mem, r262_mem, r263_mem, r264_mem, r265_mem,
    r266_mem, r267_mem, r268_mem, r269_mem, decide_true, Bool.true_or, Bool.true_and]

theorem transition_047 :
    deductions047.foldl (fun s c ↦ deduceBits table s c.1 c.2) bits047 =
      bits048 := by
  decide +kernel

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
