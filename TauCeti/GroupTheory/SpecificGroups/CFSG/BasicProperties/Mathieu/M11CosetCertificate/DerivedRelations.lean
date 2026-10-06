/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations.Part06

/-! The order-eight relation and the certified M11 relation family. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

open Sporadic

/-- Concrete power relation certified by dependency node 884. -/
theorem x_pow_eight : x ^ 8 = 1 := by
  have hword : word884 = (List.replicate 8
      (decode [0, 3])).flatten := by decide +kernel
  have h := word884_eq_one
  rw [hword, eval_replicate, eval_abinv] at h
  exact h

/-- Closed-word block 0 of the selected dependency DAG. -/
@[expose]
def wordsBlock0 : List Word :=
  [word0, word1, word2, word3, word4, word5, word6, word7,
    word8, word9, word11, word12, word14, word15, word16, word17]

private theorem wordsBlock0_eq_one : ∀ w ∈ wordsBlock0, eval w = 1 := by
  intro w hw
  simp only [wordsBlock0, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word0_eq_one
  · exact word1_eq_one
  · exact word2_eq_one
  · exact word3_eq_one
  · exact word4_eq_one
  · exact word5_eq_one
  · exact word6_eq_one
  · exact word7_eq_one
  · exact word8_eq_one
  · exact word9_eq_one
  · exact word11_eq_one
  · exact word12_eq_one
  · exact word14_eq_one
  · exact word15_eq_one
  · exact word16_eq_one
  · exact word17_eq_one

/-- Closed-word block 1 of the selected dependency DAG. -/
@[expose]
def wordsBlock1 : List Word :=
  [word18, word19, word20, word21, word24, word25, word26, word28,
    word30, word32, word33, word35, word36, word38, word45, word46]

private theorem wordsBlock1_eq_one : ∀ w ∈ wordsBlock1, eval w = 1 := by
  intro w hw
  simp only [wordsBlock1, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word18_eq_one
  · exact word19_eq_one
  · exact word20_eq_one
  · exact word21_eq_one
  · exact word24_eq_one
  · exact word25_eq_one
  · exact word26_eq_one
  · exact word28_eq_one
  · exact word30_eq_one
  · exact word32_eq_one
  · exact word33_eq_one
  · exact word35_eq_one
  · exact word36_eq_one
  · exact word38_eq_one
  · exact word45_eq_one
  · exact word46_eq_one

/-- Closed-word block 2 of the selected dependency DAG. -/
@[expose]
def wordsBlock2 : List Word :=
  [word48, word50, word52, word53, word58, word62, word70, word73,
    word74, word75, word76, word79, word82, word91, word103, word104]

private theorem wordsBlock2_eq_one : ∀ w ∈ wordsBlock2, eval w = 1 := by
  intro w hw
  simp only [wordsBlock2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word48_eq_one
  · exact word50_eq_one
  · exact word52_eq_one
  · exact word53_eq_one
  · exact word58_eq_one
  · exact word62_eq_one
  · exact word70_eq_one
  · exact word73_eq_one
  · exact word74_eq_one
  · exact word75_eq_one
  · exact word76_eq_one
  · exact word79_eq_one
  · exact word82_eq_one
  · exact word91_eq_one
  · exact word103_eq_one
  · exact word104_eq_one

/-- Closed-word block 3 of the selected dependency DAG. -/
@[expose]
def wordsBlock3 : List Word :=
  [word111, word112, word115, word116, word119, word120, word121, word124,
    word125, word126, word128, word129, word130, word133, word135, word146]

private theorem wordsBlock3_eq_one : ∀ w ∈ wordsBlock3, eval w = 1 := by
  intro w hw
  simp only [wordsBlock3, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word111_eq_one
  · exact word112_eq_one
  · exact word115_eq_one
  · exact word116_eq_one
  · exact word119_eq_one
  · exact word120_eq_one
  · exact word121_eq_one
  · exact word124_eq_one
  · exact word125_eq_one
  · exact word126_eq_one
  · exact word128_eq_one
  · exact word129_eq_one
  · exact word130_eq_one
  · exact word133_eq_one
  · exact word135_eq_one
  · exact word146_eq_one

/-- Closed-word block 4 of the selected dependency DAG. -/
@[expose]
def wordsBlock4 : List Word :=
  [word148, word149, word153, word165, word167, word168, word175, word178,
    word182, word184, word185, word197, word204, word205, word206, word207]

private theorem wordsBlock4_eq_one : ∀ w ∈ wordsBlock4, eval w = 1 := by
  intro w hw
  simp only [wordsBlock4, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word148_eq_one
  · exact word149_eq_one
  · exact word153_eq_one
  · exact word165_eq_one
  · exact word167_eq_one
  · exact word168_eq_one
  · exact word175_eq_one
  · exact word178_eq_one
  · exact word182_eq_one
  · exact word184_eq_one
  · exact word185_eq_one
  · exact word197_eq_one
  · exact word204_eq_one
  · exact word205_eq_one
  · exact word206_eq_one
  · exact word207_eq_one

/-- Closed-word block 5 of the selected dependency DAG. -/
@[expose]
def wordsBlock5 : List Word :=
  [word218, word219, word223, word224, word225, word227, word231, word238,
    word241, word242, word243, word244, word247, word249, word250, word251]

private theorem wordsBlock5_eq_one : ∀ w ∈ wordsBlock5, eval w = 1 := by
  intro w hw
  simp only [wordsBlock5, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word218_eq_one
  · exact word219_eq_one
  · exact word223_eq_one
  · exact word224_eq_one
  · exact word225_eq_one
  · exact word227_eq_one
  · exact word231_eq_one
  · exact word238_eq_one
  · exact word241_eq_one
  · exact word242_eq_one
  · exact word243_eq_one
  · exact word244_eq_one
  · exact word247_eq_one
  · exact word249_eq_one
  · exact word250_eq_one
  · exact word251_eq_one

/-- Closed-word block 6 of the selected dependency DAG. -/
@[expose]
def wordsBlock6 : List Word :=
  [word253, word254, word256, word259, word261, word262, word265, word266,
    word274, word279, word280, word281, word282, word284, word285, word293]

private theorem wordsBlock6_eq_one : ∀ w ∈ wordsBlock6, eval w = 1 := by
  intro w hw
  simp only [wordsBlock6, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word253_eq_one
  · exact word254_eq_one
  · exact word256_eq_one
  · exact word259_eq_one
  · exact word261_eq_one
  · exact word262_eq_one
  · exact word265_eq_one
  · exact word266_eq_one
  · exact word274_eq_one
  · exact word279_eq_one
  · exact word280_eq_one
  · exact word281_eq_one
  · exact word282_eq_one
  · exact word284_eq_one
  · exact word285_eq_one
  · exact word293_eq_one

/-- Closed-word block 7 of the selected dependency DAG. -/
@[expose]
def wordsBlock7 : List Word :=
  [word294, word296, word297, word298, word302, word309, word311, word313,
    word318, word321, word323, word325, word329, word330, word333, word334]

private theorem wordsBlock7_eq_one : ∀ w ∈ wordsBlock7, eval w = 1 := by
  intro w hw
  simp only [wordsBlock7, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word294_eq_one
  · exact word296_eq_one
  · exact word297_eq_one
  · exact word298_eq_one
  · exact word302_eq_one
  · exact word309_eq_one
  · exact word311_eq_one
  · exact word313_eq_one
  · exact word318_eq_one
  · exact word321_eq_one
  · exact word323_eq_one
  · exact word325_eq_one
  · exact word329_eq_one
  · exact word330_eq_one
  · exact word333_eq_one
  · exact word334_eq_one

/-- Closed-word block 8 of the selected dependency DAG. -/
@[expose]
def wordsBlock8 : List Word :=
  [word337, word340, word342, word344, word346, word351, word358, word359,
    word361, word368, word369, word373, word375, word376, word378, word379]

private theorem wordsBlock8_eq_one : ∀ w ∈ wordsBlock8, eval w = 1 := by
  intro w hw
  simp only [wordsBlock8, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word337_eq_one
  · exact word340_eq_one
  · exact word342_eq_one
  · exact word344_eq_one
  · exact word346_eq_one
  · exact word351_eq_one
  · exact word358_eq_one
  · exact word359_eq_one
  · exact word361_eq_one
  · exact word368_eq_one
  · exact word369_eq_one
  · exact word373_eq_one
  · exact word375_eq_one
  · exact word376_eq_one
  · exact word378_eq_one
  · exact word379_eq_one

/-- Closed-word block 9 of the selected dependency DAG. -/
@[expose]
def wordsBlock9 : List Word :=
  [word380, word385, word388, word391, word394, word395, word396, word397,
    word398, word399, word400, word401, word402, word403, word408, word410]

private theorem wordsBlock9_eq_one : ∀ w ∈ wordsBlock9, eval w = 1 := by
  intro w hw
  simp only [wordsBlock9, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word380_eq_one
  · exact word385_eq_one
  · exact word388_eq_one
  · exact word391_eq_one
  · exact word394_eq_one
  · exact word395_eq_one
  · exact word396_eq_one
  · exact word397_eq_one
  · exact word398_eq_one
  · exact word399_eq_one
  · exact word400_eq_one
  · exact word401_eq_one
  · exact word402_eq_one
  · exact word403_eq_one
  · exact word408_eq_one
  · exact word410_eq_one

/-- Closed-word block 10 of the selected dependency DAG. -/
@[expose]
def wordsBlock10 : List Word :=
  [word411, word412, word413, word414, word415, word416, word417, word419,
    word420, word421, word422, word426, word432, word434, word435, word437]

private theorem wordsBlock10_eq_one : ∀ w ∈ wordsBlock10, eval w = 1 := by
  intro w hw
  simp only [wordsBlock10, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word411_eq_one
  · exact word412_eq_one
  · exact word413_eq_one
  · exact word414_eq_one
  · exact word415_eq_one
  · exact word416_eq_one
  · exact word417_eq_one
  · exact word419_eq_one
  · exact word420_eq_one
  · exact word421_eq_one
  · exact word422_eq_one
  · exact word426_eq_one
  · exact word432_eq_one
  · exact word434_eq_one
  · exact word435_eq_one
  · exact word437_eq_one

/-- Closed-word block 11 of the selected dependency DAG. -/
@[expose]
def wordsBlock11 : List Word :=
  [word438, word439, word440, word443, word445, word446, word448, word449,
    word451, word452, word461, word462, word465, word476, word478, word482]

private theorem wordsBlock11_eq_one : ∀ w ∈ wordsBlock11, eval w = 1 := by
  intro w hw
  simp only [wordsBlock11, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word438_eq_one
  · exact word439_eq_one
  · exact word440_eq_one
  · exact word443_eq_one
  · exact word445_eq_one
  · exact word446_eq_one
  · exact word448_eq_one
  · exact word449_eq_one
  · exact word451_eq_one
  · exact word452_eq_one
  · exact word461_eq_one
  · exact word462_eq_one
  · exact word465_eq_one
  · exact word476_eq_one
  · exact word478_eq_one
  · exact word482_eq_one

/-- Closed-word block 12 of the selected dependency DAG. -/
@[expose]
def wordsBlock12 : List Word :=
  [word484, word490, word500, word512, word523, word525, word530, word538,
    word555, word598, word611, word613, word615, word617, word619, word642]

private theorem wordsBlock12_eq_one : ∀ w ∈ wordsBlock12, eval w = 1 := by
  intro w hw
  simp only [wordsBlock12, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact word484_eq_one
  · exact word490_eq_one
  · exact word500_eq_one
  · exact word512_eq_one
  · exact word523_eq_one
  · exact word525_eq_one
  · exact word530_eq_one
  · exact word538_eq_one
  · exact word555_eq_one
  · exact word598_eq_one
  · exact word611_eq_one
  · exact word613_eq_one
  · exact word615_eq_one
  · exact word617_eq_one
  · exact word619_eq_one
  · exact word642_eq_one

/-- Closed-word block 13 of the selected dependency DAG. -/
@[expose]
def wordsBlock13 : List Word :=
  [word646, word687, word691, word736, word845, word856, word884, word1014,
    word1015, word1085, word1145, word1163, word1165, word1167]

private theorem wordsBlock13_eq_one : ∀ w ∈ wordsBlock13, eval w = 1 := by
  intro w hw
  simp only [wordsBlock13, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact word646_eq_one
  · exact word687_eq_one
  · exact word691_eq_one
  · exact word736_eq_one
  · exact word845_eq_one
  · exact word856_eq_one
  · exact word884_eq_one
  · exact word1014_eq_one
  · exact word1015_eq_one
  · exact word1085_eq_one
  · exact word1145_eq_one
  · exact word1163_eq_one
  · exact word1165_eq_one
  · exact word1167_eq_one

/-- All words in the selected dependency DAG. -/
@[expose]
def derivedWords : List Word :=
  wordsBlock0 ++
    wordsBlock1 ++
    wordsBlock2 ++
    wordsBlock3 ++
    wordsBlock4 ++
    wordsBlock5 ++
    wordsBlock6 ++
    wordsBlock7 ++
    wordsBlock8 ++
    wordsBlock9 ++
    wordsBlock10 ++
    wordsBlock11 ++
    wordsBlock12 ++
    wordsBlock13

/-- Exact-group soundness, in the shape required by `extraRelators`. -/
theorem derivedWords_eq_one : ∀ w ∈ derivedWords,
    PresentedGroup.mk m11Presentation.relatorSet (FreeGroup.mk w) = 1 := by
  intro w hw
  simp only [derivedWords, List.mem_append, or_assoc] at hw
  rcases hw with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h
  · exact wordsBlock0_eq_one w h
  · exact wordsBlock1_eq_one w h
  · exact wordsBlock2_eq_one w h
  · exact wordsBlock3_eq_one w h
  · exact wordsBlock4_eq_one w h
  · exact wordsBlock5_eq_one w h
  · exact wordsBlock6_eq_one w h
  · exact wordsBlock7_eq_one w h
  · exact wordsBlock8_eq_one w h
  · exact wordsBlock9_eq_one w h
  · exact wordsBlock10_eq_one w h
  · exact wordsBlock11_eq_one w h
  · exact wordsBlock12_eq_one w h
  · exact wordsBlock13_eq_one w h

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
