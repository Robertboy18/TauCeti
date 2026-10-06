/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations.Part00

/-! Certified consequences of the exact M11 presentation relations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Canonical signed word at certificate node 48. -/
abbrev word48 : Word := decode [0, 0, 1, 0, 1, 2, 3, 2, 2, 3, 2, 1, 0, 3]

/-- Node 48 holds in the exact M11 presentation group. -/
theorem word48_eq_one : eval word48 = 1 := by
  have hl : eval (decode [2, 3, 0, 1, 0, 1, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word1_eq_one false
      8 (by decide +kernel)
  have hr : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 1, 2, 3, 2, 2, 3, 2, 1, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [2, 3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 50. -/
abbrev word50 : Word := decode [0, 0, 3, 3, 3, 3, 0, 3, 3, 0, 1, 0, 1, 2, 3, 2, 1]

/-- Node 50 holds in the exact M11 presentation group. -/
theorem word50_eq_one : eval word50 = 1 := by
  have hl : eval (decode [0, 0, 3, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      1 (by decide +kernel)
  have hr : eval (decode [2, 3, 0, 1, 0, 1, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word1_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [0, 0, 3, 3, 3, 3, 0, 3, 3, 0, 1, 0, 1, 2, 3, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 52. -/
abbrev word52 : Word := decode [0, 0, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 0, 3, 0, 1]

/-- Node 52 holds in the exact M11 presentation group. -/
theorem word52_eq_one : eval word52 = 1 := by
  have hl : eval (decode [2, 3, 2, 1, 0, 3, 0, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 0, 3, 0, 1, 0, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 53. -/
abbrev word53 : Word := decode [0, 0, 0, 3, 3, 3, 3, 3, 2, 1, 0, 3, 0, 1, 0, 3, 3]

/-- Node 53 holds in the exact M11 presentation group. -/
theorem word53_eq_one : eval word53 = 1 := by
  have hl : eval (decode [3, 0, 0, 0, 3, 3, 3, 3, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      8 (by decide +kernel)
  have hr : eval (decode [2, 3, 2, 1, 0, 3, 0, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      7 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 0, 3, 3, 3, 3, 3, 2, 1, 0, 3, 0, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 58. -/
abbrev word58 : Word := decode [0, 0, 3, 2, 3, 2, 1, 0, 3, 3, 2, 1, 0, 3, 0, 1]

/-- Node 58 holds in the exact M11 presentation group. -/
theorem word58_eq_one : eval word58 = 1 := by
  have hl : eval (decode [1, 0, 3, 2, 3, 2, 1, 0, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      4 (by decide +kernel)
  have hr : eval (decode [2, 3, 2, 1, 0, 3, 0, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      7 (by decide +kernel)
  have hc : eval (decode [0, 3, 2, 3, 2, 1, 0, 3, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [1])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 62. -/
abbrev word62 : Word := decode [0, 0, 0, 3, 2, 2, 3, 0, 0, 0, 3, 3, 3, 2, 1, 0, 3]

/-- Node 62 holds in the exact M11 presentation group. -/
theorem word62_eq_one : eval word62 = 1 := by
  have hl : eval (decode [3, 0, 1, 1, 1, 2, 2, 2, 1, 0, 0, 3, 3, 3]) = 1 :=
    variant_eq_one word2_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 1, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      2 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 1, 1, 2, 2, 2, 1, 0, 0, 1, 2, 2, 2, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    2 (by decide +kernel)

/-- Canonical signed word at certificate node 70. -/
abbrev word70 : Word := decode [0, 0, 3, 2, 1, 0, 3, 0, 1, 2, 2, 1, 2, 3, 0, 3]

/-- Node 70 holds in the exact M11 presentation group. -/
theorem word70_eq_one : eval word70 = 1 := by
  have hl : eval (decode [2, 2, 2, 1, 2, 3, 0, 3, 0, 0, 0, 1]) = 1 :=
    variant_eq_one word4_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 2, 3, 0, 3, 0, 0, 3, 2, 1, 0, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 73. -/
abbrev word73 : Word := decode [0, 0, 0, 1, 0, 3, 3, 3, 3, 0, 3, 2, 1, 2, 3, 0, 3]

/-- Node 73 holds in the exact M11 presentation group. -/
theorem word73_eq_one : eval word73 = 1 := by
  have hl : eval (decode [0, 3, 3, 3, 3, 0, 3, 0, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      2 (by decide +kernel)
  have hr : eval (decode [2, 2, 2, 1, 2, 3, 0, 3, 0, 0, 0, 1]) = 1 :=
    variant_eq_one word4_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [0, 3, 3, 3, 3, 0, 3, 2, 1, 2, 3, 0, 3, 0, 0, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 74. -/
abbrev word74 : Word := decode [0, 0, 0, 1, 2, 2, 2, 3, 3, 3, 0, 3, 0, 0, 3, 0, 3]

/-- Node 74 holds in the exact M11 presentation group. -/
theorem word74_eq_one : eval word74 = 1 := by
  have hl : eval (decode [0, 0, 0, 3, 2, 2, 2, 1, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word4_eq_one true
      5 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      5 (by decide +kernel)
  have hc : eval (decode [0, 0, 0, 3, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 75. -/
abbrev word75 : Word := decode [0, 0, 0, 0, 3, 2, 2, 2, 1, 2, 2, 1, 2, 3, 0, 1]

/-- Node 75 holds in the exact M11 presentation group. -/
theorem word75_eq_one : eval word75 = 1 := by
  have hl : eval (decode [0, 0, 0, 3, 2, 2, 2, 1, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word4_eq_one true
      5 (by decide +kernel)
  have hr : eval (decode [1, 2, 3, 2, 1, 2, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one false
      3 (by decide +kernel)
  have hc : eval (decode [0, 0, 0, 3, 2, 2, 2, 1, 2, 2, 1, 2, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 76. -/
abbrev word76 : Word := decode [0, 0, 0, 1, 2, 2, 1, 0, 3, 2, 3, 3]

/-- Node 76 holds in the exact M11 presentation group. -/
theorem word76_eq_one : eval word76 = 1 := by
  have hl : eval (decode [0, 0, 0, 3, 2, 2, 2, 1, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word4_eq_one true
      5 (by decide +kernel)
  have hr : eval (decode [1, 2, 3, 0, 1, 0, 1, 2, 3, 2]) = 1 :=
    variant_eq_one word1_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [0, 0, 3, 2, 2, 2, 1, 1, 0, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 79. -/
abbrev word79 : Word := decode [0, 0, 0, 0, 1, 0, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3, 0, 3]

/-- Node 79 holds in the exact M11 presentation group. -/
theorem word79_eq_one : eval word79 = 1 := by
  have hl : eval (decode [2, 2, 1, 2, 3, 0, 3, 0, 0, 0, 1, 2]) = 1 :=
    variant_eq_one word4_eq_one false
      5 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 3, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word1_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 2, 3, 0, 3, 0, 0, 0, 0, 1, 0, 3, 2, 3, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 82. -/
abbrev word82 : Word := decode [0, 0, 0, 3, 2, 2, 1, 0, 3, 2, 3, 2, 1, 1, 0, 3]

/-- Node 82 holds in the exact M11 presentation group. -/
theorem word82_eq_one : eval word82 = 1 := by
  have hl : eval (decode [1, 0, 3, 0, 0, 0, 3, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word4_eq_one true
      2 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 3, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word1_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 0, 0, 0, 3, 2, 2, 1, 0, 3, 2, 3, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 91. -/
abbrev word91 : Word := decode [0, 0, 0, 1, 1, 2, 2, 1, 0, 3, 2, 3, 2, 3, 0, 3]

/-- Node 91 holds in the exact M11 presentation group. -/
theorem word91_eq_one : eval word91 = 1 := by
  have hl : eval (decode [3, 0, 3, 0, 0, 0, 1, 1, 2, 2, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word5_eq_one false
      11 (by decide +kernel)
  have hr : eval (decode [1, 0, 3, 0, 1, 0, 3, 2, 3, 2]) = 1 :=
    variant_eq_one word1_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [3, 0, 3, 0, 0, 0, 1, 1, 2, 2, 1, 0, 3, 2, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 103. -/
abbrev word103 : Word := decode [0, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1, 0, 3, 3, 3, 3]

/-- Node 103 holds in the exact M11 presentation group. -/
theorem word103_eq_one : eval word103 = 1 := by
  have hl : eval (decode [1, 1, 1, 1, 0, 3, 3, 3, 3, 0, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word11_eq_one true
      2 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 3, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word1_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 1, 0, 3, 3, 3, 3, 0, 0, 3, 2, 3, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 104. -/
abbrev word104 : Word := decode [0, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 0, 3, 3, 2, 1, 0, 3]

/-- Node 104 holds in the exact M11 presentation group. -/
theorem word104_eq_one : eval word104 = 1 := by
  have hl : eval (decode [3, 2, 1, 0, 3, 0, 1, 0, 3, 2]) = 1 :=
    variant_eq_one word1_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 0, 3]) = 1 :=
    variant_eq_one word11_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 0, 3, 0, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 111. -/
abbrev word111 : Word := decode [0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 0, 3, 2, 2, 2, 1, 1]

/-- Node 111 holds in the exact M11 presentation group. -/
theorem word111_eq_one : eval word111 = 1 := by
  have hl : eval (decode [3, 0, 0, 0, 1, 2, 2, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word4_eq_one false
      11 (by decide +kernel)
  have hr : eval (decode [2, 1, 0, 3, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]) = 1 :=
    variant_eq_one word12_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 0, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 112. -/
abbrev word112 : Word := decode [0, 0, 3, 0, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1]

/-- Node 112 holds in the exact M11 presentation group. -/
theorem word112_eq_one : eval word112 = 1 := by
  have hl : eval (decode [1, 2, 3, 0, 1, 0, 1, 2, 3, 2]) = 1 :=
    variant_eq_one word1_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 3, 3, 3, 0, 3, 0, 0, 3, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word14_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 3, 2, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [1])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 115. -/
abbrev word115 : Word := decode [0, 0, 0, 3, 3, 2, 3, 2, 1, 2, 2, 3, 0, 1, 0, 0, 3]

/-- Node 115 holds in the exact M11 presentation group. -/
theorem word115_eq_one : eval word115 = 1 := by
  have hl : eval (decode [1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 0, 3, 0, 1, 0, 1]) = 1 :=
    variant_eq_one word16_eq_one true
      12 (by decide +kernel)
  have hr : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 0, 0, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 116. -/
abbrev word116 : Word := decode [0, 0, 0, 3, 2, 3, 2, 1, 2, 2, 3, 0, 1, 0, 3, 0, 3]

/-- Node 116 holds in the exact M11 presentation group. -/
theorem word116_eq_one : eval word116 = 1 := by
  have hl : eval (decode [2, 3, 0, 1, 0, 3, 0, 3, 0, 0, 0, 3, 3, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word17_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 0, 1, 2, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word1_eq_one false
      9 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 1, 0, 3, 0, 3, 0, 0, 0, 3, 2, 3, 2, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 119. -/
abbrev word119 : Word := decode [0, 0, 0, 1, 0, 3, 3, 3, 3, 0, 0, 3, 2, 3, 3]

/-- Node 119 holds in the exact M11 presentation group. -/
theorem word119_eq_one : eval word119 = 1 := by
  have hl : eval (decode [1, 2, 2, 2, 1, 1, 0, 1, 2, 3, 2, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word21_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [3, 3, 0, 3, 0, 1, 2, 1, 1, 1, 1, 2, 3, 3]) = 1 :=
    variant_eq_one word11_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [2, 2, 2, 1, 1, 0, 1, 2, 2, 1, 1, 1, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [1])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 120. -/
abbrev word120 : Word := decode [0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 2, 1, 0, 3, 2, 3, 3]

/-- Node 120 holds in the exact M11 presentation group. -/
theorem word120_eq_one : eval word120 = 1 := by
  have hl : eval (decode [1, 0, 3, 2, 3, 3, 0, 0, 0, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word21_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 1, 1, 1, 0, 0, 0, 3, 3, 3, 3, 2]) = 1 :=
    variant_eq_one word8_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 2, 3, 3, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 121. -/
abbrev word121 : Word := decode [0, 0, 3, 2, 1, 0, 3, 0, 1, 2, 1, 0, 3, 2, 3, 3]

/-- Node 121 holds in the exact M11 presentation group. -/
theorem word121_eq_one : eval word121 = 1 := by
  have hl : eval (decode [1, 0, 3, 2, 3, 3, 0, 0, 0, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word21_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 1, 1, 1, 2, 3, 2, 1, 0, 3, 0, 1, 2]) = 1 :=
    variant_eq_one word14_eq_one true
      14 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 2, 3, 3, 0, 0, 3, 2, 1, 0, 3, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 124. -/
abbrev word124 : Word := decode [0, 0, 1, 0, 3, 2, 3, 0, 3, 3, 3, 3, 3, 0, 1]

/-- Node 124 holds in the exact M11 presentation group. -/
theorem word124_eq_one : eval word124 = 1 := by
  have hl : eval (decode [3, 0, 1, 0, 3, 2, 3, 0, 3, 3, 3, 3, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word24_eq_one false
      3 (by decide +kernel)
  have hr : eval (decode [2, 3, 2, 1, 2, 3, 0, 1, 0, 1]) = 1 :=
    variant_eq_one word1_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 3, 2, 3, 0, 3, 3, 3, 3, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 125. -/
abbrev word125 : Word := decode [0, 0, 0, 1, 2, 1, 0, 1, 2, 3, 2, 2, 3, 3]

/-- Node 125 holds in the exact M11 presentation group. -/
theorem word125_eq_one : eval word125 = 1 := by
  have hl : eval (decode [3, 0, 1, 0, 3, 2, 3, 0, 3, 3, 3, 3, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word24_eq_one false
      3 (by decide +kernel)
  have hr : eval (decode [2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1]) = 1 :=
    variant_eq_one word21_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 3, 2, 3, 0, 3, 2, 2, 2, 1, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 126. -/
abbrev word126 : Word := decode [0, 0, 0, 1, 1, 2, 1, 0, 1, 2, 3, 2, 2, 3, 2, 3, 0, 3]

/-- Node 126 holds in the exact M11 presentation group. -/
theorem word126_eq_one : eval word126 = 1 := by
  have hl : eval (decode [2, 2, 2, 1, 2, 1, 0, 1, 0, 1, 2, 3, 2, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word20_eq_one true
      14 (by decide +kernel)
  have hr : eval (decode [3, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 0, 3, 3]) = 1 :=
    variant_eq_one word24_eq_one false
      13 (by decide +kernel)
  have hc : eval (decode [2, 2, 2, 1, 2, 1, 0, 1, 0, 0, 1, 0, 3, 2, 3, 0, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 128. -/
abbrev word128 : Word := decode [0, 0, 0, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 1, 0, 1, 2, 3]

/-- Node 128 holds in the exact M11 presentation group. -/
theorem word128_eq_one : eval word128 = 1 := by
  have hl : eval (decode [2, 2, 1, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word26_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 3, 0, 1, 0, 3, 2]) = 1 :=
    variant_eq_one word25_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 0, 3, 2, 3, 3, 0, 0, 1, 0, 3, 0, 1, 0, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    16 (by decide +kernel)

/-- Canonical signed word at certificate node 129. -/
abbrev word129 : Word := decode [0, 0, 0, 3, 3, 0, 1, 2, 3, 0, 0, 3, 2, 2, 3]

/-- Node 129 holds in the exact M11 presentation group. -/
theorem word129_eq_one : eval word129 = 1 := by
  have hl : eval (decode [1, 2, 2, 1, 0, 3, 2, 3, 2, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word26_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [3, 3, 3, 3, 0, 1, 1, 1, 2, 2, 2, 1, 0, 0]) = 1 :=
    variant_eq_one word2_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [1, 2, 2, 1, 0, 3, 2, 1, 1, 2, 2, 2, 1, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 130. -/
abbrev word130 : Word := decode [0, 0, 3, 0, 3, 3, 3, 3, 0, 3, 2, 1, 1, 0, 1, 2, 3]

/-- Node 130 holds in the exact M11 presentation group. -/
theorem word130_eq_one : eval word130 = 1 := by
  have hl : eval (decode [1, 2, 2, 1, 0, 3, 2, 3, 2, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word26_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [3, 3, 3, 3, 0, 3, 0, 1, 2, 1, 1, 1, 1, 2]) = 1 :=
    variant_eq_one word11_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [1, 2, 2, 1, 0, 3, 2, 3, 3, 0, 1, 2, 1, 1, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 133. -/
abbrev word133 : Word := decode [0, 0, 0, 1, 2, 2, 1, 0, 3, 2, 1, 2, 2, 2, 1, 2, 1]

/-- Node 133 holds in the exact M11 presentation group. -/
theorem word133_eq_one : eval word133 = 1 := by
  have hl : eval (decode [1, 2, 2, 1, 0, 3, 2, 3, 2, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word26_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [3, 3, 3, 3, 0, 1, 1, 2, 2, 2, 1, 2, 1, 0, 0, 0]) = 1 :=
    variant_eq_one word3_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [1, 2, 2, 1, 0, 3, 2, 1, 2, 2, 2, 1, 2, 1, 0, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 135. -/
abbrev word135 : Word := decode [0, 0, 3, 3, 3, 3, 2, 3, 0, 1, 0, 1, 1, 2, 3]

/-- Node 135 holds in the exact M11 presentation group. -/
theorem word135_eq_one : eval word135 = 1 := by
  have hl : eval (decode [1, 2, 3, 0, 0, 3, 3, 3, 3, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word26_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [2, 3, 2, 1, 2, 3, 0, 1, 0, 1]) = 1 :=
    variant_eq_one word1_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [1, 2, 3, 0, 0, 3, 3, 3, 3, 2, 3, 0, 1, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 146. -/
abbrev word146 : Word := decode [0, 1, 0, 1, 1, 2, 3, 2, 3, 3, 3, 0, 3, 0, 3]

/-- Node 146 holds in the exact M11 presentation group. -/
theorem word146_eq_one : eval word146 = 1 := by
  have hl : eval (decode [3, 0, 1, 0, 1, 2, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word1_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word30_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 0, 1, 1, 2, 3, 2, 3, 3, 3, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
