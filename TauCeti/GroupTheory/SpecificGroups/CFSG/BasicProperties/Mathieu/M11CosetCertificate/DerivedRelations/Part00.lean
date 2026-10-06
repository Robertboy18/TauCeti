/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Word

/-! Certified consequences of the exact M11 presentation relations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Canonical signed word at certificate node 0. -/
abbrev word0 : Word := decode [0, 0, 0, 3, 3, 3, 3, 0, 3]

/-- Node 0 holds in the exact M11 presentation group. -/
theorem word0_eq_one : eval word0 = 1 := by
  have hc : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      original0_eq_one (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 1. -/
abbrev word1 : Word := decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]

/-- Node 1 holds in the exact M11 presentation group. -/
theorem word1_eq_one : eval word1 = 1 := by
  have hc : eval (decode [1, 0, 3, 2, 3, 2, 1, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      original1_eq_one (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 2. -/
abbrev word2 : Word := decode [0, 0, 0, 3, 3, 3, 2, 1, 1, 1, 1, 2, 2, 3]

/-- Node 2 holds in the exact M11 presentation group. -/
theorem word2_eq_one : eval word2 = 1 := by
  have hl : eval (decode [1, 1, 1, 2, 2, 2, 1, 2, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 0, 3, 3, 3, 3, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 2, 2, 2, 1, 0, 0, 3, 3, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 3. -/
abbrev word3 : Word := decode [0, 0, 0, 3, 3, 2, 1, 1, 1, 1, 2, 2, 2, 3, 0, 3]

/-- Node 3 holds in the exact M11 presentation group. -/
theorem word3_eq_one : eval word3 = 1 := by
  have hl : eval (decode [1, 1, 2, 2, 2, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      4 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 0, 3, 3, 3, 3, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 2, 2, 1, 2, 1, 0, 0, 0, 3, 3, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 4. -/
abbrev word4 : Word := decode [0, 0, 0, 1, 2, 2, 2, 1, 2, 3, 0, 3]

/-- Node 4 holds in the exact M11 presentation group. -/
theorem word4_eq_one : eval word4 = 1 := by
  have hl : eval (decode [0, 3, 0, 0, 0, 3, 3, 3, 3]) = 1 :=
    variant_eq_one word0_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 2, 2, 2, 1, 2, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [0, 3, 0, 0, 0, 3, 2, 2, 2, 1, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 5. -/
abbrev word5 : Word := decode [0, 0, 0, 1, 1, 2, 2, 2, 1, 2, 3, 3, 0, 3]

/-- Node 5 holds in the exact M11 presentation group. -/
theorem word5_eq_one : eval word5 = 1 := by
  have hl : eval (decode [0, 3, 0, 0, 0, 3, 3, 3, 3]) = 1 :=
    variant_eq_one word0_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [1, 1, 2, 2, 2, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [0, 3, 0, 0, 0, 3, 3, 2, 2, 2, 1, 2, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 6. -/
abbrev word6 : Word := decode [0, 0, 0, 3, 3, 3, 3, 2, 1, 2, 1, 1, 1, 1, 2, 3]

/-- Node 6 holds in the exact M11 presentation group. -/
theorem word6_eq_one : eval word6 = 1 := by
  have hl : eval (decode [0, 3, 3, 3, 3, 0, 3, 0, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      2 (by decide +kernel)
  have hr : eval (decode [2, 1, 1, 1, 1, 2, 2, 2, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [0, 3, 3, 3, 3, 0, 3, 0, 1, 1, 1, 1, 2, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 7. -/
abbrev word7 : Word := decode [0, 0, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 0, 3]

/-- Node 7 holds in the exact M11 presentation group. -/
theorem word7_eq_one : eval word7 = 1 := by
  have hl : eval (decode [1, 2, 1, 1, 1, 1, 2, 2, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      0 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 3, 3, 0, 3, 0, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [1, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 0, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 8. -/
abbrev word8 : Word := decode [0, 0, 0, 3, 3, 3, 3, 2, 2, 1, 2, 1, 1, 1]

/-- Node 8 holds in the exact M11 presentation group. -/
theorem word8_eq_one : eval word8 = 1 := by
  have hl : eval (decode [1, 1, 1, 1, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      2 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 3, 3, 0, 3, 0, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 0, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 9. -/
abbrev word9 : Word := decode [0, 0, 0, 3, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 0, 3]

/-- Node 9 holds in the exact M11 presentation group. -/
theorem word9_eq_one : eval word9 = 1 := by
  have hl : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      5 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 0, 3, 3, 3, 3, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 0, 0, 0, 3, 3, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 11. -/
abbrev word11 : Word := decode [0, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 0, 3]

/-- Node 11 holds in the exact M11 presentation group. -/
theorem word11_eq_one : eval word11 = 1 := by
  have hl : eval (decode [2, 1, 2, 1, 1, 1, 1, 2, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 3, 3, 0, 3, 0, 0]) = 1 :=
    variant_eq_one word0_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 12. -/
abbrev word12 : Word := decode [0, 0, 0, 0, 3, 3, 3, 3, 3, 2, 1, 2, 3, 0, 1]

/-- Node 12 holds in the exact M11 presentation group. -/
theorem word12_eq_one : eval word12 = 1 := by
  have hl : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [2, 1, 1, 1, 1, 2, 2, 2, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 1, 0, 3, 0, 1, 1, 1, 1, 1, 2, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 14. -/
abbrev word14 : Word := decode [0, 0, 3, 2, 1, 2, 3, 0, 1, 0, 3, 3, 3, 0, 3]

/-- Node 14 holds in the exact M11 presentation group. -/
theorem word14_eq_one : eval word14 = 1 := by
  have hl : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [2, 2, 2, 1, 2, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 1, 0, 3, 0, 1, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 15. -/
abbrev word15 : Word := decode [0, 1, 0, 1, 0, 3, 3, 3, 3, 0, 3, 0, 3, 2, 1, 2, 3]

/-- Node 15 holds in the exact M11 presentation group. -/
theorem word15_eq_one : eval word15 = 1 := by
  have hl : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [2, 2, 1, 2, 1, 1, 1, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      7 (by decide +kernel)
  have hc : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 2, 1, 2, 1, 1, 1, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 16. -/
abbrev word16 : Word := decode [0, 0, 0, 3, 3, 3, 2, 3, 2, 1, 2, 3, 0, 1, 0, 0, 3]

/-- Node 16 holds in the exact M11 presentation group. -/
theorem word16_eq_one : eval word16 = 1 := by
  have hl : eval (decode [1, 1, 1, 2, 2, 2, 1, 2, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 17. -/
abbrev word17 : Word := decode [0, 0, 0, 3, 3, 2, 3, 2, 1, 2, 3, 0, 1, 0, 3, 0, 3]

/-- Node 17 holds in the exact M11 presentation group. -/
theorem word17_eq_one : eval word17 = 1 := by
  have hl : eval (decode [1, 1, 2, 2, 2, 1, 2, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      4 (by decide +kernel)
  have hr : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 18. -/
abbrev word18 : Word := decode [0, 0, 0, 3, 2, 3, 2, 1, 2, 3, 0, 1, 0, 3, 3, 0, 3]

/-- Node 18 holds in the exact M11 presentation group. -/
theorem word18_eq_one : eval word18 = 1 := by
  have hl : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      5 (by decide +kernel)
  have hr : eval (decode [3, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word1_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 0, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 19. -/
abbrev word19 : Word := decode [0, 0, 3, 0, 1, 0, 3, 2, 3, 0, 0, 3, 3, 3, 3]

/-- Node 19 holds in the exact M11 presentation group. -/
theorem word19_eq_one : eval word19 = 1 := by
  have hl : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      0 (by decide +kernel)
  have hr : eval (decode [1, 2, 1, 1, 1, 1, 2, 2, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 20. -/
abbrev word20 : Word := decode [0, 0, 0, 3, 3, 0, 3, 0, 1, 0, 3, 2, 3, 2, 3, 0, 3]

/-- Node 20 holds in the exact M11 presentation group. -/
theorem word20_eq_one : eval word20 = 1 := by
  have hl : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      0 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 2, 2, 2, 1, 2, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 21. -/
abbrev word21 : Word := decode [0, 0, 0, 3, 3, 3, 0, 3, 0, 1, 0, 3, 2, 3, 3]

/-- Node 21 holds in the exact M11 presentation group. -/
theorem word21_eq_one : eval word21 = 1 := by
  have hl : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      0 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 1, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      2 (by decide +kernel)
  have hc : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 24. -/
abbrev word24 : Word := decode [0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 0, 3, 3, 3, 3, 0, 3]

/-- Node 24 holds in the exact M11 presentation group. -/
theorem word24_eq_one : eval word24 = 1 := by
  have hl : eval (decode [2, 1, 2, 1, 1, 1, 1, 2, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [2, 1, 2, 1, 1, 1, 1, 2, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    16 (by decide +kernel)

/-- Canonical signed word at certificate node 25. -/
abbrev word25 : Word := decode [0, 0, 1, 0, 3, 0, 1, 0, 3, 2, 3, 3, 3, 3, 3, 0, 3]

/-- Node 25 holds in the exact M11 presentation group. -/
theorem word25_eq_one : eval word25 = 1 := by
  have hl : eval (decode [2, 2, 1, 2, 1, 1, 1, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 26. -/
abbrev word26 : Word := decode [0, 0, 3, 3, 3, 3, 3, 0, 1, 0, 1, 2, 3]

/-- Node 26 holds in the exact M11 presentation group. -/
theorem word26_eq_one : eval word26 = 1 := by
  have hl : eval (decode [0, 1, 0, 3, 2, 3, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [1, 2, 1, 1, 1, 1, 2, 2, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    0 (by decide +kernel)

/-- Canonical signed word at certificate node 28. -/
abbrev word28 : Word := decode [0, 0, 0, 3, 3, 3, 2, 3, 0, 1, 0, 1, 2, 3, 3]

/-- Node 28 holds in the exact M11 presentation group. -/
theorem word28_eq_one : eval word28 = 1 := by
  have hl : eval (decode [0, 1, 0, 3, 2, 3, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 1, 2, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      2 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 2, 3, 2, 1, 0, 1, 1, 1, 2, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 30. -/
abbrev word30 : Word := decode [0, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 3, 0, 3]

/-- Node 30 holds in the exact M11 presentation group. -/
theorem word30_eq_one : eval word30 = 1 := by
  have hl : eval (decode [0, 1, 0, 3, 2, 3, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      5 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 3, 2, 3, 2, 1, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 32. -/
abbrev word32 : Word := decode [0, 0, 1, 2, 3, 0, 1, 0, 1, 2, 3, 3, 3, 3, 3, 0, 3]

/-- Node 32 holds in the exact M11 presentation group. -/
theorem word32_eq_one : eval word32 = 1 := by
  have hl : eval (decode [2, 2, 1, 2, 1, 1, 1, 1, 2]) = 1 :=
    variant_eq_one word0_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 3, 2, 3, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 2, 1, 1, 1, 1, 1, 0, 3, 2, 3, 2, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 33. -/
abbrev word33 : Word := decode [0, 0, 0, 3, 3, 3, 0, 1, 2, 3, 2, 1, 2, 3, 0, 0, 3]

/-- Node 33 holds in the exact M11 presentation group. -/
theorem word33_eq_one : eval word33 = 1 := by
  have hl : eval (decode [0, 3, 0, 0, 0, 3, 3, 3, 3]) = 1 :=
    variant_eq_one word0_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [0, 3, 0, 0, 0, 3, 3, 3, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    2 (by decide +kernel)

/-- Canonical signed word at certificate node 35. -/
abbrev word35 : Word := decode [0, 0, 0, 3, 3, 0, 1, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3]

/-- Node 35 holds in the exact M11 presentation group. -/
theorem word35_eq_one : eval word35 = 1 := by
  have hl : eval (decode [3, 0, 3, 0, 0, 0, 3, 3, 3]) = 1 :=
    variant_eq_one word0_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 3, 0, 0, 0, 3, 3, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 36. -/
abbrev word36 : Word := decode [0, 0, 0, 0, 1, 2, 3, 2, 1, 2, 3, 0, 3, 3, 3, 0, 3]

/-- Node 36 holds in the exact M11 presentation group. -/
theorem word36_eq_one : eval word36 = 1 := by
  have hl : eval (decode [3, 3, 3, 0, 3, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word0_eq_one false
      4 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 3, 3, 0, 3, 0, 0, 0, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 38. -/
abbrev word38 : Word := decode [0, 0, 1, 0, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 2, 3]

/-- Node 38 holds in the exact M11 presentation group. -/
theorem word38_eq_one : eval word38 = 1 := by
  have hl : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      0 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [0, 1, 0, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 45. -/
abbrev word45 : Word := decode [0, 0, 0, 0, 3, 2, 3, 2, 1, 0, 3, 0, 3, 3, 3, 0, 3]

/-- Node 45 holds in the exact M11 presentation group. -/
theorem word45_eq_one : eval word45 = 1 := by
  have hl : eval (decode [2, 1, 2, 3, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    variant_eq_one word0_eq_one true
      5 (by decide +kernel)
  have hc : eval (decode [2, 1, 2, 3, 0, 1, 0, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 46. -/
abbrev word46 : Word := decode [0, 0, 3, 0, 1, 0, 3, 3, 2, 3, 2, 1]

/-- Node 46 holds in the exact M11 presentation group. -/
theorem word46_eq_one : eval word46 = 1 := by
  have hl : eval (decode [2, 1, 2, 3, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word1_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 2, 3, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word1_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [2, 1])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
