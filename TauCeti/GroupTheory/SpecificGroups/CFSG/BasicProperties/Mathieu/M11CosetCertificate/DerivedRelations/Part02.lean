/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations.Part01

/-! Certified consequences of the exact M11 presentation relations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Canonical signed word at certificate node 148. -/
abbrev word148 : Word := decode [0, 0, 3, 2, 3, 3, 3, 0, 3, 0, 3, 0, 1, 0, 3, 3, 0, 3]

/-- Node 148 holds in the exact M11 presentation group. -/
theorem word148_eq_one : eval word148 = 1 := by
  have hl : eval (decode [3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 0, 3, 2, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word18_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word30_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 149. -/
abbrev word149 : Word := decode [0, 0, 3, 3, 3, 2, 1, 1, 1, 0, 1, 0, 3, 3, 2, 3]

/-- Node 149 holds in the exact M11 presentation group. -/
theorem word149_eq_one : eval word149 = 1 := by
  have hl : eval (decode [1, 1, 1, 2, 2, 1, 0, 1, 2, 3, 2, 1, 2, 2, 1]) = 1 :=
    variant_eq_one word19_eq_one true
      1 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 3, 0]) = 1 :=
    variant_eq_one word30_eq_one false
      14 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 2, 2, 1, 0, 1, 1, 2, 3, 2, 3, 3, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 153. -/
abbrev word153 : Word := decode [0, 0, 0, 3, 2, 3, 2, 1, 0, 3, 2, 2, 1, 1, 0, 1, 2, 3]

/-- Node 153 holds in the exact M11 presentation group. -/
theorem word153_eq_one : eval word153 = 1 := by
  have hl : eval (decode [2, 2, 1, 0, 3, 2, 3, 2, 1, 1, 1, 1, 1]) = 1 :=
    variant_eq_one word26_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 2, 3, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word32_eq_one false
      10 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 0, 3, 2, 3, 3, 0, 0, 1, 2, 3, 0, 1, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    16 (by decide +kernel)

/-- Canonical signed word at certificate node 165. -/
abbrev word165 : Word := decode [0, 0, 0, 1, 2, 2, 1, 0, 3, 3, 0, 1, 0, 3, 2, 3, 2, 3]

/-- Node 165 holds in the exact M11 presentation group. -/
theorem word165_eq_one : eval word165 = 1 := by
  have hl : eval (decode [3, 0, 0, 0, 1, 2, 2, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word4_eq_one false
      11 (by decide +kernel)
  have hr : eval (decode [2, 1, 0, 3, 0, 1, 0, 3, 3, 0, 1, 0, 3, 2, 3, 2]) = 1 :=
    variant_eq_one word38_eq_one true
      15 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 0, 1, 2, 2, 1, 0, 3, 3, 0, 1, 0, 3, 2, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 167. -/
abbrev word167 : Word := decode [0, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3]

/-- Node 167 holds in the exact M11 presentation group. -/
theorem word167_eq_one : eval word167 = 1 := by
  have hl : eval (decode [3, 2, 3, 2, 2, 1, 0, 3, 0, 1, 0, 3, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word38_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [2, 3, 2, 1, 0, 3, 0, 1, 0, 3]) = 1 :=
    variant_eq_one word1_eq_one true
      7 (by decide +kernel)
  have hc : eval (decode [3, 2, 3, 2, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 168. -/
abbrev word168 : Word := decode [0, 0, 3, 0, 3, 3, 3, 0, 3, 0, 1, 2, 1, 1, 2, 3, 2, 1]

/-- Node 168 holds in the exact M11 presentation group. -/
theorem word168_eq_one : eval word168 = 1 := by
  have hl : eval (decode [1, 2, 1, 1, 2, 3, 2, 1, 0, 3, 0, 1, 0, 1, 2, 2, 2]) = 1 :=
    variant_eq_one word18_eq_one true
      0 (by decide +kernel)
  have hr : eval (decode [0, 0, 0, 3, 2, 3, 2, 1, 0, 3, 0, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word45_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [1, 2, 1, 1, 2, 3, 2, 1, 0, 0, 3, 0, 3, 3, 3, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 175. -/
abbrev word175 : Word := decode [0, 1, 0, 1, 1, 1, 2, 3, 2, 3, 3, 3, 0, 3, 3]

/-- Node 175 holds in the exact M11 presentation group. -/
theorem word175_eq_one : eval word175 = 1 := by
  have hl : eval (decode [2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word46_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 1, 2, 3, 2, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word30_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 0, 1, 1, 1, 2, 3, 2, 3, 3, 3, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 178. -/
abbrev word178 : Word := decode [0, 0, 0, 3, 0, 1, 0, 3, 3, 3, 2, 3, 2, 1]

/-- Node 178 holds in the exact M11 presentation group. -/
theorem word178_eq_one : eval word178 = 1 := by
  have hl : eval (decode [0, 1, 1, 2, 3, 2, 1, 2, 2, 3, 0, 1]) = 1 :=
    variant_eq_one word46_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [3, 2, 1, 2, 3, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word1_eq_one false
      5 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 0, 1, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 182. -/
abbrev word182 : Word := decode [0, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 1, 0, 0, 3]

/-- Node 182 holds in the exact M11 presentation group. -/
theorem word182_eq_one : eval word182 = 1 := by
  have hl : eval (decode [3, 2, 1, 2, 2, 3, 0, 1, 0, 1, 1, 2]) = 1 :=
    variant_eq_one word46_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 3, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word1_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [2, 1, 2, 2, 3, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 184. -/
abbrev word184 : Word := decode [0, 0, 0, 0, 3, 0, 1, 0, 3, 3, 3, 3, 2, 3, 2, 1]

/-- Node 184 holds in the exact M11 presentation group. -/
theorem word184_eq_one : eval word184 = 1 := by
  have hl : eval (decode [0, 1, 1, 2, 3, 2, 1, 2, 2, 3, 0, 1]) = 1 :=
    variant_eq_one word46_eq_one true
      3 (by decide +kernel)
  have hr : eval (decode [3, 2, 1, 2, 2, 3, 0, 1, 0, 1, 1, 2]) = 1 :=
    variant_eq_one word46_eq_one true
      7 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 0, 1, 0, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 185. -/
abbrev word185 : Word := decode [0, 0, 0, 3, 0, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1]

/-- Node 185 holds in the exact M11 presentation group. -/
theorem word185_eq_one : eval word185 = 1 := by
  have hl : eval (decode [3, 2, 1, 2, 2, 3, 0, 1, 0, 1, 1, 2]) = 1 :=
    variant_eq_one word46_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 2, 3, 2, 1, 2, 3, 0, 1, 0, 3, 0, 3, 0, 0]) = 1 :=
    variant_eq_one word17_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 2, 2, 2, 3, 0, 1, 0, 3, 0, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 197. -/
abbrev word197 : Word := decode [0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 2, 3, 0, 0, 3, 2, 2, 3]

/-- Node 197 holds in the exact M11 presentation group. -/
theorem word197_eq_one : eval word197 = 1 := by
  have hl : eval (decode [0, 0, 3, 2, 2, 3, 0, 0, 0, 3, 3, 3, 2, 1, 0, 3, 0]) = 1 :=
    variant_eq_one word62_eq_one false
      1 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 3, 0, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3]) = 1 :=
    variant_eq_one word53_eq_one true
      4 (by decide +kernel)
  have hc : eval (decode [0, 0, 3, 2, 2, 3, 0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 204. -/
abbrev word204 : Word := decode [0, 0, 0, 1, 0, 3, 3, 3, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3]

/-- Node 204 holds in the exact M11 presentation group. -/
theorem word204_eq_one : eval word204 = 1 := by
  have hl : eval (decode [3, 0, 0, 0, 1, 0, 3, 3, 3, 3, 0, 3, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word73_eq_one false
      16 (by decide +kernel)
  have hr : eval (decode [2, 1, 0, 3, 0, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3]) = 1 :=
    variant_eq_one word15_eq_one true
      16 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 0, 1, 0, 3, 3, 3, 2, 1, 1, 1, 1, 2, 3, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 205. -/
abbrev word205 : Word := decode [0, 0, 0, 0, 3, 2, 2, 2, 1, 0, 3, 2, 2, 2, 1, 1]

/-- Node 205 holds in the exact M11 presentation group. -/
theorem word205_eq_one : eval word205 = 1 := by
  have hl : eval (decode [0, 3, 0, 0, 0, 1, 2, 2, 2, 2, 3, 2, 1, 0, 3, 0]) = 1 :=
    variant_eq_one word75_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 3, 0, 3, 0, 0, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word4_eq_one false
      6 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [0])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 206. -/
abbrev word206 : Word := decode [0, 0, 0, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 3, 2, 1, 0, 3]

/-- Node 206 holds in the exact M11 presentation group. -/
theorem word206_eq_one : eval word206 = 1 := by
  have hl : eval (decode [2, 1, 2, 3, 0, 1, 2, 2, 1, 2, 1, 0, 3, 0, 0, 3]) = 1 :=
    variant_eq_one word70_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 1, 2, 3, 0, 1, 0, 0, 0, 0, 3, 2, 2, 2]) = 1 :=
    variant_eq_one word75_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [2, 1, 2, 3, 0, 1, 2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    17 (by decide +kernel)

/-- Canonical signed word at certificate node 207. -/
abbrev word207 : Word := decode [0, 0, 0, 1, 0, 3, 2, 2, 2, 1, 2, 1, 0, 0, 3, 2, 3, 3]

/-- Node 207 holds in the exact M11 presentation group. -/
theorem word207_eq_one : eval word207 = 1 := by
  have hl : eval (decode [2, 3, 0, 3, 0, 0, 0, 1, 2, 2, 2, 1]) = 1 :=
    variant_eq_one word4_eq_one false
      8 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 3, 2, 2, 2, 1, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word76_eq_one true
      5 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 3, 0, 0, 0, 1, 2, 3, 2, 2, 2, 1, 1, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 218. -/
abbrev word218 : Word := decode [0, 0, 0, 0, 1, 0, 3, 2, 3, 0, 0, 1, 2, 2, 2, 2, 3, 3]

/-- Node 218 holds in the exact M11 presentation group. -/
theorem word218_eq_one : eval word218 = 1 := by
  have hl : eval (decode [3, 0, 0, 0, 0, 1, 0, 3, 2, 3, 2, 1, 2, 2, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word79_eq_one false
      17 (by decide +kernel)
  have hr : eval (decode [2, 1, 0, 3, 0, 0, 3, 0, 0, 0, 1, 2, 2, 2, 2, 3]) = 1 :=
    variant_eq_one word75_eq_one true
      1 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 0, 0, 1, 0, 3, 2, 3, 0, 0, 1, 2, 2, 2, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 219. -/
abbrev word219 : Word := decode [0, 0, 0, 0, 1, 0, 3, 3, 3, 2, 3, 2, 1, 1, 2, 3, 0, 3]

/-- Node 219 holds in the exact M11 presentation group. -/
theorem word219_eq_one : eval word219 = 1 := by
  have hl : eval (decode [3, 3, 2, 3, 2, 1, 0, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word46_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [2, 3, 2, 1, 2, 2, 1, 2, 3, 0, 3, 0, 0, 0, 0, 1, 0, 3]) = 1 :=
    variant_eq_one word79_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [3, 3, 2, 3, 2, 1, 1, 2, 3, 0, 3, 0, 0, 0, 0, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 223. -/
abbrev word223 : Word := decode [0, 0, 0, 0, 3, 2, 3, 3, 3, 3, 3, 0, 1, 2, 2, 1, 1]

/-- Node 223 holds in the exact M11 presentation group. -/
theorem word223_eq_one : eval word223 = 1 := by
  have hl : eval (decode [2, 2, 1, 1, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 0, 3, 2]) = 1 :=
    variant_eq_one word111_eq_one false
      13 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 0, 1]) = 1 :=
    variant_eq_one word103_eq_one true
      12 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 3, 3, 3, 3, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 224. -/
abbrev word224 : Word := decode [0, 0, 0, 0, 3, 0, 1, 2, 2, 1, 2, 2, 3, 2, 1]

/-- Node 224 holds in the exact M11 presentation group. -/
theorem word224_eq_one : eval word224 = 1 := by
  have hl : eval (decode [2, 2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word46_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 3, 2, 1, 2, 2]) = 1 :=
    variant_eq_one word112_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [2, 2, 3, 0, 1, 0, 0, 3, 0, 0, 3, 2, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 225. -/
abbrev word225 : Word := decode [0, 0, 0, 3, 0, 1, 2, 2, 1, 1, 0, 3, 2, 3, 2, 2, 1]

/-- Node 225 holds in the exact M11 presentation group. -/
theorem word225_eq_one : eval word225 = 1 := by
  have hl : eval (decode [2, 3, 0, 0, 1, 0, 1, 2, 3, 2, 1, 1, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word38_eq_one false
      14 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 3, 2, 1, 2, 2]) = 1 :=
    variant_eq_one word112_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 0, 1, 0, 1, 2, 3, 3, 0, 0, 3, 2, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    16 (by decide +kernel)

/-- Canonical signed word at certificate node 227. -/
abbrev word227 : Word := decode [0, 0, 3, 2, 3, 3, 3, 0, 3, 3, 0, 1, 0, 3, 0, 3]

/-- Node 227 holds in the exact M11 presentation group. -/
theorem word227_eq_one : eval word227 = 1 := by
  have hl : eval (decode [3, 3, 3, 3, 0, 3, 3, 0, 1, 0, 1, 2, 3, 2, 1, 0, 0]) = 1 :=
    variant_eq_one word50_eq_one false
      2 (by decide +kernel)
  have hr : eval (decode [2, 2, 3, 0, 1, 0, 3, 3, 0, 3, 0, 0, 3, 2, 1]) = 1 :=
    variant_eq_one word112_eq_one true
      13 (by decide +kernel)
  have hc : eval (decode [3, 3, 3, 0, 3, 3, 0, 1, 0, 3, 0, 3, 0, 0, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [3])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 231. -/
abbrev word231 : Word := decode [0, 0, 0, 0, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1]

/-- Node 231 holds in the exact M11 presentation group. -/
theorem word231_eq_one : eval word231 = 1 := by
  have hl : eval (decode [2, 3, 3, 0, 0, 0, 1, 0, 3, 3, 3, 3, 0, 0, 3]) = 1 :=
    variant_eq_one word119_eq_one false
      12 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 0, 0, 0]) = 1 :=
    variant_eq_one word111_eq_one true
      5 (by decide +kernel)
  have hc : eval (decode [3, 3, 0, 0, 0, 1, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    4 (by decide +kernel)

/-- Canonical signed word at certificate node 238. -/
abbrev word238 : Word := decode [0, 0, 3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 2, 3, 0, 1]

/-- Node 238 holds in the exact M11 presentation group. -/
theorem word238_eq_one : eval word238 = 1 := by
  have hl : eval (decode [2, 3, 2, 3, 3, 3, 0, 3, 0, 3, 0, 1, 0, 1, 1]) = 1 :=
    variant_eq_one word146_eq_one false
      5 (by decide +kernel)
  have hr : eval (decode [3, 3, 2, 3, 2, 1, 2, 2, 3, 0, 1, 0, 0, 3, 0, 0, 0]) = 1 :=
    variant_eq_one word115_eq_one false
      3 (by decide +kernel)
  have hc : eval (decode [3, 2, 3, 3, 3, 0, 3, 2, 3, 0, 1, 0, 0, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 241. -/
abbrev word241 : Word := decode [0, 0, 1, 0, 1, 2, 3, 3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 3]

/-- Node 241 holds in the exact M11 presentation group. -/
theorem word241_eq_one : eval word241 = 1 := by
  have hl : eval (decode [3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 0, 3, 0, 1, 0, 3, 3, 0]) = 1 :=
    variant_eq_one word148_eq_one false
      17 (by decide +kernel)
  have hr : eval (decode [2, 1, 1, 2, 3, 2, 1, 2, 3, 0, 0, 1, 0, 1, 2, 3]) = 1 :=
    variant_eq_one word38_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 3, 0, 0, 1, 0, 1, 2, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 242. -/
abbrev word242 : Word := decode [0, 0, 0, 3, 2, 2, 1, 1, 0, 1, 2, 2, 1, 2, 3, 2, 1]

/-- Node 242 holds in the exact M11 presentation group. -/
theorem word242_eq_one : eval word242 = 1 := by
  have hl : eval (decode [2, 1, 2, 3, 2, 1, 0, 0, 3, 0, 1, 0, 1, 2, 2, 2, 1]) = 1 :=
    variant_eq_one word116_eq_one true
      1 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 0, 3, 2, 3, 2, 1, 0, 3, 2, 2, 1, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word153_eq_one false
      17 (by decide +kernel)
  have hc : eval (decode [2, 1, 2, 3, 2, 1, 0, 0, 0, 3, 2, 2, 1, 1, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 243. -/
abbrev word243 : Word := decode [0, 0, 1, 0, 0, 3, 0, 0, 3, 2, 3, 3, 3, 3, 2, 1, 2, 3]

/-- Node 243 holds in the exact M11 presentation group. -/
theorem word243_eq_one : eval word243 = 1 := by
  have hl : eval (decode [1, 1, 1, 0, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2]) = 1 :=
    variant_eq_one word148_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 3, 2, 2, 1, 0, 3, 0, 1]) = 1 :=
    variant_eq_one word167_eq_one true
      5 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 0, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 0, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 244. -/
abbrev word244 : Word := decode [0, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 0, 1, 2, 2, 3, 2, 1]

/-- Node 244 holds in the exact M11 presentation group. -/
theorem word244_eq_one : eval word244 = 1 := by
  have hl : eval (decode [2, 2, 3, 0, 1, 0, 1, 1, 2, 3, 2, 1]) = 1 :=
    variant_eq_one word46_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 0, 3, 3, 0, 3, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2]) = 1 :=
    variant_eq_one word168_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [2, 2, 3, 0, 1, 0, 0, 3, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    16 (by decide +kernel)

/-- Canonical signed word at certificate node 247. -/
abbrev word247 : Word := decode [0, 0, 3, 2, 3, 3, 0, 0, 3, 3, 3, 0, 3, 3, 0, 1, 0, 3]

/-- Node 247 holds in the exact M11 presentation group. -/
theorem word247_eq_one : eval word247 = 1 := by
  have hl : eval (decode [2, 3, 2, 1, 1, 2, 1, 1, 1, 0, 1, 0, 3, 3, 3]) = 1 :=
    variant_eq_one word175_eq_one true
      12 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 0, 1, 2, 2, 1]) = 1 :=
    variant_eq_one word119_eq_one true
      7 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 0, 1, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 249. -/
abbrev word249 : Word := decode [0, 0, 1, 2, 1, 1, 1, 0, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1]

/-- Node 249 holds in the exact M11 presentation group. -/
theorem word249_eq_one : eval word249 = 1 := by
  have hl : eval (decode [1, 2, 1, 1, 1, 0, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2]) = 1 :=
    variant_eq_one word148_eq_one true
      9 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 1, 0, 3, 3, 3, 2, 3, 2, 1, 0, 0]) = 1 :=
    variant_eq_one word178_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [1, 2, 1, 1, 1, 0, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    16 (by decide +kernel)

/-- Canonical signed word at certificate node 250. -/
abbrev word250 : Word := decode [0, 0, 0, 0, 0, 3, 0, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1]

/-- Node 250 holds in the exact M11 presentation group. -/
theorem word250_eq_one : eval word250 = 1 := by
  have hl : eval (decode [0, 3, 0, 0, 3, 2, 1, 2, 2, 3, 0, 1, 0, 3, 3]) = 1 :=
    variant_eq_one word112_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 0, 1, 0, 1]) = 1 :=
    variant_eq_one word178_eq_one true
      5 (by decide +kernel)
  have hc : eval (decode [0, 3, 0, 0, 3, 2, 1, 2, 2, 2, 2, 2, 3, 0, 1, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 251. -/
abbrev word251 : Word := decode [0, 0, 0, 0, 3, 0, 1, 2, 2, 3, 3, 3, 0, 3, 0, 3, 2, 1]

/-- Node 251 holds in the exact M11 presentation group. -/
theorem word251_eq_one : eval word251 = 1 := by
  have hl : eval (decode [3, 2, 1, 0, 0, 0, 0, 3, 0, 1, 0, 3, 3, 3, 3, 2]) = 1 :=
    variant_eq_one word184_eq_one false
      13 (by decide +kernel)
  have hr : eval (decode [0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word8_eq_one true
      6 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 0, 0, 0, 0, 3, 0, 1, 2, 2, 3, 3, 3, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    3 (by decide +kernel)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
