/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.DerivedRelations.Part02

/-! Certified consequences of the exact M11 presentation relations. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations

/-- Canonical signed word at certificate node 253. -/
abbrev word253 : Word := decode [0, 0, 0, 0, 3, 2, 2, 1, 1, 0, 1, 2, 2, 2, 3, 2, 1]

/-- Node 253 holds in the exact M11 presentation group. -/
theorem word253_eq_one : eval word253 = 1 := by
  have hl : eval (decode [1, 2, 2, 2, 2, 3, 0, 1, 0, 1, 1, 1, 1, 2, 3, 2]) = 1 :=
    variant_eq_one word184_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 3, 3, 3, 3, 0, 0, 3, 2, 3, 3, 0, 0]) = 1 :=
    variant_eq_one word119_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [1, 2, 2, 2, 2, 3, 0, 1, 0, 0, 0, 3, 2, 3, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 254. -/
abbrev word254 : Word := decode [0, 0, 0, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1]

/-- Node 254 holds in the exact M11 presentation group. -/
theorem word254_eq_one : eval word254 = 1 := by
  have hl : eval (decode [3, 0, 0, 3, 2, 2, 2, 3, 0, 3, 0, 0, 0, 3, 0, 1, 2]) = 1 :=
    variant_eq_one word133_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [0, 3, 2, 1, 2, 2, 2, 3, 0, 1, 0, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word185_eq_one true
      8 (by decide +kernel)
  have hc : eval (decode [3, 0, 0, 3, 2, 2, 2, 3, 0, 3, 3, 0, 1, 0, 3, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 256. -/
abbrev word256 : Word := decode [0, 0, 0, 1, 0, 3, 3, 3, 2, 1, 2, 3, 2, 1, 1, 2, 1]

/-- Node 256 holds in the exact M11 presentation group. -/
theorem word256_eq_one : eval word256 = 1 := by
  have hl : eval (decode [3, 0, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 0, 1, 0, 3, 3, 3]) = 1 :=
    variant_eq_one word204_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 2, 3, 2, 3, 3, 3, 0, 3, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word175_eq_one false
      3 (by decide +kernel)
  have hc : eval (decode [3, 0, 1, 1, 1, 2, 3, 2, 2, 2, 3, 0, 3, 3, 0, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 259. -/
abbrev word259 : Word := decode [0, 0, 0, 3, 2, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 1]

/-- Node 259 holds in the exact M11 presentation group. -/
theorem word259_eq_one : eval word259 = 1 := by
  have hl : eval (decode [2, 2, 2, 2, 3, 3, 0, 0, 0, 1, 2, 3, 0, 0, 0, 1]) = 1 :=
    variant_eq_one word205_eq_one true
      12 (by decide +kernel)
  have hr : eval (decode [3, 2, 2, 2, 1, 0, 3, 2, 3, 3, 0, 0, 1, 0, 3, 0, 1, 0]) = 1 :=
    variant_eq_one word128_eq_one true
      14 (by decide +kernel)
  have hc : eval (decode [2, 2, 2, 3, 3, 0, 0, 3, 3, 0, 0, 1, 0, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [2])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 261. -/
abbrev word261 : Word := decode [0, 0, 3, 2, 3, 3, 2, 1, 2, 1, 0, 3, 3, 0, 1, 0, 3]

/-- Node 261 holds in the exact M11 presentation group. -/
theorem word261_eq_one : eval word261 = 1 := by
  have hl : eval (decode [2, 3, 2, 1, 1, 2, 3, 0, 3, 0, 0, 0, 0, 1, 0, 3, 3, 3]) = 1 :=
    variant_eq_one word219_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 0, 1, 2, 2, 1]) = 1 :=
    variant_eq_one word119_eq_one true
      7 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 1, 1, 2, 3, 0, 3, 0, 1, 1, 0, 1, 2, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    1 (by decide +kernel)

/-- Canonical signed word at certificate node 262. -/
abbrev word262 : Word := decode [0, 1, 0, 3, 3, 3, 3, 3, 2, 1, 1, 2, 3, 0, 3, 0, 1, 1]

/-- Node 262 holds in the exact M11 presentation group. -/
theorem word262_eq_one : eval word262 = 1 := by
  have hl : eval (decode [3, 2, 1, 1, 2, 3, 0, 3, 0, 0, 0, 0, 1, 0, 3, 3, 3, 2]) = 1 :=
    variant_eq_one word219_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [0, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 0, 1, 0, 3, 3, 3, 3]) = 1 :=
    variant_eq_one word204_eq_one true
      9 (by decide +kernel)
  have hc : eval (decode [3, 2, 1, 1, 2, 3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 3, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 265. -/
abbrev word265 : Word := decode [0, 0, 0, 1, 1, 1, 1, 0, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1]

/-- Node 265 holds in the exact M11 presentation group. -/
theorem word265_eq_one : eval word265 = 1 := by
  have hl : eval (decode [1, 1, 1, 1, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 3, 2, 1]) = 1 :=
    variant_eq_one word223_eq_one true
      7 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 2, 2, 1, 1, 0, 3, 2, 3, 2, 2, 1, 0, 0, 0]) = 1 :=
    variant_eq_one word225_eq_one false
      3 (by decide +kernel)
  have hc : eval (decode [1, 1, 1, 1, 0, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 0, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 266. -/
abbrev word266 : Word := decode [0, 0, 1, 0, 1, 1, 2, 3, 0, 3, 2, 3, 3, 3, 0, 3, 2, 3]

/-- Node 266 holds in the exact M11 presentation group. -/
theorem word266_eq_one : eval word266 = 1 := by
  have hl : eval (decode [1, 0, 3, 3, 2, 3, 2, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0]) = 1 :=
    variant_eq_one word167_eq_one true
      10 (by decide +kernel)
  have hr : eval (decode [2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word227_eq_one true
      15 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 3, 2, 3, 2, 2, 1, 0, 1, 2, 1, 1, 1, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 274. -/
abbrev word274 : Word := decode [0, 0, 0, 1, 0, 3, 3, 0, 3, 2, 3, 2, 2, 1, 1, 2, 1]

/-- Node 274 holds in the exact M11 presentation group. -/
theorem word274_eq_one : eval word274 = 1 := by
  have hl : eval (decode [1, 1, 2, 3, 2, 2, 2, 1, 1, 0, 1, 2, 2, 1, 1]) = 1 :=
    variant_eq_one word119_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [3, 3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 3, 0, 0, 1, 0, 1, 2]) = 1 :=
    variant_eq_one word241_eq_one false
      6 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 3, 2, 2, 2, 3, 0, 3, 3, 0, 0, 1, 0, 1, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 279. -/
abbrev word279 : Word := decode [0, 0, 3, 3, 3, 0, 3, 3, 0, 1, 2, 3, 2, 1, 0, 1, 2, 1]

/-- Node 279 holds in the exact M11 presentation group. -/
theorem word279_eq_one : eval word279 = 1 := by
  have hl : eval (decode [2, 3, 2, 1, 0, 1, 2, 1, 1, 1, 0, 1, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word238_eq_one true
      15 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 0, 3, 2, 3, 3, 0, 0, 3, 3, 3, 0, 3, 3, 0, 1]) = 1 :=
    variant_eq_one word247_eq_one false
      16 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 1, 0, 1, 2, 1, 0, 0, 3, 3, 3, 0, 3, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    8 (by decide +kernel)

/-- Canonical signed word at certificate node 280. -/
abbrev word280 : Word := decode [0, 0, 0, 3, 2, 2, 3, 0, 3, 2, 2, 3, 0, 1, 1]

/-- Node 280 holds in the exact M11 presentation group. -/
theorem word280_eq_one : eval word280 = 1 := by
  have hl : eval (decode [0, 0, 1, 2, 2, 2, 3, 0, 1, 0, 3, 0, 0, 3, 2, 3, 3]) = 1 :=
    variant_eq_one word242_eq_one true
      11 (by decide +kernel)
  have hr : eval (decode [1, 1, 0, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 0, 0, 1, 2, 1]) = 1 :=
    variant_eq_one word249_eq_one false
      5 (by decide +kernel)
  have hc : eval (decode [0, 0, 1, 2, 2, 2, 3, 3, 2, 1, 0, 0, 1, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 281. -/
abbrev word281 : Word := decode [0, 0, 1, 2, 1, 0, 0, 3, 3, 3, 0, 3, 3, 3, 2, 1]

/-- Node 281 holds in the exact M11 presentation group. -/
theorem word281_eq_one : eval word281 = 1 := by
  have hl : eval (decode [0, 0, 3, 3, 3, 0, 3, 3, 0, 1, 0, 3, 0, 0, 3, 2, 3, 3]) = 1 :=
    variant_eq_one word247_eq_one false
      6 (by decide +kernel)
  have hr : eval (decode [1, 1, 0, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 0, 0, 1, 2, 1]) = 1 :=
    variant_eq_one word249_eq_one false
      5 (by decide +kernel)
  have hc : eval (decode [0, 0, 3, 3, 3, 0, 3, 3, 3, 2, 1, 0, 0, 1, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    11 (by decide +kernel)

/-- Canonical signed word at certificate node 282. -/
abbrev word282 : Word := decode [0, 0, 0, 0, 0, 3, 3, 3, 0, 0, 1, 2, 2, 2, 3, 3, 2, 1]

/-- Node 282 holds in the exact M11 presentation group. -/
theorem word282_eq_one : eval word282 = 1 := by
  have hl : eval (decode [3, 3, 0, 0, 1, 2, 2, 2, 3, 0, 1, 0, 3, 0, 0, 3, 2]) = 1 :=
    variant_eq_one word242_eq_one true
      9 (by decide +kernel)
  have hr : eval (decode [0, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 0, 0, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word250_eq_one false
      6 (by decide +kernel)
  have hc : eval (decode [3, 3, 0, 0, 1, 2, 2, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    12 (by decide +kernel)

/-- Canonical signed word at certificate node 284. -/
abbrev word284 : Word := decode [0, 0, 0, 1, 2, 3, 0, 1, 1, 0, 1, 2, 2, 2, 3, 2, 3]

/-- Node 284 holds in the exact M11 presentation group. -/
theorem word284_eq_one : eval word284 = 1 := by
  have hl : eval (decode [1, 1, 0, 1, 2, 2, 2, 3, 2, 1, 0, 0, 0, 0, 3, 2, 2]) = 1 :=
    variant_eq_one word253_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [0, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 0, 1, 2, 3, 0]) = 1 :=
    variant_eq_one word205_eq_one true
      9 (by decide +kernel)
  have hc : eval (decode [1, 1, 0, 1, 2, 2, 2, 3, 2, 3, 0, 0, 0, 1, 2, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 285. -/
abbrev word285 : Word := decode [0, 0, 0, 0, 1, 0, 3, 2, 1, 0, 1, 2, 2, 2, 3, 2, 3]

/-- Node 285 holds in the exact M11 presentation group. -/
theorem word285_eq_one : eval word285 = 1 := by
  have hl : eval (decode [1, 0, 1, 2, 2, 2, 3, 2, 1, 0, 0, 0, 0, 3, 2, 2, 1]) = 1 :=
    variant_eq_one word253_eq_one false
      8 (by decide +kernel)
  have hr : eval (decode [3, 0, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 0, 0, 1, 0, 3, 2]) = 1 :=
    variant_eq_one word218_eq_one false
      8 (by decide +kernel)
  have hc : eval (decode [1, 0, 1, 2, 2, 2, 3, 2, 3, 0, 0, 0, 0, 1, 0, 3, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 293. -/
abbrev word293 : Word := decode [0, 0, 0, 3, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 2, 3]

/-- Node 293 holds in the exact M11 presentation group. -/
theorem word293_eq_one : eval word293 = 1 := by
  have hl : eval (decode [3, 3, 3, 0, 1, 2, 2, 2, 1, 2, 1, 1, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word9_eq_one true
      8 (by decide +kernel)
  have hr : eval (decode [1, 2, 2, 2, 3, 3, 0, 0, 3, 3, 0, 0, 1, 0, 3, 0]) = 1 :=
    variant_eq_one word259_eq_one true
      12 (by decide +kernel)
  have hc : eval (decode [3, 3, 3, 0, 1, 2, 2, 2, 1, 0, 3, 3, 0, 0, 1, 0, 3, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 294. -/
abbrev word294 : Word := decode [0, 1, 0, 3, 2, 1, 1, 2, 3, 0, 3, 0, 3, 0, 3, 2, 3]

/-- Node 294 holds in the exact M11 presentation group. -/
theorem word294_eq_one : eval word294 = 1 := by
  have hl : eval (decode [2, 3, 2, 1, 0, 1, 2, 1, 1, 1, 0, 1, 2, 2, 1, 2]) = 1 :=
    variant_eq_one word238_eq_one true
      15 (by decide +kernel)
  have hr : eval (decode [0, 3, 0, 0, 3, 2, 3, 3, 2, 1, 2, 1, 0, 3, 3, 0, 1]) = 1 :=
    variant_eq_one word261_eq_one false
      15 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 1, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 296. -/
abbrev word296 : Word := decode [0, 0, 1, 2, 1, 2, 1, 2, 1, 0, 3, 3, 3, 2, 1]

/-- Node 296 holds in the exact M11 presentation group. -/
theorem word296_eq_one : eval word296 = 1 := by
  have hl : eval (decode [1, 1, 2, 3, 0, 3, 0, 1, 1, 0, 1, 2, 2, 1, 2, 3, 2]) = 1 :=
    variant_eq_one word261_eq_one true
      4 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 2, 2, 3, 0, 1]) = 1 :=
    variant_eq_one word249_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [1, 1, 2, 3, 0, 3, 0, 3, 0, 3, 2, 2, 3, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 297. -/
abbrev word297 : Word := decode [0, 0, 0, 0, 3, 2, 2, 3, 3, 2, 2, 2, 3, 0, 0, 1, 1]

/-- Node 297 holds in the exact M11 presentation group. -/
theorem word297_eq_one : eval word297 = 1 := by
  have hl : eval (decode [3, 3, 2, 2, 2, 3, 0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 3, 3]) = 1 :=
    variant_eq_one word265_eq_one true
      13 (by decide +kernel)
  have hr : eval (decode [1, 1, 0, 1, 2, 2, 2, 3, 2, 1, 0, 0, 0, 0, 3, 2, 2]) = 1 :=
    variant_eq_one word253_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [3, 3, 2, 2, 2, 3, 0, 0, 1, 1, 0, 0, 0, 0, 3, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    10 (by decide +kernel)

/-- Canonical signed word at certificate node 298. -/
abbrev word298 : Word := decode [0, 0, 1, 0, 0, 3, 2, 3, 2, 3, 2, 2, 1, 0, 0, 1, 2, 3]

/-- Node 298 holds in the exact M11 presentation group. -/
theorem word298_eq_one : eval word298 = 1 := by
  have hl : eval (decode [2, 2, 3, 0, 0, 1, 0, 1, 0, 0, 0, 3, 2, 3, 3, 3, 3, 2]) = 1 :=
    variant_eq_one word265_eq_one true
      16 (by decide +kernel)
  have hr : eval (decode [0, 1, 1, 1, 1, 0, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word243_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [2, 2, 3, 0, 0, 1, 0, 1, 0, 1, 2, 2, 3, 2, 2, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    3 (by decide +kernel)

/-- Canonical signed word at certificate node 302. -/
abbrev word302 : Word := decode [0, 0, 0, 3, 2, 1, 2, 2, 3, 2, 2, 3, 0, 3, 3, 0, 0, 1]

/-- Node 302 holds in the exact M11 presentation group. -/
theorem word302_eq_one : eval word302 = 1 := by
  have hl : eval (decode [2, 3, 2, 2, 1, 1, 2, 1, 0, 0, 0, 1, 0, 3, 3, 0, 3]) = 1 :=
    variant_eq_one word274_eq_one false
      9 (by decide +kernel)
  have hr : eval (decode [1, 2, 1, 1, 2, 3, 2, 1, 0, 0, 3, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word112_eq_one false
      7 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 2, 1, 1, 2, 1, 0, 0, 1, 0, 0, 3, 0, 1, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    17 (by decide +kernel)

/-- Canonical signed word at certificate node 309. -/
abbrev word309 : Word := decode [0, 0, 1, 1, 1, 2, 2, 3, 0, 3, 2, 2, 3, 0, 3, 0, 3]

/-- Node 309 holds in the exact M11 presentation group. -/
theorem word309_eq_one : eval word309 = 1 := by
  have hl : eval (decode [2, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 3, 2, 1, 1, 2]) = 1 :=
    variant_eq_one word35_eq_one true
      15 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 0, 1, 2, 3, 2, 1, 0, 1, 2, 1, 0, 0, 3, 3, 3]) = 1 :=
    variant_eq_one word279_eq_one false
      5 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 2, 1, 2, 1, 0, 0, 1, 2, 1, 0, 0, 3, 3, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    15 (by decide +kernel)

/-- Canonical signed word at certificate node 311. -/
abbrev word311 : Word := decode [0, 0, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1]

/-- Node 311 holds in the exact M11 presentation group. -/
theorem word311_eq_one : eval word311 = 1 := by
  have hl : eval (decode [2, 1, 0, 0, 1, 2, 1, 0, 0, 1, 2, 2, 2, 3, 3]) = 1 :=
    variant_eq_one word280_eq_one true
      2 (by decide +kernel)
  have hr : eval (decode [1, 1, 0, 0, 0, 3, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1]) = 1 :=
    variant_eq_one word74_eq_one true
      8 (by decide +kernel)
  have hc : eval (decode [2, 1, 0, 0, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    2 (by decide +kernel)

/-- Canonical signed word at certificate node 313. -/
abbrev word313 : Word := decode [0, 0, 1, 0, 0, 3, 3, 0, 1, 2, 3, 2, 3, 3, 2, 1]

/-- Node 313 holds in the exact M11 presentation group. -/
theorem word313_eq_one : eval word313 = 1 := by
  have hl : eval (decode [1, 0, 3, 2, 1, 1, 2, 2, 2, 1, 0, 0, 1, 2, 2]) = 1 :=
    variant_eq_one word129_eq_one true
      6 (by decide +kernel)
  have hr : eval (decode [0, 0, 3, 2, 2, 3, 0, 3, 2, 2, 3, 0, 1, 1, 0]) = 1 :=
    variant_eq_one word280_eq_one false
      1 (by decide +kernel)
  have hc : eval (decode [1, 0, 3, 2, 1, 1, 2, 2, 3, 2, 2, 3, 0, 1, 1, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    5 (by decide +kernel)

/-- Canonical signed word at certificate node 318. -/
abbrev word318 : Word := decode [0, 0, 0, 0, 0, 1, 2, 3, 0, 3, 3, 2, 2, 2, 3]

/-- Node 318 holds in the exact M11 presentation group. -/
theorem word318_eq_one : eval word318 = 1 := by
  have hl : eval (decode [0, 0, 0, 1, 2, 3, 0, 1, 1, 0, 1, 2, 2, 2, 3, 2, 3]) = 1 :=
    variant_eq_one word284_eq_one false
      0 (by decide +kernel)
  have hr : eval (decode [1, 0, 1, 0, 0, 0, 3, 2, 3, 3, 3, 3, 2, 2, 2, 3, 0, 0]) = 1 :=
    variant_eq_one word265_eq_one true
      3 (by decide +kernel)
  have hc : eval (decode [0, 0, 0, 1, 2, 3, 0, 3, 3, 2, 2, 2, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    13 (by decide +kernel)

/-- Canonical signed word at certificate node 321. -/
abbrev word321 : Word := decode [0, 0, 0, 3, 2, 2, 3, 0, 0, 3, 0, 3, 0, 3, 0, 3, 2, 3]

/-- Node 321 holds in the exact M11 presentation group. -/
theorem word321_eq_one : eval word321 = 1 := by
  have hl : eval (decode [2, 2, 1, 0, 0, 1, 2, 2, 1, 0, 3, 2, 1, 1, 2]) = 1 :=
    variant_eq_one word129_eq_one true
      13 (by decide +kernel)
  have hr : eval (decode [0, 3, 3, 0, 1, 2, 3, 2, 1, 0, 1, 2, 1, 2, 1, 2, 1]) = 1 :=
    variant_eq_one word294_eq_one true
      9 (by decide +kernel)
  have hc : eval (decode [2, 2, 1, 0, 0, 1, 2, 2, 2, 1, 0, 1, 2, 1, 2, 1, 2, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc true
    9 (by decide +kernel)

/-- Canonical signed word at certificate node 323. -/
abbrev word323 : Word := decode [0, 0, 0, 3, 2, 3, 0, 3, 0, 3, 0, 3, 2, 2, 3, 0, 0, 3]

/-- Node 323 holds in the exact M11 presentation group. -/
theorem word323_eq_one : eval word323 = 1 := by
  have hl : eval (decode [2, 3, 0, 3, 0, 3, 0, 3, 2, 3, 0, 1, 0, 3, 2, 1, 1]) = 1 :=
    variant_eq_one word294_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [3, 3, 0, 1, 2, 3, 2, 1, 2, 3, 0, 0, 3, 0, 0, 0, 3]) = 1 :=
    variant_eq_one word33_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [2, 3, 0, 3, 0, 3, 0, 3, 2, 2, 3, 0, 0, 3, 0, 0, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 325. -/
abbrev word325 : Word := decode [0, 0, 0, 0, 3, 0, 3, 0, 3, 2, 2, 2, 3, 2, 1, 1, 2, 1]

/-- Node 325 holds in the exact M11 presentation group. -/
theorem word325_eq_one : eval word325 = 1 := by
  have hl : eval (decode [2, 3, 2, 1, 1, 2, 1, 0, 0, 0, 1, 0, 3, 3, 3, 2, 1]) = 1 :=
    variant_eq_one word256_eq_one false
      10 (by decide +kernel)
  have hr : eval (decode [3, 0, 1, 1, 1, 2, 3, 0, 3, 0, 3, 0, 3, 2, 2]) = 1 :=
    variant_eq_one word296_eq_one true
      0 (by decide +kernel)
  have hc : eval (decode [2, 3, 2, 1, 1, 2, 1, 0, 0, 0, 0, 3, 0, 3, 0, 3, 2, 2]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

/-- Canonical signed word at certificate node 329. -/
abbrev word329 : Word := decode [0, 0, 0, 1, 0, 3, 2, 2, 3, 0, 1, 1, 2, 3, 3, 2, 2, 1]

/-- Node 329 holds in the exact M11 presentation group. -/
theorem word329_eq_one : eval word329 = 1 := by
  have hl : eval (decode [2, 3, 3, 2, 2, 1, 0, 0, 0, 1, 1, 0, 0, 1, 2, 2, 2]) = 1 :=
    variant_eq_one word297_eq_one true
      16 (by decide +kernel)
  have hr : eval (decode [0, 0, 0, 3, 2, 2, 3, 0, 3, 2, 2, 3, 0, 1, 1]) = 1 :=
    variant_eq_one word280_eq_one false
      0 (by decide +kernel)
  have hc : eval (decode [2, 3, 3, 2, 2, 1, 0, 0, 0, 1, 0, 3, 2, 2, 3, 0, 1, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 330. -/
abbrev word330 : Word := decode [0, 0, 0, 0, 3, 2, 1, 0, 3, 0, 0, 3, 3, 2, 2, 2, 3]

/-- Node 330 holds in the exact M11 presentation group. -/
theorem word330_eq_one : eval word330 = 1 := by
  have hl : eval (decode [3, 3, 2, 2, 2, 3, 0, 0, 1, 1, 0, 0, 0, 0, 3, 2, 2]) = 1 :=
    variant_eq_one word297_eq_one false
      7 (by decide +kernel)
  have hr : eval (decode [0, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 3, 2, 1, 0, 3, 0, 0]) = 1 :=
    variant_eq_one word206_eq_one false
      2 (by decide +kernel)
  have hc : eval (decode [3, 3, 2, 2, 2, 3, 0, 0, 0, 0, 3, 2, 1, 0, 3, 0, 0]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    6 (by decide +kernel)

/-- Canonical signed word at certificate node 333. -/
abbrev word333 : Word := decode [0, 0, 0, 1, 1, 0, 0, 3, 2, 3, 2, 3, 2, 2, 1, 0, 3, 3]

/-- Node 333 holds in the exact M11 presentation group. -/
theorem word333_eq_one : eval word333 = 1 := by
  have hl : eval (decode [1, 0, 0, 3, 2, 3, 2, 3, 2, 2, 1, 0, 0, 1, 2, 3, 0, 0]) = 1 :=
    variant_eq_one word298_eq_one false
      2 (by decide +kernel)
  have hr : eval (decode [2, 2, 1, 0, 3, 2, 3, 3, 0, 0, 0, 1]) = 1 :=
    variant_eq_one word76_eq_one false
      4 (by decide +kernel)
  have hc : eval (decode [1, 0, 0, 3, 2, 3, 2, 3, 2, 2, 1, 0, 3, 3, 0, 0, 0, 1]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    14 (by decide +kernel)

/-- Canonical signed word at certificate node 334. -/
abbrev word334 : Word := decode [0, 0, 1, 1, 0, 3, 3, 2, 1, 0, 3, 2, 1, 0, 3, 2, 2, 3]

/-- Node 334 holds in the exact M11 presentation group. -/
theorem word334_eq_one : eval word334 = 1 := by
  have hl : eval (decode [2, 1, 0, 3, 2, 2, 3, 0, 0, 1, 0, 1, 0, 1, 2, 2, 3, 2]) = 1 :=
    variant_eq_one word298_eq_one true
      17 (by decide +kernel)
  have hr : eval (decode [0, 1, 0, 0, 3, 2, 3, 2, 1, 0, 3, 3, 2, 1, 0, 3]) = 1 :=
    variant_eq_one word58_eq_one false
      14 (by decide +kernel)
  have hc : eval (decode [2, 1, 0, 3, 2, 2, 3, 0, 0, 1, 1, 0, 3, 3, 2, 1, 0, 3]) = 1 :=
    reduced_conjugate_eq_one (decode [])
      (product_eq_one hl hr) (by decide +kernel)
  exact variant_eq_one hc false
    7 (by decide +kernel)

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.Relations
