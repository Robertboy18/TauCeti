/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableFast

/-!
# M11 coset certificate: Words0

Literal defining words and their block representation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def w0 : List (Fin 4) := []

@[expose]
def w1 : List (Fin 4) := [0]

@[expose]
def w2 : List (Fin 4) := [1]

@[expose]
def w3 : List (Fin 4) := [2]

@[expose]
def w4 : List (Fin 4) := [0, 0]

@[expose]
def w5 : List (Fin 4) := [1, 0]

@[expose]
def w6 : List (Fin 4) := [3, 0]

@[expose]
def w7 : List (Fin 4) := [0, 1]

@[expose]
def w8 : List (Fin 4) := [1, 1]

@[expose]
def w9 : List (Fin 4) := [2, 1]

@[expose]
def w10 : List (Fin 4) := [2, 2]

@[expose]
def w11 : List (Fin 4) := [3, 2]

@[expose]
def w12 : List (Fin 4) := [0, 0, 0]

@[expose]
def w13 : List (Fin 4) := [1, 0, 0]

@[expose]
def w14 : List (Fin 4) := [3, 0, 0]

@[expose]
def w15 : List (Fin 4) := [0, 1, 0]

@[expose]
def w16 : List (Fin 4) := [1, 1, 0]

@[expose]
def w17 : List (Fin 4) := [2, 1, 0]

@[expose]
def w18 : List (Fin 4) := [0, 3, 0]

@[expose]
def w19 : List (Fin 4) := [2, 3, 0]

@[expose]
def w20 : List (Fin 4) := [3, 3, 0]

@[expose]
def w21 : List (Fin 4) := [0, 0, 1]

@[expose]
def w22 : List (Fin 4) := [1, 0, 1]

@[expose]
def w23 : List (Fin 4) := [3, 0, 1]

@[expose]
def w24 : List (Fin 4) := [0, 1, 1]

@[expose]
def w25 : List (Fin 4) := [1, 1, 1]

@[expose]
def w26 : List (Fin 4) := [2, 1, 1]

@[expose]
def w27 : List (Fin 4) := [1, 2, 1]

@[expose]
def w28 : List (Fin 4) := [2, 2, 1]

@[expose]
def w29 : List (Fin 4) := [3, 2, 1]

@[expose]
def w30 : List (Fin 4) := [1, 2, 2]

@[expose]
def w31 : List (Fin 4) := [2, 2, 2]

@[expose]
def w32 : List (Fin 4) := [3, 2, 2]

@[expose]
def w33 : List (Fin 4) := [0, 3, 2]

@[expose]
def w34 : List (Fin 4) := [2, 3, 2]

@[expose]
def w35 : List (Fin 4) := [3, 3, 2]

@[expose]
def w36 : List (Fin 4) := [0, 0, 0, 0]

@[expose]
def w37 : List (Fin 4) := [1, 0, 0, 0]

@[expose]
def w38 : List (Fin 4) := [3, 0, 0, 0]

@[expose]
def w39 : List (Fin 4) := [0, 1, 0, 0]

@[expose]
def w40 : List (Fin 4) := [1, 1, 0, 0]

@[expose]
def w41 : List (Fin 4) := [2, 1, 0, 0]

@[expose]
def w42 : List (Fin 4) := [2, 3, 0, 0]

@[expose]
def w43 : List (Fin 4) := [3, 3, 0, 0]

@[expose]
def w44 : List (Fin 4) := [0, 0, 1, 0]

@[expose]
def w45 : List (Fin 4) := [1, 0, 1, 0]

@[expose]
def w46 : List (Fin 4) := [3, 0, 1, 0]

@[expose]
def w47 : List (Fin 4) := [0, 1, 1, 0]

@[expose]
def w48 : List (Fin 4) := [1, 1, 1, 0]

@[expose]
def w49 : List (Fin 4) := [2, 1, 1, 0]

@[expose]
def w50 : List (Fin 4) := [1, 2, 1, 0]

@[expose]
def w51 : List (Fin 4) := [2, 2, 1, 0]

@[expose]
def w52 : List (Fin 4) := [3, 2, 1, 0]

@[expose]
def w53 : List (Fin 4) := [0, 0, 3, 0]

@[expose]
def w54 : List (Fin 4) := [1, 0, 3, 0]

@[expose]
def w55 : List (Fin 4) := [1, 2, 3, 0]

@[expose]
def w56 : List (Fin 4) := [2, 2, 3, 0]

@[expose]
def w57 : List (Fin 4) := [3, 2, 3, 0]

@[expose]
def w58 : List (Fin 4) := [0, 3, 3, 0]

@[expose]
def w59 : List (Fin 4) := [2, 3, 3, 0]

@[expose]
def w60 : List (Fin 4) := [3, 3, 3, 0]

@[expose]
def w61 : List (Fin 4) := [0, 0, 0, 1]

@[expose]
def w62 : List (Fin 4) := [1, 0, 0, 1]

@[expose]
def w63 : List (Fin 4) := [3, 0, 0, 1]

@[expose]
def w64 : List (Fin 4) := [0, 1, 0, 1]

@[expose]
def w65 : List (Fin 4) := [1, 1, 0, 1]

@[expose]
def w66 : List (Fin 4) := [2, 1, 0, 1]

@[expose]
def w67 : List (Fin 4) := [2, 3, 0, 1]

@[expose]
def w68 : List (Fin 4) := [3, 3, 0, 1]

@[expose]
def w69 : List (Fin 4) := [0, 0, 1, 1]

@[expose]
def w70 : List (Fin 4) := [1, 0, 1, 1]

@[expose]
def w71 : List (Fin 4) := [3, 0, 1, 1]

@[expose]
def w72 : List (Fin 4) := [0, 1, 1, 1]

@[expose]
def w73 : List (Fin 4) := [1, 1, 1, 1]

@[expose]
def w74 : List (Fin 4) := [1, 2, 1, 1]

@[expose]
def w75 : List (Fin 4) := [2, 2, 1, 1]

@[expose]
def w76 : List (Fin 4) := [3, 2, 1, 1]

@[expose]
def w77 : List (Fin 4) := [0, 1, 2, 1]

@[expose]
def w78 : List (Fin 4) := [1, 1, 2, 1]

@[expose]
def w79 : List (Fin 4) := [2, 1, 2, 1]

@[expose]
def w80 : List (Fin 4) := [1, 2, 2, 1]

@[expose]
def w81 : List (Fin 4) := [2, 2, 2, 1]

@[expose]
def w82 : List (Fin 4) := [3, 2, 2, 1]

@[expose]
def w83 : List (Fin 4) := [0, 3, 2, 1]

@[expose]
def w84 : List (Fin 4) := [2, 3, 2, 1]

@[expose]
def w85 : List (Fin 4) := [3, 3, 2, 1]

@[expose]
def w86 : List (Fin 4) := [0, 1, 2, 2]

@[expose]
def w87 : List (Fin 4) := [1, 1, 2, 2]

@[expose]
def w88 : List (Fin 4) := [2, 1, 2, 2]

@[expose]
def w89 : List (Fin 4) := [2, 2, 2, 2]

@[expose]
def w90 : List (Fin 4) := [3, 2, 2, 2]

@[expose]
def w91 : List (Fin 4) := [2, 3, 2, 2]

@[expose]
def w92 : List (Fin 4) := [3, 3, 2, 2]

@[expose]
def w93 : List (Fin 4) := [0, 0, 3, 2]

@[expose]
def w94 : List (Fin 4) := [1, 0, 3, 2]

@[expose]
def w95 : List (Fin 4) := [3, 0, 3, 2]

@[expose]
def w96 : List (Fin 4) := [2, 2, 3, 2]

@[expose]
def w97 : List (Fin 4) := [3, 2, 3, 2]

@[expose]
def w98 : List (Fin 4) := [0, 3, 3, 2]

@[expose]
def w99 : List (Fin 4) := [2, 3, 3, 2]

@[expose]
def w100 : List (Fin 4) := [0, 0, 0, 0, 0]

@[expose]
def w101 : List (Fin 4) := [1, 0, 0, 0, 0]

@[expose]
def w102 : List (Fin 4) := [3, 0, 0, 0, 0]

@[expose]
def w103 : List (Fin 4) := [0, 1, 0, 0, 0]

@[expose]
def w104 : List (Fin 4) := [1, 1, 0, 0, 0]

@[expose]
def w105 : List (Fin 4) := [2, 1, 0, 0, 0]

@[expose]
def w106 : List (Fin 4) := [2, 3, 0, 0, 0]

@[expose]
def w107 : List (Fin 4) := [3, 3, 0, 0, 0]

@[expose]
def w108 : List (Fin 4) := [0, 0, 1, 0, 0]

@[expose]
def w109 : List (Fin 4) := [1, 0, 1, 0, 0]

@[expose]
def w110 : List (Fin 4) := [3, 0, 1, 0, 0]

@[expose]
def w111 : List (Fin 4) := [0, 1, 1, 0, 0]

@[expose]
def w112 : List (Fin 4) := [1, 1, 1, 0, 0]

@[expose]
def w113 : List (Fin 4) := [2, 1, 1, 0, 0]

@[expose]
def w114 : List (Fin 4) := [2, 2, 1, 0, 0]

@[expose]
def w115 : List (Fin 4) := [2, 2, 3, 0, 0]

@[expose]
def w116 : List (Fin 4) := [3, 2, 3, 0, 0]

@[expose]
def w117 : List (Fin 4) := [0, 3, 3, 0, 0]

@[expose]
def w118 : List (Fin 4) := [2, 3, 3, 0, 0]

@[expose]
def w119 : List (Fin 4) := [0, 0, 0, 1, 0]

@[expose]
def w120 : List (Fin 4) := [1, 0, 0, 1, 0]

@[expose]
def w121 : List (Fin 4) := [3, 0, 0, 1, 0]

@[expose]
def w122 : List (Fin 4) := [0, 1, 0, 1, 0]

@[expose]
def w123 : List (Fin 4) := [1, 1, 0, 1, 0]

@[expose]
def w124 : List (Fin 4) := [2, 1, 0, 1, 0]

@[expose]
def w125 : List (Fin 4) := [0, 3, 0, 1, 0]

@[expose]
def w126 : List (Fin 4) := [3, 3, 0, 1, 0]

@[expose]
def w127 : List (Fin 4) := [0, 0, 1, 1, 0]

@[expose]
def w128 : List (Fin 4) := [1, 0, 1, 1, 0]

@[expose]
def w129 : List (Fin 4) := [3, 0, 1, 1, 0]

@[expose]
def w130 : List (Fin 4) := [1, 1, 1, 1, 0]

@[expose]
def w131 : List (Fin 4) := [2, 1, 1, 1, 0]

@[expose]
def w132 : List (Fin 4) := [1, 2, 1, 1, 0]

@[expose]
def w133 : List (Fin 4) := [2, 2, 1, 1, 0]

@[expose]
def w134 : List (Fin 4) := [3, 2, 1, 1, 0]

@[expose]
def w135 : List (Fin 4) := [0, 1, 2, 1, 0]

@[expose]
def w136 : List (Fin 4) := [1, 1, 2, 1, 0]

@[expose]
def w137 : List (Fin 4) := [1, 2, 2, 1, 0]

@[expose]
def w138 : List (Fin 4) := [2, 2, 2, 1, 0]

@[expose]
def w139 : List (Fin 4) := [3, 2, 2, 1, 0]

@[expose]
def w140 : List (Fin 4) := [0, 3, 2, 1, 0]

@[expose]
def w141 : List (Fin 4) := [2, 3, 2, 1, 0]

@[expose]
def w142 : List (Fin 4) := [3, 3, 2, 1, 0]

@[expose]
def w143 : List (Fin 4) := [0, 0, 0, 3, 0]

@[expose]
def w144 : List (Fin 4) := [1, 0, 0, 3, 0]

@[expose]
def w145 : List (Fin 4) := [3, 0, 0, 3, 0]

@[expose]
def w146 : List (Fin 4) := [0, 1, 0, 3, 0]

@[expose]
def w147 : List (Fin 4) := [1, 1, 0, 3, 0]

@[expose]
def w148 : List (Fin 4) := [2, 1, 0, 3, 0]

@[expose]
def w149 : List (Fin 4) := [1, 1, 2, 3, 0]

@[expose]
def w150 : List (Fin 4) := [2, 2, 2, 3, 0]

@[expose]
def w151 : List (Fin 4) := [0, 3, 2, 3, 0]

@[expose]
def w152 : List (Fin 4) := [2, 3, 2, 3, 0]

@[expose]
def w153 : List (Fin 4) := [3, 3, 2, 3, 0]

@[expose]
def w154 : List (Fin 4) := [0, 0, 3, 3, 0]

@[expose]
def w155 : List (Fin 4) := [1, 0, 3, 3, 0]

@[expose]
def w156 : List (Fin 4) := [3, 0, 3, 3, 0]

@[expose]
def w157 : List (Fin 4) := [1, 2, 3, 3, 0]

@[expose]
def w158 : List (Fin 4) := [2, 2, 3, 3, 0]

@[expose]
def w159 : List (Fin 4) := [3, 2, 3, 3, 0]

@[expose]
def w160 : List (Fin 4) := [2, 3, 3, 3, 0]

@[expose]
def w161 : List (Fin 4) := [0, 0, 0, 0, 1]

@[expose]
def w162 : List (Fin 4) := [1, 0, 0, 0, 1]

@[expose]
def w163 : List (Fin 4) := [3, 0, 0, 0, 1]

@[expose]
def w164 : List (Fin 4) := [0, 1, 0, 0, 1]

@[expose]
def w165 : List (Fin 4) := [1, 1, 0, 0, 1]

@[expose]
def w166 : List (Fin 4) := [0, 3, 0, 0, 1]

@[expose]
def w167 : List (Fin 4) := [2, 3, 0, 0, 1]

@[expose]
def w168 : List (Fin 4) := [3, 3, 0, 0, 1]

@[expose]
def w169 : List (Fin 4) := [0, 0, 1, 0, 1]

@[expose]
def w170 : List (Fin 4) := [1, 0, 1, 0, 1]

@[expose]
def w171 : List (Fin 4) := [1, 1, 1, 0, 1]

@[expose]
def w172 : List (Fin 4) := [2, 1, 1, 0, 1]

@[expose]
def w173 : List (Fin 4) := [1, 2, 1, 0, 1]

@[expose]
def w174 : List (Fin 4) := [2, 2, 1, 0, 1]

@[expose]
def w175 : List (Fin 4) := [3, 2, 1, 0, 1]

@[expose]
def w176 : List (Fin 4) := [1, 2, 3, 0, 1]

@[expose]
def w177 : List (Fin 4) := [2, 2, 3, 0, 1]

@[expose]
def w178 : List (Fin 4) := [3, 2, 3, 0, 1]

@[expose]
def w179 : List (Fin 4) := [0, 3, 3, 0, 1]

@[expose]
def w180 : List (Fin 4) := [3, 3, 3, 0, 1]

@[expose]
def w181 : List (Fin 4) := [0, 0, 0, 1, 1]

@[expose]
def w182 : List (Fin 4) := [1, 0, 0, 1, 1]

@[expose]
def w183 : List (Fin 4) := [3, 0, 0, 1, 1]

@[expose]
def w184 : List (Fin 4) := [0, 1, 0, 1, 1]

@[expose]
def w185 : List (Fin 4) := [1, 1, 0, 1, 1]

@[expose]
def w186 : List (Fin 4) := [2, 1, 0, 1, 1]

@[expose]
def w187 : List (Fin 4) := [0, 3, 0, 1, 1]

@[expose]
def w188 : List (Fin 4) := [2, 3, 0, 1, 1]

@[expose]
def w189 : List (Fin 4) := [3, 3, 0, 1, 1]

@[expose]
def w190 : List (Fin 4) := [0, 0, 1, 1, 1]

@[expose]
def w191 : List (Fin 4) := [1, 0, 1, 1, 1]

@[expose]
def w192 : List (Fin 4) := [1, 1, 1, 1, 1]

@[expose]
def w193 : List (Fin 4) := [0, 1, 2, 1, 1]

@[expose]
def w194 : List (Fin 4) := [1, 1, 2, 1, 1]

@[expose]
def w195 : List (Fin 4) := [1, 2, 2, 1, 1]

@[expose]
def w196 : List (Fin 4) := [2, 2, 2, 1, 1]

@[expose]
def w197 : List (Fin 4) := [3, 2, 2, 1, 1]

@[expose]
def w198 : List (Fin 4) := [0, 3, 2, 1, 1]

@[expose]
def w199 : List (Fin 4) := [2, 3, 2, 1, 1]

@[expose]
def w200 : List (Fin 4) := [3, 3, 2, 1, 1]

@[expose]
def w201 : List (Fin 4) := [0, 0, 1, 2, 1]

@[expose]
def w202 : List (Fin 4) := [1, 0, 1, 2, 1]

@[expose]
def w203 : List (Fin 4) := [3, 0, 1, 2, 1]

@[expose]
def w204 : List (Fin 4) := [0, 1, 1, 2, 1]

@[expose]
def w205 : List (Fin 4) := [1, 1, 1, 2, 1]

@[expose]
def w206 : List (Fin 4) := [2, 1, 1, 2, 1]

@[expose]
def w207 : List (Fin 4) := [3, 2, 1, 2, 1]

@[expose]
def w208 : List (Fin 4) := [1, 1, 2, 2, 1]

@[expose]
def w209 : List (Fin 4) := [2, 1, 2, 2, 1]

@[expose]
def w210 : List (Fin 4) := [2, 2, 2, 2, 1]

@[expose]
def w211 : List (Fin 4) := [3, 2, 2, 2, 1]

@[expose]
def w212 : List (Fin 4) := [0, 3, 2, 2, 1]

@[expose]
def w213 : List (Fin 4) := [2, 3, 2, 2, 1]

@[expose]
def w214 : List (Fin 4) := [3, 3, 2, 2, 1]

@[expose]
def w215 : List (Fin 4) := [0, 0, 3, 2, 1]

@[expose]
def w216 : List (Fin 4) := [1, 0, 3, 2, 1]

@[expose]
def w217 : List (Fin 4) := [3, 0, 3, 2, 1]

@[expose]
def w218 : List (Fin 4) := [2, 2, 3, 2, 1]

@[expose]
def w219 : List (Fin 4) := [0, 3, 3, 2, 1]

@[expose]
def w220 : List (Fin 4) := [2, 3, 3, 2, 1]

@[expose]
def w221 : List (Fin 4) := [0, 0, 1, 2, 2]

@[expose]
def w222 : List (Fin 4) := [3, 0, 1, 2, 2]

@[expose]
def w223 : List (Fin 4) := [0, 1, 1, 2, 2]

@[expose]
def w224 : List (Fin 4) := [2, 1, 1, 2, 2]

@[expose]
def w225 : List (Fin 4) := [1, 2, 1, 2, 2]

@[expose]
def w226 : List (Fin 4) := [2, 2, 1, 2, 2]

@[expose]
def w227 : List (Fin 4) := [3, 2, 1, 2, 2]

@[expose]
def w228 : List (Fin 4) := [1, 2, 2, 2, 2]

@[expose]
def w229 : List (Fin 4) := [2, 2, 2, 2, 2]

@[expose]
def w230 : List (Fin 4) := [3, 2, 2, 2, 2]

@[expose]
def w231 : List (Fin 4) := [2, 3, 2, 2, 2]

@[expose]
def w232 : List (Fin 4) := [1, 2, 3, 2, 2]

@[expose]
def w233 : List (Fin 4) := [3, 2, 3, 2, 2]

@[expose]
def w234 : List (Fin 4) := [0, 3, 3, 2, 2]

@[expose]
def w235 : List (Fin 4) := [2, 3, 3, 2, 2]

@[expose]
def w236 : List (Fin 4) := [3, 3, 3, 2, 2]

@[expose]
def w237 : List (Fin 4) := [1, 0, 0, 3, 2]

@[expose]
def w238 : List (Fin 4) := [3, 0, 0, 3, 2]

@[expose]
def w239 : List (Fin 4) := [1, 1, 0, 3, 2]

@[expose]
def w240 : List (Fin 4) := [2, 1, 0, 3, 2]

@[expose]
def w241 : List (Fin 4) := [0, 3, 0, 3, 2]

@[expose]
def w242 : List (Fin 4) := [2, 3, 0, 3, 2]

@[expose]
def w243 : List (Fin 4) := [3, 3, 0, 3, 2]

@[expose]
def w244 : List (Fin 4) := [1, 2, 2, 3, 2]

@[expose]
def w245 : List (Fin 4) := [2, 2, 2, 3, 2]

@[expose]
def w246 : List (Fin 4) := [3, 2, 2, 3, 2]

@[expose]
def w247 : List (Fin 4) := [3, 3, 2, 3, 2]

@[expose]
def w248 : List (Fin 4) := [1, 0, 3, 3, 2]

@[expose]
def w249 : List (Fin 4) := [3, 0, 3, 3, 2]

@[expose]
def w250 : List (Fin 4) := [2, 2, 3, 3, 2]

@[expose]
def w251 : List (Fin 4) := [3, 2, 3, 3, 2]

@[expose]
def w252 : List (Fin 4) := [1, 0, 0, 0, 0, 0]

@[expose]
def w253 : List (Fin 4) := [3, 0, 0, 0, 0, 0]

@[expose]
def w254 : List (Fin 4) := [0, 1, 0, 0, 0, 0]

@[expose]
def w255 : List (Fin 4) := [1, 1, 0, 0, 0, 0]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
