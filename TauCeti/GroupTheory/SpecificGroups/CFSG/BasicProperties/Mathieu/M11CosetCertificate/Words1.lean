/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableFast

/-!
# M11 coset certificate: Words1

Literal defining words and their block representation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def w256 : List (Fin 4) := [2, 1, 0, 0, 0, 0]

@[expose]
def w257 : List (Fin 4) := [2, 3, 0, 0, 0, 0]

@[expose]
def w258 : List (Fin 4) := [3, 3, 0, 0, 0, 0]

@[expose]
def w259 : List (Fin 4) := [0, 0, 1, 0, 0, 0]

@[expose]
def w260 : List (Fin 4) := [1, 0, 1, 0, 0, 0]

@[expose]
def w261 : List (Fin 4) := [3, 0, 1, 0, 0, 0]

@[expose]
def w262 : List (Fin 4) := [0, 1, 1, 0, 0, 0]

@[expose]
def w263 : List (Fin 4) := [1, 1, 1, 0, 0, 0]

@[expose]
def w264 : List (Fin 4) := [2, 1, 1, 0, 0, 0]

@[expose]
def w265 : List (Fin 4) := [2, 2, 1, 0, 0, 0]

@[expose]
def w266 : List (Fin 4) := [3, 2, 1, 0, 0, 0]

@[expose]
def w267 : List (Fin 4) := [1, 2, 3, 0, 0, 0]

@[expose]
def w268 : List (Fin 4) := [2, 2, 3, 0, 0, 0]

@[expose]
def w269 : List (Fin 4) := [3, 2, 3, 0, 0, 0]

@[expose]
def w270 : List (Fin 4) := [0, 3, 3, 0, 0, 0]

@[expose]
def w271 : List (Fin 4) := [3, 3, 3, 0, 0, 0]

@[expose]
def w272 : List (Fin 4) := [0, 0, 0, 1, 0, 0]

@[expose]
def w273 : List (Fin 4) := [1, 0, 0, 1, 0, 0]

@[expose]
def w274 : List (Fin 4) := [3, 0, 0, 1, 0, 0]

@[expose]
def w275 : List (Fin 4) := [0, 1, 0, 1, 0, 0]

@[expose]
def w276 : List (Fin 4) := [2, 1, 0, 1, 0, 0]

@[expose]
def w277 : List (Fin 4) := [0, 3, 0, 1, 0, 0]

@[expose]
def w278 : List (Fin 4) := [2, 3, 0, 1, 0, 0]

@[expose]
def w279 : List (Fin 4) := [3, 3, 0, 1, 0, 0]

@[expose]
def w280 : List (Fin 4) := [0, 0, 1, 1, 0, 0]

@[expose]
def w281 : List (Fin 4) := [1, 0, 1, 1, 0, 0]

@[expose]
def w282 : List (Fin 4) := [0, 1, 1, 1, 0, 0]

@[expose]
def w283 : List (Fin 4) := [1, 1, 1, 1, 0, 0]

@[expose]
def w284 : List (Fin 4) := [2, 1, 1, 1, 0, 0]

@[expose]
def w285 : List (Fin 4) := [1, 2, 1, 1, 0, 0]

@[expose]
def w286 : List (Fin 4) := [2, 2, 1, 1, 0, 0]

@[expose]
def w287 : List (Fin 4) := [3, 2, 1, 1, 0, 0]

@[expose]
def w288 : List (Fin 4) := [1, 2, 2, 1, 0, 0]

@[expose]
def w289 : List (Fin 4) := [2, 2, 2, 1, 0, 0]

@[expose]
def w290 : List (Fin 4) := [3, 2, 2, 1, 0, 0]

@[expose]
def w291 : List (Fin 4) := [1, 2, 2, 3, 0, 0]

@[expose]
def w292 : List (Fin 4) := [2, 2, 2, 3, 0, 0]

@[expose]
def w293 : List (Fin 4) := [3, 2, 2, 3, 0, 0]

@[expose]
def w294 : List (Fin 4) := [0, 3, 2, 3, 0, 0]

@[expose]
def w295 : List (Fin 4) := [2, 3, 2, 3, 0, 0]

@[expose]
def w296 : List (Fin 4) := [3, 3, 2, 3, 0, 0]

@[expose]
def w297 : List (Fin 4) := [0, 0, 3, 3, 0, 0]

@[expose]
def w298 : List (Fin 4) := [1, 0, 3, 3, 0, 0]

@[expose]
def w299 : List (Fin 4) := [1, 2, 3, 3, 0, 0]

@[expose]
def w300 : List (Fin 4) := [2, 2, 3, 3, 0, 0]

@[expose]
def w301 : List (Fin 4) := [0, 0, 0, 0, 1, 0]

@[expose]
def w302 : List (Fin 4) := [3, 0, 0, 0, 1, 0]

@[expose]
def w303 : List (Fin 4) := [0, 1, 0, 0, 1, 0]

@[expose]
def w304 : List (Fin 4) := [1, 1, 0, 0, 1, 0]

@[expose]
def w305 : List (Fin 4) := [2, 1, 0, 0, 1, 0]

@[expose]
def w306 : List (Fin 4) := [0, 3, 0, 0, 1, 0]

@[expose]
def w307 : List (Fin 4) := [2, 3, 0, 0, 1, 0]

@[expose]
def w308 : List (Fin 4) := [3, 3, 0, 0, 1, 0]

@[expose]
def w309 : List (Fin 4) := [0, 0, 1, 0, 1, 0]

@[expose]
def w310 : List (Fin 4) := [1, 0, 1, 0, 1, 0]

@[expose]
def w311 : List (Fin 4) := [0, 1, 1, 0, 1, 0]

@[expose]
def w312 : List (Fin 4) := [1, 1, 1, 0, 1, 0]

@[expose]
def w313 : List (Fin 4) := [2, 1, 1, 0, 1, 0]

@[expose]
def w314 : List (Fin 4) := [2, 2, 1, 0, 1, 0]

@[expose]
def w315 : List (Fin 4) := [3, 2, 1, 0, 1, 0]

@[expose]
def w316 : List (Fin 4) := [0, 0, 3, 0, 1, 0]

@[expose]
def w317 : List (Fin 4) := [3, 0, 3, 0, 1, 0]

@[expose]
def w318 : List (Fin 4) := [2, 3, 3, 0, 1, 0]

@[expose]
def w319 : List (Fin 4) := [0, 0, 0, 1, 1, 0]

@[expose]
def w320 : List (Fin 4) := [1, 0, 0, 1, 1, 0]

@[expose]
def w321 : List (Fin 4) := [3, 0, 0, 1, 1, 0]

@[expose]
def w322 : List (Fin 4) := [0, 1, 0, 1, 1, 0]

@[expose]
def w323 : List (Fin 4) := [1, 1, 0, 1, 1, 0]

@[expose]
def w324 : List (Fin 4) := [2, 1, 0, 1, 1, 0]

@[expose]
def w325 : List (Fin 4) := [0, 3, 0, 1, 1, 0]

@[expose]
def w326 : List (Fin 4) := [2, 3, 0, 1, 1, 0]

@[expose]
def w327 : List (Fin 4) := [3, 3, 0, 1, 1, 0]

@[expose]
def w328 : List (Fin 4) := [0, 1, 1, 1, 1, 0]

@[expose]
def w329 : List (Fin 4) := [1, 1, 1, 1, 1, 0]

@[expose]
def w330 : List (Fin 4) := [2, 2, 1, 1, 1, 0]

@[expose]
def w331 : List (Fin 4) := [3, 2, 1, 1, 1, 0]

@[expose]
def w332 : List (Fin 4) := [0, 1, 2, 1, 1, 0]

@[expose]
def w333 : List (Fin 4) := [1, 1, 2, 1, 1, 0]

@[expose]
def w334 : List (Fin 4) := [1, 2, 2, 1, 1, 0]

@[expose]
def w335 : List (Fin 4) := [2, 3, 2, 1, 1, 0]

@[expose]
def w336 : List (Fin 4) := [1, 0, 1, 2, 1, 0]

@[expose]
def w337 : List (Fin 4) := [3, 0, 1, 2, 1, 0]

@[expose]
def w338 : List (Fin 4) := [1, 1, 1, 2, 1, 0]

@[expose]
def w339 : List (Fin 4) := [2, 1, 1, 2, 1, 0]

@[expose]
def w340 : List (Fin 4) := [0, 1, 2, 2, 1, 0]

@[expose]
def w341 : List (Fin 4) := [1, 1, 2, 2, 1, 0]

@[expose]
def w342 : List (Fin 4) := [2, 1, 2, 2, 1, 0]

@[expose]
def w343 : List (Fin 4) := [2, 2, 2, 2, 1, 0]

@[expose]
def w344 : List (Fin 4) := [3, 2, 2, 2, 1, 0]

@[expose]
def w345 : List (Fin 4) := [0, 3, 2, 2, 1, 0]

@[expose]
def w346 : List (Fin 4) := [2, 3, 2, 2, 1, 0]

@[expose]
def w347 : List (Fin 4) := [3, 3, 2, 2, 1, 0]

@[expose]
def w348 : List (Fin 4) := [0, 0, 3, 2, 1, 0]

@[expose]
def w349 : List (Fin 4) := [1, 0, 3, 2, 1, 0]

@[expose]
def w350 : List (Fin 4) := [3, 0, 3, 2, 1, 0]

@[expose]
def w351 : List (Fin 4) := [2, 2, 3, 2, 1, 0]

@[expose]
def w352 : List (Fin 4) := [0, 3, 3, 2, 1, 0]

@[expose]
def w353 : List (Fin 4) := [2, 3, 3, 2, 1, 0]

@[expose]
def w354 : List (Fin 4) := [0, 0, 0, 0, 3, 0]

@[expose]
def w355 : List (Fin 4) := [0, 1, 0, 0, 3, 0]

@[expose]
def w356 : List (Fin 4) := [1, 1, 0, 0, 3, 0]

@[expose]
def w357 : List (Fin 4) := [2, 1, 0, 0, 3, 0]

@[expose]
def w358 : List (Fin 4) := [0, 3, 0, 0, 3, 0]

@[expose]
def w359 : List (Fin 4) := [2, 3, 0, 0, 3, 0]

@[expose]
def w360 : List (Fin 4) := [3, 3, 0, 0, 3, 0]

@[expose]
def w361 : List (Fin 4) := [0, 0, 1, 0, 3, 0]

@[expose]
def w362 : List (Fin 4) := [1, 0, 1, 0, 3, 0]

@[expose]
def w363 : List (Fin 4) := [0, 1, 1, 0, 3, 0]

@[expose]
def w364 : List (Fin 4) := [1, 1, 1, 0, 3, 0]

@[expose]
def w365 : List (Fin 4) := [2, 1, 1, 0, 3, 0]

@[expose]
def w366 : List (Fin 4) := [1, 2, 1, 0, 3, 0]

@[expose]
def w367 : List (Fin 4) := [2, 2, 1, 0, 3, 0]

@[expose]
def w368 : List (Fin 4) := [0, 1, 1, 2, 3, 0]

@[expose]
def w369 : List (Fin 4) := [1, 1, 1, 2, 3, 0]

@[expose]
def w370 : List (Fin 4) := [1, 2, 2, 2, 3, 0]

@[expose]
def w371 : List (Fin 4) := [2, 2, 2, 2, 3, 0]

@[expose]
def w372 : List (Fin 4) := [3, 2, 2, 2, 3, 0]

@[expose]
def w373 : List (Fin 4) := [0, 0, 3, 2, 3, 0]

@[expose]
def w374 : List (Fin 4) := [3, 0, 3, 2, 3, 0]

@[expose]
def w375 : List (Fin 4) := [1, 2, 3, 2, 3, 0]

@[expose]
def w376 : List (Fin 4) := [2, 2, 3, 2, 3, 0]

@[expose]
def w377 : List (Fin 4) := [0, 3, 3, 2, 3, 0]

@[expose]
def w378 : List (Fin 4) := [2, 3, 3, 2, 3, 0]

@[expose]
def w379 : List (Fin 4) := [3, 3, 3, 2, 3, 0]

@[expose]
def w380 : List (Fin 4) := [1, 0, 0, 3, 3, 0]

@[expose]
def w381 : List (Fin 4) := [3, 0, 0, 3, 3, 0]

@[expose]
def w382 : List (Fin 4) := [0, 1, 0, 3, 3, 0]

@[expose]
def w383 : List (Fin 4) := [1, 1, 0, 3, 3, 0]

@[expose]
def w384 : List (Fin 4) := [0, 3, 0, 3, 3, 0]

@[expose]
def w385 : List (Fin 4) := [2, 3, 0, 3, 3, 0]

@[expose]
def w386 : List (Fin 4) := [3, 3, 0, 3, 3, 0]

@[expose]
def w387 : List (Fin 4) := [1, 1, 2, 3, 3, 0]

@[expose]
def w388 : List (Fin 4) := [2, 1, 2, 3, 3, 0]

@[expose]
def w389 : List (Fin 4) := [1, 2, 2, 3, 3, 0]

@[expose]
def w390 : List (Fin 4) := [2, 2, 2, 3, 3, 0]

@[expose]
def w391 : List (Fin 4) := [2, 3, 2, 3, 3, 0]

@[expose]
def w392 : List (Fin 4) := [3, 3, 2, 3, 3, 0]

@[expose]
def w393 : List (Fin 4) := [1, 2, 3, 3, 3, 0]

@[expose]
def w394 : List (Fin 4) := [0, 0, 0, 0, 0, 1]

@[expose]
def w395 : List (Fin 4) := [1, 0, 0, 0, 0, 1]

@[expose]
def w396 : List (Fin 4) := [3, 0, 0, 0, 0, 1]

@[expose]
def w397 : List (Fin 4) := [0, 1, 0, 0, 0, 1]

@[expose]
def w398 : List (Fin 4) := [1, 1, 0, 0, 0, 1]

@[expose]
def w399 : List (Fin 4) := [2, 1, 0, 0, 0, 1]

@[expose]
def w400 : List (Fin 4) := [2, 3, 0, 0, 0, 1]

@[expose]
def w401 : List (Fin 4) := [0, 0, 1, 0, 0, 1]

@[expose]
def w402 : List (Fin 4) := [1, 0, 1, 0, 0, 1]

@[expose]
def w403 : List (Fin 4) := [1, 1, 1, 0, 0, 1]

@[expose]
def w404 : List (Fin 4) := [0, 0, 3, 0, 0, 1]

@[expose]
def w405 : List (Fin 4) := [1, 0, 3, 0, 0, 1]

@[expose]
def w406 : List (Fin 4) := [1, 2, 3, 0, 0, 1]

@[expose]
def w407 : List (Fin 4) := [3, 2, 3, 0, 0, 1]

@[expose]
def w408 : List (Fin 4) := [0, 3, 3, 0, 0, 1]

@[expose]
def w409 : List (Fin 4) := [2, 3, 3, 0, 0, 1]

@[expose]
def w410 : List (Fin 4) := [3, 3, 3, 0, 0, 1]

@[expose]
def w411 : List (Fin 4) := [0, 0, 0, 1, 0, 1]

@[expose]
def w412 : List (Fin 4) := [3, 0, 0, 1, 0, 1]

@[expose]
def w413 : List (Fin 4) := [0, 1, 0, 1, 0, 1]

@[expose]
def w414 : List (Fin 4) := [1, 1, 0, 1, 0, 1]

@[expose]
def w415 : List (Fin 4) := [0, 1, 1, 1, 0, 1]

@[expose]
def w416 : List (Fin 4) := [1, 1, 1, 1, 0, 1]

@[expose]
def w417 : List (Fin 4) := [2, 1, 1, 1, 0, 1]

@[expose]
def w418 : List (Fin 4) := [1, 2, 1, 1, 0, 1]

@[expose]
def w419 : List (Fin 4) := [3, 2, 1, 1, 0, 1]

@[expose]
def w420 : List (Fin 4) := [0, 1, 2, 1, 0, 1]

@[expose]
def w421 : List (Fin 4) := [1, 1, 2, 1, 0, 1]

@[expose]
def w422 : List (Fin 4) := [1, 2, 2, 1, 0, 1]

@[expose]
def w423 : List (Fin 4) := [2, 2, 2, 1, 0, 1]

@[expose]
def w424 : List (Fin 4) := [3, 2, 2, 1, 0, 1]

@[expose]
def w425 : List (Fin 4) := [0, 3, 2, 1, 0, 1]

@[expose]
def w426 : List (Fin 4) := [3, 3, 2, 1, 0, 1]

@[expose]
def w427 : List (Fin 4) := [0, 1, 2, 3, 0, 1]

@[expose]
def w428 : List (Fin 4) := [1, 1, 2, 3, 0, 1]

@[expose]
def w429 : List (Fin 4) := [1, 2, 2, 3, 0, 1]

@[expose]
def w430 : List (Fin 4) := [3, 2, 2, 3, 0, 1]

@[expose]
def w431 : List (Fin 4) := [0, 3, 2, 3, 0, 1]

@[expose]
def w432 : List (Fin 4) := [2, 3, 2, 3, 0, 1]

@[expose]
def w433 : List (Fin 4) := [3, 3, 2, 3, 0, 1]

@[expose]
def w434 : List (Fin 4) := [0, 0, 3, 3, 0, 1]

@[expose]
def w435 : List (Fin 4) := [1, 0, 3, 3, 0, 1]

@[expose]
def w436 : List (Fin 4) := [0, 3, 3, 3, 0, 1]

@[expose]
def w437 : List (Fin 4) := [2, 3, 3, 3, 0, 1]

@[expose]
def w438 : List (Fin 4) := [0, 0, 0, 0, 1, 1]

@[expose]
def w439 : List (Fin 4) := [1, 0, 0, 0, 1, 1]

@[expose]
def w440 : List (Fin 4) := [0, 1, 0, 0, 1, 1]

@[expose]
def w441 : List (Fin 4) := [2, 1, 0, 0, 1, 1]

@[expose]
def w442 : List (Fin 4) := [0, 3, 0, 0, 1, 1]

@[expose]
def w443 : List (Fin 4) := [2, 3, 0, 0, 1, 1]

@[expose]
def w444 : List (Fin 4) := [0, 0, 1, 0, 1, 1]

@[expose]
def w445 : List (Fin 4) := [1, 0, 1, 0, 1, 1]

@[expose]
def w446 : List (Fin 4) := [0, 1, 1, 0, 1, 1]

@[expose]
def w447 : List (Fin 4) := [1, 1, 1, 0, 1, 1]

@[expose]
def w448 : List (Fin 4) := [2, 1, 1, 0, 1, 1]

@[expose]
def w449 : List (Fin 4) := [1, 2, 1, 0, 1, 1]

@[expose]
def w450 : List (Fin 4) := [2, 2, 1, 0, 1, 1]

@[expose]
def w451 : List (Fin 4) := [3, 2, 1, 0, 1, 1]

@[expose]
def w452 : List (Fin 4) := [0, 0, 3, 0, 1, 1]

@[expose]
def w453 : List (Fin 4) := [1, 0, 3, 0, 1, 1]

@[expose]
def w454 : List (Fin 4) := [1, 2, 3, 0, 1, 1]

@[expose]
def w455 : List (Fin 4) := [3, 2, 3, 0, 1, 1]

@[expose]
def w456 : List (Fin 4) := [2, 3, 3, 0, 1, 1]

@[expose]
def w457 : List (Fin 4) := [0, 1, 0, 1, 1, 1]

@[expose]
def w458 : List (Fin 4) := [1, 1, 0, 1, 1, 1]

@[expose]
def w459 : List (Fin 4) := [2, 1, 0, 1, 1, 1]

@[expose]
def w460 : List (Fin 4) := [0, 1, 1, 1, 1, 1]

@[expose]
def w461 : List (Fin 4) := [3, 0, 1, 2, 1, 1]

@[expose]
def w462 : List (Fin 4) := [0, 1, 1, 2, 1, 1]

@[expose]
def w463 : List (Fin 4) := [1, 1, 1, 2, 1, 1]

@[expose]
def w464 : List (Fin 4) := [2, 1, 1, 2, 1, 1]

@[expose]
def w465 : List (Fin 4) := [0, 1, 2, 2, 1, 1]

@[expose]
def w466 : List (Fin 4) := [2, 1, 2, 2, 1, 1]

@[expose]
def w467 : List (Fin 4) := [3, 2, 2, 2, 1, 1]

@[expose]
def w468 : List (Fin 4) := [0, 3, 2, 2, 1, 1]

@[expose]
def w469 : List (Fin 4) := [2, 3, 2, 2, 1, 1]

@[expose]
def w470 : List (Fin 4) := [3, 3, 2, 2, 1, 1]

@[expose]
def w471 : List (Fin 4) := [0, 0, 3, 2, 1, 1]

@[expose]
def w472 : List (Fin 4) := [1, 0, 3, 2, 1, 1]

@[expose]
def w473 : List (Fin 4) := [2, 3, 3, 2, 1, 1]

@[expose]
def w474 : List (Fin 4) := [0, 0, 0, 1, 2, 1]

@[expose]
def w475 : List (Fin 4) := [1, 0, 0, 1, 2, 1]

@[expose]
def w476 : List (Fin 4) := [3, 0, 0, 1, 2, 1]

@[expose]
def w477 : List (Fin 4) := [1, 1, 0, 1, 2, 1]

@[expose]
def w478 : List (Fin 4) := [0, 3, 0, 1, 2, 1]

@[expose]
def w479 : List (Fin 4) := [2, 3, 0, 1, 2, 1]

@[expose]
def w480 : List (Fin 4) := [0, 0, 1, 1, 2, 1]

@[expose]
def w481 : List (Fin 4) := [1, 0, 1, 1, 2, 1]

@[expose]
def w482 : List (Fin 4) := [3, 0, 1, 1, 2, 1]

@[expose]
def w483 : List (Fin 4) := [2, 1, 1, 1, 2, 1]

@[expose]
def w484 : List (Fin 4) := [1, 2, 1, 1, 2, 1]

@[expose]
def w485 : List (Fin 4) := [2, 2, 1, 1, 2, 1]

@[expose]
def w486 : List (Fin 4) := [0, 3, 2, 1, 2, 1]

@[expose]
def w487 : List (Fin 4) := [3, 3, 2, 1, 2, 1]

@[expose]
def w488 : List (Fin 4) := [2, 1, 1, 2, 2, 1]

@[expose]
def w489 : List (Fin 4) := [1, 2, 1, 2, 2, 1]

@[expose]
def w490 : List (Fin 4) := [2, 2, 2, 2, 2, 1]

@[expose]
def w491 : List (Fin 4) := [3, 2, 2, 2, 2, 1]

@[expose]
def w492 : List (Fin 4) := [2, 3, 2, 2, 2, 1]

@[expose]
def w493 : List (Fin 4) := [1, 0, 3, 2, 2, 1]

@[expose]
def w494 : List (Fin 4) := [1, 2, 3, 2, 2, 1]

@[expose]
def w495 : List (Fin 4) := [2, 2, 3, 2, 2, 1]

@[expose]
def w496 : List (Fin 4) := [0, 3, 3, 2, 2, 1]

@[expose]
def w497 : List (Fin 4) := [2, 3, 3, 2, 2, 1]

@[expose]
def w498 : List (Fin 4) := [0, 0, 0, 3, 2, 1]

@[expose]
def w499 : List (Fin 4) := [1, 0, 0, 3, 2, 1]

@[expose]
def w500 : List (Fin 4) := [3, 0, 0, 3, 2, 1]

@[expose]
def w501 : List (Fin 4) := [2, 1, 0, 3, 2, 1]

@[expose]
def w502 : List (Fin 4) := [0, 3, 0, 3, 2, 1]

@[expose]
def w503 : List (Fin 4) := [2, 3, 0, 3, 2, 1]

@[expose]
def w504 : List (Fin 4) := [3, 2, 2, 3, 2, 1]

@[expose]
def w505 : List (Fin 4) := [0, 0, 3, 3, 2, 1]

@[expose]
def w506 : List (Fin 4) := [3, 0, 3, 3, 2, 1]

@[expose]
def w507 : List (Fin 4) := [1, 2, 3, 3, 2, 1]

@[expose]
def w508 : List (Fin 4) := [2, 2, 3, 3, 2, 1]

@[expose]
def w509 : List (Fin 4) := [1, 0, 0, 1, 2, 2]

@[expose]
def w510 : List (Fin 4) := [3, 0, 0, 1, 2, 2]

@[expose]
def w511 : List (Fin 4) := [2, 3, 0, 1, 2, 2]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
