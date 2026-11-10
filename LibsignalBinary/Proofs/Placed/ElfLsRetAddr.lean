/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Proofs.Placed.Bridge

/-!
# Block Byte-Length Table and Return-Address Predicates

Defines `lsLen`, a depth-10 binary decision tree giving the byte length of each block `0 .. 623` in
`libsignalSessionLib` without unfolding `CodeBlock` blobs, together with the caller return-address
predicates `LsRetAddr` (`j < 623`, excluding `String::clone` in block `623`) and `LsRetAddr624`
(`j < 624`) and their `@[wp_norm]` introduction rules.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Placed.ElfLsRetAddr

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement lsmpl libsignalSessionLib)

/-- Closed byte-length table for the 624 blocks (`0 .. 623`) of `libsignalSessionLib`.
    Structured as a balanced binary decision tree of depth 10 (`≤ 10` `Nat` comparisons per lookup)
    so `simp (config := { decide := true })` and `decide` evaluate `lsLen j` in O(1) heartbeats
    without unfolding `GeneratedLean` code blobs or linear 624-element list walks. -/
def lsLen (j : Nat) : Nat :=
  if j < 624 then
    if j < 312 then if j < 156 then if j < 78 then if j < 39 then if j < 19 then if j < 9 then if j < 4 then if j < 2 then if j < 1 then 88 else 800 else if j < 3 then 180 else 188 else if j < 6 then if j < 5 then 164 else 184 else if j < 7 then 272 else if j < 8 then 1084 else 300 else if j < 14 then if j < 11 then if j < 10 then 300 else 1064 else if j < 12 then 2536 else if j < 13 then 2044 else 140 else if j < 16 then if j < 15 then 2788 else 2800 else if j < 17 then 456 else if j < 18 then 192 else 268 else if j < 29 then if j < 24 then if j < 21 then if j < 20 then 1308 else 316 else if j < 22 then 1024 else if j < 23 then 100 else 112 else if j < 26 then if j < 25 then 2596 else 396 else if j < 27 then 284 else if j < 28 then 524 else 272 else if j < 34 then if j < 31 then if j < 30 then 404 else 972 else if j < 32 then 88 else if j < 33 then 228 else 312 else if j < 36 then if j < 35 then 52 else 88 else if j < 37 then 328 else if j < 38 then 252 else 144 else if j < 58 then if j < 48 then if j < 43 then if j < 41 then if j < 40 then 116 else 460 else if j < 42 then 2196 else 104 else if j < 45 then if j < 44 then 104 else 104 else if j < 46 then 180 else if j < 47 then 1468 else 68 else if j < 53 then if j < 50 then if j < 49 then 60 else 200 else if j < 51 then 804 else if j < 52 then 412 else 912 else if j < 55 then if j < 54 then 1220 else 540 else if j < 56 then 128 else if j < 57 then 124 else 1512 else if j < 68 then if j < 63 then if j < 60 then if j < 59 then 708 else 264 else if j < 61 then 1264 else if j < 62 then 240 else 888 else if j < 65 then if j < 64 then 2224 else 280 else if j < 66 then 740 else if j < 67 then 324 else 300 else if j < 73 then if j < 70 then if j < 69 then 812 else 444 else if j < 71 then 364 else if j < 72 then 144 else 1380 else if j < 75 then if j < 74 then 812 else 20 else if j < 76 then 608 else if j < 77 then 704 else 1448 else if j < 117 then if j < 97 then if j < 87 then if j < 82 then if j < 80 then if j < 79 then 20 else 1728 else if j < 81 then 1212 else 60 else if j < 84 then if j < 83 then 872 else 568 else if j < 85 then 940 else if j < 86 then 1896 else 1132 else if j < 92 then if j < 89 then if j < 88 then 156 else 416 else if j < 90 then 48 else if j < 91 then 1896 else 56 else if j < 94 then if j < 93 then 28 else 16 else if j < 95 then 8 else if j < 96 then 20 else 8 else if j < 107 then if j < 102 then if j < 99 then if j < 98 then 8 else 28 else if j < 100 then 224 else if j < 101 then 8 else 20 else if j < 104 then if j < 103 then 8 else 8 else if j < 105 then 8 else if j < 106 then 8 else 8 else if j < 112 then if j < 109 then if j < 108 then 4 else 400 else if j < 110 then 212 else if j < 111 then 8 else 2700 else if j < 114 then if j < 113 then 288 else 4 else if j < 115 then 2164 else if j < 116 then 24 else 264 else if j < 136 then if j < 126 then if j < 121 then if j < 119 then if j < 118 then 260 else 264 else if j < 120 then 520 else 20 else if j < 123 then if j < 122 then 20 else 112 else if j < 124 then 448 else if j < 125 then 13744 else 864 else if j < 131 then if j < 128 then if j < 127 then 232 else 152 else if j < 129 then 88 else if j < 130 then 88 else 420 else if j < 133 then if j < 132 then 3288 else 228 else if j < 134 then 156 else if j < 135 then 24 else 384 else if j < 146 then if j < 141 then if j < 138 then if j < 137 then 224 else 420 else if j < 139 then 420 else if j < 140 then 276 else 724 else if j < 143 then if j < 142 then 136 else 252 else if j < 144 then 136 else if j < 145 then 52 else 236 else if j < 151 then if j < 148 then if j < 147 then 888 else 580 else if j < 149 then 988 else if j < 150 then 1936 else 320 else if j < 153 then if j < 152 then 588 else 368 else if j < 154 then 220 else if j < 155 then 676 else 600 else if j < 234 then if j < 195 then if j < 175 then if j < 165 then if j < 160 then if j < 158 then if j < 157 then 788 else 120 else if j < 159 then 440 else 436 else if j < 162 then if j < 161 then 168 else 872 else if j < 163 then 372 else if j < 164 then 236 else 44 else if j < 170 then if j < 167 then if j < 166 then 20 else 28 else if j < 168 then 8 else if j < 169 then 8 else 8 else if j < 172 then if j < 171 then 20 else 484 else if j < 173 then 236 else if j < 174 then 304 else 64 else if j < 185 then if j < 180 then if j < 177 then if j < 176 then 284 else 20 else if j < 178 then 1644 else if j < 179 then 504 else 288 else if j < 182 then if j < 181 then 372 else 284 else if j < 183 then 124 else if j < 184 then 24 else 124 else if j < 190 then if j < 187 then if j < 186 then 328 else 264 else if j < 188 then 40 else if j < 189 then 288 else 284 else if j < 192 then if j < 191 then 52 else 20 else if j < 193 then 328 else if j < 194 then 236 else 16 else if j < 214 then if j < 204 then if j < 199 then if j < 197 then if j < 196 then 4 else 20 else if j < 198 then 9804 else 4036 else if j < 201 then if j < 200 then 4 else 4 else if j < 202 then 272 else if j < 203 then 236 else 40 else if j < 209 then if j < 206 then if j < 205 then 1132 else 84 else if j < 207 then 212 else if j < 208 then 224 else 84 else if j < 211 then if j < 210 then 424 else 20 else if j < 212 then 272 else if j < 213 then 28 else 840 else if j < 224 then if j < 219 then if j < 216 then if j < 215 then 60 else 72 else if j < 217 then 20 else if j < 218 then 40 else 120 else if j < 221 then if j < 220 then 56 else 32 else if j < 222 then 168 else if j < 223 then 976 else 148 else if j < 229 then if j < 226 then if j < 225 then 4 else 84 else if j < 227 then 20 else if j < 228 then 20 else 20 else if j < 231 then if j < 230 then 148 else 140 else if j < 232 then 20 else if j < 233 then 8 else 264 else if j < 273 then if j < 253 then if j < 243 then if j < 238 then if j < 236 then if j < 235 then 520 else 380 else if j < 237 then 236 else 240 else if j < 240 then if j < 239 then 32 else 128 else if j < 241 then 128 else if j < 242 then 264 else 128 else if j < 248 then if j < 245 then if j < 244 then 264 else 128 else if j < 246 then 100 else if j < 247 then 84 else 312 else if j < 250 then if j < 249 then 388 else 20 else if j < 251 then 252 else if j < 252 then 20 else 96 else if j < 263 then if j < 258 then if j < 255 then if j < 254 then 788 else 380 else if j < 256 then 536 else if j < 257 then 136 else 128 else if j < 260 then if j < 259 then 36 else 164 else if j < 261 then 124 else if j < 262 then 92 else 88 else if j < 268 then if j < 265 then if j < 264 then 420 else 420 else if j < 266 then 420 else if j < 267 then 116 else 692 else if j < 270 then if j < 269 then 24 else 192 else if j < 271 then 160 else if j < 272 then 208 else 8 else if j < 292 then if j < 282 then if j < 277 then if j < 275 then if j < 274 then 436 else 72 else if j < 276 then 132 else 100 else if j < 279 then if j < 278 then 112 else 112 else if j < 280 then 136 else if j < 281 then 96 else 236 else if j < 287 then if j < 284 then if j < 283 then 156 else 216 else if j < 285 then 192 else if j < 286 then 236 else 144 else if j < 289 then if j < 288 then 136 else 152 else if j < 290 then 252 else if j < 291 then 912 else 580 else if j < 302 then if j < 297 then if j < 294 then if j < 293 then 1064 else 448 else if j < 295 then 576 else if j < 296 then 468 else 908 else if j < 299 then if j < 298 then 848 else 3420 else if j < 300 then 580 else if j < 301 then 616 else 960 else if j < 307 then if j < 304 then if j < 303 then 1108 else 520 else if j < 305 then 1096 else if j < 306 then 856 else 1024 else if j < 309 then if j < 308 then 520 else 956 else if j < 310 then 516 else if j < 311 then 1164 else 668 else if j < 468 then if j < 390 then if j < 351 then if j < 331 then if j < 321 then if j < 316 then if j < 314 then if j < 313 then 724 else 336 else if j < 315 then 644 else 400 else if j < 318 then if j < 317 then 236 else 732 else if j < 319 then 664 else if j < 320 then 876 else 140 else if j < 326 then if j < 323 then if j < 322 then 64 else 64 else if j < 324 then 304 else if j < 325 then 448 else 2980 else if j < 328 then if j < 327 then 656 else 428 else if j < 329 then 72 else if j < 330 then 3036 else 200 else if j < 341 then if j < 336 then if j < 333 then if j < 332 then 388 else 19536 else if j < 334 then 11644 else if j < 335 then 2460 else 164 else if j < 338 then if j < 337 then 156 else 452 else if j < 339 then 396 else if j < 340 then 432 else 192 else if j < 346 then if j < 343 then if j < 342 then 428 else 148 else if j < 344 then 212 else if j < 345 then 128 else 164 else if j < 348 then if j < 347 then 268 else 1124 else if j < 349 then 356 else if j < 350 then 612 else 2056 else if j < 370 then if j < 360 then if j < 355 then if j < 353 then if j < 352 then 848 else 440 else if j < 354 then 152 else 136 else if j < 357 then if j < 356 then 124 else 104 else if j < 358 then 104 else if j < 359 then 104 else 104 else if j < 365 then if j < 362 then if j < 361 then 104 else 180 else if j < 363 then 272 else if j < 364 then 464 else 1184 else if j < 367 then if j < 366 then 956 else 1248 else if j < 368 then 596 else if j < 369 then 592 else 1300 else if j < 380 then if j < 375 then if j < 372 then if j < 371 then 428 else 776 else if j < 373 then 680 else if j < 374 then 708 else 1748 else if j < 377 then if j < 376 then 704 else 1300 else if j < 378 then 408 else if j < 379 then 188 else 1892 else if j < 385 then if j < 382 then if j < 381 then 36 else 284 else if j < 383 then 340 else if j < 384 then 40 else 236 else if j < 387 then if j < 386 then 68 else 496 else if j < 388 then 372 else if j < 389 then 44 else 236 else if j < 429 then if j < 409 then if j < 399 then if j < 394 then if j < 392 then if j < 391 then 44 else 20 else if j < 393 then 144 else 52 else if j < 396 then if j < 395 then 72 else 20 else if j < 397 then 8 else if j < 398 then 8 else 44 else if j < 404 then if j < 401 then if j < 400 then 484 else 236 else if j < 402 then 304 else if j < 403 then 2164 else 20 else if j < 406 then if j < 405 then 284 else 1644 else if j < 407 then 504 else if j < 408 then 288 else 372 else if j < 419 then if j < 414 then if j < 411 then if j < 410 then 24 else 124 else if j < 412 then 328 else if j < 413 then 776 else 264 else if j < 416 then if j < 415 then 288 else 284 else if j < 417 then 4916 else if j < 418 then 836 else 2064 else if j < 424 then if j < 421 then if j < 420 then 516 else 20 else if j < 422 then 328 else if j < 423 then 20 else 64 else if j < 426 then if j < 425 then 236 else 448 else if j < 427 then 7760 else if j < 428 then 13744 else 864 else if j < 448 then if j < 438 then if j < 433 then if j < 431 then if j < 430 then 232 else 152 else if j < 432 then 88 else 88 else if j < 435 then if j < 434 then 420 else 3288 else if j < 436 then 228 else if j < 437 then 156 else 24 else if j < 443 then if j < 440 then if j < 439 then 384 else 224 else if j < 441 then 420 else if j < 442 then 420 else 276 else if j < 445 then if j < 444 then 724 else 136 else if j < 446 then 252 else if j < 447 then 136 else 52 else if j < 458 then if j < 453 then if j < 450 then if j < 449 then 236 else 888 else if j < 451 then 580 else if j < 452 then 988 else 1936 else if j < 455 then if j < 454 then 320 else 588 else if j < 456 then 368 else if j < 457 then 220 else 676 else if j < 463 then if j < 460 then if j < 459 then 600 else 788 else if j < 461 then 120 else if j < 462 then 440 else 436 else if j < 465 then if j < 464 then 9804 else 4036 else if j < 466 then 168 else if j < 467 then 12 else 44 else if j < 546 then if j < 507 then if j < 487 then if j < 477 then if j < 472 then if j < 470 then if j < 469 then 872 else 372 else if j < 471 then 236 else 44 else if j < 474 then if j < 473 then 20 else 28 else if j < 475 then 8 else if j < 476 then 8 else 8 else if j < 482 then if j < 479 then if j < 478 then 20 else 484 else if j < 480 then 236 else if j < 481 then 304 else 64 else if j < 484 then if j < 483 then 284 else 20 else if j < 485 then 1644 else if j < 486 then 504 else 288 else if j < 497 then if j < 492 then if j < 489 then if j < 488 then 372 else 284 else if j < 490 then 124 else if j < 491 then 24 else 124 else if j < 494 then if j < 493 then 328 else 264 else if j < 495 then 40 else if j < 496 then 288 else 284 else if j < 502 then if j < 499 then if j < 498 then 52 else 20 else if j < 500 then 328 else if j < 501 then 236 else 16 else if j < 504 then if j < 503 then 4 else 20 else if j < 505 then 232 else if j < 506 then 88 else 88 else if j < 526 then if j < 516 then if j < 511 then if j < 509 then if j < 508 then 420 else 3288 else if j < 510 then 368 else 24 else if j < 513 then if j < 512 then 184 else 276 else if j < 514 then 252 else if j < 515 then 888 else 580 else if j < 521 then if j < 518 then if j < 517 then 1936 else 120 else if j < 519 then 14268 else if j < 520 then 832 else 564 else if j < 523 then if j < 522 then 6472 else 168 else if j < 524 then 144 else if j < 525 then 872 else 20 else if j < 536 then if j < 531 then if j < 528 then if j < 527 then 8 else 8 else if j < 529 then 8 else if j < 530 then 20 else 100 else if j < 533 then if j < 532 then 64 else 20 else if j < 534 then 284 else if j < 535 then 124 else 24 else if j < 541 then if j < 538 then if j < 537 then 52 else 20 else if j < 539 then 16 else if j < 540 then 4 else 20 else if j < 543 then if j < 542 then 1156 else 292 else if j < 544 then 348 else if j < 545 then 128 else 424 else if j < 585 then if j < 565 then if j < 555 then if j < 550 then if j < 548 then if j < 547 then 420 else 4 else if j < 549 then 148 else 248 else if j < 552 then if j < 551 then 460 else 164 else if j < 553 then 76 else if j < 554 then 184 else 120 else if j < 560 then if j < 557 then if j < 556 then 164 else 96 else if j < 558 then 76 else if j < 559 then 912 else 580 else if j < 562 then if j < 561 then 976 else 140 else if j < 563 then 824 else if j < 564 then 212 else 324 else if j < 575 then if j < 570 then if j < 567 then if j < 566 then 540 else 512 else if j < 568 then 212 else if j < 569 then 308 else 372 else if j < 572 then if j < 571 then 216 else 480 else if j < 573 then 128 else if j < 574 then 420 else 216 else if j < 580 then if j < 577 then if j < 576 then 332 else 684 else if j < 578 then 128 else if j < 579 then 1116 else 11696 else if j < 582 then if j < 581 then 472 else 560 else if j < 583 then 312 else if j < 584 then 196 else 100 else if j < 604 then if j < 594 then if j < 589 then if j < 587 then if j < 586 then 140 else 104 else if j < 588 then 180 else 188 else if j < 591 then if j < 590 then 524 else 252 else if j < 592 then 144 else if j < 593 then 360 else 288 else if j < 599 then if j < 596 then if j < 595 then 340 else 132 else if j < 597 then 292 else if j < 598 then 192 else 496 else if j < 601 then if j < 600 then 80 else 96 else if j < 602 then 104 else if j < 603 then 76 else 76 else if j < 614 then if j < 609 then if j < 606 then if j < 605 then 80 else 96 else if j < 607 then 84 else if j < 608 then 96 else 84 else if j < 611 then if j < 610 then 96 else 84 else if j < 612 then 84 else if j < 613 then 96 else 100 else if j < 619 then if j < 616 then if j < 615 then 24 else 1232 else if j < 617 then 204 else if j < 618 then 4092 else 120 else if j < 621 then if j < 620 then 96 else 168 else if j < 622 then 104 else if j < 623 then 180 else 132
  else
    0

/-- Caller return address inside `libsignalSessionLib` blocks `0 .. 622` (`j < 623`) at strict byte offset `o < lsLen j`. -/
def LsRetAddr [LibsignalPlacement] (lr : BitVec 64) : Prop :=
  ∃ j < 623, ∃ o < lsLen j, lr = lsmpl.base j + BitVec.ofNat 64 o

@[wp_norm]
theorem lsRetAddr_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 623) (ho : off.toNat < lsLen j) :
    LsRetAddr (lsmpl.base j + off) :=
  ⟨j, hj, off.toNat, ho, by simp [BitVec.ofNat_toNat]⟩

@[wp_norm]
theorem lsRetAddr_blockPlacement_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 623) (ho : off.toNat < lsLen j) :
    LsRetAddr ((libsignalSessionLib.blockPlacement lsmpl j).base + off) :=
  lsRetAddr_base_add j off hj ho

@[wp_norm]
theorem lsRetAddr_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 623) (ho : 0 < lsLen j) :
    LsRetAddr (lsmpl.base j) :=
  ⟨j, hj, 0, ho, by simp⟩

@[wp_norm]
theorem lsRetAddr_blockPlacement_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 623) (ho : 0 < lsLen j) :
    LsRetAddr ((libsignalSessionLib.blockPlacement lsmpl j).base) :=
  lsRetAddr_base_zero j hj ho

/-- Caller return address inside `libsignalSessionLib` blocks `0 .. 623` (`j < 624`) at strict byte offset `o < lsLen j`. -/
def LsRetAddr624 [LibsignalPlacement] (lr : BitVec 64) : Prop :=
  ∃ j < 624, ∃ o < lsLen j, lr = lsmpl.base j + BitVec.ofNat 64 o

abbrev LsRetAddrSub [LibsignalPlacement] (lr : BitVec 64) : Prop :=
  LsRetAddr624 lr

theorem lsRetAddr624_of_lsRetAddr [LibsignalPlacement] {lr : BitVec 64}
    (h : LsRetAddr lr) : LsRetAddr624 lr := by
  rcases h with ⟨j, hj, o, ho, hlr⟩
  exact ⟨j, Nat.lt_trans hj (by decide), o, ho, hlr⟩

@[wp_norm]
theorem lsRetAddr624_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (ho : off.toNat < lsLen j) :
    LsRetAddr624 (lsmpl.base j + off) :=
  ⟨j, hj, off.toNat, ho, by simp [BitVec.ofNat_toNat]⟩

@[wp_norm]
theorem lsRetAddr624_blockPlacement_base_add [LibsignalPlacement] (j : Nat) (off : BitVec 64)
    (hj : j < 624) (ho : off.toNat < lsLen j) :
    LsRetAddr624 ((libsignalSessionLib.blockPlacement lsmpl j).base + off) :=
  lsRetAddr624_base_add j off hj ho

@[wp_norm]
theorem lsRetAddr624_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (ho : 0 < lsLen j) :
    LsRetAddr624 (lsmpl.base j) :=
  ⟨j, hj, 0, ho, by simp⟩

@[wp_norm]
theorem lsRetAddr624_blockPlacement_base_zero [LibsignalPlacement] (j : Nat)
    (hj : j < 624) (ho : 0 < lsLen j) :
    LsRetAddr624 ((libsignalSessionLib.blockPlacement lsmpl j).base) :=
  lsRetAddr624_base_zero j hj ho

end LibsignalBinary.Proofs.Placed.ElfLsRetAddr
