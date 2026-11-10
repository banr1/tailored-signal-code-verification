/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Terms01
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Bytes03
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Bytes04
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Bytes05

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes00

open DY.Libsignal (HwBytes)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)

def sub00 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨0, Terms00.t_0, .lit Bytes00.b_0, Bytes00.b_0, true⟩)
              (.leaf ⟨512, Terms01.t_512, .kdf 509 511, Bytes05.b_413, true⟩))
            (.branch (.leaf ⟨256, Terms00.t_256, .kdf 255 132, Bytes03.b_238, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨128, Terms00.t_128, .sChain 51 1 58, Bytes01.b_124, false⟩)
              (.leaf ⟨640, Terms01.t_640, .cat 639 137, Bytes05.b_478, true⟩))
            (.branch (.leaf ⟨384, Terms00.t_384, .kdf 383 132, Bytes02.b_161, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨64, Terms00.t_64, .sSendSt 60 63, Bytes00.b_61, false⟩)
              (.leaf ⟨576, Terms01.t_576, .cat 575 134, Bytes05.b_468, true⟩))
            (.branch (.leaf ⟨320, Terms00.t_320, .kdf 317 319, Bytes03.b_275, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨192, Terms00.t_192, .cat 10 191, Bytes02.b_184, true⟩) .empty)
            (.branch (.leaf ⟨448, Terms00.t_448, .kdf 443 447, Bytes04.b_349, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨32, Terms00.t_32, .rnd 24 32, Bytes00.b_31, true⟩)
              (.leaf ⟨544, Terms01.t_544, .cat 543 137, Bytes05.b_445, true⟩))
            (.branch (.leaf ⟨288, Terms00.t_288, .kdf 285 262, Bytes03.b_270, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨160, Terms00.t_160, .cat 7 159, Bytes02.b_154, true⟩)
              (.leaf ⟨672, Terms01.t_672, .cat 671 137, Bytes05.b_478, true⟩))
            (.branch (.leaf ⟨416, Terms00.t_416, .kdf 413 355, Bytes03.b_311, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨96, Terms00.t_96, .sSendSt 91 95, Bytes01.b_92, false⟩)
              (.leaf ⟨608, Terms01.t_608, .tr8 607, Bytes05.b_473, true⟩))
            (.branch (.leaf ⟨352, Terms00.t_352, .cat 351 137, Bytes03.b_307, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨224, Terms00.t_224, .kdf 221 223, Bytes02.b_215, true⟩) .empty)
            (.branch (.leaf ⟨480, Terms01.t_480, .kdf 477 479, Bytes04.b_381, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨16, Terms00.t_16, .rnd 22 32, Bytes00.b_16, true⟩)
              (.leaf ⟨528, Terms01.t_528, .cat 527 137, Bytes05.b_429, true⟩))
            (.branch (.leaf ⟨272, Terms00.t_272, .tr8 271, Bytes03.b_254, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨144, Terms00.t_144, .cat 7 143, Bytes01.b_139, true⟩)
              (.leaf ⟨656, Terms01.t_656, .cat 655 137, Bytes05.b_478, true⟩))
            (.branch (.leaf ⟨400, Terms00.t_400, .sRecvK 64 90, Bytes02.b_158, false⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨80, Terms00.t_80, .kdf 71 39, Bytes01.b_77, true⟩)
              (.leaf ⟨592, Terms01.t_592, .kdf 591 442, Bytes05.b_466, true⟩))
            (.branch (.leaf ⟨336, Terms00.t_336, .kdf 333 335, Bytes03.b_291, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨208, Terms00.t_208, .kdf 205 207, Bytes02.b_199, true⟩) .empty)
            (.branch (.leaf ⟨464, Terms01.t_464, .kdf 461 463, Bytes04.b_365, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨48, Terms00.t_48, .lit Bytes00.b_47, Bytes00.b_47, true⟩)
              (.leaf ⟨560, Terms01.t_560, .cat 559 137, Bytes05.b_461, true⟩))
            (.branch (.leaf ⟨304, Terms00.t_304, .cat 303 137, Bytes03.b_268, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨176, Terms00.t_176, .cat 10 175, Bytes02.b_169, true⟩) .empty)
            (.branch (.leaf ⟨432, Terms00.t_432, .cat 431 137, Bytes03.b_307, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨112, Terms00.t_112, .cat 0 111, Bytes01.b_108, true⟩)
              (.leaf ⟨624, Terms01.t_624, .kdf 619 623, Bytes02.b_180, true⟩))
            (.branch (.leaf ⟨368, Terms00.t_368, .cat 367 134, Bytes04.b_323, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨240, Terms00.t_240, .cat 239 134, Bytes01.b_147, true⟩) .empty)
            (.branch (.leaf ⟨496, Terms01.t_496, .kdf 493 495, Bytes04.b_397, true⟩) .empty))
        )
      )
    )
  )

def sub01 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨8, Terms00.t_8, .rnd 5 32, Bytes00.b_8, true⟩)
              (.leaf ⟨520, Terms01.t_520, .cat 519 40, Bytes05.b_421, true⟩))
            (.branch (.leaf ⟨264, Terms00.t_264, .tr8 263, Bytes03.b_246, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨136, Terms00.t_136, .kdf 130 135, Bytes01.b_132, true⟩)
              (.leaf ⟨648, Terms01.t_648, .cat 647 137, Bytes05.b_478, true⟩))
            (.branch (.leaf ⟨392, Terms00.t_392, .kdf 391 165, Bytes02.b_160, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨72, Terms00.t_72, .sInit 51 0, Bytes00.b_69, false⟩)
              (.leaf ⟨584, Terms01.t_584, .kdf 583 132, Bytes05.b_467, true⟩))
            (.branch (.leaf ⟨328, Terms00.t_328, .kdf 325 327, Bytes03.b_283, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨200, Terms00.t_200, .rnd 17 64, Bytes02.b_192, true⟩) .empty)
            (.branch (.leaf ⟨456, Terms01.t_456, .kdf 453 455, Bytes04.b_357, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨40, Terms00.t_40, .cat 36 39, Bytes00.b_39, true⟩)
              (.leaf ⟨552, Terms01.t_552, .cat 551 137, Bytes05.b_453, true⟩))
            (.branch (.leaf ⟨296, Terms00.t_296, .kdf 291 295, Bytes03.b_269, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨168, Terms00.t_168, .cat 167 134, Bytes02.b_162, true⟩) .empty)
            (.branch (.leaf ⟨424, Terms00.t_424, .kdf 419 423, Bytes03.b_308, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨104, Terms00.t_104, .cat 0 103, Bytes01.b_100, true⟩)
              (.leaf ⟨616, Terms01.t_616, .kdf 613 193, Bytes02.b_186, true⟩))
            (.branch (.leaf ⟨360, Terms00.t_360, .cat 359 134, Bytes03.b_315, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨232, Terms00.t_232, .kdf 229 231, Bytes02.b_223, true⟩) .empty)
            (.branch (.leaf ⟨488, Terms01.t_488, .kdf 485 487, Bytes04.b_389, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨24, Terms00.t_24, .cat 19 23, Bytes00.b_23, true⟩)
              (.leaf ⟨536, Terms01.t_536, .cat 535 137, Bytes05.b_437, true⟩))
            (.branch (.leaf ⟨280, Terms00.t_280, .tr8 279, Bytes03.b_262, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨152, Terms00.t_152, .cat 151 134, Bytes01.b_147, true⟩)
              (.leaf ⟨664, Terms01.t_664, .cat 663 137, Bytes05.b_478, true⟩))
            (.branch (.leaf ⟨408, Terms00.t_408, .tr8 407, Bytes02.b_171, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨88, Terms00.t_88, .cat 87 40, Bytes01.b_85, true⟩)
              (.leaf ⟨600, Terms01.t_600, .sRecvK 96 190, Bytes05.b_465, false⟩))
            (.branch (.leaf ⟨344, Terms00.t_344, .cat 343 40, Bytes03.b_299, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨216, Terms00.t_216, .kdf 213 215, Bytes02.b_207, true⟩) .empty)
            (.branch (.leaf ⟨472, Terms01.t_472, .kdf 469 471, Bytes04.b_373, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨56, Terms00.t_56, .cat 43 55, Bytes00.b_53, true⟩)
              (.leaf ⟨568, Terms01.t_568, .kdf 565 567, Bytes05.b_469, true⟩))
            (.branch (.leaf ⟨312, Terms00.t_312, .kdf 309 311, Bytes01.b_148, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨184, Terms00.t_184, .cat 183 134, Bytes02.b_177, true⟩) .empty)
            (.branch (.leaf ⟨440, Terms00.t_440, .kdf 437 439, Bytes04.b_341, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨120, Terms00.t_120, .cat 1 20, Bytes01.b_116, true⟩)
              (.leaf ⟨632, Terms01.t_632, .cat 631 137, Bytes02.b_179, true⟩))
            (.branch (.leaf ⟨376, Terms00.t_376, .cat 375 134, Bytes04.b_331, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨248, Terms00.t_248, .kdf 247 37, Bytes02.b_230, true⟩) .empty)
            (.branch (.leaf ⟨504, Terms01.t_504, .kdf 501 503, Bytes04.b_405, true⟩) .empty))
        )
      )
    )
  )

def sub02 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨4, Terms00.t_4, .lit Bytes00.b_4, Bytes00.b_4, true⟩)
              (.leaf ⟨516, Terms01.t_516, .tr8 515, Bytes05.b_417, true⟩))
            (.branch (.leaf ⟨260, Terms00.t_260, .kdf 255 259, Bytes03.b_242, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨132, Terms00.t_132, .cat 131 0, Bytes01.b_128, true⟩)
              (.leaf ⟨644, Terms01.t_644, .kdf 573 523, Bytes05.b_474, true⟩))
            (.branch (.leaf ⟨388, Terms00.t_388, .kdf 383 387, Bytes02.b_165, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨68, Terms00.t_68, .kdf 38 67, Bytes00.b_65, true⟩)
              (.leaf ⟨580, Terms01.t_580, .kdf 577 450, Bytes05.b_472, true⟩))
            (.branch (.leaf ⟨324, Terms00.t_324, .tr8 323, Bytes03.b_279, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨196, Terms00.t_196, .cat 191 195, Bytes02.b_188, true⟩) .empty)
            (.branch (.leaf ⟨452, Terms01.t_452, .tr8 451, Bytes04.b_353, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨36, Terms00.t_36, .lit Bytes00.b_35, Bytes00.b_35, true⟩)
              (.leaf ⟨548, Terms01.t_548, .kdf 164 523, Bytes05.b_449, true⟩))
            (.branch (.leaf ⟨292, Terms00.t_292, .kdf 291 132, Bytes03.b_265, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨164, Terms00.t_164, .sSendK 78 81, Bytes02.b_158, false⟩) .empty)
            (.branch (.leaf ⟨420, Terms00.t_420, .kdf 419 132, Bytes03.b_304, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨100, Terms00.t_100, .cat 1 99, Bytes01.b_96, true⟩)
              (.leaf ⟨612, Terms01.t_612, .cat 611 134, Bytes02.b_177, true⟩))
            (.branch (.leaf ⟨356, Terms00.t_356, .kdf 351 355, Bytes03.b_311, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨228, Terms00.t_228, .tr8 227, Bytes02.b_219, true⟩) .empty)
            (.branch (.leaf ⟨484, Terms01.t_484, .tr8 483, Bytes04.b_385, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨20, Terms00.t_20, .rnd 16 64, Bytes00.b_20, true⟩)
              (.leaf ⟨532, Terms01.t_532, .kdf 128 523, Bytes05.b_433, true⟩))
            (.branch (.leaf ⟨276, Terms00.t_276, .kdf 273 275, Bytes03.b_258, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨148, Terms00.t_148, .sSendK 60 63, Bytes01.b_143, false⟩)
              (.leaf ⟨660, Terms01.t_660, .kdf 591 523, Bytes05.b_474, true⟩))
            (.branch (.leaf ⟨404, Terms00.t_404, .kdf 401 403, Bytes02.b_163, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨84, Terms00.t_84, .dhPk 83, Bytes01.b_81, true⟩)
              (.leaf ⟨596, Terms01.t_596, .cat 595 137, Bytes05.b_470, true⟩))
            (.branch (.leaf ⟨340, Terms00.t_340, .tr8 339, Bytes03.b_295, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨212, Terms00.t_212, .tr8 211, Bytes02.b_203, true⟩) .empty)
            (.branch (.leaf ⟨468, Terms01.t_468, .tr8 467, Bytes04.b_369, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨52, Terms00.t_52, .sInit 51 1, Bytes00.b_51, false⟩)
              (.leaf ⟨564, Terms01.t_564, .sRecvK 52 190, Bytes05.b_465, false⟩))
            (.branch (.leaf ⟨308, Terms00.t_308, .sRecvK 74 77, Bytes01.b_143, false⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨180, Terms00.t_180, .sSendK 91 95, Bytes02.b_173, false⟩) .empty)
            (.branch (.leaf ⟨436, Terms00.t_436, .dh 84 32, Bytes04.b_337, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨116, Terms00.t_116, .cat 1 115, Bytes01.b_112, true⟩)
              (.leaf ⟨628, Terms01.t_628, .kdf 627 181, Bytes02.b_175, true⟩))
            (.branch (.leaf ⟨372, Terms00.t_372, .kdf 369 355, Bytes04.b_327, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨244, Terms00.t_244, .kdf 241 160, Bytes02.b_155, true⟩) .empty)
            (.branch (.leaf ⟨500, Terms01.t_500, .tr8 499, Bytes04.b_401, true⟩) .empty))
        )
      )
    )
  )

def sub03 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨12, Terms00.t_12, .lit Bytes00.b_12, Bytes00.b_12, true⟩)
              (.leaf ⟨524, Terms01.t_524, .kdf 11 523, Bytes05.b_425, true⟩))
            (.branch (.leaf ⟨268, Terms00.t_268, .kdf 265 267, Bytes03.b_250, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨140, Terms00.t_140, .rnd 31 32, pt0, true⟩)
              (.leaf ⟨652, Terms01.t_652, .kdf 582 523, Bytes05.b_474, true⟩))
            (.branch (.leaf ⟨396, Terms00.t_396, .cat 395 137, Bytes02.b_164, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨76, Terms00.t_76, .cat 58 75, Bytes00.b_73, true⟩)
              (.leaf ⟨588, Terms01.t_588, .kdf 583 587, Bytes05.b_471, true⟩))
            (.branch (.leaf ⟨332, Terms00.t_332, .tr8 331, Bytes03.b_287, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨204, Terms00.t_204, .rnd 83 32, Bytes02.b_195, true⟩) .empty)
            (.branch (.leaf ⟨460, Terms01.t_460, .tr8 459, Bytes04.b_361, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨44, Terms00.t_44, .cat 33 31, Bytes00.b_43, true⟩)
              (.leaf ⟨556, Terms01.t_556, .kdf 180 523, Bytes05.b_457, true⟩))
            (.branch (.leaf ⟨300, Terms00.t_300, .kdf 299 254, Bytes03.b_264, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨172, Terms00.t_172, .rnd 58 32, ptReply0, true⟩) .empty)
            (.branch (.leaf ⟨428, Terms00.t_428, .kdf 427 347, Bytes03.b_303, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨108, Terms00.t_108, .cat 3 107, Bytes01.b_104, true⟩)
              (.leaf ⟨620, Terms01.t_620, .kdf 619 132, Bytes02.b_176, true⟩))
            (.branch (.leaf ⟨364, Terms00.t_364, .kdf 361 355, Bytes04.b_319, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨236, Terms00.t_236, .tr8 235, Bytes02.b_227, true⟩) .empty)
            (.branch (.leaf ⟨492, Terms01.t_492, .tr8 491, Bytes04.b_393, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨28, Terms00.t_28, .kdf 11 27, Bytes00.b_27, true⟩)
              (.leaf ⟨540, Terms01.t_540, .kdf 148 523, Bytes05.b_441, true⟩))
            (.branch (.leaf ⟨284, Terms00.t_284, .cat 283 134, Bytes03.b_266, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨156, Terms00.t_156, .rnd 38 32, pt1, true⟩)
              (.leaf ⟨668, Terms01.t_668, .kdf 600 523, Bytes05.b_474, true⟩))
            (.branch (.leaf ⟨412, Terms00.t_412, .cat 411 134, Bytes03.b_305, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨92, Terms00.t_92, .cat 0 75, Bytes01.b_87, true⟩)
              (.leaf ⟨604, Terms01.t_604, .kdf 601 603, Bytes05.b_469, true⟩))
            (.branch (.leaf ⟨348, Terms00.t_348, .kdf 11 347, Bytes03.b_303, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨220, Terms00.t_220, .tr8 219, Bytes02.b_211, true⟩) .empty)
            (.branch (.leaf ⟨476, Terms01.t_476, .tr8 475, Bytes04.b_377, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨60, Terms00.t_60, .sSendSt 52 59, Bytes00.b_57, false⟩)
              (.leaf ⟨572, Terms01.t_572, .tr8 571, Bytes05.b_473, true⟩))
            (.branch (.leaf ⟨316, Terms00.t_316, .tr8 315, Bytes02.b_156, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨188, Terms00.t_188, .rnd 76 32, pt2, true⟩) .empty)
            (.branch (.leaf ⟨444, Terms00.t_444, .kdf 443 132, Bytes04.b_345, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨124, Terms00.t_124, .cat 0 123, Bytes01.b_120, true⟩)
              (.leaf ⟨636, Terms01.t_636, .kdf 564 523, Bytes05.b_474, true⟩))
            (.branch (.leaf ⟨380, Terms00.t_380, .kdf 377 355, Bytes04.b_335, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨252, Terms00.t_252, .kdf 251 39, Bytes03.b_234, true⟩) .empty)
            (.branch (.leaf ⟨508, Terms01.t_508, .tr8 507, Bytes05.b_409, true⟩) .empty))
        )
      )
    )
  )

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes00
