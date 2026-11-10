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

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes01

open DY.Libsignal (HwBytes)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)

def sub04 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨2, Terms00.t_2, .lit Bytes00.b_2, Bytes00.b_2, true⟩)
              (.leaf ⟨514, Terms01.t_514, .kdf 509 513, Bytes05.b_415, true⟩))
            (.branch (.leaf ⟨258, Terms00.t_258, .kdf 255 257, Bytes03.b_240, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨130, Terms00.t_130, .kdf 128 129, Bytes01.b_126, true⟩)
              (.leaf ⟨642, Terms01.t_642, .kdf 639 450, Bytes05.b_480, true⟩))
            (.branch (.leaf ⟨386, Terms00.t_386, .kdf 383 385, Bytes02.b_163, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨66, Terms00.t_66, .dhPk 65, Bytes00.b_63, true⟩)
              (.leaf ⟨578, Terms01.t_578, .cat 577 137, Bytes05.b_470, true⟩))
            (.branch (.leaf ⟨322, Terms00.t_322, .kdf 317 321, Bytes03.b_277, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨194, Terms00.t_194, .kdf 185 193, Bytes02.b_186, true⟩) .empty)
            (.branch (.leaf ⟨450, Terms01.t_450, .cat 10 449, Bytes04.b_351, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨34, Terms00.t_34, .dh 33 13, Bytes00.b_33, true⟩)
              (.leaf ⟨546, Terms01.t_546, .kdf 543 450, Bytes05.b_447, true⟩))
            (.branch (.leaf ⟨290, Terms00.t_290, .sRecvK 60 77, Bytes03.b_263, false⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨162, Terms00.t_162, .tr8 161, Bytes02.b_156, true⟩)
              (.leaf ⟨674, Terms01.t_674, .kdf 671 450, Bytes05.b_480, true⟩))
            (.branch (.leaf ⟨418, Terms00.t_418, .sRecvK 78 90, Bytes00.b_11, false⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨98, Terms00.t_98, .cat 1 97, Bytes01.b_94, true⟩)
              (.leaf ⟨610, Terms01.t_610, .kdf 609 181, Bytes02.b_175, true⟩))
            (.branch (.leaf ⟨354, Terms00.t_354, .cat 10 174, Bytes03.b_309, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨226, Terms00.t_226, .kdf 221 225, Bytes02.b_217, true⟩) .empty)
            (.branch (.leaf ⟨482, Terms01.t_482, .kdf 477 481, Bytes04.b_383, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨18, Terms00.t_18, .dh 17 8, Bytes00.b_18, true⟩)
              (.leaf ⟨530, Terms01.t_530, .kdf 527 450, Bytes05.b_431, true⟩))
            (.branch (.leaf ⟨274, Terms00.t_274, .kdf 273 132, Bytes03.b_256, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨146, Terms00.t_146, .tr8 145, Bytes01.b_141, true⟩)
              (.leaf ⟨658, Terms01.t_658, .kdf 655 450, Bytes05.b_480, true⟩))
            (.branch (.leaf ⟨402, Terms00.t_402, .kdf 401 132, Bytes02.b_161, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨82, Terms00.t_82, .sSendSt 78 81, Bytes01.b_79, false⟩)
              (.leaf ⟨594, Terms01.t_594, .cat 593 134, Bytes05.b_468, true⟩))
            (.branch (.leaf ⟨338, Terms00.t_338, .kdf 333 337, Bytes03.b_293, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨210, Terms00.t_210, .kdf 205 209, Bytes02.b_201, true⟩) .empty)
            (.branch (.leaf ⟨466, Terms01.t_466, .kdf 461 465, Bytes04.b_367, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨50, Terms00.t_50, .cat 47 49, Bytes00.b_49, true⟩)
              (.leaf ⟨562, Terms01.t_562, .kdf 559 450, Bytes05.b_463, true⟩))
            (.branch (.leaf ⟨306, Terms00.t_306, .kdf 303 262, Bytes03.b_270, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨178, Terms00.t_178, .tr8 177, Bytes02.b_171, true⟩) .empty)
            (.branch (.leaf ⟨434, Terms00.t_434, .kdf 431 355, Bytes03.b_311, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨114, Terms00.t_114, .cat 1 113, Bytes01.b_110, true⟩)
              (.leaf ⟨626, Terms01.t_626, .tr8 625, Bytes02.b_187, true⟩))
            (.branch (.leaf ⟨370, Terms00.t_370, .cat 369 137, Bytes04.b_325, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨242, Terms00.t_242, .cat 241 137, Bytes01.b_149, true⟩) .empty)
            (.branch (.leaf ⟨498, Terms01.t_498, .kdf 493 497, Bytes04.b_399, true⟩) .empty))
        )
      )
    )
  )

def sub05 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨10, Terms00.t_10, .cat 4 9, Bytes00.b_10, true⟩)
              (.leaf ⟨522, Terms01.t_522, .kdf 521 39, Bytes05.b_423, true⟩))
            (.branch (.leaf ⟨266, Terms00.t_266, .kdf 265 132, Bytes03.b_248, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨138, Terms00.t_138, .cat 136 137, Bytes01.b_134, true⟩)
              (.leaf ⟨650, Terms01.t_650, .kdf 647 450, Bytes05.b_480, true⟩))
            (.branch (.leaf ⟨394, Terms00.t_394, .cat 393 134, Bytes02.b_162, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨74, Terms00.t_74, .sRecvSt 72 73, Bytes00.b_71, false⟩)
              (.leaf ⟨586, Terms01.t_586, .kdf 583 585, Bytes05.b_469, true⟩))
            (.branch (.leaf ⟨330, Terms00.t_330, .kdf 325 329, Bytes03.b_285, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨202, Terms00.t_202, .cat 201 21, Bytes02.b_194, true⟩) .empty)
            (.branch (.leaf ⟨458, Terms01.t_458, .kdf 453 457, Bytes04.b_359, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨42, Terms00.t_42, .kdf 35 41, Bytes00.b_41, true⟩)
              (.leaf ⟨554, Terms01.t_554, .kdf 551 450, Bytes05.b_455, true⟩))
            (.branch (.leaf ⟨298, Terms00.t_298, .tr8 297, Bytes03.b_271, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨170, Terms00.t_170, .cat 169 137, Bytes02.b_164, true⟩) .empty)
            (.branch (.leaf ⟨426, Terms00.t_426, .tr8 425, Bytes03.b_312, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨106, Terms00.t_106, .cat 1 8, Bytes01.b_102, true⟩)
              (.leaf ⟨618, Terms01.t_618, .sRecvK 78 190, Bytes02.b_173, false⟩))
            (.branch (.leaf ⟨362, Terms00.t_362, .cat 361 137, Bytes03.b_317, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨234, Terms00.t_234, .kdf 229 233, Bytes02.b_225, true⟩) .empty)
            (.branch (.leaf ⟨490, Terms01.t_490, .kdf 485 489, Bytes04.b_391, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨26, Terms00.t_26, .cat 15 25, Bytes00.b_25, true⟩)
              (.leaf ⟨538, Terms01.t_538, .kdf 535 450, Bytes05.b_439, true⟩))
            (.branch (.leaf ⟨282, Terms00.t_282, .kdf 281 254, Bytes03.b_264, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨154, Terms00.t_154, .cat 153 137, Bytes01.b_149, true⟩)
              (.leaf ⟨666, Terms01.t_666, .kdf 663 450, Bytes05.b_480, true⟩))
            (.branch (.leaf ⟨410, Terms00.t_410, .kdf 409 347, Bytes03.b_303, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨90, Terms00.t_90, .sSendM 78 81, Bytes01.b_87, false⟩)
              (.leaf ⟨602, Terms01.t_602, .kdf 601 132, Bytes05.b_467, true⟩))
            (.branch (.leaf ⟨346, Terms00.t_346, .kdf 345 39, Bytes03.b_301, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨218, Terms00.t_218, .kdf 213 217, Bytes02.b_209, true⟩) .empty)
            (.branch (.leaf ⟨474, Terms01.t_474, .kdf 469 473, Bytes04.b_375, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨58, Terms00.t_58, .lit Bytes00.b_55, Bytes00.b_55, true⟩)
              (.leaf ⟨570, Terms01.t_570, .kdf 565 569, Bytes05.b_471, true⟩))
            (.branch (.leaf ⟨314, Terms00.t_314, .kdf 309 313, Bytes02.b_150, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨186, Terms00.t_186, .cat 185 137, Bytes02.b_179, true⟩) .empty)
            (.branch (.leaf ⟨442, Terms00.t_442, .kdf 440 0, Bytes04.b_343, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨122, Terms00.t_122, .cat 3 121, Bytes01.b_118, true⟩)
              (.leaf ⟨634, Terms01.t_634, .kdf 631 193, Bytes02.b_186, true⟩))
            (.branch (.leaf ⟨378, Terms00.t_378, .cat 377 137, Bytes04.b_333, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨250, Terms00.t_250, .kdf 247 249, Bytes03.b_232, true⟩) .empty)
            (.branch (.leaf ⟨506, Terms01.t_506, .kdf 501 505, Bytes05.b_407, true⟩) .empty))
        )
      )
    )
  )

def sub06 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨6, Terms00.t_6, .dhPk 5, Bytes00.b_6, true⟩)
              (.leaf ⟨518, Terms01.t_518, .kdf 87 517, Bytes05.b_419, true⟩))
            (.branch (.leaf ⟨262, Terms00.t_262, .cat 10 261, Bytes03.b_244, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨134, Terms00.t_134, .cat 131 39, Bytes01.b_130, true⟩)
              (.leaf ⟨646, Terms01.t_646, .cat 645 134, Bytes05.b_476, true⟩))
            (.branch (.leaf ⟨390, Terms00.t_390, .tr8 389, Bytes02.b_171, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨70, Terms00.t_70, .cat 69 40, Bytes00.b_67, true⟩)
              (.leaf ⟨582, Terms01.t_582, .sRecvK 64 190, Bytes05.b_465, false⟩))
            (.branch (.leaf ⟨326, Terms00.t_326, .kdf 325 132, Bytes03.b_281, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨198, Terms00.t_198, .cat 4 14, Bytes02.b_190, true⟩) .empty)
            (.branch (.leaf ⟨454, Terms01.t_454, .kdf 453 132, Bytes04.b_355, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨38, Terms00.t_38, .kdf 35 37, Bytes00.b_37, true⟩)
              (.leaf ⟨550, Terms01.t_550, .cat 549 134, Bytes05.b_451, true⟩))
            (.branch (.leaf ⟨294, Terms00.t_294, .kdf 291 293, Bytes03.b_267, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨166, Terms00.t_166, .kdf 164 165, Bytes02.b_160, true⟩) .empty)
            (.branch (.leaf ⟨422, Terms00.t_422, .kdf 419 421, Bytes03.b_306, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨102, Terms00.t_102, .cat 0 101, Bytes01.b_98, true⟩)
              (.leaf ⟨614, Terms01.t_614, .cat 613 137, Bytes02.b_179, true⟩))
            (.branch (.leaf ⟨358, Terms00.t_358, .kdf 128 347, Bytes03.b_313, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨230, Terms00.t_230, .kdf 229 132, Bytes02.b_221, true⟩) .empty)
            (.branch (.leaf ⟨486, Terms01.t_486, .kdf 485 132, Bytes04.b_387, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨22, Terms00.t_22, .rnd 23 32, Bytes00.b_21, true⟩)
              (.leaf ⟨534, Terms01.t_534, .cat 533 134, Bytes05.b_435, true⟩))
            (.branch (.leaf ⟨278, Terms00.t_278, .kdf 273 277, Bytes03.b_260, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨150, Terms00.t_150, .kdf 148 149, Bytes01.b_145, true⟩)
              (.leaf ⟨662, Terms01.t_662, .cat 661 134, Bytes05.b_476, true⟩))
            (.branch (.leaf ⟨406, Terms00.t_406, .kdf 401 405, Bytes02.b_165, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨86, Terms00.t_86, .kdf 69 85, Bytes01.b_83, true⟩)
              (.leaf ⟨598, Terms01.t_598, .kdf 595 450, Bytes05.b_472, true⟩))
            (.branch (.leaf ⟨342, Terms00.t_342, .kdf 69 341, Bytes03.b_297, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨214, Terms00.t_214, .kdf 213 132, Bytes02.b_205, true⟩) .empty)
            (.branch (.leaf ⟨470, Terms01.t_470, .kdf 469 132, Bytes04.b_371, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨54, Terms00.t_54, .cat 1 53, Bytes00.b_1, true⟩)
              (.leaf ⟨566, Terms01.t_566, .kdf 565 132, Bytes05.b_467, true⟩))
            (.branch (.leaf ⟨310, Terms00.t_310, .kdf 309 132, Bytes01.b_146, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨182, Terms00.t_182, .kdf 180 181, Bytes02.b_175, true⟩) .empty)
            (.branch (.leaf ⟨438, Terms00.t_438, .kdf 437 37, Bytes04.b_339, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨118, Terms00.t_118, .cat 0 117, Bytes01.b_114, true⟩)
              (.leaf ⟨630, Terms01.t_630, .cat 629 134, Bytes02.b_177, true⟩))
            (.branch (.leaf ⟨374, Terms00.t_374, .kdf 164 347, Bytes04.b_329, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨246, Terms00.t_246, .dh 33 32, Bytes02.b_228, true⟩) .empty)
            (.branch (.leaf ⟨502, Terms01.t_502, .kdf 501 132, Bytes04.b_403, true⟩) .empty))
        )
      )
    )
  )

def sub07 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨14, Terms00.t_14, .dhPk 13, Bytes00.b_14, true⟩)
              (.leaf ⟨526, Terms01.t_526, .cat 525 134, Bytes05.b_427, true⟩))
            (.branch (.leaf ⟨270, Terms00.t_270, .kdf 265 269, Bytes03.b_252, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨142, Terms00.t_142, .trW 4 33 0 0 141 73 (DY.TrWire.canonicalVariation), Bytes01.b_137, true⟩)
              (.leaf ⟨654, Terms01.t_654, .cat 653 134, Bytes05.b_476, true⟩))
            (.branch (.leaf ⟨398, Terms00.t_398, .kdf 395 176, Bytes02.b_170, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨78, Terms00.t_78, .sRecvSt 74 77, Bytes01.b_75, false⟩)
              (.leaf ⟨590, Terms01.t_590, .tr8 589, Bytes05.b_473, true⟩))
            (.branch (.leaf ⟨334, Terms00.t_334, .kdf 333 132, Bytes03.b_289, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨206, Terms00.t_206, .kdf 205 132, Bytes02.b_197, true⟩) .empty)
            (.branch (.leaf ⟨462, Terms01.t_462, .kdf 461 132, Bytes04.b_363, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨46, Terms00.t_46, .cat 31 45, Bytes00.b_45, true⟩)
              (.leaf ⟨558, Terms01.t_558, .cat 557 134, Bytes05.b_459, true⟩))
            (.branch (.leaf ⟨302, Terms00.t_302, .cat 301 134, Bytes03.b_266, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨174, Terms00.t_174, .trW 4 66 0 0 173 90 (DY.TrWire.canonicalVariation), Bytes02.b_167, true⟩)
              .empty)
            (.branch (.leaf ⟨430, Terms00.t_430, .cat 429 134, Bytes03.b_305, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨110, Terms00.t_110, .cat 0 109, Bytes01.b_106, true⟩)
              (.leaf ⟨622, Terms01.t_622, .kdf 619 621, Bytes02.b_178, true⟩))
            (.branch (.leaf ⟨366, Terms00.t_366, .kdf 148 347, Bytes04.b_321, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨238, Terms00.t_238, .kdf 237 149, Bytes01.b_145, true⟩) .empty)
            (.branch (.leaf ⟨494, Terms01.t_494, .kdf 493 132, Bytes04.b_395, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨30, Terms00.t_30, .cat 29 0, Bytes00.b_29, true⟩)
              (.leaf ⟨542, Terms01.t_542, .cat 541 134, Bytes05.b_443, true⟩))
            (.branch (.leaf ⟨286, Terms00.t_286, .cat 285 137, Bytes03.b_268, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨158, Terms00.t_158, .trW 4 33 1 0 157 77 (DY.TrWire.canonicalVariation), Bytes02.b_152, true⟩)
              (.leaf ⟨670, Terms01.t_670, .cat 669 134, Bytes05.b_476, true⟩))
            (.branch (.leaf ⟨414, Terms00.t_414, .cat 413 137, Bytes03.b_307, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨94, Terms00.t_94, .kdf 89 39, Bytes01.b_90, true⟩)
              (.leaf ⟨606, Terms01.t_606, .kdf 601 605, Bytes05.b_471, true⟩))
            (.branch (.leaf ⟨350, Terms00.t_350, .cat 349 134, Bytes03.b_305, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨222, Terms00.t_222, .kdf 221 132, Bytes02.b_213, true⟩) .empty)
            (.branch (.leaf ⟨478, Terms01.t_478, .kdf 477 132, Bytes04.b_379, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨62, Terms00.t_62, .lit Bytes00.b_59, Bytes00.b_59, true⟩)
              (.leaf ⟨574, Terms01.t_574, .kdf 573 442, Bytes05.b_466, true⟩))
            (.branch (.leaf ⟨318, Terms00.t_318, .kdf 317 132, Bytes03.b_273, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨190, Terms00.t_190, .sSendM 91 95, Bytes02.b_182, false⟩) .empty)
            (.branch (.leaf ⟨446, Terms00.t_446, .kdf 443 445, Bytes04.b_347, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨126, Terms00.t_126, .cat 0 125, Bytes01.b_122, true⟩)
              (.leaf ⟨638, Terms01.t_638, .cat 637 134, Bytes05.b_476, true⟩))
            (.branch (.leaf ⟨382, Terms00.t_382, .sRecvK 52 90, Bytes02.b_158, false⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨254, Terms00.t_254, .kdf 251 0, Bytes03.b_236, true⟩) .empty)
            (.branch (.leaf ⟨510, Terms01.t_510, .kdf 509 132, Bytes05.b_411, true⟩) .empty))
        )
      )
    )
  )

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes01
