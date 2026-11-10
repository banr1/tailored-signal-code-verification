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

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes02

open DY.Libsignal (HwBytes)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)

def sub08 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨1, Terms00.t_1, .lit Bytes00.b_1, Bytes00.b_1, true⟩)
              (.leaf ⟨513, Terms01.t_513, .cat 512 137, Bytes05.b_414, true⟩))
            (.branch (.leaf ⟨257, Terms00.t_257, .cat 256 134, Bytes03.b_239, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨129, Terms00.t_129, .kdf 42 0, Bytes01.b_125, true⟩)
              (.leaf ⟨641, Terms01.t_641, .kdf 636 640, Bytes05.b_479, true⟩))
            (.branch (.leaf ⟨385, Terms00.t_385, .cat 384 134, Bytes02.b_162, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨65, Terms00.t_65, .rnd 45 32, Bytes00.b_62, true⟩)
              (.leaf ⟨577, Terms01.t_577, .kdf 574 576, Bytes05.b_469, true⟩))
            (.branch (.leaf ⟨321, Terms00.t_321, .cat 320 137, Bytes03.b_276, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨193, Terms00.t_193, .cat 7 192, Bytes02.b_185, true⟩) .empty)
            (.branch (.leaf ⟨449, Terms00.t_449, .cat 7 191, Bytes04.b_350, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨33, Terms00.t_33, .dhPk 32, Bytes00.b_32, true⟩)
              (.leaf ⟨545, Terms01.t_545, .kdf 540 544, Bytes05.b_446, true⟩))
            (.branch (.leaf ⟨289, Terms00.t_289, .tr8 288, Bytes03.b_271, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨161, Terms00.t_161, .kdf 153 160, Bytes02.b_155, true⟩)
              (.leaf ⟨673, Terms01.t_673, .kdf 668 672, Bytes05.b_479, true⟩))
            (.branch (.leaf ⟨417, Terms00.t_417, .tr8 416, Bytes03.b_312, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨97, Terms00.t_97, .cat 1 5, Bytes01.b_93, true⟩)
              (.leaf ⟨609, Terms01.t_609, .sRecvK 74 190, Bytes02.b_173, false⟩))
            (.branch (.leaf ⟨353, Terms00.t_353, .kdf 348 352, Bytes03.b_308, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨225, Terms00.t_225, .cat 224 137, Bytes02.b_216, true⟩) .empty)
            (.branch (.leaf ⟨481, Terms01.t_481, .cat 480 137, Bytes04.b_382, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨17, Terms00.t_17, .dhPk 16, Bytes00.b_17, true⟩)
              (.leaf ⟨529, Terms01.t_529, .kdf 524 528, Bytes05.b_430, true⟩))
            (.branch (.leaf ⟨273, Terms00.t_273, .kdf 148 254, Bytes03.b_255, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨145, Terms00.t_145, .kdf 136 144, Bytes01.b_140, true⟩)
              (.leaf ⟨657, Terms01.t_657, .kdf 652 656, Bytes05.b_479, true⟩))
            (.branch (.leaf ⟨401, Terms00.t_401, .kdf 400 165, Bytes02.b_160, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨81, Terms00.t_81, .rnd 59 32, Bytes01.b_78, true⟩)
              (.leaf ⟨593, Terms01.t_593, .kdf 592 132, Bytes05.b_467, true⟩))
            (.branch (.leaf ⟨337, Terms00.t_337, .cat 336 137, Bytes03.b_292, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨209, Terms00.t_209, .cat 208 137, Bytes02.b_200, true⟩) .empty)
            (.branch (.leaf ⟨465, Terms01.t_465, .cat 464 137, Bytes04.b_366, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨49, Terms00.t_49, .cat 29 48, Bytes00.b_48, true⟩)
              (.leaf ⟨561, Terms01.t_561, .kdf 556 560, Bytes05.b_462, true⟩))
            (.branch (.leaf ⟨305, Terms00.t_305, .kdf 300 304, Bytes03.b_269, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨177, Terms00.t_177, .kdf 169 176, Bytes02.b_170, true⟩) .empty)
            (.branch (.leaf ⟨433, Terms00.t_433, .kdf 428 432, Bytes03.b_308, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨113, Terms00.t_113, .cat 0 13, Bytes01.b_109, true⟩)
              (.leaf ⟨625, Terms01.t_625, .kdf 622 193, Bytes02.b_186, true⟩))
            (.branch (.leaf ⟨369, Terms00.t_369, .kdf 366 368, Bytes04.b_324, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨241, Terms00.t_241, .kdf 238 240, Bytes01.b_148, true⟩) .empty)
            (.branch (.leaf ⟨497, Terms01.t_497, .cat 496 137, Bytes04.b_398, true⟩) .empty))
        )
      )
    )
  )

def sub09 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨9, Terms00.t_9, .dhPk 8, Bytes00.b_9, true⟩)
              (.leaf ⟨521, Terms01.t_521, .kdf 518 520, Bytes05.b_422, true⟩))
            (.branch (.leaf ⟨265, Terms00.t_265, .kdf 128 254, Bytes03.b_247, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨137, Terms00.t_137, .cat 131 48, Bytes01.b_133, true⟩)
              (.leaf ⟨649, Terms01.t_649, .kdf 644 648, Bytes05.b_479, true⟩))
            (.branch (.leaf ⟨393, Terms00.t_393, .kdf 392 132, Bytes02.b_161, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨73, Terms00.t_73, .sSendM 52 59, Bytes00.b_70, false⟩)
              (.leaf ⟨585, Terms01.t_585, .cat 584 134, Bytes05.b_468, true⟩))
            (.branch (.leaf ⟨329, Terms00.t_329, .cat 328 137, Bytes03.b_284, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨201, Terms00.t_201, .lit Bytes02.b_193, Bytes02.b_193, true⟩)
              .empty)
            (.branch (.leaf ⟨457, Terms01.t_457, .cat 456 137, Bytes04.b_358, true⟩) .empty)
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨41, Terms00.t_41, .cat 38 40, Bytes00.b_40, true⟩)
              (.leaf ⟨553, Terms01.t_553, .kdf 548 552, Bytes05.b_454, true⟩))
            (.branch (.leaf ⟨297, Terms00.t_297, .kdf 294 262, Bytes03.b_270, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨169, Terms00.t_169, .kdf 166 168, Bytes02.b_163, true⟩) .empty)
            (.branch (.leaf ⟨425, Terms00.t_425, .kdf 422 355, Bytes03.b_311, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨105, Terms00.t_105, .cat 0 104, Bytes01.b_101, true⟩)
              (.leaf ⟨617, Terms01.t_617, .tr8 616, Bytes02.b_187, true⟩))
            (.branch (.leaf ⟨361, Terms00.t_361, .kdf 358 360, Bytes03.b_316, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨233, Terms00.t_233, .cat 232 137, Bytes02.b_224, true⟩) .empty)
            (.branch (.leaf ⟨489, Terms01.t_489, .cat 488 137, Bytes04.b_390, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨25, Terms00.t_25, .cat 18 24, Bytes00.b_24, true⟩)
              (.leaf ⟨537, Terms01.t_537, .kdf 532 536, Bytes05.b_438, true⟩))
            (.branch (.leaf ⟨281, Terms00.t_281, .sRecvK 52 77, Bytes03.b_263, false⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨153, Terms00.t_153, .kdf 150 152, Bytes01.b_148, true⟩)
              (.leaf ⟨665, Terms01.t_665, .kdf 660 664, Bytes05.b_479, true⟩))
            (.branch (.leaf ⟨409, Terms00.t_409, .sRecvK 74 90, Bytes00.b_11, false⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨89, Terms00.t_89, .kdf 86 88, Bytes01.b_86, true⟩)
              (.leaf ⟨601, Terms01.t_601, .kdf 600 442, Bytes05.b_466, true⟩))
            (.branch (.leaf ⟨345, Terms00.t_345, .kdf 342 344, Bytes03.b_300, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨217, Terms00.t_217, .cat 216 137, Bytes02.b_208, true⟩) .empty)
            (.branch (.leaf ⟨473, Terms01.t_473, .cat 472 137, Bytes04.b_374, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨57, Terms00.t_57, .kdf 42 39, Bytes00.b_54, true⟩)
              (.leaf ⟨569, Terms01.t_569, .cat 568 137, Bytes05.b_470, true⟩))
            (.branch (.leaf ⟨313, Terms00.t_313, .cat 312 137, Bytes01.b_149, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨185, Terms00.t_185, .kdf 182 184, Bytes02.b_178, true⟩) .empty)
            (.branch (.leaf ⟨441, Terms00.t_441, .kdf 440 39, Bytes04.b_342, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨121, Terms00.t_121, .cat 0 120, Bytes01.b_117, true⟩)
              (.leaf ⟨633, Terms01.t_633, .kdf 628 632, Bytes02.b_180, true⟩))
            (.branch (.leaf ⟨377, Terms00.t_377, .kdf 374 376, Bytes04.b_332, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨249, Terms00.t_249, .cat 248 40, Bytes02.b_231, true⟩) .empty)
            (.branch (.leaf ⟨505, Terms01.t_505, .cat 504 137, Bytes05.b_406, true⟩) .empty))
        )
      )
    )
  )

def sub10 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨5, Terms00.t_5, .rnd 0 32, Bytes00.b_5, true⟩)
              (.leaf ⟨517, Terms01.t_517, .dh 84 83, Bytes05.b_418, true⟩))
            (.branch (.leaf ⟨261, Terms00.t_261, .cat 7 158, Bytes03.b_243, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨133, Terms00.t_133, .kdf 130 132, Bytes01.b_129, true⟩)
              (.leaf ⟨645, Terms01.t_645, .kdf 644 132, Bytes05.b_475, true⟩))
            (.branch (.leaf ⟨389, Terms00.t_389, .kdf 386 176, Bytes02.b_170, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨69, Terms00.t_69, .kdf 68 37, Bytes00.b_66, true⟩)
              (.leaf ⟨581, Terms01.t_581, .tr8 580, Bytes05.b_473, true⟩))
            (.branch (.leaf ⟨325, Terms00.t_325, .kdf 128 165, Bytes03.b_280, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨197, Terms00.t_197, .rnd 11 64, Bytes02.b_189, true⟩) .empty)
            (.branch (.leaf ⟨453, Terms01.t_453, .kdf 128 442, Bytes04.b_354, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨37, Terms00.t_37, .cat 36 0, Bytes00.b_36, true⟩)
              (.leaf ⟨549, Terms01.t_549, .kdf 548 132, Bytes05.b_450, true⟩))
            (.branch (.leaf ⟨293, Terms00.t_293, .cat 292 134, Bytes03.b_266, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨165, Terms00.t_165, .kdf 71 0, Bytes02.b_159, true⟩) .empty)
            (.branch (.leaf ⟨421, Terms00.t_421, .cat 420 134, Bytes03.b_305, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨101, Terms00.t_101, .cat 0 100, Bytes01.b_97, true⟩)
              (.leaf ⟨613, Terms01.t_613, .kdf 610 612, Bytes02.b_178, true⟩))
            (.branch (.leaf ⟨357, Terms00.t_357, .tr8 356, Bytes03.b_312, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨229, Terms00.t_229, .kdf 128 149, Bytes02.b_220, true⟩) .empty)
            (.branch (.leaf ⟨485, Terms01.t_485, .kdf 11 181, Bytes04.b_386, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨21, Terms00.t_21, .kemPk 20, myKyberPubBytes, false⟩)
              (.leaf ⟨533, Terms01.t_533, .kdf 532 132, Bytes05.b_434, true⟩))
            (.branch (.leaf ⟨277, Terms00.t_277, .cat 276 137, Bytes03.b_259, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨149, Terms00.t_149, .kdf 57 0, Bytes01.b_144, true⟩)
              (.leaf ⟨661, Terms01.t_661, .kdf 660 132, Bytes05.b_475, true⟩))
            (.branch (.leaf ⟨405, Terms00.t_405, .cat 404 137, Bytes02.b_164, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨85, Terms00.t_85, .dh 84 65, Bytes01.b_82, true⟩)
              (.leaf ⟨597, Terms01.t_597, .kdf 592 596, Bytes05.b_471, true⟩))
            (.branch (.leaf ⟨341, Terms00.t_341, .dh 66 65, Bytes03.b_296, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨213, Terms00.t_213, .kdf 148 129, Bytes02.b_204, true⟩) .empty)
            (.branch (.leaf ⟨469, Terms01.t_469, .kdf 164 442, Bytes04.b_370, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨53, Terms00.t_53, .lit ([] : HwBytes), ([] : HwBytes), true⟩)
              (.leaf ⟨565, Terms01.t_565, .kdf 564 442, Bytes05.b_466, true⟩))
            (.branch (.leaf ⟨309, Terms00.t_309, .kdf 308 149, Bytes01.b_145, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨181, Terms00.t_181, .kdf 89 0, Bytes02.b_174, true⟩) .empty)
            (.branch (.leaf ⟨437, Terms00.t_437, .kdf 38 436, Bytes04.b_338, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨117, Terms00.t_117, .cat 0 116, Bytes01.b_113, true⟩)
              (.leaf ⟨629, Terms01.t_629, .kdf 628 132, Bytes02.b_176, true⟩))
            (.branch (.leaf ⟨373, Terms00.t_373, .tr8 372, Bytes04.b_328, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨245, Terms00.t_245, .tr8 244, Bytes02.b_156, true⟩) .empty)
            (.branch (.leaf ⟨501, Terms01.t_501, .kdf 148 181, Bytes04.b_402, true⟩) .empty))
        )
      )
    )
  )

def sub11 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨13, Terms00.t_13, .rnd 10 32, Bytes00.b_13, true⟩)
              (.leaf ⟨525, Terms01.t_525, .kdf 524 132, Bytes05.b_426, true⟩))
            (.branch (.leaf ⟨269, Terms00.t_269, .cat 268 137, Bytes03.b_251, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨141, Terms00.t_141, .sym 133 139 140, Bytes01.b_136, true⟩)
              (.leaf ⟨653, Terms01.t_653, .kdf 652 132, Bytes05.b_475, true⟩))
            (.branch (.leaf ⟨397, Terms00.t_397, .kdf 392 396, Bytes02.b_165, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨77, Terms00.t_77, .sSendM 60 63, Bytes00.b_74, false⟩)
              (.leaf ⟨589, Terms01.t_589, .kdf 586 450, Bytes05.b_472, true⟩))
            (.branch (.leaf ⟨333, Terms00.t_333, .kdf 148 165, Bytes03.b_288, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨205, Terms00.t_205, .kdf 11 129, Bytes02.b_196, true⟩) .empty)
            (.branch (.leaf ⟨461, Terms01.t_461, .kdf 148 442, Bytes04.b_362, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨45, Terms00.t_45, .cat 29 39, Bytes00.b_44, true⟩)
              (.leaf ⟨557, Terms01.t_557, .kdf 556 132, Bytes05.b_458, true⟩))
            (.branch (.leaf ⟨301, Terms00.t_301, .kdf 300 132, Bytes03.b_265, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨173, Terms00.t_173, .sym 167 171 172, Bytes02.b_166, true⟩)
              .empty)
            (.branch (.leaf ⟨429, Terms00.t_429, .kdf 428 132, Bytes03.b_304, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨109, Terms00.t_109, .cat 1 108, Bytes01.b_105, true⟩)
              (.leaf ⟨621, Terms01.t_621, .cat 620 134, Bytes02.b_177, true⟩))
            (.branch (.leaf ⟨365, Terms00.t_365, .tr8 364, Bytes04.b_320, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨237, Terms00.t_237, .sChain 51 1 62, Bytes01.b_143, false⟩)
              .empty)
            (.branch (.leaf ⟨493, Terms01.t_493, .kdf 128 181, Bytes04.b_394, true⟩) .empty)
          )
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨29, Terms00.t_29, .lit Bytes00.b_28, Bytes00.b_28, true⟩)
              (.leaf ⟨541, Terms01.t_541, .kdf 540 132, Bytes05.b_442, true⟩))
            (.branch (.leaf ⟨285, Terms00.t_285, .kdf 282 284, Bytes03.b_267, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨157, Terms00.t_157, .sym 151 155 156, Bytes02.b_151, true⟩)
              (.leaf ⟨669, Terms01.t_669, .kdf 668 132, Bytes05.b_475, true⟩))
            (.branch (.leaf ⟨413, Terms00.t_413, .kdf 410 412, Bytes03.b_306, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨93, Terms00.t_93, .cat 58 92, Bytes01.b_89, true⟩)
              (.leaf ⟨605, Terms01.t_605, .cat 604 137, Bytes05.b_470, true⟩))
            (.branch (.leaf ⟨349, Terms00.t_349, .kdf 348 132, Bytes03.b_304, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨221, Terms00.t_221, .kdf 11 149, Bytes02.b_212, true⟩) .empty)
            (.branch (.leaf ⟨477, Terms01.t_477, .kdf 180 442, Bytes04.b_378, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨61, Terms00.t_61, .kdf 57 39, Bytes00.b_58, true⟩)
              (.leaf ⟨573, Terms01.t_573, .sRecvK 60 190, Bytes05.b_465, false⟩))
            (.branch (.leaf ⟨317, Terms00.t_317, .kdf 11 165, Bytes03.b_272, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨189, Terms00.t_189, .sym 183 187 188, Bytes02.b_181, true⟩)
              .empty)
            (.branch (.leaf ⟨445, Terms00.t_445, .cat 444 134, Bytes04.b_346, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨125, Terms00.t_125, .cat 0 124, Bytes01.b_121, true⟩)
              (.leaf ⟨637, Terms01.t_637, .kdf 636 132, Bytes05.b_475, true⟩))
            (.branch (.leaf ⟨381, Terms00.t_381, .tr8 380, Bytes04.b_336, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨253, Terms00.t_253, .kdf 250 0, Bytes03.b_235, true⟩) .empty)
            (.branch (.leaf ⟨509, Terms01.t_509, .kdf 164 181, Bytes05.b_410, true⟩) .empty))
        )
      )
    )
  )

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes02
