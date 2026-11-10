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

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes03

open DY.Libsignal (HwBytes)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)

def sub12 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨3, Terms00.t_3, .lit Bytes00.b_3, Bytes00.b_3, true⟩)
              (.leaf ⟨515, Terms01.t_515, .kdf 512 193, Bytes05.b_416, true⟩))
            (.branch (.leaf ⟨259, Terms00.t_259, .cat 258 137, Bytes03.b_241, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨131, Terms00.t_131, .lit Bytes01.b_127, Bytes01.b_127, true⟩)
              (.leaf ⟨643, Terms01.t_643, .tr8 642, Bytes05.b_481, true⟩))
            (.branch (.leaf ⟨387, Terms00.t_387, .cat 386 137, Bytes02.b_164, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨67, Terms00.t_67, .dh 66 32, Bytes00.b_64, true⟩)
              (.leaf ⟨579, Terms01.t_579, .kdf 574 578, Bytes05.b_471, true⟩))
            (.branch (.leaf ⟨323, Terms00.t_323, .kdf 320 176, Bytes03.b_278, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨195, Terms00.t_195, .tr8 194, Bytes02.b_187, true⟩) .empty)
            (.branch (.leaf ⟨451, Terms01.t_451, .kdf 446 450, Bytes04.b_352, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨35, Terms00.t_35, .kdf 31 34, Bytes00.b_34, true⟩)
              (.leaf ⟨547, Terms01.t_547, .tr8 546, Bytes05.b_448, true⟩))
            (.branch (.leaf ⟨291, Terms00.t_291, .kdf 290 254, Bytes03.b_264, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨163, Terms00.t_163, .cat 158 162, Bytes02.b_157, true⟩)
              (.leaf ⟨675, Terms01.t_675, .tr8 674, Bytes05.b_481, true⟩))
            (.branch (.leaf ⟨419, Terms00.t_419, .kdf 418 347, Bytes03.b_303, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨99, Terms00.t_99, .cat 2 98, Bytes01.b_95, true⟩)
              (.leaf ⟨611, Terms01.t_611, .kdf 610 132, Bytes02.b_176, true⟩))
            (.branch (.leaf ⟨355, Terms00.t_355, .cat 7 354, Bytes03.b_310, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨227, Terms00.t_227, .kdf 224 160, Bytes02.b_218, true⟩) .empty)
            (.branch (.leaf ⟨483, Terms01.t_483, .kdf 480 450, Bytes04.b_384, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨19, Terms00.t_19, .dh 17 13, Bytes00.b_19, true⟩)
              (.leaf ⟨531, Terms01.t_531, .tr8 530, Bytes05.b_432, true⟩))
            (.branch (.leaf ⟨275, Terms00.t_275, .cat 274 134, Bytes03.b_257, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨147, Terms00.t_147, .cat 142 146, Bytes01.b_142, true⟩)
              (.leaf ⟨659, Terms01.t_659, .tr8 658, Bytes05.b_481, true⟩))
            (.branch (.leaf ⟨403, Terms00.t_403, .cat 402 134, Bytes02.b_162, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨83, Terms00.t_83, .rnd 65 32, Bytes01.b_80, true⟩)
              (.leaf ⟨595, Terms01.t_595, .kdf 592 594, Bytes05.b_469, true⟩))
            (.branch (.leaf ⟨339, Terms00.t_339, .kdf 336 176, Bytes03.b_294, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨211, Terms00.t_211, .kdf 208 144, Bytes02.b_202, true⟩) .empty)
            (.branch (.leaf ⟨467, Terms01.t_467, .kdf 464 450, Bytes04.b_368, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨51, Terms00.t_51, .kdf 28 50, Bytes00.b_50, true⟩)
              (.leaf ⟨563, Terms01.t_563, .tr8 562, Bytes05.b_464, true⟩))
            (.branch (.leaf ⟨307, Terms00.t_307, .tr8 306, Bytes03.b_271, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨179, Terms00.t_179, .cat 174 178, Bytes02.b_172, true⟩) .empty)
            (.branch (.leaf ⟨435, Terms00.t_435, .tr8 434, Bytes03.b_312, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨115, Terms00.t_115, .cat 3 114, Bytes01.b_111, true⟩)
              (.leaf ⟨627, Terms01.t_627, .sRecvK 82 190, Bytes02.b_173, false⟩))
            (.branch (.leaf ⟨371, Terms00.t_371, .kdf 366 370, Bytes04.b_326, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨243, Terms00.t_243, .kdf 238 242, Bytes02.b_150, true⟩) .empty)
            (.branch (.leaf ⟨499, Terms01.t_499, .kdf 496 193, Bytes04.b_400, true⟩) .empty))
        )
      )
    )
  )

def sub13 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨11, Terms00.t_11, .lit Bytes00.b_11, Bytes00.b_11, true⟩)
              (.leaf ⟨523, Terms01.t_523, .kdf 521 0, Bytes05.b_424, true⟩))
            (.branch (.leaf ⟨267, Terms00.t_267, .cat 266 134, Bytes03.b_249, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨139, Terms00.t_139, .kdf 130 138, Bytes01.b_135, true⟩)
              (.leaf ⟨651, Terms01.t_651, .tr8 650, Bytes05.b_481, true⟩))
            (.branch (.leaf ⟨395, Terms00.t_395, .kdf 392 394, Bytes02.b_163, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨75, Terms00.t_75, .cat 0 55, Bytes00.b_72, true⟩)
              (.leaf ⟨587, Terms01.t_587, .cat 586 137, Bytes05.b_470, true⟩))
            (.branch (.leaf ⟨331, Terms00.t_331, .kdf 328 176, Bytes03.b_286, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨203, Terms00.t_203, .sig 8 200 202, Bytes02.b_191, false⟩) .empty)
            (.branch (.leaf ⟨459, Terms01.t_459, .kdf 456 450, Bytes04.b_360, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨43, Terms00.t_43, .lit Bytes00.b_42, Bytes00.b_42, true⟩)
              (.leaf ⟨555, Terms01.t_555, .tr8 554, Bytes05.b_456, true⟩))
            (.branch (.leaf ⟨299, Terms00.t_299, .sRecvK 64 77, Bytes03.b_263, false⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨171, Terms00.t_171, .kdf 166 170, Bytes02.b_165, true⟩) .empty)
            (.branch (.leaf ⟨427, Terms00.t_427, .sRecvK 82 90, Bytes00.b_11, false⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨107, Terms00.t_107, .cat 1 106, Bytes01.b_103, true⟩)
              (.leaf ⟨619, Terms01.t_619, .kdf 618 181, Bytes02.b_175, true⟩))
            (.branch (.leaf ⟨363, Terms00.t_363, .kdf 358 362, Bytes04.b_318, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨235, Terms00.t_235, .kdf 232 160, Bytes02.b_226, true⟩) .empty)
            (.branch (.leaf ⟨491, Terms01.t_491, .kdf 488 193, Bytes04.b_392, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨27, Terms00.t_27, .cat 12 26, Bytes00.b_26, true⟩)
              (.leaf ⟨539, Terms01.t_539, .tr8 538, Bytes05.b_440, true⟩))
            (.branch (.leaf ⟨283, Terms00.t_283, .kdf 282 132, Bytes03.b_265, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨155, Terms00.t_155, .kdf 150 154, Bytes02.b_150, true⟩)
              (.leaf ⟨667, Terms01.t_667, .tr8 666, Bytes05.b_481, true⟩))
            (.branch (.leaf ⟨411, Terms00.t_411, .kdf 410 132, Bytes03.b_304, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨91, Terms00.t_91, .sRecvSt 64 90, Bytes01.b_88, false⟩)
              (.leaf ⟨603, Terms01.t_603, .cat 602 134, Bytes05.b_468, true⟩))
            (.branch (.leaf ⟨347, Terms00.t_347, .kdf 345 0, Bytes03.b_302, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨219, Terms00.t_219, .kdf 216 144, Bytes02.b_210, true⟩) .empty)
            (.branch (.leaf ⟨475, Terms01.t_475, .kdf 472 450, Bytes04.b_376, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨59, Terms00.t_59, .rnd 32 32, Bytes00.b_56, true⟩)
              (.leaf ⟨571, Terms01.t_571, .kdf 568 450, Bytes05.b_472, true⟩))
            (.branch (.leaf ⟨315, Terms00.t_315, .kdf 312 160, Bytes02.b_155, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨187, Terms00.t_187, .kdf 182 186, Bytes02.b_180, true⟩) .empty)
            (.branch (.leaf ⟨443, Terms00.t_443, .kdf 11 442, Bytes04.b_344, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨123, Terms00.t_123, .cat 1 122, Bytes01.b_119, true⟩)
              (.leaf ⟨635, Terms01.t_635, .tr8 634, Bytes02.b_187, true⟩))
            (.branch (.leaf ⟨379, Terms00.t_379, .kdf 374 378, Bytes04.b_334, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨251, Terms00.t_251, .kdf 250 39, Bytes03.b_233, true⟩) .empty)
            (.branch (.leaf ⟨507, Terms01.t_507, .kdf 504 193, Bytes05.b_408, true⟩) .empty))
        )
      )
    )
  )

def sub14 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨7, Terms00.t_7, .cat 4 6, Bytes00.b_7, true⟩)
              (.leaf ⟨519, Terms01.t_519, .kdf 518 37, Bytes05.b_420, true⟩))
            (.branch (.leaf ⟨263, Terms00.t_263, .kdf 258 262, Bytes03.b_245, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨135, Terms00.t_135, .cat 133 134, Bytes01.b_131, true⟩)
              (.leaf ⟨647, Terms01.t_647, .kdf 644 646, Bytes05.b_477, true⟩))
            (.branch (.leaf ⟨391, Terms00.t_391, .sRecvK 60 90, Bytes02.b_158, false⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨71, Terms00.t_71, .kdf 68 70, Bytes00.b_68, true⟩)
              (.leaf ⟨583, Terms01.t_583, .kdf 582 442, Bytes05.b_466, true⟩))
            (.branch (.leaf ⟨327, Terms00.t_327, .cat 326 134, Bytes03.b_282, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨199, Terms00.t_199, .sig 8 197 198, Bytes02.b_191, false⟩) .empty)
            (.branch (.leaf ⟨455, Terms01.t_455, .cat 454 134, Bytes04.b_356, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨39, Terms00.t_39, .lit Bytes00.b_38, Bytes00.b_38, true⟩)
              (.leaf ⟨551, Terms01.t_551, .kdf 548 550, Bytes05.b_452, true⟩))
            (.branch (.leaf ⟨295, Terms00.t_295, .cat 294 137, Bytes03.b_268, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨167, Terms00.t_167, .kdf 166 132, Bytes02.b_161, true⟩) .empty)
            (.branch (.leaf ⟨423, Terms00.t_423, .cat 422 137, Bytes03.b_307, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨103, Terms00.t_103, .cat 0 102, Bytes01.b_99, true⟩)
              (.leaf ⟨615, Terms01.t_615, .kdf 610 614, Bytes02.b_180, true⟩))
            (.branch (.leaf ⟨359, Terms00.t_359, .kdf 358 132, Bytes03.b_314, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨231, Terms00.t_231, .cat 230 134, Bytes02.b_222, true⟩) .empty)
            (.branch (.leaf ⟨487, Terms01.t_487, .cat 486 134, Bytes04.b_388, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨23, Terms00.t_23, .kemSS 21 22, Bytes00.b_22, true⟩)
              (.leaf ⟨535, Terms01.t_535, .kdf 532 534, Bytes05.b_436, true⟩))
            (.branch (.leaf ⟨279, Terms00.t_279, .kdf 276 262, Bytes03.b_261, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨151, Terms00.t_151, .kdf 150 132, Bytes01.b_146, true⟩)
              (.leaf ⟨663, Terms01.t_663, .kdf 660 662, Bytes05.b_477, true⟩))
            (.branch (.leaf ⟨407, Terms00.t_407, .kdf 404 176, Bytes02.b_170, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨87, Terms00.t_87, .kdf 86 37, Bytes01.b_84, true⟩)
              (.leaf ⟨599, Terms01.t_599, .tr8 598, Bytes05.b_473, true⟩))
            (.branch (.leaf ⟨343, Terms00.t_343, .kdf 342 37, Bytes03.b_298, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨215, Terms00.t_215, .cat 214 134, Bytes02.b_206, true⟩) .empty)
            (.branch (.leaf ⟨471, Terms01.t_471, .cat 470 134, Bytes04.b_372, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨55, Terms00.t_55, .cat 0 54, Bytes00.b_52, true⟩)
              (.leaf ⟨567, Terms01.t_567, .cat 566 134, Bytes05.b_468, true⟩))
            (.branch (.leaf ⟨311, Terms00.t_311, .cat 310 134, Bytes01.b_147, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨183, Terms00.t_183, .kdf 182 132, Bytes02.b_176, true⟩) .empty)
            (.branch (.leaf ⟨439, Terms00.t_439, .cat 438 40, Bytes04.b_340, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨119, Terms00.t_119, .cat 0 118, Bytes01.b_115, true⟩)
              (.leaf ⟨631, Terms01.t_631, .kdf 628 630, Bytes02.b_178, true⟩))
            (.branch (.leaf ⟨375, Terms00.t_375, .kdf 374 132, Bytes04.b_330, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨247, Terms00.t_247, .kdf 38 246, Bytes02.b_229, true⟩) .empty)
            (.branch (.leaf ⟨503, Terms01.t_503, .cat 502 134, Bytes04.b_404, true⟩) .empty))
        )
      )
    )
  )

def sub15 : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨15, Terms00.t_15, .dh 14 5, Bytes00.b_15, true⟩)
              (.leaf ⟨527, Terms01.t_527, .kdf 524 526, Bytes05.b_428, true⟩))
            (.branch (.leaf ⟨271, Terms00.t_271, .kdf 268 262, Bytes03.b_253, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨143, Terms00.t_143, .cat 10 142, Bytes01.b_138, true⟩)
              (.leaf ⟨655, Terms01.t_655, .kdf 652 654, Bytes05.b_477, true⟩))
            (.branch (.leaf ⟨399, Terms00.t_399, .tr8 398, Bytes02.b_171, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨79, Terms00.t_79, .cat 62 75, Bytes01.b_76, true⟩)
              (.leaf ⟨591, Terms01.t_591, .sRecvK 91 190, Bytes05.b_465, false⟩))
            (.branch (.leaf ⟨335, Terms00.t_335, .cat 334 134, Bytes03.b_290, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨207, Terms00.t_207, .cat 206 134, Bytes02.b_198, true⟩) .empty)
            (.branch (.leaf ⟨463, Terms01.t_463, .cat 462 134, Bytes04.b_364, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨47, Terms00.t_47, .kdf 28 46, Bytes00.b_46, true⟩)
              (.leaf ⟨559, Terms01.t_559, .kdf 556 558, Bytes05.b_460, true⟩))
            (.branch (.leaf ⟨303, Terms00.t_303, .kdf 300 302, Bytes03.b_267, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨175, Terms00.t_175, .cat 7 174, Bytes02.b_168, true⟩) .empty)
            (.branch (.leaf ⟨431, Terms00.t_431, .kdf 428 430, Bytes03.b_306, true⟩) .empty))
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨111, Terms00.t_111, .cat 0 110, Bytes01.b_107, true⟩)
              (.leaf ⟨623, Terms01.t_623, .cat 622 137, Bytes02.b_179, true⟩))
            (.branch (.leaf ⟨367, Terms00.t_367, .kdf 366 132, Bytes04.b_322, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨239, Terms00.t_239, .kdf 238 132, Bytes01.b_146, true⟩) .empty)
            (.branch (.leaf ⟨495, Terms01.t_495, .cat 494 134, Bytes04.b_396, true⟩) .empty))
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨31, Terms00.t_31, .kdf 28 30, Bytes00.b_30, true⟩)
              (.leaf ⟨543, Terms01.t_543, .kdf 540 542, Bytes05.b_444, true⟩))
            (.branch (.leaf ⟨287, Terms00.t_287, .kdf 282 286, Bytes03.b_269, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨159, Terms00.t_159, .cat 10 158, Bytes02.b_153, true⟩)
              (.leaf ⟨671, Terms01.t_671, .kdf 668 670, Bytes05.b_477, true⟩))
            (.branch (.leaf ⟨415, Terms00.t_415, .kdf 410 414, Bytes03.b_308, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨95, Terms00.t_95, .rnd 77 32, Bytes01.b_91, true⟩)
              (.leaf ⟨607, Terms01.t_607, .kdf 604 450, Bytes05.b_472, true⟩))
            (.branch (.leaf ⟨351, Terms00.t_351, .kdf 348 350, Bytes03.b_306, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨223, Terms00.t_223, .cat 222 134, Bytes02.b_214, true⟩) .empty)
            (.branch (.leaf ⟨479, Terms01.t_479, .cat 478 134, Bytes04.b_380, true⟩) .empty))
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.leaf ⟨63, Terms00.t_63, .rnd 39 32, Bytes00.b_60, true⟩)
              (.leaf ⟨575, Terms01.t_575, .kdf 574 132, Bytes05.b_467, true⟩))
            (.branch (.leaf ⟨319, Terms00.t_319, .cat 318 134, Bytes03.b_274, true⟩) .empty)
          )
          (.branch
            (.branch
              (.leaf ⟨191, Terms00.t_191, .trW 4 84 0 1 189 190 (DY.TrWire.canonicalVariation), Bytes02.b_183, true⟩)
              .empty)
            (.branch (.leaf ⟨447, Terms00.t_447, .cat 446 137, Bytes04.b_348, true⟩) .empty)
          )
        )
        (.branch
          (.branch
            (.branch
              (.leaf ⟨127, Terms00.t_127, .kemEnc 21 22, Bytes01.b_123, true⟩)
              (.leaf ⟨639, Terms01.t_639, .kdf 636 638, Bytes05.b_477, true⟩))
            (.branch (.leaf ⟨383, Terms00.t_383, .kdf 382 165, Bytes02.b_160, true⟩) .empty)
          )
          (.branch
            (.branch (.leaf ⟨255, Terms00.t_255, .kdf 11 254, Bytes03.b_237, true⟩) .empty)
            (.branch (.leaf ⟨511, Terms01.t_511, .cat 510 134, Bytes05.b_412, true⟩) .empty))
        )
      )
    )
  )

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes03
