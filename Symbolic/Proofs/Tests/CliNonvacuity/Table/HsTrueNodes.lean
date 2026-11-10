/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Terms01
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Bytes05
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Bytes06

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTrueNodes

open DY.Libsignal (HwBytes)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)

def hsTrueIdTree : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨0, Terms00.t_13, .rnd 10 32, Bytes00.b_13, true⟩)
                  (.leaf ⟨128, Terms01.t_728, .cat 49 127, Bytes06.b_532, true⟩))
                (.branch (.leaf ⟨64, Terms01.t_707, .kdf 61 63, Bytes06.b_512, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨32, Terms01.t_689, .cat 28 31, Bytes05.b_494, true⟩) .empty)
                (.branch (.leaf ⟨96, Terms00.t_98, .cat 49 95, Bytes01.b_94, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨16, Terms01.t_677, .rnd 27 32, Bytes05.b_484, true⟩) .empty)
                (.branch (.leaf ⟨80, Terms01.t_717, .cat 76 79, Bytes06.b_521, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨48, Terms01.t_698, .kdf 36 47, Bytes06.b_503, true⟩) .empty)
                (.branch (.leaf ⟨112, Terms00.t_114, .cat 49 111, Bytes01.b_110, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨8, Terms00.t_21, .kemPk 7, myKyberPubBytes, false⟩)
                  (.leaf ⟨136, Terms01.t_736, .cat 135 68, Bytes06.b_540, true⟩))
                (.branch
                  (.leaf ⟨72, Terms01.t_713, .sInit 48 49, Bytes06.b_518, false⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨40, Terms01.t_694, .kdf 36 39, Bytes06.b_499, true⟩) .empty)
                (.branch (.leaf ⟨104, Terms00.t_106, .cat 49 2, Bytes01.b_102, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨24, Terms00.t_12, .lit Bytes00.b_12, Bytes00.b_12, true⟩)
                  .empty)
                (.branch (.leaf ⟨88, Terms01.t_722, .cat 22 40, Bytes06.b_526, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨56, Terms01.t_702, .kdf 53 55, Bytes06.b_507, true⟩) .empty)
                (.branch (.leaf ⟨120, Terms00.t_122, .cat 86 119, Bytes01.b_118, true⟩) .empty))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨4, Terms00.t_4, .lit Bytes00.b_4, Bytes00.b_4, true⟩)
                  (.leaf ⟨132, Terms01.t_732, .kdf 23 60, Bytes06.b_536, true⟩))
                (.branch (.leaf ⟨68, Terms00.t_137, .cat 62 45, Bytes01.b_133, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨36, Terms01.t_693, .kdf 23 35, Bytes06.b_498, true⟩) .empty)
                (.branch (.leaf ⟨100, Terms00.t_102, .cat 38 99, Bytes01.b_98, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨20, Terms01.t_681, .dhPk 15, Bytes05.b_486, true⟩) .empty)
                (.branch (.leaf ⟨84, Terms01.t_721, .rnd 42 32, Bytes06.b_525, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨52, Terms01.t_700, .dh 22 0, Bytes06.b_505, true⟩) .empty)
                (.branch (.leaf ⟨116, Terms00.t_118, .cat 38 115, Bytes01.b_114, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨12, Terms00.t_203, .sig 2 9 11, Bytes02.b_191, false⟩) .empty)
                (.branch (.leaf ⟨76, Terms00.t_7, .cat 4 75, Bytes00.b_7, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨44, Terms01.t_696, .kdf 36 43, Bytes06.b_501, true⟩) .empty)
                (.branch (.leaf ⟨108, Terms00.t_110, .cat 38 107, Bytes01.b_106, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨28, Terms01.t_685, .dh 20 0, Bytes05.b_490, true⟩) .empty)
                (.branch (.leaf ⟨92, Terms00.t_56, .cat 87 91, Bytes00.b_53, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨60, Terms01.t_705, .kdf 59 38, Bytes06.b_510, true⟩) .empty)
                (.branch (.leaf ⟨124, Terms00.t_126, .cat 38 123, Bytes01.b_122, true⟩) .empty))
            )
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨2, Terms00.t_8, .rnd 5 32, Bytes00.b_8, true⟩)
                  (.leaf ⟨130, Terms01.t_730, .cat 38 129, Bytes06.b_534, true⟩))
                (.branch (.leaf ⟨66, Terms01.t_708, .cat 64 65, Bytes06.b_513, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨34, Terms01.t_691, .cat 26 33, Bytes05.b_496, true⟩) .empty)
                (.branch (.leaf ⟨98, Terms00.t_100, .cat 49 97, Bytes01.b_96, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨18, Terms01.t_679, .rnd 35 32, pt0, true⟩) .empty)
                (.branch (.leaf ⟨82, Terms01.t_719, .tr8 81, Bytes06.b_523, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨50, Terms00.t_58, .lit Bytes00.b_55, Bytes00.b_55, true⟩)
                  .empty)
                (.branch (.leaf ⟨114, Terms00.t_116, .cat 49 113, Bytes01.b_112, true⟩) .empty)
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨10, Terms00.t_201, .lit Bytes02.b_193, Bytes02.b_193, true⟩)
                  (.leaf ⟨138, Terms01.t_738, .kdf 135 80, Bytes06.b_542, true⟩))
                (.branch
                  (.leaf ⟨74, Terms01.t_715, .trW 4 22 0 0 71 73 (DY.TrWire.canonicalVariation), Bytes06.b_519, true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨42, Terms00.t_45, .cat 37 41, Bytes00.b_44, true⟩) .empty)
                (.branch (.leaf ⟨106, Terms00.t_108, .cat 86 105, Bytes01.b_104, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨26, Terms00.t_15, .dh 1 25, Bytes00.b_15, true⟩) .empty)
                (.branch (.leaf ⟨90, Terms00.t_54, .cat 49 89, Bytes00.b_1, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨58, Terms01.t_703, .cat 56 57, Bytes06.b_508, true⟩) .empty)
                (.branch (.leaf ⟨122, Terms00.t_124, .cat 38 121, Bytes01.b_120, true⟩) .empty))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨6, Terms00.t_199, .sig 2 3 5, Bytes02.b_191, false⟩)
                  (.leaf ⟨134, Terms01.t_734, .cat 133 65, Bytes06.b_538, true⟩))
                (.branch (.leaf ⟨70, Terms01.t_711, .kdf 61 69, Bytes06.b_516, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨38, Terms00.t_0, .lit Bytes00.b_0, Bytes00.b_0, true⟩) .empty)
                (.branch (.leaf ⟨102, Terms00.t_104, .cat 38 101, Bytes01.b_100, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨22, Terms01.t_683, .dhPk 17, Bytes05.b_488, true⟩) .empty)
                (.branch (.leaf ⟨86, Terms00.t_3, .lit Bytes00.b_3, Bytes00.b_3, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨54, Terms00.t_36, .lit Bytes00.b_35, Bytes00.b_35, true⟩)
                  .empty)
                (.branch (.leaf ⟨118, Terms00.t_120, .cat 49 7, Bytes01.b_116, true⟩) .empty)
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨14, Terms00.t_17, .dhPk 13, Bytes00.b_17, true⟩) .empty)
                (.branch (.leaf ⟨78, Terms00.t_10, .cat 4 77, Bytes00.b_10, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨46, Terms00.t_49, .cat 37 45, Bytes00.b_48, true⟩) .empty)
                (.branch (.leaf ⟨110, Terms00.t_112, .cat 38 109, Bytes01.b_108, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨30, Terms01.t_687, .kemSS 8 16, Bytes05.b_492, true⟩) .empty)
                (.branch
                  (.leaf ⟨94, Terms01.t_724, .sSendSt 72 19, Bytes06.b_528, false⟩)
                  .empty)
              )
              (.branch
                (.branch
                  (.leaf ⟨62, Terms00.t_131, .lit Bytes01.b_127, Bytes01.b_127, true⟩)
                  .empty)
                (.branch (.leaf ⟨126, Terms01.t_726, .cat 38 125, Bytes06.b_530, true⟩) .empty)
              )
            )
          )
        )
      )
    )
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨1, Terms00.t_14, .dhPk 0, Bytes00.b_14, true⟩)
                  (.leaf ⟨129, Terms01.t_729, .cat 38 128, Bytes06.b_533, true⟩))
                (.branch (.leaf ⟨65, Terms00.t_134, .cat 62 41, Bytes01.b_130, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨33, Terms01.t_690, .cat 27 32, Bytes05.b_495, true⟩) .empty)
                (.branch (.leaf ⟨97, Terms00.t_99, .cat 85 96, Bytes01.b_95, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨17, Terms01.t_678, .rnd 28 32, Bytes05.b_485, true⟩) .empty)
                (.branch (.leaf ⟨81, Terms01.t_718, .kdf 67 80, Bytes06.b_522, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨49, Terms00.t_1, .lit Bytes00.b_1, Bytes00.b_1, true⟩) .empty)
                (.branch (.leaf ⟨113, Terms00.t_115, .cat 86 112, Bytes01.b_111, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨9, Terms00.t_200, .rnd 17 64, Bytes02.b_192, true⟩)
                  (.leaf ⟨137, Terms01.t_737, .kdf 132 136, Bytes06.b_541, true⟩))
                (.branch
                  (.leaf ⟨73, Terms01.t_714, .sSendM 72 19, Bytes00.b_70, false⟩)
                  .empty)
              )
              (.branch
                (.branch
                  (.leaf ⟨41, Terms00.t_39, .lit Bytes00.b_38, Bytes00.b_38, true⟩)
                  .empty)
                (.branch (.leaf ⟨105, Terms00.t_107, .cat 49 104, Bytes01.b_103, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨25, Terms00.t_5, .rnd 0 32, Bytes00.b_5, true⟩) .empty)
                (.branch
                  (.leaf ⟨89, Terms00.t_53, .lit ([] : HwBytes), ([] : HwBytes), true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨57, Terms00.t_40, .cat 54 41, Bytes00.b_39, true⟩) .empty)
                (.branch (.leaf ⟨121, Terms00.t_123, .cat 49 120, Bytes01.b_119, true⟩) .empty))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨5, Terms00.t_198, .cat 4 1, Bytes02.b_190, true⟩)
                  (.leaf ⟨133, Terms01.t_733, .kdf 132 63, Bytes06.b_537, true⟩))
                (.branch (.leaf ⟨69, Terms01.t_710, .cat 67 68, Bytes06.b_515, true⟩) .empty)
              )
              (.branch
                (.branch
                  (.leaf ⟨37, Terms00.t_29, .lit Bytes00.b_28, Bytes00.b_28, true⟩)
                  .empty)
                (.branch (.leaf ⟨101, Terms00.t_103, .cat 38 100, Bytes01.b_99, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨21, Terms01.t_682, .kemEnc 8 16, Bytes05.b_487, true⟩) .empty)
                (.branch (.leaf ⟨85, Terms00.t_2, .lit Bytes00.b_2, Bytes00.b_2, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨53, Terms01.t_701, .kdf 40 52, Bytes06.b_506, true⟩) .empty)
                (.branch (.leaf ⟨117, Terms00.t_119, .cat 38 116, Bytes01.b_115, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨13, Terms00.t_16, .rnd 22 32, Bytes00.b_16, true⟩) .empty)
                (.branch (.leaf ⟨77, Terms00.t_9, .dhPk 2, Bytes00.b_9, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨45, Terms00.t_48, .lit Bytes00.b_47, Bytes00.b_47, true⟩)
                  .empty)
                (.branch (.leaf ⟨109, Terms00.t_111, .cat 38 108, Bytes01.b_107, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨29, Terms01.t_686, .dh 20 13, Bytes05.b_491, true⟩) .empty)
                (.branch (.leaf ⟨93, Terms01.t_723, .kdf 59 41, Bytes06.b_527, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨61, Terms01.t_706, .kdf 51 60, Bytes06.b_511, true⟩) .empty)
                (.branch (.leaf ⟨125, Terms01.t_725, .cat 38 13, Bytes06.b_529, true⟩) .empty))
            )
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨3, Terms00.t_197, .rnd 11 64, Bytes02.b_189, true⟩)
                  (.leaf ⟨131, Terms01.t_731, .cat 38 130, Bytes06.b_535, true⟩))
                (.branch (.leaf ⟨67, Terms01.t_709, .kdf 61 66, Bytes06.b_514, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨35, Terms01.t_692, .cat 24 34, Bytes06.b_497, true⟩) .empty)
                (.branch (.leaf ⟨99, Terms00.t_101, .cat 38 98, Bytes01.b_97, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨19, Terms01.t_680, .rnd 36 32, Bytes00.b_56, true⟩) .empty)
                (.branch (.leaf ⟨83, Terms01.t_720, .cat 74 82, Bytes06.b_524, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨51, Terms01.t_699, .sChain 48 49 50, Bytes06.b_504, false⟩)
                  .empty)
                (.branch (.leaf ⟨115, Terms00.t_117, .cat 38 114, Bytes01.b_113, true⟩) .empty)
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨11, Terms00.t_202, .cat 10 8, Bytes02.b_194, true⟩)
                  (.leaf ⟨139, Terms01.t_739, .tr8 138, Bytes06.b_543, true⟩))
                (.branch (.leaf ⟨75, Terms00.t_6, .dhPk 25, Bytes00.b_6, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨43, Terms01.t_695, .cat 40 42, Bytes06.b_500, true⟩) .empty)
                (.branch (.leaf ⟨107, Terms00.t_109, .cat 49 106, Bytes01.b_105, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨27, Terms01.t_684, .dh 20 2, Bytes05.b_489, true⟩) .empty)
                (.branch (.leaf ⟨91, Terms00.t_55, .cat 38 90, Bytes00.b_52, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨59, Terms01.t_704, .kdf 53 58, Bytes06.b_509, true⟩) .empty)
                (.branch (.leaf ⟨123, Terms00.t_125, .cat 38 122, Bytes01.b_121, true⟩) .empty))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨7, Terms00.t_20, .rnd 16 64, Bytes00.b_20, true⟩)
                  (.leaf ⟨135, Terms01.t_735, .kdf 132 134, Bytes06.b_539, true⟩))
                (.branch
                  (.leaf ⟨71, Terms01.t_712, .sym 64 70 18, Bytes06.b_517, true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨39, Terms00.t_30, .cat 37 38, Bytes00.b_29, true⟩) .empty)
                (.branch (.leaf ⟨103, Terms00.t_105, .cat 38 102, Bytes01.b_101, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨23, Terms00.t_11, .lit Bytes00.b_11, Bytes00.b_11, true⟩)
                  .empty)
                (.branch
                  (.leaf ⟨87, Terms00.t_43, .lit Bytes00.b_42, Bytes00.b_42, true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨55, Terms00.t_37, .cat 54 38, Bytes00.b_36, true⟩) .empty)
                (.branch (.leaf ⟨119, Terms00.t_121, .cat 38 118, Bytes01.b_117, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨15, Terms01.t_676, .rnd 26 32, Bytes05.b_483, true⟩) .empty)
                (.branch (.leaf ⟨79, Terms01.t_716, .cat 78 74, Bytes06.b_520, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨47, Terms01.t_697, .cat 44 46, Bytes06.b_502, true⟩) .empty)
                (.branch (.leaf ⟨111, Terms00.t_113, .cat 38 0, Bytes01.b_109, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨31, Terms01.t_688, .cat 29 30, Bytes05.b_493, true⟩) .empty)
                (.branch (.leaf ⟨95, Terms00.t_97, .cat 49 25, Bytes01.b_93, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨63, Terms00.t_132, .cat 62 38, Bytes01.b_128, true⟩) .empty)
                (.branch (.leaf ⟨127, Terms01.t_727, .cat 86 126, Bytes06.b_531, true⟩) .empty))
            )
          )
        )
      )
    )
  )

end Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTrueNodes
