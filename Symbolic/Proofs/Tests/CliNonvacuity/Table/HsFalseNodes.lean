/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Bytes05
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Terms00

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.HsFalseNodes

open DY.Libsignal (HwBytes)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)

def hsFalseIdTree : BinTree CertNode :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨0, Terms00.t_13, .rnd 10 32, Bytes00.b_13, true⟩)
                  (.leaf ⟨128, Terms00.t_212, .tr8 127, Bytes02.b_203, true⟩))
                (.branch (.leaf ⟨64, Terms00.t_137, .cat 58 41, Bytes01.b_133, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨32, Terms00.t_28, .kdf 21 31, Bytes00.b_27, true⟩) .empty)
                (.branch (.leaf ⟨96, Terms00.t_102, .cat 34 95, Bytes01.b_98, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨16, Terms00.t_140, .rnd 31 32, pt0, true⟩) .empty)
                (.branch (.leaf ⟨80, Terms00.t_156, .rnd 38 32, Bytes05.b_482, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨48, Terms00.t_34, .dh 20 0, Bytes00.b_33, true⟩) .empty)
                (.branch (.leaf ⟨112, Terms00.t_118, .cat 34 111, Bytes01.b_114, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨8, Terms00.t_21, .kemPk 7, myKyberPubBytes, false⟩) .empty)
                (.branch (.leaf ⟨72, Terms00.t_7, .cat 4 71, Bytes00.b_7, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨40, Terms00.t_47, .kdf 32 39, Bytes00.b_46, true⟩) .empty)
                (.branch (.leaf ⟨104, Terms00.t_110, .cat 34 103, Bytes01.b_106, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨24, Terms00.t_15, .dh 1 23, Bytes00.b_15, true⟩) .empty)
                (.branch (.leaf ⟨88, Terms00.t_56, .cat 83 87, Bytes00.b_53, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨56, Terms00.t_129, .kdf 55 34, Bytes01.b_125, true⟩) .empty)
                (.branch (.leaf ⟨120, Terms00.t_126, .cat 34 119, Bytes01.b_122, true⟩) .empty))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨4, Terms00.t_4, .lit Bytes00.b_4, Bytes00.b_4, true⟩) .empty)
                (.branch (.leaf ⟨68, Terms00.t_52, .sInit 44 45, Bytes00.b_51, false⟩) .empty))
              (.branch
                (.branch (.leaf ⟨36, Terms00.t_31, .kdf 32 35, Bytes00.b_30, true⟩) .empty)
                (.branch (.leaf ⟨100, Terms00.t_106, .cat 45 2, Bytes01.b_102, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨20, Terms00.t_33, .dhPk 15, Bytes00.b_32, true⟩) .empty)
                (.branch (.leaf ⟨84, Terms00.t_44, .cat 20 36, Bytes00.b_43, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨52, Terms00.t_38, .kdf 49 51, Bytes00.b_37, true⟩) .empty)
                (.branch (.leaf ⟨116, Terms00.t_122, .cat 82 115, Bytes01.b_118, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨12, Terms00.t_203, .sig 2 9 11, Bytes02.b_191, false⟩) .empty)
                (.branch (.leaf ⟨76, Terms00.t_144, .cat 72 75, Bytes01.b_139, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨44, Terms00.t_51, .kdf 32 43, Bytes00.b_50, true⟩) .empty)
                (.branch (.leaf ⟨108, Terms00.t_114, .cat 45 107, Bytes01.b_110, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨28, Terms00.t_24, .cat 26 27, Bytes00.b_23, true⟩) .empty)
                (.branch (.leaf ⟨92, Terms00.t_98, .cat 45 91, Bytes01.b_94, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨60, Terms00.t_133, .kdf 57 59, Bytes01.b_129, true⟩) .empty)
                (.branch
                  (.leaf ⟨124, Terms00.t_208, .kdf 121 123, Bytes02.b_199, true⟩)
                  .empty)
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
                (.branch (.leaf ⟨2, Terms00.t_8, .rnd 5 32, Bytes00.b_8, true⟩) .empty)
                (.branch (.leaf ⟨66, Terms00.t_139, .kdf 57 65, Bytes01.b_135, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨34, Terms00.t_0, .lit Bytes00.b_0, Bytes00.b_0, true⟩) .empty)
                (.branch (.leaf ⟨98, Terms00.t_104, .cat 34 97, Bytes01.b_100, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨18, Terms00.t_17, .dhPk 13, Bytes00.b_17, true⟩) .empty)
                (.branch (.leaf ⟨82, Terms00.t_3, .lit Bytes00.b_3, Bytes00.b_3, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨50, Terms00.t_36, .lit Bytes00.b_35, Bytes00.b_35, true⟩)
                  .empty)
                (.branch (.leaf ⟨114, Terms00.t_120, .cat 45 7, Bytes01.b_116, true⟩) .empty)
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨10, Terms00.t_201, .lit Bytes02.b_193, Bytes02.b_193, true⟩)
                  .empty)
                (.branch (.leaf ⟨74, Terms00.t_10, .cat 4 73, Bytes00.b_10, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨42, Terms00.t_49, .cat 33 41, Bytes00.b_48, true⟩) .empty)
                (.branch (.leaf ⟨106, Terms00.t_112, .cat 34 105, Bytes01.b_108, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨26, Terms00.t_19, .dh 18 0, Bytes00.b_19, true⟩) .empty)
                (.branch
                  (.leaf ⟨90, Terms00.t_60, .sSendSt 68 17, Bytes00.b_57, false⟩)
                  .empty)
              )
              (.branch
                (.branch
                  (.leaf ⟨58, Terms00.t_131, .lit Bytes01.b_127, Bytes01.b_127, true⟩)
                  .empty)
                (.branch (.leaf ⟨122, Terms00.t_206, .kdf 121 59, Bytes02.b_197, true⟩) .empty)
              )
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨6, Terms00.t_199, .sig 2 3 5, Bytes02.b_191, false⟩) .empty)
                (.branch
                  (.leaf ⟨70, Terms00.t_142, .trW 4 20 0 0 67 69 (DY.TrWire.canonicalVariation), Bytes01.b_137, true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨38, Terms00.t_45, .cat 33 37, Bytes00.b_44, true⟩) .empty)
                (.branch (.leaf ⟨102, Terms00.t_108, .cat 82 101, Bytes01.b_104, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨22, Terms00.t_12, .lit Bytes00.b_12, Bytes00.b_12, true⟩)
                  .empty)
                (.branch (.leaf ⟨86, Terms00.t_54, .cat 45 85, Bytes00.b_1, true⟩) .empty)
              )
              (.branch
                (.branch (.leaf ⟨54, Terms00.t_41, .cat 52 53, Bytes00.b_40, true⟩) .empty)
                (.branch (.leaf ⟨118, Terms00.t_124, .cat 34 117, Bytes01.b_120, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨14, Terms00.t_22, .rnd 23 32, Bytes00.b_21, true⟩) .empty)
                (.branch (.leaf ⟨78, Terms00.t_146, .tr8 77, Bytes01.b_141, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨46, Terms00.t_58, .lit Bytes00.b_55, Bytes00.b_55, true⟩)
                  .empty)
                (.branch (.leaf ⟨110, Terms00.t_116, .cat 45 109, Bytes01.b_112, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨30, Terms00.t_26, .cat 24 29, Bytes00.b_25, true⟩) .empty)
                (.branch (.leaf ⟨94, Terms00.t_100, .cat 45 93, Bytes01.b_96, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨62, Terms00.t_135, .cat 60 61, Bytes01.b_131, true⟩) .empty)
                (.branch
                  (.leaf ⟨126, Terms00.t_210, .kdf 121 125, Bytes02.b_201, true⟩)
                  .empty)
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
                (.branch (.leaf ⟨1, Terms00.t_14, .dhPk 0, Bytes00.b_14, true⟩) .empty)
                (.branch (.leaf ⟨65, Terms00.t_138, .cat 63 64, Bytes01.b_134, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨33, Terms00.t_29, .lit Bytes00.b_28, Bytes00.b_28, true⟩)
                  .empty)
                (.branch (.leaf ⟨97, Terms00.t_103, .cat 34 96, Bytes01.b_99, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨17, Terms00.t_59, .rnd 32 32, Bytes00.b_56, true⟩) .empty)
                (.branch (.leaf ⟨81, Terms00.t_2, .lit Bytes00.b_2, Bytes00.b_2, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨49, Terms00.t_35, .kdf 36 48, Bytes00.b_34, true⟩) .empty)
                (.branch (.leaf ⟨113, Terms00.t_119, .cat 34 112, Bytes01.b_115, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨9, Terms00.t_200, .rnd 17 64, Bytes02.b_192, true⟩) .empty)
                (.branch (.leaf ⟨73, Terms00.t_9, .dhPk 2, Bytes00.b_9, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨41, Terms00.t_48, .lit Bytes00.b_47, Bytes00.b_47, true⟩)
                  .empty)
                (.branch (.leaf ⟨105, Terms00.t_111, .cat 34 104, Bytes01.b_107, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨25, Terms00.t_18, .dh 18 2, Bytes00.b_18, true⟩) .empty)
                (.branch (.leaf ⟨89, Terms00.t_57, .kdf 55 37, Bytes00.b_54, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨57, Terms00.t_130, .kdf 47 56, Bytes01.b_126, true⟩) .empty)
                (.branch (.leaf ⟨121, Terms00.t_205, .kdf 21 56, Bytes02.b_196, true⟩) .empty))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨5, Terms00.t_198, .cat 4 1, Bytes02.b_190, true⟩) .empty)
                (.branch (.leaf ⟨69, Terms00.t_73, .sSendM 68 17, Bytes00.b_70, false⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨37, Terms00.t_39, .lit Bytes00.b_38, Bytes00.b_38, true⟩)
                  .empty)
                (.branch (.leaf ⟨101, Terms00.t_107, .cat 45 100, Bytes01.b_103, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch
                  (.leaf ⟨21, Terms00.t_11, .lit Bytes00.b_11, Bytes00.b_11, true⟩)
                  .empty)
                (.branch
                  (.leaf ⟨85, Terms00.t_53, .lit ([] : HwBytes), ([] : HwBytes), true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨53, Terms00.t_40, .cat 50 37, Bytes00.b_39, true⟩) .empty)
                (.branch (.leaf ⟨117, Terms00.t_123, .cat 45 116, Bytes01.b_119, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨13, Terms00.t_16, .rnd 22 32, Bytes00.b_16, true⟩) .empty)
                (.branch (.leaf ⟨77, Terms00.t_145, .kdf 63 76, Bytes01.b_140, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨45, Terms00.t_1, .lit Bytes00.b_1, Bytes00.b_1, true⟩) .empty)
                (.branch (.leaf ⟨109, Terms00.t_115, .cat 82 108, Bytes01.b_111, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨29, Terms00.t_25, .cat 25 28, Bytes00.b_24, true⟩) .empty)
                (.branch (.leaf ⟨93, Terms00.t_99, .cat 81 92, Bytes01.b_95, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨61, Terms00.t_134, .cat 58 37, Bytes01.b_130, true⟩) .empty)
                (.branch (.leaf ⟨125, Terms00.t_209, .cat 124 64, Bytes02.b_200, true⟩) .empty))
            )
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨3, Terms00.t_197, .rnd 11 64, Bytes02.b_189, true⟩) .empty)
                (.branch
                  (.leaf ⟨67, Terms00.t_141, .sym 60 66 16, Bytes01.b_136, true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨35, Terms00.t_30, .cat 33 34, Bytes00.b_29, true⟩) .empty)
                (.branch (.leaf ⟨99, Terms00.t_105, .cat 34 98, Bytes01.b_101, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨19, Terms00.t_127, .kemEnc 8 14, Bytes01.b_123, true⟩) .empty)
                (.branch
                  (.leaf ⟨83, Terms00.t_43, .lit Bytes00.b_42, Bytes00.b_42, true⟩)
                  .empty)
              )
              (.branch
                (.branch (.leaf ⟨51, Terms00.t_37, .cat 50 34, Bytes00.b_36, true⟩) .empty)
                (.branch (.leaf ⟨115, Terms00.t_121, .cat 34 114, Bytes01.b_117, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨11, Terms00.t_202, .cat 10 8, Bytes02.b_194, true⟩) .empty)
                (.branch (.leaf ⟨75, Terms00.t_143, .cat 74 70, Bytes01.b_138, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨43, Terms00.t_50, .cat 40 42, Bytes00.b_49, true⟩) .empty)
                (.branch (.leaf ⟨107, Terms00.t_113, .cat 34 0, Bytes01.b_109, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨27, Terms00.t_23, .kemSS 8 14, Bytes00.b_22, true⟩) .empty)
                (.branch (.leaf ⟨91, Terms00.t_97, .cat 45 23, Bytes01.b_93, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨59, Terms00.t_132, .cat 58 34, Bytes01.b_128, true⟩) .empty)
                (.branch (.leaf ⟨123, Terms00.t_207, .cat 122 61, Bytes02.b_198, true⟩) .empty))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨7, Terms00.t_20, .rnd 16 64, Bytes00.b_20, true⟩) .empty)
                (.branch (.leaf ⟨71, Terms00.t_6, .dhPk 23, Bytes00.b_6, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨39, Terms00.t_46, .cat 36 38, Bytes00.b_45, true⟩) .empty)
                (.branch (.leaf ⟨103, Terms00.t_109, .cat 45 102, Bytes01.b_105, true⟩) .empty))
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨23, Terms00.t_5, .rnd 0 32, Bytes00.b_5, true⟩) .empty)
                (.branch (.leaf ⟨87, Terms00.t_55, .cat 34 86, Bytes00.b_52, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨55, Terms00.t_42, .kdf 49 54, Bytes00.b_41, true⟩) .empty)
                (.branch (.leaf ⟨119, Terms00.t_125, .cat 34 118, Bytes01.b_121, true⟩) .empty))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf ⟨15, Terms00.t_32, .rnd 24 32, Bytes00.b_31, true⟩) .empty)
                (.branch (.leaf ⟨79, Terms00.t_147, .cat 70 78, Bytes01.b_142, true⟩) .empty))
              (.branch
                (.branch
                  (.leaf ⟨47, Terms00.t_128, .sChain 44 45 46, Bytes01.b_124, false⟩)
                  .empty)
                (.branch (.leaf ⟨111, Terms00.t_117, .cat 34 110, Bytes01.b_113, true⟩) .empty)
              )
            )
            (.branch
              (.branch
                (.branch (.leaf ⟨31, Terms00.t_27, .cat 22 30, Bytes00.b_26, true⟩) .empty)
                (.branch (.leaf ⟨95, Terms00.t_101, .cat 34 94, Bytes01.b_97, true⟩) .empty))
              (.branch
                (.branch (.leaf ⟨63, Terms00.t_136, .kdf 57 62, Bytes01.b_132, true⟩) .empty)
                (.branch (.leaf ⟨127, Terms00.t_211, .kdf 124 76, Bytes02.b_202, true⟩) .empty))
            )
          )
        )
      )
    )
  )

end Symbolic.Proofs.Tests.CliNonvacuity.Table.HsFalseNodes
