/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes00
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes01
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes02
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes03

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.CliTable

open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (Trie emptyTrie)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode CertTable)

def cliIdTree : BinTree CertNode :=
  .branch
    (.branch
      (.branch (.branch Nodes00.sub00 Nodes00.sub01)
               (.branch Nodes00.sub02 Nodes00.sub03))
      (.branch (.branch Nodes01.sub04 Nodes01.sub05)
               (.branch Nodes01.sub06 Nodes01.sub07)))
    (.branch
      (.branch (.branch Nodes02.sub08 Nodes02.sub09)
               (.branch Nodes02.sub10 Nodes02.sub11))
      (.branch (.branch Nodes03.sub12 Nodes03.sub13)
               (.branch Nodes03.sub14 Nodes03.sub15)))

def cliHashTrie : Trie Nat :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [450, 262, 176]) (emptyTrie 0))
                  (.branch (.leaf [449, 108]) (.leaf [524, 485, 443, 348, 317, 205, 33])))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [137]))
                  (.branch (.leaf [559, 480, 185]) (emptyTrie 0)))
              )
              (.branch
                (.branch
                  (.branch
                    (.leaf [670,
                      662,
                      654,
                      646,
                      638,
                      630,
                      621,
                      612,
                      603,
                      594,
                      585,
                      576,
                      567,
                      558,
                      550,
                      542,
                      511,
                      503,
                      479,
                      471,
                      463,
                      430,
                      421,
                      412,
                      403,
                      394,
                      385,
                      376,
                      368,
                      335,
                      311,
                      302,
                      293,
                      284,
                      275,
                      215,
                      184,
                      168,
                      152])
                    (emptyTrie 0)
                  )
                  (.branch (emptyTrie 0) (.leaf [290]))
                )
                (.branch (.branch (.leaf [54]) (.leaf [190, 180, 96])) (emptyTrie 1))
              )
            )
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [548, 509, 469, 374, 166, 128, 26]) (.leaf [175, 47]))
                  (.branch (.leaf [201]) (emptyTrie 0)))
                (.branch
                  (.branch
                    (.leaf [247, 52])
                    (.leaf [529, 490, 448, 353, 322, 260, 226, 210, 65]))
                  (.branch (.leaf [400, 91]) (emptyTrie 0))
                )
              )
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [141, 38]))
                  (.branch (.leaf [419, 410, 241]) (emptyTrie 0)))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [95]))
                  (.branch (emptyTrie 0) (.leaf [3])))
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [519, 115]) (.leaf [126, 119, 112, 105, 104, 103, 92]))
                  (.branch (.leaf [1]) (emptyTrie 0)))
                (emptyTrie 2)
              )
              (.branch
                (.branch
                  (.branch (.leaf [174]) (.leaf [8]))
                  (.branch (emptyTrie 0) (.leaf [537, 498, 458, 363, 330, 270, 234, 139])))
                (.branch (.branch (emptyTrie 0) (.leaf [147, 6])) (emptyTrie 1))
              )
            )
            (.branch
              (.branch
                (.branch
                  (emptyTrie 1)
                  (.branch
                    (.leaf [536, 497, 457, 362, 329, 269, 242, 233, 199, 138])
                    (.leaf [545, 506, 466, 371, 338, 278, 218, 191, 155]))
                )
                (.branch
                  (.branch (emptyTrie 0) (.leaf [308, 78]))
                  (.branch (emptyTrie 0) (.leaf [341, 101])))
              )
              (.branch
                (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [203])))
                (emptyTrie 2))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [27])))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [520, 439, 344, 249, 88, 70, 41]))
                  (emptyTrie 1))
              )
              (.branch
                (.branch
                  (.branch (.leaf [557, 478, 183, 24]) (emptyTrie 0))
                  (.branch (.leaf [521]) (emptyTrie 0)))
                (.branch (.branch (emptyTrie 0) (.leaf [83, 12])) (emptyTrie 1))
              )
            )
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [239]) (emptyTrie 0))
                  (.branch (.leaf [564]) (emptyTrie 0)))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [200]))
                  (.branch (.leaf [409]) (emptyTrie 0)))
              )
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [68, 49, 15]) (emptyTrie 0)))
                (.branch
                  (.branch (.leaf [540, 501, 461, 366, 333, 213, 31]) (emptyTrie 0))
                  (.branch (.leaf [532, 493, 453, 358, 325, 130]) (emptyTrie 0)))
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [40]))
                  (.branch (emptyTrie 0) (.leaf [121])))
                (.branch (emptyTrie 1) (.branch (.leaf [354]) (emptyTrie 0)))
              )
              (.branch
                (.branch (.branch (.leaf [591]) (emptyTrie 0)) (emptyTrie 1))
                (.branch
                  (emptyTrie 1)
                  (.branch (.leaf [541, 502, 462, 367, 334, 274, 214, 151]) (emptyTrie 0)))
              )
            )
            (.branch
              (.branch
                (.branch
                  (.branch
                    (emptyTrie 0)
                    (.leaf [674,
                      666,
                      658,
                      650,
                      642,
                      634,
                      628,
                      625,
                      616,
                      607,
                      598,
                      589,
                      580,
                      571,
                      562,
                      554,
                      546,
                      515,
                      507,
                      483,
                      475,
                      467,
                      434,
                      425,
                      416,
                      407,
                      398,
                      389,
                      380,
                      372,
                      339,
                      315,
                      306,
                      297,
                      288,
                      279,
                      219,
                      194,
                      177,
                      161])
                  )
                  (emptyTrie 1)
                )
                (.branch (.branch (.leaf [198, 196]) (emptyTrie 0)) (emptyTrie 1))
              )
              (.branch
                (.branch (.branch (.leaf [192]) (.leaf [19])) (emptyTrie 1))
                (.branch
                  (.branch (.leaf [46]) (emptyTrie 0))
                  (.branch (.leaf [533, 494, 454, 359, 326, 266, 230, 133]) (emptyTrie 0)))
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
                (.branch (emptyTrie 1) (.branch (.leaf [382]) (emptyTrie 0)))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [140]))
                  (.branch (.leaf [668, 601]) (emptyTrie 0)))
              )
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [261]) (emptyTrie 0)))
                (.branch (emptyTrie 1) (.branch (.leaf [582]) (emptyTrie 0))))
            )
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [58]) (emptyTrie 0))
                  (.branch (emptyTrie 0) (.leaf [131])))
                (.branch
                  (.branch
                    (.leaf [675,
                      667,
                      659,
                      651,
                      643,
                      635,
                      626,
                      617,
                      608,
                      599,
                      590,
                      581,
                      572,
                      563,
                      555,
                      547,
                      539,
                      531,
                      516,
                      508,
                      500,
                      492,
                      484,
                      476,
                      468,
                      460,
                      452,
                      435,
                      426,
                      417,
                      408,
                      399,
                      390,
                      381,
                      373,
                      365,
                      357,
                      340,
                      332,
                      324,
                      316,
                      307,
                      298,
                      289,
                      280,
                      272,
                      264,
                      245,
                      236,
                      228,
                      220,
                      212,
                      195,
                      178,
                      162,
                      146,
                      7])
                    (emptyTrie 0)
                  )
                  (.branch (.leaf [438, 248, 69]) (.leaf [345, 89]))
                )
              )
              (.branch
                (.branch
                  (.branch (.leaf [93, 76]) (emptyTrie 0))
                  (.branch (.leaf [30]) (.leaf [644, 574])))
                (.branch (.branch (emptyTrie 0) (.leaf [14])) (emptyTrie 1))
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [39]) (.leaf [652, 583])))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [63]))
                  (.branch (emptyTrie 0) (.leaf [21])))
              )
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [553, 514, 474, 379, 171]))
                  (.branch
                    (.leaf [672,
                      664,
                      656,
                      648,
                      640,
                      632,
                      623,
                      614,
                      605,
                      596,
                      587,
                      578,
                      569,
                      560,
                      552,
                      544,
                      513,
                      505,
                      481,
                      473,
                      465,
                      432,
                      423,
                      414,
                      405,
                      396,
                      387,
                      378,
                      370,
                      337,
                      313,
                      304,
                      295,
                      286,
                      277,
                      217,
                      186,
                      170,
                      154,
                      85])
                    (emptyTrie 0)
                  )
                )
                (emptyTrie 2)
              )
            )
            (.branch
              (emptyTrie 3)
              (.branch
                (.branch (.branch (.leaf [124, 123, 117, 110]) (.leaf [22])) (emptyTrie 1))
                (.branch
                  (.branch
                    (.leaf [671,
                      663,
                      655,
                      647,
                      639,
                      631,
                      622,
                      613,
                      604,
                      595,
                      586,
                      577,
                      568,
                      431,
                      422,
                      413,
                      404,
                      395,
                      386,
                      312,
                      303,
                      294,
                      285])
                    (emptyTrie 0)
                  )
                  (emptyTrie 1)
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
                  (.branch (emptyTrie 0) (.leaf [281]))
                  (.branch (emptyTrie 0) (.leaf [437, 36])))
                (emptyTrie 2)
              )
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [238]) (emptyTrie 0)))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [114]))
                  (.branch (.leaf [609]) (.leaf [29])))
              )
            )
            (.branch
              (emptyTrie 3)
              (.branch
                (emptyTrie 2)
                (.branch
                  (.branch (emptyTrie 0) (.leaf [523, 442, 347, 253, 204, 181, 165, 129]))
                  (emptyTrie 1))
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [534, 495, 455, 360, 327, 267, 240, 231, 135]) (emptyTrie 0))
                  (emptyTrie 1))
                (.branch (.branch (emptyTrie 0) (.leaf [197])) (emptyTrie 1))
              )
              (.branch
                (.branch
                  (.branch (.leaf [122]) (emptyTrie 0))
                  (.branch (.leaf [120]) (emptyTrie 0)))
                (.branch (.branch (emptyTrie 0) (.leaf [440, 250, 71])) (emptyTrie 1))
              )
            )
            (.branch
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [252, 61]) (emptyTrie 0)))
                (.branch
                  (.branch (emptyTrie 0) (.leaf [81]))
                  (.branch (.leaf [636, 565]) (.leaf [107])))
              )
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [132, 55]))
                  (.branch (.leaf [517]) (emptyTrie 0)))
                (.branch
                  (.branch (.leaf [627, 549, 510, 470, 375, 167, 97, 25]) (.leaf [17]))
                  (emptyTrie 1))
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
                (emptyTrie 2)
                (.branch (emptyTrie 1) (.branch (.leaf [561, 482, 187]) (emptyTrie 0))))
              (.branch
                (.branch (.branch (emptyTrie 0) (.leaf [383])) (emptyTrie 1))
                (.branch (.branch (emptyTrie 0) (.leaf [44])) (emptyTrie 1)))
            )
            (.branch
              (.branch
                (.branch (.branch (.leaf [237, 163, 43]) (.leaf [51])) (emptyTrie 1))
                (.branch (.branch (.leaf [72, 34]) (emptyTrie 0)) (emptyTrie 1)))
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [243]) (.leaf [127, 23])))
                (.branch
                  (emptyTrie 1)
                  (.branch (.leaf [526, 487, 445, 350, 319, 257, 223, 207]) (emptyTrie 0)))
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [0]) (emptyTrie 0)))
                (.branch
                  (.branch (.leaf [156]) (emptyTrie 0))
                  (.branch (emptyTrie 0) (.leaf [342])))
              )
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [551, 512, 472, 377, 169]))
                  (.branch (.leaf [84]) (.leaf [189])))
                (emptyTrie 2)
              )
            )
            (.branch
              (.branch
                (.branch
                  (.branch
                    (emptyTrie 0)
                    (.leaf [538, 499, 459, 364, 331, 271, 244, 235, 145, 99]))
                  (emptyTrie 1)
                )
                (.branch (emptyTrie 1) (.branch (.leaf [98]) (emptyTrie 0)))
              )
              (.branch
                (.branch (.branch (.leaf [16]) (emptyTrie 0)) (emptyTrie 1))
                (emptyTrie 2))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [53]) (emptyTrie 0))
                  (.branch (.leaf [125, 118, 111, 102]) (emptyTrie 0)))
                (.branch (.branch (emptyTrie 0) (.leaf [299])) (emptyTrie 1))
              )
              (.branch
                (emptyTrie 2)
                (.branch
                  (.branch (.leaf [11]) (emptyTrie 0))
                  (.branch (.leaf [74]) (emptyTrie 0)))
              )
            )
            (.branch
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [66]) (.leaf [436])))
                (.branch (.branch (emptyTrie 0) (.leaf [100])) (emptyTrie 1)))
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [79]) (emptyTrie 0)))
                (.branch (emptyTrie 1) (.branch (.leaf [2]) (.leaf [392]))))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [309]))
                  (.branch (.leaf [4]) (emptyTrie 0)))
                (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [556, 477, 401, 182])))
              )
              (.branch
                (.branch (.branch (.leaf [28, 13]) (emptyTrie 0)) (emptyTrie 1))
                (.branch
                  (.branch (.leaf [660, 619, 610, 592, 9]) (emptyTrie 0))
                  (.branch (emptyTrie 0) (.leaf [530, 491, 451, 356, 323, 263, 227, 211])))
              )
            )
            (.branch
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [254, 149]) (emptyTrie 0)))
                (.branch
                  (.branch (.leaf [427, 172]) (emptyTrie 0))
                  (.branch (.leaf [142]) (emptyTrie 0)))
              )
              (.branch
                (.branch (.branch (.leaf [618, 202]) (.leaf [573])) (emptyTrie 1))
                (emptyTrie 2))
            )
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [157, 106])))
                (.branch
                  (.branch (.leaf [291, 158, 59]) (emptyTrie 0))
                  (.branch (.leaf [67, 56]) (.leaf [50])))
              )
              (.branch
                (.branch
                  (.branch (.leaf [265, 229, 5]) (emptyTrie 0))
                  (.branch (emptyTrie 0) (.leaf [273, 150])))
                (.branch (.branch (emptyTrie 0) (.leaf [179])) (emptyTrie 1))
              )
            )
            (.branch
              (.branch
                (.branch (.branch (.leaf [62]) (emptyTrie 0)) (emptyTrie 1))
                (.branch
                  (.branch (.leaf [355, 193, 160, 144, 20]) (emptyTrie 0))
                  (.branch (emptyTrie 0) (.leaf [35])))
              )
              (.branch
                (.branch
                  (emptyTrie 1)
                  (.branch (.leaf [525, 486, 444, 349, 318, 256, 222, 206, 45]) (emptyTrie 0)))
                (emptyTrie 2)
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [113, 37]))
                  (.branch (.leaf [48]) (emptyTrie 0)))
                (.branch (.branch (.leaf [148, 77, 64]) (emptyTrie 0)) (emptyTrie 1))
              )
              (.branch
                (.branch (.branch (.leaf [418, 75]) (.leaf [391])) (emptyTrie 1))
                (emptyTrie 2))
            )
            (.branch
              (.branch
                (.branch
                  (.branch (.leaf [300]) (emptyTrie 0))
                  (.branch (.leaf [86, 73, 60]) (emptyTrie 0)))
                (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [42])))
              )
              (.branch
                (.branch (.branch (.leaf [600, 32]) (emptyTrie 0)) (emptyTrie 1))
                (.branch
                  (.branch
                    (.leaf [673,
                      665,
                      657,
                      649,
                      641,
                      633,
                      624,
                      615,
                      606,
                      597,
                      588,
                      579,
                      570,
                      433,
                      424,
                      415,
                      406,
                      397,
                      388,
                      314,
                      305,
                      296,
                      287])
                    (.leaf [528, 489, 447, 352, 321, 259, 225, 209])
                  )
                  (emptyTrie 1)
                )
              )
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (emptyTrie 3)
              (.branch
                (.branch
                  (.branch (emptyTrie 0) (.leaf [343, 87]))
                  (.branch (emptyTrie 0) (.leaf [535, 496, 456, 361, 328, 268, 232, 136])))
                (emptyTrie 2)
              )
            )
            (.branch
              (.branch
                (.branch
                  (emptyTrie 1)
                  (.branch (emptyTrie 0) (.leaf [543, 504, 464, 369, 336, 276, 216, 173, 153])))
                (.branch (.branch (emptyTrie 0) (.leaf [10])) (emptyTrie 1))
              )
              (.branch
                (.branch
                  (.branch (.leaf [18]) (emptyTrie 0))
                  (.branch (emptyTrie 0) (.leaf [116, 109])))
                (.branch
                  (.branch (.leaf [143]) (.leaf [522, 441, 346, 251, 94, 80, 57]))
                  (emptyTrie 1))
              )
            )
          )
          (.branch
            (.branch
              (.branch
                (emptyTrie 2)
                (.branch
                  (.branch (.leaf [159]) (.leaf [527, 488, 446, 351, 320, 258, 224, 208]))
                  (.branch
                    (emptyTrie 0)
                    (.leaf [669,
                      661,
                      653,
                      645,
                      637,
                      629,
                      620,
                      611,
                      602,
                      593,
                      584,
                      575,
                      566,
                      429,
                      420,
                      411,
                      402,
                      393,
                      384,
                      310,
                      301,
                      292,
                      283])
                  )
                )
              )
              (.branch
                (.branch (emptyTrie 1) (.branch (.leaf [518, 255, 221]) (emptyTrie 0)))
                (.branch (.branch (.leaf [188]) (.leaf [282])) (emptyTrie 1)))
            )
            (.branch
              (.branch
                (emptyTrie 2)
                (.branch (.branch (.leaf [246]) (.leaf [428, 164, 90, 82])) (emptyTrie 1)))
              (.branch
                (.branch (.branch (emptyTrie 0) (.leaf [134])) (emptyTrie 1))
                (emptyTrie 2))
            )
          )
        )
      )
    )
  )

def cliTable : CertTable := ⟨10, cliIdTree, cliHashTrie⟩

end Symbolic.Proofs.Tests.CliNonvacuity.Table.CliTable
