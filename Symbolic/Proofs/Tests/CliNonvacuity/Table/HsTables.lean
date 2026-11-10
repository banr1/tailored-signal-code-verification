/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsFalseNodes
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTrueNodes

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables

open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (Trie emptyTrie)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (CertTable)

def hsFalseHashTrie : Trie Nat :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [121, 102, 20]))
                (.branch (.leaf [64]) (emptyTrie 0)))
              (.branch (emptyTrie 1) (.branch (.leaf [86]) (emptyTrie 0)))
            )
            (.branch
              (.branch
                (.branch (.leaf [47, 40, 30]) (.leaf [10]))
                (.branch (.leaf [126, 68]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [67, 52]) (emptyTrie 0))
                (.branch (emptyTrie 0) (.leaf [82])))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf [120, 113, 109, 106, 99, 98, 97]) (.leaf [45]))
                (emptyTrie 1))
              (.branch
                (.branch (.leaf [2]) (.leaf [66]))
                (.branch (.leaf [79, 71]) (emptyTrie 0)))
            )
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [65, 6]))
                (.branch (emptyTrie 0) (.leaf [95])))
              (.branch (.branch (emptyTrie 0) (.leaf [12])) (emptyTrie 1))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [31]))
                (.branch (.leaf [54]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [28]) (emptyTrie 0))
                (.branch (.leaf [22]) (emptyTrie 0)))
            )
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [9]) (emptyTrie 0)))
              (.branch
                (.branch (emptyTrie 0) (.leaf [42, 24]))
                (.branch (.leaf [36]) (.leaf [57])))
            )
          )
          (.branch
            (.branch
              (.branch (.branch (.leaf [53]) (.leaf [115])) (emptyTrie 1))
              (emptyTrie 2))
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [5]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [26]) (emptyTrie 0))
                (.branch (.leaf [39]) (.leaf [60])))
            )
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [16]) (emptyTrie 0)))
              (emptyTrie 2))
            (.branch
              (.branch
                (.branch (.leaf [46]) (.leaf [58]))
                (.branch (.leaf [128, 78, 72]) (emptyTrie 0)))
              (.branch
                (.branch (emptyTrie 0) (.leaf [35]))
                (.branch (.leaf [1]) (emptyTrie 0)))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [37]))
                (.branch (emptyTrie 0) (.leaf [8])))
              (emptyTrie 2)
            )
            (.branch
              (emptyTrie 2)
              (.branch (.branch (.leaf [118, 117, 111, 104, 14]) (emptyTrie 0)) (emptyTrie 1)))
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch (.branch (emptyTrie 0) (.leaf [50])) (emptyTrie 1))
              (.branch (emptyTrie 1) (.branch (.leaf [108]) (.leaf [33]))))
            (.branch
              (emptyTrie 2)
              (.branch (emptyTrie 1) (.branch (.leaf [56]) (emptyTrie 0))))
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf [62]) (emptyTrie 0))
                (.branch (.leaf [3]) (emptyTrie 0)))
              (.branch (.branch (.leaf [116]) (.leaf [114])) (emptyTrie 1))
            )
            (.branch
              (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [101])))
              (.branch
                (.branch (.leaf [87, 59]) (emptyTrie 0))
                (.branch (.leaf [91, 29, 18]) (emptyTrie 0)))
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
              (emptyTrie 2)
              (.branch (emptyTrie 1) (.branch (.leaf [84]) (emptyTrie 0))))
            (.branch
              (.branch
                (.branch (.leaf [83, 44]) (emptyTrie 0))
                (.branch (.leaf [48]) (emptyTrie 0)))
              (.branch
                (.branch (emptyTrie 0) (.leaf [27, 19]))
                (.branch (emptyTrie 0) (.leaf [123])))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [34]))
                (.branch (.leaf [80]) (emptyTrie 0)))
              (emptyTrie 2)
            )
            (.branch
              (.branch
                (.branch (.leaf [93, 77]) (emptyTrie 0))
                (.branch (emptyTrie 0) (.leaf [92])))
              (.branch (.branch (.leaf [13]) (emptyTrie 0)) (emptyTrie 1))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch (.branch (.leaf [85]) (.leaf [119, 112, 105, 96])) (emptyTrie 1))
              (.branch (emptyTrie 1) (.branch (.leaf [21]) (emptyTrie 0))))
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [94]) (emptyTrie 0)))
              (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [81]))))
          )
          (.branch
            (.branch
              (.branch (.branch (emptyTrie 0) (.leaf [4])) (emptyTrie 1))
              (.branch
                (.branch (.leaf [32, 0]) (emptyTrie 0))
                (.branch (.leaf [73]) (.leaf [127])))
            )
            (.branch
              (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [70])))
              (.branch (.branch (.leaf [11]) (emptyTrie 0)) (emptyTrie 1)))
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [100]))
                (.branch (.leaf [17]) (.leaf [88, 43])))
              (.branch (.branch (.leaf [23]) (emptyTrie 0)) (emptyTrie 1))
            )
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [76, 7]) (.leaf [49])))
              (.branch (.branch (emptyTrie 0) (.leaf [122, 38])) (emptyTrie 1)))
          )
          (.branch
            (.branch
              (.branch (.branch (.leaf [107, 51]) (.leaf [41])) (emptyTrie 1))
              (emptyTrie 2))
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [90, 69]))
                (.branch (emptyTrie 0) (.leaf [55])))
              (.branch
                (.branch (.leaf [15]) (emptyTrie 0))
                (.branch (.leaf [125]) (emptyTrie 0)))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (emptyTrie 2)
              (.branch (.branch (emptyTrie 0) (.leaf [63])) (emptyTrie 1)))
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [74]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [25]) (.leaf [110, 103]))
                (.branch (.leaf [89, 75]) (emptyTrie 0)))
            )
          )
          (.branch
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [124]) (emptyTrie 0)))
              (emptyTrie 2))
            (.branch
              (emptyTrie 2)
              (.branch (.branch (.leaf [61]) (emptyTrie 0)) (emptyTrie 1)))
          )
        )
      )
    )
  )

def hsFalseTable : CertTable := ⟨8, HsFalseNodes.hsFalseIdTree, hsFalseHashTrie⟩

def hsTrueHashTrie : Trie Nat :=
  (.branch
    (.branch
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [132, 106]))
                (.branch (.leaf [68]) (emptyTrie 0)))
              (.branch (emptyTrie 1) (.branch (.leaf [90]) (emptyTrie 0)))
            )
            (.branch
              (.branch
                (.branch (.leaf [51, 44]) (.leaf [10]))
                (.branch (.leaf [137, 72]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [56]) (emptyTrie 0))
                (.branch (emptyTrie 0) (.leaf [86])))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf [131, 124, 117, 113, 110, 103, 102, 101]) (.leaf [49]))
                (emptyTrie 1))
              (.branch (.branch (.leaf [2]) (.leaf [70])) (.branch (.leaf [75]) (emptyTrie 0)))
            )
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [69, 6]))
                (.branch (emptyTrie 0) (.leaf [99])))
              (.branch (.branch (emptyTrie 0) (.leaf [12])) (emptyTrie 1))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [35, 22]))
                (.branch (.leaf [58]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [33]) (emptyTrie 0))
                (.branch (.leaf [24]) (emptyTrie 0)))
            )
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [9]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [71]) (.leaf [46, 26]))
                (.branch (.leaf [40]) (.leaf [61])))
            )
          )
          (.branch
            (.branch
              (.branch (.branch (.leaf [57]) (.leaf [119])) (emptyTrie 1))
              (emptyTrie 2))
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [5]) (emptyTrie 0)))
              (.branch (emptyTrie 1) (.branch (.leaf [43]) (.leaf [64]))))
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch (.branch (emptyTrie 0) (.leaf [20])) (emptyTrie 1))
              (emptyTrie 2))
            (.branch
              (.branch
                (.branch (.leaf [50]) (.leaf [62]))
                (.branch (.leaf [139, 82, 76]) (emptyTrie 0)))
              (.branch
                (.branch (emptyTrie 0) (.leaf [39]))
                (.branch (.leaf [29, 1]) (.leaf [74])))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [41]))
                (.branch (emptyTrie 0) (.leaf [8])))
              (emptyTrie 2)
            )
            (.branch
              (emptyTrie 2)
              (.branch
                (.branch (.leaf [129, 128, 122, 121, 115, 108]) (emptyTrie 0))
                (emptyTrie 1))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [54]))
                (.branch (.leaf [18]) (emptyTrie 0)))
              (.branch (emptyTrie 1) (.branch (.leaf [112, 28]) (.leaf [37])))
            )
            (.branch
              (emptyTrie 2)
              (.branch (emptyTrie 1) (.branch (.leaf [60]) (emptyTrie 0))))
          )
          (.branch
            (.branch
              (.branch
                (.branch (.leaf [66]) (emptyTrie 0))
                (.branch (.leaf [3]) (emptyTrie 0)))
              (.branch (.branch (.leaf [120]) (.leaf [118])) (emptyTrie 1))
            )
            (.branch
              (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [105])))
              (.branch
                (.branch (.leaf [91, 63, 16]) (emptyTrie 0))
                (.branch (.leaf [95, 14]) (emptyTrie 0)))
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
              (.branch (.branch (.leaf [34]) (emptyTrie 0)) (emptyTrie 1))
              (.branch (emptyTrie 1) (.branch (.leaf [27]) (emptyTrie 0))))
            (.branch
              (.branch (.branch (.leaf [87, 48]) (emptyTrie 0)) (emptyTrie 1))
              (.branch (emptyTrie 1) (.branch (emptyTrie 0) (.leaf [134]))))
          )
          (.branch
            (.branch
              (.branch (.branch (emptyTrie 0) (.leaf [38])) (emptyTrie 1))
              (emptyTrie 2))
            (.branch
              (.branch
                (.branch (.leaf [97, 81]) (emptyTrie 0))
                (.branch (emptyTrie 0) (.leaf [96])))
              (.branch (.branch (.leaf [13]) (emptyTrie 0)) (emptyTrie 1))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch (.branch (.leaf [89]) (.leaf [130, 123, 116, 109, 100])) (emptyTrie 1))
              (.branch (emptyTrie 1) (.branch (.leaf [23]) (emptyTrie 0))))
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [98]) (emptyTrie 0)))
              (.branch
                (.branch (emptyTrie 0) (.leaf [30, 21]))
                (.branch (emptyTrie 0) (.leaf [126, 85])))
            )
          )
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [31, 4]))
                (.branch (.leaf [84]) (emptyTrie 0)))
              (.branch
                (.branch (.leaf [36, 0]) (emptyTrie 0))
                (.branch (.leaf [77]) (.leaf [138])))
            )
            (.branch
              (.branch (.branch (emptyTrie 0) (.leaf [83])) (emptyTrie 1))
              (.branch
                (.branch (.leaf [15, 11]) (emptyTrie 0))
                (.branch (emptyTrie 0) (.leaf [53])))
            )
          )
        )
      )
      (.branch
        (.branch
          (.branch
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [104]))
                (.branch (emptyTrie 0) (.leaf [92, 47])))
              (.branch (.branch (.leaf [25]) (.leaf [32])) (emptyTrie 1))
            )
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [80, 7]) (emptyTrie 0)))
              (.branch (.branch (emptyTrie 0) (.leaf [133, 42])) (emptyTrie 1)))
          )
          (.branch
            (.branch
              (.branch (.branch (.leaf [111, 55]) (.leaf [88, 45])) (emptyTrie 1))
              (emptyTrie 2))
            (.branch
              (.branch
                (.branch (emptyTrie 0) (.leaf [79]))
                (.branch (emptyTrie 0) (.leaf [59])))
              (.branch (emptyTrie 1) (.branch (.leaf [136, 52]) (emptyTrie 0)))
            )
          )
        )
        (.branch
          (.branch
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [19]) (emptyTrie 0)))
              (.branch (.branch (emptyTrie 0) (.leaf [67])) (emptyTrie 1)))
            (.branch
              (.branch
                (.branch (.leaf [125]) (.leaf [127]))
                (.branch (.leaf [78]) (emptyTrie 0)))
              (.branch
                (.branch (emptyTrie 0) (.leaf [114, 107]))
                (.branch (.leaf [93]) (emptyTrie 0)))
            )
          )
          (.branch
            (.branch
              (.branch (emptyTrie 1) (.branch (.leaf [135]) (emptyTrie 0)))
              (emptyTrie 2))
            (.branch
              (.branch (.branch (emptyTrie 0) (.leaf [94, 73])) (emptyTrie 1))
              (.branch (.branch (.leaf [65, 17]) (emptyTrie 0)) (emptyTrie 1)))
          )
        )
      )
    )
  )

def hsTrueTable : CertTable := ⟨8, HsTrueNodes.hsTrueIdTree, hsTrueHashTrie⟩

def hsTable (withOpk : Bool) : CertTable :=
  if withOpk then hsTrueTable else hsFalseTable

end Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables
