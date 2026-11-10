/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Proofs.CliExec.ElfRunPlacedSound
public import Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseFull
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Files
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q2L
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q2R
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C5
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C6
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C7
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C8
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q2L
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q2R
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C10
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C11
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C12
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C13
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C14
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C15
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C16
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q3L
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q3R
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C18
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C19
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C20
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C21
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C22
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C23
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C24
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C25
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C26
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C27
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C28
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C29
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C30
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C31
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C32
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C33
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C34
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C35
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C36
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C37
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C38
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C39
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C40
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C41
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C42
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C43
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C45
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C46
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C47
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C48
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C49
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C50
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C51
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C52
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C53
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C54
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C55
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C56
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C57
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C58
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C59
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C60
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C61
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C63
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C64
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C65
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C66
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C67
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C68
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C69
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C70
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C71
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s4

/-! Chained `131`-chunk `cliRunPlacedSig` proof (`wsRun2`) for `Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2`. -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession (cliExternsPlacedSig)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq (compHooks0_placed_eq)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfCkptReachablePlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfRunPlacedSound (cliRunPlacedSig_of_elfFinalChunk)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (wsInp2 wsOut2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseFull (wsSpec)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Files (wsFiles1 wsFiles2 wsInp2_eq c2Out_eq)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C0 (c0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C1 (c1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C2 (c2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C3 (c3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q0 (c4q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q1 (c4q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q0 (c4q2q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q0 (c4q2q1q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q1 (c4q2q1q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q0 (c4q2q1q2q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q1 (c4q2q1q2q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q2 (c4q2q1q2q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q0 (c4q2q1q2q3q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q1 (c4q2q1q2q3q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q2L (c4q2q1q2q3q2L)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q2R (c4q2q1q2q3q2R)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q2q3q3 (c4q2q1q2q3q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q1q3 (c4q2q1q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q2 (c4q2q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q2q3 (c4q2q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C4q3 (c4q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C5 (c5)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C6 (c6)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C7 (c7)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C8 (c8)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q0 (c9q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q1 (c9q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q2 (c9q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q0 (c9q3q0q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q1 (c9q3q0q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q2 (c9q3q0q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q0 (c9q3q0q3q0q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q1 (c9q3q0q3q0q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q2L (c9q3q0q3q0q2L)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q2R (c9q3q0q3q0q2R)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q0q3 (c9q3q0q3q0q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q1 (c9q3q0q3q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q2 (c9q3q0q3q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q0q3q3 (c9q3q0q3q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q1 (c9q3q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q2 (c9q3q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C9q3q3 (c9q3q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C10 (c10)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C11 (c11)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C12 (c12)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C13 (c13)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C14 (c14)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C15 (c15)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C16 (c16)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q0 (c17q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q1 (c17q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q2 (c17q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q0 (c17q3q0q0q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q0 (c17q3q0q0q1q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q1 (c17q3q0q0q1q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q2 (c17q3q0q0q1q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q3L (c17q3q0q0q1q3L)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q1q3R (c17q3q0q0q1q3R)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q2 (c17q3q0q0q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q0q3 (c17q3q0q0q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q1 (c17q3q0q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q2 (c17q3q0q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q0q3 (c17q3q0q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q1 (c17q3q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q2 (c17q3q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C17q3q3 (c17q3q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C18 (c18)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C19 (c19)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C20 (c20)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C21 (c21)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C22 (c22)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C23 (c23)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C24 (c24)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C25 (c25)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C26 (c26)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C27 (c27)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C28 (c28)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C29 (c29)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C30 (c30)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C31 (c31)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C32 (c32)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C33 (c33)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C34 (c34)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C35 (c35)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C36 (c36)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C37 (c37)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C38 (c38)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C39 (c39)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C40 (c40)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C41 (c41)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C42 (c42)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C43 (c43)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q0 (c44q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q1 (c44q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q2 (c44q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C44q3 (c44q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C45 (c45)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C46 (c46)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C47 (c47)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C48 (c48)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C49 (c49)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C50 (c50)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C51 (c51)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C52 (c52)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C53 (c53)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C54 (c54)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C55 (c55)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C56 (c56)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C57 (c57)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C58 (c58)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C59 (c59)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C60 (c60)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C61 (c61)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q0 (c62q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q1 (c62q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q2 (c62q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C62q3 (c62q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C63 (c63)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C64 (c64)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C65 (c65)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C66 (c66)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C67 (c67)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C68 (c68)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C69 (c69)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C70 (c70)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C71 (c71)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s0 (c72s0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s1 (c72s1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s2 (c72s2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s3 (c72s3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2.C72s4 (c72s4)

theorem wsRun2 {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv : ElfFullValidPlaced mpl mmpl elf wsSpec) :
    cliRunPlacedSig mpl mmpl elf compHooks0 (wsInp2 wsFiles1) =
      some (wsOut2 wsFiles2) :=
  cliRunPlacedSig_of_elfFinalChunk hv
    (fun name => congrArg (cliExternsPlacedSig mmpl · name) compHooks0_placed_eq)
    wsInp2_eq c2Out_eq
    ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((ElfCkptReachablePlaced.init.step c0).step c1).step c2).step c3).step c4q0).step c4q1).step c4q2q0).step c4q2q1q0).step c4q2q1q1).step c4q2q1q2q0).step c4q2q1q2q1).step c4q2q1q2q2).step c4q2q1q2q3q0).step c4q2q1q2q3q1).step c4q2q1q2q3q2L).step c4q2q1q2q3q2R).step c4q2q1q2q3q3).step c4q2q1q3).step c4q2q2).step c4q2q3).step c4q3).step c5).step c6).step c7).step c8).step c9q0).step c9q1).step c9q2).step c9q3q0q0).step c9q3q0q1).step c9q3q0q2).step c9q3q0q3q0q0).step c9q3q0q3q0q1).step c9q3q0q3q0q2L).step c9q3q0q3q0q2R).step c9q3q0q3q0q3).step c9q3q0q3q1).step c9q3q0q3q2).step c9q3q0q3q3).step c9q3q1).step c9q3q2).step c9q3q3).step c10).step c11).step c12).step c13).step c14).step c15).step c16).step c17q0).step c17q1).step c17q2).step c17q3q0q0q0).step c17q3q0q0q1q0).step c17q3q0q0q1q1).step c17q3q0q0q1q2).step c17q3q0q0q1q3L).step c17q3q0q0q1q3R).step c17q3q0q0q2).step c17q3q0q0q3).step c17q3q0q1).step c17q3q0q2).step c17q3q0q3).step c17q3q1).step c17q3q2).step c17q3q3).step c18).step c19).step c20).step c21).step c22).step c23).step c24).step c25).step c26).step c27).step c28).step c29).step c30).step c31).step c32).step c33).step c34).step c35).step c36).step c37).step c38).step c39).step c40).step c41).step c42).step c43).step c44q0).step c44q1).step c44q2).step c44q3).step c45).step c46).step c47).step c48).step c49).step c50).step c51).step c52).step c53).step c54).step c55).step c56).step c57).step c58).step c59).step c60).step c61).step c62q0).step c62q1).step c62q2).step c62q3).step c63).step c64).step c65).step c66).step c67).step c68).step c69).step c70).step c71).step c72s0).step c72s1).step c72s2).step c72s3) c72s4

end Symbolic.BugInjection.Disproofs.Impl.WeakState.Call2
