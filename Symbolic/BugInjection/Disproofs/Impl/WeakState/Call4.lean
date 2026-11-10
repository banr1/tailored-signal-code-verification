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
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C4
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q3L
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q3R
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C6
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C7
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C8
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C9
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C10
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q1L
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q1R
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C12
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C13
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q0L
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q0R
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C15
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C16
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C17
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C18
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C19
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C20
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C21
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C22
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C23
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C24
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C25
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C26
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C27
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C28
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C29
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C30
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C31
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C32
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C33
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C34
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C35
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C36
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C37
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C38
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C39
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C40
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C41
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C42
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C43
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C44
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C45
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C46
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C47
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C48
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C49
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C50
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C51
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C52
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q0
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q1
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q2
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q3
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C54

/-! Chained `106`-chunk `cliRunPlacedSig` proof (`wsRun4`) for `Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4`. -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification.SignalSession (cliExternsPlacedSig)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.Common.CompHooks0PlacedEq (compHooks0_placed_eq)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfCkptReachablePlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfRunPlacedSound (cliRunPlacedSig_of_elfFinalChunk)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (wsInp4 wsOut4)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.BaseFull (wsSpec)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Files (wsFiles2 wsFiles4 wsInp4_eq)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C0 (c0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C1 (c1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C2 (c2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C3 (c3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C4 (c4)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q0 (c5q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q0 (c5q1q0q0q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q0 (c5q1q0q0q1q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q1 (c5q1q0q0q1q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q2 (c5q1q0q0q1q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q3L (c5q1q0q0q1q3L)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q1q3R (c5q1q0q0q1q3R)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q2 (c5q1q0q0q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q0q3 (c5q1q0q0q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q1 (c5q1q0q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q2 (c5q1q0q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q0q3 (c5q1q0q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q1 (c5q1q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q2 (c5q1q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q1q3 (c5q1q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q2 (c5q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C5q3 (c5q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C6 (c6)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C7 (c7)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C8 (c8)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C9 (c9)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C10 (c10)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q0 (c11q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q1 (c11q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q0 (c11q2q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q1 (c11q2q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q2 (c11q2q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q0 (c11q2q3q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q0 (c11q2q3q1q0q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q1L (c11q2q3q1q0q1L)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q1R (c11q2q3q1q0q1R)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q2 (c11q2q3q1q0q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q0q3 (c11q2q3q1q0q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q1 (c11q2q3q1q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q2 (c11q2q3q1q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q1q3 (c11q2q3q1q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q2 (c11q2q3q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q2q3q3 (c11q2q3q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C11q3 (c11q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C12 (c12)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C13 (c13)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q0 (c14q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q1 (c14q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q0 (c14q2q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q1 (c14q2q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q0 (c14q2q2q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q0 (c14q2q2q1q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q1 (c14q2q2q1q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q2 (c14q2q2q1q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q0L (c14q2q2q1q3q0L)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q0R (c14q2q2q1q3q0R)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q1 (c14q2q2q1q3q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q2 (c14q2q2q1q3q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q1q3q3 (c14q2q2q1q3q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q2 (c14q2q2q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q2q3 (c14q2q2q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q2q3 (c14q2q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C14q3 (c14q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C15 (c15)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C16 (c16)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C17 (c17)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C18 (c18)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C19 (c19)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C20 (c20)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C21 (c21)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C22 (c22)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C23 (c23)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C24 (c24)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C25 (c25)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C26 (c26)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C27 (c27)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C28 (c28)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C29 (c29)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C30 (c30)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C31 (c31)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C32 (c32)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C33 (c33)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C34 (c34)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C35 (c35)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C36 (c36)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C37 (c37)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C38 (c38)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C39 (c39)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C40 (c40)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C41 (c41)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C42 (c42)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C43 (c43)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C44 (c44)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C45 (c45)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C46 (c46)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C47 (c47)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C48 (c48)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C49 (c49)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C50 (c50)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C51 (c51)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C52 (c52)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q0 (c53q0)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q1 (c53q1)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q2 (c53q2)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C53q3 (c53q3)
open Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4.C54 (c54)

theorem wsRun4 {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv : ElfFullValidPlaced mpl mmpl elf wsSpec) :
    cliRunPlacedSig mpl mmpl elf compHooks0 (wsInp4 wsFiles2) =
      some (wsOut4 wsFiles4) :=
  cliRunPlacedSig_of_elfFinalChunk hv
    (fun name => congrArg (cliExternsPlacedSig mmpl · name) compHooks0_placed_eq)
    wsInp4_eq rfl
    (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((ElfCkptReachablePlaced.init.step c0).step c1).step c2).step c3).step c4).step c5q0).step c5q1q0q0q0).step c5q1q0q0q1q0).step c5q1q0q0q1q1).step c5q1q0q0q1q2).step c5q1q0q0q1q3L).step c5q1q0q0q1q3R).step c5q1q0q0q2).step c5q1q0q0q3).step c5q1q0q1).step c5q1q0q2).step c5q1q0q3).step c5q1q1).step c5q1q2).step c5q1q3).step c5q2).step c5q3).step c6).step c7).step c8).step c9).step c10).step c11q0).step c11q1).step c11q2q0).step c11q2q1).step c11q2q2).step c11q2q3q0).step c11q2q3q1q0q0).step c11q2q3q1q0q1L).step c11q2q3q1q0q1R).step c11q2q3q1q0q2).step c11q2q3q1q0q3).step c11q2q3q1q1).step c11q2q3q1q2).step c11q2q3q1q3).step c11q2q3q2).step c11q2q3q3).step c11q3).step c12).step c13).step c14q0).step c14q1).step c14q2q0).step c14q2q1).step c14q2q2q0).step c14q2q2q1q0).step c14q2q2q1q1).step c14q2q2q1q2).step c14q2q2q1q3q0L).step c14q2q2q1q3q0R).step c14q2q2q1q3q1).step c14q2q2q1q3q2).step c14q2q2q1q3q3).step c14q2q2q2).step c14q2q2q3).step c14q2q3).step c14q3).step c15).step c16).step c17).step c18).step c19).step c20).step c21).step c22).step c23).step c24).step c25).step c26).step c27).step c28).step c29).step c30).step c31).step c32).step c33).step c34).step c35).step c36).step c37).step c38).step c39).step c40).step c41).step c42).step c43).step c44).step c45).step c46).step c47).step c48).step c49).step c50).step c51).step c52).step c53q0).step c53q1).step c53q2).step c53q3) c54

end Symbolic.BugInjection.Disproofs.Impl.WeakState.Call4
