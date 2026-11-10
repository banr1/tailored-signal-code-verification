/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced

/-!
# Placed Prebuild and Hook Agreement Specifications

Defines `PrebuildSpecPlaced`, the postcondition of `prebuildElfPlaced`, and `HooksAgreePlaced`,
which relates the depth-62 hook radix tree to `(cliProgPlacedSig mpl mmpl W).externAt?`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced

open Arm64 Arm64.Obj Arm64.Process
open CryptoVerification.SignalSession (CliHooks cliExternsPlacedSig)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree btGet rawCellAt)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (PrebuiltElfPlaced overlayHooksPlaced
  progPlacedDepth)

set_option linter.dupNamespace false in
/-- Postcondition of `prebuildElfPlaced`: ELF well-formedness, segment and token-patch bounds below
`elf.brkStart`, cellwise agreement of `pb.baseLines` with token-patched segment memory, and `pb.prog`
structure. -/
structure PrebuildSpecPlaced (W : CliHooks) (elf : ElfImage) (tokS tokO : BitVec 64)
    (addrs : MallocngCallAddrs) (stubs : List (String × Nat)) (pb : PrebuiltElfPlaced) : Prop where
  wellFormed : elf.WellFormed = true
  seg_le_brk : ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ elf.brkStart.toNat
  brk_le     : elf.brkStart.toNat ≤ 2 ^ 48
  tokS_le    : tokS.toNat + 1 ≤ elf.brkStart.toNat
  tokO_le    : tokO.toNat + 12 ≤ elf.brkStart.toNat
  cells      : ∀ a : BitVec 64, rawCellAt pb.baseLines a.toNat =
                 (((⟨Snapshot.loadCellAt elf.segments⟩ : Memory).writeBytes tokS [0#8]).writeBytes
                    (tokO + 8#64) [0#8, 0#8, 0#8, 0#8]).cells a
  prog_eq    : pb.prog = { addrs := addrs, hooks := overlayHooksPlaced W stubs .empty,
                           rxLines := pb.baseLines }

/-- Agreement between the word-indexed hook tree `t` and `(cliProgPlacedSig mpl mmpl W).externAt?`
at every 4-byte-aligned `pc`. -/
def HooksAgreePlaced (mpl mmpl : MultiPlacement) (W : CliHooks) (t : BinTree String) : Prop :=
  ∀ pc : BitVec 64, pc.toNat % 4 = 0 →
    match btGet progPlacedDepth t (pc.toNat / 4) with
    | some name => ∀ h, cliExternsPlacedSig mmpl W name = some h →
        (cliProgPlacedSig mpl mmpl W).externAt? pc = some h
    | none => (cliProgPlacedSig mpl mmpl W).externAt? pc = none

end Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced
