/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterface
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Inlined `SessionStructure::decode` Loop-Body Interface

`[LibsignalPlacement]` Block-`518` register invariant (`OverDecRegsPlaced`) and arm contract
(`OverDecArmPlacedStmt`) corresponding to `VerNe.Chain3.DecInterface`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG prostChainGAt GenField SSG)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalPlacement
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Placed register invariant at offset `off` inside `decryptPrekeyClosureName` (Block `518`). -/
def OverDecRegsPlaced [LibsignalPlacement]
    (_ext : String → Option (State → State)) (s0 : State) (g : OverDecG)
    (off : BitVec 64) (s : State) : Prop :=
  s.pc = (blkPl_518).base + off ∧
  s.status = .Running ∧
  s.sp = g.q ∧
  (s.sp &&& 15#64 == 0#64) = true ∧
  s.trace = s0.trace ∧
  LibsignalCodeLoaded lsmpl s.mem ∧
  s.readReg64 .x19 = g.r19 ∧
  s.readReg64 .x20 = g.r20 ∧
  s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧
  s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧
  s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧
  s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

/-- Placed arm contract (`overDecArmOff fl → +0x2160`) for fields satisfying
`P : GenFieldQ → Prop`. -/
def OverDecArmPlacedStmt [LibsignalPlacement] (P : GenFieldQ → Prop) : Prop :=
  ∀ (ext : String → Option (State → State)),
  ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc →
    g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g (overDecArmOff fl) s →
    s.readReg64 .x0 = overDecWt fl →
    s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
    SepWPp (lsProg_518 (Rust.withPanics ext))
        ((blkPl_518).base + 0x2160#64) s
      (overDecHeap g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply fl)))
      (PanicOomProp s0)

abbrev OverDecArmPlacedStmtTR [LibsignalPlacement] (P : GenFieldQ → Prop) : Prop :=
  OverDecArmPlacedStmt P

theorem OverDecArmPlacedStmt.toTR [LibsignalPlacement] {P : GenFieldQ → Prop}
    (h : OverDecArmPlacedStmt P) : OverDecArmPlacedStmtTR P := h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
