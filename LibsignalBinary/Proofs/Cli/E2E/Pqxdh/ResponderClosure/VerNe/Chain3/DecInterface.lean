/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs

/-!
# CLI Inlined `SessionStructure::decode` Arm Interface

Defines the loop-state register and spatial invariants (`overDecStackX`, `OverDecG`,
`overPrevElemRestExt`, `OverDecRegs`, `overDecHeapExt`), jump-table offsets (`overDecArmOff`), and
arm contract (`OverDecArmStmtTRExt`) for the inlined `SessionStructure::decode` loop in
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)

/-- Callee stack budget below closure frame `q` during inlined `SessionStructure::decode` (`64 KiB`). -/
abbrev overDecStackX : Nat := 65536

/-- Ghost bundle of the inlined `SessionStructure::decode` loop in `decryptPrekeyClosureName`. -/
structure OverDecG where
  q : BitVec 64
  r19 : BitVec 64
  r20 : BitVec 64
  r26 : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  encCap : BitVec 64
  encPtr : BitVec 64
  enc : List (BitVec 8)
  sv : State

/-- `overPrevElemAt` without `encPtr ↦ₛ enc` (lent to the slice cursor during the decode loop),
parameterized over `A : RustAlloc`. -/
def overPrevElemRestExt (A : RustAlloc) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) : SepProp :=
  ⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
    A.live prevPtr (prevCap.toNat * 24) 8 ∗
    (vecHeader prevPtr encCap encPtr (BitVec.ofNat 64 enc.length) ∗
      ⌜enc.length ≤ encCap.toNat ∧ encCap.toNat < 2 ^ 63 ∧ encPtr ≠ 0⌝ ∗
      (A.live encPtr encCap.toNat 1 ∗
        memRegion (encPtr + BitVec.ofNat 64 enc.length) (encCap.toNat - enc.length))) ∗
    memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24)

abbrev overPrevElemRest (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) :
    SepProp :=
  overPrevElemRestExt CryptoVerification.E2E.Record.A0 prevCap prevPtr encCap encPtr enc

/-- Register and machine-state invariant at `decryptPrekeyClosureName + off` inside the decode loop. -/
def OverDecRegs (img : Obj.Image) (ext : String → Option (State → State)) (s0 : State)
    (g : OverDecG) (off : BitVec 64) (s : State) : Prop :=
  s.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + off ∧
  s.status = .Running ∧ s.sp = g.q ∧ (s.sp &&& 15#64 == 0#64) = true ∧ s.trace = s0.trace ∧
  img.FrozenLoaded s ∧ s.symtab = img.symtab ∧
  s.readReg64 .x19 = g.r19 ∧ s.readReg64 .x20 = g.r20 ∧ s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧ s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧ s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

/-- Spatial invariant of the decode loop at undecoded suffix `rest` and partial `SSGQ` value `v`,
parameterized over `A : RustAlloc`. -/
def overDecHeapExt (A : RustAlloc) (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr
      g.enc rest ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool

abbrev overDecHeap (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  overDecHeapExt CryptoVerification.E2E.Record.A0 g rest v

/-- Tag 6 (`sender_chain`, `merge<Chain> [local#5]` in place into `Option<Chain>`). -/
def OverDecSenderField : GenFieldQ → Prop
  | .base (.sender _) => True
  | _ => False

/-- Jump-table target (closure offset) of a field's tag in `decryptPrekeyClosureName`. -/
def overDecArmOff : GenFieldQ → BitVec 64
  | .base (.version _) => 0x21bc#64
  | .base (.lik _) => 0x22cc#64
  | .base (.rik _) => 0x22b8#64
  | .base (.root _) => 0x2290#64
  | .base (.prevCounter _) => 0x21e8#64
  | .base (.sender _) => 0x2214#64
  | .base (.recv _) => 0x22e0#64
  | .base (.pending _) | .pendingId _ _ | .pendingSpk _ _ _ => 0x2350#64
  | .remReg _ => 0x23a8#64
  | .locReg _ => 0x2390#64
  | .abk _ => 0x21d4#64
  | .kyber _ _ => 0x2258#64
  | .pq _ => 0x2200#64

/-- Wire type held in `x0` on entry to a field arm (`0` varint, `2` length-delimited). -/
def overDecWt (fl : GenFieldQ) : BitVec 64 :=
  if fl.wt = .varint then 0#64 else 2#64

/-- Arm contract (`overDecArmOff fl → +0x2160`) under `LibsignalTripleRatchet.AllocContractsX`
for the CLI handshake closure (`decryptPrekeyClosureName`), parameterized over `A : RustAlloc`. -/
def OverDecArmStmtTRExt (A : RustAlloc) (P : GenFieldQ → Prop) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegs img ext s0 g (overDecArmOff fl) s →
    s.readReg64 .x0 = overDecWt fl →
    s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply fl)))
      (PanicOomProp s0)

abbrev OverDecArmStmtTR (P : GenFieldQ → Prop) : Prop :=
  OverDecArmStmtTRExt CryptoVerification.E2E.Record.A0 P

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
