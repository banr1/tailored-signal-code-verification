/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.PrevEncOK
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs

/-!
# Inlined `SessionStructure::decode` Loop Definitions

Loop-state invariants (`OverDecG`, `OverDecRegs`, `overDecHeap`), field-group predicates, and
per-step contracts (`OverPrevDecodeStmt`, `OverDecEntryStmt`, `OverDecHeadConsStmt`,
`OverDecHeadNilStmt`, `OverDecKeyStmt`, `OverDecArmStmtTR`) for the inlined
`SessionStructure::decode` range (`+0x1ee8..+0x2620`) in `message_decrypt_prekey::<Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)

/-- Callee stack budget below closure frame `q` during inlined `SessionStructure::decode` (`64 KiB`). -/
abbrev overDecStackX : Nat := 65536

/-- The archived element of `previous_sessions` at `prevPtr` (`{encCap, encPtr, enc.length}`), its
buffer's allocation token and bytes, and the spare `(prevCap - 1) · 24` bytes with the outer token
(parameterized over `A : RustAlloc`). -/
def overPrevElemAtExt (A : RustAlloc) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) : SepProp :=
  ⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
    A.live prevPtr (prevCap.toNat * 24) 8 ∗
    vecU8At A prevPtr encCap encPtr enc ∗
    memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24)

abbrev overPrevElemAt (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) :
    SepProp :=
  overPrevElemAtExt CryptoVerification.E2E.Record.A0 prevCap prevPtr encCap encPtr enc

/-- Closure scratch owned by the decode before `+0x1ee8` (closure frame `q`). -/
def overDecScratchPre (q : BitVec 64) : SepProp :=
  memRegion (q + 0x920#64) 112 ∗ memRegion (q + 0x990#64) 256 ∗
    memRegion (q + 0xa90#64) 344 ∗ memRegion (q + 0xbe8#64) 136

/-- Closure scratch after the decode at `+0x2620` (closure frame `q`, decoded value `v`,
allocator `A : RustAlloc`). -/
def overDecScratchPostExt (A : RustAlloc) (q : BitVec 64) (v : SSGQ) : SepProp :=
  memRegion (q + 0x920#64) 16 ∗ prostSSGQAt A (q + 0x930#64) v ∗
    memRegion (q + 0xa88#64) 8 ∗ memRegion (q + 0xa90#64) 344 ∗ memRegion (q + 0xbe8#64) 136

abbrev overDecScratchPost (q : BitVec 64) (v : SSGQ) : SepProp :=
  overDecScratchPostExt CryptoVerification.E2E.Record.A0 q v

/-- Inlined `SessionStructure::decode` of `enc` (`+0x1ee8 → +0x2620`, closure frame `s.sp`) in
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`, parameterized over
`A : RustAlloc`. -/
def OverPrevDecodeStmtExt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
    ∀ (s0 s : State) (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8))
      (sess : Session (List (BitVec 8))),
    OverPrevEncOKAt enc sess →
    img.FrozenLoaded s → s.symtab = img.symtab →
    s.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x1ee8#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x21 = s.sp + 0x930#64 →
    s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 →
    s.readReg64 .x27 = prevPtr →
    s.readReg64 .x29 = s.sp + 0xc70#64 →
    SepWPp (contractProg img.base ext) ((contractProg img.base ext).fnAddr
        decryptPrekeyClosureName + 0x2620#64) s
      (overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ∗ overDecScratchPre s.sp ∗
        stackAt s.sp overDecStackX ∗
        A.pool)
      (fun sf P_f =>
        (P_f ⊢ overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ∗
            overDecScratchPostExt A s.sp (ssgqOf sess) ∗
            stackAt s.sp overDecStackX ∗
            A.pool ∗ anyHeap) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0)

abbrev OverPrevDecodeStmt : Prop :=
  OverPrevDecodeStmtExt CryptoVerification.E2E.Record.A0

/-! ## Loop State -/

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

/-- `overPrevElemAtExt A` without `encPtr ↦ₛ enc` (lent to the slice cursor during the decode loop). -/
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

/-- Spatial invariant of the decode loop at undecoded suffix `rest` and partial `SSGQ` value `v`
(allocator `A : RustAlloc`). -/
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

/-! ## Step Statements -/

/-- Entry (`+0x1ee8 → +0x216c`) parameterized over `A : RustAlloc`. -/
def OverDecEntryStmtExt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    Proofs.libsignal.Stage1X.AllocContractsX img A ext →
    ∀ (s0 s : State) (g : OverDecG),
    g.enc ≠ [] → g.enc.length < 2 ^ 62 →
    img.FrozenLoaded s → s.symtab = img.symtab →
    s.pc = (contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x1ee8#64 →
    s.status = .Running → s.sp = g.q → (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x19 = g.r19 → s.readReg64 .x20 = g.r20 → s.readReg64 .x26 = g.r26 →
    s.readReg64 .x21 = g.q + 0x930#64 → s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 → s.readReg64 .x27 = g.prevPtr →
    s.readReg64 .x29 = g.q + 0xc70#64 →
    calleeSavedVRegs s = calleeSavedVRegs g.sv →
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x216c#64) s
      (overPrevElemAtExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗ overDecScratchPre g.q ∗
        stackAt g.q overDecStackX ∗
        A.pool)
      (fun sf P_f => OverDecRegs img ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ overDecHeapExt A g g.enc SSGQ.empty))
      (PanicOomProp s0)

/-- Entry (`+0x1ee8 → +0x216c`): from `OverPrevDecodeStmt`'s pre with `enc ≠ []` to the field
body with `rest = enc` and `SSGQ.empty`. -/
abbrev OverDecEntryStmt : Prop :=
  OverDecEntryStmtExt CryptoVerification.E2E.Record.A0

/-- One field (`+0x216c → +0x2160`) restricted by `P`, parameterized over `A : RustAlloc`. -/
def OverDecFieldStmtExt (A : RustAlloc) (P : GenFieldQ → Prop) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegs img ext s0 g 0x216c#64 s →
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecHeapExt A g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply fl)))
      (PanicOomProp s0)

abbrev OverDecFieldStmt (P : GenFieldQ → Prop) : Prop :=
  OverDecFieldStmtExt CryptoVerification.E2E.Record.A0 P

/-- Loop head (`+0x2160 → +0x216c`) when `rest ≠ []`, parameterized over `A : RustAlloc`. -/
def OverDecHeadConsStmtExt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (rest : List (BitVec 8)),
    rest ≠ [] → rest <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegs img ext s0 g 0x2160#64 s →
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x216c#64) s
      (overDecHeapExt A g rest v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x216c#64 sf ∧ (P_f ⊢ overDecHeapExt A g rest v))
      (PanicOomProp s0)

abbrev OverDecHeadConsStmt : Prop :=
  OverDecHeadConsStmtExt CryptoVerification.E2E.Record.A0

/-- Loop head (`+0x2160 → +0x2620`) when `rest = []`, parameterized over `A : RustAlloc`. -/
def OverDecHeadNilStmtExt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ),
    g.enc.length < 2 ^ 62 →
    OverDecRegs img ext s0 g 0x2160#64 s →
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2620#64) s
      (overDecHeapExt A g [] v)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2620#64 sf ∧ (P_f ⊢ overDecHeapExt A g [] v))
      (PanicOomProp s0)

abbrev OverDecHeadNilStmt : Prop :=
  OverDecHeadNilStmtExt CryptoVerification.E2E.Record.A0

/-! ## Field Groups -/

/-- Varint arms: tags 1 (`session_version`), 5 (`previous_counter`), 10, 11 (registration ids). -/
def OverDecVarintField : GenFieldQ → Prop
  | .base (.version _) | .base (.prevCounter _) | .remReg _ | .locReg _ => True
  | _ => False

/-- `bytes::merge` arms: tags 2, 3, 4 (identity keys, root key), 13 (`alice_base_key`),
15 (`pq_ratchet_state`). -/
def OverDecBytesField : GenFieldQ → Prop
  | .base (.lik _) | .base (.rik _) | .base (.root _) | .abk _ | .pq _ => True
  | _ => False

/-- Tag 6 (`sender_chain`, `merge<Chain>` in place into `Option<Chain>`). -/
def OverDecSenderField : GenFieldQ → Prop
  | .base (.sender _) => True
  | _ => False

/-- Tag 7 (`receiver_chains`, `merge<Chain>` into a temporary, then the push). -/
def OverDecRecvField : GenFieldQ → Prop
  | .base (.recv _) => True
  | _ => False

/-- The fields of a session with neither pending pre-key are in one of the four groups. -/
def OverDecAnyField (fl : GenFieldQ) : Prop :=
  OverDecVarintField fl ∨ OverDecBytesField fl ∨ OverDecSenderField fl ∨ OverDecRecvField fl

/-! ## Key and Arm Split of `OverDecFieldStmt` -/

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

/-- Key (`+0x216c → overDecArmOff fl`) parameterized over `A : RustAlloc`. -/
def OverDecKeyStmtExt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    Proofs.libsignal.Stage1X.AllocContractsX img A ext →
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    OverDecAnyField fl → fl.Ok →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegs img ext s0 g 0x216c#64 s →
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + overDecArmOff fl) s
      (overDecHeapExt A g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegs img ext s0 g (overDecArmOff fl) sf ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) ∧
        (P_f ⊢ overDecHeapExt A g (fl.payload ++ rest) v))
      (PanicOomProp s0)

/-- Key (`+0x216c → overDecArmOff fl`): `decode_varint [local#5]` reads the one-byte key of `fl`,
the checks pass, and the jump table goes to `fl`'s arm. -/
abbrev OverDecKeyStmt : Prop :=
  OverDecKeyStmtExt CryptoVerification.E2E.Record.A0

/-- Arm contract (`overDecArmOff fl → +0x2160`) under `Stage1X.AllocContractsX`, parameterized over
`A : RustAlloc`. -/
def OverDecArmStmtExt (A : RustAlloc) (P : GenFieldQ → Prop) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    Proofs.libsignal.Stage1X.AllocContractsX img A ext →
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

abbrev OverDecArmStmt (P : GenFieldQ → Prop) : Prop :=
  OverDecArmStmtExt CryptoVerification.E2E.Record.A0 P

/-- Arm contract (`overDecArmOff fl → +0x2160`) under `LibsignalTripleRatchet.AllocContractsX`,
parameterized over `A : RustAlloc`. -/
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

theorem stage1XAllocContractsX_of_trAllocContractsX {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := by
    refine Proofs.libsignal.Hooks2.subroutine_ok_inImage_map' hA.alloc fun ⟨size, align⟩ R s0 hpre => ?_
    refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpre ⊢
      exact hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := by
    refine Proofs.libsignal.Hooks2.subroutine_ok_inImage_map' hA.dealloc fun ⟨p, size, align⟩ R s0 hpre => ?_
    refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpost ⊢
      exact hpost
  realloc := by
    refine Proofs.libsignal.Hooks2.subroutine_ok_inImage_map' hA.realloc
      fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_
    refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩,
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := hA.shim extHookStack (Nat.le_refl _) (by decide)
  session_memmove := hA.session_memmove extHookStack (Nat.le_refl _) (by decide)

/-- Lift an allocator-polymorphic `Stage1X` arm contract to `LibsignalTripleRatchet.AllocContractsX`. -/
theorem OverDecArmStmtExt.toTR {A : RustAlloc} {P : GenFieldQ → Prop} (h : OverDecArmStmtExt A P) :
    OverDecArmStmtTRExt A P :=
  fun img ext hL hAC =>
    h img ext hL (stage1XAllocContractsX_of_trAllocContractsX hAC)

theorem OverDecArmStmt.toTR {P : GenFieldQ → Prop} (h : OverDecArmStmt P) :
    OverDecArmStmtTR P :=
  OverDecArmStmtExt.toTR h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
