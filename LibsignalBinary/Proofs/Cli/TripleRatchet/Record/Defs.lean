/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.Root
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Seam States and Segment Specifications for CLI `try_decrypt_from_record`

Defines the callee bundle `RecordCallees`, checkpoint seam states (`VState`, `MState`, `FState`,
`JState`), five segment contracts (`SegCloneSpec`, `SegDecryptSpec`, `SegMismatchSpec`,
`SegTailSpec`, `SegExitSpec`), and seam-composition theorems for the `try_decrypt_from_record`
region inside CLI `signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Host Function and `try_decrypt_with_state` Callee Predicates -/

set_option maxRecDepth 200000 in
open ProofLib.ProgramReflection in
/-- `signal_session_ratchet::decrypt_signal` (`msgDecryptName`, unique by `recordRegion_unique`)
starts at image offset `ls_off% "signal_session_ratchet::decrypt_signal"` (`238760`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") := by
  exact (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")

/-- `try_decrypt_with_state::<Coins>` (called at `+0x6b4`) meets `tryDecryptSpec` on
`tripleRatchetProgAtExt img.base ext`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName) (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img)

/-- `try_decrypt_with_state::<Coins>` (called at `+0x6b4`) meets `tryDecryptSpec` on
`tripleRatchetProgAt img.base …`, restricted to session states whose PQ state satisfies `Q`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase_trap (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

/-- `tryDecryptSpec` restricted by `Q ·.st.pqRatchetState` with spatial frame `F` on the right of
`pre` and `post` so `wpElimSpatialContext` keeps the existential and pure prefixes outside. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF' (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).pre x s ∗ F
    post := fun x s0 sf => (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).post x s0 sf ∗ F }

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF' Q F C A ctl parse S img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF_trap (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF' Q F C A ctl parse S img)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.subroutine_ok_tryDecryptSpecQF'_emp {P : Program} {addr : BitVec 64}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    (h : subroutine_ok P addr
      ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))) :
    subroutine_ok P addr (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF' Q emp C A ctl parse S img) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', Spec.restrictPre] at hpre ⊢
    rwa [sepConj_emp] at hpre
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', Spec.restrictPre] at hpost ⊢
    rwa [sepConj_emp]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBaseQF_of_v1Run_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : LibsignalSpqrV1.MlKem} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt_trap C A ctl K abs img)
    (hhooks : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hspqr : LibsignalSpqrV1.SpqrHooks C A K abs)
    (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF_trap (·.length < 2 ^ 32) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs := by
  have h' := h hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads,
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) hloads] at h'
  refine subroutine_ok_mono h' (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT] at hpre ⊢
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpre
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT] at hpost ⊢
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpost

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBaseQF_of_v1Run {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : LibsignalSpqrV1.MlKem} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img)
    (hhooks : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hspqr : LibsignalSpqrV1.SpqrHooks C A K abs)
    (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF (·.length < 2 ^ 32) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs := by
  have h' := h hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hloads] at h'
  refine subroutine_ok_mono h' (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT] at hpre ⊢
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpre
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptSpecQF', CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT] at hpost ⊢
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpost

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBase_of_run_trap {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt_trap C A ctl S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : _root_.CryptoVerification.LibsignalTripleRatchet.SpqrRecvOk_trap C A S abs img)
    (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase_trap Q img C A ctl uuidTryParse S abs := by
  have h' := h hhooks hrecv hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads, entryOf_eq_tripleRatchetProgAt_trap (C := C)
    (abs := abs) hloads] at h'
  exact Spec.subroutine_ok_restrictPre _ h'

/-- Unconditional `TryDecryptRunStmt` entails `TryDecryptOkAtImageBase Q` for every `Q`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBase_of_run {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt C A ctl S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase Q img C A ctl uuidTryParse S abs := by
  have h' := h hhooks hrecv hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) hloads] at h'
  exact Spec.subroutine_ok_restrictPre _ h'

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOktripleRatchetProgAt_of_emptyRun_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt_trap C A ctl S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk) (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase_trap (· = []) img C A ctl uuidTryParse S abs := by
  have h' := h hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads, entryOf_eq_tripleRatchetProgAt_trap (C := C)
    (abs := abs) hloads] at h'
  exact h'

/-- Empty-state `TryDecryptEmptyRunStmt` entails `TryDecryptOkAtImageBase (· = [])`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOktripleRatchetProgAt_of_emptyRun {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt C A ctl S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk) (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase (· = []) img C A ctl uuidTryParse S abs := by
  have h' := h hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) hloads] at h'
  exact h'

/-- In-image callees of the `try_decrypt_from_record` region (`__rust_alloc`, `__rust_dealloc`,
`memcpy`, and the no-alloc shim come from `TripleRatchetHooks`, with `handle_error` as a panic stub):
* `chainClone` / `senderClone`: `Chain::clone` on receiver (`+0x350`) and sender (`+0x2b4`) chains;
* `dropLocal2`: `drop_glue<SessionStructure>` on the cloned session (`+0x854`, `+0x1e88`);
* `setState`: `SessionRecord::set_session_state` (`+0x7d8`);
* `growSpe`: `RawVec<SignalProtocolError>::grow_one` (`+0x824`, `+0x17a0`);
* `closure`: `try_decrypt_from_record::{closure#0}` with logging disabled (`+0x80c`, `+0x1788`). -/
structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  chainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOk img.base C A ctl abs
  senderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOk img.base C A ctl abs
  dropLocal2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs
  setState : FromRecordCallees.SetSessionStateOk img.base C A ctl abs
  growSpe : FromRecordCallees.GrowOneSpeOk img.base C A ctl abs
  closure : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk img C ctl abs

structure _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop where
  chainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOk_trap img.base C A abs
  senderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOk_trap img.base C A abs
  dropLocal2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok_trap img.base C A abs
  setState : FromRecordCallees.SetSessionStateOk_trap img.base C A abs
  growSpe : FromRecordCallees.GrowOneSpeOk_trap img.base C A abs
  closure : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk_trap img C abs

/-! ## Seam PCs and Checkpoint States -/

/-- V (`+0x69c`): the version check passed (`+0x698: b.ne` not taken); next
`try_decrypt_with_state` (`+0x69c..+0x6b4`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x69c#64

/-- M (`+0x7e4`): the version check failed (`+0x698: b.ne` taken); next the
`UnrecognizedMessageVersion` push. -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recMPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x7e4#64

/-- F (`+0x850`): one error collected (from M, or from V's non-duplicate `Err`, `+0x17d4: b.eq`
taken); next `drop_glue<SS> [local#2]` on the clone (`+0x854`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x850#64

/-- J (`+0x1e8c`): the result is in the slot and `x28`; next the `errs` drop loop. Reached by
`b` from `+0x7e0` (`Ok`) and `+0x1e28` (`"decryption failed"`), by fall-through from `+0x1e88`
(`DuplicatedMessage`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1e8c#64

set_option linter.unusedVariables false in
/-- Seam **V** (`recVPC`, `+0x69c`): session clone `G₁` at `sp + 0xca0` (`CloneRel`, value `x.st`),
matching message/session versions (`(session_version = 0 ? 2 : session_version) = message_version`),
empty `errs`, free return slot, untouched coins tape, and `tryDecryptSpec` precondition facts. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC img ∧ recMeta img s0 s ∧ recPure x ∧ CloneRel x.G G₁ ∧
  x.st.version.toNat = x.msg.messageVersion.toNat ∧
  (s.mem ⊨ recFrame A img x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ R)

set_option linter.unusedVariables false in
/-- Seam **M** (`recMPC`, `+0x7e4`): as `VState`, with mismatched versions and `x9` holding the
message version (`+0x668: ldr w9, [sp, #0x9c]`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recMPC img ∧ recMeta img s0 s ∧
  x.st.version.toNat ≠ x.msg.messageVersion.toNat ∧
  s.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
  (s.mem ⊨ recFrame A img x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ R)

set_option linter.unusedVariables false in
/-- Seam **F** (`recFPC`, `+0x850`): one error collected in `errs`, model result
`InvalidMessage(Whisper, "decryption failed")`, unchanged record, session clone at `sp + 0xca0`,
free return slot, and coins tape advanced by `x.draws`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) (x : RecordDecryptGhost) (R : SepProp) (s0 s : State) :
    Prop :=
  let sp := s0.sp
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC img ∧ recMeta img s0 s ∧
  (x.model C S parse).1 = .error (.invalidMessage .whisper .decryptionFailed) ∧
  (s.mem ⊨ recFrame A img x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    (∃∗ G₂ : SessionGhost, ∃∗ st₂ : SessionState (List (BitVec 8)),
      sessionStateAt A (sp + 0xca0#64) G₂ st₂) ∗
    (∃∗ r : RecErr, errsAt A (sp + 0x5d8#64) [r]) ∗ memRegion (sp + 0x4b0#64) 48 ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C) ∗ R)

set_option linter.unusedVariables false in
/-- Seam **J** (`recJPC`, `+0x1e8c`): non-panicking model result `res` written to `recordResultAt`
with word 0 in `x28`, `x26 = sp + 0xa0`, `x27 = x.sret`, updated or preserved session record
matching `recordDecryptSpec.post`, at most one error in `errs`, and the clone's heap allocations
freed. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) (x : RecordDecryptGhost) (R : SepProp) (s0 s : State) :
    Prop :=
  let sp := s0.sp
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC img ∧ recMeta img s0 s ∧ (x.model C S parse).1 ≠ .error .panic ∧
  s.readReg64 .x26 = sp + 0xa0#64 ∧ s.readReg64 .x27 = x.sret ∧
  s.readReg64 .x28 = recordResultTag (x.model C S parse).1 ∧
  (s.mem ⊨ recFrame A img x sp ∗
    (match (x.model C S parse).1 with
     | .ok _ => ∃∗ G' : SessionGhost, ⌜x.G.AfterRecordDecrypt G'⌝ ∗
         sessionStateAt A (sp + 0x138#64) G' (x.model C S parse).2
     | .error _ => sessionStateAt A (sp + 0x138#64) x.G x.st) ∗
    recordResultAt A (sp + 0x4b0#64) (x.model C S parse).1 ∗
    (∃∗ errs : List RecErr, errsAt A (sp + 0x5d8#64) errs) ∗ memRegion (sp + 0xca0#64) 344 ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C) ∗ R)

/-! ## Segment Specifications

Each segment steps from its entry seam state either to a successor seam state or directly to a
`regionOutcome` of `recordDecryptSpec`. -/

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img → s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s0.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s0 s' ∧
        ((∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s') ∨ (∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s') ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img → s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s0.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s0 s' ∧
        ((∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s') ∨ (∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s') ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

/-- Clone segment (`+0x1a8 → +0x69c / +0x7e4`): initializes frame slots, clones `SessionStructure`
field-by-field into `sp + 0xca0`, and branches on the session/message version check to `V` or `M`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOk img.base C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOk img.base C A ctl abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img → s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s0.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s0 s' ∧
        ((∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s') ∨ (∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s') ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOk_trap img.base C A abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img → s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      (trTrapProgAt img.base C abs).CodeLoaded s0.mem →
      ∃ s', Steps (trTrapProgAt img.base C abs) s0 s' ∧
        ((∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s') ∨ (∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s') ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkExt img C A ctl parse S ext →
  FromRecordCallees.SetSessionStateOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext →
  FromRecordCallees.GrowOneSpeOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt img ext →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨ CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkExt img C A ctl parse S ext →
  FromRecordCallees.SetSessionStateOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext →
  FromRecordCallees.GrowOneSpeOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt img ext →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨ CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

/-- Decrypt segment (`+0x69c → +0x1e8c / +0x850`): calls `try_decrypt_with_state` at `+0x6b4`
under `Q x.st.pqRatchetState` and dispatches `Ok` (via `memcpy` + `set_session_state`) and
`DuplicatedMessage` (via `drop_glue<SS>`) to `J`, or pushes any other error onto `errs` to reach `F`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase Q img C A ctl parse S abs →
  FromRecordCallees.SetSessionStateOk img.base C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  FromRecordCallees.GrowOneSpeOk img.base C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk img C ctl abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨ CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec_trap (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase_trap Q img C A ctl parse S abs →
  FromRecordCallees.SetSessionStateOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok_trap img.base C A abs →
  FromRecordCallees.GrowOneSpeOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk_trap img C abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ R s0 s →
      rootStack ≤ s0.sp.toNat →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨ CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec RecordDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).pre x s
    post := fun x s0 sf => F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).post x s0 sf }

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF Q F img C A ctl parse S abs →
  FromRecordCallees.SetSessionStateOk img.base C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  FromRecordCallees.GrowOneSpeOk img.base C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk img C ctl abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ (F ∗ R) s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x (F ∗ R) s0 s' ∨ CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x (F ∗ R) s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecQF_trap (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF_trap Q F img C A ctl parse S abs →
  FromRecordCallees.SetSessionStateOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok_trap img.base C A abs →
  FromRecordCallees.GrowOneSpeOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk_trap img C abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VState A ctl img x G₁ (F ∗ R) s0 s →
      rootStack ≤ s0.sp.toNat →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x (F ∗ R) s0 s' ∨ CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x (F ∗ R) s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  FromRecordCallees.GrowOneSpeOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt img ext →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  FromRecordCallees.GrowOneSpeOkExt img.base A ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt img ext →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

/-- Version-mismatch segment (`+0x7e4 → +0x850`): stages `UnrecognizedMessageVersion(x9)` at
`sp + 0x5f0`, invokes `{closure#0}` and `grow_one`, pushes onto `errs`, and reaches `F`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  FromRecordCallees.GrowOneSpeOk img.base C A ctl abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk img C ctl abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  FromRecordCallees.GrowOneSpeOk_trap img.base C A abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOk_trap img C abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

/-- Error-tail segment (`+0x850 → +0x1e8c`): drops the cloned `SessionStructure`, takes the empty
`previous_sessions` branch (`+0x868`), allocates the 17-byte `"decryption failed"` string, writes
the error return slot (`x28 = speWord 24`), and reaches `J`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok_trap img.base C A abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl parse S img x R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpecExt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts_trap img.base C A parse S ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s'

/-- Exit segment (`+0x1e8c → +0x1f50`): drops elements of `errs` via the `.rodata` jump table
(freeing owned `String` payloads for tags `{1, 24}`), deallocates the `errs` buffer when `cap ≠ 0`,
and reaches `recordRegionExit` satisfying `recordDecryptSpec.post`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s'

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl parse S img x R s0 s →
      (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
        regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s'

/-! ## Seam Composition -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost}
    {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    rootStack ≤ s0.sp.toNat := by
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2.1.2.2.2.2.2.2.2.2

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.onPanic_drop_frame_record {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : RecordDecryptGhost} {F R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 sf : State}
    (h : regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x (F ∗ R) s0 sf) :
    regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl parse S img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 sf := by
  rcases h with ⟨hpc, hrun, hvregs, hpost⟩ | ⟨hpan, hqp⟩
  · refine Or.inl ⟨hpc, hrun, hvregs, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF]
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpost
  · exact Or.inr ⟨hpan, CryptoVerification.Cli.LibsignalTripleRatchet.Record.onPanic_drop_frame_record hqp⟩

/-- Composes the five segment specifications into `region_ok` (preserving `calleeSavedVRegs`) on
session states whose PQ state satisfies `Q`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_vregs_ok_of_seams {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees img C A ctl abs)
    (htd : CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase Q img C A ctl uuidTryParse S abs)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec Q img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec img C A ctl uuidTryParse S abs) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)) := by
  apply region_ok_withVRegs_restrictPre_of_reaches
  intro x R s0 hQ hpc hst hpre hL
  have hstk := CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre hpre
  have hJ : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := fun s hs hLs => hexit hloads hhooks x R s0 s hs hLs
  have hF : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x R s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone hloads hhooks hc.chainClone hc.senderClone x R s0 hpc hst hpre hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ := hdec hloads hhooks htd hc.setState hc.dropLocal2 hc.growSpe
      hc.closure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ := hmis hloads hhooks hc.growSpe hc.closure x G₁ R s0 s' hm
      (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · exact ⟨s', hst', hout⟩

/-- Composes the five segment specifications with spatial frame `F` on session states whose PQ
state satisfies `Q`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seamsQF {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees img C A ctl abs)
    (htd : CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF Q F img C A ctl uuidTryParse S abs)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecQF Q F img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec img C A ctl uuidTryParse S abs) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl uuidTryParse S img) := by
  apply region_ok_of_reaches
  intro x R s0 hpc hst hpre hL
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ (F ∗ R) :=
    Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpre
  have hstk := CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre hpre'
  have hJ : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (F ∗ R) s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨sf, hstf, hout⟩ := hexit hloads hhooks x (F ∗ R) s0 s hs hLs
    exact ⟨sf, hstf, CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩
  have hF : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (F ∗ R) s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x (F ∗ R) s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone hloads hhooks hc.chainClone hc.senderClone x (F ∗ R) s0 hpc hst hpre' hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ := hdec hloads hhooks htd hc.setState hc.dropLocal2 hc.growSpe
      hc.closure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ := hmis hloads hhooks hc.growSpe hc.closure x G₁ (F ∗ R) s0 s' hm
      (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩
  · exact ⟨s', hst', CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩

/-- Composes the five segment specifications on session states whose PQ state satisfies `Q`
(`F := emp`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seams {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees img C A ctl abs)
    (htd : CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase Q img C A ctl uuidTryParse S abs)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec Q img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec img C A ctl uuidTryParse S abs) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).restrictPre (Q ·.st.pqRatchetState)) := by
  apply region_ok_restrictPre_of_reaches
  intro x R s0 hQ hpc hst hpre hL
  have hstk := CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre hpre
  have hJ : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := fun s hs hLs => hexit hloads hhooks x R s0 s hs hLs
  have hF : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x R s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone hloads hhooks hc.chainClone hc.senderClone x R s0 hpc hst hpre hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ := hdec hloads hhooks htd hc.setState hc.dropLocal2 hc.growSpe
      hc.closure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ := hmis hloads hhooks hc.growSpe hc.closure x G₁ R s0 s' hm
      (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · exact ⟨s', hst', hout⟩

/-- Instantiates `recordDecrypt_region_ok_of_seams` at `Q := fun _ => True` to establish
`RecordDecryptRunStmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_run_of_seams (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees img C A ctl abs)
    (htry : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt C A ctl S abs img)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec (fun _ => True) img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptRunStmt C A ctl S abs img := by
  intro hhooks hrecv hloads
  have h : region_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).restrictPre (fun _ => True)) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seams hloads hhooks (hcallees hhooks hloads)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBase_of_run htry hhooks hrecv hloads) hclone hdec hmis htail hexit
  rw [Spec.restrictPre_true] at h
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact h

/-- Instantiates `recordDecrypt_region_ok_of_seams` at `Q := (· = [])` using
`TryDecryptEmptyRunStmt` to establish `RecordDecryptEmptyRunStmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptEmpty_run_of_seams (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees img C A ctl abs)
    (htry : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt C A ctl S abs img)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec (· = []) img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptEmptyRunStmt C A ctl S abs img := by
  intro hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seams hloads hhooks (hcallees hhooks hloads)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOktripleRatchetProgAt_of_emptyRun htry hhooks hempty hloads) hclone hdec hmis htail hexit

/-- Instantiates `recordDecrypt_region_ok_of_seamsQF` at `Q := (·.length < 2 ^ 32)` and
`F := TokenInit img` using `TryDecryptV1RunStmt` to establish `RecordDecryptV1RunStmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptV1_run_of_seams (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
      Obj.Loads libsignalSessionImage img → CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees img C A ctl abs)
    (htry : CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecQF (·.length < 2 ^ 32) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    CryptoVerification.Cli.LibsignalSpqrV1.RecordDecryptV1RunStmt C A ctl K abs img := by
  intro hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seamsQF hloads hhooks (hcallees hhooks hloads)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBaseQF_of_v1Run htry hhooks hspqr hloads) hclone hdec hmis htail hexit

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptRunStmt_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → _root_.CryptoVerification.LibsignalTripleRatchet.SpqrRecvOk_trap C A S abs img → Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg_trap img C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptEmptyRunStmt_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg_trap img C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      { CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜x.st.pqRatchetState = []⌝ ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).pre x s }

def _root_.CryptoVerification.Cli.LibsignalSpqrV1.RecordDecryptV1RunStmt_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs → LibsignalSpqrV1.SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg_trap img C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) img)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_vregs_ok_of_seams_trap {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees_trap img C A abs)
    (htd : CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase_trap Q img C A ctl uuidTryParse S abs)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec_trap img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec_trap Q img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec_trap img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec_trap img C A ctl uuidTryParse S abs) :
    region_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)) := by
  apply region_ok_withVRegs_restrictPre_of_reaches
  intro x R s0 hQ hpc hst hpre hL
  have hstk := CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre hpre
  have hJ : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := fun s hs hLs => hexit hloads hhooks x R s0 s hs hLs
  have hF : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x R s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone hloads hhooks hc.chainClone hc.senderClone x R s0 hpc hst hpre hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ := hdec hloads hhooks htd hc.setState hc.dropLocal2 hc.growSpe
      hc.closure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ := hmis hloads hhooks hc.growSpe hc.closure x G₁ R s0 s' hm
      (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · exact ⟨s', hst', hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seamsQF_trap {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees_trap img C A abs)
    (htd : CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBaseQF_trap Q F img C A ctl uuidTryParse S abs)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec_trap img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecQF_trap Q F img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec_trap img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec_trap img C A ctl uuidTryParse S abs) :
    region_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl uuidTryParse S img) := by
  apply region_ok_of_reaches
  intro x R s0 hpc hst hpre hL
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ (F ∗ R) :=
    Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpre
  have hstk := CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre hpre'
  have hJ : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (F ∗ R) s0 s →
      region_reaches (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨sf, hstf, hout⟩ := hexit hloads hhooks x (F ∗ R) s0 s hs hLs
    exact ⟨sf, hstf, CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩
  have hF : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (F ∗ R) s0 s →
      region_reaches (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x (F ∗ R) s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone hloads hhooks hc.chainClone hc.senderClone x (F ∗ R) s0 hpc hst hpre' hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ := hdec hloads hhooks htd hc.setState hc.dropLocal2 hc.growSpe
      hc.closure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ := hmis hloads hhooks hc.growSpe hc.closure x G₁ (F ∗ R) s0 s' hm
      (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩
  · exact ⟨s', hst', CryptoVerification.Cli.LibsignalTripleRatchet.Record.regionOutcome_recordDecryptSpecQF hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seams_trap {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees_trap img C A abs)
    (htd : CryptoVerification.Cli.LibsignalTripleRatchet.Record.TryDecryptOkAtImageBase_trap Q img C A ctl uuidTryParse S abs)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec_trap img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec_trap Q img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec_trap img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec_trap img C A ctl uuidTryParse S abs) :
    region_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).restrictPre (Q ·.st.pqRatchetState)) := by
  apply region_ok_restrictPre_of_reaches
  intro x R s0 hQ hpc hst hpre hL
  have hstk := CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre hpre
  have hJ : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := fun s hs hLs => hexit hloads hhooks x R s0 s hs hLs
  have hF : ∀ s, CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x R s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone hloads hhooks hc.chainClone hc.senderClone x R s0 hpc hst hpre hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ := hdec hloads hhooks htd hc.setState hc.dropLocal2 hc.growSpe
      hc.closure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ := hmis hloads hhooks hc.growSpe hc.closure x G₁ R s0 s' hm
      (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · exact ⟨s', hst', hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_run_of_seams_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees_trap img C A abs)
    (htry : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptRunStmt_trap C A ctl S abs img)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec_trap img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec_trap (fun _ => True) img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec_trap img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec_trap img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptRunStmt_trap C A ctl S abs img := by
  intro hhooks hrecv hloads
  have h : region_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).restrictPre (fun _ => True)) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seams_trap hloads hhooks (hcallees hhooks hloads)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBase_of_run_trap htry hhooks hrecv hloads) hclone hdec hmis htail hexit
  rw [Spec.restrictPre_true] at h
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads]
  exact h

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptEmpty_run_of_seams_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees_trap img C A abs)
    (htry : CryptoVerification.Cli.LibsignalTripleRatchet.TryDecryptEmptyRunStmt_trap C A ctl S abs img)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec_trap img C A ctl uuidTryParse S abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpec_trap (· = []) img C A ctl uuidTryParse S abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap img C A ctl uuidTryParse S abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec_trap img C A ctl uuidTryParse S abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec_trap img C A ctl uuidTryParse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.RecordDecryptEmptyRunStmt_trap C A ctl S abs img := by
  intro hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads]
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seams_trap hloads hhooks (hcallees hhooks hloads)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOktripleRatchetProgAt_of_emptyRun_trap htry hhooks hempty hloads) hclone hdec hmis htail hexit

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptV1_run_of_seams_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
      Obj.Loads libsignalSessionImage img → CryptoVerification.Cli.LibsignalTripleRatchet.Record.RecordCallees_trap img C A abs)
    (htry : CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt_trap C A ctl K abs img)
    (hclone : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSpec_trap img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hdec : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptSpecQF_trap (·.length < 2 ^ 32) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hmis : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegMismatchSpec_trap img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (htail : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegTailSpec_trap img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hexit : CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegExitSpec_trap img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    CryptoVerification.Cli.LibsignalSpqrV1.RecordDecryptV1RunStmt_trap C A ctl K abs img := by
  intro hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap hloads]
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecrypt_region_ok_of_seamsQF_trap hloads hhooks (hcallees hhooks hloads)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptOkAtImageBaseQF_of_v1Run_trap htry hhooks hspqr hloads) hclone hdec hmis htail hexit

end CryptoVerification.LibsignalTripleRatchet.Record
