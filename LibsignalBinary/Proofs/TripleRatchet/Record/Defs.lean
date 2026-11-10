/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.Defs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosure
public import LibsignalBinary.Proofs.TripleRatchet.Record.RecordCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.ErrRaw
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Seam States and Segment Specifications for `try_decrypt_from_record`

Decomposes the `try_decrypt_from_record` region (`recordRegionEntry img` `+0x1a8` to
`recordRegionExit img` `+0x1f50` of `session_message_decrypt_signal`, `0x3a4a8`) across four
intermediate control-flow seams — version-ok `V` (`+0x69c`), version-mismatch `M` (`+0x7e4`),
collected-error `F` (`+0x850`), and result-join `J` (`+0x1e8c`) — and proves
`recordDecrypt_run_of_seams` composing the five segment contracts (`SegCloneSpec`, `SegDecryptSpec`,
`SegMismatchSpec`, `SegTailSpec`, `SegExitSpec`) into `RecordDecryptRunStmt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Host function offset -/

set_option maxRecDepth 200000 in
open ProofLib.ProgramReflection in
/-- `session_message_decrypt_signal` (`msgDecryptName`) starts at image offset `0x3a4a8`. -/
theorem libsignalSessionCode_fnOff_sym_3a4a8 :
    libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") := by
  exact (ls_lemma% fnOff "session_message_decrypt_signal")

/-! ## Region reachability -/

/-- The two outcomes `region_ok` allows at `sf`: a `.Running` arrival at `exit` with `post`, or a
panic with `onPanic` (both framed by `R`). -/
def regionOutcome {α : Type} (spec : Spec α) (exit : BitVec 64) (x : α) (R : SepProp)
    (s0 sf : State) : Prop :=
  (sf.pc = exit ∧ sf.status = .Running ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
    (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∨
  (sf.status = .Panicked ∧ (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))

/-- From the current state `s` of a run started at `s0`, `prog` reaches a `regionOutcome` if its
code is loaded: the region analogue of `reaches_outcome` (`region_ok` is `region_reaches … s0 s0`
at the entry). -/
def region_reaches {α : Type} (prog : Program) (spec : Spec α) (exit : BitVec 64) (x : α)
    (R : SepProp) (s0 s : State) : Prop :=
  prog.CodeLoaded s.mem → ∃ sf, Steps prog s sf ∧ regionOutcome spec exit x R s0 sf

/-- Prepend steps to a `region_reaches` (as `reaches_outcome_steps`). -/
theorem region_reaches_steps {α : Type} {prog : Program} {spec : Spec α} {exit : BitVec 64}
    {x : α} {R : SepProp} {s0 s s' : State} (h_steps : Steps prog s s')
    (h_next : region_reaches prog spec exit x R s0 s') :
    region_reaches prog spec exit x R s0 s := by
  intro hL
  rcases h_next (h_steps.codeLoaded hL) with ⟨sf, hsteps2, hout⟩
  exact ⟨sf, h_steps.trans hsteps2, hout⟩

/-- `region_ok` from `region_reaches` at every entry state. -/
theorem region_ok_of_reaches {α : Type} {prog : Program} {entry exit : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → region_reaches prog spec exit x R s0 s0) :
    region_ok prog entry exit spec := by
  intro x R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', _, hpost⟩ | hpan⟩ := h x R s0 hpc hst hpre hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc', hrun', hpost⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-! ## Callee hypotheses -/

/-- `try_decrypt_with_state::<HookRng>` (`0x3439c`, called at `+0x6b4`) meets the trusted
`tryDecryptSpec` on `tripleRatchetProgAtExt img.base ext`. -/
def TryDecryptOkExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName) (tryDecryptSpec C A ctl parse S img)

/-- `try_decrypt_with_state::<HookRng>` (`0x3439c`, called at `+0x6b4`) meets the trusted
`tryDecryptSpec` on `tripleRatchetProgAt img.base …`, restricted to session states whose pq state meets `Q`
(from `TryDecryptRunStmt` by `tryDecryptOkAtImageBase_of_run` for every `Q`, or from
`TryDecryptEmptyRunStmt` by `tryDecryptOktripleRatchetProgAt_of_emptyRun` for `Q := (· = [])`). -/
def TryDecryptOkAtImageBase (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName)
    ((tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))

/-- `tryDecryptSpec` with `Q ·.st.pqRatchetState` in `pre` and spatial frame `F` on the right of
`pre` and `post` (so `wpElimSpatialContext` keeps the existential and pure prefixes of `post` on
the outside). -/
def tryDecryptSpecQF' (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec TryDecryptGhost :=
  { tryDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ (tryDecryptSpec C A ctl parse S img).pre x s ∗ F
    post := fun x s0 sf => (tryDecryptSpec C A ctl parse S img).post x s0 sf ∗ F }

/-- `TryDecryptOkAtImageBase` generalized with spatial frame `F`. -/
def TryDecryptOkAtImageBaseQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr tryDecryptName)
    (tryDecryptSpecQF' Q F C A ctl parse S img)

theorem subroutine_ok_tryDecryptSpecQF'_emp {P : Program} {addr : BitVec 64}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    (h : subroutine_ok P addr
      ((tryDecryptSpec C A ctl parse S img).restrictPre (Q ·.st.pqRatchetState))) :
    subroutine_ok P addr (tryDecryptSpecQF' Q emp C A ctl parse S img) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  · dsimp only [tryDecryptSpecQF', Spec.restrictPre] at hpre ⊢
    rwa [sepConj_emp] at hpre
  · dsimp only [tryDecryptSpecQF', Spec.restrictPre] at hpost ⊢
    rwa [sepConj_emp]

theorem tryDecryptOkAtImageBaseQF_of_okQ {Q : List (BitVec 8) → Prop} {img : Obj.Image}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h : TryDecryptOkAtImageBase Q img C A ctl parse S abs) :
    TryDecryptOkAtImageBaseQF Q emp img C A ctl parse S abs :=
  subroutine_ok_tryDecryptSpecQF'_emp h

theorem tryDecryptOkAtImageBaseQF_of_v1Run {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : LibsignalSpqrV1.MlKem} {abs : String → Option (State → State)}
    (h : LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img)
    (hhooks : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hspqr : LibsignalSpqrV1.SpqrHooks C A K abs)
    (hloads : Obj.Loads libsignalSessionImage img) :
    TryDecryptOkAtImageBaseQF (·.length < 2 ^ 32) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs := by
  have h' := h hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hloads] at h'
  refine subroutine_ok_mono h' (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    (fun _ _ _ _ hp => hp) (fun _ _ _ _ _ he => he) (fun _ _ _ _ ho => ho)
  · dsimp only [tryDecryptSpecQF', LibsignalSpqrV1.tryDecryptSpecT] at hpre ⊢
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpre
  · dsimp only [tryDecryptSpecQF', LibsignalSpqrV1.tryDecryptSpecT] at hpost ⊢
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpost

/-- Specializes `TryDecryptRunStmt` to `TryDecryptOkAtImageBase Q` for arbitrary `Q`. -/
theorem tryDecryptOkAtImageBase_of_run {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : TryDecryptRunStmt C A ctl S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOk C A ctl S abs img)
    (hloads : Obj.Loads libsignalSessionImage img) :
    TryDecryptOkAtImageBase Q img C A ctl uuidTryParse S abs := by
  have h' := h hhooks hrecv hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) hloads] at h'
  exact Spec.subroutine_ok_restrictPre _ h'

/-- Specializes `TryDecryptEmptyRunStmt` to `TryDecryptOkAtImageBase (· = [])`. -/
theorem tryDecryptOktripleRatchetProgAt_of_emptyRun {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : TryDecryptEmptyRunStmt C A ctl S abs img) (hhooks : TripleRatchetHooks C A S abs)
    (hempty : S.RecvEmptyOk) (hloads : Obj.Loads libsignalSessionImage img) :
    TryDecryptOkAtImageBase (· = []) img C A ctl uuidTryParse S abs := by
  have h' := h hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) hloads] at h'
  exact h'

/-- Generalized `tripleRatchetProgAtExt` version of `RecordCallees`. -/
structure RecordCalleesExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  chainClone : FromRecordChainClone.ChainCloneOkExt img.base A ext
  senderClone : FromRecordChainClone.SenderChainCloneOkExt img.base A ext
  dropLocal2 : FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext
  setState : FromRecordCallees.SetSessionStateOkExt img.base A ext
  growSpe : FromRecordCallees.GrowOneSpeOkExt img.base A ext
  closure : FromRecordCallees.LogClosureOkExt img ext

/-- Callee contracts required by the `try_decrypt_from_record` region: `Chain::clone` on receiver
and sender chains, `drop_glue<SessionStructure> [local#2]`, `SessionRecord::set_session_state`,
`RawVec<SignalProtocolError>::grow_one`, and `try_decrypt_from_record::{closure#0}`. -/
structure RecordCallees (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop where
  chainClone : FromRecordChainClone.ChainCloneOk img.base C A ctl abs
  senderClone : FromRecordChainClone.SenderChainCloneOk img.base C A ctl abs
  dropLocal2 : FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs
  setState : FromRecordCallees.SetSessionStateOk img.base C A ctl abs
  growSpe : FromRecordCallees.GrowOneSpeOk img.base C A ctl abs
  closure : FromRecordCallees.LogClosureOk img C ctl abs

/-! ## Collected-error layout and session-clone relation -/

/-- Element of the local error vector `errs`: a `SignalProtocolError` returned by
`try_decrypt_with_state`, an `UnrecognizedMessageVersion(v)` built on version mismatch, or
(`.iscmk`) the static `"invalid receiver chain message keys"` error (`DecX.iscmkErrAt`). -/
inductive RecErr where
  | spe (e : SignalProtocolError)
  | version (v : BitVec 32)
  | iscmk

/-- 48-byte memory representation of a `RecErr` at `p`: `speAt` for `.spe`, tag `speWord 6` with
`u32` `v` at `p + 8` for `.version v`, or `DecX.iscmkErrAt` (tag `speWord 20` with static `.rodata`
`&str`) for `.iscmk`. -/
def recErrAt (A : RustAlloc) (p : BitVec 64) : RecErr → SepProp
  | .spe e => speAt A (utf8 "decrypt") p e
  | .version v => (p ↦₆₄ speWord 6) ∗ ((p + 8#64) ↦₃₂ v) ∗ memRegion (p + 12#64) 36
  | .iscmk => Proofs.libsignal.SR.DecX.iscmkErrAt p

/-- Local `Vec<SignalProtocolError>` with header at `h`: empty `{cap = 0, ptr = 8, len = 0}` for
`[]`, or a 4-element buffer (`192` B, `len = 1`) holding `recErrAt A ptr r` for `[r]`. -/
def errsAt (A : RustAlloc) (h : BitVec 64) : List RecErr → SepProp
  | [] => (h ↦₆₄ 0#64) ∗ ((h + 8#64) ↦₆₄ 8#64) ∗ ((h + 16#64) ↦₆₄ 0#64)
  | [r] =>
    ∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ (h ↦₆₄ 4#64) ∗ ((h + 8#64) ↦₆₄ p) ∗ ((h + 16#64) ↦₆₄ 1#64) ∗
      A.live p 192 8 ∗ recErrAt A p r ∗ memRegion (p + 48#64) 144
  | _ :: _ :: _ => ⌜False⌝

/-- The clone `G₁` of the record's session `G` (`+0x1fc..+0x638`): every `Vec` is fresh, so only
the bytes the model does not determine are related (both identity keys, `alice_base_key`, the
registration ids), as in `AfterRecordDecrypt`. -/
def CloneRel (G G₁ : SessionGhost) : Prop :=
  G₁.localIk.bytes = G.localIk.bytes ∧ G₁.remoteIk.bytes = G.remoteIk.bytes ∧
    G₁.alice.bytes = G.alice.bytes ∧ G₁.regIds = G.regIds

/-- A successful decrypt of the clone (`AfterTryDecrypt true`) relates the result to the record's ghost by
`AfterRecordDecrypt`. -/
theorem recordOkRel_of_clone_dec {G G₁ G' : SessionGhost} (hc : CloneRel G G₁)
    (hd : G₁.AfterTryDecrypt true G') : G.AfterRecordDecrypt G' := by
  simp only [SessionGhost.AfterTryDecrypt, SessionGhost.Keeps, ite_true] at hd
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := hd
  obtain ⟨c1, c2, c3, c4⟩ := hc
  exact ⟨(congrArg VecGhost.bytes h1).trans c1, (congrArg VecGhost.bytes h2).trans c2,
    (congrArg VecGhost.bytes h3).trans c3, h4.trans c4, h5, h6⟩

/-! ## Seam program counters and fixed stack frame -/

/-- V (`+0x69c`): the version check passed (`+0x698: b.ne` not taken); next
`try_decrypt_with_state` (`+0x69c..+0x6b4`). -/
abbrev recVPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x69c#64

/-- M (`+0x7e4`): the version check failed (`+0x698: b.ne` taken); next the
`UnrecognizedMessageVersion` push. -/
abbrev recMPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x7e4#64

/-- F (`+0x850`): one error collected (from M, or from V's non-duplicate `Err`, `+0x17d4: b.eq`
taken); next `drop_glue<SS> [local#2]` on the clone (`+0x854`). -/
abbrev recFPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x850#64

/-- J (`+0x1e8c`): the result is in the slot and `x28`; next the `errs` drop loop. Reached by
`b` from `+0x7e0` (`Ok`) and `+0x1e28` (`"decryption failed"`), by fall-through from `+0x1e88`
(`DuplicatedMessage`). -/
abbrev recJPC (img : Obj.Image) : BitVec 64 := entryOf img msgDecryptName + 0x1e8c#64

/-- Machine facts at every seam: running, `sp` / `x29` / the trace as at the entry `s0`, the image
loaded (for the callees' `Spec.inImage`). -/
def recMeta (img : Obj.Image) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp ∧ s.spAligned = true ∧
    s.readReg64 .x29 = s0.readReg64 .x29 ∧ s.trace = s0.trace ∧
    img.FrozenLoaded s ∧ s.symtab = img.symtab ∧
    calleeSavedVRegs s = calleeSavedVRegs s0

/-- Pure preconditions of `tryDecryptSpec` on `x.st` (`remoteIdentity ≠ some localIdentity`, `SeedsLen32`, and `< 2^32` chains). -/
def recPure (x : RecordDecryptGhost) : Prop :=
  x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
    x.st.receiverChains.length < 2 ^ 32

/-- Fixed stack and heap frame preserved across all seams (`sp = s0.sp`): spilled arguments at
`sp + 0x80..0xa0`, preserved caller slots (`0xe0`, `0xf0`, `0x128`, `0x130`), logging-closure
environment at `sp + 0x5b0..0x5d8`, scratch `memRegion`s, borrowed addresses and `SignalMessage`,
`logOff img`, `stackAt sp rootStack`, and `A.pool`. -/
def recFrame (A : RustAlloc) (img : Obj.Image) (x : RecordDecryptGhost) (sp : BitVec 64) :
    SepProp :=
  memRegion sp 0x80 ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  memRegion (sp + 0x5f0#64) 0x6b0 ∗ memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ logOff img ∗ stackAt sp rootStack ∗ A.pool

/-! ## Seam states -/

/-- Seam `V` (`recVPC`, `+0x69c`): session cloned into `sp + 0xca0` (`CloneRel G G₁`), session and
message versions match, `errs` empty, result slot `sp + 0x4b0` free, and RNG tape untouched. -/
def VState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recVPC img ∧ recMeta img s0 s ∧ recPure x ∧ CloneRel x.G G₁ ∧
  x.st.version.toNat = x.msg.messageVersion.toNat ∧
  (s.mem ⊨ recFrame A img x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ tapeAt ctl x.cur x.rest ∗ R)

/-- Seam `M` (`recMPC`, `+0x7e4`): as `VState`, but session and message versions differ and `x9` holds the message version. -/
def MState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recMPC img ∧ recMeta img s0 s ∧
  x.st.version.toNat ≠ x.msg.messageVersion.toNat ∧
  s.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
  (s.mem ⊨ recFrame A img x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ tapeAt ctl x.cur x.rest ∗ R)

/-- Seam `F` (`recFPC`, `+0x850`): one error collected in `errs`, model outcome is
`InvalidMessage(Whisper, "decryption failed")`, record unchanged, clone still allocated at
`sp + 0xca0`, result slot free, and RNG tape advanced by `x.draws`. -/
def FState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) (x : RecordDecryptGhost) (R : SepProp) (s0 s : State) :
    Prop :=
  let sp := s0.sp
  s.pc = recFPC img ∧ recMeta img s0 s ∧
  (x.model C S parse).1 = .error (.invalidMessage .whisper .decryptionFailed) ∧
  (s.mem ⊨ recFrame A img x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    (∃∗ G₂ : SessionGhost, ∃∗ st₂ : SessionState (List (BitVec 8)),
      sessionStateAt A (sp + 0xca0#64) G₂ st₂) ∗
    (∃∗ r : RecErr, errsAt A (sp + 0x5d8#64) [r]) ∗ memRegion (sp + 0x4b0#64) 48 ∗
    tapeAfter ctl x.cur x.rest (x.draws C) ∗ R)

/-- Seam `J` (`recJPC`, `+0x1e8c`): non-panic model result `res` written to `sp + 0x4b0` with
discriminant in `x28`, record updated on `Ok` (`AfterRecordDecrypt`) or preserved on `Err`, `errs`
holding at most one element, and the clone buffer deallocated. -/
def JState (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) (x : RecordDecryptGhost) (R : SepProp) (s0 s : State) :
    Prop :=
  let sp := s0.sp
  s.pc = recJPC img ∧ recMeta img s0 s ∧ (x.model C S parse).1 ≠ .error .panic ∧
  s.readReg64 .x26 = sp + 0xa0#64 ∧ s.readReg64 .x27 = x.sret ∧
  s.readReg64 .x28 = recordResultTag (x.model C S parse).1 ∧
  (s.mem ⊨ recFrame A img x sp ∗
    (match (x.model C S parse).1 with
     | .ok _ => ∃∗ G' : SessionGhost, ⌜x.G.AfterRecordDecrypt G'⌝ ∗
         sessionStateAt A (sp + 0x138#64) G' (x.model C S parse).2
     | .error _ => sessionStateAt A (sp + 0x138#64) x.G x.st) ∗
    recordResultAt A (sp + 0x4b0#64) (x.model C S parse).1 ∗
    (∃∗ errs : List RecErr, errsAt A (sp + 0x5d8#64) errs) ∗ memRegion (sp + 0xca0#64) 344 ∗
    tapeAfter ctl x.cur x.rest (x.draws C) ∗ R)

/-! ## Segment specifications -/

/-- Generalized `tripleRatchetProgAtExt` version of `SegCloneSpec`. -/
def SegCloneSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  FromRecordChainClone.ChainCloneOkExt img.base A ext →
  FromRecordChainClone.SenderChainCloneOkExt img.base A ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = recordRegionEntry img → s0.status = .Running →
      (s0.mem ⊨ (recordDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s0.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s0 s' ∧
        ((∃ G₁, VState A ctl img x G₁ R s0 s') ∨ (∃ G₁, MState A ctl img x G₁ R s0 s') ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Clone segment (`+0x1a8 → +0x69c / +0x7e4`): initializes frame slots, clones the active
`SessionStructure` into `sp + 0xca0`, and branches on the message version check to `VState` or
`MState` (panicking only on allocator failure). -/
def SegCloneSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  FromRecordChainClone.ChainCloneOk img.base C A ctl abs →
  FromRecordChainClone.SenderChainCloneOk img.base C A ctl abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = recordRegionEntry img → s0.status = .Running →
      (s0.mem ⊨ (recordDecryptSpec C A ctl parse S img).pre x s0 ∗ R) →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s0.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s0 s' ∧
        ((∃ G₁, VState A ctl img x G₁ R s0 s') ∨ (∃ G₁, MState A ctl img x G₁ R s0 s') ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Generalized `tripleRatchetProgAtExt` version of `SegDecryptSpec`. -/
def SegDecryptSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  TryDecryptOkExt img C A ctl parse S ext →
  FromRecordCallees.SetSessionStateOkExt img.base A ext →
  FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext →
  FromRecordCallees.GrowOneSpeOkExt img.base A ext →
  FromRecordCallees.LogClosureOkExt img ext →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      VState A ctl img x G₁ R s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (JState C A ctl parse S img x R s0 s' ∨ FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Decrypt segment (`+0x69c → +0x1e8c / +0x850`): invokes `try_decrypt_with_state` on the cloned
session at `sp + 0xca0` and dispatches `Ok` (committing via `set_session_state`) and
`DuplicatedMessage` (dropping the clone) to `JState`, and non-duplicate errors (pushing onto `errs`)
to `FState`. -/
def SegDecryptSpec (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  TryDecryptOkAtImageBase Q img C A ctl parse S abs →
  FromRecordCallees.SetSessionStateOk img.base C A ctl abs →
  FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  FromRecordCallees.GrowOneSpeOk img.base C A ctl abs →
  FromRecordCallees.LogClosureOk img C ctl abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      VState A ctl img x G₁ R s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (JState C A ctl parse S img x R s0 s' ∨ FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- `recordDecryptSpec` with `Q ·.st.pqRatchetState` and spatial frame `F` in `pre` and `post`. -/
def recordDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    Spec RecordDecryptGhost :=
  { recordDecryptSpec C A ctl parse S img with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗ (recordDecryptSpec C A ctl parse S img).pre x s
    post := fun x s0 sf => F ∗ (recordDecryptSpec C A ctl parse S img).post x s0 sf }

/-- `SegDecryptSpec` generalized with spatial frame `F`. -/
def SegDecryptSpecQF (Q : List (BitVec 8) → Prop) (F : SepProp) (img : Obj.Image) (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  TryDecryptOkAtImageBaseQF Q F img C A ctl parse S abs →
  FromRecordCallees.SetSessionStateOk img.base C A ctl abs →
  FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  FromRecordCallees.GrowOneSpeOk img.base C A ctl abs →
  FromRecordCallees.LogClosureOk img C ctl abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      Q x.st.pqRatchetState →
      VState A ctl img x G₁ (F ∗ R) s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (JState C A ctl parse S img x (F ∗ R) s0 s' ∨ FState C A ctl parse S img x (F ∗ R) s0 s' ∨
          regionOutcome (recordDecryptSpecQF Q F C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Generalized `tripleRatchetProgAtExt` version of `SegMismatchSpec`. -/
def SegMismatchSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  FromRecordCallees.GrowOneSpeOkExt img.base A ext →
  FromRecordCallees.LogClosureOkExt img ext →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      MState A ctl img x G₁ R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Version-mismatch segment (`+0x7e4 → +0x850`): constructs `UnrecognizedMessageVersion(x9)`,
invokes the logging closure and `RawVec::grow_one`, pushes the error onto `errs`, and reaches `FState`. -/
def SegMismatchSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  FromRecordCallees.GrowOneSpeOk img.base C A ctl abs →
  FromRecordCallees.LogClosureOk img C ctl abs →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      MState A ctl img x G₁ R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (FState C A ctl parse S img x R s0 s' ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Generalized `tripleRatchetProgAtExt` version of `SegTailSpec`. -/
def SegTailSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
  FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      FState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (JState C A ctl parse S img x R s0 s' ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Error-tail segment (`+0x850 → +0x1e8c`): drops the cloned `SessionStructure`, observes no
previous sessions, allocates `"decryption failed"` (17 B), writes `InvalidMessage` to `sp + 0x4b0`,
and reaches `JState`. -/
def SegTailSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      FState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        (JState C A ctl parse S img x R s0 s' ∨
          regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s')

/-- Generalized `tripleRatchetProgAtExt` version of `SegExitSpec`. -/
def SegExitSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  Stage2Contracts img.base C A ctl parse S ext →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      JState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s'

/-- Exit segment (`+0x1e8c → +0x1f50`): drops the elements and buffer of `errs` via the `.rodata`
drop jump table and reaches `recordRegionExit` with `recordDecryptSpec.post`. -/
def SegExitSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      JState C A ctl parse S img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x R s0 s'

/-! ## Segment composition -/

/-- Extracts `rootStack ≤ s0.sp.toNat` from `recordDecryptSpec.pre`. -/
theorem rootStack_le_of_recordPre {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost}
    {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    rootStack ≤ s0.sp.toNat := by
  simp only [recordDecryptSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2.1.2.2.2.2.2.2.2.2

theorem onPanic_drop_frame_record {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : RecordDecryptGhost} {F R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (recordDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ (recordDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R := by
  dsimp only [recordDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem⟩

theorem regionOutcome_recordDecryptSpecQF {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 sf : State}
    (h : regionOutcome (recordDecryptSpec C A ctl parse S img) (recordRegionExit img) x (F ∗ R) s0 sf) :
    regionOutcome (recordDecryptSpecQF Q F C A ctl parse S img) (recordRegionExit img) x R s0 sf := by
  rcases h with ⟨hpc, hrun, hvregs, hpost⟩ | ⟨hpan, hqp⟩
  · refine Or.inl ⟨hpc, hrun, hvregs, ?_⟩
    dsimp only [recordDecryptSpecQF]
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpost
  · exact Or.inr ⟨hpan, onPanic_drop_frame_record hqp⟩

/-- Generalized `tripleRatchetProgAtExt` composition of the five segment specs into `region_ok`. -/
theorem recordDecrypt_run_of_seams_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image)
    (hhooks : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hc : RecordCalleesExt img A ext)
    (htd : TryDecryptOkExt img C A ctl uuidTryParse S ext)
    (hclone : SegCloneSpecExt img C A ctl uuidTryParse S ext)
    (hdec : SegDecryptSpecExt img C A ctl uuidTryParse S ext)
    (hmis : SegMismatchSpecExt img C A ctl uuidTryParse S ext)
    (htail : SegTailSpecExt img C A ctl uuidTryParse S ext)
    (hexit : SegExitSpecExt img C A ctl uuidTryParse S ext) :
    region_ok (tripleRatchetProgAtExt img.base ext) (recordRegionEntry img) (recordRegionExit img)
      (recordDecryptSpec C A ctl uuidTryParse S img) := by
  apply region_ok_of_reaches
  intro x R s0 hpc hst hpre hL
  have hstk := rootStack_le_of_recordPre hpre
  have hJ : ∀ s, JState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAtExt img.base ext) (recordDecryptSpec C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := fun s hs hLs => hexit hloads hhooks x R s0 s hs hLs
  have hF : ∀ s, FState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAtExt img.base ext) (recordDecryptSpec C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x R s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone hloads hhooks hc.chainClone hc.senderClone x R s0 hpc hst hpre hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ := hdec hloads hhooks htd hc.setState hc.dropLocal2 hc.growSpe
      hc.closure x G₁ R s0 s' hv hstk (hst'.codeLoaded hL)
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

/-- `region_ok` of a restricted contract from `region_reaches` of the contract at every entry
state meeting the restriction. -/
theorem region_ok_restrictPre_of_reaches {α : Type} {prog : Program} {entry exit : BitVec 64}
    {spec : Spec α} {P : α → Prop}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), P x → s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → region_reaches prog spec exit x R s0 s0) :
    region_ok prog entry exit (spec.restrictPre P) := by
  refine Spec.region_ok_restrictPre_of fun x R s0 hP hpc hst hpre hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc', hrun', _, hpost⟩ | hpan⟩ := h x R s0 hP hpc hst hpre hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc', hrun', hpost⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- `region_ok` of `(spec.withVRegs).restrictPre P` from `region_reaches` of `spec`. -/
theorem region_ok_withVRegs_restrictPre_of_reaches {α : Type} {prog : Program}
    {entry exit : BitVec 64} {spec : Spec α} {P : α → Prop}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), P x → s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → region_reaches prog spec exit x R s0 s0) :
    region_ok prog entry exit (spec.withVRegs.restrictPre P) := by
  refine Spec.region_ok_restrictPre_of fun x R s0 hP hpc hst hpre hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ := h x R s0 hP hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Composes the five segment specifications into `region_ok` (preserving `calleeSavedVRegs`) on PQ states satisfying `Q`. -/
theorem recordDecrypt_region_vregs_ok_of_seams {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : RecordCallees img C A ctl abs)
    (htd : TryDecryptOkAtImageBase Q img C A ctl uuidTryParse S abs)
    (hclone : SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : SegDecryptSpec Q img C A ctl uuidTryParse S abs)
    (hmis : SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : SegExitSpec img C A ctl uuidTryParse S abs) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)) := by
  apply region_ok_withVRegs_restrictPre_of_reaches
  intro x R s0 hQ hpc hst hpre hL
  have hstk := rootStack_le_of_recordPre hpre
  have hJ : ∀ s, JState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (recordDecryptSpec C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := fun s hs hLs => hexit hloads hhooks x R s0 s hs hLs
  have hF : ∀ s, FState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (recordDecryptSpec C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := by
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

/-- Composes the five segment specifications into `region_ok` on PQ states satisfying `Q` with spatial frame `F`. -/
theorem recordDecrypt_region_ok_of_seamsQF {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)} {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : RecordCallees img C A ctl abs)
    (htd : TryDecryptOkAtImageBaseQF Q F img C A ctl uuidTryParse S abs)
    (hclone : SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : SegDecryptSpecQF Q F img C A ctl uuidTryParse S abs)
    (hmis : SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : SegExitSpec img C A ctl uuidTryParse S abs) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      (recordDecryptSpecQF Q F C A ctl uuidTryParse S img) := by
  apply region_ok_of_reaches
  intro x R s0 hpc hst hpre hL
  dsimp only [recordDecryptSpecQF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ (F ∗ R) :=
    Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpre
  have hstk := rootStack_le_of_recordPre hpre'
  have hJ : ∀ s, JState C A ctl uuidTryParse S img x (F ∗ R) s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs)
        (recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨sf, hstf, hout⟩ := hexit hloads hhooks x (F ∗ R) s0 s hs hLs
    exact ⟨sf, hstf, regionOutcome_recordDecryptSpecQF hout⟩
  have hF : ∀ s, FState C A ctl uuidTryParse S img x (F ∗ R) s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs)
        (recordDecryptSpecQF Q F C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hnext⟩ := htail hloads hhooks hc.dropLocal2 x (F ∗ R) s0 s hs hLs
    rcases hnext with hj | hout
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', regionOutcome_recordDecryptSpecQF hout⟩
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
    · exact ⟨s'', hst'.trans hst'', regionOutcome_recordDecryptSpecQF hout⟩
  · exact ⟨s', hst', regionOutcome_recordDecryptSpecQF hout⟩

/-- Composes the five segment specifications into `region_ok` on PQ states satisfying `Q`. -/
theorem recordDecrypt_region_ok_of_seams {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    {img : Obj.Image}
    (hloads : Obj.Loads libsignalSessionImage img) (hhooks : TripleRatchetHooks C A S abs)
    (hc : RecordCallees img C A ctl abs)
    (htd : TryDecryptOkAtImageBase Q img C A ctl uuidTryParse S abs)
    (hclone : SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : SegDecryptSpec Q img C A ctl uuidTryParse S abs)
    (hmis : SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : SegExitSpec img C A ctl uuidTryParse S abs) :
    region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      ((recordDecryptSpec C A ctl uuidTryParse S img).restrictPre (Q ·.st.pqRatchetState)) := by
  apply region_ok_restrictPre_of_reaches
  intro x R s0 hQ hpc hst hpre hL
  have hstk := rootStack_le_of_recordPre hpre
  have hJ : ∀ s, JState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (recordDecryptSpec C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := fun s hs hLs => hexit hloads hhooks x R s0 s hs hLs
  have hF : ∀ s, FState C A ctl uuidTryParse S img x R s0 s →
      region_reaches (tripleRatchetProgAt img.base C ctl abs) (recordDecryptSpec C A ctl uuidTryParse S img)
        (recordRegionExit img) x R s0 s := by
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

/-- Composes the five segment specifications into `RecordDecryptRunStmt` (`Q := fun _ => True`). -/
theorem recordDecrypt_run_of_seams (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      RecordCallees img C A ctl abs)
    (htry : TryDecryptRunStmt C A ctl S abs img)
    (hclone : SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : SegDecryptSpec (fun _ => True) img C A ctl uuidTryParse S abs)
    (hmis : SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : SegExitSpec img C A ctl uuidTryParse S abs) :
    RecordDecryptRunStmt C A ctl S abs img := by
  intro hhooks hrecv hloads
  have h : region_ok (tripleRatchetProgAt img.base C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      ((recordDecryptSpec C A ctl uuidTryParse S img).restrictPre (fun _ => True)) :=
    recordDecrypt_region_ok_of_seams hloads hhooks (hcallees hhooks hloads)
      (tryDecryptOkAtImageBase_of_run htry hhooks hrecv hloads) hclone hdec hmis htail hexit
  rw [Spec.restrictPre_true] at h
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact h

/-- Composes the five segment specifications into `RecordDecryptEmptyRunStmt` (`Q := (· = [])`). -/
theorem recordDecryptEmpty_run_of_seams (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      RecordCallees img C A ctl abs)
    (htry : TryDecryptEmptyRunStmt C A ctl S abs img)
    (hclone : SegCloneSpec img C A ctl uuidTryParse S abs)
    (hdec : SegDecryptSpec (· = []) img C A ctl uuidTryParse S abs)
    (hmis : SegMismatchSpec img C A ctl uuidTryParse S abs)
    (htail : SegTailSpec img C A ctl uuidTryParse S abs)
    (hexit : SegExitSpec img C A ctl uuidTryParse S abs) :
    RecordDecryptEmptyRunStmt C A ctl S abs img := by
  intro hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact recordDecrypt_region_ok_of_seams hloads hhooks (hcallees hhooks hloads)
    (tryDecryptOktripleRatchetProgAt_of_emptyRun htry hhooks hempty hloads) hclone hdec hmis htail hexit

/-- Composes the five segment specifications into `RecordDecryptV1RunStmt` (`Q := (·.length < 2 ^ 32)`, `F := TokenInit img`). -/
theorem recordDecryptV1_run_of_seams (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
      Obj.Loads libsignalSessionImage img → RecordCallees img C A ctl abs)
    (htry : LibsignalSpqrV1.TryDecryptV1RunStmt C A ctl K abs img)
    (hclone : SegCloneSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hdec : SegDecryptSpecQF (·.length < 2 ^ 32) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hmis : SegMismatchSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (htail : SegTailSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hexit : SegExitSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    LibsignalSpqrV1.RecordDecryptV1RunStmt C A ctl K abs img := by
  intro hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact recordDecrypt_region_ok_of_seamsQF hloads hhooks (hcallees hhooks hloads)
    (tryDecryptOkAtImageBaseQF_of_v1Run htry hhooks hspqr hloads) hclone hdec hmis htail hexit

/-! ## Relocatable `[LibsignalPlacement]` seam definitions and composition -/

/-- Both unmutated code blocks (`LibsignalCodeLoaded`) and `.rodata` (`LibsignalRoLoaded`) are
loaded in `m`. Preserved across `KeepsFrozen` transitions and implied by `LibsignalFrozen`. -/
def LibsignalCodeRoLoaded (pl : Obj.MultiPlacement) (m : Memory) : Prop :=
  LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m

theorem LibsignalCodeRoLoaded.of_keepsFrozen {pl : Obj.MultiPlacement} {m m' : Memory}
    (h : LibsignalCodeRoLoaded pl m) (hk : m.KeepsFrozen m') : LibsignalCodeRoLoaded pl m' :=
  ⟨h.1.of_keepsFrozen hk, libsignalRoLoaded_of_keepsFrozen h.2 hk⟩

theorem LibsignalCodeRoLoaded.of_libsignalFrozen {pl : Obj.MultiPlacement} {m : Memory}
    (h : LibsignalFrozen pl m) : LibsignalCodeRoLoaded pl m :=
  ⟨LibsignalCodeLoaded.of_codeLoaded h.2, h.1⟩

theorem ls_externAt?_226 [LibsignalPlacement] {H : LibsignalHooks} {sym : String}
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    ((blkPC_197).rebase (blkPl_197).base H).externAt? (lsmpl.ρ sym) = H sym := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by rw [List.getElem?_eq_getElem hlt, hk])

theorem ls_hook_ok_226 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hmem : sym ∈ libsignalSessionExterns := by decide) (h : HookSat H sym spec) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.ρ sym) spec := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) h

abbrev recEntryPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 0x1a8#64
abbrev recVPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 0x69c#64
abbrev recMPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 0x7e4#64
abbrev recFPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 0x850#64
abbrev recJPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 0x1e8c#64
abbrev recExitPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_197).base + 0x1f50#64

def recMetaPlaced [LibsignalPlacement] (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp ∧ s.spAligned = true ∧
    s.readReg64 .x29 = s0.readReg64 .x29 ∧ s.trace = s0.trace ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧ calleeSavedVRegs s = calleeSavedVRegs s0

def recFramePlaced [LibsignalPlacement] (A : RustAlloc) (x : RecordDecryptGhost) (sp : BitVec 64) :
    SepProp :=
  memRegion sp 0x80 ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  memRegion (sp + 0x5f0#64) 0x6b0 ∗ memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool

def tryDecryptPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
      s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
      (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
      x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
      x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
    sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
    memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
    stackAt s.sp rootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
    (∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidParse).1.toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.model C S uuidParse).2) ∗
    vecResultAt A x.ret (x.model C S uuidParse).1 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
    FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool
  onPanic := fun x s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.recvPanics x.st.pqRatchetState x.msg.pqRatchet ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def recordDecryptPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec RecordDecryptGhost where
  pre := fun x s =>
    ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
    ⌜s.spAligned = true ∧ s.readReg64 .x27 = x.sret ∧ s.readReg64 .x19 = x.remA ∧
      s.readReg64 .x23 = s.sp + 0x5f0#64 ∧ s.readReg64 .x24 = s.sp + 0xca0#64 ∧
      x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
      x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
    memRegion s.sp 0xa0 ∗ ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
    ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
    sessionStateAt A (s.sp + 0x138#64) x.G x.st ∗ memRegion (s.sp + 0x4b0#64) 0x950 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗
    tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace ∧ sf.sp = s0.sp ∧
      sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.readReg64 .x27 = x.sret ∧
      sf.readReg64 .x26 = s0.sp + 0xa0#64 ∧
      sf.readReg64 .x28 = recordResultTag (x.model C S uuidParse).1⌝ ∗
    memRegion s0.sp 0xa0 ∗ ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
    ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
    (match (x.model C S uuidParse).1 with
     | .ok _ => ∃∗ G' : SessionGhost, ⌜x.G.AfterRecordDecrypt G'⌝ ∗
         sessionStateAt A (s0.sp + 0x138#64) G' (x.model C S uuidParse).2
     | .error _ => sessionStateAt A (s0.sp + 0x138#64) x.G x.st) ∗
    recordResultAt A (s0.sp + 0x4b0#64) (x.model C S uuidParse).1 ∗
    memRegion (s0.sp + 0x4e0#64) 0x920 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest (x.draws C) ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool
  onPanic := fun x s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def VStatePlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recVPCPlaced ∧ recMetaPlaced s0 s ∧ recPure x ∧ CloneRel x.G G₁ ∧
  x.st.version.toNat = x.msg.messageVersion.toNat ∧
  (s.mem ⊨ recFramePlaced A x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ tapeAt ctl x.cur x.rest ∗ R)

def MStatePlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recMPCPlaced ∧ recMetaPlaced s0 s ∧ x.st.version.toNat ≠ x.msg.messageVersion.toNat ∧
  s.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
  (s.mem ⊨ recFramePlaced A x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ tapeAt ctl x.cur x.rest ∗ R)

def FStatePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (x : RecordDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recFPCPlaced ∧ recMetaPlaced s0 s ∧
  (x.model C S parse).1 = .error (.invalidMessage .whisper .decryptionFailed) ∧
  (s.mem ⊨ recFramePlaced A x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    (∃∗ G₂ : SessionGhost, ∃∗ st₂ : SessionState (List (BitVec 8)), sessionStateAt A (sp + 0xca0#64) G₂ st₂) ∗
    (∃∗ r : RecErr, errsAt A (sp + 0x5d8#64) [r]) ∗ memRegion (sp + 0x4b0#64) 48 ∗
    tapeAfter ctl x.cur x.rest (x.draws C) ∗ R)

def JStatePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (x : RecordDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recJPCPlaced ∧ recMetaPlaced s0 s ∧ (x.model C S parse).1 ≠ .error .panic ∧
  s.readReg64 .x26 = sp + 0xa0#64 ∧ s.readReg64 .x27 = x.sret ∧
  s.readReg64 .x28 = recordResultTag (x.model C S parse).1 ∧
  (s.mem ⊨ recFramePlaced A x sp ∗
    (match (x.model C S parse).1 with
     | .ok _ => ∃∗ G' : SessionGhost, ⌜x.G.AfterRecordDecrypt G'⌝ ∗ sessionStateAt A (sp + 0x138#64) G' (x.model C S parse).2
     | .error _ => sessionStateAt A (sp + 0x138#64) x.G x.st) ∗
    recordResultAt A (sp + 0x4b0#64) (x.model C S parse).1 ∗
    (∃∗ errs : List RecErr, errsAt A (sp + 0x5d8#64) errs) ∗ memRegion (sp + 0xca0#64) 344 ∗
    tapeAfter ctl x.cur x.rest (x.draws C) ∗ R)

def SegClonePlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustNoAllocShimSym sessionShimSpec →
  HookSat H lsRustAllocSym (rustAllocSpec A) →
  HookSat H lsRustDeallocSym (rustDeallocSpec A) →
  HookSat H "memcpy" sessionMemcpyRegionSpec →
  H lsHandleErrorSym = some Rust.panicked →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161) (withLsCodeLoaded lsmpl (FromRecordChainClone.chainCloneSpec A)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161) (withLsCodeLoaded lsmpl (FromRecordChainClone.senderChainCloneSpec A)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 6) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A)) →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced → s0.status = .Running →
      (s0.mem ⊨ (recordDecryptPlacedSpec C A ctl parse S).pre x s0 ∗ R) →
      ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s0.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s0 s' ∧
        ((∃ G₁, VStatePlaced A ctl x G₁ R s0 s') ∨ (∃ G₁, MStatePlaced A ctl x G₁ R s0 s') ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegDecryptPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H "memcpy" sessionMemcpyRegionSpec →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131) (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A ctl parse S)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48) (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42) (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159) (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec) →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      VStatePlaced A ctl x G₁ R s0 s → rootStack ≤ s0.sp.toNat →
      ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
        (JStatePlaced C A ctl parse S x R s0 s' ∨ FStatePlaced C A ctl parse S x R s0 s' ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegMismatchPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42) (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159) (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec) →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      MStatePlaced A ctl x G₁ R s0 s → ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
        (FStatePlaced C A ctl parse S x R s0 s' ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegTailPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustNoAllocShimSym sessionShimSpec →
  HookSat H lsRustAllocSym (rustAllocSpec A) →
  H lsHandleErrorSym = some Rust.panicked →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)) →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      FStatePlaced C A ctl parse S x R s0 s → ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
        (JStatePlaced C A ctl parse S x R s0 s' ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegExitPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustDeallocSym (rustDeallocSpec A) →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      JStatePlaced C A ctl parse S x R s0 s → ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
        regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s'

theorem rootStack_le_of_recordPlacedPre [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {x : RecordDecryptGhost}
    {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (recordDecryptPlacedSpec C A ctl parse S).pre x s0 ∗ R) :
    rootStack ≤ s0.sp.toNat := by
  simp only [recordDecryptPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2.1.2.2.2.2.2.2.2.2

theorem recordDecrypt_placed_region_ok_of_seams [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161) (withLsCodeLoaded lsmpl (FromRecordChainClone.chainCloneSpec A)))
    (hsc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161) (withLsCodeLoaded lsmpl (FromRecordChainClone.senderChainCloneSpec A)))
    (hdrop1 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 6) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A)))
    (htd : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131) (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A ctl parse S)))
    (hset : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48) (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)))
    (hdrop2 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)))
    (hgrow : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42) (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)))
    (hclosure : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159) (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec))
    (hclone : SegClonePlacedSpec C A ctl parse S H)
    (hdec : SegDecryptPlacedSpec C A ctl parse S H)
    (hmis : SegMismatchPlacedSpec C A ctl parse S H)
    (htail : SegTailPlacedSpec C A ctl parse S H)
    (hexit : SegExitPlacedSpec C A ctl parse S H) :
    region_ok ((blkPC_197).rebase (blkPl_197).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpec C A ctl parse S) := by
  apply region_ok_of_reaches; intro x R s0 hpc hst hpre hL
  have hstk := rootStack_le_of_recordPlacedPre hpre
  have hJ : ∀ s, JStatePlaced C A ctl parse S x R s0 s →
      region_reaches ((blkPC_197).rebase (blkPl_197).base H)
        (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s :=
    fun s hs hLs => hexit hdealloc x R s0 s hs hLs
  have hF : ∀ s, FStatePlaced C A ctl parse S x R s0 s →
      region_reaches ((blkPC_197).rebase (blkPl_197).base H)
        (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hj | hout⟩ := htail hshim halloc hpanic hdrop2 x R s0 s hs hLs
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout⟩ :=
    hclone hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 x R s0 hpc hst hpre hL
  · obtain ⟨s'', hst'', hj | hf | hout⟩ := hdec hmemcpy htd hset hdrop2 hgrow hclosure x G₁ R s0 s' hv
      hstk (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hf | hout⟩ := hmis hgrow hclosure x G₁ R s0 s' hm (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · exact ⟨s', hst', hout⟩

end CryptoVerification.LibsignalTripleRatchet.Record
