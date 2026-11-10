/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.RatchetDecryptCodeSym
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Seam States and Segment Specifications for CLI `try_decrypt_from_record`

Defines the `[LibsignalPlacement]` code/`.rodata` invariant `LibsignalCodeRoLoaded`, seam PCs,
checkpoint states, segment specifications, and seam composition on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record hiding LibsignalCodeRoLoaded ls_externAt?_226 ls_hook_ok_226 recEntryPlaced recVPCPlaced recMPCPlaced recFPCPlaced recJPCPlaced recExitPlaced recMetaPlaced recFramePlaced tryDecryptPlacedSpec recordDecryptPlacedSpec VStatePlaced MStatePlaced FStatePlaced JStatePlaced SegClonePlacedSpec SegDecryptPlacedSpec SegMismatchPlacedSpec SegTailPlacedSpec SegExitPlacedSpec rootStack_le_of_recordPlacedPre recordDecrypt_placed_region_ok_of_seams
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.Cli.CoinsTape

noncomputable abbrev lsProg_463 [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  CryptoVerification.CliRatchet.DecPlaced.lsProg_463 H

/-! ## Relocatable Seam Definitions and Composition -/

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
    ((blkPC_463).rebase (blkPl_463).base H).externAt? (lsmpl.ρ sym) = H sym := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by rw [List.getElem?_eq_getElem hlt, hk])

theorem ls_hook_ok_226 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hmem : sym ∈ libsignalSessionExterns := by decide) (h : HookSat H sym spec) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.ρ sym) spec := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) h

abbrev recEntryPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 0x1a8#64
abbrev recVPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 0x69c#64
abbrev recMPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 0x7e4#64
abbrev recFPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 0x850#64
abbrev recJPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 0x1e8c#64
abbrev recExitPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 0x1f50#64

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
    memRegion x.ret 48 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
    stackAt s.sp rootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
    (∃∗ G' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidParse).1.toBool G'⌝ ∗
      sessionStateAt A x.ss G' (x.model C S uuidParse).2) ∗
    vecResultAt A x.ret (x.model C S uuidParse).1 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗
    cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
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
    cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool
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
    cliTapeAfter ctl x.cur x.rest (x.draws C) ∗ FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool
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
    memRegion (sp + 0x4b0#64) 48 ∗ cliTapeAt ctl x.cur x.rest ∗ R)

def MStatePlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : RecordDecryptGhost)
    (G₁ : SessionGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recMPCPlaced ∧ recMetaPlaced s0 s ∧ x.st.version.toNat ≠ x.msg.messageVersion.toNat ∧
  s.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
  (s.mem ⊨ recFramePlaced A x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    sessionStateAt A (sp + 0xca0#64) G₁ x.st ∗ errsAt A (sp + 0x5d8#64) [] ∗
    memRegion (sp + 0x4b0#64) 48 ∗ cliTapeAt ctl x.cur x.rest ∗ R)

def FStatePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (x : RecordDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp
  s.pc = recFPCPlaced ∧ recMetaPlaced s0 s ∧
  (x.model C S parse).1 = .error (.invalidMessage .whisper .decryptionFailed) ∧
  (s.mem ⊨ recFramePlaced A x sp ∗ sessionStateAt A (sp + 0x138#64) x.G x.st ∗
    (∃∗ G₂ : SessionGhost, ∃∗ st₂ : SessionState (List (BitVec 8)), sessionStateAt A (sp + 0xca0#64) G₂ st₂) ∗
    (∃∗ r : RecErr, errsAt A (sp + 0x5d8#64) [r]) ∗ memRegion (sp + 0x4b0#64) 48 ∗
    cliTapeAfter ctl x.cur x.rest (x.draws C) ∗ R)

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
    cliTapeAfter ctl x.cur x.rest (x.draws C) ∗ R)

def SegClonePlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustNoAllocShimSym sessionShimSpec →
  HookSat H lsRustAllocSym (rustAllocSpec A) →
  HookSat H lsRustDeallocSym (rustDeallocSpec A) →
  HookSat H "memcpy" sessionMemcpyRegionSpec →
  H lsHandleErrorSym = some Rust.panicked →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468) (withLsCodeLoaded lsmpl (FromRecordChainClone.chainCloneSpec A)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468) (withLsCodeLoaded lsmpl (FromRecordChainClone.senderChainCloneSpec A)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A)) →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced → s0.status = .Running →
      (s0.mem ⊨ (recordDecryptPlacedSpec C A ctl parse S).pre x s0 ∗ R) →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s0.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s0 s' ∧
        ((∃ G₁, VStatePlaced A ctl x G₁ R s0 s') ∨ (∃ G₁, MStatePlaced A ctl x G₁ R s0 s') ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegDecryptPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H "memcpy" sessionMemcpyRegionSpec →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434) (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A ctl parse S)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48) (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42) (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462) (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec) →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      VStatePlaced A ctl x G₁ R s0 s → rootStack ≤ s0.sp.toNat →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        (JStatePlaced C A ctl parse S x R s0 s' ∨ FStatePlaced C A ctl parse S x R s0 s' ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegMismatchPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42) (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462) (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec) →
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      MStatePlaced A ctl x G₁ R s0 s → ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        (FStatePlaced C A ctl parse S x R s0 s' ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegTailPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustNoAllocShimSym sessionShimSpec →
  HookSat H lsRustAllocSym (rustAllocSpec A) →
  H lsHandleErrorSym = some Rust.panicked →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)) →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      FStatePlaced C A ctl parse S x R s0 s → ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        (JStatePlaced C A ctl parse S x R s0 s' ∨
          regionOutcome (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s')

def SegExitPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustDeallocSym (rustDeallocSpec A) →
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 s : State),
      JStatePlaced C A ctl parse S x R s0 s → ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
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
    (hcc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468) (withLsCodeLoaded lsmpl (FromRecordChainClone.chainCloneSpec A)))
    (hsc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468) (withLsCodeLoaded lsmpl (FromRecordChainClone.senderChainCloneSpec A)))
    (hdrop1 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A)))
    (htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434) (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A ctl parse S)))
    (hset : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48) (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)))
    (hdrop2 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442) (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)))
    (hgrow : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42) (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462) (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec))
    (hclone : SegClonePlacedSpec C A ctl parse S H)
    (hdec : SegDecryptPlacedSpec C A ctl parse S H)
    (hmis : SegMismatchPlacedSpec C A ctl parse S H)
    (htail : SegTailPlacedSpec C A ctl parse S H)
    (hexit : SegExitPlacedSpec C A ctl parse S H) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpec C A ctl parse S) := by
  apply region_ok_of_reaches; intro x R s0 hpc hst hpre hL
  have hstk := rootStack_le_of_recordPlacedPre hpre
  have hJ : ∀ s, JStatePlaced C A ctl parse S x R s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpec C A ctl parse S) recExitPlaced x R s0 s :=
    fun s hs hLs => hexit hdealloc x R s0 s hs hLs
  have hF : ∀ s, FStatePlaced C A ctl parse S x R s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
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

end CryptoVerification.Cli.LibsignalTripleRatchet.Record
