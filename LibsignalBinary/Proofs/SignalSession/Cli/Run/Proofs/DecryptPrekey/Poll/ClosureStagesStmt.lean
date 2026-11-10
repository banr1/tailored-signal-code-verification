/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitFold
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.Agree -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntry
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Stage P2, P3, and P4 Interface Statements

Defines matched-session Path B Stage P4 spatial predicates (`stageP4MatchedPre`,
`stageP4MatchedExitAt`, `StageP4MatchedBranch`, `StageP4MatchedExtStmt`), shared post-`StageP1`
bundles at `+0x0868`, Path B and Path A Stage P2 contracts (`StageP2MatchedCliStmt`,
`StageP2PathACliStmt`), and the combined `ClosureStagesStmt` bundle.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Path B Stage P4 (`M4`) Spatial Entry/Exit & Three-Way Outcome (`StageP4MatchedBranch`) -/

/-- Unified stack budget for matched-session Path B Stage P4 (`save_identity` + `store_session` +
error unwinds; `mark_kyber_pre_key_used` and `remove_pre_key` are skipped). -/
def stageP4MatchedCallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (saveIdCallStack ikit) (storeSessionCallStack kit)

/-- Shared spatial resources across `P4.1` (`save_identity`) and `P4.4` (`store_session`) on
matched-session Path B (`opkIdIsSome = 2#32`, skipping `P4.2` and `P4.3`). -/
def stageP4MatchedShared {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) :
    SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xb8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xc0#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
  ((coroPtr + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
  ((coroPtr + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2ac#64) 8 ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  logOff img ∗
  A.pool ∗
  stackAt s.sp (stageP4MatchedCallStack kit ikit)

/-- Spatial precondition at `+0x34dc` for matched-session Path B Stage P4 (`M4`). -/
def stageP4MatchedPre {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MatchedShared img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kit.storeAt sessionStorePtr sst0

/-- Spatial postcondition at `s0.readReg64.x30` for matched-session Path B Stage P4 (`M4`),
after `SessionStructure` (`+0xf8`, 344B) and `prevSessionsEmptyAt` (`+0xe0`, 24B + spare `prevPtr`)
have been dropped into `memRegion (coroPtr + 0xe0#64) 368`. -/
def stageP4MatchedExitAt {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (outSlot : SepProp) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sstf : kit.StoreState) (istf : ikit.IdState) : SepProp :=
  stageP4MatchedShared img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk ∗
  outSlot ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr istf ∗
  kit.storeAt sessionStorePtr sstf

/-- Three-way outcome classification of matched-session Path B Stage P4 (`+0x34dc → s0.readReg64.x30`,
`opkIdIsSome = 2#32`, skipping `mark_kyber_pre_key_used` and `remove_pre_key`). -/
inductive StageP4MatchedBranch {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()))
      (hpost : Pf ⊢ stageP4MatchedExitAt img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (vecResultAt A outPtr (.ok pt))
        pt peer remoteIk
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)))
  | saveErr
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4MatchedExitAt img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (savePollOutAt img.base outPtr (.error ()))
        pt peer remoteIk sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())))
  | storeErr (c : IdentityChange)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()))
      (hpost : Pf ⊢ stageP4MatchedExitAt img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (storePollOutAt img.base outPtr (.error ()))
        pt peer remoteIk
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)))

/-- Path B Stage P4 (`+0x34dc → s0.readReg64.x30`) for `opkIdIsSome = 2#32`:
runs `P4.1` (`save_identity`), skips `P4.2` and `P4.3`, runs `P4.4` (`store_session`), and drops
both `SessionStructure` (`+0xf8`, 344B) and `prevSessionsEmptyAt A coroPtr g` (`+0xe0`, 24B + spare
`prevPtr`) into `memRegion (coroPtr + 0xe0#64) 368`. -/
def StageP4MatchedExtStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base),
    AllocContracts img.base A ext →
    DropSessionStructure3OkExt img.base A ext →
    SessionOnlyKitOkSE kit Scope encRecord ext →
    SessionOnlyVtablesOk img kit →
    IdentityStoreKitOkIE img ikit ext →
    IdentityVtablesOk img ikit →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
      (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (peer : AddrGhost) (remoteIk : IdentityKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))),
      img.base &&& 0xfff#64 = 0#64 →
      SessionExtraRel G ss →
      kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      pt.length ≤ ptCap.toNat →
      ptCap.toNat < 2 ^ 63 →
      ptPtr ≠ 0#64 →
      stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
      FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
        (tripleRatchetProgAtExt img.base ext) s →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
        Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr →
      s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (stageP4MatchedPre img kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk
          sst0 ist0 g G ss.state)
        (fun sf Pf =>
          Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          StageP4MatchedBranch img kit ikit encRecord s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
            ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk
            sst0 ist0 ss sf Pf)
        (PanicOomProp s0)

/-! ## 2. Shared `+0x0868` Post-`StageP1` Bundle & `loadRec` Empty-Session Lemma -/

/-- Because `E2E.Record.encodeRecord ⟨none⟩ = []`, `Slots.loadRec Scope F peer =.ok opt` with
`opt.bind (·.currentSession) = none` forces `opt = none` (never `some ⟨none⟩`). -/
theorem opt_eq_none_of_loadRec_cur_none {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {opt : Option (SessionRecord (List (BitVec 8)))}
    (hload : Slots.loadRec Scope F peer = .ok opt)
    (hcur : opt.bind (·.currentSession) = none) :
    opt = none := by
  cases opt with
  | none => rfl
  | some r =>
    have hr : r = ⟨none⟩ := by cases r; simpa using hcur
    subst hr
    unfold Slots.loadRec at hload
    rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with
      _ | (_ | ⟨b, bs⟩) <;> rw [hget] at hload <;> dsimp only at hload
    · cases hload
    · cases hload
    · split at hload
      · rename_i hex
        simp only [Except.ok.injEq, Option.some.injEq] at hload
        have henc := (Classical.choose_spec hex).1
        have hnil : E2E.Record.encodeRecord (⟨none⟩ : SessionRecord (List (BitVec 8))) = [] := rfl
        rw [hload, hnil] at henc
        cases henc
      · cases hload

/-- Canonical coroutine + stack spatial bundle at `+0x0868` immediately after `StageP1OkExtStmt`,
shared by both Path B (`StageP2MatchedCliStmt`) and Path A (`StageP2PathACliStmt`). -/
def stageP2PostP1At (A : RustAlloc)
    (coroPtr outPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr sessVt idStorePtr idVt
     preKeyStorePtr preKeyVt spkStorePtr spkVt
     kyberStorePtr kyberVt rngPtr
     sp v_a8 v_b8 v_d0 : BitVec 64) (s0 : State) : SepProp :=
  decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
  processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr preKeyVt
    spkStorePtr spkVt kyberStorePtr kyberVt ∗
  processPrekeyPostTrustAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr preKeyVt
    spkStorePtr spkVt kyberStorePtr kyberVt ∗
  ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
  cells (coroPtr + 0x398#64) 2 ∗
  ((coroPtr + 0x4f2#64) ↦₈ 0#8) ∗
  memRegion (coroPtr + 0x250#64) 48 ∗
  coroUnusedP1At coroPtr ∗
  (sp ↦₆₄ 0#64) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
  ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  memRegion (sp + 0xd8#64) 348 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  closStackUnusedP1OkAt sp ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  A.pool

/-- Stack slots in `[sp.. sp + 0xc70)` framed untouched across Stage P3 (`+0x1778 → +0x34dc`)
and consumed by Stage P4 (`+0x34dc → x30`) and `clos_stack_3280_of_regions`. -/
def stageP3StackFrameAt (sp remoteIkPtr remAddrPtr : BitVec 64) : SepProp :=
  (sp ↦₆₄ 0#64) ∗
  spLowGapsAt sp ∗
  ((sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((sp + 0xa8#64) ↦₆₄ remAddrPtr) ∗
  memRegion (sp + 0xbc#64) 4 ∗
  memRegion (sp + 0xd8#64) 376 ∗
  memRegion (sp + 0x264#64) 12 ∗
  memRegion (sp + 0x2a0#64) 16 ∗
  memRegion (sp + 0x2b0#64) 192 ∗
  memRegion (sp + 0x394#64) 12 ∗
  memRegion (sp + 0x3a8#64) 4 ∗
  memRegion (sp + 0x3ad#64) 27 ∗
  memRegion (sp + 0x538#64) 24 ∗
  spHighGapsAt sp

/-- Coroutine regions in `[coroPtr.. coroPtr + 2008)` framed untouched across Stage P3
(`+0x1778 → +0x34dc`) and consumed by Stage P4 (`+0x34dc → x30`) and `coro_regions_entails_dpFutDoneAt`. -/
def stageP3CoroFrameAt
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr sessVt idStorePtr idVt
     preKeyStorePtr preKeyVt spkStorePtr spkVt
     kyberStorePtr kyberVt rngPtr : BitVec 64)
    (opkSlot coro2a0Slot : SepProp) : SepProp :=
  decryptPrekeyCoroInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  decryptPrekeyCoroCopyAt coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessVt idStorePtr idVt
    preKeyStorePtr preKeyVt spkStorePtr spkVt
    kyberStorePtr kyberVt rngPtr ∗
  memRegion (coroPtr + 0x250#64) 48 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  opkSlot ∗
  coro2a0Slot ∗
  memRegion (coroPtr + 0x2ac#64) 8 ∗
  memRegion (coroPtr + 0x2b4#64) 12 ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  memRegion (coroPtr + 0x2d8#64) 184 ∗
  memRegion (coroPtr + 0x390#64) 1 ∗
  memRegion (coroPtr + 0x398#64) 16 ∗
  memRegion (coroPtr + 0x428#64) 64 ∗
  memRegion (coroPtr + 0x468#64) 40 ∗
  memRegion (coroPtr + 0x490#64) 32 ∗
  memRegion (coroPtr + 0x4f2#64) 1 ∗
  coroPostP2UnusedAt coroPtr

/-! ## 3. Path B Stage P2 Statement (`StageP2MatchedCliStmt`) -/

/-- Exact register state guaranteed by `StageP1OkExtStmt` at `+0x0868#64`. -/
def StageP1PostRegs (s0 s1 : State) (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt : BitVec 64) : Prop :=
  s1.readReg64 .x8 = kyberStorePtr ∧
  s1.readReg64 .x9 = msgPtr ∧
  s1.readReg64 .x10 = kyberStoreVt ∧
  s1.readReg64 .x11 = preKeyStorePtr ∧
  s1.readReg64 .x12 = remoteAddrPtr ∧
  s1.readReg64 .x13 = preKeyStoreVt ∧
  s1.readReg64 .x14 = localAddrPtr ∧
  s1.readReg64 .x15 = idStorePtr ∧
  s1.readReg64 .x16 = idStoreVt ∧
  s1.readReg64 .x17 = coroPtr + 0x4f2#64 ∧
  s1.readReg64 .x19 = coroPtr ∧
  s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
  s1.readReg64 .x22 = spkStorePtr ∧
  s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
  s1.readReg64 .x24 = spkStoreVt ∧
  s1.readReg64 .x25 = sp + 0x210#64 ∧
  s1.readReg64 .x28 = sp + 0xa90#64 ∧
  s1.readReg64 .x29 = s0.sp - 0x60#64 ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s0

/-- CPS Stage P2 contract for Path B (`opt = some ⟨some sess⟩`) at `+0x0868`:
either exits to `s0.readReg64.x30` with `BadCiphertext` when
`sess.state.remoteIdentity ≠ some y.g.msg.identityKey`, or advances to `+0x1778` when
`sess.state.remoteIdentity = some y.g.msg.identityKey`. -/
def StageP2MatchedCliStmt : Prop :=
  ∀ (W : CliHooks) (img : Obj.Image) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    RunHooks img E2E.HooksE.A0 (cliExterns W) →
    img.base &&& 0xfff#64 = 0#64 →
    SessMatchesPm sess y.g.msg →
    ImgCallInv img s1 →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    rootStack ≤ sp.toNat →
    s1.pc = closureEntry img (cliExterns W) + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (hmismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ sf Pf,
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 sf →
        sf.sp = s0.sp →
        sf.trace = s1.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        ImgCallInv img sf →
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt E2E.HooksE.A0 y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          coinsInstalled img y.g.coinsP y.g.coins ∗
          TokenInit img ∗
          logOff img ∗
          E2E.HooksE.A0.pool ∗
          stackAt sp rootStack) →
        Q sf Pf) →
    (hmatch : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ (s2 : State) (g : RecordGhost) (recG : SessionGhost)
        (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
        (preKeyMsgRem : SepProp)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        SessionExtraRel recG sess →
        (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ⊢
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) →
        Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 s2 →
        s2.pc = closureEntry img (cliExterns W) + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s1.trace →
        s2.readReg64 .x19 = y.fut →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = s0.sp - 0x60#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s0 →
        ImgCallInv img s2 →
        SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2
          (TokenInit img ∗
           genP3Pre E2E.HooksE.A0 img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
             whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
             recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
           stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
           stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
             (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
             (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
             (y.g.stores + 0x78#64) (kyberVt img) rngPtr
             (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
             (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
              ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
              memRegion (y.fut + 0x2a8#64) 4) ∗
           stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
           ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
           preKeyMsgRem)
          Q (PanicOomProp s0)) →
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1
      (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Scope E2E.HooksE.A0 y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp rootStack)
      Q (PanicOomProp s0)

/-! ## 4. Path A Stage P2 Statement (`StageP2PathACliStmt`) & Combined `ClosureStagesStmt` -/

/-- Outcome of the 6 Stage P2 error exits on Path A (`+0x0868 → s0.readReg64.x30`):
all 6 CLI store/key/crypto error paths preserve `sf.trace = s1.trace`, keep the stores intact at
`StoresGhost.opened`, satisfy `decPkDef = some none`, and emit a `SpeOwned` error (`err ≠.panic`,
`err ≠.store ()`). -/
inductive StageP2PathAErr (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 s1 sf : State) (sp : BitVec 64) (Pf : SepProp) : Prop where
  | reject (err : ApiError AddrVal Unit)
      (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
      (htr : sf.trace = s1.trace)
      (hmodel : decPkDef X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins =
        some none)
      (hpost : Pf ⊢
        dpFutDoneAt y.fut ∗
        memRegion sp 3280 ∗
        decResAt E2E.HooksE.A0 y.out (.error err) ∗
        storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        logOff img ∗
        E2E.HooksE.A0.pool ∗
        stackAt sp (dpClosSubStack B) ∗
        anyHeap)

/-- CPS Stage P2 contract for Path A (`opt = none`, `DecPkOk₀`) at `+0x0868`:
either exits to `s0.readReg64.x30` via `StageP2PathAErr`, or advances to `+0x1778` with the
promoted initial Bob session `pathAInitSession`. -/
def StageP2PathACliStmt : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (g1 : StoresGhost)
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    RunHooks img E2E.HooksE.A0 (cliExterns W) →
    img.base &&& 0xfff#64 = 0#64 →
    DecPkOk₀ ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg →
    g1 = StoresGhost.opened →
    FsAt (fun f => f = y.g.F) True
      (tripleRatchetProgAtExt img.base (cliExterns W)) s1 →
    ImgCallInv img s1 →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    dpClosSubStack B ≤ sp.toNat →
    s1.pc = closureEntry img (cliExterns W) + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (herr : ∀ sf Pf,
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 sf →
      sf.sp = s0.sp →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      StageP2PathAErr X W img B S Scope y s0 s1 sf sp Pf →
      Q sf Pf) →
    (hok : ∀ (s2 : State)
      (m : PreKeyMessageFields) (i : SignalMessage)
      (k : ResponderPreKeySecrets)
      (kp : RecordCodecs.IdentityKeyPair) (reg : BitVec 32)
      (dk : SignalPqxdh.DRKey)
      (recG : SessionGhost)
      (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
      (preKeyMsgRem : SepProp),
      y.g.msg = pmOfE m i →
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner = .ok i →
      pkStoreKeys y.g.F m = some k →
      StoresGhost.opened.identity.keyPair cliIo.rd y.g.F = .ok kp →
      StoresGhost.opened.identity.regId cliIo.rd y.g.F = .ok reg →
      SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
        (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk →
      SessionExtraRel recG
        (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) →
      (signalMessageAt E2E.HooksE.A0 whisperG whisperMsgPtr y.g.msg.message ∗
        ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
        ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
        preKeyMsgRem ⊢
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg) →
      Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s1 s2 →
      s2.trace = s1.trace →
      s2.pc = closureEntry img (cliExterns W) + 0x1778#64 →
      s2.status = .Running →
      s2.sp = sp →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.readReg64 .x19 = y.fut →
      s2.readReg64 .x27 = sp + 0x370#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      ImgCallInv img s2 →
      SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s2
        (TokenInit img ∗
         genP3Pre E2E.HooksE.A0 img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
           whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
           recG (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk)
           y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
         stageP3Sub5ExtraPre s0 s2 y.fut y.out 8#64 8#64 0#8 ∗
         stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
           (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
           (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
           (y.g.stores + 0x78#64) (kyberVt img) rngPtr
           (coroOpkIdAtP4 y.fut m.opkId)
           (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
            ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
         stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
         ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
         ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
         preKeyMsgRem ∗
         storesAt E2E.HooksE.A0 y.g.stores g1 ∗
         memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack))
        Q (PanicOomProp s0)) →
    SepWPp (tripleRatchetProgAtExt img.base (cliExterns W)) (s0.readReg64 .x30) s1
      (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Scope E2E.HooksE.A0 y.fut none ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores g1 ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B))
      Q (PanicOomProp s0)

/-- Combined bundle of stage contracts parameterizing `cliDpPollOk_state_of_stages`. -/
structure ClosureStagesStmt : Prop where
  stageP1Ok : StageP1OkExtStmt
  stageP1Untrusted : StageP1UntrustedExtStmt
  stageP2Matched : StageP2MatchedCliStmt
  stageP3PrevEmpty : StageP3PrevEmptyVRegsStmt
  stageP4Matched : StageP4MatchedExtStmt
  stageP2PathA : StageP2PathACliStmt

/-! ## 5. Contract-Parameterized `(P, A, ext)` Stage P4 (`AllocContractsX`) & Stage P2 Variants -/

/-- `AllocHooks` counterpart of `StageP4MatchedExtStmt` for `(P, A, ext)` under `CliExternsOk P A ext`. -/
def StageP4MatchedXExtStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base),
    AllocHooks A ext →
    DropSessionStructure3OkExt img.base A ext →
    SessionOnlyKitOkSE kit Scope encRecord ext →
    SessionOnlyVtablesOk img kit →
    IdentityStoreKitOkIE img ikit ext →
    IdentityVtablesOk img ikit →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
      (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (peer : AddrGhost) (remoteIk : IdentityKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))),
      img.base &&& 0xfff#64 = 0#64 →
      SessionExtraRel G ss →
      kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      pt.length ≤ ptCap.toNat →
      ptCap.toNat < 2 ^ 63 →
      ptPtr ≠ 0#64 →
      stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
      FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
        (tripleRatchetProgAtExt img.base ext) s →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
        Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x34dc#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr →
      s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (stageP4MatchedPre img kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk
          sst0 ist0 g G ss.state)
        (fun sf Pf =>
          Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          StageP4MatchedBranch img kit ikit encRecord s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
            ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk
            sst0 ist0 ss sf Pf)
        (PanicOomProp s0)

/-- CPS Stage P2 contract for Path B (`opt = some ⟨some sess⟩`) at `+0x0868` generalized to
arbitrary `(P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))` under
`CliExternsOk P A ext` and `RunHooksExt img A (cliExternsWith ext)`. -/
def StageP2MatchedExtStmt : Prop :=
  ∀ (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (_ : CliExternsOk P A ext)
    (img : Obj.Image) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (sess : Session (List (BitVec 8)))
    (s0 s1 : State) (sp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (Q : State → SepProp → Prop),
    Obj.Loads libsignalSessionImage img →
    RunHooksExt img A (cliExternsWith ext) →
    img.base &&& 0xfff#64 = 0#64 →
    SessMatchesPm sess y.g.msg →
    ImgCallInv img s1 →
    s0.trace <+: s1.trace →
    s1.sp = sp →
    sp + 0xcd0#64 = s0.sp →
    rootStack ≤ sp.toNat →
    s1.pc = closureEntry img (cliExternsWith ext) + 0x0868#64 →
    s1.status = .Running →
    (s1.sp &&& 15#64 == 0#64) = true →
    StageP1PostRegs s0 s1 sp y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) →
    (hmismatch : sess.state.remoteIdentity ≠ some y.g.msg.identityKey →
      ∀ sf Pf,
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        Steps (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s1 sf →
        sf.sp = s0.sp →
        sf.trace = s1.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        ImgCallInv img sf →
        (Pf ⊢
          dpFutDoneAt y.fut ∗
          memRegion sp 3280 ∗
          apiDecResultAt A y.out
            (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          coinsInstalled img y.g.coinsP y.g.coins ∗
          TokenInit img ∗
          logOff img ∗
          A.pool ∗
          stackAt sp rootStack) →
        Q sf Pf) →
    (hmatch : sess.state.remoteIdentity = some y.g.msg.identityKey →
      ∀ (s2 : State) (g : RecordGhost) (recG : SessionGhost)
        (whisperMsgPtr : BitVec 64) (whisperG : SignalMessageGhost)
        (preKeyMsgRem : SepProp)
        (opkHi kyberPreKeyId signedPreKeyId : BitVec 32),
        SessionExtraRel recG sess →
        (signalMessageAt A whisperG whisperMsgPtr y.g.msg.message ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem ⊢
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg) →
        Steps (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s1 s2 →
        s2.pc = closureEntry img (cliExternsWith ext) + 0x1778#64 →
        s2.status = .Running →
        s2.sp = sp →
        (s2.sp &&& 15#64 == 0#64) = true →
        s2.trace = s1.trace →
        s2.readReg64 .x19 = y.fut →
        s2.readReg64 .x27 = sp + 0x370#64 →
        s2.readReg64 .x29 = s0.sp - 0x60#64 →
        calleeSavedVRegs s2 = calleeSavedVRegs s0 →
        ImgCallInv img s2 →
        SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .x30) s2
          (TokenInit img ∗
           genP3Pre A img s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
             whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
             recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
           stageP3Sub5ExtraPrePrevEmpty A s0 s2 y.fut y.out 8#64 g 0#8 ∗
           stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
             (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
             (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
             (y.g.stores + 0x78#64) (kyberVt img) rngPtr
             (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
             (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
              ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
              memRegion (y.fut + 0x2a8#64) 4) ∗
           stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
           ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
           preKeyMsgRem)
          Q (PanicOomProp s0)) →
    SepWPp (tripleRatchetProgAtExt img.base (cliExternsWith ext)) (s0.readReg64 .x30) s1
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Scope A y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp rootStack)
      Q (PanicOomProp s0)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
