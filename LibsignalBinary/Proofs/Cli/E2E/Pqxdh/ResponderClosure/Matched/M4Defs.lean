/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Matched-Session Stage P4 (`+0x34dc → exit`): Spatial Bundles and Statement

Defines the matched-session Stage P4 (`opkIdIsSome = 2#32`, skipping `mark_kyber_pre_key_used` and
`remove_pre_key`, over general `prevSessionsEmptyAt A coroPtr g`) stack budget, spatial entry/exit
predicates, three-way outcome `StageP4MatchedBranch`, and `StageP4MatchedExtStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

/-! ## Stack budget -/

/-- Stack budget for matched-session Stage P4 (`save_identity`, `store_session`, and error
unwinds; `mark_kyber_pre_key_used` and `remove_pre_key` are skipped). -/
def stageP4MatchedCallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max (saveIdCallStack ikit) (storeSessionCallStack kit)

theorem saveIdStack_le_matched {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    saveIdCallStack ikit ≤ stageP4MatchedCallStack kit ikit :=
  Nat.le_max_left _ _

theorem storeSessionStack_le_matched {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    storeSessionCallStack kit ≤ stageP4MatchedCallStack kit ikit :=
  Nat.le_max_right _ _

theorem stack_matched_to_saveId {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP4MatchedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4MatchedCallStack kit ikit))
        (stageP4MatchedCallStack kit ikit - saveIdCallStack ikit) ∗
        stackAt sp (saveIdCallStack ikit) :=
  stackAt_sub_eq sp (stageP4MatchedCallStack kit ikit) (saveIdCallStack ikit)
    (saveIdStack_le_matched kit ikit) hn

theorem stack_matched_to_storeSession {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4MatchedCallStack kit ikit ≤ 2 ^ 64) :
    stackAt sp (stageP4MatchedCallStack kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4MatchedCallStack kit ikit))
        (stageP4MatchedCallStack kit ikit - storeSessionCallStack kit) ∗
        stackAt sp (storeSessionCallStack kit) :=
  stackAt_sub_eq sp (stageP4MatchedCallStack kit ikit) (storeSessionCallStack kit)
    (storeSessionStack_le_matched kit ikit) hn

/-! ## Spatial entry/exit bundles and three-way outcome -/

/-- Shared spatial resources across `P4.1` (`save_identity`) and `P4.4` (`store_session`) on
matched-session Stage P4 (`opkIdIsSome = 2#32`, skipping `P4.2` and `P4.3`). -/
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

/-- Spatial precondition at `+0x34dc` for matched-session Stage P4. -/
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

/-- Spatial postcondition at `s0.readReg64 .x30` for matched-session Stage P4, after
`SessionStructure` (`+0xf8`, 344B) and `prevSessionsEmptyAt` (`+0xe0`, 24B + spare `prevPtr`) are
dropped into `memRegion (coroPtr + 0xe0#64) 368`. -/
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

/-- Three-way outcome classification of matched-session Stage P4 (`+0x34dc → s0.readReg64 .x30`,
`opkIdIsSome = 2#32`). -/
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

/-- Dealloc-only (`StageP4Alloc img.base A ext`) statement of matched-session Stage P4
(`+0x34dc → s0.readReg64 .x30` for `opkIdIsSome = 2#32`). -/
def StageP4MatchedP4ExtStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State))
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base),
    StageP4Alloc img.base A ext →
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
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 →
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

/-- `AllocHooks A ext` statement of matched-session Stage P4 (`+0x34dc → s0.readReg64 .x30`
for `opkIdIsSome = 2#32`). -/
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
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 →
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

/-- Matched-session Stage P4 (`+0x34dc → s0.readReg64 .x30`, `opkIdIsSome = 2#32`): runs
`save_identity`, skips `mark_kyber_pre_key_used` and `remove_pre_key`, runs `store_session`, and
drops `SessionStructure` plus `prevSessionsEmptyAt` into `memRegion (coroPtr + 0xe0#64) 368`. -/
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
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 →
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

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
