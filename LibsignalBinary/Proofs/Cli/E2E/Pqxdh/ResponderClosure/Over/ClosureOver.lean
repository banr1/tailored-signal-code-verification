/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Top
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveEnc
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Responder Closure Over-Path Scope Bridges and Stage P3/P4 Instantiations

Defines the archived previous-session validity predicate `OverPrevEncOK`, proves `clearPending`
canonicality and `< 2 ^ 32` length bounds from `Cli.Slots.scopeIn`, and instantiates over-path
Stages P3 and P4 (`previous_sessions = [enc]`) for general `RustAlloc` and `E2E.HooksE.A0`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record.Serialization (CanonSession encSessionMem_eq_of_canon)
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.SignalSession

/-! ## Archived Previous-Session Predicates and `clearPending` Scope Bridges -/

def OverPrevEncOKAt (enc : List (BitVec 8)) (sess : Session (List (BitVec 8))) : Prop :=
  enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

def OverPrevEncOK (enc : List (BitVec 8)) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    enc = CryptoVerification.E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧ sess.pendingKyberPreKey = none

def prevArchived1AtD2c (A : RustAlloc) (coroPtr : BitVec 64)
    (recG : SessionGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  ∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
    ⌜prevCap' ≠ 0#64⌝ ∗
    prevVecAt A (coroPtr + 0xe0#64) prevCap' prevPtr'
      [CryptoVerification.E2E.Record.Serialization.encSessionMem
        (clearPendingGhost recG) (clearPending sess)]

theorem encSessionMem_clearPending_eq {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : CanonSession G s) :
    CryptoVerification.E2E.Record.Serialization.encSessionMem
      (clearPendingGhost G) (clearPending s) =
      CryptoVerification.E2E.Record.encSession (clearPending s) :=
  encSessionMem_eq_of_canon _ _ (canonSession_clearPending h)

theorem scopeIn_clearPending {s : Session (List (BitVec 8))}
    (h : Cli.Slots.scopeIn ⟨some s⟩) :
    Cli.Slots.scopeIn ⟨some (clearPending s)⟩ := by
  rcases h with ⟨⟨hin, hpq, hrepr⟩, s', hs', hss⟩
  injection hs' with hs_eq; subst hs_eq
  refine ⟨⟨?_, ?_, ?_⟩, clearPending s, rfl, ?_⟩
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    have hin0 := hin s rfl
    exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [clearPending] at hk⟩
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    exact hpq s rfl
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr s rfl
    exact ⟨hr1, hr2, rfl, hr4⟩
  · exact ⟨hss.1, fun p hp => by simp [clearPending] at hp,
      fun k hk => by simp [clearPending] at hk, hss.2.2.2⟩

theorem overPrevEncOK_clearPending_of_scopeIn {s : Session (List (BitVec 8))}
    (h : Cli.Slots.scopeIn ⟨some s⟩) (hver : s.state.sessionVersion = 4#32) :
    OverPrevEncOK (CryptoVerification.E2E.Record.encSession (clearPending s)) :=
  ⟨clearPending s, rfl, Cli.Slots.scopeKit_of_scopeIn (scopeIn_clearPending h), hver, rfl, rfl⟩

theorem lenField2_clearPending_length_lt {s : Session (List (BitVec 8))}
    (h : Cli.Slots.scopeIn ⟨some s⟩) :
    (CryptoVerification.E2E.Record.lenField 2
      (CryptoVerification.E2E.Record.encSession (clearPending s))).length <
      2 ^ 31 + 2 ^ 21 + 40 := by
  have hc : Cli.Slots.scopeIn ⟨some (clearPending s)⟩ := scopeIn_clearPending h
  have hb_strip : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
      ⟨some (Cli.Slots.PqValid.stripPq (clearPending s))⟩ := by
    apply CryptoVerification.E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    rcases hc with ⟨⟨hin, _hpq, hrepr⟩, s', hs', hss⟩
    injection hs' with hs_eq; subst hs_eq
    refine ⟨⟨?_, ?_, ?_⟩, Cli.Slots.PqValid.stripPq (clearPending s), rfl, ?_⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      have hin0 := hin (clearPending s) rfl
      exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [clearPending, Cli.Slots.PqValid.stripPq] at hk⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq; rfl
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr (clearPending s) rfl
      exact ⟨hr1, hr2, rfl, hr4⟩
    · exact ⟨hss.1, fun p hp => by simp [clearPending, Cli.Slots.PqValid.stripPq] at hp,
        fun k hk => by simp [clearPending, Cli.Slots.PqValid.stripPq] at hk, hss.2.2.2⟩
  have h21 :
      (CryptoVerification.E2E.Record.encodeRecord
        ⟨some (Cli.Slots.PqValid.stripPq (clearPending s))⟩).length < 2 ^ 21 :=
    CryptoVerification.E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge :
      (CryptoVerification.E2E.Record.encSession
        (Cli.Slots.PqValid.stripPq (clearPending s))).length ≤
        (CryptoVerification.E2E.Record.encodeRecord
          ⟨some (Cli.Slots.PqValid.stripPq (clearPending s))⟩).length := by
    unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    dsimp only [Option.map_some]
    exact CryptoVerification.E2E.RecordX.lenField_length_ge' 1
      (CryptoVerification.E2E.Record.encSession (Cli.Slots.PqValid.stripPq (clearPending s)))
  have heq :
      (CryptoVerification.E2E.Record.encSession (clearPending s)).length =
        (CryptoVerification.E2E.Record.encSession
          (Cli.Slots.PqValid.stripPq (clearPending s))).length +
          (CryptoVerification.E2E.Record.bytesField 15
            (clearPending s).state.pqRatchetState).length := by
    simp only [CryptoVerification.E2E.Record.encSession, Cli.Slots.PqValid.stripPq,
      show (CryptoVerification.E2E.Record.bytesField 15 []).length = 0 from rfl,
      List.length_append]
    omega
  have hb15 :
      (CryptoVerification.E2E.Record.bytesField 15
        (clearPending s).state.pqRatchetState).length ≤
        (clearPending s).state.pqRatchetState.length + 20 :=
    CryptoVerification.E2E.RecordX.bytesField_length_le' 15 (clearPending s).state.pqRatchetState
  have hpq31 : (clearPending s).state.pqRatchetState.length < 2 ^ 31 :=
    (hc.1.2.1 (clearPending s) rfl).2
  have hlf2 :
      (CryptoVerification.E2E.Record.lenField 2
        (CryptoVerification.E2E.Record.encSession (clearPending s))).length ≤
        (CryptoVerification.E2E.Record.encSession (clearPending s)).length + 20 :=
    CryptoVerification.E2E.RecordX.lenField_length_le' 2
      (CryptoVerification.E2E.Record.encSession (clearPending s))
  omega

/-! ## Stage P3 (`Prev1`) Instantiations -/

abbrev OverVerNe1e04CliA0Stmt : Prop :=
  OverVerNe1e04CliAtStmt E2E.HooksE.A0 OverPrevEncOK

theorem OverVerNe1e04CliStmt.toA0 (h : OverVerNe1e04CliStmt OverPrevEncOK) :
    OverVerNe1e04CliA0Stmt :=
  h (A := E2E.HooksE.A0)

abbrev StageP3Prev1VRegsA0Stmt : Prop :=
  StageP3Prev1VRegsAtStmt E2E.HooksE.A0 OverPrevEncOK

theorem StageP3Prev1VRegsStmt.toA0 (h : StageP3Prev1VRegsStmt OverPrevEncOK) :
    StageP3Prev1VRegsA0Stmt :=
  h (A := E2E.HooksE.A0)

/-- Version-mismatch exit (`+0x1e04 → s0.readReg64 .x30`) at allocator `A` under 4K-aligned
memory contracts. -/
theorem overVerNe_1e04_cli_at_4k {A : RustAlloc} : OverVerNe1e04CliAt4KStmt A OverPrevEncOK :=
  VerNe.overVerNe_1e04_cli_ext

theorem overVerNe_1e04_cli_4k : OverVerNe1e04Cli4KStmt OverPrevEncOK :=
  fun {_A} => overVerNe_1e04_cli_at_4k

theorem overVerNe_1e04_cli_at {A : RustAlloc} : OverVerNe1e04CliAtStmt A OverPrevEncOK :=
  overVerNe_1e04_cli_at_4k.toAtStmt

theorem overVerNe_1e04_cli : OverVerNe1e04CliStmt OverPrevEncOK :=
  fun {_A} => overVerNe_1e04_cli_at

/-- Stage P3 (`+0x1778 → +0x34dc` or `s0.readReg64 .x30`) over a 1-element `previous_sessions`
at allocator `A` under 4K-aligned memory contracts. -/
theorem stageP3_prev1_vregs_at_4k_ok {A : RustAlloc} : StageP3Prev1VRegsAt4KStmt A OverPrevEncOK :=
  stageP3Gen_prev1_vregs_at_4k_ok overVerNe_1e04_cli_at_4k

theorem stageP3_prev1_vregs_4k_ok : StageP3Prev1VRegs4KStmt OverPrevEncOK :=
  stageP3Gen_prev1_vregs_4k_ok overVerNe_1e04_cli_4k

theorem stageP3_prev1_vregs_at_ok {A : RustAlloc} : StageP3Prev1VRegsAtStmt A OverPrevEncOK :=
  stageP3_prev1_vregs_at_4k_ok.toAtStmt

theorem stageP3_prev1_vregs_ok : StageP3Prev1VRegsStmt OverPrevEncOK :=
  fun {_A} => stageP3_prev1_vregs_at_ok

theorem overVerNe_1e04_cli_a0 : OverVerNe1e04CliA0Stmt :=
  overVerNe_1e04_cli.toA0

theorem stageP3_prev1_vregs_a0_ok : StageP3Prev1VRegsA0Stmt :=
  stageP3_prev1_vregs_ok.toA0

/-! ## Stage P4 (`Prev1`) Statements and Instantiations -/

def StageP4Prev1VRegsAt4KStmt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base),
    AllocContractsMem4K img.base A ext → DropSessionStructure3OkExt img.base A ext →
    SessionPrev1KitOkSE kit ops ext → SessionOnlyVtablesOk img kit →
    IdentityStoreKitOkIE img ikit ext → IdentityVtablesOk img ikit →
    PreKeyStoreKitOkImgE img pkKit ext → PreKeyVtablesOk img pkKit →
    KyberPreKeyStoreKitOkImgE img kpkKit ext → KyberPreKeyVtablesOk img kpkKit →
    ∀ (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      img.base &&& 0xfff#64 = 0#64 → SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (tripleRatchetProgAtExt img.base ext) s →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (stageP4Prev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
          ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          StageP4Prev1Branch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
            baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (PanicOomProp s0)

def StageP4Prev1VRegs4KStmt : Prop :=
  ∀ {A : RustAlloc}, StageP4Prev1VRegsAt4KStmt A

def StageP4Prev1VRegsAtStmt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base),
    AllocContracts img.base A ext → DropSessionStructure3OkExt img.base A ext →
    SessionPrev1KitOkSE kit ops ext → SessionOnlyVtablesOk img kit →
    IdentityStoreKitOkIE img ikit ext → IdentityVtablesOk img ikit →
    PreKeyStoreKitOkImgE img pkKit ext → PreKeyVtablesOk img pkKit →
    KyberPreKeyStoreKitOkImgE img kpkKit ext → KyberPreKeyVtablesOk img kpkKit →
    ∀ (s0 s : State)
      (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
      (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
      (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
      (G : SessionGhost) (ss : Session (List (BitVec 8))),
      img.base &&& 0xfff#64 = 0#64 → SessionExtraRel G ss → ops.RecPrev1Ok G ss enc →
      kit.addrOk peer.val → ikit.addrOk peer.val →
      kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey →
      (∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId) →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64 →
      FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
        (tripleRatchetProgAtExt img.base ext) s →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr → s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 → s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr → s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (stageP4Prev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
          remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
          ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss.state)
        (fun sf Pf =>
          Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧ ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          StageP4Prev1Branch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
            ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
            baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
        (PanicOomProp s0)

def StageP4Prev1VRegsStmt : Prop :=
  ∀ {A : RustAlloc}, StageP4Prev1VRegsAtStmt A

theorem StageP4Prev1VRegsAt4KStmt.toAtStmt {A : RustAlloc} (h : StageP4Prev1VRegsAt4KStmt A) :
    StageP4Prev1VRegsAtStmt A :=
  fun img ext kit ops ikit pkKit kpkKit hA =>
    h img ext kit ops ikit pkKit kpkKit (AllocContractsMem4K.of_AllocContracts hA)

abbrev StageP4Prev1VRegsA0Stmt : Prop :=
  StageP4Prev1VRegsAtStmt E2E.HooksE.A0

theorem StageP4Prev1VRegsStmt.toA0 (h : StageP4Prev1VRegsStmt) :
    StageP4Prev1VRegsA0Stmt :=
  h (A := E2E.HooksE.A0)

/-- Stage P4 (`+0x34dc → s0.readReg64 .x30`) over a 1-element `previous_sessions` at allocator
`A` under 4K-aligned memory contracts. -/
theorem stageP4_prev1_vregs_at_4k_ok {A : RustAlloc} : StageP4Prev1VRegsAt4KStmt A :=
  stageP4_prev1_vregs_kits_4k_ok

theorem stageP4_prev1_vregs_4k_ok : StageP4Prev1VRegs4KStmt :=
  fun {_A} => stageP4_prev1_vregs_kits_4k_ok

theorem stageP4_prev1_vregs_at_ok {A : RustAlloc} : StageP4Prev1VRegsAtStmt A :=
  stageP4_prev1_vregs_at_4k_ok.toAtStmt

theorem stageP4_prev1_vregs_ok : StageP4Prev1VRegsStmt :=
  fun {_A} => stageP4_prev1_vregs_at_ok

theorem stageP4_prev1_vregs_a0_ok : StageP4Prev1VRegsA0Stmt :=
  stageP4_prev1_vregs_ok.toA0

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
