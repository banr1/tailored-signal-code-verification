/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244Placed
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main -- shake: keep

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-!
# Symbolic Execution Step Lemmas for Segment S1 (`LoadRatchet`)

Fixed-image and relocatable `[LibsignalPlacement]` basic-block symbolic execution lemmas for
Segment S1 (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`) around `TripleRatchet::from_session_state`.
-/

theorem loadRatchet_bl_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    {s0 s : State}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x1d8#64)
    (hmeta : tryDecryptWPInv s0 s) :
    let sp := s0.sp - 1504#64
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr trFromName) s
      emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 0x1e4#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x21 ∧
        (s1.readReg64 .x1).setWidth 32 = (s.readReg64 .x1).setWidth 32 ∧
        s1.readReg64 .x8 = sp + 0x190#64 ∧
        CalleeSavedPreserved s s1) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hcal : (tripleRatchetProgAtExt b ext).fnAddr trFromName =
      (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName +
        (0x1e0#64 + BitVec.signExtend 64 (-98808#28 : BitVec 28)) :=
    fnAddr_tryDecrypt_rel64 (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") (by decide)
  dec_fetches b ext hfn 0x1d8 12
  rw [hcal]
  clear hcal hfn
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem memRegion_0x38_split_trFrom (sp : BitVec 64) :
    memRegion (sp + 0x38#64) 0x548 =
      memRegion (sp + 0x38#64) 0x158 ∗
      memRegion (sp + 0x190#64) 264 ∗
      memRegion (sp + 0x298#64) 0x2e8 := by
  rw [memRegion_split (sp + 0x38#64) 0x158 0x3f0 (by decide),
      show (sp + 0x38#64) + BitVec.ofNat 64 0x158 = sp + 0x190#64 by bv_omega,
      memRegion_split (sp + 0x190#64) 264 0x2e8 (by decide),
      show (sp + 0x190#64) + BitVec.ofNat 64 264 = sp + 0x298#64 by bv_omega]

theorem loadRatchet_call_trFrom_reaches {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (htrFrom : TrFromOkExt img A ext)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : LoadRatchetState A ctl img x R s0 s) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    let res := Mut.exec TripleRatchet.fromSessionState x.st
    reaches_pc prog (tryDecryptEntry img + 0x1e4#64) s
      (fun s_ret =>
        tryDecryptMidMeta img s0 s_ret ∧ s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧ s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧ s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s_ret.readReg64 .x25 = x.locA ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom res.2 ∗ trResultAt A (sp + 0x190#64) x.G res.1 ∗
          memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
          tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS1 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx1, hmem⟩
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  dsimp only [segLoadRatchetPC] at hpc; rw [hentry] at hpc
  have hwp_bl := loadRatchet_bl_wp hpc (tryDecryptMidMeta.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G x.st ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x548 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by rw [emp_sepConj]; exact hmem
  have hinv_s : img.FrozenLoaded s ∧ s.symtab = img.symtab := ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  refine reaches_pc_seq_callInv hinv_s (sepWP_to_reaches_pc hwp_bl hmem_emp) ?_
  intro s_call hpc_call _ ⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩ hinv_call
  subst hP1; rw [emp_sepConj] at hm_call; unfold tryDecryptCommonHeap at hm_call
  rw [memRegion_0x38_split_trFrom, stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  have hlr_call' : s_call.readReg64 Reg.lr = tryDecryptEntry img + 0x1e4#64 := by rw [hentry]; exact hlr_call
  let tg : TrFromGhost := { ss := x.ss, G := x.G, st := x.st, ret := sp + 0x190#64 }
  let F_call : SepProp :=
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - trFromStack) ∗ tryDecryptSavedRegs s0.sp s0 ∗ R
  have hpre_call : s_call.mem ⊨
      (⌜s_call.readReg64 .x0 = tg.ss ∧ (s_call.readReg64 .x1).setWidth 32 = 0#32 ∧ s_call.readReg64 .x8 = tg.ret⌝ ∗
       sessionStateAt A tg.ss tg.G tg.st ∗ memRegion tg.ret 264 ∗ logOff img ∗
       stackAt s_call.sp trFromStack ∗ A.pool) ∗ F_call := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx21, hx1_c.trans hx1, hx8_c⟩, ?_⟩
    rw [hsp_call]; dsimp only [tg, F_call, sp] at hm_call ⊢; convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_inImage htrFrom tg F_call hpc_call hwpInv_call.1 hlr_call' hinv_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hinv_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨_, htr_ret⟩, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta img s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain, hinv_ret.1, hinv_ret.2, by reg_chain⟩
  refine ⟨hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret; unfold tryDecryptCommonHeap
  rw [stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)]
  dsimp only [tg, TrFromGhost.model, F_call, sp] at hm_ret ⊢; convert hm_ret using 1; sep_ac_rfl

theorem loadRatchet_call_trFrom_reaches_x {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (htrFrom : TrFromOkX img A ext)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : LoadRatchetState A ctl img x R s0 s) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    let res := Mut.exec TripleRatchet.fromSessionState x.st
    reaches_pc prog (tryDecryptEntry img + 0x1e4#64) s
      (fun s_ret =>
        tryDecryptMidMeta img s0 s_ret ∧ s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧ s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧ s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s_ret.readReg64 .x25 = x.locA ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom res.2 ∗ trResultAt A (sp + 0x190#64) x.G res.1 ∗
          memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
          tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS1 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx1, hmem⟩
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  dsimp only [segLoadRatchetPC] at hpc; rw [hentry] at hpc
  have hwp_bl := loadRatchet_bl_wp hpc (tryDecryptMidMeta.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G x.st ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x548 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by rw [emp_sepConj]; exact hmem
  have hinv_s : img.FrozenLoaded s ∧ s.symtab = img.symtab := ⟨hmeta.2.2.2.2.2.2.1, hmeta.2.2.2.2.2.2.2.1⟩
  refine reaches_pc_seq_callInv hinv_s (sepWP_to_reaches_pc hwp_bl hmem_emp) ?_
  intro s_call hpc_call _ ⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩ hinv_call
  subst hP1; rw [emp_sepConj] at hm_call; unfold tryDecryptCommonHeap at hm_call
  rw [memRegion_0x38_split_trFrom, stackAt_tryDecryptSubStack_sub s0.sp trFromStackX (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  have hlr_call' : s_call.readReg64 Reg.lr = tryDecryptEntry img + 0x1e4#64 := by rw [hentry]; exact hlr_call
  let tg : TrFromGhost := { ss := x.ss, G := x.G, st := x.st, ret := sp + 0x190#64 }
  let F_call : SepProp :=
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - trFromStackX) ∗ tryDecryptSavedRegs s0.sp s0 ∗ R
  have hpre_call : s_call.mem ⊨
      (⌜s_call.readReg64 .x0 = tg.ss ∧ (s_call.readReg64 .x1).setWidth 32 = 0#32 ∧ s_call.readReg64 .x8 = tg.ret⌝ ∗
       sessionStateAt A tg.ss tg.G tg.st ∗ memRegion tg.ret 264 ∗ logOff img ∗
       stackAt s_call.sp trFromStackX ∗ A.pool) ∗ F_call := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx21, hx1_c.trans hx1, hx8_c⟩, ?_⟩
    rw [hsp_call]; dsimp only [tg, F_call, sp] at hm_call ⊢; convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_inImage htrFrom tg F_call hpc_call hwpInv_call.1 hlr_call' hinv_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hinv_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  have hcs : CalleeSavedPreserved s s_ret := CalleeSavedPreserved.trans hcs_c hcs_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨_, htr_ret⟩, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := hsp_ret.trans hsp_call
  have halign_ret : s_ret.spAligned = true := by rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta img s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret,
     (hcs_ret.2.2.2.2.2.2.2.2.2.2.1).trans hwpInv_call.2.2.2.2.1,
     htr_ret.trans hwpInv_call.2.2.2.2.2.1, hinv_ret.1, hinv_ret.2,
     (hcs.2.2.2.2.2.2.2.2.2.2.2).trans hmeta.2.2.2.2.2.2.2.2⟩
  refine ⟨hmeta_ret, (hcs.1).trans hx19, (hcs.2.1).trans hx20, (hcs.2.2.1).trans hx21,
    (hcs.2.2.2.1).trans hx22, (hcs.2.2.2.2.1).trans hx23,
    by change (s_ret.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
    (hcs.2.2.2.2.2.2.1).trans hx25, ?_⟩
  rw [hsp_call] at hm_ret; unfold tryDecryptCommonHeap
  rw [stackAt_tryDecryptSubStack_sub s0.sp trFromStackX (by decide)]
  dsimp only [tg, TrFromGhost.model, F_call, sp] at hm_ret ⊢; convert hm_ret using 1; sep_ac_rfl

theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

theorem fromSessionState_exec (st : SessionState (List (BitVec 8))) :
    Mut.exec TripleRatchet.fromSessionState st =
      match st.remoteIdentity with
      | some remote =>
        (.ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩,
         { st with receiverChains := [], pqRatchetState := default })
      | none =>
        (.error (.invalidSessionStructure .missingRemoteIdentity),
         { st with receiverChains := [], pqRatchetState := default }) := by
  rcases st with ⟨sv, li, ri, rk, pc, sc, rcs, ppk, pqr⟩
  cases ri <;> rfl

theorem fromSessionState_error_imp (C : Crypto) (S : SpqrModel)
    (x : TryDecryptGhost) (e : SignalProtocolError) (st1 : SessionState (List (BitVec 8)))
    (h : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1)) :
    e = .invalidSessionStructure .missingRemoteIdentity ∧
    e ≠ .panic ∧
    decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 ∧
    x.model C S uuidTryParse = (.error e, st1) := by
  have hexec := fromSessionState_exec x.st
  have hrem : x.st.remoteIdentity = none ∧
      e = .invalidSessionStructure .missingRemoteIdentity := by
    rw [hexec] at h
    cases hri : x.st.remoteIdentity <;> rw [hri] at h
    · injection h with h1 _
      injection h1 with h2
      exact ⟨rfl, h2.symm⟩
    · injection h with h1 _
      cases h1
  rcases hrem with ⟨hri, rfl⟩
  refine ⟨rfl, by decide, ?_, ?_⟩
  · simp [decryptDraws, drawsCoins, hri]
  · unfold TryDecryptGhost.model SessionState.tryDecryptWithState
    rw [mut_exec_bind, h]

theorem fromSessionState_error_imp_fn (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (S : SpqrModel)
    (x : TryDecryptGhost) (e : SignalProtocolError) (st1 : SessionState (List (BitVec 8)))
    (h : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1)) :
    e = .invalidSessionStructure .missingRemoteIdentity ∧
    e ≠ .panic ∧
    decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 ∧
    x.modelFn C decFn S uuidTryParse = (.error e, st1) := by
  have hexec := fromSessionState_exec x.st
  have hrem : x.st.remoteIdentity = none ∧
      e = .invalidSessionStructure .missingRemoteIdentity := by
    rw [hexec] at h
    cases hri : x.st.remoteIdentity <;> rw [hri] at h
    · injection h with h1 _
      injection h1 with h2
      exact ⟨rfl, h2.symm⟩
    · injection h with h1 _
      cases h1
  rcases hrem with ⟨hri, rfl⟩
  refine ⟨rfl, by decide, ?_, ?_⟩
  · simp [decryptDraws, drawsCoins, hri]
  · unfold TryDecryptGhost.modelFn SessionState.tryDecryptWithStateFn
    rw [mut_exec_bind, h]

theorem loadRatchet_err_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    {ret tag w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (retEpiloguePC img) s
      (((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ tag) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       ((sp + 0x500#64) ↦₆₄ t0) ∗
       words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₆₄ errTag) ∗
             ((sp + 0x198#64) ↦₆₄ tag) ∗
             words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
             ((sp + 0x500#64) ↦₆₄ tag) ∗
             words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  dec_fetches img.base ext hfn 0x1e4 32
  dec_fetches img.base ext hfn 0x384 16
  dsimp only [retEpiloguePC]
  rw [hentry] at hpc ⊢
  clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  examples_hide_fetches
  unfold words5At errTag
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩


/-- The 256-byte inline body of `trAt A t trG tr` at `p = t + 8#64`. -/
def trBodyAt (p : BitVec 64) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  (p ↦₆₄ trG.ratchet.chainsPtr) ∗
  ((p + 8#64) ↦₆₄ BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) ∗
  ((p + 16#64) ↦ₛ optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad) ∗
  ((p + 120#64) ↦ₛ keyToBytes32 tr.ratchet.rootKey) ∗
  ((p + 152#64) ↦₆₄ BitVec.ofNat 64 tr.ratchet.maxForwardJumps) ∗
  ((p + 160#64) ↦₃₂ tr.ratchet.previousCounter) ∗
  memRegion (p + 164#64) 4 ∗
  ((p + 168#64) ↦₆₄ trG.pq.cap) ∗
  ((p + 176#64) ↦₆₄ trG.pq.ptr) ∗
  ((p + 184#64) ↦₆₄ BitVec.ofNat 64 tr.pqrState.length) ∗
  ((p + 192#64) ↦ₛ tr.localIdentityKey.publicKey.bytes.toList) ∗
  ((p + 224#64) ↦ₛ tr.remoteIdentityKey.publicKey.bytes.toList)

/-- The address-independent heap and pure invariants of `trAt A t trG tr`. -/
def trHeapAt (A : RustAlloc) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) : SepProp :=
  ⌜∀ sc, tr.ratchet.senderChain = some sc →
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
  ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
    trG.ratchet.senderPad.length = 100 ∧
    tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
  ⌜tr.pqrState.length ≤ trG.pq.cap.toNat ∧
    trG.pq.cap.toNat < 2 ^ 63 ∧
    trG.pq.ptr ≠ 0⌝ ∗
  vecBuf A 104 8 (chainAt A) trG.ratchet.chainsCap trG.ratchet.chainsPtr
    (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
  (if trG.pq.cap = 0 then emp
   else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
     (trG.pq.ptr ↦ₛ tr.pqrState) ∗
     memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length)
       (trG.pq.cap.toNat - tr.pqrState.length))

theorem trAt_eq_cap_body_heap (A : RustAlloc) (t : BitVec 64) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    trAt A t trG tr =
      (t ↦₆₄ trG.ratchet.chainsCap) ∗
      trBodyAt (t + 8#64) trG tr ∗
      trHeapAt A trG tr := by
  unfold trAt ratchetAt vecU8At vecAt vecHeader trBodyAt trHeapAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem relocBytes_trBodyAt (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (hpad : trG.ratchet.senderPad.length = 100) :
    RelocBytes 256 (fun p => trBodyAt p trG tr) := by
  have h_sc : (optSenderChainBytes tr.ratchet.senderChain trG.ratchet.senderPad).length = 104 :=
    optSenderChainBytes_length tr.ratchet.senderChain trG.ratchet.senderPad hpad
  have h_rk : (keyToBytes32 tr.ratchet.rootKey).length = 32 := by
    simp [keyToBytes32]
  have h_lik : tr.localIdentityKey.publicKey.bytes.toList.length = 32 :=
    List.Vector.toList_length _
  have h_rik : tr.remoteIdentityKey.publicKey.bytes.toList.length = 32 :=
    List.Vector.toList_length _
  have h16 := relocBytes_append
    (relocBytes_pointsTo64 trG.ratchet.chainsPtr)
    (relocBytes_pointsTo64 (BitVec.ofNat 64 (trG.ratchet.chains.zip tr.ratchet.receiverChains).length)) rfl
  have h120 := relocBytes_append h16
    (relocBytes_pointsToBytes _ h_sc) rfl
  have h152 := relocBytes_append h120
    (relocBytes_pointsToBytes _ h_rk) rfl
  have h160 := relocBytes_append h152
    (relocBytes_pointsTo64 (BitVec.ofNat 64 tr.ratchet.maxForwardJumps)) rfl
  have h164 := relocBytes_append h160
    (relocBytes_pointsTo32 tr.ratchet.previousCounter) rfl
  have h168 := relocBytes_append h164
    (relocBytes_memRegion 4 (by decide)) rfl
  have h176 := relocBytes_append h168
    (relocBytes_pointsTo64 trG.pq.cap) rfl
  have h184 := relocBytes_append h176
    (relocBytes_pointsTo64 trG.pq.ptr) rfl
  have h192 := relocBytes_append h184
    (relocBytes_pointsTo64 (BitVec.ofNat 64 tr.pqrState.length)) rfl
  have h224 := relocBytes_append h192
    (relocBytes_pointsToBytes _ h_lik) rfl
  have h256 := relocBytes_append h224
    (relocBytes_pointsToBytes _ h_rik) rfl
  refine relocBytes_congr (fun p => ?_) h256
  unfold trBodyAt
  simp only [Nat.reduceAdd]
  sep_ac_rfl

theorem trHeapAt_facts {A : RustAlloc} {trG : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ trHeapAt A trG tr ∗ R) :
    trG.ratchet.senderPad.length = 100 ∧
    trG.ratchet.chainsCap + 1#64 ≠ 0#64 := by
  have hm' : m ⊨
      ⌜trG.ratchet.chains.length = tr.ratchet.receiverChains.length ∧
        trG.ratchet.senderPad.length = 100 ∧
        tr.ratchet.maxForwardJumps < 2 ^ 64⌝ ∗
      ⌜(trG.ratchet.chains.zip tr.ratchet.receiverChains).length ≤ trG.ratchet.chainsCap.toNat ∧
        trG.ratchet.chainsCap.toNat * 104 < 2 ^ 63 ∧
        trG.ratchet.chainsPtr ≠ 0⌝ ∗
      (⌜∀ sc, tr.ratchet.senderChain = some sc →
          Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes⌝ ∗
       ⌜tr.pqrState.length ≤ trG.pq.cap.toNat ∧
         trG.pq.cap.toNat < 2 ^ 63 ∧
         trG.pq.ptr ≠ 0⌝ ∗
       (if trG.ratchet.chainsCap = 0 then emp
        else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 trG.ratchet.chainsPtr
            (trG.ratchet.chains.zip tr.ratchet.receiverChains) ∗
          memRegion
            (trG.ratchet.chainsPtr +
              BitVec.ofNat 64 ((trG.ratchet.chains.zip tr.ratchet.receiverChains).length * 104))
            ((trG.ratchet.chainsCap.toNat -
              (trG.ratchet.chains.zip tr.ratchet.receiverChains).length) * 104)) ∗
       (if trG.pq.cap = 0 then emp
        else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
          (trG.pq.ptr ↦ₛ tr.pqrState) ∗
          memRegion (trG.pq.ptr + BitVec.ofNat 64 tr.pqrState.length)
            (trG.pq.cap.toNat - tr.pqrState.length)) ∗ R) := by
    unfold trHeapAt vecBuf at hm
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨⟨_, hpad, _⟩, ⟨_, hcap_lt, _⟩, _⟩
  refine ⟨hpad, ?_⟩
  bv_omega

theorem loadRatchet_ok_1a_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    {cap locA g20 w0 w1 w2 w3 w4 w5 t0 t1 t2 t3 t4 t5 : BitVec 64} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (tryDecryptEntry img + 0x210#64) s
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x190#64) ↦₆₄ cap) ∗ words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
       ((sp + 0x1b8#64) ↦₆₄ w4) ∗ ((sp + 0x1c0#64) ↦₆₄ w5) ∗ words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5))
      (fun sf P =>
        P = (((sp + 0x20#64) ↦₆₄ locA) ∗ ((sp + 0x190#64) ↦₆₄ cap) ∗ words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
             ((sp + 0x1b8#64) ↦₆₄ w4) ∗ ((sp + 0x1c0#64) ↦₆₄ w5) ∗ words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5)) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x8 = cap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = sp + 0x38#64) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  dec_fetches img.base ext hfn 0x1e4 44
  rw [hentry] at hpc ⊢; clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  examples_hide_fetches; unfold words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1b_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    {cap remA msgA d_cap w6 w7 w16 w17 w24 w25 w26 w27 w28 w29 w30 w31 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {s0 s : State} (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = tryDecryptEntry img + 0x210#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = cap) (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (tryDecryptEntry img + 0x24c#64) s
      (((sp + 0x30#64) ↦₆₄ remA) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗ ((sp + 0x1c8#64) ↦₆₄ w6) ∗
       ((sp + 0x1d0#64) ↦₆₄ w7) ∗ ((sp + 0x218#64) ↦₆₄ w16) ∗ ((sp + 0x220#64) ↦₆₄ w17) ∗
       words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
       words8At (sp + 0x100#64) d24 d25 d26 d27 d28 d29 d30 d31)
      (fun sf P =>
        P = (((sp + 0x30#64) ↦₆₄ remA) ∗ ((sp + 0x38#64) ↦₆₄ cap) ∗ ((sp + 0x1c8#64) ↦₆₄ w6) ∗
             ((sp + 0x1d0#64) ↦₆₄ w7) ∗ ((sp + 0x218#64) ↦₆₄ w16) ∗ ((sp + 0x220#64) ↦₆₄ w17) ∗
             words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
             words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 0x38#64 ∧ sf.readReg64 .x1 = msgA + 0x38#64 ∧
        sf.readReg64 .x8 = remA ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = sp + 0x2c0#64 ∧ sf.readVReg128 0#5 = w17 ++ w16 ∧ sf.readVReg128 2#5 = w7 ++ w6) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  dec_fetches img.base ext hfn 0x210 60
  rw [hentry] at hpc ⊢; clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  examples_hide_fetches; unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1c_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    {w8 w9 w16 w17 w18 w19 w20 w21 w22 w23 d16 d17 d18 d19 d20 d21 d22 d23 : BitVec 64}
    {s0 s : State} (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = tryDecryptEntry img + 0x24c#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hq0 : s.readVReg128 0#5 = w17 ++ w16) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (tryDecryptEntry img + 0x26c#64) s
      (((sp + 0x1d8#64) ↦₆₄ w8) ∗ ((sp + 0x1e0#64) ↦₆₄ w9) ∗ ((sp + 0x228#64) ↦₆₄ w18) ∗
       ((sp + 0x230#64) ↦₆₄ w19) ∗ words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
       words8At (sp + 0xc0#64) d16 d17 d18 d19 d20 d21 d22 d23)
      (fun sf P =>
        P = (((sp + 0x1d8#64) ↦₆₄ w8) ∗ ((sp + 0x1e0#64) ↦₆₄ w9) ∗ ((sp + 0x228#64) ↦₆₄ w18) ∗
             ((sp + 0x230#64) ↦₆₄ w19) ∗ words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
             words8At (sp + 0xc0#64) w16 w17 w18 w19 w20 w21 w22 w23) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = w9 ++ w8 ∧ sf.readVReg128 2#5 = s.readVReg128 2#5) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  dec_fetches img.base ext hfn 0x24c 32
  rw [hentry] at hpc ⊢; clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  examples_hide_fetches; unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1d_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    {remA msgA g2a0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = tryDecryptEntry img + 0x26c#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = remA) (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hq0 : s.readVReg128 0#5 = w9 ++ w8) (hq2 : s.readVReg128 2#5 = w7 ++ w6) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (segFindChainPC img) s
      (((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x1e8#64) ↦₆₄ w10) ∗ ((sp + 0x1f0#64) ↦₆₄ w11) ∗
       words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗ ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter) ∗ words8At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
       words8At (sp + 0x80#64) d8 d9 d10 d11 d12 d13 d14 d15)
      (fun sf P =>
        P = (((sp + 0x28#64) ↦₃₂ counter) ∗ ((sp + 0x1e8#64) ↦₆₄ w10) ∗ ((sp + 0x1f0#64) ↦₆₄ w11) ∗
             words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗ ((sp + 0x2a0#64) ↦₆₄ remA) ∗
             ((sp + 0x2ac#64) ↦₈ (s.readReg64 .x26).setWidth 8) ∗ words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗ ((msgA + 0x68#64) ↦₃₂ counter) ∗
             words8At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
             words8At (sp + 0x80#64) w8 w9 w10 w11 w12 w13 w14 w15) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = sp + 0x190#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  dec_fetches img.base ext hfn 0x26c 56
  dsimp only [segFindChainPC]; rw [hentry] at hpc ⊢; clear hentry hfn himg
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  examples_hide_fetches; unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem words32At_198_eq (sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 =
    words4At (sp + 0x198#64) w0 w1 w2 w3 ∗ ((sp + 0x1b8#64) ↦₆₄ w4) ∗ ((sp + 0x1c0#64) ↦₆₄ w5) ∗
    ((sp + 0x1c8#64) ↦₆₄ w6) ∗ ((sp + 0x1d0#64) ↦₆₄ w7) ∗ ((sp + 0x1d8#64) ↦₆₄ w8) ∗
    ((sp + 0x1e0#64) ↦₆₄ w9) ∗ ((sp + 0x1e8#64) ↦₆₄ w10) ∗ ((sp + 0x1f0#64) ↦₆₄ w11) ∗
    words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗ ((sp + 0x218#64) ↦₆₄ w16) ∗ ((sp + 0x220#64) ↦₆₄ w17) ∗
    ((sp + 0x228#64) ↦₆₄ w18) ∗ ((sp + 0x230#64) ↦₆₄ w19) ∗ words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
    words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 := by
  unfold words32At words16At words8At words4At
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words32At_40_eq (sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 =
    words8At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗ words8At (sp + 0x80#64) w8 w9 w10 w11 w12 w13 w14 w15 ∗
    words8At (sp + 0xc0#64) w16 w17 w18 w19 w20 w21 w22 w23 ∗
    words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31 := by
  unfold words32At words16At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem loadRatchet_ok_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    {cap locA remA msgA g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8}
    {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hcap : cap + 1#64 ≠ 0#64)
    (hpc : s.pc = tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := tripleRatchetProgAtExt img.base ext
    let sp := s0.sp - 1504#64
    SepWP prog (segFindChainPC img) s
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x30#64) ↦₆₄ remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ cap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
       ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗
       ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter))
      (fun sf P =>
        ∃ b2ac : BitVec 8,
          P = (((sp + 0x20#64) ↦₆₄ locA) ∗
               ((sp + 0x28#64) ↦₃₂ counter) ∗
               ((sp + 0x30#64) ↦₆₄ remA) ∗
               ((sp + 0x38#64) ↦₆₄ cap) ∗
               words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x190#64) ↦₆₄ cap) ∗
               words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x2a0#64) ↦₆₄ remA) ∗
               ((sp + 0x2ac#64) ↦₈ b2ac) ∗
               words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
               ((sp + 0x520#64) ↦₆₄ w4) ∗
               ((sp + 0x528#64) ↦₆₄ w5) ∗
               ((msgA + 0x68#64) ↦₃₂ counter)) ∧
          tryDecryptWPInv s0 sf ∧
          sf.readReg64 .x0 = sp + 0x38#64 ∧
          sf.readReg64 .x1 = msgA + 0x38#64 ∧
          sf.readReg64 .x8 = sp + 0x190#64 ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = sp + 0x190#64 ∧
          sf.readReg64 .x27 = sp + 0x38#64 ∧
          sf.readReg64 .x28 = sp + 0x2c0#64) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have h1a := loadRatchet_ok_1a_wp (ext := ext)
    (cap := cap) (locA := locA) (g20 := g20)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    himg hcap hpc hmeta hx20 hx23 hx25
  refine SepWP.rw_pre (by rw [words32At_40_eq, words32At_198_eq]) ?_
  refine SepWP.bind_framed h1a (by sep_frame) ?_
  intro s1a P1a ⟨hP1a, hmeta1a, hx8_1a, hx19_1a, hx20_1a, hx21_1a, hx22_1a, hx23_1a, hx24_1a, hx25_1a, hx27_1a⟩ hpc1a
  subst hP1a
  have h1b := loadRatchet_ok_1b_wp (ext := ext)
    (cap := cap) (remA := remA) (msgA := msgA) (d_cap := d_cap)
    (w6 := w6) (w7 := w7) (w16 := w16) (w17 := w17)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27)
    (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27)
    (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    himg hpc1a hmeta1a hx8_1a (hx22_1a.trans hx22) hx25_1a hx27_1a
  refine SepWP.bind_framed h1b (by sep_frame) ?_
  intro s1b P1b ⟨hP1b, hmeta1b, hx0_1b, hx1_1b, hx8_1b, hx19_1b, hx20_1b, hx21_1b, hx22_1b, hx23_1b, hx24_1b, hx25_1b, hx27_1b, hx28_1b, hq0_1b, hq2_1b⟩ hpc1b
  subst hP1b
  have h1c := loadRatchet_ok_1c_wp (ext := ext)
    (w8 := w8) (w9 := w9) (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19)
    (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19)
    (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    himg hpc1b hmeta1b (hx25_1b.trans hx25_1a) (hx27_1b.trans hx27_1a) hq0_1b
  refine SepWP.bind_framed h1c (by sep_frame) ?_
  intro s1c P1c ⟨hP1c, hmeta1c, hx0_1c, hx1_1c, hx8_1c, hx19_1c, hx20_1c, hx21_1c, hx22_1c, hx23_1c, hx24_1c, hx25_1c, hx27_1c, hx28_1c, hq0_1c, hq2_1c⟩ hpc1c
  subst hP1c
  have h1d := loadRatchet_ok_1d_wp (ext := ext)
    (remA := remA) (msgA := msgA) (g2a0 := g2a0)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (w6 := w6) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11)
    (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (counter := counter) (g28 := g28) (g2ac := g2ac)
    himg hpc1c hmeta1c (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
    hq0_1c (by reg_chain)
  refine SepWP.bind_framed h1d (by sep_frame) ?_
  intro sf Pf ⟨hPf, hmetaf, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨(s1c.readReg64 .x26).setWidth 8, ?_, hmetaf, by reg_chain⟩
  rw [words32At_40_eq, words32At_198_eq]
  sep_ac_rfl

/-! ## Relocatable (`[LibsignalPlacement]`) Segment S1 Symbolic Steps -/

theorem reaches_pc_lsro {prog : Program} {pl : Obj.MultiPlacement} {t : BitVec 64}
    {s : State} {Q : State → Prop} (hro : LibsignalRoLoaded pl s.mem)
    (h : reaches_pc prog t s Q) :
    reaches_pc prog t s (fun sf => Q sf ∧ LibsignalRoLoaded pl sf.mem) := by
  intro hL
  obtain ⟨sf, hst, ⟨hpc, hrun, hq⟩ | hoom⟩ := h hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, hq, libsignalRoLoaded_of_keepsFrozen hro hst.keepsFrozen⟩⟩
  · exact ⟨sf, hst, Or.inr hoom⟩

theorem loadRatchet_bl_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    (hpc : s.pc = segLoadRatchetPC_placed)
    (hmeta : tryDecryptWPInv s0 s) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) (blkPl_57).base s emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (blkPl_131).base + 484#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x21 ∧
        (s1.readReg64 .x1).setWidth 32 = (s.readReg64 .x1).setWidth 32 ∧
        s1.readReg64 .x8 = sp + 0x190#64 ∧
        CalleeSavedPreserved s s1) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [segLoadRatchetPC_placed, tryDecryptEntry_placed] at hpc
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]; rfl) (by simp_all [arm64_norm]) ?_
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem loadRatchet_call_trFrom_reaches_placed [LibsignalPlacement]
    {A : RustAlloc} {ctl : BitVec 64} {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base (trFromPlacedSpec A))
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : LoadRatchetState_placed A ctl x R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    let res := Mut.exec TripleRatchet.fromSessionState x.st
    reaches_pc prog ((blkPl_131).base + 484#64) s
      (fun s_ret =>
        tryDecryptMidMeta_placed s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 0x140#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 0x500#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = x.locA ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom res.2 ∗
          trResultAt A (sp + 0x190#64) x.G res.1 ∗
          memRegion x.ret 48 ∗
          memRegion sp 0x30 ∗
          ((sp + 0x30#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 0x38#64) 0x158 ∗
          memRegion (sp + 0x298#64) 0x2e8 ∗
          tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS1 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx1, hmem⟩
  have hwp_bl := loadRatchet_bl_wp_placed (H := H) hpc (tryDecryptMidMeta_placed.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G x.st ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x548 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  refine reaches_pc_seq_lscl hmeta.2.2.2.2.2.2.1 (reaches_pc_lsro hro (sepWP_to_reaches_pc hwp_bl hmem_emp)) ?_
  intro s_call hpc_call _ ⟨⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩, hro_call⟩ hcl_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold tryDecryptCommonHeap at hm_call
  rw [memRegion_0x38_split_trFrom, logOff_tryDecryptDummyImg,
      stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  let tg : TrFromGhost := { ss := x.ss, G := x.G, st := x.st, ret := sp + 0x190#64 }
  let F_call : SepProp :=
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - trFromStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ R
  have htrFrom_blk := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H) htrFrom
  have hpre_call : s_call.mem ⊨ (withLsRoLoaded lsmpl (trFromRawPlacedSpec A)).pre tg s_call ∗ F_call := by
    dsimp only [withLsRoLoaded, trFromRawPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro_call, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx21, hx1_c.trans hx1, hx8_c⟩, ?_⟩
    rw [hsp_call]; dsimp only [tg, F_call, sp] at hm_call ⊢; convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_lscl htrFrom_blk tg F_call hpc_call hwpInv_call.1 hlr_call hcl_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hcl_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  dsimp only [withLsRoLoaded, trFromRawPlacedSpec] at hpost_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨_, htr_ret⟩, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta_placed s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain, hcl_ret, by reg_chain⟩
  refine ⟨hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret
  unfold tryDecryptCommonHeap
  rw [logOff_tryDecryptDummyImg, stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)]
  dsimp only [tg, TrFromGhost.model, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

theorem loadRatchet_err_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {ret tag w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog retEpiloguePC_placed s
      (((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ tag) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       ((sp + 0x500#64) ↦₆₄ t0) ∗
       words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₆₄ errTag) ∗
             ((sp + 0x198#64) ↦₆₄ tag) ∗
             words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
             ((sp + 0x500#64) ↦₆₄ tag) ∗
             words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [retEpiloguePC_placed, tryDecryptEntry_placed]
  unfold words5At errTag
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩

theorem loadRatchet_ok_1a_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA g20 w0 w1 w2 w3 w4 w5 t0 t1 t2 t3 t4 t5 : BitVec 64} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_131).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 528#64) s
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x190#64) ↦₆₄ cap) ∗ words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
       ((sp + 0x1b8#64) ↦₆₄ w4) ∗ ((sp + 0x1c0#64) ↦₆₄ w5) ∗ words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5))
      (fun sf P =>
        P = (((sp + 0x20#64) ↦₆₄ locA) ∗ ((sp + 0x190#64) ↦₆₄ cap) ∗ words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
             ((sp + 0x1b8#64) ↦₆₄ w4) ∗ ((sp + 0x1c0#64) ↦₆₄ w5) ∗ words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5)) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x8 = cap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = sp + 0x38#64) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1b_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap remA msgA d_cap w6 w7 w16 w17 w24 w25 w26 w27 w28 w29 w30 w31 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_131).base + 528#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = cap) (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 588#64) s
      (((sp + 0x30#64) ↦₆₄ remA) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗ ((sp + 0x1c8#64) ↦₆₄ w6) ∗
       ((sp + 0x1d0#64) ↦₆₄ w7) ∗ ((sp + 0x218#64) ↦₆₄ w16) ∗ ((sp + 0x220#64) ↦₆₄ w17) ∗
       words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
       words8At (sp + 0x100#64) d24 d25 d26 d27 d28 d29 d30 d31)
      (fun sf P =>
        P = (((sp + 0x30#64) ↦₆₄ remA) ∗ ((sp + 0x38#64) ↦₆₄ cap) ∗ ((sp + 0x1c8#64) ↦₆₄ w6) ∗
             ((sp + 0x1d0#64) ↦₆₄ w7) ∗ ((sp + 0x218#64) ↦₆₄ w16) ∗ ((sp + 0x220#64) ↦₆₄ w17) ∗
             words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
             words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 0x38#64 ∧ sf.readReg64 .x1 = msgA + 0x38#64 ∧
        sf.readReg64 .x8 = remA ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = sp + 0x2c0#64 ∧ sf.readVReg128 0#5 = w17 ++ w16 ∧ sf.readVReg128 2#5 = w7 ++ w6) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1c_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w8 w9 w16 w17 w18 w19 w20 w21 w22 w23 d16 d17 d18 d19 d20 d21 d22 d23 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_131).base + 588#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hq0 : s.readVReg128 0#5 = w17 ++ w16) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 620#64) s
      (((sp + 0x1d8#64) ↦₆₄ w8) ∗ ((sp + 0x1e0#64) ↦₆₄ w9) ∗ ((sp + 0x228#64) ↦₆₄ w18) ∗
       ((sp + 0x230#64) ↦₆₄ w19) ∗ words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
       words8At (sp + 0xc0#64) d16 d17 d18 d19 d20 d21 d22 d23)
      (fun sf P =>
        P = (((sp + 0x1d8#64) ↦₆₄ w8) ∗ ((sp + 0x1e0#64) ↦₆₄ w9) ∗ ((sp + 0x228#64) ↦₆₄ w18) ∗
             ((sp + 0x230#64) ↦₆₄ w19) ∗ words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
             words8At (sp + 0xc0#64) w16 w17 w18 w19 w20 w21 w22 w23) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = w9 ++ w8 ∧ sf.readVReg128 2#5 = s.readVReg128 2#5) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1d_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {remA msgA g2a0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 620#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = remA) (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hq0 : s.readVReg128 0#5 = w9 ++ w8) (hq2 : s.readVReg128 2#5 = w7 ++ w6) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
      (((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x1e8#64) ↦₆₄ w10) ∗ ((sp + 0x1f0#64) ↦₆₄ w11) ∗
       words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗ ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter) ∗ words8At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
       words8At (sp + 0x80#64) d8 d9 d10 d11 d12 d13 d14 d15)
      (fun sf P =>
        P = (((sp + 0x28#64) ↦₃₂ counter) ∗ ((sp + 0x1e8#64) ↦₆₄ w10) ∗ ((sp + 0x1f0#64) ↦₆₄ w11) ∗
             words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗ ((sp + 0x2a0#64) ↦₆₄ remA) ∗
             ((sp + 0x2ac#64) ↦₈ (s.readReg64 .x26).setWidth 8) ∗ words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗ ((msgA + 0x68#64) ↦₃₂ counter) ∗
             words8At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
             words8At (sp + 0x80#64) w8 w9 w10 w11 w12 w13 w14 w15) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = sp + 0x190#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [segFindChainPC_placed, tryDecryptEntry_placed]
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA remA msgA g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
     w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_131).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog segFindChainPC_placed s
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x30#64) ↦₆₄ remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ cap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter))
      (fun sf P =>
        ∃ b2ac : BitVec 8,
          P = (((sp + 0x20#64) ↦₆₄ locA) ∗ ((sp + 0x28#64) ↦₃₂ counter) ∗ ((sp + 0x30#64) ↦₆₄ remA) ∗
               ((sp + 0x38#64) ↦₆₄ cap) ∗
               words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x190#64) ↦₆₄ cap) ∗
               words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x2a0#64) ↦₆₄ remA) ∗ ((sp + 0x2ac#64) ↦₈ b2ac) ∗
               words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
               ((msgA + 0x68#64) ↦₃₂ counter)) ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 0x38#64 ∧ sf.readReg64 .x1 = msgA + 0x38#64 ∧
          sf.readReg64 .x8 = sp + 0x190#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
          sf.readReg64 .x27 = sp + 0x38#64 ∧ sf.readReg64 .x28 = sp + 0x2c0#64) := by
  dsimp only
  have h1a := loadRatchet_ok_1a_wp_placed (H := H)
    (cap := cap) (locA := locA) (g20 := g20)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    hcap hpc hmeta hx20 hx23 hx25
  refine SepWP.rw_pre (by rw [words32At_40_eq, words32At_198_eq]) ?_
  refine SepWP.bind_framed h1a (by sep_frame) ?_
  intro s1a P1a ⟨hP1a, hmeta1a, hx8_1a, hx19_1a, hx20_1a, hx21_1a, hx22_1a, hx23_1a, hx24_1a, hx25_1a, hx27_1a⟩ hpc1a
  subst hP1a
  have h1b := loadRatchet_ok_1b_wp_placed (H := H)
    (cap := cap) (remA := remA) (msgA := msgA) (d_cap := d_cap)
    (w6 := w6) (w7 := w7) (w16 := w16) (w17 := w17)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27)
    (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27)
    (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    hpc1a hmeta1a hx8_1a (hx22_1a.trans hx22) hx25_1a hx27_1a
  refine SepWP.bind_framed h1b (by sep_frame) ?_
  intro s1b P1b ⟨hP1b, hmeta1b, hx0_1b, hx1_1b, hx8_1b, hx19_1b, hx20_1b, hx21_1b, hx22_1b, hx23_1b, hx24_1b, hx25_1b, hx27_1b, hx28_1b, hq0_1b, hq2_1b⟩ hpc1b
  subst hP1b
  have h1c := loadRatchet_ok_1c_wp_placed (H := H)
    (w8 := w8) (w9 := w9) (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19)
    (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19)
    (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    hpc1b hmeta1b (hx25_1b.trans hx25_1a) (hx27_1b.trans hx27_1a) hq0_1b
  refine SepWP.bind_framed h1c (by sep_frame) ?_
  intro s1c P1c ⟨hP1c, hmeta1c, hx0_1c, hx1_1c, hx8_1c, hx19_1c, hx20_1c, hx21_1c, hx22_1c, hx23_1c, hx24_1c, hx25_1c, hx27_1c, hx28_1c, hq0_1c, hq2_1c⟩ hpc1c
  subst hP1c
  have h1d := loadRatchet_ok_1d_wp_placed (H := H)
    (remA := remA) (msgA := msgA) (g2a0 := g2a0)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (w6 := w6) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11)
    (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (counter := counter) (g28 := g28) (g2ac := g2ac)
    hpc1c hmeta1c (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
    hq0_1c (by reg_chain)
  refine SepWP.bind_framed h1d (by sep_frame) ?_
  intro sf Pf ⟨hPf, hmetaf, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨(s1c.readReg64 .x26).setWidth 8, ?_, hmetaf, by reg_chain⟩
  rw [words32At_40_eq, words32At_198_eq]
  sep_ac_rfl

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
