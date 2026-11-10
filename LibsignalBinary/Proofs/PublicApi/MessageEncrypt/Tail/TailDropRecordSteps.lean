/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.RegChain

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem libsignalSessionCode_fnOff_dropSsLocal2 :
    libsignalSessionCode.fnOff FromRecordCallees.dropSessionStructureLocal2Name = 219708 := by
  exact libsignalSessionCode_fnOff_0x35a3c

theorem dropSs_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hdrop : FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName - 29084#64)
      (FromRecordCallees.dropSessionStructureLocal2Spec A) := by
  have heq :
      (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName - 29084#64 =
        (tripleRatchetProgAt b C ctl abs).fnAddr FromRecordCallees.dropSessionStructureLocal2Name := by
    unfold tripleRatchetProgAt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      libsignalSessionCode_fnOff_sym_3caf4, libsignalSessionCode_fnOff_dropSsLocal2]
    bv_omega
  rw [heq]
  exact hdrop

theorem sepWP_call_dropSs {prog : Program} {entry target_pc : BitVec 64} (ret_pc : BitVec 64)
    {A : RustAlloc} (hdrop : subroutine_ok prog entry (FromRecordCallees.dropSessionStructureLocal2Spec A))
    {ss sp : BitVec 64} {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hsp : s.sp = sp)
    (hP : P = (sessionStateAt A ss G st ∗ A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F)
    (hx0 : s.readReg64 .x0 = ss)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP prog target_pc sf
        ((memRegion ss 344 ∗ A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  subst hsp
  exact SepWP.call_framed_mut hdrop ⟨ss, G, st⟩ rfl (fun _ => rfl) hP hx0
    hpc hrun hsp_al hlr hnext

theorem stackAt_encSubStack_dropSs (sp : BitVec 64) :
    stackAt sp encSubStack =
      stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack ∗
        memRegion (sp - BitVec.ofNat 64 encSubStack)
          (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) := by
  have hd : FromRecordCallees.dropSessionStructureLocal2Stack = 4192 := rfl
  unfold stackAt
  rw [memRegion_split' (b := sp - BitVec.ofNat 64 encSubStack)
        (b' := sp - BitVec.ofNat 64 FromRecordCallees.dropSessionStructureLocal2Stack)
        (N := encSubStack)
        (n := encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack)
        (k := FromRecordCallees.dropSessionStructureLocal2Stack)
        (by decide)
        (by dsimp [encSubStack, withStoresEncStack, entryStack, encFrameSize, hd]; bv_omega)
        (by decide),
      sepConj_comm]

theorem scratch_has_50 {scratch : BitVec 64 → SepProp}
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (sp : BitVec 64) :
    ∃ S50 : SepProp,
      scratch sp = S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∧
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ⊢ memRegion sp 0x58) := by
  rcases hscr with rfl | rfl
  · refine ⟨memRegion sp 0x50, rfl, ?_⟩
    rw [memRegion_split' (b := sp) (b' := sp + 0x50#64) (N := 0x58) (n := 0x50) (k := 8)
          (by decide) (by bv_omega) (by decide)]
    exact sepConj_mono_right (pointsTo64_entails_memRegion _ _)
  · refine ⟨memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
      ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗ memRegion (sp + 0x48#64) 8,
      by unfold cmScratch; ac_rfl, ?_⟩
    have h1 := pointsTo64_entails_memRegion (sp + 0x38#64) (sp + 0x288#64)
    have h2 := pointsTo64_entails_memRegion (sp + 0x40#64) (sp + 0x350#64)
    have h3 := pointsTo64_entails_memRegion (sp + 0x50#64) (sp + 0x128#64)
    have hjoin :
        memRegion sp 0x58 =
          (memRegion sp 0x38 ∗ (memRegion (sp + 0x38#64) 8 ∗
            (memRegion (sp + 0x40#64) 8 ∗ memRegion (sp + 0x48#64) 8))) ∗
          memRegion (sp + 0x50#64) 8 := by
      rw [memRegion_split' (b := sp) (b' := sp + 0x38#64) (N := 0x58) (n := 0x38) (k := 0x20)
            (by decide) (by bv_omega) (by decide),
          memRegion_split' (b := sp + 0x38#64) (b' := sp + 0x40#64) (N := 0x20) (n := 8) (k := 0x18)
            (by decide) (by bv_omega) (by decide),
          memRegion_split' (b := sp + 0x40#64) (b' := sp + 0x48#64) (N := 0x18) (n := 8) (k := 0x10)
            (by decide) (by bv_omega) (by decide),
          memRegion_split' (b := sp + 0x48#64) (b' := sp + 0x50#64) (N := 0x10) (n := 8) (k := 8)
            (by decide) (by bv_omega) (by decide)]
      ac_rfl
    rw [hjoin]
    exact sepConj_mono
      (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) h3

theorem dropRecordDropSs_sepWP
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hdrop : FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x55c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x564#64) s
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  have hdrop' := dropSs_ok_at b C A ctl abs hdrop
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1372 8
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dropSs (sp := s.sp) (entry + bv% (1380)) hdrop' rfl
    (F := (s.sp + 80#64) ↦₆₄ (s.sp + 296#64))
    (by ac_rfl)
    rfl (by dsimp only [State.setPC, State.writeReg64, State.pc]; bv_omega)
    hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, _, hx23_sf, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx23_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx23_sf, hx25_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

/-! ## Session state cap unfolding and `ADDS XZR, X8, #1` helper -/

theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

def vecGhostTailAt (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_unfold_cap (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt]
  ac_rfl

def sessionStateAfterLocalIk (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostTailAt A G.localIk ss ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

theorem sessionStateAt_unfold_cap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      ((ss ↦₆₄ G.localIk.cap) ∗ sessionStateAfterLocalIk A ss G st) := by
  unfold sessionStateAt sessionStateAfterLocalIk
  rw [vecGhostAt_unfold_cap]
  ac_rfl

/-! ## Stepper lemmas from `+0x54c` (`1356`) and `+0x488` (`1160`) -/

theorem dropRecordCur_none_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  unfold noneCap
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1356 16
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem dropRecordCur_some_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  have hcmn := cap_add_one_beq_zero_eq_false hcap_lt
  have hcmn_ne := cap_add_one_ne_zero hcap_lt
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1356 16
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem dropRecordAfterDealloc_none_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  unfold noneCap
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1160 20
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem dropRecordAfterDealloc_some_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  have hcmn := cap_add_one_beq_zero_eq_false hcap_lt
  have hcmn_ne := cap_add_one_ne_zero hcap_lt
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1160 20
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

/-! ## Stepper lemmas from `+0x46c` (`1132`) -/

theorem dropRecord_otr_none_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x54c#64) s
      ((sp + 0x469#64) ↦₈ 0#8)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = ((sp + 0x469#64) ↦₈ 0#8)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1132 8
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dropRecord_otr_zero_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x54c#64) s
      (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1132 16
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem dropRecord_otr_nz_sepWP
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp pqCap pqPtr : BitVec 64}
    (hA : AllocHooks A abs)
    (hpq_nz : pqCap ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x488#64) s
      (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        A.pool ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗ A.pool ∗ stackAt sp allocHookStack)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_sym_3caf4
  have hdealloc := dealloc_ok_at b C A ctl abs hA encryptWithStoresName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "session_message_encrypt"))
    (by rw [hfn]; exact (ls_stub% "__rustc::__rust_dealloc").symm)
  messageEncryptTail_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1132 28
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dealloc (sp := s.sp) (entry + bv% (1160)) hdealloc rfl
    (F := ((s.sp + 648#64) ↦₆₄ pqCap) ∗ ((s.sp + 656#64) ↦₆₄ pqPtr) ∗ ((s.sp + 1129#64) ↦₈ 1#8))
    (by ac_rfl)
    rfl rfl rfl rfl hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, _, hx23_sf, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx23_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx23_sf, hx25_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

/-! ## Weakening lemmas for `sessionRecordAt`, `otrAt`, and `vecU8At` -/

theorem cur_none_weaken (sp : BitVec 64) :
    ((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336 ⊢
      memRegion (sp + 0x128#64) 0x158 := by
  rw [memRegion_split' (b := sp + 0x128#64) (b' := sp + 0x130#64) (N := 0x158) (n := 8) (k := 336)
        (by decide) (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem flag_memRegion_weaken (sp : BitVec 64) (b469 : BitVec 8) :
    memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ⊢
      memRegion (sp + 0x280#64) 0x1ea := by
  rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x469#64) (N := 0x1ea) (n := 0x1e9) (k := 1)
        (by decide) (by bv_omega) (by decide)]
  exact sepConj_mono_right (pointsTo8_entails_memRegion _ _)

theorem otr_none_slots_eq (A : RustAlloc) (sp : BitVec 64) :
    memRegion (sp + 0x280#64) 8 ∗ otrSlotAt A sp none ∗ cmSlotAt A sp none =
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8) := by
  dsimp only [otrSlotAt, cmSlotAt]
  have hm :
      memRegion (sp + 0x280#64) 0x1e9 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 200 ∗ memRegion (sp + 0x350#64) 0x119) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (N := 0x1e9) (n := 8) (k := 0x1e1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x350#64) (N := 0x1e1) (n := 200) (k := 0x119)
          (by decide) (by bv_omega) (by decide)]
  rw [hm]
  ac_rfl

theorem otrAt_weaken_vecU8At (A : RustAlloc) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    otrAt A o pqCap pqPtr ot ⊢
      vecU8At A o pqCap pqPtr ot.pqrState ∗ memRegion (o + 0x18#64) 176 := by
  unfold otrAt
  refine sepConj_mono_right ?_
  have h1 := ProofLib.pointsToBytes_entails_memRegion (o + 0x18#64) ot.senderRatchetKey.publicKey.bytes.toList
  have h2 := ProofLib.pointsToBytes_entails_memRegion (o + 0x38#64) ot.senderRatchetKey.privateKey.bytes.toList
  have h3 := ProofLib.pointsToBytes_entails_memRegion (o + 0x58#64) ot.localIdentityKey.publicKey.bytes.toList
  have h4 := ProofLib.pointsToBytes_entails_memRegion (o + 0x78#64) ot.remoteIdentityKey.publicKey.bytes.toList
  rw [List.Vector.toList_length] at h1 h2 h3 h4
  have h5 := ProofLib.pointsToBytes_entails_memRegion (o + 0x98#64) (chainKeyBytes ot.senderChainKey)
  have hck_len : (chainKeyBytes ot.senderChainKey).length = 36 := by
    unfold chainKeyBytes leBytes CryptoGames.HMAC.keyToBytes32
    simp
  rw [hck_len] at h5
  have h6 := pointsTo32_entails_memRegion (o + 0xbc#64) ot.previousCounter
  have h7 := pointsTo8_entails_memRegion (o + 0xc0#64) ot.sessionVersion
  have hjoin :
      memRegion (o + 0x18#64) 176 =
        memRegion (o + 0x18#64) 32 ∗ (memRegion (o + 0x38#64) 32 ∗
          (memRegion (o + 0x58#64) 32 ∗ (memRegion (o + 0x78#64) 32 ∗
            (memRegion (o + 0x98#64) 36 ∗ (memRegion (o + 0xbc#64) 4 ∗
              (memRegion (o + 0xc0#64) 1 ∗ memRegion (o + 0xc1#64) 7)))))) := by
    rw [memRegion_split' (b := o + 0x18#64) (b' := o + 0x38#64) (N := 176) (n := 32) (k := 144)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x38#64) (b' := o + 0x58#64) (N := 144) (n := 32) (k := 112)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x58#64) (b' := o + 0x78#64) (N := 112) (n := 32) (k := 80)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x78#64) (b' := o + 0x98#64) (N := 80) (n := 32) (k := 48)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0x98#64) (b' := o + 0xbc#64) (N := 48) (n := 36) (k := 12)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0xbc#64) (b' := o + 0xc0#64) (N := 12) (n := 4) (k := 8)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := o + 0xc0#64) (b' := o + 0xc1#64) (N := 8) (n := 1) (k := 7)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4
    (sepConj_mono h5 (sepConj_mono h6 (sepConj_mono_left h7))))))

theorem vecU8At_zero_weaken (A : RustAlloc) (v pqPtr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v 0#64 pqPtr bs ⊢
      (v ↦₆₄ 0#64) ∗ memRegion (v + 8#64) 16 := by
  unfold vecU8At vecHeader
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  rw [sepConj_comm]
  refine Entails.pure_left fun _ => ?_
  have h1 := pointsTo64_entails_memRegion (v + 8#64) pqPtr
  have h2 := pointsTo64_entails_memRegion (v + 16#64) (BitVec.ofNat 64 bs.length)
  have hm : memRegion (v + 8#64) 16 = memRegion (v + 8#64) 8 ∗ memRegion (v + 16#64) 8 := by
    rw [memRegion_split' (b := v + 8#64) (b' := v + 16#64) (N := 16) (n := 8) (k := 8)
          (by decide) (by bv_omega) (by decide)]
  rw [hm]
  exact sepConj_mono_right (sepConj_mono h1 h2)

theorem otr_zero_post_weaken (sp : BitVec 64) :
    memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ 0#64) ∗
      memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
      memRegion (sp + 0x350#64) 0x119 ⊢
    memRegion (sp + 0x280#64) 0x1e9 := by
  have h0 := pointsTo64_entails_memRegion (sp + 0x288#64) 0#64
  have hjoin :
      memRegion (sp + 0x280#64) 0x1e9 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 8 ∗
            (memRegion (sp + 0x290#64) 16 ∗
              (memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119))) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (N := 0x1e9) (n := 8) (k := 0x1e1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x290#64) (N := 0x1e1) (n := 8) (k := 0x1d9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x290#64) (b' := sp + 0x2a0#64) (N := 0x1d9) (n := 16) (k := 0x1c9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x2a0#64) (b' := sp + 0x350#64) (N := 0x1c9) (n := 176) (k := 0x119)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono_right (sepConj_mono_left h0)

theorem vecU8At_nz_weaken (A : RustAlloc) (v pqCap pqPtr : BitVec 64) (bs : List (BitVec 8))
    (hpq : pqCap ≠ 0#64) :
    vecU8At A v pqCap pqPtr bs ⊢
      (v ↦₆₄ pqCap) ∗ ((v + 8#64) ↦₆₄ pqPtr) ∗ memRegion (v + 16#64) 8 ∗
        A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat := by
  unfold vecU8At vecHeader
  have hpq' : pqCap ≠ 0 := hpq
  simp only [hpq', ↓reduceIte]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hle, _, _⟩ => ?_
  have hlen := pointsTo64_entails_memRegion (v + 16#64) (BitVec.ofNat 64 bs.length)
  have hbs := ProofLib.pointsToBytes_entails_memRegion pqPtr bs
  have hjoin :
      memRegion pqPtr bs.length ∗
        memRegion (pqPtr + BitVec.ofNat 64 bs.length) (pqCap.toNat - bs.length) =
      memRegion pqPtr pqCap.toNat := by
    rw [← memRegion_split pqPtr bs.length (pqCap.toNat - bs.length) (by omega),
        Nat.add_sub_of_le hle]
  have hassoc :
      ((v ↦₆₄ pqCap) ∗ ((v + 8#64) ↦₆₄ pqPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        (A.live pqPtr pqCap.toNat 1 ∗ (pqPtr ↦ₛ bs) ∗
          memRegion (pqPtr + BitVec.ofNat 64 bs.length) (pqCap.toNat - bs.length)) =
      (v ↦₆₄ pqCap) ∗ ((v + 8#64) ↦₆₄ pqPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live pqPtr pqCap.toNat 1 ∗
        ((pqPtr ↦ₛ bs) ∗
          memRegion (pqPtr + BitVec.ofNat 64 bs.length) (pqCap.toNat - bs.length)) := by
    ac_rfl
  rw [hassoc, ← hjoin]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hlen (sepConj_mono_right (sepConj_mono_left hbs))))

theorem otr_nz_post_weaken (sp pqCap pqPtr : BitVec 64) :
    memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
      ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
      memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119 ⊢
    memRegion (sp + 0x280#64) 0x1e9 := by
  have h0 := pointsTo64_entails_memRegion (sp + 0x288#64) pqCap
  have h1 := pointsTo64_entails_memRegion (sp + 0x290#64) pqPtr
  have hjoin :
      memRegion (sp + 0x280#64) 0x1e9 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 8 ∗
            (memRegion (sp + 0x290#64) 8 ∗
              (memRegion (sp + 0x298#64) 8 ∗
                (memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119)))) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (N := 0x1e9) (n := 8) (k := 0x1e1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x290#64) (N := 0x1e1) (n := 8) (k := 0x1d9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x290#64) (b' := sp + 0x298#64) (N := 0x1d9) (n := 8) (k := 0x1d1)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x298#64) (b' := sp + 0x2a0#64) (N := 0x1d1) (n := 8) (k := 0x1c9)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x2a0#64) (b' := sp + 0x350#64) (N := 0x1c9) (n := 176) (k := 0x119)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono_right (sepConj_mono h0 (sepConj_mono_left h1))

/-! ## `SegExit` bridge theorems for `+0x55c`, `+0x54c`, `+0x488`, and `+0x46c` -/

open CryptoVerification.LibsignalPublicApi.StoreKit

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

theorem tailDropRecordAt55c_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x55c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
  change s.mem ⊨
    (scratch sp ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAt A (sp + 0x128#64) G st ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  rw [hscr_eq] at hmem
  let F := S50 ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
    encSavedRegs s0.sp s0 ∗ R
  have hmem_re : s.mem ⊨
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F := by
    have heq :
        (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G st ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) := by
      unfold encCommon
      change (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
        stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R) = _
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hwp := dropRecordDropSs_sepWP (G := G) (st := st) env.callees.dropSs hpc hrun hsp_al hsp
  refine segExit_of_sepWP hmem_re hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = encEntry img + 0x564#64 := by
    rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine tailFreePrevSessions_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
    hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
  have hmf2 : s1.mem ⊨
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x128#64) 0x158 ∗
       memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
    have heq :
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) =
        ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
         (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
      unfold encCommon
      change _ = ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         memRegion (sp + 0x128#64) 0x158 ∗
         memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hmf3 := Satisfies.mono (sepConj_mono_left hscr_weaken) hmf2
  have heq2 :
      (memRegion sp 0x58 ∗
       (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
      ((memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
  rwa [← heq2]

theorem tailDropRecordCur_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x54c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  unfold sessionRecordAt at hmem
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  have h130 : sp + 0x110#64 + 0x20#64 = sp + 0x130#64 := by bv_omega
  rcases g with ⟨prevCap, prevPtr, _ | G⟩ <;> rcases hcur : rec.currentSession with _ | sess
  · rw [hcur, h128, h130] at hmem
    rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
    have hscr_mem : scratch sp ⊢ memRegion sp 0x58 := hscr_eq ▸ hscr_weaken
    let F := scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x130#64) 336 ∗ memRegion (sp + 0x280#64) 0x1e9 ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨ (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ F := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336)) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ F) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hwp := dropRecordCur_none_sepWP (b469 := b469) hpc hrun hsp_al hsp
    refine segExit_of_sepWP hmem_re hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = encEntry img + 0x564#64 := by
      rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine tailFreePrevSessions_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
      hsteps1.frozenLoaded hfl, by reg_chain, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (scratch sp ∗
          (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ F) =
          ((scratch sp ∗
            (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
            (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
           (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono hscr_mem
        (sepConj_mono (cur_none_weaken sp) (flag_memRegion_weaken sp 0#8)))) hmf2
    have heq2 :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) ∗
         (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    dsimp only at hmem
    unfold sessionStateReprAt at hmem
    rw [h128, sessionStateAt_unfold_cap A (sp + 0x128#64) G sess.state] at hmem
    let P_sess_pure : Prop :=
      PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧
        G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat
    let P_ik_pure : Prop :=
      G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0
    let F := scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      ⌜P_ik_pure⌝ ∗ sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨ ⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗
          (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
            sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommon A ctl img x (x.draws S answers) s0 ∗ R))) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (⌜P_sess_pure⌝ ∗
                (⌜P_ik_pure⌝ ∗
                  (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
                    sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state)))) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗
              (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
                sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
                memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
                encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
                encCommon A ctl img x (x.draws S answers) s0 ∗ R)))) := by
        dsimp only [P_sess_pure, P_ik_pure]; ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨_, h_ik, hmem2⟩
    have hcap_lt : G.localIk.cap.toNat < 2 ^ 63 := h_ik.2.1
    have hwp := dropRecordCur_some_sepWP (b469 := b469) hcap_lt hpc hrun hsp_al hsp
    refine segExit_of_sepWP hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = encEntry img + 0x55c#64 := by
      rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine tailDropRecordAt55c_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr
      prevCap prevPtr G sess.state hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
      hsteps1.frozenLoaded hfl, by reg_chain, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
    have hmf1' : s1.mem ⊨ ⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
          (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
            sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨h_ik, hmf1⟩
    have hmf2 : s1.mem ⊨
        (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G sess.state ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
              (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
                sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
                memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
                encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
                encCommon A ctl img x (x.draws S answers) s0 ∗ R))) =
          ((memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             sessionStateAt A (sp + 0x128#64) G sess.state ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        rw [sessionStateAt_unfold_cap A (sp + 0x128#64) G sess.state]
        dsimp only [P_ik_pure]
        ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (flag_memRegion_weaken sp 0#8)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x1ea ∗
         (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           sessionStateAt A (sp + 0x128#64) G sess.state ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((scratch sp ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
