/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Main
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import ProofLib.SepLogic.WP.Apply

@[expose] public section

set_option autoImplicit false

/-!
# Stacked 16 KiB `TripleRatchet::from_session_state` (`TrFromOkX`)

Proves `TrFromOkX img A ext` on `tripleRatchetProgAtExt img.base ext` under `AllocContractsX`
(`trFromStackX = 16976` B).
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.Ratchet (clampScalar)
open CryptoGames.LibsignalSession (PublicKey SessionState maxForwardJumps)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecAt vecBuf vecU8Buf)
open CryptoVerification.LibsignalSessionRepr (chainAt optSenderChainBytes vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost noneCap optSenderChainAt
  sessionStateAt speAt)
open CryptoVerification.LibsignalTripleRatchet (AllocContractsX DeserializeOkExt DropSpeOkX
  DropVecChainOkX ReceiveRatchetApply.stackAt_sub_split RemoteIdentityKeyOkExt TrFromGhost TrFromOkX
  deserializeName extHookStack logOff rustDeallocExternSpecWithStack trFromName trFromSpecX
  trFromStack trFromStackX trResultAt tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Getters (DropSpeGhost DropVecChainGhost dropSpeName
  dropSpeSpecX dropSpeStackX dropVecChainName dropVecChainSpecX dropVecChainStack
  dropVecChainStackX dropVecMessageKeyStackX remoteIdentityKeyName)
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom (SepWP.mono_pre
  SepWP.with_post afterTrFrom_decRel deserialize_ok_at_from err22_pack_ret
  err22_pack_stack err22_unpack_stack exists_err22_split exists_localIk_split_of_length_32
  exists_rootKey_split_of_length_32 exists_unpack64_of_length_104
  lik_pack_ret memRegion_24_of_8_2_14 memRegion_24_of_8_8_8 memRegion_33_to_tag_and_32
  memRegion_48_of_8_2_38 memRegion_48_of_8_8_8_8_2_14 memRegion_48_split_8_2_38
  optSenderChainAt_some_expose_from optSenderChainBytes_length rem_pack_ret
  remoteIdentityTag ret_168_split_prev ret_200_split_lik ret_232_split_rem ret_264_split_none
  ret_264_split_some rk_pack_ret rk_pack_stack rk_unpack_stack scRawCells_none_entails sc_pack_ret
  sc_pack_stack sc_unpack_stack sessionAfter208Frame sessionFromFrame_expose_remoteIk
  sessionStateAt_expose_from sessionStateAt_reassemble_after208 sp_288_combine_prev
  speAt_missingRemoteIdentity_sp_160 stackAt_dropVecChain_eq_allocHook_x
  stackAt_dropVecChain_eq_dropSpe_x stackAt_trFrom stackAt_trFrom_fold stack_256_96_split
  stack_280_184_fold stack_400_fold stack_456_160_split_deser stack_496_40_fold trFrom10cTail
  trFromGhost_model_snd trFromSavedRegs trFrom_step_10c_to_244 trFrom_step_244_to_428
  trFrom_step_ac_to_244 trResultAt_err_missingRemoteIdentity_intro trResultAt_ok_intro
  vecAt_chains_stack_fold vecAt_nil_chains_0_8 vecU8Buf_entails_dealloc
  vecU8Buf_zero_entails_emp)

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.ExtTrFromX

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

private theorem rk_bytes_length_32 (k : BitVec 256) :
    (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
  simp [CryptoGames.HMAC.keyToBytes32]

private theorem stackAt_trFromX_split (sp : BitVec 64) :
    stackAt sp trFromStackX =
      memRegion (sp - 16976#64) 12288 ∗ stackAt sp trFromStack := by
  rw [ReceiveRatchetApply.stackAt_sub_split sp trFromStackX trFromStack (by decide) (by decide)]
  have heq : sp - BitVec.ofNat 64 trFromStackX = sp - 16976#64 := by
    simp only [trFromStackX, dropVecChainStackX, dropVecMessageKeyStackX, extHookStack]; bv_omega
  rw [heq]; rfl

private theorem stackAt_dropVecChainX_split (sp : BitVec 64) :
    stackAt (sp - 496#64) dropVecChainStackX =
      memRegion (sp - 16976#64) 12288 ∗ stackAt (sp - 496#64) dropVecChainStack := by
  rw [ReceiveRatchetApply.stackAt_sub_split (sp - 496#64) dropVecChainStackX dropVecChainStack
    (by decide) (by decide)]
  have heq : sp - 496#64 - BitVec.ofNat 64 dropVecChainStackX = sp - 16976#64 := by
    simp only [dropVecChainStackX, dropVecMessageKeyStackX, extHookStack]; bv_omega
  rw [heq]; rfl

private theorem dropSpe_ok_at_from_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropSpeOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") -
          (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")))
      ((dropSpeSpecX A).inImage img) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff trFromName) +
      bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") -
        (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff dropSpeName) := by
    simp only [arm64_norm]
  have haddr : (tripleRatchetProgAtExt img.base ext).fnAddr trFromName +
      bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") -
        (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, hk]
  rwa [haddr]

private theorem dropVecChain_ok_at_from_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropVecChainOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") -
          (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")))
      ((dropVecChainSpecX A).inImage img) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff trFromName) +
      bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") -
        (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff dropVecChainName) := by
    simp only [arm64_norm]
  have haddr : (tripleRatchetProgAtExt img.base ext).fnAddr trFromName +
      bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") -
        (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropVecChainName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, hk]
  rwa [haddr]

private theorem dealloc_ok_at_from_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hA.dealloc_ok_at trFromName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))

private theorem call_dropSpe_x {prog : Program} {img : Obj.Image}
    {entry target_pc sp_val : BitVec 64} {A : RustAlloc}
    (hsub : subroutine_ok prog entry ((dropSpeSpecX A).inImage img)) (x : DropSpeGhost)
    {s : State} {P F_frame : SepProp} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp_val) (hx0 : s.readReg64 .x0 = x.a)
    (hpre : P = (speAt A x.fnName x.a x.e ∗ A.pool ∗ stackAt sp_val dropSpeStackX) ∗ F_frame)
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP prog target_pc sf (memRegion x.a 48 ∗ A.pool ∗ stackAt sp_val dropSpeStackX ∗ F_frame) post) :
    SepWP prog target_pc s P post := by
  apply CryptoVerification.SepWP.of_sepWP_inv (mid := s.readReg64 .lr) hfl hsym
  refine ProofLib.SepWP.call_subroutine_frame (x := x) (F := F_frame)
    hsub hpc hrun hsp rfl ?_ ?_ ?_ ?_ ?_
  · intro R hm
    have hm1 : s.mem ⊨ ((dropSpeSpecX A).pre x s ∗ F_frame) ∗ R := by
      rw [hpre, ← hsp_eq] at hm
      dsimp only [dropSpeSpecX]
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hx0, by simpa only [sepConj_assoc] using hm⟩
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfl, hsym⟩, by simpa only [sepConj_assoc] using hm1⟩
  · intro R' sf _ hpan_mem
    unfold Spec.inImage dropSpeSpecX at hpan_mem; dsimp only at hpan_mem
    rw [satisfies_pure_sepConj] at hpan_mem; exact hpan_mem.1
  · intro R' code sf _ hundef_mem
    unfold Spec.inImage dropSpeSpecX at hundef_mem; dsimp only at hundef_mem
    rw [satisfies_pure_sepConj] at hundef_mem; exact hundef_mem.1
  · intro sm hpcm hrunm hspm hcsm
    have hsp_alignm : sm.spAligned = true := by
      simpa [State.spAligned, hspm] using hsp
    dsimp only [Spec.inImage, dropSpeSpecX]
    simp only [sepConj_assoc, hsp_eq]
    refine SepWP.pure_elim fun htrm => ?_
    apply SepWP.done hpcm hrunm
    intro hflm hsymm
    exact SepWP.mono_pre (Entails.of_eq (by ac_rfl))
      (hcont sm hpcm hspm hrunm hsp_alignm hcsm htrm hflm hsymm)
  · intro R' sf _ hoom_mem
    exfalso
    unfold Spec.inImage dropSpeSpecX at hoom_mem; dsimp only at hoom_mem
    rw [satisfies_pure_sepConj] at hoom_mem; exact hoom_mem.1

private theorem call_dropVecChain_x {prog : Program} {img : Obj.Image}
    {entry target_pc sp_val : BitVec 64} {A : RustAlloc}
    (hsub : subroutine_ok prog entry ((dropVecChainSpecX A).inImage img)) (x : DropVecChainGhost)
    {s : State} {P F_frame : SepProp} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp_val) (hx0 : s.readReg64 .x0 = x.v)
    (hpre : P = (vecAt A 104 8 (chainAt A) x.v x.cap x.ptr x.cs ∗ A.pool ∗ stackAt sp_val dropVecChainStackX) ∗ F_frame)
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP prog target_pc sf (memRegion x.v 24 ∗ A.pool ∗ stackAt sp_val dropVecChainStackX ∗ F_frame) post) :
    SepWP prog target_pc s P post := by
  apply CryptoVerification.SepWP.of_sepWP_inv (mid := s.readReg64 .lr) hfl hsym
  refine ProofLib.SepWP.call_subroutine_frame (x := x) (F := F_frame)
    hsub hpc hrun hsp rfl ?_ ?_ ?_ ?_ ?_
  · intro R hm
    have hm1 : s.mem ⊨ ((dropVecChainSpecX A).pre x s ∗ F_frame) ∗ R := by
      rw [hpre, ← hsp_eq] at hm
      dsimp only [dropVecChainSpecX]
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hx0, by simpa only [sepConj_assoc] using hm⟩
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfl, hsym⟩, by simpa only [sepConj_assoc] using hm1⟩
  · intro R' sf _ hpan_mem
    unfold Spec.inImage dropVecChainSpecX at hpan_mem; dsimp only at hpan_mem
    rw [satisfies_pure_sepConj] at hpan_mem; exact hpan_mem.1
  · intro R' code sf _ hundef_mem
    unfold Spec.inImage dropVecChainSpecX at hundef_mem; dsimp only at hundef_mem
    rw [satisfies_pure_sepConj] at hundef_mem; exact hundef_mem.1
  · intro sm hpcm hrunm hspm hcsm
    have hsp_alignm : sm.spAligned = true := by
      simpa [State.spAligned, hspm] using hsp
    dsimp only [Spec.inImage, dropVecChainSpecX]
    simp only [sepConj_assoc, hsp_eq]
    refine SepWP.pure_elim fun htrm => ?_
    apply SepWP.done hpcm hrunm
    intro hflm hsymm
    exact SepWP.mono_pre (Entails.of_eq (by ac_rfl))
      (hcont sm hpcm hspm hrunm hsp_alignm hcsm htrm hflm hsymm)
  · intro R' sf _ hoom_mem
    exfalso
    unfold Spec.inImage dropVecChainSpecX at hoom_mem; dsimp only at hoom_mem
    rw [satisfies_pure_sepConj] at hoom_mem; exact hoom_mem.1

private theorem call_dealloc_x {prog : Program} {img : Obj.Image}
    {entry target_pc sp_val p : BitVec 64} {size align : Nat} {A : RustAlloc}
    (hsub : subroutine_ok prog entry ((rustDeallocExternSpecWithStack A extHookStack).inImage img))
    {s : State} {P F_frame : SepProp} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp_val)
    (hx0 : s.readReg64 .x0 = p) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align) (hlay : LayoutOk size align)
    (hpre : P = (A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt sp_val extHookStack) ∗ F_frame)
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP prog target_pc sf (A.pool ∗ stackAt sp_val extHookStack ∗ F_frame) post) :
    SepWP prog target_pc s P post := by
  apply CryptoVerification.SepWP.of_sepWP_inv (mid := s.readReg64 .lr) hfl hsym
  refine ProofLib.SepWP.call_subroutine_frame (x := (p, size, align)) (F := F_frame)
    hsub hpc hrun hsp rfl ?_ ?_ ?_ ?_ ?_
  · intro R hm
    have hm1 : s.mem ⊨ ((rustDeallocExternSpecWithStack A extHookStack).pre (p, size, align) s ∗ F_frame) ∗ R := by
      rw [hpre, ← hsp_eq] at hm
      dsimp only [rustDeallocExternSpecWithStack]
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hlay⟩, by simpa only [sepConj_assoc] using hm⟩
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfl, hsym⟩, by simpa only [sepConj_assoc] using hm1⟩
  · intro R' sf _ hpan_mem
    unfold Spec.inImage rustDeallocExternSpecWithStack at hpan_mem; dsimp only at hpan_mem
    rw [satisfies_pure_sepConj] at hpan_mem; exact hpan_mem.1
  · intro R' code sf _ hundef_mem
    unfold Spec.inImage rustDeallocExternSpecWithStack at hundef_mem; dsimp only at hundef_mem
    rw [satisfies_pure_sepConj] at hundef_mem; exact hundef_mem.1
  · intro sm hpcm hrunm hspm hcsm
    have hsp_alignm : sm.spAligned = true := by
      simpa [State.spAligned, hspm] using hsp
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack]
    simp only [sepConj_assoc, hsp_eq]
    refine SepWP.pure_elim fun htrm => ?_
    apply SepWP.done hpcm hrunm
    intro hflm hsymm
    exact SepWP.mono_pre (Entails.of_eq (by ac_rfl))
      (hcont sm hpcm hspm hrunm hsp_alignm hcsm htrm hflm hsymm)
  · intro R' sf _ hoom_mem
    exfalso
    unfold Spec.inImage rustDeallocExternSpecWithStack at hoom_mem; dsimp only at hoom_mem
    rw [satisfies_pure_sepConj] at hoom_mem; exact hoom_mem.1

private theorem trFrom_step_428_to_0e8_x
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hDropSpe : DropSpeOkX img A ext)
    (hDropVecChain : DropVecChainOkX img A ext)
    (ret ss : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (senderPad : List (BitVec 8))
    (s0 sm : State) (target_pc : BitVec 64) (F_cs : SepProp)
    (post : State → SepProp → Prop)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8}
    {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {remBs : List (BitVec 8)}
    {rd0 : BitVec 32} {rh4 : BitVec 16} {rw6 rw14 rw22 : BitVec 64} {rh30 : BitVec 16}
    {u_232 : BitVec 32} {u_228 : BitVec 16} {u_208 u_284 : BitVec 32}
    {sc0 sc1 sc2 sc3 sc4 sc5 sc6 sc7 sc8 sc9 sc10 sc11 sc12 : BitVec 64}
    {rk0 rk1 rk2 rk3 : BitVec 64}
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, st.senderChain = some sc →
      clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : G.chains.length = st.receiverChains.length)
    (hpq_ne : G.pq.cap ≠ 0 → 0 < G.pq.cap.toNat ∧ G.pq.cap.toNat < 2 ^ 63 ∧ G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hlik_split2 : ∀ a : BitVec 64,
      (a ↦ₛ st.localIdentity.publicKey.bytes.toList) =
        ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
         ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
         ((a + 6#64) ↦₈ b6) ∗
         ((a + 7#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
         ((a + 15#64) ↦₆₄ w15) ∗
         ((a + 23#64) ↦₆₄ w23) ∗
         ((a + 31#64) ↦₈ b31)))
    (hsc_split : ∀ a : BitVec 64, (a ↦ₛ optSenderChainBytes st.senderChain senderPad) =
      ((a ↦₆₄ sc0) ∗ ((a + 8#64) ↦₆₄ sc1) ∗ ((a + 16#64) ↦₆₄ sc2) ∗
       ((a + 24#64) ↦₆₄ sc3) ∗ ((a + 32#64) ↦₆₄ sc4) ∗ ((a + 40#64) ↦₆₄ sc5) ∗
       ((a + 48#64) ↦₆₄ sc6) ∗ ((a + 56#64) ↦₆₄ sc7) ∗ ((a + 64#64) ↦₆₄ sc8) ∗
       ((a + 72#64) ↦₆₄ sc9) ∗ ((a + 80#64) ↦₆₄ sc10) ∗ ((a + 88#64) ↦₆₄ sc11) ∗
       ((a + 96#64) ↦₆₄ sc12)))
    (hrk_split : ∀ a : BitVec 64, (a ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) =
      ((a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3)))
    (hrem_eq : ∀ ik, st.remoteIdentity = some ik → remBs = ik.publicKey.bytes.toList)
    (hrem_split : ∀ a : BitVec 64, (a ↦ₛ remBs) =
      ((a ↦₃₂ rd0) ∗ ((a + 4#64) ↦₁₆ rh4) ∗ ((a + 6#64) ↦₆₄ rw6) ∗
       ((a + 14#64) ↦₆₄ rw14) ∗ ((a + 22#64) ↦₆₄ rw22) ∗ ((a + 30#64) ↦₁₆ rh30)))
    (hfl : img.FrozenLoaded sm) (hsym : sm.symtab = img.symtab)
    (hpc : sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 1064#64)
    (hrun : sm.status = .Running) (halign : (s0.sp &&& 15#64 == 0#64) = true) (htr : sm.trace = s0.trace)
    (_hx8 : sm.readReg64 .x8 = img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))
    (_hx9 : sm.readReg64 .x9 = 27#64)
    (hx10 : sm.readReg64 .x10 = (remoteIdentityTag st.remoteIdentity).zeroExtend 64)
    (hx11 : sm.readReg64 .x11 = rw14)
    (hx12 : sm.readReg64 .x12 = rw6)
    (hx19 : sm.readReg64 .x19 = ret)
    (hx20 : sm.readReg64 .x20 = G.pq.cap)
    (hx21 : sm.readReg64 .x21 = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64)
    (hx22 : sm.readReg64 .x22 = s0.sp - 160#64)
    (hx23 : sm.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : sm.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : sm.readReg64 .x25 = b7.zeroExtend 64)
    (hx26 : sm.readReg64 .x26 = (b12 ++ b11 ++ b10 ++ b9).zeroExtend 64)
    (hx27 : sm.readReg64 .x27 = (b14 ++ b13).zeroExtend 64)
    (hx28 : sm.readReg64 .x28 = b8.zeroExtend 64)
    (hx29 : sm.readReg64 .x29 = s0.sp - 96#64)
    (hsp : sm.sp = s0.sp - 496#64)
    (hcont : ∀ sf,
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 232#64 →
      sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp - 496#64 →
      calleeSavedVRegs sf = calleeSavedVRegs sm →
      SepWP (tripleRatchetProgAtExt img.base ext) target_pc sf
        (A.pool ∗
         trResultAt A ret G
           (match st.remoteIdentity with
            | some rem =>
              .ok ⟨⟨st.rootKey, st.senderChain, st.receiverChains,
                    st.previousCounter, maxForwardJumps⟩,
                   st.pqRatchetState, st.localIdentity, rem⟩
            | none => .error (.invalidSessionStructure .missingRemoteIdentity)) ∗
         sessionStateAt A ss G.afterTrFrom
           { st with receiverChains := [], pqRatchetState := [] } ∗
         memRegion (s0.sp - 496#64) 400 ∗
         stackAt (s0.sp - 496#64) dropVecChainStackX ∗
         F_cs)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) target_pc sm
      ((G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
       vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
       memRegion (s0.sp - 496#64) 8 ∗
       ((s0.sp - 488#64) ↦₃₂ (b5 ++ b4).zeroExtend 32) ∗
       ((s0.sp - 484#64) ↦₃₂ b6.zeroExtend 32) ∗
       ((s0.sp - 480#64) ↦₆₄ w15) ∗
       ((s0.sp - 472#64) ↦₆₄ BitVec.ofNat 64 st.pqRatchetState.length) ∗
       ((s0.sp - 464#64) ↦₆₄ G.pq.ptr) ∗
       ((s0.sp - 280#64) ↦₆₄ w23) ∗
       ((s0.sp - 272#64) ↦₈ b31) ∗
       memRegion (s0.sp - 271#64) 7 ∗
       ((s0.sp - 264#64) ↦₃₂ rd0) ∗
       ((s0.sp - 260#64) ↦₁₆ rh4) ∗
       memRegion (s0.sp - 258#64) 26 ∗
       ((s0.sp - 232#64) ↦₃₂ u_232) ∗
       ((s0.sp - 228#64) ↦₁₆ u_228) ∗
       memRegion (s0.sp - 226#64) 18 ∗
       ((s0.sp - 208#64) ↦₃₂ u_208) ∗
       memRegion (s0.sp - 204#64) 20 ∗
       ((s0.sp - 184#64) ↦₆₄ rw22) ∗
       ((s0.sp - 176#64) ↦₁₆ rh30) ∗
       memRegion (s0.sp - 174#64) 14 ∗
       ((s0.sp - 160#64) ↦₆₄ 0x8000000000000014#64) ∗
       ((s0.sp - 152#64) ↦₆₄ (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))) ∗
       ((s0.sp - 144#64) ↦₆₄ 27#64) ∗
       ((s0.sp - 136#64) ↦₆₄ rw22) ∗
       ((s0.sp - 128#64) ↦₁₆ rh30) ∗
       memRegion (s0.sp - 126#64) 14 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       stackAt (s0.sp - 496#64) dropVecChainStackX ∗
       (A.pool ∗
        ((s0.sp - 456#64) ↦₆₄ G.chainsCap) ∗
        ((s0.sp - 448#64) ↦₆₄ G.chainsPtr) ∗
        ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
        vecU8Buf A G.pq.cap G.pq.ptr st.pqRatchetState ∗
        ((s0.sp - 432#64) ↦ₛ optSenderChainBytes st.senderChain senderPad) ∗
        ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
        ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
        ((s0.sp - 288#64) ↦₃₂ st.previousCounter) ∗
        ((s0.sp - 284#64) ↦₃₂ u_284) ∗
        memRegion ret 264 ∗
        sessionAfter208Frame A ss G st ∗
        F_cs))
      post := by
  have hfn : libsignalSessionCode.fnOff trFromName =
      num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by
    simp only [arm64_norm]
  have hdropSpe := dropSpe_ok_at_from_x hDropSpe
  have hdropCh := dropVecChain_ok_at_from_x hDropVecChain
  have hdealloc := dealloc_ok_at_from_x hA
  clear hDropSpe hDropVecChain
  have hsc_len : (optSenderChainBytes st.senderChain senderPad).length = 104 :=
    optSenderChainBytes_length st.senderChain hpad
  have hrk_len : (CryptoGames.HMAC.keyToBytes32 st.rootKey).length = 32 :=
    rk_bytes_length_32 st.rootKey
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 1064 59
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 1420 23
  dsimp only [tripleRatchetProgAtExt] at hpc hdropSpe hdropCh hdealloc hcont ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = entry
  examples_hide_fetches
  apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (232)) hfl hsym
  refine SepWP.fold (sessionStateAt_reassemble_after208 A ss G st hlik) (by sep_focus) ?_
  generalize hS_post :
    sessionStateAt A ss G.afterTrFrom { st with receiverChains := [], pqRatchetState := [] } = S_post at *
  cases hrem : st.remoteIdentity with
  | some rem =>
    have hrem_bs : remBs = rem.publicKey.bytes.toList := hrem_eq rem hrem
    subst hrem_bs
    dsimp only [remoteIdentityTag] at hx10
    refine CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom.SepWP.intro_rodata_missingRemoteIdentity himg hfl ?_
    refine SepWP.fold (memRegion_24_of_8_2_14 s0.sp rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold (speAt_missingRemoteIdentity_sp_160 A s0.sp img.base) (by sep_focus) ?_
    rw [stackAt_dropVecChain_eq_dropSpe_x s0.sp]
    apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))) hfl hsym
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hfl_454 hsym_454
    refine call_dropSpe_x (sp_val := s0.sp - 496#64) hdropSpe
      ⟨s0.sp - 160#64, _, .invalidSessionStructure .missingRemoteIdentity⟩
      hfl_454 hsym_454 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_focus) ?_
    intro s_458 hpc_458 hsp_458 hrun_458 _ hcs_458 htr_458 _ _
    rcases hcs_458 with ⟨hx19_458, hx20_458, hx21_458, hx22_458, hx23_458, hx24_458,
      hx25_458, hx26_458, hx27_458, hx28_458, hx29_458, hvregs_458⟩
    simp only [arm64_norm, hsp, hx19, hx20, hx25, hx26, hx27, hx28, hx29] at hpc_458 hsp_458 hx19_458 hx20_458 hx21_458 hx22_458 hx23_458 hx24_458 hx25_458 hx26_458 hx27_458 hx28_458 hx29_458 hvregs_458
    have hstack_dropSpe_fold :
        (memRegion (s0.sp - 16976#64) 64 ∗ stackAt (s0.sp - 496#64) dropSpeStackX) ⊢
          stackAt (s0.sp - 496#64) dropVecChainStackX :=
      Entails.of_eq (stackAt_dropVecChain_eq_dropSpe_x s0.sp).symm
    refine SepWP.fold hstack_dropSpe_fold (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sp_288_combine_prev s0.sp st.previousCounter u_284)) (by sep_focus) ?_
    refine SepWP.fold (Entails.refl (memRegion ret 264)) (by sep_focus) ?_
    refine SepWP.fold (Entails.refl (memRegion (s0.sp - 160#64) 48)) (by sep_focus) ?_
    rw [memRegion_48_split_8_2_38 s0.sp,
        sc_unpack_stack s0.sp hsc_split,
        rk_unpack_stack s0.sp hrk_split,
        ret_264_split_some ret,
        ret_200_split_lik ret,
        ret_232_split_rem ret]
    simp (config := { maxSteps := 2000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun u_152 => SepWP.exists_elim fun u_160 => ?_
    refine SepWP.exists_elim fun m30 => SepWP.exists_elim fun m22 => ?_
    refine SepWP.exists_elim fun m14 => SepWP.exists_elim fun m6 => ?_
    refine SepWP.exists_elim fun m4 => SepWP.exists_elim fun m0 => ?_
    refine SepWP.exists_elim fun l31 => SepWP.exists_elim fun l23 => ?_
    refine SepWP.exists_elim fun l15 => SepWP.exists_elim fun l7 => ?_
    refine SepWP.exists_elim fun l6 => SepWP.exists_elim fun l4 => ?_
    refine SepWP.exists_elim fun l0 => SepWP.exists_elim fun w24 => ?_
    refine SepWP.exists_elim fun w23_r => SepWP.exists_elim fun w22_r => ?_
    refine SepWP.exists_elim fun w21_r => SepWP.exists_elim fun w20_r => ?_
    refine SepWP.exists_elim fun w19_r => SepWP.exists_elim fun w18_r => ?_
    refine SepWP.exists_elim fun w17_r => SepWP.exists_elim fun w16_r => ?_
    refine SepWP.exists_elim fun w15_r => SepWP.exists_elim fun w14_r => ?_
    refine SepWP.exists_elim fun w13_r => SepWP.exists_elim fun w12_r => ?_
    refine SepWP.exists_elim fun w11_r => SepWP.exists_elim fun w10_r => ?_
    refine SepWP.exists_elim fun w9_r => SepWP.exists_elim fun w8_r => ?_
    refine SepWP.exists_elim fun w7_r => SepWP.exists_elim fun w6_r => ?_
    refine SepWP.exists_elim fun w5_r => SepWP.exists_elim fun w4_r => ?_
    refine SepWP.exists_elim fun w3_r => SepWP.exists_elim fun w2_r => ?_
    refine SepWP.exists_elim fun w1_r => SepWP.exists_elim fun w0_r => ?_
    wp_steps
    refine SepWP.fold (sc_pack_stack s0.sp hsc_split) (by sep_focus) ?_
    refine SepWP.fold (sc_pack_ret ret hsc_split) (by sep_focus) ?_
    refine SepWP.fold (rk_pack_stack s0.sp hrk_split) (by sep_focus) ?_
    refine SepWP.fold (rk_pack_ret ret hrk_split) (by sep_focus) ?_
    refine SepWP.fold (lik_pack_ret ret hlik_split2) (by sep_focus) ?_
    refine SepWP.fold (rem_pack_ret ret hrem_split) (by sep_focus) ?_
    refine SepWP.fold (ret_168_split_prev ret st.previousCounter u_284) (by sep_focus) ?_
    refine SepWP.fold (trResultAt_ok_intro A ret G st rem senderPad hclamp hchains hpad) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (sp_288_combine_prev s0.sp st.previousCounter u_284).symm) (by sep_focus) ?_
    refine SepWP.fold (memRegion_48_of_8_2_38 s0.sp rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_280_184_fold s0.sp w23 b31 rd0 rh4 u_232 u_228 u_208 rw22 rh30) (by sep_focus) ?_
    refine SepWP.fold
      (stack_496_40_fold s0.sp ((b5 ++ b4).zeroExtend 32) (b6.zeroExtend 32)
        w15 (BitVec.ofNat 64 st.pqRatchetState.length) G.pq.ptr) (by sep_focus) ?_
    refine SepWP.fold
      (memRegion_24_of_8_8_8 s0.sp G.chainsCap G.chainsPtr
        (BitVec.ofNat 64 st.receiverChains.length)) (by sep_focus) ?_
    refine SepWP.fold
      (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
        (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
        25000#64 st.previousCounter u_284) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hfl_f hsym_f
    have hcont' := hcont _ hfl_f hsym_f
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
    rw [hrem] at hcont'
    exact SepWP.mono_pre (by sep_frame) hcont'
  | none =>
    dsimp only [remoteIdentityTag] at hx10
    refine CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom.SepWP.intro_rodata_missingRemoteIdentity himg hfl ?_
    obtain ⟨ed0, eh4, ew6, ew14, eh22, herr_split, herr_ret⟩ :=
      exists_err22_split (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) rw22
    refine SepWP.fold (err22_unpack_stack s0.sp (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) rw22 herr_split) (by sep_focus) ?_
    rw [ret_264_split_none ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun r38 => SepWP.exists_elim fun r30 => ?_
    refine SepWP.exists_elim fun r22 => SepWP.exists_elim fun r20 => ?_
    refine SepWP.exists_elim fun r16 => SepWP.exists_elim fun r8 => ?_
    refine SepWP.exists_elim fun r0 => ?_
    by_cases hpq0 : G.pq.cap = 0
    · rw [hpq0] at hx20
      apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))) hfl hsym
      wp_steps
      refine SepWP.fold (err22_pack_stack s0.sp (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) rw22 herr_split) (by sep_focus) ?_
      refine SepWP.fold (err22_pack_ret ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) herr_ret r38) (by sep_focus) ?_
      refine SepWP.fold
        (trResultAt_err_missingRemoteIdentity_intro A ret G (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))) (by sep_focus) ?_
      refine SepWP.fold
        (memRegion_48_of_8_8_8_8_2_14 s0.sp 0x8000000000000014#64
          (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) 27#64 rw22 rh30) (by sep_focus) ?_
      refine SepWP.fold
        (stack_280_184_fold s0.sp w23 b31 rd0 rh4 ed0 eh4 ed0 rw22 rh30) (by sep_focus) ?_
      refine SepWP.fold
        (stack_496_40_fold s0.sp ((b5 ++ b4).zeroExtend 32) (b6.zeroExtend 32)
          w15 (BitVec.ofNat 64 st.pqRatchetState.length) G.pq.ptr) (by sep_focus) ?_
      refine SepWP.fold (vecAt_chains_stack_fold A s0.sp G st hchains) (by sep_focus) ?_
      refine SepWP.fold
        (vecU8Buf_zero_entails_emp A G.pq.cap G.pq.ptr st.pqRatchetState hpq0) (by sep_focus) ?_
      simp only [emp_sepConj]
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_ch hsym_ch
      refine call_dropVecChain_x (sp_val := s0.sp - 496#64) hdropCh
        ⟨s0.sp - 456#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
        hfl_ch hsym_ch (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm])
        (by sep_focus) ?_
      intro s_5a4 hpc_5a4 hsp_5a4 hrun_5a4 _ hcs_5a4 htr_5a4 _ _
      rcases hcs_5a4 with ⟨_, _, _, _, _, _, _, _, _, _, _, hvregs_5a4⟩
      simp only [arm64_norm, hsp] at hpc_5a4 hsp_5a4 hvregs_5a4
      wp_steps
      refine SepWP.fold
        (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
          (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
          25000#64 st.previousCounter u_284) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_f hsym_f
      have hcont' := hcont _ hfl_f hsym_f
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      rw [hrem] at hcont'
      exact SepWP.mono_pre (by sep_frame) hcont'
    · have hpq_beq_false : (G.pq.cap == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; exact hpq0
      have hpq_cond : ¬(G.pq.cap == 0#64) = true := by
        rw [hpq_beq_false]; decide
      obtain ⟨hpq_pos, hpq_lt, _⟩ := hpq_ne hpq0
      have hlay_pq : LayoutOk G.pq.cap.toNat 1 := ⟨hpq_pos, ⟨0, rfl⟩, by omega⟩
      apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) hfl hsym
      wp_steps
      refine SepWP.fold (err22_pack_stack s0.sp (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) rw22 herr_split) (by sep_focus) ?_
      refine SepWP.fold (err22_pack_ret ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) herr_ret r38) (by sep_focus) ?_
      refine SepWP.fold
        (trResultAt_err_missingRemoteIdentity_intro A ret G (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)))) (by sep_focus) ?_
      refine SepWP.fold
        (memRegion_48_of_8_8_8_8_2_14 s0.sp 0x8000000000000014#64
          (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) 27#64 rw22 rh30) (by sep_focus) ?_
      refine SepWP.fold
        (stack_280_184_fold s0.sp w23 b31 rd0 rh4 ed0 eh4 ed0 rw22 rh30) (by sep_focus) ?_
      refine SepWP.fold
        (stack_496_40_fold s0.sp ((b5 ++ b4).zeroExtend 32) (b6.zeroExtend 32)
          w15 (BitVec.ofNat 64 st.pqRatchetState.length) G.pq.ptr) (by sep_focus) ?_
      refine SepWP.fold (vecAt_chains_stack_fold A s0.sp G st hchains) (by sep_focus) ?_
      refine SepWP.fold
        (vecU8Buf_entails_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState hpq0) (by sep_focus) ?_
      rw [stackAt_dropVecChain_eq_allocHook_x s0.sp]
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_d hsym_d
      refine call_dealloc_x (sp_val := s0.sp - 496#64) (p := G.pq.ptr) (size := G.pq.cap.toNat) (align := 1)
        hdealloc hfl_d hsym_d (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        hlay_pq (by sep_focus) ?_
      intro s_59c hpc_59c hsp_59c hrun_59c _ hcs_59c htr_59c hfl_59c hsym_59c
      rcases hcs_59c with ⟨_, _, _, _, _, _, _, _, _, _, _, hvregs_59c⟩
      simp only [arm64_norm, hsp] at hpc_59c hsp_59c hvregs_59c
      have hstack_dealloc_fold :
          (memRegion (s0.sp - 16976#64) 96 ∗ stackAt (s0.sp - 496#64) extHookStack) ⊢
            stackAt (s0.sp - 496#64) dropVecChainStackX :=
        Entails.of_eq (stackAt_dropVecChain_eq_allocHook_x s0.sp).symm
      refine SepWP.fold hstack_dealloc_fold (by sep_focus) ?_
      apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))) hfl_59c hsym_59c
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_ch hsym_ch
      refine call_dropVecChain_x (sp_val := s0.sp - 496#64) hdropCh
        ⟨s0.sp - 456#64, G.chainsCap, G.chainsPtr, G.chains.zip st.receiverChains⟩
        hfl_ch hsym_ch (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm])
        (by sep_focus) ?_
      intro s_5a4 hpc_5a4 hsp_5a4 hrun_5a4 _ hcs_5a4 htr_5a4 _ _
      rcases hcs_5a4 with ⟨_, _, _, _, _, _, _, _, _, _, _, hvregs_5a4⟩
      simp only [arm64_norm, hsp_59c, hvregs_59c] at hpc_5a4 hsp_5a4 hvregs_5a4
      wp_steps
      refine SepWP.fold
        (stack_400_fold s0.sp (optSenderChainBytes st.senderChain senderPad)
          (CryptoGames.HMAC.keyToBytes32 st.rootKey) hsc_len hrk_len
          25000#64 st.previousCounter u_284) (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_f hsym_f
      have hcont' := hcont _ hfl_f hsym_f
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
      rw [hrem] at hcont'
      exact SepWP.mono_pre (by sep_frame) hcont'

private theorem trFrom_step_244_to_ret_x
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hRemoteIk : RemoteIdentityKeyOkExt img A ext)
    (hDropSpe : DropSpeOkX img A ext)
    (hDropVecChain : DropVecChainOkX img A ext)
    (x : TrFromGhost) (senderPad : List (BitVec 8))
    (s0 s : State) (post : State → SepProp → Prop)
    (u_284 : BitVec 32)
    (hpad : senderPad.length = 100)
    (hclamp : ∀ sc, x.st.senderChain = some sc →
      clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (hchains : x.G.chains.length = x.st.receiverChains.length)
    (hpq_ne : x.G.pq.cap ≠ 0 → 0 < x.G.pq.cap.toNat ∧ x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0)
    (hlik : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hlik_toNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length)
    (hrik : match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + 580#64)
    (hrun : s.status = .Running) (halign : (s0.sp &&& 0xf#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = x.G.localIk.ptr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 x.G.localIk.bytes.length)
    (hx8 : s.readReg64 .x8 = s0.sp - 160#64)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = x.G.pq.cap)
    (hx21 : s.readReg64 .x21 = x.G.pq.ptr)
    (hx22 : s.readReg64 .x22 = x.ss)
    (hx23 : s.readReg64 .x23 = 0x8000000000000014#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 184#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hsp : s.sp = s0.sp - 496#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hdone : ∀ sf,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.trace = s0.trace →
      sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sf
        (sessionStateAt A x.ss x.G.afterTrFrom x.model.2 ∗
         trResultAt A x.ret x.G x.model.1 ∗
         logOff img ∗ stackAt s0.sp trFromStackX ∗ A.pool)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      ((memRegion (s0.sp - 16976#64) 12288 ∗
        (x.G.localIk.ptr ↦ₛ x.G.localIk.bytes) ∗
        vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
        memRegion (s0.sp - 496#64) 40 ∗
        memRegion (s0.sp - 280#64) 184 ∗
        stackAt (s0.sp - 496#64) dropVecChainStack ∗
        (A.pool ∗
         ((s0.sp - 456#64) ↦₆₄ x.G.chainsCap) ∗
         ((s0.sp - 448#64) ↦₆₄ x.G.chainsPtr) ∗
         ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
         vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
         vecU8Buf A x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
         ((s0.sp - 432#64) ↦ₛ optSenderChainBytes x.st.senderChain senderPad) ∗
         ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
         ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
         ((s0.sp - 288#64) ↦₃₂ x.st.previousCounter) ∗
         ((s0.sp - 284#64) ↦₃₂ u_284) ∗
         memRegion x.ret 264 ∗
         sessionAfter208Frame A x.ss x.G x.st ∗
         (logOff img ∗ trFromSavedRegs s0.sp s0))))
      post := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, w15, w23, b31,
    hlik_split1, hlik_split2⟩ :=
    exists_localIk_split_of_length_32 x.st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨sc0, sc1, sc2, sc3, sc4, sc5, sc6, sc7, sc8, sc9, sc10, sc11, sc12, hsc_split⟩ :=
    exists_unpack64_of_length_104 (optSenderChainBytes_length x.st.senderChain hpad)
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_split⟩ :=
    exists_unpack64_of_length_32 (rk_bytes_length_32 x.st.rootKey)
  refine SepWP.mono_pre (by sep_frame)
    (trFrom_step_244_to_428 himg True.intro hRemoteIk x.ss x.G x.st s0 s (s0.readReg64 .lr)
      (memRegion (s0.sp - 16976#64) 12288 ∗
       A.pool ∗
       ((s0.sp - 456#64) ↦₆₄ x.G.chainsCap) ∗
       ((s0.sp - 448#64) ↦₆₄ x.G.chainsPtr) ∗
       ((s0.sp - 440#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
       vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
       vecU8Buf A x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       ((s0.sp - 432#64) ↦ₛ optSenderChainBytes x.st.senderChain senderPad) ∗
       ((s0.sp - 328#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) ∗
       ((s0.sp - 296#64) ↦₆₄ 25000#64) ∗
       ((s0.sp - 288#64) ↦₃₂ x.st.previousCounter) ∗
       ((s0.sp - 284#64) ↦₃₂ u_284) ∗
       memRegion x.ret 264 ∗
       sessionAfter208Frame A x.ss x.G x.st ∗
       trFromSavedRegs s0.sp s0) post
      hlik_split1 hlik hlik_toNat hrik hfl hsym hpc hrun halign htr
      hx0 hx1 hx8 hx21 hx22 hx23 hx24 hx25 hx29 hsp ?_)
  intro sm remBs rd0 rh4 rw6 rw14 rw22 rh30 u_232 u_228 u_208
    _ hrem_eq hrem_split hfl_m hsym_m hpc_m hrun_m htr_m
    hx8_m hx9_m hx10_m hx11_m hx12_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
    hx25_m hx26_m hx27_m hx28_m hx29_m hsp_m hvregs_m
  rw [hx19] at hx19_m
  rw [hx20] at hx20_m
  have hstack_dvcX_fold :
      (memRegion (s0.sp - 16976#64) 12288 ∗ stackAt (s0.sp - 496#64) dropVecChainStack) ⊢
        stackAt (s0.sp - 496#64) dropVecChainStackX :=
    Entails.of_eq (stackAt_dropVecChainX_split s0.sp).symm
  refine SepWP.fold hstack_dvcX_fold (by sep_focus) ?_
  refine SepWP.mono_pre (by sep_frame)
    (trFrom_step_428_to_0e8_x himg hA hDropSpe hDropVecChain
      x.ret x.ss x.G x.st senderPad s0 sm (s0.readReg64 .lr)
      (logOff img ∗ trFromSavedRegs s0.sp s0) post
      hpad hclamp hchains hpq_ne hlik hlik_split2 hsc_split hrk_split hrem_eq hrem_split
      hfl_m hsym_m hpc_m hrun_m halign htr_m
      hx8_m hx9_m hx10_m hx11_m hx12_m hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
      hx25_m hx26_m hx27_m hx28_m hx29_m hsp_m ?_)
  intro sf hfl_f hsym_f hpc_f hrun_f htr_f hsp_f hvregs_f
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
    (hvregs_f.trans hvregs_m).trans hvregs
  have hm1 : ∀ a, a = (match x.st.remoteIdentity with
        | some rem =>
          .ok ⟨⟨x.st.rootKey, x.st.senderChain, x.st.receiverChains,
                x.st.previousCounter, maxForwardJumps⟩,
               x.st.pqRatchetState, x.st.localIdentity, rem⟩
        | none => .error (.invalidSessionStructure .missingRemoteIdentity)) →
      trResultAt A x.ret x.G a = trResultAt A x.ret x.G x.model.1 := by
    rintro _ rfl
    rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
    cases rik <;> rfl
  rw [hm1 _ (by rfl), ← trFromGhost_model_snd x, stackAt_dropVecChainX_split s0.sp]
  have hfn : libsignalSessionCode.fnOff trFromName =
      num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by
    simp only [arm64_norm]
  generalize hentry : (tripleRatchetProgAtExt img.base ext).fnAddr trFromName = entry at hpc_f
  unfold trFromSavedRegs
  apply CryptoVerification.SepWP.of_sepWP_inv (mid := s0.readReg64 .lr) hfl_f hsym_f
  tr_from_fetches img.base (Rust.withPanics ext) hfn hentry 232 8
  wp_steps
  examples_clear_fetches
  refine SepWP.fold (stackAt_trFrom_fold s0.sp s0) (by sep_focus) ?_
  have hstack_trFromX_fold :
      (memRegion (s0.sp - 16976#64) 12288 ∗ stackAt s0.sp trFromStack) ⊢
        stackAt s0.sp trFromStackX :=
    Entails.of_eq (stackAt_trFromX_split s0.sp).symm
  refine SepWP.fold hstack_trFromX_fold (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hfl_ret hsym_ret
  refine SepWP.mono_pre (by sep_frame)
    (hdone _
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, hvregs_sf]⟩
      hfl_ret hsym_ret)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.trFrom_ok_ext_x
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hDeser : DeserializeOkExt img.base ext :=
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_ok img.base _)
    (hRemoteIk : RemoteIdentityKeyOkExt img A ext)
    (hDropSpe : DropSpeOkX img A ext)
    (hDropVecChain : DropVecChainOkX img A ext) :
    TrFromOkX img A ext := by
  have hb_align : img.base &&& 0xfff#64 = 0#64 := base_aligned_of_loads himg
  have hdeser := deserialize_ok_at_from hDeser
  clear hDeser
  simp only [TrFromOkX, Spec.inImage, trFromSpecX]
  wp_init x s0
  have hfl0 : img.FrozenLoaded s0 := by assumption
  have hsym0 : s0.symtab = img.symtab := by assumption
  have hx0 : s0.readReg64 .x0 = x.ss := by assumption
  have hw1 : (s0.readReg64 .x1).setWidth 32 = 0#32 := by assumption
  have hx8 : s0.readReg64 .x8 = x.ret := by assumption
  apply SepWP.with_post; intro post_ok hpost_ok
  have hfn : libsignalSessionCode.fnOff trFromName =
      num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by
    simp only [arm64_norm]
  have hstep10c := @trFrom_step_10c_to_244 img ext
  have hstepac := @trFrom_step_ac_to_244 img ext
  have hstep244 := @trFrom_step_244_to_ret_x img A ext himg hA hRemoteIk hDropSpe hDropVecChain
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 0 23
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 92 20
  tr_from_fetches_raw img.base (Rust.withPanics ext) hfn 264 1
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hpc hdeser hstep10c hstepac hstep244 ⊢
  have hentry_pc : (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = s0.pc := by
    simp only [arm64_norm, hpc]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr trFromName = entry
  examples_hide_fetches
  clear hpc
  have hpc : s0.pc = entry := hentry_pc.symm
  clear hentry_pc
  have halign0 : (s0.sp &&& 0xf#64 == 0#64) = true := by
    simpa only [State.spAligned] using hsp_align
  refine SepWP.mono_pre (sepConj_mono (sessionStateAt_expose_from A x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hlik, hlik_toNat, hchains, hcmn_chains, _, hpq_ne, hsc_some⟩ => ?_
  refine SepWP.mono_pre (sepConj_mono (sessionFromFrame_expose_remoteIk A x.ss x.G x.st) (Entails.refl _)) ?_
  simp only [sepConj_assoc]
  refine SepWP.pure_elim fun hrik => ?_
  obtain ⟨rk_b0, rk_b1, rk_b2, rk_b3, rk_b4, rk_b5, rk_b6, rk_w7, rk_w15, rk_w23, rk_b31, hrk⟩ :=
    exists_rootKey_split_of_length_32 (rk_bytes_length_32 x.st.rootKey)
  refine SepWP.fold (Entails.of_eq (stackAt_trFromX_split s0.sp)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_trFrom s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun r11 => SepWP.exists_elim fun r10 => ?_
  refine SepWP.exists_elim fun r9 => SepWP.exists_elim fun r8 => ?_
  refine SepWP.exists_elim fun r7 => SepWP.exists_elim fun r6 => ?_
  refine SepWP.exists_elim fun r5 => SepWP.exists_elim fun r4 => ?_
  refine SepWP.exists_elim fun r3 => SepWP.exists_elim fun r2 => ?_
  refine SepWP.exists_elim fun r1 => SepWP.exists_elim fun r0 => ?_
  refine SepWP.exists_elim fun u_144 => SepWP.exists_elim fun u_152 => ?_
  refine SepWP.exists_elim fun u_160 => SepWP.exists_elim fun u_284 => ?_
  refine SepWP.exists_elim fun u_288 => SepWP.exists_elim fun u_296 => ?_
  refine SepWP.fold (Entails.of_eq (stack_256_96_split s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun h_188 => SepWP.exists_elim fun d_192 => ?_
  refine SepWP.exists_elim fun b_200 => SepWP.exists_elim fun w_208 => ?_
  refine SepWP.exists_elim fun b_210 => SepWP.exists_elim fun b_211 => ?_
  refine SepWP.exists_elim fun b_212 => SepWP.exists_elim fun b_213 => ?_
  refine SepWP.exists_elim fun b_214 => SepWP.exists_elim fun b_215 => ?_
  refine SepWP.exists_elim fun b_216 => SepWP.exists_elim fun b_224 => ?_
  refine SepWP.exists_elim fun w_232 => ?_
  rw [hrk x.G.root.ptr]
  apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (92)) hfl0 hsym0
  wp_steps
  refine SepWP.fold (vecAt_nil_chains_0_8 A (x.ss + 72#64)) (by sep_focus) ?_
  have hsaved_fold :
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      trFromSavedRegs s0.sp s0 := Entails.refl _
  refine SepWP.fold hsaved_fold (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hfl_5c hsym_5c
  cases hsc_opt : x.st.senderChain with
  | none =>
    cases hsender_opt : x.G.sender with
    | some _ => simp [hsender_opt, hsc_opt] at hsc_some
    | none =>
      have hclamp_none : ∀ sc, x.st.senderChain = some sc →
          clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes := by
        intro _ h; rw [hsc_opt] at h; cases h
      have hsc_none_unfold :
          optSenderChainAt A (x.ss + 144#64) none none =
            (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) := by
        dsimp only [optSenderChainAt, noneCap]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hsc_none_fold :
          (((x.ss + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.ss + 152#64) 96) ⊢
            optSenderChainAt A (x.ss + 144#64) x.G.sender x.st.senderChain := by
        rw [hsender_opt, hsc_opt, hsc_none_unfold]; exact Entails.refl _
      apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (268)) hfl_5c hsym_5c
      refine SepWP.fold (Entails.of_eq hsc_none_unfold) (by sep_focus) ?_
      wp_steps
      refine SepWP.fold hsc_none_fold (by sep_focus) ?_
      have hrk_fold :
          ((x.G.root.ptr ↦₈ rk_b0) ∗ ((x.G.root.ptr + 1#64) ↦₈ rk_b1) ∗
           ((x.G.root.ptr + 2#64) ↦₈ rk_b2) ∗ ((x.G.root.ptr + 3#64) ↦₈ rk_b3) ∗
           ((x.G.root.ptr + 4#64) ↦₈ rk_b4) ∗ ((x.G.root.ptr + 5#64) ↦₈ rk_b5) ∗
           ((x.G.root.ptr + 6#64) ↦₈ rk_b6) ∗ ((x.G.root.ptr + 7#64) ↦₆₄ rk_w7) ∗
           ((x.G.root.ptr + 15#64) ↦₆₄ rk_w15) ∗ ((x.G.root.ptr + 23#64) ↦₆₄ rk_w23) ∗
           ((x.G.root.ptr + 31#64) ↦₈ rk_b31)) ⊢
          (x.G.root.ptr ↦ₛ CryptoGames.HMAC.keyToBytes32 x.st.rootKey) := by
        rw [hrk x.G.root.ptr]; exact Entails.refl _
      refine SepWP.fold hrk_fold (by sep_focus) ?_
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_10c hsym_10c
      refine SepWP.mono_pre (by unfold trFrom10cTail; sep_frame)
        (hstep10c A x.ret x.ss x.G x.st s0 _ (s0.readReg64 .lr)
          (memRegion (s0.sp - 16976#64) 12288 ∗ trFrom10cTail img A x s0) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hcmn_chains hfl_10c hsym_10c
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          halign0
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *]; rfl)
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          ?_)
      intro s_244 hfl_244 hsym_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      refine SepWP.fold (scRawCells_none_entails s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun senderPad => ?_
      refine SepWP.pure_elim fun hpad => ?_
      rw [← hsc_opt]
      refine SepWP.mono_pre (by unfold trFrom10cTail; sep_frame)
        (hstep244
          x senderPad s0 s_244 post_ok u_284 hpad hclamp_none hchains hpq_ne hlik hlik_toNat hrik
          hfl_244 hsym_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨afterTrFrom_decRel x.G, htr_ret⟩, hm⟩
  | some sc =>
    cases hsender_opt : x.G.sender with
    | none => simp [hsender_opt, hsc_opt] at hsc_some
    | some sg =>
      have hlog : logOff img = ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) := rfl
      apply CryptoVerification.SepWP.of_sepWP_inv (mid := entry + bv% (172)) hfl_5c hsym_5c
      refine SepWP.fold (optSenderChainAt_some_expose_from A x.ss sg sc) (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨hsrk, hsrk_lt, hsrk_toNat, hclamp_sc, hsrk_cmn, hck_cmn⟩ => ?_
      have hclamp_some : ∀ sc', x.st.senderChain = some sc' →
          clampScalar sc'.ratchetKey.privateKey.bytes = sc'.ratchetKey.privateKey.bytes := by
        intro sc' h; rw [hsc_opt] at h; cases h; exact hclamp_sc
      rw [stack_456_160_split_deser s0.sp, hlog]
      refine SepWP.fold (memRegion_33_to_tag_and_32 (s0.sp - 456#64)) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWP.exists_elim fun tag0 => SepWP.exists_elim fun out32 => ?_
      refine SepWP.pure_elim fun hout32_len => ?_
      wp_steps
      wp_apply
      rw [← hlog]
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hfl_ac hsym_ac
      refine SepWP.mono_pre (by unfold trFrom10cTail; sep_frame)
        (hstepac A x sg sc s0 _ (memRegion (s0.sp - 16976#64) 12288 ∗ trFrom10cTail img A x s0) post_ok
          w_208 b_200 d_192 h_188 u_296 u_288 u_284
          hrk hsender_opt hsc_opt hclamp_sc hsrk_cmn hck_cmn hcmn_chains hfl_ac hsym_ac
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          halign0
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          ?_)
      intro s_244 hfl_244 hsym_244 hpc_244 hrun_244 htr_244
        hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244 hvregs_244
      have hpad : (List.replicate 100 0#8).length = 100 := by simp
      refine SepWP.mono_pre (by unfold trFrom10cTail; sep_frame)
        (hstep244
          x (List.replicate 100 0#8) s0 s_244 post_ok u_284 hpad hclamp_some hchains hpq_ne hlik hlik_toNat hrik
          hfl_244 hsym_244 hpc_244 hrun_244 halign0 htr_244
          hx0_244 hx1_244 hx8_244 hx19_244 hx20_244 hx21_244 hx22_244 hx23_244 hx24_244 hx25_244 hx29_244 hsp_244
          (by simp only [arm64_norm, *])
          ?_)
      intro sf hpc_ret hrun_ret htr_ret hsp_ret hcs_ret _ _
      subst hpost_ok
      apply SepWP.done hpc_ret hrun_ret
      refine ⟨fun hm => ?_, hsp_ret, hcs_ret⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨afterTrFrom_decRel x.G, htr_ret⟩, hm⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.trFrom_ok_of_allocX
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) :
    TrFromOkX img A ext :=
  CryptoVerification.Cli.LibsignalTripleRatchet.trFrom_ok_ext_x himg hA
    (CryptoVerification.LibsignalTripleRatchet.Glue.deserializeOk_ext img.base ext)
    (CryptoVerification.LibsignalTripleRatchet.Glue.remoteIdentityKeyOk_ext img A ext himg)
    (CryptoVerification.LibsignalTripleRatchet.Glue.dropSpeOk_ext_x himg hA)
    (CryptoVerification.LibsignalTripleRatchet.Glue.drop_vec_chain_ok_ext_x hA)

end LibsignalBinary.Proofs.Cli.TripleRatchet.ExtTrFromX
