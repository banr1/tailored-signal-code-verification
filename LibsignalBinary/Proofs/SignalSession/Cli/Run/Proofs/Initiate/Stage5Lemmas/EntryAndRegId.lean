/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDrop
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBase
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Fetch

/-!
# Stage 5 Entry and Unacknowledged PreKey Metadata

Verifies Stage 5 from `+0x1484` (`offEntry`) across `set_unacknowledged_pre_key_message` and
`set_unacknowledged_kyber_pre_key_id` into `stage5_reg_and_branch_ok`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm, -wp_norm] fsp_stage5_eqs
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

@[local arm64_norm, local wp_norm]
private theorem fsp_compound_offs (fsp : BitVec 64) :
    fsp + 0xe0#64 + 8#64 = fsp + 0xe8#64 ∧ fsp + 0xf0#64 + 8#64 = fsp + 0xf8#64 ∧
    fsp + 0xf8#64 + 8#64 = fsp + 0x100#64 ∧ fsp + 0x100#64 + 8#64 = fsp + 0x108#64 ∧
    fsp + 0x80#64 + 168#64 = fsp + 0x128#64 ∧ fsp + 0x80#64 + 192#64 = fsp + 0x140#64 ∧
    fsp + 0x80#64 + 536#64 = fsp + 0x298#64 ∧ fsp + 0x460#64 + 0x154#64 = fsp + 0x5b4#64 ∧
    fsp + 4096#64 + 1536#64 = fsp + 0x1600#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-- Ext-parameterized implementation of `initiate_stage5_ok` from Cut 4 (`offEntry`) to `lr`. -/
theorem initiate_stage5_ok_impl_ext {img : Obj.Image} {A : RustAlloc}
    {P : PEParams} {extP : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hExt : Stage5ExternDeps img A extP)
    (hStore : InitStoreCalleesExt img A extP B stk)
    (hCal : Stage5CalleesExt img A extP)
    (hS : S.initiate = initDef X P)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (_hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : S5AtStage5 img P extP X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base extP) (s0.readReg64 .lr) s5
      (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0)
      Q Qp (initOom s0) := by
  apply sepWPp_with_oom
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f :=
    fun sf P_f hoom => hpanic sf P_f (initPanicPost_of_oom hoom (entails_anyHeap _))
  have hfs0 : s0.fs.files = x.F := hs5.ctrl.files0.symm.trans hs5.files
  have hx19_0 : s5.readReg64 (.gpr 19#5) = x.ret := hs5.ctrl.x19.trans hs5.x8
  have halign_s5 : s5.spAligned = true := spAligned_fsp hs5.ctrl.spAligned hs5.ctrl.sp
  have hrun0 : s5.status = .Running := hs5.ctrl.run
  have hsp0 : s5.sp = fsp := hs5.ctrl.sp
  have hx20_0 : s5.readReg64 (.gpr 20#5) = fsp + 0x460#64 := hs5.x20
  obtain ⟨hekU8Len, hekEncEq, hkemLen, hkyberKey⟩ :=
    initiateKeys_hdr_props hs5.ekPairEq hs5.keysOk
  have hekLen : ekASk.length = 32 ∧ ekAPk.length = 32 := by
    let ekSeed : List.Vector (BitVec 8) 32 := ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    let ekKP := keyPairOf P.C ekSeed
    have hek : ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList :=
      hs5.ekPairEq
    exact ⟨hek.1 ▸ ekKP.privateKey.bytes.toList_length,
           hek.2 ▸ ekKP.publicKey.bytes.toList_length⟩
  have hpc0 : s5.pc = (tripleRatchetProgAtExt img.base extP).fnAddr cliInitiateName + offEntry :=
    hs5.ctrl.pc
  have hfn := cliInitiate_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode stage5EpilogueBin img.base
    (Rust.withPanics extP) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate")) 5252 52
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hpc0
  generalize_entry h_entry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics extP)).fnAddr cliInitiateName =
      entry
  examples_hide_fetches
  have hSetMsg : subroutine_ok (tripleRatchetProgAtExt img.base extP)
      (entry +
        bv% (2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_pre_key_message" -
          ls_off% "libsignal_cli_handshake::initiate"))
      (Slots.setUnackPreKeyMsgExtStackEpochSpec A img) :=
    @Eq.subst (BitVec 64)
      (fun c => subroutine_ok (tripleRatchetProgAtExt img.base extP) c
        (Slots.setUnackPreKeyMsgExtStackEpochSpec A img))
      _ _ ((s5_setUnackMsg_fnAddr_eq_ext img extP).symm.trans (congrArg (· + _) h_entry))
      hCal.setUnackPreKeyMsg
  have hSetKyb : subroutine_ok (tripleRatchetProgAtExt img.base extP)
      (entry +
        bv% (2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id" -
          ls_off% "libsignal_cli_handshake::initiate"))
      Pqxdh.setUnackKyberPreKeyIdSpec :=
    @Eq.subst (BitVec 64)
      (fun c => subroutine_ok (tripleRatchetProgAtExt img.base extP) c Pqxdh.setUnackKyberPreKeyIdSpec)
      _ _ ((s5_setUnackKyb_fnAddr_eq_ext img extP).symm.trans (congrArg (· + _) h_entry))
      hCal.setUnackKyberId
  have h_entry_box : ∃ _ : Unit, (tripleRatchetProgAtExt img.base extP).fnAddr cliInitiateName = entry :=
    ⟨(), h_entry⟩
  clear h_entry
  conv =>
    arg 4
    unfold stage5Mem
    dsimp only
    rw [show s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp from rfl]
    simp only [sepConj_assoc]
  s5_have_eq hpScr : memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗ ?scrRem := by
    s5_ac_rfl
  refine sepWPp_conseq (Entails.trans (Entails.of_eq hpScr)
    (sepConj_mono_left (scratch_split fsp))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro w5c0
  apply SepWPp.exists_elim; intro w5c8
  apply SepWPp.exists_elim; intro w5d0
  s5_have_eq hpBun :
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗ ?bunRem := by
    s5_ac_rfl
  refine s5_apply_lens hpBun fun R m hm => ?_
  obtain ⟨BRest, hkpkLen, hmBun, hfoldBundle⟩ :=
    cliBundleAt_stage5_lens x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr R m hm
  simp only [← sepConj_assoc] at hmBun
  refine ⟨_, hmBun, ?_⟩
  obtain ⟨_, _, halice, hpend0, ⟨kg, hkyb0, hkgBytes⟩, _, _⟩ := hs5.canonPre
  s5_have_eq hpSS : sessionStateAt A (fsp + 0x460#64) sg ss ∗ ?ssRem := by
    s5_ac_rfl
  refine s5_apply_lens hpSS fun R2 m2 hm2 => ?_
  obtain ⟨capKyb, w0_kyb, w1_kyb, SSRest, _, hcapKybNe, hmSS, hfoldUnack⟩ :=
    sessionState_unack_lens A (fsp + 0x460#64) sg ss hpend0 hkyb0
      (pendBytes := (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
      (by dsimp only [PublicKey.serialize]; simp) R2 m2 hm2
  simp only [← sepConj_assoc] at hmSS
  refine ⟨_, hmSS, ?_⟩
  conv => arg 4; unfold initArgsAt; rw [stage3KeySlotsAt_unfold]; simp only [sepConj_assoc]
  apply sepWPp_step_to_frozen_mem hs5.ctrl.inv
    (mid := entry +
      bv% (2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_pre_key_message" -
        ls_off% "libsignal_cli_handshake::initiate"))
  · s5_clear_callees
    dsimp only [tripleRatchetProgAtExt, offEntry] at hpc0 ⊢
    wp_steps
    s5_step_done
  intro _ hF1 hsym1
  let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
  let gUnack : Pqxdh.TopLevel.SetUnackExactGhost :=
    { statePtr := fsp + 0x460#64
      optOpkTag := opkFlag
      optOpkVal := opkId
      spkId := x.bundle.spkId
      baseKeyPtr := fsp + 0x298#64
      baseKeyBytes := toU8 ekAPk }
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (unack_ext_le_stkSub hstk) (stkSub_hi hstk64),
        stackAt_split_setUnack_ext fsp]
    simp only [sepConj_assoc]
  refine s5_call_setUnackMsg_ext (ret_pc := entry + offAfterUnackMsg)
    hExt hSetMsg fsp gUnack ?eF1
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp0])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s5)
    (by dsimp only [offAfterUnackMsg]; wp_norm_goal)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hs5.trace]) ⟨hF1, hsym1⟩
    (by dsimp only [gUnack]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_0])
    (by dsimp only [gUnack, opkFlag]; wp_norm_goal)
    (by dsimp only [gUnack]; wp_norm_goal)
    (by dsimp only [gUnack]; wp_norm_goal)
    (by dsimp only [gUnack]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp0])
    (by wp_norm_goal) (by wp_norm_goal)
    hekU8Len hpan ?ePre1 ?_
  case ePre1 =>
    inImageKitClearInvHyps
    dsimp only [gUnack]
    rw [bytesToBv8_toU8 ekAPk]
    s5_close_frame
  intro sm1 hpc1 hrun1 hsp1 hal1 hcs1 hinv1 htr1 hfs1
  have hfs1' : sm1.fs.files = x.F := hfs1.trans hs5.files
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_0, hx20_0, hs5.ctrl.vregs] at hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  s5_rw_pre (stackAt_split_setUnack_ext fsp).symm
  s5_rw_pre (s5_stackAt_sub_split fsp (unack_ext_le_stkSub hstk) (stkSub_hi hstk64)).symm
  apply sepWPp_step_to_frozen_mem hinv1
    (mid := entry +
      bv% (2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id" -
        ls_off% "libsignal_cli_handshake::initiate"))
  · s5_clear_callees
    dsimp only [tripleRatchetProgAtExt, offAfterUnackMsg] at hpc1 ⊢
    wp_steps
    s5_step_done
  intro _ hF2 hsym2
  refine s5_call_setUnackKyb_ext (ret_pc := entry + offAfterUnackKyb)
    hExt hSetKyb fsp (fsp + 0x460#64) capKyb w0_kyb x.bundle.kpkId ?eF2
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal1)
    (by dsimp only [offAfterUnackKyb]; wp_norm_goal)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr1]) ⟨hF2, hsym2⟩
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_1])
    (by wp_norm_goal) hcapKybNe
    hpan ?ePre2 ?_
  case ePre2 => s5_close_frame
  intro sm2 hpc2 hrun2 hsp2 _hal2 hcs2 hinv2 htr2 hfs2
  have hfs2' : sm2.fs.files = x.F := hfs2.trans hfs1'
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_1, hx20_1, hvregs_1] at hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  conv =>
    arg 4
    dsimp only [gUnack]
    try rw [bytesToBv8_toU8 ekAPk]
    try rw [hekEncEq]
  s5_have_eq hpUnackVec :
      (Pqxdh.Initiator.vecU8 A ((fsp + 0x460#64) + 0xf8#64)
        (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize ∗
       memRegion ((fsp + 0x460#64) + 0x124#64) 4) ∗ ?unackVecRem := by
    s5_ac_rfl
  refine sepWPp_conseq (Entails.trans (Entails.of_eq hpUnackVec)
    (sepConj_mono_left (sepConj_mono_right (memRegion_4_entails_32 ((fsp + 0x460#64) + 0x124#64))))) ?_
  conv =>
    arg 4
    unfold Pqxdh.Initiator.vecU8
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro padVal
  apply SepWPp.exists_elim; intro dataPtr
  refine SepWPp.pure_elim fun hdataNonNull => ?_
  have hssFolded := hfoldUnack opkFlag opkId x.bundle.spkId x.bundle.kpkId padVal dataPtr hdataNonNull
  s5_have_eq hpFoldSS :
      ((((fsp + 0x460#64) + 0xf8#64) ↦₆₄ 33#64) ∗
        (((fsp + 0x460#64) + 0x100#64) ↦₆₄ dataPtr) ∗
        (((fsp + 0x460#64) + 0x108#64) ↦₆₄ 33#64) ∗
        (dataPtr ↦ₛ (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize) ∗
        A.live dataPtr 33 1 ∗
        (((fsp + 0x460#64) + 0x110#64) ↦₃₂ opkFlag) ∗
        (((fsp + 0x460#64) + 0x114#64) ↦₃₂ opkId) ∗
        (((fsp + 0x460#64) + 0x118#64) ↦₆₄ 0#64) ∗
        (((fsp + 0x460#64) + 0x120#64) ↦₃₂ x.bundle.spkId) ∗
        (((fsp + 0x460#64) + 0x124#64) ↦₃₂ padVal) ∗
        (((fsp + 0x460#64) + 0x128#64) ↦₆₄ capKyb) ∗
        (((fsp + 0x460#64) + 0x140#64) ↦₃₂ x.bundle.kpkId) ∗ SSRest) ∗ ?afterFoldSS := by
    conv => lhs; simp (config := { zetaDelta := false }) only [
      show ((fsp + 0x460#64) + 0xf8#64) + 8#64 = (fsp + 0x460#64) + 0x100#64 by bv_omega,
      show ((fsp + 0x460#64) + 0xf8#64) + 16#64 = (fsp + 0x460#64) + 0x108#64 by bv_omega,
      show (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize.length = 33 by
        dsimp only [PublicKey.serialize]; simp,
      show BitVec.ofNat 64 33 = 33#64 from rfl]
    s5_ac_rfl
  refine sepWPp_conseq (Entails.trans (Entails.of_eq hpFoldSS) (sepConj_mono_left hssFolded)) ?_
  obtain ⟨_, h_init_entry⟩ := h_entry_box
  refine sepWPp_conseq ?_
    (stage5_reg_and_branch_ok_ext (dataPtr := dataPtr) (w5c0 := w5c0) (w5c8 := w5c8) (w5d0 := w5d0)
      (padVal := padVal) (w1_kyb := w1_kyb) (kg := kg)
      himg hExt hStore hCal hS hinitOk hstk hstk64 hs5
      halice hkgBytes hkemLen hkyberKey hekLen hkpkLen hfoldBundle
      (hpc2.trans (congrArg (· + offAfterUnackKyb) h_init_entry.symm))
      hrun2 hsp2 hvregs_2 hinv2 htr2 hfs0 hfs2' hx19_2 hx20_2 hpost hpan)
  inImageKitClearInvHyps
  dsimp only [initArgsAt]
  conv =>
    rhs
    rw [show s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp from rfl, stage3KeySlotsAt_unfold]
    simp only [sepConj_assoc]
  conv =>
    rhs
    pattern ((fsp + 0x300#64) ↦₃₂ _)
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm]
  conv =>
    rhs
    pattern ((fsp + 0x438#64) ↦₈ _)
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm]
  conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
  exact Entails.of_eq (by s5_ac_rfl)

theorem initiate_stage5_ok_impl {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : AtStage5 img W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s5
      (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0)
      Q Qp (initOom s0) :=
  initiate_stage5_ok_impl_ext himg (stage5ExternDeps_of_runHooks hh)
    (initStoreCallees_to_ext hStore) (Stage5CalleesExt.of_initLocalCallees hLocal)
    hS hinitOk hcoinsLt hstk hstk64 (S5AtStage5.of_atStage5 hs5) hpost hpanic

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
