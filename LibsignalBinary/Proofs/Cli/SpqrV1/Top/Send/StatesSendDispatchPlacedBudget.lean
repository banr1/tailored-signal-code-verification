/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Unified 11-Arm `<States>::send` Dispatch (Block `427`)

Assembles all 11 budget-threaded `<States>::send` arms and post-arm reassembly (`+3068 -> +3196`)
under `StatesSendTightEnv` and `StatesSendEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (call_memcpy_bytes_vm
   step_send_post_arm_3068_to_3196_placed_vm
   step_send_post_arm_3068_to_3196_sepWP_placed
   step_send_post_arm_3068_to_3196_placed
   StatesSendEnvOfEnv
   StatesSendEnv
   statesSendEnvOfEnv_default_eq
   StatesSendTightEnv
   statesSendEnvOfEnv_tight_eq
   statesSendEnvOfEnv_nonempty
   statesSendEnv_nonempty
   statesSendTightEnv_nonempty
   SpqrSendAt3196SepWPPlaced
   SpqrSendAt3196Placed
   step_send_post_arm_cont_sepWP_placed
   step_send_post_arm_cont_placed)

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (SpqrSendJoinStatePlaced of_sepWP_lscro spqrCoinsAtPlaced
   spqrMlkemEncaps1Sym spqrMlkemFromSeedSym spqrMlkemPk1Sym spqrMlkemPk2Sym)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB MlKem States StatesPanic StatesResult V1Send
   mlkemEncaps1Spec mlkemFromSeedSpec mlkemPk1Spec mlkemPk2Spec spqrAuthApi
   spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded)
open CryptoVerification.SpqrV1.Drop (chunkedKeysSampledToCt1Received chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesWord0 spqrSendCalleeStack statesSendArmOffset statesSendPreArmScratch)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX Ct1ReceivedSendEkChunkPlacedOkX
   Ct1ReceivedSendEkChunkPlacedOkXOfEnv Ct1ReceivedSendEkChunkTightPlacedOkX
   Ct1SampledSendCt1ChunkPlacedOkX Ct1SampledSendCt1ChunkPlacedOkXOfEnv
   Ct1SampledSendCt1ChunkTightPlacedOkX Ct2SampledSendCt2ChunkPlacedOkX
   Ct2SampledSendCt2ChunkPlacedOkXOfEnv Ct2SampledSendCt2ChunkTightPlacedOkX
   EkReceivedCt1SampledSendCt1ChunkPlacedOkX EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv
   EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX EncodeBytesPlacedOkX
   HeaderSentSendEkChunkPlacedOkX HeaderSentSendEkChunkPlacedOkXOfEnv
   HeaderSentSendEkChunkTightPlacedOkX PolyNextChunkPlacedOkX spqrLogLevelZeroPlacedAt
   spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
  (memRegion_190_928_eq memRegion_4080_104_eq memRegion_4192_504_eq
   statesSendImmFrame statesSendLeafFrame statesSendPreArmScratch_eq_leaf
   step_send_post_arm_cont_imm_sepWP_placed step_send_post_arm_cont_leaf_sepWP_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (AuthUpdatePlacedOkX HkdfToVecPlacedOkX spqrRustAllocZeroedSym)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudget
  (HeaderReceivedArmEnv step_send_arm_headerReceived_sepWP_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3PlacedBudget
  (KeysUnsampledArmEnv step_send_arm_keysUnsampled_sepWP_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
  (AuthMacHdrPinnedPlacedOkX DoReserve2PlacedOkX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
  (of_sepWP_lscro_plain step_send_arm_ct1Acknowledged_placed step_send_arm_ekSentCt1Received_placed
   step_send_arm_noHeaderReceived_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudget
  (step_send_arm_ct1Sampled_placed_sepWP_ofEnv step_send_arm_ct2Sampled_placed_sepWP_ofEnv
   step_send_arm_ekReceivedCt1Sampled_placed_sepWP_ofEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2PlacedBudgetAux
  (step_send_arm_ct1Received_placed_sepWP_ofEnv step_send_arm_headerSent_placed_sepWP_ofEnv
   step_send_arm_keysSampled_placed_sepWP_ofEnv)

variable [LibsignalPlacement]

omit [LibsignalPlacement] in
private theorem states_send_ok_elim {F : ShaCompress} {α : Type}
    {r : Except StatesPanic α} {f : α → V1Send spqrPolyApi (spqrAuthApi F) × Bytes}
    {sOut : V1Send spqrPolyApi (spqrAuthApi F)} {tape' : Bytes}
    (h : (StatesResult.ofPanic r >>= fun x => Except.ok (f x)) = Except.ok (sOut, tape')) :
    ∃ x, r = Except.ok x ∧ f x = (sOut, tape') := by
  cases r with
  | error p => contradiction
  | ok x => exact ⟨x, rfl, Except.ok.inj h⟩

set_option maxHeartbeats 1200000 in
/-- Envelope-parametric non-panicking `SepWP` unified 11-arm `<States>::send` + post-arm
    reassembly (`statesSendArmOffset st0 -> +3196`) when `st0.send K tape = .ok (sOut, tape')`. -/
theorem step_send_statesSend_sepWP_placed_ofEnv {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {EnvHsEk : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
    {EnvCt1rEk : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    {EnvCt1sCt1 : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {EnvEkrCt1 : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {EnvCt2sCt2 : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (hhs_call : HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F EnvHsEk ext)
    (hct1r_call : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F EnvCt1rEk ext)
    (hct1s_call : Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F EnvCt1sCt1 ext)
    (hct2s_call : Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F EnvCt2sCt2 ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F EnvEkrCt1 ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    (hfit : FitsEnv M lim st_b
      (StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp st0 tape))
    {tgt : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
      statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196SepWPPlaced (ctl := ctl) A lim st_b
      (StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp st0 tape)
      ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state tgt Frame post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  subst hP; cases st0 with
  | keysUnsampled st =>
    obtain ⟨⟨outSt, chunk, tape1⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2.symm with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.keysUnsampled st) tape =
        KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    unfold statesSendPreArmScratch
    refine step_send_arm_keysUnsampled_sepWP_placed A lim ext hA hcoinsFill hseed hpk1 hpk2
      hmac_call hres_call henc_call hnc_call hpk1_slice hpk2_slice
      sp cur tape tape' st outSt chunk h1 st_b hfit
      (Frame := optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗ memRegion (sp + 0x190#64) 928 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 32#64) 16 ∗ memRegion (sp + 4064#64) 16 ∗ Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28_0 hvregs
      (by rw [show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]; sep_ac_rfl)
      fun s1 evs hevs hinv1 hjoin1 => ?_
    have hjoin1' : SpqrSendJoinStatePlaced sp ext s0 s1 _ _ :=
      ⟨hjoin1.1, hjoin1.2, hjoin1.3, hjoin1.4, hjoin1.5, hjoin1.6, hjoin1.7, hjoin1.8, hjoin1.9, hjoin1.10, hjoin1.11⟩
    refine step_send_post_arm_cont_sepWP_placed A lim st_b evs
      (KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape) hevs ext hA
      sp cur tape tape' chain none hjoin1' trivial hsp_align hinv1 ?_ hnext
    unfold statesSendPreArmScratch
    rw [show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
    exact Entails.of_eq (by sep_ac_rfl)
  | keysSampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.keysSampled st) tape =
        EnvCt1rEk
          { outA := sp + 0x1260#64, stA := sp + 0x958#64,
            st := chunkedKeysSampledToCt1Received st,
            outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    dsimp only at hnext
    rw [statesSendPreArmScratch_eq_leaf sp 504]
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_keysSampled_placed_sepWP_ofEnv A lim st_b ext hA hct1r_call
      sp st outSt chunk h1 hfit
      (Frame := statesSendLeafFrame (ctl := ctl) A.repAlloc sp cur tape chain 504 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; sep_ac_rfl) fun s1 evs hevs hinv1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro _
    exact step_send_post_arm_cont_leaf_sepWP_placed A lim st_b evs _ hevs ext hA
      sp cur tape chain 504 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | headerSent st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.headerSent st) tape =
        EnvHsEk { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    dsimp only at hnext
    rw [statesSendPreArmScratch_eq_leaf sp 880]
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_headerSent_placed_sepWP_ofEnv A lim st_b ext hA hhs_call
      sp st outSt chunk h1 hfit
      (Frame := statesSendLeafFrame (ctl := ctl) A.repAlloc sp cur tape chain 880 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; sep_ac_rfl) fun s1 evs hevs hinv1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro _
    exact step_send_post_arm_cont_leaf_sepWP_placed A lim st_b evs _ hevs ext hA
      sp cur tape chain 880 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ct1Received st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.ct1Received st) tape =
        EnvCt1rEk { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    dsimp only at hnext
    rw [statesSendPreArmScratch_eq_leaf sp 504]
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ct1Received_placed_sepWP_ofEnv A lim st_b ext hA hct1r_call
      sp st outSt chunk h1 hfit
      (Frame := statesSendLeafFrame (ctl := ctl) A.repAlloc sp cur tape chain 504 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; sep_ac_rfl) fun s1 evs hevs hinv1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro _
    exact step_send_post_arm_cont_leaf_sepWP_placed A lim st_b evs _ hevs ext hA
      sp cur tape chain 504 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ekSentCt1Received st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.ekSentCt1Received st) tape =
        (fun evs => evs = []) := rfl
    rw [henv_eq] at hnext
    dsimp only at hnext
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ekSentCt1Received_placed A lim st_b ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) A.repAlloc sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; sep_ac_rfl) fun s1 hjoin1 _ => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm_sepWP_placed A lim st_b (fun evs => evs = []) rfl ext hA
      sp cur tape chain hjoin1 rfl hsp_align hinv1 hnext
  | noHeaderReceived st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.noHeaderReceived st) tape =
        (fun evs => evs = []) := rfl
    rw [henv_eq] at hnext
    dsimp only at hnext
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_noHeaderReceived_placed A lim st_b ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) A.repAlloc sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; sep_ac_rfl) fun s1 hjoin1 _ => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm_sepWP_placed A lim st_b (fun evs => evs = []) rfl ext hA
      sp cur tape chain hjoin1 trivial hsp_align hinv1 hnext
  | headerReceived st =>
    obtain ⟨⟨outSt, chunk, ek, tape1⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2.symm with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.headerReceived st) tape =
        HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    unfold statesSendPreArmScratch
    rw [memRegion_190_928_eq sp, memRegion_4080_104_eq sp, memRegion_4192_504_eq sp]
    refine step_send_arm_headerReceived_sepWP_placed A lim ext hA hZero hcoinsFill henc1
      hhkdf hupd henc_call hnc_call sp cur tape tape' st outSt chunk ek (hroot_len st rfl) h1 st_b hfit
      (Frame := optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗ memRegion (sp + 1320#64) 8 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 3552#64) 504 ∗
        memRegion (sp + 4128#64) 56 ∗ memRegion (sp + 4640#64) 56 ∗ Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28 hx28_0 hvregs (by sep_ac_rfl)
      fun s1 evs hinv1 hevs hjoin1 => ?_
    refine step_send_post_arm_cont_sepWP_placed A lim st_b evs
      (HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk) hevs ext hA
      sp cur tape tape' chain (some ek) hjoin1 trivial hsp_align hinv1 ?_ hnext
    unfold statesSendPreArmScratch
    rw [memRegion_190_928_eq sp, memRegion_4080_104_eq sp, memRegion_4192_504_eq sp]
    exact Entails.of_eq (by sep_ac_rfl)
  | ct1Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.ct1Sampled st) tape =
        EnvCt1sCt1 { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    dsimp only at hnext
    rw [statesSendPreArmScratch_eq_leaf sp 928]
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ct1Sampled_placed_sepWP_ofEnv A lim st_b ext hA hct1s_call
      sp st outSt chunk h1 hfit
      (Frame := statesSendLeafFrame (ctl := ctl) A.repAlloc sp cur tape chain 928 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; sep_ac_rfl) fun s1 evs hevs hinv1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro _
    exact step_send_post_arm_cont_leaf_sepWP_placed A lim st_b evs _ hevs ext hA
      sp cur tape chain 928 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ekReceivedCt1Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.ekReceivedCt1Sampled st) tape =
        EnvEkrCt1 { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    dsimp only at hnext
    rw [statesSendPreArmScratch_eq_leaf sp 528]
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ekReceivedCt1Sampled_placed_sepWP_ofEnv A lim st_b ext hA hekct1s_call
      sp st outSt chunk h1 hfit
      (Frame := statesSendLeafFrame (ctl := ctl) A.repAlloc sp cur tape chain 528 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; sep_ac_rfl) fun s1 evs hevs hinv1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro _
    exact step_send_post_arm_cont_leaf_sepWP_placed A lim st_b evs _ hevs ext hA
      sp cur tape chain 528 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ct1Acknowledged st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.ct1Acknowledged st) tape =
        (fun evs => evs = []) := rfl
    rw [henv_eq] at hnext
    dsimp only at hnext
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ct1Acknowledged_placed A lim st_b ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) A.repAlloc sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; sep_ac_rfl) fun s1 hjoin1 _ => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm_sepWP_placed A lim st_b (fun evs => evs = []) rfl ext hA
      sp cur tape chain hjoin1 trivial hsp_align hinv1 hnext
  | ct2Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    have henv_eq :
        StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp (.ct2Sampled st) tape =
        EnvCt2sCt2 { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } := by
      funext evs; simp only [StatesSendEnvOfEnv, h1]
    rw [henv_eq] at hfit hnext
    dsimp only at hnext
    rw [statesSendPreArmScratch_eq_leaf sp 456]
    apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ct2Sampled_placed_sepWP_ofEnv A lim st_b ext hA hct2s_call
      sp st outSt chunk h1 hfit
      (Frame := statesSendLeafFrame (ctl := ctl) A.repAlloc sp cur tape chain 456 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; sep_ac_rfl) fun s1 evs hevs hinv1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro _
    exact step_send_post_arm_cont_leaf_sepWP_placed A lim st_b evs _ hevs ext hA
      sp cur tape chain 456 (by decide) hjoin1 trivial hsp_align hinv1 hnext

/-- Envelope-parametric `SepWPp` unified 11-arm `<States>::send` + post-arm reassembly
    (`statesSendArmOffset st0 -> +3196`), polymorphic in `panicPost`. -/
theorem step_send_statesSend_placed_ofEnv {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    {EnvHsEk : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
    {EnvCt1rEk : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    {EnvCt1sCt1 : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {EnvEkrCt1 : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {EnvCt2sCt2 : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (hhs_call : HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F EnvHsEk ext)
    (hct1r_call : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F EnvCt1rEk ext)
    (hct1s_call : Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F EnvCt1sCt1 ext)
    (hct2s_call : Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F EnvCt2sCt2 ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F EnvEkrCt1 ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    (hfit : FitsEnv M lim st_b
      (StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp st0 tape))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
      statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A lim st_b
      (StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp st0 tape)
      ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state ret Frame post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3196#64) hinv
  refine step_send_statesSend_sepWP_placed_ofEnv A lim st_b ext hA hZero hcoinsFill
    hseed hpk1 hpk2 henc1 hpk1_slice hpk2_slice hmac_call hres_call henc_call hnc_call
    hhkdf hupd hhs_call hct1r_call hct1s_call hct2s_call hekct1s_call
    sp cur tape tape' chain st0 sOut hroot_len hsend hfit
    hinv hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hx28_0 hvregs hP ?_
  intro sf evs hevs hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx25_f hx26_f hx28_f hx23_none hz_f hvregs_f
  exact SepWP.done hpc_f hrun_f fun _ =>
    hnext sf evs hevs hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx25_f hx26_f hx28_f hx23_none hz_f hvregs_f

/-- Peer-seam default (`StatesSendEnv`) non-panicking `SepWP` unified 11-arm `<States>::send` +
    post-arm reassembly (`statesSendArmOffset st0 -> +3196`). -/
theorem step_send_statesSend_sepWP_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (hhs_call : HeaderSentSendEkChunkPlacedOkX M A lim F ext)
    (hct1r_call : Ct1ReceivedSendEkChunkPlacedOkX M A lim F ext)
    (hct1s_call : Ct1SampledSendCt1ChunkPlacedOkX M A lim F ext)
    (hct2s_call : Ct2SampledSendCt2ChunkPlacedOkX M A lim F ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    (hfit : FitsEnv M lim st_b (StatesSendEnv F K st0 tape))
    {tgt : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
      statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196SepWPPlaced (ctl := ctl) A lim st_b (StatesSendEnv F K st0 tape)
      ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state tgt Frame post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  rw [← statesSendEnvOfEnv_default_eq F K sp st0 tape] at hfit hnext
  exact step_send_statesSend_sepWP_placed_ofEnv A lim st_b ext hA hZero hcoinsFill
    hseed hpk1 hpk2 henc1 hpk1_slice hpk2_slice hmac_call hres_call henc_call hnc_call
    hhkdf hupd hhs_call hct1r_call hct1s_call hct2s_call hekct1s_call
    sp cur tape tape' chain st0 sOut hroot_len hsend hfit
    hinv hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hx28_0 hvregs hP hnext

/-- Peer-seam default (`StatesSendEnv`) `SepWPp` unified 11-arm `<States>::send` + post-arm
    reassembly (`statesSendArmOffset st0 -> +3196`), polymorphic in `panicPost`. -/
theorem step_send_statesSend_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (hhs_call : HeaderSentSendEkChunkPlacedOkX M A lim F ext)
    (hct1r_call : Ct1ReceivedSendEkChunkPlacedOkX M A lim F ext)
    (hct1s_call : Ct1SampledSendCt1ChunkPlacedOkX M A lim F ext)
    (hct2s_call : Ct2SampledSendCt2ChunkPlacedOkX M A lim F ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkPlacedOkX M A lim F ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    (hfit : FitsEnv M lim st_b (StatesSendEnv F K st0 tape))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
      statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A lim st_b (StatesSendEnv F K st0 tape)
      ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state ret Frame post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  rw [← statesSendEnvOfEnv_default_eq F K sp st0 tape] at hfit hnext
  exact step_send_statesSend_placed_ofEnv A lim st_b ext hA hZero hcoinsFill
    hseed hpk1 hpk2 henc1 hpk1_slice hpk2_slice hmac_call hres_call henc_call hnc_call
    hhkdf hupd hhs_call hct1r_call hct1s_call hct2s_call hekct1s_call
    sp cur tape tape' chain st0 sOut hroot_len hsend hfit
    hinv hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hx28_0 hvregs hP hnext

/-- Tight exact-envelope (`StatesSendTightEnv`) non-panicking `SepWP` unified 11-arm
    `<States>::send` + post-arm reassembly (`statesSendArmOffset st0 -> +3196`). -/
theorem step_send_statesSend_tight_sepWP_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (hhs_call : HeaderSentSendEkChunkTightPlacedOkX M A lim F ext)
    (hct1r_call : Ct1ReceivedSendEkChunkTightPlacedOkX M A lim F ext)
    (hct1s_call : Ct1SampledSendCt1ChunkTightPlacedOkX M A lim F ext)
    (hct2s_call : Ct2SampledSendCt2ChunkTightPlacedOkX M A lim F ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    (hfit : FitsEnv M lim st_b (StatesSendTightEnv F K st0 tape))
    {tgt : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
      statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196SepWPPlaced (ctl := ctl) A lim st_b (StatesSendTightEnv F K st0 tape)
      ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state tgt Frame post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  rw [← statesSendEnvOfEnv_tight_eq F K sp st0 tape] at hfit hnext
  exact step_send_statesSend_sepWP_placed_ofEnv A lim st_b ext hA hZero hcoinsFill
    hseed hpk1 hpk2 henc1 hpk1_slice hpk2_slice hmac_call hres_call henc_call hnc_call
    hhkdf hupd hhs_call hct1r_call hct1s_call hct2s_call hekct1s_call
    sp cur tape tape' chain st0 sOut hroot_len hsend hfit
    hinv hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hx28_0 hvregs hP hnext

/-- Tight exact-envelope (`StatesSendTightEnv`) `SepWPp` unified 11-arm `<States>::send` +
    post-arm reassembly (`statesSendArmOffset st0 -> +3196`), polymorphic in `panicPost`. -/
theorem step_send_statesSend_tight_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (hhs_call : HeaderSentSendEkChunkTightPlacedOkX M A lim F ext)
    (hct1r_call : Ct1ReceivedSendEkChunkTightPlacedOkX M A lim F ext)
    (hct1s_call : Ct1SampledSendCt1ChunkTightPlacedOkX M A lim F ext)
    (hct2s_call : Ct2SampledSendCt2ChunkTightPlacedOkX M A lim F ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX M A lim F ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    (hfit : FitsEnv M lim st_b (StatesSendTightEnv F K st0 tape))
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
      statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A lim st_b (StatesSendTightEnv F K st0 tape)
      ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state ret Frame post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  rw [← statesSendEnvOfEnv_tight_eq F K sp st0 tape] at hfit hnext
  exact step_send_statesSend_placed_ofEnv A lim st_b ext hA hZero hcoinsFill
    hseed hpk1 hpk2 henc1 hpk1_slice hpk2_slice hmac_call hres_call henc_call hnc_call
    hhkdf hupd hhs_call hct1r_call hct1s_call hct2s_call hekct1s_call
    sp cur tape tape' chain st0 sOut hroot_len hsend hfit
    hinv hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28 hx28_0 hvregs hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudget
