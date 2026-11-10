/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudgetAux
public meta import LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable `<SignalMessage>::verify_mac_with_addresses`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts
(`verifyMacWithAddressesPlacedSpecWithStack`, `verifyMacWithAddressesPlacedSpec`, and
`verifyMacWithAddressesPlacedSpecX`) for `<SignalMessage>::verify_mac_with_addresses`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto computeMac macLength)
open CryptoVerification (
  LibsignalPlacement blkPC_62 blkPl_62 lsBlackBoxU8Sym lsLogFilterAddr lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser noneCap okTagVec optBoxU8At protocolAddressAt
  serializeAddresses serviceIdParse signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (
  ComputeMacGhost SerializeAddressesGhost withLsCodeRoLoaded
  blackBoxSpec computeMacStack computeMacStackX extHookStack
  lsMacRustDeallocSym macLsLogOff mac_ls_hook_ok_of_mem optSerializeAddressesAt
  serializeAddressesStack serializeAddressesStackX verifyMacResultAt
)
open CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses (
  VmaClState VmaCroState VmaInvClass VmaSymState
  bne_zext32_ite boxU8At_expose_nonempty computeMac_length
  cset_eq_byte cset_eq_byte_alt forall_some_eq_imp
  ite_one_zero_and_32 ite_one_zero_and_64 ite_one_zero_and_8
  ite_one_zero_and_one_64 ite_one_zero_and_one_8
  keepVmaClState len_sub_8_bv len_sub_8_eq len_sub_8_ult len_ult_8_false
  list_beq_comm list_beq_false_of_length_ne mac8_eq_bool
  memRegion_16_of_sp_208 memRegion_24_of_16_8 memRegion_24_split_16_8
  memRegion_36_of_pointsToBytes memRegion_9_split noneCap_add_one_eq_zero
  okTagVec_add_two_eq_zero okTagVec_add_two_ne_zero
  optBoxU8At_some_expose optSerializeAddressesAt_none_eq optSerializeAddressesAt_some_eq
  pack64_byte0 pack64_byte1 pack64_byte2 pack64_byte3
  pack64_byte4 pack64_byte5 pack64_byte6 pack64_byte7
  pointsToBytes_serialized_split serializeAddresses_some_length
  setWidth32_and_1095216660735 setWidth32_and_4294967297 setWidth32_ite_one_zero_64
  setWidth8_and32 setWidth8_and64 setWidth8_ite_one_zero_64
  setWidth8_setWidth32 setWidth8_zext64_32 signalMessageAt_expose signalMessageRest
  stackAt_combine_ge stackAt_split_ge stackAt_verifyMacWithAddresses_gen
  subroutine_ok_keepVmaClState verifyMacFrameRest verifyMacWithAddresses_fnOff
  verifyMacWithAddresses_of_addrs_none verifyMacWithAddresses_of_exp_none
  verifyMacWithAddresses_of_exp_some verifyMacWithAddresses_of_mac_false
  withVmaClState zeroExtend32_ite_one_zero_8 zeroExtend64_ite_one_zero_32
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  blackBoxU8BudgetSpec rustDeallocExternSpecWithStack
  rustDeallocExternWithStack_of_rustDealloc withStack
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (
  computeMacEvents computeMacSpec computeMacSpecWithStack computeMacSpecX
  serializeAddressesEvents serializeAddressesSpec serializeAddressesSpecWithStack
  serializeAddressesSpecX verifyMacWithAddressesEvents verifyMacWithAddressesPlacedSpec
  verifyMacWithAddressesPlacedSpecWithStack verifyMacWithAddressesPlacedSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudgetAux (
  blackBox_placed_budget_ok blackBox_placed_budget_ok_x
  ctEqLoop_sepWPp_placed_budget_gen fitsVerifyMac_compute fitsVerifyMac_serialize
  macCompare8_full_sepWPp_placed_budget_gen session2BlackBoxBudgetSpecX
  stepEvents_verifyMac_of_addrs_none stepEvents_verifyMac_of_exp_none
  stepEvents_verifyMac_of_exp_some stepEvents_verifyMac_of_mac_false
)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs
attribute [local simp, local arm64_norm]
  verifyMacWithAddresses_fnOff
  cset_eq_byte cset_eq_byte_alt bne_zext32_ite
  okTagVec_add_two_ne_zero okTagVec_add_two_eq_zero noneCap_add_one_eq_zero
  pack64_byte0 pack64_byte1 pack64_byte2 pack64_byte3
  pack64_byte4 pack64_byte5 pack64_byte6 pack64_byte7
  ite_one_zero_and_64 ite_one_zero_and_32 setWidth32_ite_one_zero_64
  zeroExtend64_ite_one_zero_32 ite_one_zero_and_one_64 setWidth8_ite_one_zero_64
  mac8_eq_bool
  setWidth8_zext64_32 setWidth8_setWidth32 setWidth8_and64 setWidth8_and32
  ite_one_zero_and_8 setWidth32_and_4294967297 setWidth32_and_1095216660735
  ite_one_zero_and_one_8 zeroExtend32_ite_one_zero_8

/-! ## `VmaInv` lift and sequencing helpers -/

private theorem subroutine_ok_withVmaClState_of_lscl [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog addr (withVmaClState (VmaInv := VmaClState) spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeLoaded, VmaClState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

private theorem subroutine_ok_lscl_of_withVmaClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withVmaClState (VmaInv := VmaClState) spec)) :
    subroutine_ok prog addr (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeLoaded, VmaClState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

private theorem subroutine_ok_withVmaClState_of_lscro [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog addr (withVmaClState (VmaInv := VmaCroState) spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeRoLoaded, VmaCroState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

private theorem subroutine_ok_lscro_of_withVmaClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withVmaClState (VmaInv := VmaCroState) spec)) :
    subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeRoLoaded, VmaCroState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

private theorem of_sepWP_vma {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : VmaInv s.mem) (_hsym : VmaSymState s)
    (h : SepWP prog mid s P
      (fun sm Pm => VmaInv sm.mem → VmaSymState sm →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (Φ := VmaInv)
    (fun _ _ => VmaInvClass.of_keepsFrozen) hF
    (SepWP.mono h fun _ _ _ _ hnext hcl => hnext hcl trivial)

private theorem seq_vma {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} (mid : BitVec 64) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : VmaInv s.mem) (_hsym : VmaSymState s)
    (h : SepWP prog mid s P (fun sm Pm =>
      VmaInv sm.mem → VmaSymState sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  SepWP.seq_frozen (Φ := VmaInv)
    (fun _ _ => VmaInvClass.of_keepsFrozen) hF
    (SepWP.mono h fun _ _ _ _ hnext hcl => hnext hcl trivial)

private theorem seq_vma_x30 {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : VmaInv s.mem) (hsym : VmaSymState s)
    (h : SepWP prog (s.readReg64 .x30) s P (fun sm Pm =>
      VmaInv sm.mem → VmaSymState sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  seq_vma (s.readReg64 .x30) hF hsym h

local macro "wp_sync_pool " mid:term : tactic =>
  `(tactic| (
    wp_steps_sync_pool $mid
    try conv => arg 3; simp only [State.setMem_setMem]
    try conv => arg 4; pattern (RustCliAllocBudget.pool _ _ _ _); simp only [State.setMem_setMem]))

local macro "wp_steps_vma_pool " mid:term : tactic =>
  `(tactic| (
    refine seq_vma $mid ‹_› ‹_› ?_
    wp_sync_pool $mid
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hF_step hsym_step))

private theorem sepWPp_done_vma {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.done hpc hrun hq

private theorem sepWPp_bind_vma {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : VmaInv s.mem) (_hsym : VmaSymState s)
    (h : SepWPp prog mid s P
      (fun sm Pm => VmaInv sm.mem → VmaSymState sm → SepWPp prog ret sm Pm Q Qp) Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | hpan | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (VmaInvClass.of_keepsFrozen hF hsteps.keepsFrozen) trivial R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

private theorem macLsLogOff_eq [LibsignalPlacement] :
    macLsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

/-! ## Main relocatable `[LibsignalPlacement]` budget proof -/

private structure VMHooksPlacedBudget [LibsignalPlacement] (VmaInv : Memory → Prop)
    (cmStack saStack daStack : Nat) (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State)) : Prop where
  hdealloc : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
    (lsρ lsMacRustDeallocSym)
    (rustDeallocExternSpecWithStack M A lim daStack)
  hbb_all : ∀ (sp_cur : BitVec 64) (n : Nat), daStack ≤ n → n ≤ cmStack → ∀ (v : BitVec 8),
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym)
      (session2BlackBoxBudgetSpecX sp_cur n v)
  hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
    (lsmpl.base 61)
    (withVmaClState (VmaInv := VmaInv) (serializeAddressesSpecWithStack M A lim parse saStack))
  hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
    (lsmpl.base 60)
    (withVmaClState (VmaInv := VmaInv) (computeMacSpecWithStack M A lim C.F cmStack))

set_option maxHeartbeats 3200000 in
private theorem verifyMacWithAddresses_placed_ok_of_hooks_gen_aux [LibsignalPlacement]
    {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    (cmStack saStack daStack : Nat)
    (hsa_le : saStack ≤ cmStack)
    (hda_le : daStack ≤ cmStack)
    (hcm_lt : cmStack + 288 < 2 ^ 64)
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hk : VMHooksPlacedBudget VmaInv cmStack saStack daStack C M A lim parse H) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withVmaClState (VmaInv := VmaInv)
        (verifyMacWithAddressesPlacedSpecWithStack M A lim C.F parse (cmStack + 288))) := by
  simp only [withVmaClState, verifyMacWithAddressesPlacedSpecWithStack]
  wpp_init x_st s0
  rcases x_st with ⟨x, st⟩
  dsimp only at *
  have hVma0 : VmaInv s0.mem := ‹VmaInv s0.mem›
  have hsym0 : VmaSymState s0 := ‹VmaSymState s0›
  have hfits_all : FitsEnv M lim st _ := ‹FitsEnv M lim st _›
  have hfits_cm := fitsVerifyMac_compute hfits_all
  set st1 := M.stepEvents computeMacEvents st
  have hlay36 : RustLayoutOk 36 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  have _hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  obtain ⟨hdealloc, hbb_all, hser, hCompute⟩ := hk
  have hCompute_keep := subroutine_ok_keepVmaClState hCompute
  clear hCompute
  have hser_keep := subroutine_ok_keepVmaClState hser
  clear hser
  have hbb0 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 0#8
  have hbb1 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 1#8
  have hmac_cmp := @macCompare8_full_sepWPp_placed_budget_gen _ cmStack H
    (fun sp_cur v => hbb_all sp_cur cmStack hda_le (Nat.le_refl _) v)
  have hct_eq := @ctEqLoop_sepWPp_placed_budget_gen _ cmStack H (s0.sp - 288#64)
    (fun v => hbb_all (s0.sp - 288#64) cmStack hda_le (Nat.le_refl _) v)
  clear hbb_all
  have h192_init : s0.sp - 208#64 + 16#64 = s0.sp - 192#64 := by bv_arith
  conv =>
    arg 4
    rw [signalMessageAt_expose, stackAt_verifyMacWithAddresses_gen cmStack (by omega),
      memRegion_24_split_16_8, h192_init, memRegion_9_split]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 =>
    SepWPp.exists_elim fun v_stk_12 => SepWPp.exists_elim fun v_stk_13 =>
    SepWPp.exists_elim fun v_stk_14 => SepWPp.exists_elim fun v_stk_15 =>
    SepWPp.exists_elim fun v_stk_16 => SepWPp.exists_elim fun v_stk_17 =>
    SepWPp.exists_elim fun v_stk_18 =>
    SepWPp.exists_elim fun v_stk_19 => SepWPp.exists_elim fun v_stk_20 =>
    SepWPp.pure_elim fun ⟨h_min, h_max, h_ct_lt, h_pq_lt, h_ad_lt⟩ => ?_
  have hne : x.msg.serialized ≠ [] := by
    intro heq; rw [heq, List.length_nil] at h_min; unfold macLength at h_min; omega
  have hlen_ge9 : 9 ≤ x.msg.serialized.length := by unfold macLength at h_min; omega
  have hlen_ge8 : 8 ≤ x.msg.serialized.length := by omega
  have hsub8 := len_sub_8_eq hlen_ge9 h_max
  have hsub8_bv := len_sub_8_bv hlen_ge9 h_max
  have hult8 := len_ult_8_false hlen_ge9 h_max
  obtain ⟨hult_sub, hult_sub_rev, hule_sub, hneq_sub⟩ := len_sub_8_ult hlen_ge9 h_max
  have h48 : x.msgA + 40#64 + 8#64 = x.msgA + 48#64 := by bv_arith
  rw [boxU8At_expose_nonempty A.repAlloc (x.msgA + 40#64) x.msgG.serPtr x.msg.serialized hne, h48]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hser_ne, hser_lt⟩ => ?_
  conv => enter [4]; rw [pointsToBytes_serialized_split x.msgG.serPtr x.msg.serialized hlen_ge8]
  simp only [sepConj_assoc]
  apply of_sepWP_vma hVma0 hsym0 (mid := lsmpl.base 60)
  wp_sync_pool (lsmpl.base 60)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hF_1 hsym_1
  clear c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 v_stk_16 v_stk_17
  let cg : ComputeMacGhost :=
    { ret := s0.sp - 208#64
      senderA := x.senderIkA
      sender := x.senderIk
      receiverA := x.receiverIkA
      receiver := x.receiverIk
      keyA := x.keyA
      macKey := x.macKey
      msgA := x.msgG.serPtr
      message := x.msg.serialized.take (x.msg.serialized.length - 8) }
  have htake_len : (BitVec.ofNat 64 (x.msg.serialized.length - 8)).toNat =
      (x.msg.serialized.take (x.msg.serialized.length - 8)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), List.length_take]
    omega
  refine SepWPp.call hCompute_keep (x := (cg, st)) (ret_pc := (blkPl_62).base + 100#64)
    (F := (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
      (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
      (x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        List.drop (x.msg.serialized.length - 8) x.msg.serialized ∗
      A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
      optBoxU8At A.repAlloc (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
      signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
      protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
      protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
      x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
      verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗
      (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗ (s0.sp - 280#64) ↦₆₄ v_stk_13 ∗
      (s0.sp - 272#64) ↦₆₄ v_stk_14 ∗ (s0.sp - 264#64) ↦₆₄ v_stk_15 ∗
      (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align ⊢)
    (by simp only [wp_norm, arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro _R' _hmR'
    dsimp only [keepVmaClState, withVmaClState, computeMacSpecWithStack, cg]
    simp only [satisfies_pure_sepConj, sepConj_assoc]
    refine ⟨⟨hF_1, hsym_1⟩, by simp [wp_norm, arm64_norm, *]; omega, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) _hmR'
    conv => rhs; pattern (stackAt _ cmStack); arg 1; simp only [wp_norm, arm64_norm, *]
    sep_ac_rfl
  · intro _ _ _ _ hm
    exact (not_satisfies_false_sepConj (by simpa only [keepVmaClState, withVmaClState,
      computeMacSpecWithStack, sepConj_assoc] using hm)).elim
  · intro _ _ hm
    exact (not_satisfies_false_sepConj (by simpa only [keepVmaClState, withVmaClState,
      computeMacSpecWithStack, sepConj_assoc] using hm)).elim
  · intro sf_1 hpc_1 hrun_1 hsp_1 hcs_1
    simp only [keepVmaClState, withVmaClState, computeMacSpecWithStack, cg, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hF_1', hsym_1'⟩ => ?_
    refine SepWPp.pure_elim fun htr_1 => ?_
    have htr_1' : sf_1.trace = s0.trace := by simp only [wp_norm, arm64_norm, *]
    have hsp_1' : sf_1.sp = s0.sp - 288#64 := by simp only [wp_norm, arm64_norm, *]
    have hsp_align_1 : sf_1.spAligned = true := by
      rw [State.spAligned, hsp_1']
      simp only [wp_norm, arm64_norm, *] at hsp_align ⊢
    obtain ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩ := hcs_1
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 hvregs_1
    conv =>
      arg 4
      pattern (stackAt _ cmStack)
      arg 1
      simp only [wp_norm, arm64_norm, *]
    let ourMac := computeMac C.F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8))
    have hour_len : ourMac.length = 8 := computeMac_length _ _ _ _ _
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 208#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 208#64 + 8#64) ↦ₛ ourMac) ∗
      (x.msgG.serPtr ↦ₛ x.msg.serialized.take (x.msg.serialized.length - 8)) ∗
      ((x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        x.msg.serialized.drop (x.msg.serialized.length - 8)) ∗
      ((s0.sp - 280#64) ↦₆₄ v_stk_13) ∗ ((s0.sp - 272#64) ↦₆₄ v_stk_14) ∗
      ((s0.sp - 264#64) ↦₆₄ v_stk_15) ∗
      stackAt (s0.sp - 288#64) cmStack ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
       x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
       x.keyA ↦ₛ keyToBytes32 x.macKey ∗
       A.pool lim st1 sf_1 ∗
       (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
       (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
       A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
       optBoxU8At A.repAlloc (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
       signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
       protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
       protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
       x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
       verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗
       (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
       (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
       (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
       (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
       (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
       (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
       (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
       (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
       (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
       (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
       (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
       (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
       (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
       (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by sep_ac_rfl))
    refine sepWPp_bind_vma
      (if (ourMac == x.msg.serialized.drop (x.msg.serialized.length - 8)) then
         (blkPl_62).base + 344#64
       else
         (blkPl_62).base + 504#64)
      hF_1' hsym_1' ?_
    refine hmac_cmp ourMac x.msg.serialized s0.sp x.msgG.serPtr x.msgA x.receiverAddrA
      x.senderAddrA x.ret v_stk_13 v_stk_14 v_stk_15 _ sf_1 hour_len hlen_ge8
      hpc_1 hrun_1 hsp_align_1 hsp_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      fun sf_2 v8_2 v16_2 hpc_2 hrun_2 hsp_align_2 htr_2 hvm_2 hsp_2 hx20_2 hx21_2 hx22_2
        hx29_2 hvregs_2 =>
        sepWPp_done_vma hpc_2 hrun_2 fun hF_2 hsym_2 => ?_
    refine ProofLib.SepWPp.transport_budgetPool hvm_2 (hnext := ?_)
    have htr_2' : sf_2.trace = s0.trace := htr_2.trans htr_1'
    have hx29_2' : sf_2.readReg64 .x29 = s0.sp - 96#64 := hx29_2.trans hx29_1
    have hvregs_2' : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := hvregs_2.trans hvregs_1
    clear hCompute_keep hmac_cmp cg hpc_1 hrun_1 hsp_1 hF_1' hsym_1' htr_1 htr_1' hsp_1'
      hsp_align_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 hvregs_1 hF_1 hsym_1 hvm_2
      htr_2 hx29_2 hvregs_2
    cases hmac : (ourMac == x.msg.serialized.drop (x.msg.serialized.length - 8))
    · simp only [hmac, Bool.false_eq_true, ↓reduceIte] at hpc_2
      have hres := verifyMacWithAddresses_of_mac_false C.F x.msg
        (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
        x.senderIk x.receiverIk x.macKey hmac
      have hst_eq : st1 = M.stepEvents (verifyMacWithAddressesEvents C.F parse x) st :=
        stepEvents_verifyMac_of_mac_false M st C.F parse x hmac
      have h_ad_true := eq_true h_ad_lt
      conv => arg 4; rw [hst_eq]
      simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte,
        signalMessageAt_expose, boxU8At_expose_nonempty A.repAlloc _ _ _ hne, h48, h_ad_true,
        stackAt_verifyMacWithAddresses_gen cmStack (by omega),
        memRegion_24_split_16_8, h192_init, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_sync_pool (s0.readReg64 Reg.lr)
      wp_done
    · simp only [hmac, ↓reduceIte] at hpc_2
      cases haddr : x.msg.addresses with
      | none =>
        have hres := verifyMacWithAddresses_of_addrs_none C.F x.msg
          (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey hmac haddr
        have hst_eq : st1 = M.stepEvents (verifyMacWithAddressesEvents C.F parse x) st :=
          stepEvents_verifyMac_of_addrs_none M st C.F parse x haddr
        conv => arg 4; rw [hst_eq]
        simp only [optBoxU8At, verifyMacResultAt, hres, ↓reduceIte,
          signalMessageAt_expose, boxU8At_expose_nonempty A.repAlloc _ _ _ hne, h48,
          stackAt_verifyMacWithAddresses_gen cmStack (by omega),
          memRegion_24_split_16_8, h192_init, sepConj_assoc]
        apply SepWPp.of_sepWP_ret
        wp_sync_pool (s0.readReg64 Reg.lr)
        wp_done
      | some ad =>
        have had_lt40 : ad.length < 1099511627776 := h_ad_lt ad haddr
        rw [optBoxU8At_some_expose A.repAlloc x.msgA x.msgG.addrPtr ad]
        simp only [sepConj_assoc]
        apply SepWPp.weaken_pre (P' :=
          ⌜x.msgG.addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
          ((memRegion (s0.sp - 208#64) 16 ∗ ((s0.sp - 192#64) ↦₆₄ v_stk_18)) ∗
          ((x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
           (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
           (if ad = [] then emp else A.repAlloc.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
           (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
           ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
           ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
           x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
           x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
           x.keyA ↦ₛ keyToBytes32 x.macKey ∗
           A.pool lim st1 sf_2 ∗ stackAt (s0.sp - 288#64) cmStack ∗
           (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
           (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
           A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
           signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
           protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
           protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
           x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
           verifyMacFrameRest s0.sp ∗
           (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
           (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
           (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
           (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
           (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
           (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
           (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
           (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
           (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
           (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
           (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
           (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
           (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
           (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by sep_ac_rfl))
        refine SepWPp.pure_elim fun ⟨haddr_ne, haddr_lt⟩ => ?_
        have haddr_beq : (x.msgG.addrPtr == 0#64) = false := beq_false_of_ne haddr_ne
        apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_24_of_16_8 s0.sp v_stk_18))
        conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)]
        simp only [sepConj_assoc]
        apply of_sepWP_vma hF_2 hsym_2 (mid := lsmpl.base 61)
        wp_sync_pool (lsmpl.base 61)
        apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        intro hF_2' hsym_2'
        let sg : SerializeAddressesGhost :=
          { ret := s0.sp - 208#64
            senderA := x.senderAddrA
            sender := x.senderAddr
            recipientA := x.receiverAddrA
            recipient := x.receiverAddr }
        have hfits_sa : FitsEnv M lim st1 _ :=
          fitsVerifyMac_serialize hfits_all hmac haddr sg rfl rfl
        set st2 := M.stepEvents (serializeAddressesEvents parse sg) st1
        refine SepWPp.call hser_keep (x := (sg, st1)) (ret_pc := (blkPl_62).base + 372#64)
          (F := (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
            (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
            (if ad = [] then emp else A.repAlloc.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
            (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
            ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
            ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
            x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
            x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
            x.keyA ↦ₛ keyToBytes32 x.macKey ∗
            memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack)
              (cmStack - saStack) ∗
            (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
            (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
            A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
            signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
            x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
            verifyMacFrameRest s0.sp ∗
            (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
            (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
            (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
            (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
            (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
            (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
            (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
            (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
            (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
            (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
            (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
            (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
            (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
            (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_2 ⊢)
          (by simp only [wp_norm, arm64_norm, *])
          ?_ ?_ ?_ ?_
        · intro _R' _hmR'
          dsimp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack, sg]
          dsimp only [sg] at hfits_sa
          simp only [satisfies_pure_sepConj, sepConj_assoc]
          refine ⟨⟨hF_2', hsym_2'⟩, by simp [wp_norm, arm64_norm, *], ?_⟩
          refine Satisfies.mono (Entails.of_eq ?_) _hmR'
          conv => rhs; pattern (stackAt _ saStack); arg 1; simp only [wp_norm, arm64_norm, *]
          sep_ac_rfl
        · intro _ _ _ _ hm
          exact (not_satisfies_false_sepConj (by simpa only [keepVmaClState, withVmaClState,
            serializeAddressesSpecWithStack, sepConj_assoc] using hm)).elim
        · intro _ _ hm
          exact (not_satisfies_false_sepConj (by simpa only [keepVmaClState, withVmaClState,
            serializeAddressesSpecWithStack, sepConj_assoc] using hm)).elim
        · intro sf_3 hpc_3 hrun_3 hsp_3 hcs_3
          simp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack, sg,
            sepConj_assoc, wp_norm, arm64_norm, *]
          refine SepWPp.pure_elim fun ⟨⟨hF_3, hsym_3⟩, htr_3⟩ => ?_
          have hsp_3' : sf_3.sp = s0.sp - 288#64 := by
            simp only [wp_norm, arm64_norm, *]
          have hsp_align_3 : sf_3.spAligned = true := by
            rw [State.spAligned, hsp_3']
            simp only [wp_norm, arm64_norm, *] at hsp_align_2 ⊢
          obtain ⟨hx19_3, hx20_3, _, _, hx23_3, _, _, _, _, _, hx29_3, hvregs_3⟩ := hcs_3
          simp only [wp_norm, arm64_norm, *] at hx19_3 hx20_3 hx23_3 hx29_3 hvregs_3
          clear hser_keep
          apply SepWPp.weaken_pre (P' :=
            (stackAt (s0.sp - 288#64) saStack ∗
              memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack)
                (cmStack - saStack)) ∗
            (optSerializeAddressesAt A.repAlloc (s0.sp - 208#64)
              (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr) ∗
             protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
             protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
             A.pool lim st2 sf_3 ∗
             (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
             (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
             (if ad = [] then emp else A.repAlloc.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
             (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
             ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
             ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
             x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
             x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
             x.keyA ↦ₛ keyToBytes32 x.macKey ∗
             (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
             (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
             A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
             signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
             x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
             verifyMacFrameRest s0.sp ∗
             (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
             (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
             (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
             (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
             (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
             (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
             (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
             (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
             (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
             (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
             (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
             (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
             (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
             (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by sep_ac_rfl))
          apply SepWPp.weaken_pre (sepConj_mono_left
            (stackAt_combine_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)))
          rw [← sepConj_assoc, sepConj_comm (stackAt (s0.sp - 288#64) cmStack), sepConj_assoc]
          cases hexp : serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr with
          | none =>
            conv => enter [4]; rw [optSerializeAddressesAt_none_eq A.repAlloc s0.sp]
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun w2_none => SepWPp.exists_elim fun w1_none => ?_
            have hres := verifyMacWithAddresses_of_exp_none C.F x.msg ad
              x.senderIk x.receiverIk x.macKey hmac haddr
            have hst_eq : st2 = M.stepEvents (verifyMacWithAddressesEvents C.F parse x) st :=
              stepEvents_verifyMac_of_exp_none M st C.F parse x sg rfl rfl hexp
            conv => arg 4; rw [hst_eq]
            simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte,
              signalMessageAt_expose, boxU8At_expose_nonempty A.repAlloc _ _ _ hne, h48,
              haddr, forall_some_eq_imp, optBoxU8At_some_expose,
              stackAt_verifyMacWithAddresses_gen cmStack (by omega),
              memRegion_24_split_16_8, h192_init, sepConj_assoc]
            conv => enter [4]; rw [macLsLogOff_eq]
            apply SepWPp.of_sepWP_ret
            wp_sync_pool (s0.readReg64 Reg.lr)
            rw [← macLsLogOff_eq]
            conv => enter [4, 2]; rw [← sepConj_assoc]
            apply SepWP.weaken_pre
              (sepConj_mono_right (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp noneCap w1_none)))
            wp_done
          | some exp =>
            have hexp_len : exp.length = 36 := serializeAddresses_some_length hexp
            have hst_eq :
                M.stepEvents (rustDeallocEvents 36 1) st2 =
                  M.stepEvents (verifyMacWithAddressesEvents C.F parse x) st :=
              stepEvents_verifyMac_of_exp_some M st C.F parse x sg rfl rfl hmac haddr hexp
            conv => enter [4]; rw [optSerializeAddressesAt_some_eq A.repAlloc (s0.sp - 208#64) hexp_len]
            have h200 : s0.sp - 208#64 + 8#64 = s0.sp - 200#64 := by bv_arith
            have h192 : s0.sp - 208#64 + 16#64 = s0.sp - 192#64 := by bv_arith
            conv => enter [4]; rw [h200, h192]
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun expPtr => SepWPp.pure_elim fun hexp_ne => ?_
            by_cases had_len : ad.length = 36
            · have had_ne : ad ≠ [] := by intro h; simp [h] at had_len
              have had_len_bv : BitVec.ofNat 64 ad.length = 36#64 := by rw [had_len]
              conv => enter [4]; simp only [had_ne, had_len_bv, ↓reduceIte, sepConj_assoc]
              apply of_sepWP_vma hF_3 hsym_3 (mid := (blkPl_62).base + 412#64)
              wp_sync_pool ((blkPl_62).base + 412#64)
              apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
              intro hF_3' hsym_3'
              let s_412 := ((blkPC_62).rebase (blkPl_62).base H)
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗ (x.msgG.addrPtr ↦ₛ ad) ∗
                stackAt (s0.sp - 288#64) cmStack ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64) ∗
                 ((s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                 A.live expPtr 36 1 ∗
                 protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
                 A.pool lim st2 _ ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                 (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                 A.repAlloc.live x.msgG.addrPtr ad.length 1 ∗
                 (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                 ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                 ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
                 verifyMacFrameRest s0.sp ∗
                 (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                 (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                 (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                 (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                 (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                 (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                 (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
                (by dsimp only [RustCliAllocBudget.repAlloc]; exact Entails.of_eq (by sep_ac_rfl))
              clear s_412
              have hexp_ne_nil : exp ≠ [] := by intro h; simp [h] at hexp_len
              refine sepWPp_bind_vma ((blkPl_62).base + 444#64) hF_3' hsym_3' ?_
              refine hct_eq exp ad expPtr x.msgG.addrPtr true _ _
                hexp_ne_nil (hexp_len.trans had_len.symm) (by omega)
                (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
                (by simp only [State.spAligned, wp_norm, arm64_norm, *] at hsp_align_3 ⊢)
                (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
                fun sf_4 hpc_4 hrun_4 hsp_align_4 htr_4 hvm_4 hsp_4
                  hx19_4 hx20_4 hx21_4 _ _ _ hx29_4 hvregs_4 hx22_4 =>
                  sepWPp_done_vma hpc_4 hrun_4 fun hF_4 hsym_4 => ?_
              refine ProofLib.SepWPp.transport_budgetPool hvm_4 (hnext := ?_)
              simp only [wp_norm, arm64_norm, *] at htr_4 hsp_4 hx19_4 hx20_4 hx21_4 hx29_4 hvregs_4 hx22_4
              have hres := verifyMacWithAddresses_of_exp_some C.F x.msg ad exp
                x.senderIk x.receiverIk x.macKey hmac haddr
              rw [list_beq_comm ad exp] at hres
              apply SepWPp.weaken_pre (sepConj_mono_right
                (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len)))
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢
                  stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da]
              clear hrem_da
              cases heq_ad : (exp == ad)
              · simp only [heq_ad, Bool.false_eq_true, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, okTagVec, hres, heq_ad, Bool.false_eq_true,
                  ↓reduceIte, signalMessageAt_expose, boxU8At_expose_nonempty A.repAlloc _ _ _ hne,
                  h48, haddr, forall_some_eq_imp, optBoxU8At_some_expose, had_ne, had_len,
                  stackAt_verifyMacWithAddresses_gen cmStack (by omega),
                  memRegion_24_split_16_8, h192_init, sepConj_assoc]
                apply SepWPp.of_sepWP_ret
                wp_steps_vma_pool (lsρ lsBlackBoxU8Sym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hbb0 ()
                sync_call_pool
                apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                  (by simp only [wp_norm, arm64_norm, *])
                intro hF_bb hsym_bb
                conv => enter [4]; rw [macLsLogOff_eq]
                wp_steps_vma_pool (lsρ lsMacRustDeallocSym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1, st2)
                apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                  (by simp only [wp_norm, arm64_norm, *])
                intro hF_da hsym_da
                conv =>
                  arg 4
                  pattern (stackAt _ daStack)
                  arg 1
                  simp only [wp_norm, arm64_norm, *]
                conv => arg 4; rw [hst_eq]
                wp_sync_pool (s0.readReg64 Reg.lr)
                rw [← macLsLogOff_eq]
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool lim (M.stepEvents (verifyMacWithAddressesEvents C.F parse x) st) _ ∗
                    (x.msgG.addrPtr ↦ₛ ad) ∗
                    ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                    (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.repAlloc.live x.msgG.addrPtr 36 1 ∗
                    (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                    ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ macLsLogOff ∗
                    verifyMacFrameRest s0.sp ∗
                    (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                    (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                    (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                    (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                    (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                    (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
                  (Entails.of_eq (by sep_ac_rfl))
                apply SepWP.weaken_pre (sepConj_mono hcomb_da
                  (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
                wp_done
              · simp only [heq_ad, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, okTagVec, hres, heq_ad, ↓reduceIte,
                  signalMessageAt_expose, boxU8At_expose_nonempty A.repAlloc _ _ _ hne,
                  h48, haddr, forall_some_eq_imp, optBoxU8At_some_expose, had_ne, had_len,
                  stackAt_verifyMacWithAddresses_gen cmStack (by omega),
                  memRegion_24_split_16_8, h192_init, sepConj_assoc]
                apply SepWPp.of_sepWP_ret
                wp_steps_vma_pool (lsρ lsBlackBoxU8Sym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hbb1 ()
                sync_call_pool
                apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                  (by simp only [wp_norm, arm64_norm, *])
                intro hF_bb hsym_bb
                wp_steps_vma_pool (lsρ lsMacRustDeallocSym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1, st2)
                apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                  (by simp only [wp_norm, arm64_norm, *])
                intro hF_da hsym_da
                conv =>
                  arg 4
                  pattern (stackAt _ daStack)
                  arg 1
                  simp only [wp_norm, arm64_norm, *]
                conv => arg 4; rw [hst_eq]
                wp_sync_pool (s0.readReg64 Reg.lr)
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool lim (M.stepEvents (verifyMacWithAddressesEvents C.F parse x) st) _ ∗
                    (x.msgG.addrPtr ↦ₛ ad) ∗
                    ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                    (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.repAlloc.live x.msgG.addrPtr 36 1 ∗
                    (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                    ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 1#8 ∗ macLsLogOff ∗
                    verifyMacFrameRest s0.sp ∗
                    (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                    (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                    (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                    (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                    (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                    (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
                  (Entails.of_eq (by sep_ac_rfl))
                apply SepWP.weaken_pre (sepConj_mono hcomb_da
                  (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
                wp_done
            · have had_len_bv : (36#64 == BitVec.ofNat 64 ad.length) = false := by
                cases h : (36#64 == BitVec.ofNat 64 ad.length)
                · rfl
                · exfalso
                  have heq := eq_of_beq h
                  have h1 : (36#64 : BitVec 64).toNat = 36 := rfl
                  have h2 : (BitVec.ofNat 64 ad.length).toNat = ad.length := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have h3 := congrArg BitVec.toNat heq
                  exact had_len (by omega)
              have hres := verifyMacWithAddresses_of_exp_some C.F x.msg ad exp
                x.senderIk x.receiverIk x.macKey hmac haddr
              have hbeq_false : (ad == exp) = false :=
                list_beq_false_of_length_ne (by omega)
              rw [hbeq_false] at hres
              simp only [verifyMacResultAt, okTagVec, hres, Bool.false_eq_true, ↓reduceIte,
                signalMessageAt_expose, boxU8At_expose_nonempty A.repAlloc _ _ _ hne,
                h48, haddr, forall_some_eq_imp, optBoxU8At_some_expose,
                stackAt_verifyMacWithAddresses_gen cmStack (by omega),
                memRegion_24_split_16_8, h192_init, sepConj_assoc]
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢
                  stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da]
              clear hrem_da
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗
                ((s0.sp - 208#64) ↦₆₄ 36#64 ∗
                 (s0.sp - 200#64) ↦₆₄ expPtr ∗
                 (s0.sp - 192#64) ↦₆₄ 36#64 ∗
                 A.live expPtr 36 1 ∗
                 stackAt (s0.sp - 288#64) daStack ∗
                 remDa ∗
                 protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
                 A.pool lim st2 sf_3 ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                 (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                 (if ad = [] then emp else A.repAlloc.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                 x.msgG.serPtr ↦ₛ x.msg.serialized ∗
                 (s0.sp - 280#64) ↦₆₄ v8_2 ∗
                 (s0.sp - 272#64) ↦₆₄ v16_2 ∗
                 (s0.sp - 264#64) ↦₆₄ x.ret ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗
                 (x.ret + 8#64) ↦₈ v_stk_20 ∗
                 macLsLogOff ∗
                 verifyMacFrameRest s0.sp ∗
                 (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗
                 (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                 (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                 (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                 (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                 (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                 (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                 (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
                (by dsimp only [RustCliAllocBudget.repAlloc]; exact Entails.of_eq (by sep_ac_rfl))
              apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len))
              apply SepWPp.of_sepWP_ret
              wp_steps_vma_pool (lsρ lsBlackBoxU8Sym)
              refine seq_vma_x30 ‹_› ‹_› ?_
              wp_call hbb0 ()
              sync_call_pool
              apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
              intro hF_bb hsym_bb
              conv => enter [4]; rw [macLsLogOff_eq]
              wp_steps_vma_pool (lsρ lsMacRustDeallocSym)
              refine seq_vma_x30 ‹_› ‹_› ?_
              wp_call hdealloc (expPtr, 36, 1, st2)
              apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
              intro hF_da hsym_da
              conv =>
                arg 4
                pattern (stackAt _ daStack)
                arg 1
                simp only [wp_norm, arm64_norm, *]
              conv => arg 4; rw [hst_eq]
              wp_sync_pool (s0.readReg64 Reg.lr)
              rw [← macLsLogOff_eq]
              apply SepWP.weaken_pre (P' :=
                (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 (A.pool lim (M.stepEvents (verifyMacWithAddressesEvents C.F parse x) st) _ ∗
                  ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                  protocolAddressAt A.repAlloc x.senderAddr x.senderAddrA ∗
                  protocolAddressAt A.repAlloc x.receiverAddr x.receiverAddrA ∗
                  (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                  (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                  (if ad = [] then emp else A.repAlloc.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                  (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                  ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                  ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                  x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                  x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                  x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                  (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                  (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                  A.repAlloc.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                  signalMessageRest A.repAlloc x.msgG x.msgA x.msg ∗
                  x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ macLsLogOff ∗
                  verifyMacFrameRest s0.sp ∗
                  (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                  (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                  (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                  (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                  (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                  (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                  (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                  (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                  (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                  (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                  (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                  (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                  (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                  (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
                (Entails.of_eq (by sep_ac_rfl))
              apply SepWP.weaken_pre (sepConj_mono hcomb_da
                (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
              wp_done

/-! ## Top-level placed budget contracts -/

theorem verifyMacWithAddresses_placed_ok_of_hooks_gen [LibsignalPlacement]
    (cmStack saStack daStack : Nat)
    (hsa_le : saStack ≤ cmStack)
    (hda_le : daStack ≤ cmStack)
    (hcm_lt : cmStack + 288 < 2 ^ 64)
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hdealloc : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsMacRustDeallocSym)
      (rustDeallocExternSpecWithStack M A lim daStack))
    (hbb_all : ∀ (sp_cur : BitVec 64) (n : Nat), daStack ≤ n → n ≤ cmStack → ∀ (v : BitVec 8),
      subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
        (lsρ lsBlackBoxU8Sym)
        (session2BlackBoxBudgetSpecX sp_cur n v))
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecWithStack M A lim parse saStack)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecWithStack M A lim C.F cmStack))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl
        (verifyMacWithAddressesPlacedSpecWithStack M A lim C.F parse (cmStack + 288))) :=
  subroutine_ok_lscl_of_withVmaClState
    (verifyMacWithAddresses_placed_ok_of_hooks_gen_aux cmStack saStack daStack hsa_le hda_le hcm_lt
      C M A lim parse H ⟨hdealloc, hbb_all, subroutine_ok_withVmaClState_of_lscl hser,
        subroutine_ok_withVmaClState_of_lscl hCompute⟩)

theorem verifyMacWithAddresses_placed_ok_of_compute [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (withVmPreserved blackBoxSpec))
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec M A lim parse)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec M A lim C.F))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F parse)) :=
  verifyMacWithAddresses_placed_ok_of_hooks_gen
    computeMacStack serializeAddressesStack allocHookStack
    (by decide) (by decide) (by decide) C M A lim parse H
    (rustDeallocExternWithStack_of_rustDealloc (stk := allocHookStack) (by decide) (by decide)
      (mac_ls_hook_ok_of_mem (i := 62) hdealloc))
    (fun sp_cur n _ _ v => blackBox_placed_budget_ok sp_cur n hbb_raw v)
    hser
    hCompute

theorem verifyMacWithAddresses_placed_cro_ok_of_compute [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (withVmPreserved blackBoxSpec))
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeRoLoaded lsmpl (serializeAddressesSpec M A lim parse)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeRoLoaded lsmpl (computeMacSpec M A lim C.F))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec M A lim C.F parse)) :=
  subroutine_ok_lscro_of_withVmaClState
    (verifyMacWithAddresses_placed_ok_of_hooks_gen_aux
      computeMacStack serializeAddressesStack allocHookStack
      (by decide) (by decide) (by decide) C M A lim parse H
      ⟨rustDeallocExternWithStack_of_rustDealloc (stk := allocHookStack) (by decide) (by decide)
         (mac_ls_hook_ok_of_mem (i := 62) hdealloc),
       fun sp_cur n _ _ v => blackBox_placed_budget_ok sp_cur n hbb_raw v,
       subroutine_ok_withVmaClState_of_lscro hser,
       subroutine_ok_withVmaClState_of_lscro hCompute⟩)

theorem verifyMacWithAddresses_placed_ok_of_compute_x [LibsignalPlacement]
    (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (H : String → Option (State → State))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym)
      (withStack blackBoxU8BudgetSpec extHookStack))
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX M A lim parse)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecX M A lim C.F))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecX M A lim C.F parse)) :=
  verifyMacWithAddresses_placed_ok_of_hooks_gen
    computeMacStackX serializeAddressesStackX extHookStack
    (by decide) (by decide) (by decide) C M A lim parse H
    (rustDeallocExternWithStack_of_rustDealloc (stk := extHookStack) (by decide) (by decide)
      (mac_ls_hook_ok_of_mem (i := 62) hdealloc))
    (fun sp_cur n hn hncm v =>
      blackBox_placed_budget_ok_x sp_cur n hbb_raw v hn (Nat.lt_of_le_of_lt hncm (by decide)))
    hser
    hCompute

end LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudget
