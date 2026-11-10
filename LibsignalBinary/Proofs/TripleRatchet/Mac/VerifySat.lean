/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Verify -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddresses
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `HookSat`-backed `black_box` Sibling of `Mac.Verify` (`VerifySat`)

Replaces raw `blackBoxSpec` / `withStack blackBoxU8Spec extHookStack` `subroutine_ok` premises in
Block `62` `<SignalMessage>::verify_mac_with_addresses` (`Verify.lean:243, 268, 294`) with
`HookSat H lsBlackBoxU8Sym blackBoxSpecSat`, keeping token-identical conclusions.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.VerifySat

open Arm64 ProofLib
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto computeMac macLength)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_60 blkPC_61 blkPC_62 blkPl_60 blkPl_61
   blkPl_62 extract_withLsCodeLoaded libsignalMutatedBlocks libsignalSessionLib lsBlackBoxU8Sym
   lsLogFilterAddr ls_externAt?_blockProgram_eq_of_externs_eq lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (ComputeMacGhost SerializeAddressesGhost blackBoxSpec blackBoxU8Spec computeMacSpec
   computeMacSpecX computeMacStack computeMacStackX computeMac_placed_cro_ok computeMac_placed_ok
   computeMac_placed_ok_x compress256Spec extHookStack keys_ls_subroutine_ok_of_block_cro
   lsMacCompress256Sym lsMacHandleErrorSym lsMacMemcpySym lsMacMemsetSym lsMacRustAllocSym
   lsMacRustDeallocSym lsMacRustNoAllocShimSym macLsLogOff mac_ls_hook_ok_of_mem newFromSliceSpec
   noAllocShimSpec optSerializeAddressesAt parseSidCodeSpec parseSidCodeStackSpec
   publicKeySerializeSpec publicKeySerializeSpecX rustDeallocExternSpecWithStack
   rustDeallocExternWithStack_of_rustDealloc serializeAddressesSpec serializeAddressesSpecX
   serializeAddressesStack serializeAddressesStackX serialize_addresses_placed_ok
   serialize_addresses_placed_ok_x sessionMemcpyRegionSpec sessionMemsetRegionSpec
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded verifyMacResultAt
   verifyMacWithAddressesPlacedSpec verifyMacWithAddressesPlacedSpecWithStack
   verifyMacWithAddressesPlacedSpecX withLsCodeRoLoaded withStack)
open CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses
  (VmaCroState VmaInvClass VmaSymState bne_zext32_ite boxU8At_expose_nonempty computeMacSpecWithStack
   computeMac_length cset_eq_byte cset_eq_byte_alt ctEqLoop_sepWPp_placed_gen ite_one_zero_and_32
   ite_one_zero_and_64 ite_one_zero_and_8 ite_one_zero_and_one_64 ite_one_zero_and_one_8
   keepVmaClState len_sub_8_bv len_sub_8_eq len_sub_8_ult len_ult_8_false list_beq_comm
   list_beq_false_of_length_ne mac8_eq_bool macCompare8_full_sepWPp_placed_gen
   memRegion_16_of_sp_208 memRegion_24_of_16_8 memRegion_24_split_16_8
   memRegion_36_of_pointsToBytes memRegion_9_split noneCap_add_one_eq_zero
   okTagVec_add_two_eq_zero okTagVec_add_two_ne_zero optBoxU8At_some_expose
   optSerializeAddressesAt_none_eq optSerializeAddressesAt_some_eq pack64_byte0 pack64_byte1
   pack64_byte2 pack64_byte3 pack64_byte4 pack64_byte5 pack64_byte6 pack64_byte7
   pointsToBytes_serialized_split serializeAddressesSpecWithStack serializeAddresses_some_length
   session2BlackBoxSpecX setWidth32_and_1095216660735 setWidth32_and_4294967297
   setWidth32_ite_one_zero_64 setWidth8_and32 setWidth8_and64 setWidth8_ite_one_zero_64
   setWidth8_setWidth32 setWidth8_zext64_32 signalMessageAt_expose signalMessageRest
   stackAt_combine_ge stackAt_split_ge stackAt_verifyMacWithAddresses_gen
   subroutine_ok_keepVmaClState verifyMacFrameRest verifyMacWithAddresses_fnOff
   verifyMacWithAddresses_of_addrs_none verifyMacWithAddresses_of_exp_none
   verifyMacWithAddresses_of_exp_some verifyMacWithAddresses_of_mac_false
   verifyMacWithAddresses_placed_ok_of_compute_x verifyMacWithAddresses_placed_ok_of_hooks_gen
   withVmaClState zeroExtend32_ite_one_zero_8 zeroExtend64_ite_one_zero_32)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser noneCap okTagVec optBoxU8At protocolAddressAt serializeAddresses serviceIdParse
   uuidTryParse)
open CryptoVerification.RustHeap
  (RustAlloc allocFailedIn allocHookStack rustAllocSpec rustDeallocSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpec16 blackBoxSpecSat hookSat_blackBox16_of_sat hookSat_blackBox_withStack_of_sat)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

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

private theorem ls_subroutine_ok_lscl_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

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

local macro "wp_steps_vma " mid:term : tactic =>
  `(tactic| (
    refine seq_vma $mid ‹_› ‹_› ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
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

private structure VMHooksPlaced [LibsignalPlacement] (VmaInv : Memory → Prop)
    (cmStack saStack daStack : Nat) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (H : String → Option (State → State)) : Prop where
  hdealloc : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
    (lsρ lsMacRustDeallocSym) (rustDeallocExternSpecWithStack A daStack)
  hbb_all : ∀ (sp_cur : BitVec 64) (n : Nat), daStack ≤ n → n ≤ cmStack → ∀ (v : BitVec 8),
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (session2BlackBoxSpecX sp_cur n v)
  hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsmpl.base 61)
    (withVmaClState (VmaInv := VmaInv) (serializeAddressesSpecWithStack A parse saStack))
  hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsmpl.base 60)
    (withVmaClState (VmaInv := VmaInv) (computeMacSpecWithStack C.F A cmStack))

private theorem macLsLogOff_eq [LibsignalPlacement] :
    macLsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

set_option maxHeartbeats 1600000 in
private theorem verifyMacWithAddresses_placed_ok_of_hooks_gen_aux [LibsignalPlacement]
    {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    (cmStack saStack daStack : Nat) (hsa_le : saStack ≤ cmStack)
    (hda_le : daStack ≤ cmStack) (hcm_lt : cmStack + 288 < 2 ^ 64)
    (C : Crypto) (A : RustAlloc) (parse : UuidParser) (H : String → Option (State → State))
    (hk : VMHooksPlaced VmaInv cmStack saStack daStack C A parse H) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (blkPl_62).base
      (withVmaClState (VmaInv := VmaInv)
        (verifyMacWithAddressesPlacedSpecWithStack C.F A parse (cmStack + 288))) := by
  simp only [withVmaClState, verifyMacWithAddressesPlacedSpecWithStack, signalMessageAt_expose,
    stackAt_verifyMacWithAddresses_gen cmStack (by omega), memRegion_24_split_16_8, memRegion_9_split,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  obtain ⟨hdealloc, hbb_all, hser, hCompute⟩ := hk
  have hCompute_keep := subroutine_ok_keepVmaClState hCompute
  clear hCompute
  have hser_keep := subroutine_ok_keepVmaClState hser
  clear hser
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbb0 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 0#8
  have hbb1 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 1#8
  have hmac_cmp := @macCompare8_full_sepWPp_placed_gen _ cmStack H
    (fun sp_cur v => hbb_all sp_cur cmStack hda_le (Nat.le_refl _) v)
  have hct_eq := @ctEqLoop_sepWPp_placed_gen _ cmStack H (s0.sp - 288#64)
    (fun v => hbb_all (s0.sp - 288#64) cmStack hda_le (Nat.le_refl _) v)
  clear hbb_all
  have hne : x.msg.serialized ≠ [] := by
    intro heq; rw [heq, List.length_nil] at h_5; unfold macLength at h_5; omega
  have hlen_ge9 : 9 ≤ x.msg.serialized.length := by unfold macLength at h_5; omega
  have hlen_ge8 : 8 ≤ x.msg.serialized.length := by omega
  have hsub8 := len_sub_8_eq hlen_ge9 h_7
  have hsub8_bv := len_sub_8_bv hlen_ge9 h_7
  have hult8 := len_ult_8_false hlen_ge9 h_7
  obtain ⟨hult_sub, hult_sub_rev, hule_sub, hneq_sub⟩ := len_sub_8_ult hlen_ge9 h_7
  have h48 : x.msgA + 40#64 + 8#64 = x.msgA + 48#64 := by bv_arith
  rw [boxU8At_expose_nonempty A (x.msgA + 40#64) x.msgG.serPtr x.msg.serialized hne, h48]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hser_ne, hser_lt⟩ => ?_
  conv => enter [4]; rw [pointsToBytes_serialized_split x.msgG.serPtr x.msg.serialized hlen_ge8]
  simp only [sepConj_assoc]
  apply of_sepWP_vma h_2 h_1 (mid := lsmpl.base 60)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF_1 hsym_1
  let cg : ComputeMacGhost :=
    { ret := s0.sp - 208#64, senderA := x.senderIkA, sender := x.senderIk,
      receiverA := x.receiverIkA, receiver := x.receiverIk, keyA := x.keyA,
      macKey := x.macKey, msgA := x.msgG.serPtr,
      message := x.msg.serialized.take (x.msg.serialized.length - 8) }
  have htake_len : (BitVec.ofNat 64 (x.msg.serialized.length - 8)).toNat =
      (x.msg.serialized.take (x.msg.serialized.length - 8)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), List.length_take]; omega
  have htake_lt : (x.msg.serialized.take (x.msg.serialized.length - 8)).length < 2 ^ 63 := by
    rw [List.length_take]; omega
  refine SepWPp.call hCompute_keep (x := cg) (ret_pc := (blkPl_62).base + 100#64)
    (F := (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
      (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
      (x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        List.drop (x.msg.serialized.length - 8) x.msg.serialized ∗
      A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
      optBoxU8At A (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
      signalMessageRest A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
      verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗
      (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗ (s0.sp - 280#64) ↦₆₄ v_stk_13 ∗
      (s0.sp - 272#64) ↦₆₄ v_stk_14 ∗ (s0.sp - 264#64) ↦₆₄ v_stk_15 ∗
      (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *] at hsp_align ⊢)
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro _R' _hmR'
    simp only [keepVmaClState, withVmaClState, computeMacSpecWithStack, cg, satisfies_pure_sepConj, sepConj_assoc, arm64_norm]
    exact ⟨⟨⟨hF_1, h_1⟩, htake_len, htake_lt⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) _hmR'⟩
  · intro _ _ _ _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [keepVmaClState, withVmaClState, computeMacSpecWithStack] at hm
    rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨ha, htr⟩ => ?_) hm
    unfold allocFailedIn at ha ⊢
    simpa only [arm64_norm, *] using ⟨ha, htr⟩
  · intro sf_1 hpc_1 hrun_1 hsp_1 hcs_1
    simp only [keepVmaClState, withVmaClState, computeMacSpecWithStack, cg, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hF_1', hsym_1'⟩ => ?_
    refine SepWPp.pure_elim fun htr_1 => ?_
    have htr_1' : sf_1.trace = s0.trace := by simpa only [arm64_norm] using htr_1
    have hsp_1' : sf_1.sp = s0.sp - 288#64 := by simpa only [arm64_norm] using hsp_1
    have hsp_align_1 : sf_1.spAligned = true := by
      rw [State.spAligned, hsp_1']; simp only [arm64_norm, *] at hsp_align ⊢
    obtain ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩ := hcs_1
    simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 hvregs_1
    conv => arg 4; pattern (stackAt _ cmStack); arg 1; simp only [wp_norm, arm64_norm, *]
    let ourMac := computeMac C.F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8))
    have hour_len : ourMac.length = 8 := computeMac_length _ _ _ _ _
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 208#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 208#64 + 8#64) ↦ₛ ourMac) ∗
      (x.msgG.serPtr ↦ₛ x.msg.serialized.take (x.msg.serialized.length - 8)) ∗
      ((x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        x.msg.serialized.drop (x.msg.serialized.length - 8)) ∗
      ((s0.sp - 280#64) ↦₆₄ v_stk_13) ∗ ((s0.sp - 272#64) ↦₆₄ v_stk_14) ∗
      ((s0.sp - 264#64) ↦₆₄ v_stk_15) ∗ stackAt (s0.sp - 288#64) cmStack ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
       x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
       x.keyA ↦ₛ keyToBytes32 x.macKey ∗ A.pool ∗
       (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
       (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
       A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
       optBoxU8At A (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
       signalMessageRest A x.msgG x.msgA x.msg ∗
       protocolAddressAt A x.senderAddr x.senderAddrA ∗
       protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
       x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
       verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
       (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
       (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
       (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
       (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
       (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
       (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
       (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Entails.of_eq (by sep_ac_rfl))
    refine sepWPp_bind_vma
      (if (ourMac == x.msg.serialized.drop (x.msg.serialized.length - 8)) then
         (blkPl_62).base + 344#64 else (blkPl_62).base + 504#64) hF_1' hsym_1' ?_
    refine hmac_cmp ourMac x.msg.serialized s0.sp x.msgG.serPtr x.msgA x.receiverAddrA
      x.senderAddrA x.ret v_stk_13 v_stk_14 v_stk_15 _ sf_1 hour_len hlen_ge8
      hpc_1 hrun_1 hsp_align_1 hsp_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      fun sf_2 v8_2 v16_2 hpc_2 hrun_2 hsp_align_2 htr_2 hsp_2 hx20_2 hx21_2 hx22_2 hx29_2 hvregs_2 =>
        sepWPp_done_vma hpc_2 hrun_2 fun hF_2 hsym_2 => ?_
    have htr_2' : sf_2.trace = s0.trace := htr_2.trans htr_1'
    have hx29_2' : sf_2.readReg64 .x29 = s0.sp - 96#64 := hx29_2.trans hx29_1
    have hvregs_2' : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := hvregs_2.trans hvregs_1
    cases hmac : (ourMac == x.msg.serialized.drop (x.msg.serialized.length - 8))
    · simp only [hmac, Bool.false_eq_true, ↓reduceIte] at hpc_2
      have hres := verifyMacWithAddresses_of_mac_false C.F x.msg
        (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
        x.senderIk x.receiverIk x.macKey hmac
      simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply SepWPp.of_sepWP_ret; wp_steps; wp_done
    · simp only [hmac, ↓reduceIte] at hpc_2
      cases haddr : x.msg.addresses with
      | none =>
        have hres := verifyMacWithAddresses_of_addrs_none C.F x.msg
          (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey hmac haddr
        simp only [optBoxU8At, verifyMacResultAt, hres, ↓reduceIte, sepConj_assoc]
        apply SepWPp.of_sepWP_ret; wp_steps; wp_done
      | some ad =>
        have had_lt40 : ad.length < 1099511627776 := h ad haddr
        rw [optBoxU8At_some_expose A x.msgA x.msgG.addrPtr ad]
        simp only [sepConj_assoc]
        apply SepWPp.weaken_pre (P' :=
          ⌜x.msgG.addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
          ((memRegion (s0.sp - 208#64) 16 ∗ ((s0.sp - 192#64) ↦₆₄ v_stk_18)) ∗
          ((x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
           (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
           (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
           (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
           ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗ ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
           x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
           x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
           x.keyA ↦ₛ keyToBytes32 x.macKey ∗ A.pool ∗ stackAt (s0.sp - 288#64) cmStack ∗
           (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
           (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
           A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
           signalMessageRest A x.msgG x.msgA x.msg ∗
           protocolAddressAt A x.senderAddr x.senderAddrA ∗
           protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
           x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
           verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
           (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
           (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
           (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
           (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
           (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
           (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
           (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
          (Entails.of_eq (by sep_ac_rfl))
        refine SepWPp.pure_elim fun ⟨haddr_ne, haddr_lt⟩ => ?_
        have had_all : ∀ (ad_1 : List (BitVec 8)), some ad = some ad_1 → ad_1.length < 1099511627776 := by
          rintro _ ⟨⟩; exact had_lt40
        have haddr_beq : (x.msgG.addrPtr == 0#64) = false := beq_false_of_ne haddr_ne
        apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_24_of_16_8 s0.sp v_stk_18))
        conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)]
        simp only [sepConj_assoc]
        apply of_sepWP_vma hF_2 hsym_2 (mid := lsmpl.base 61)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hF_2' hsym_2'
        let sg : SerializeAddressesGhost :=
          { ret := s0.sp - 208#64, senderA := x.senderAddrA, sender := x.senderAddr,
            recipientA := x.receiverAddrA, recipient := x.receiverAddr }
        refine SepWPp.call hser_keep (x := sg) (ret_pc := (blkPl_62).base + 372#64)
          (F := (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
            (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
            (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
            (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
            ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗ ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
            x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
            x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
            x.keyA ↦ₛ keyToBytes32 x.macKey ∗
            memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - saStack) ∗
            (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
            (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
            A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
            signalMessageRest A x.msgG x.msgA x.msg ∗
            x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
            verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
            (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
            (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
            (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
            (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
            (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
            (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
            (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, *] at hsp_align_2 ⊢)
          (by simp only [arm64_norm, *])
          ?_ ?_ ?_ ?_
        · intro _R' _hmR'
          simp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack, sg, sepConj_assoc, arm64_norm, *]
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) _hmR'
        · intro _ _ _ _ hm; exact allowPanic_not_exited hm
        · intro sf _ hm
          dsimp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack] at hm
          rw [← sepConj_assoc]
          refine allowPanic_frame (fun ⟨ha, htr⟩ => ?_) hm
          unfold allocFailedIn at ha ⊢
          simp only [arm64_norm, *] at ha htr ⊢
          exact ⟨ha, htr⟩
        · intro sf_3 hpc_3 hrun_3 hsp_3 hcs_3
          simp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack, sg, sepConj_assoc, arm64_norm, *]
          refine SepWPp.pure_elim fun ⟨⟨hF_3, hsym_3⟩, htr_3⟩ => ?_
          have hsp_3' : sf_3.sp = s0.sp - 288#64 := by simp only [arm64_norm, *] at hsp_3; exact hsp_3
          have hsp_align_3 : sf_3.spAligned = true := by
            rw [State.spAligned, hsp_3']; simp only [arm64_norm, *] at hsp_align_2 ⊢
          obtain ⟨hx19_3, hx20_3, _, _, hx23_3, _, _, _, _, _, hx29_3, hvregs_3⟩ := hcs_3
          simp only [arm64_norm, *] at hx19_3 hx20_3 hx23_3 hx29_3 hvregs_3
          apply SepWPp.weaken_pre (P' :=
            (stackAt (s0.sp - 288#64) saStack ∗
              memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - saStack)) ∗
            (optSerializeAddressesAt A (s0.sp - 208#64)
              (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr) ∗
             protocolAddressAt A x.senderAddr x.senderAddrA ∗
             protocolAddressAt A x.receiverAddr x.receiverAddrA ∗ A.pool ∗
             (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
             (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
             (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
             (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
             ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗ ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
             x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
             x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
             x.keyA ↦ₛ keyToBytes32 x.macKey ∗
             (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
             (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
             A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
             signalMessageRest A x.msgG x.msgA x.msg ∗
             x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
             verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
             (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
             (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
             (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
             (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
             (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
             (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
             (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
            (Entails.of_eq (by sep_ac_rfl))
          apply SepWPp.weaken_pre (sepConj_mono_left (stackAt_combine_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)))
          rw [← sepConj_assoc, sepConj_comm (stackAt (s0.sp - 288#64) cmStack), sepConj_assoc]
          cases hexp : serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr with
          | none =>
            conv => enter [4]; rw [optSerializeAddressesAt_none_eq A s0.sp]
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun w2_none => SepWPp.exists_elim fun w1_none => ?_
            have hres := verifyMacWithAddresses_of_exp_none C.F x.msg ad
              x.senderIk x.receiverIk x.macKey hmac haddr
            simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
            conv => enter [4]; rw [macLsLogOff_eq]
            apply SepWPp.of_sepWP_ret; wp_steps
            rw [← macLsLogOff_eq, ← sepConj_assoc]
            apply SepWP.weaken_pre (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp noneCap w1_none))
            wp_done
          | some exp =>
            have hexp_len : exp.length = 36 := serializeAddresses_some_length hexp
            conv => enter [4]; rw [optSerializeAddressesAt_some_eq A (s0.sp - 208#64) hexp_len]
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
              wp_steps
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_3' hsym_3'
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗ (x.msgG.addrPtr ↦ₛ ad) ∗ stackAt (s0.sp - 288#64) cmStack ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64) ∗ ((s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 ((s0.sp - 192#64) ↦₆₄ 36#64) ∗ A.live expPtr 36 1 ∗
                 protocolAddressAt A x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A x.receiverAddr x.receiverAddrA ∗ A.pool ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗ (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                 A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                 ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗ ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
                 verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
                (Entails.of_eq (by sep_ac_rfl))
              have hexp_ne_nil : exp ≠ [] := by intro h; simp [h] at hexp_len
              refine sepWPp_bind_vma ((blkPl_62).base + 444#64) hF_3' hsym_3' ?_
              refine hct_eq exp ad expPtr x.msgG.addrPtr true _ _
                hexp_ne_nil (hexp_len.trans had_len.symm) (by omega)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [State.spAligned, arm64_norm, *] at hsp_align_3 ⊢)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                fun sf_4 hpc_4 hrun_4 hsp_align_4 htr_4 hsp_4
                  hx19_4 hx20_4 hx21_4 _ _ _ hx29_4 hvregs_4 hx22_4 =>
                  sepWPp_done_vma hpc_4 hrun_4 fun hF_4 hsym_4 => ?_
              simp only [arm64_norm, *] at htr_4 hsp_4 hx19_4 hx20_4 hx21_4 hx29_4 hvregs_4 hx22_4
              have hres := verifyMacWithAddresses_of_exp_some C.F x.msg ad exp
                x.senderIk x.receiverIk x.macKey hmac haddr
              rw [list_beq_comm ad exp] at hres
              apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len))
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢ stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da]
              clear hrem_da
              cases heq_ad : (exp == ad)
              · simp only [heq_ad, Bool.false_eq_true, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, hres, heq_ad, had_ne, had_len_bv, Bool.false_eq_true,
                  ↓reduceIte, sepConj_assoc]
                apply SepWPp.of_sepWP_ret
                wp_steps_vma (lsρ lsBlackBoxU8Sym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hbb0 ()
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_bb hsym_bb
                conv => enter [4]; rw [macLsLogOff_eq]
                wp_steps_vma (lsρ lsMacRustDeallocSym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1)
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_da hsym_da
                wp_steps
                rw [← macLsLogOff_eq]
                conv => enter [4]; simp only [arm64_norm, *]
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool ∗ (x.msgG.addrPtr ↦ₛ ad) ∗ ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗ (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.live x.msgG.addrPtr 36 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗ ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ macLsLogOff ∗
                    verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
                  (Entails.of_eq (by sep_ac_rfl))
                apply SepWP.weaken_pre (sepConj_mono hcomb_da
                  (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
                wp_done
              · simp only [heq_ad, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, hres, heq_ad, had_ne, had_len_bv, ↓reduceIte, sepConj_assoc]
                apply SepWPp.of_sepWP_ret
                wp_steps_vma (lsρ lsBlackBoxU8Sym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hbb1 ()
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_bb hsym_bb
                wp_steps_vma (lsρ lsMacRustDeallocSym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1)
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_da hsym_da
                wp_steps
                conv => enter [4]; simp only [arm64_norm, *]
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool ∗ (x.msgG.addrPtr ↦ₛ ad) ∗ ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗ (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.live x.msgG.addrPtr 36 1 ∗ (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗ ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 1#8 ∗ macLsLogOff ∗
                    verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
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
              have hbeq_false : (ad == exp) = false := list_beq_false_of_length_ne (by omega)
              rw [hbeq_false] at hres
              simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢ stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da]
              clear hrem_da
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗
                ((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr ∗
                 (s0.sp - 192#64) ↦₆₄ 36#64 ∗ A.live expPtr 36 1 ∗
                 stackAt (s0.sp - 288#64) daStack ∗ remDa ∗
                 protocolAddressAt A x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A x.receiverAddr x.receiverAddrA ∗ A.pool ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                 (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                 (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                 x.msgG.serPtr ↦ₛ x.msg.serialized ∗
                 (s0.sp - 280#64) ↦₆₄ v8_2 ∗ (s0.sp - 272#64) ↦₆₄ v16_2 ∗ (s0.sp - 264#64) ↦₆₄ x.ret ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
                 verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
                (Entails.of_eq (by sep_ac_rfl))
              apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len))
              apply SepWPp.of_sepWP_ret
              wp_steps_vma (lsρ lsBlackBoxU8Sym)
              refine seq_vma_x30 ‹_› ‹_› ?_
              wp_call hbb0 ()
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_bb hsym_bb
              conv => enter [4]; rw [macLsLogOff_eq]
              wp_steps_vma (lsρ lsMacRustDeallocSym)
              refine seq_vma_x30 ‹_› ‹_› ?_
              wp_call hdealloc (expPtr, 36, 1)
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_da hsym_da
              wp_steps
              rw [← macLsLogOff_eq]
              conv => enter [4]; simp only [arm64_norm, *]
              apply SepWP.weaken_pre (P' :=
                (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 (A.pool ∗ ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                  protocolAddressAt A x.senderAddr x.senderAddrA ∗
                  protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                  (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                  (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                  (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                  (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                  ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗ ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                  x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                  x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                  x.keyA ↦ₛ keyToBytes32 x.macKey ∗
                  (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                  (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                  A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                  signalMessageRest A x.msgG x.msgA x.msg ∗
                  x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ macLsLogOff ∗
                  verifyMacFrameRest s0.sp ∗ (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                  (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                  (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                  (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗ (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                  (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗ (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                  (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗ (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                  (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗ (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                  (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗ (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
                (Entails.of_eq (by sep_ac_rfl))
              apply SepWP.weaken_pre (sepConj_mono hcomb_da
                (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
              wp_done

private theorem blackBox_placed_ok_16_sat {prog : Program} {addr : BitVec 64}
    (sp_cur : BitVec 64) (n : Nat) (hbb16 : subroutine_ok prog addr blackBoxSpec16)
    (v : BitVec 8) (hn : 16 ≤ n) (hbound : n < 2 ^ 64) :
    subroutine_ok prog addr (session2BlackBoxSpecX sp_cur n v) := by
  have hsplit := stackAt_split_ge sp_cur n 16 hn hbound
  refine subroutine_ok_outcome_intro fun _ R s0 hpc hrun hpre hsp => ?_
  simp only [session2BlackBoxSpecX, hsplit, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hv, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ blackBoxSpec16.pre (s0.readReg64 .x0) s0 ∗
      (memRegion (sp_cur - BitVec.ofNat 64 n) (n - 16) ∗ R) := by
    simp only [blackBoxSpec16, withStack, blackBoxSpec, hsp_eq, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, hmem⟩
  refine hbb16.mono_outcome (s0.readReg64 .x0)
    (memRegion (sp_cur - BitVec.ofNat 64 n) (n - 16) ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [blackBoxSpec16, withStack, blackBoxSpec, session2BlackBoxSpecX, hsp_eq, hsplit,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hmem'⟩
    have hx0_8 : (sf.readReg64 .x0).setWidth 8 = v := by
      rw [hx0, hv]; bv_bits
    exact ⟨⟨hx0_8, htr⟩, hmem'⟩
  · dsimp only [blackBoxSpec16, withStack, blackBoxSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [blackBoxSpec16, withStack, blackBoxSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [blackBoxSpec16, withStack, blackBoxSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

private theorem hookSat_blackBoxU8_ext_of_sat {H : String → Option (State → State)} {sym : String}
    (h_bb : HookSat H sym blackBoxSpecSat) :
    HookSat H sym (withStack blackBoxU8Spec extHookStack) := by
  refine HookSat.mono (hookSat_blackBox_withStack_of_sat h_bb (n := extHookStack)) ?_
  intro x R s0 hpre
  dsimp only [withStack, blackBoxU8Spec, blackBoxSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine ⟨x, R, ?_, fun sf hpost => ?_⟩
  · simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact hpre
  · simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hmem⟩
    refine ⟨⟨?_, htr⟩, hmem⟩
    rw [hx0]
    bv_bits

/-- `HookSat` `black_box` sibling of `verifyMacWithAddresses_placed_ok` (`Verify.lean:243`). -/
theorem verifyMacWithAddresses_placed_ok_sat [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  let hbb16 := mac_ls_hook_ok_of_mem (prog := (blkPC_62).rebase (blkPl_62).base H)
    (hookSat_blackBox16_of_sat h_bb)
  verifyMacWithAddresses_placed_ok_of_hooks_gen
    computeMacStack serializeAddressesStack allocHookStack
    (by decide) (by decide) (by decide) C A parse H
    (rustDeallocExternWithStack_of_rustDealloc
      (mac_ls_hook_ok_of_mem (prog := (blkPC_62).rebase (blkPl_62).base H) hdealloc)
      (by decide) (by decide))
    (fun sp_cur n hn hncm v =>
      blackBox_placed_ok_16_sat sp_cur n hbb16 v
        (Nat.le_trans (by decide : 16 ≤ allocHookStack) hn)
        (Nat.lt_of_le_of_lt hncm (by decide)))
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc hpanic))
    (ls_subroutine_ok_lscl_of_block (computeMac_placed_ok C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

/-- `HookSat` `black_box` sibling of `verifyMacWithAddresses_placed_ok_x` (`Verify.lean:268`). -/
theorem verifyMacWithAddresses_placed_ok_x_sat [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec extHookStack)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX A)))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecX C.F A uuidTryParse)) :=
  verifyMacWithAddresses_placed_ok_of_compute_x C A uuidTryParse H
    hdealloc
    (mac_ls_hook_ok_of_mem (prog := (blkPC_62).rebase (blkPl_62).base H)
      (hookSat_blackBoxU8_ext_of_sat h_bb))
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok_x hparse hshim halloc hpanic))
    (ls_subroutine_ok_lscl_of_block (computeMac_placed_ok_x C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

/-- `HookSat` `black_box` sibling of `verifyMacWithAddresses_placed_cro_ok` (`Verify.lean:294`). -/
theorem verifyMacWithAddresses_placed_cro_ok_sat [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpec A)))
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  let hbb16 := mac_ls_hook_ok_of_mem (prog := (blkPC_62).rebase (blkPl_62).base H)
    (hookSat_blackBox16_of_sat h_bb)
  subroutine_ok_lscro_of_withVmaClState
    (verifyMacWithAddresses_placed_ok_of_hooks_gen_aux
      computeMacStack serializeAddressesStack allocHookStack
      (by decide) (by decide) (by decide) C A parse H
      ⟨rustDeallocExternWithStack_of_rustDealloc
         (mac_ls_hook_ok_of_mem (prog := (blkPC_62).rebase (blkPl_62).base H) hdealloc)
         (by decide) (by decide),
       fun sp_cur n hn hncm v =>
         blackBox_placed_ok_16_sat sp_cur n hbb16 v
           (Nat.le_trans (by decide : 16 ≤ allocHookStack) hn)
           (Nat.lt_of_le_of_lt hncm (by decide)),
       subroutine_ok_withVmaClState_of_lscro
         (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
           (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc hpanic))),
       subroutine_ok_withVmaClState_of_lscro
         (keys_ls_subroutine_ok_of_block_cro
           (computeMac_placed_cro_ok C A H hnew hpk hmemcpy hcompress hdealloc hmemset))⟩)

end LibsignalBinary.Proofs.TripleRatchet.Mac.VerifySat
