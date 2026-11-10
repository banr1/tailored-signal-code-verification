/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddresses
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `VmPreserved` and Budget Helpers for `SignalMessage::verify_mac_with_addresses`

Factors out `FitsEnv` decomposition lemmas for `verifyMacWithAddressesEvents`,
`VmPreserved`-strengthened `subtle::black_box::<u8>` contracts, and `VmPreserved` constant-time
MAC/address comparison lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress computeMac)
open CryptoVerification (
  LibsignalPlacement blkLib_eq_62 blkPC_62 blkPl_62 lsBlackBoxU8Sym lsρ
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser okTagVec serializeAddresses serviceIdParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SerializeAddressesGhost VerifyMacWithAddressesGhost
  blackBoxSpec extHookStack
)
open CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses (
  bne_zext32_ite cset_eq_byte cset_eq_byte_alt
  ite_one_zero_and_32 ite_one_zero_and_64 ite_one_zero_and_8
  ite_one_zero_and_one_64 ite_one_zero_and_one_8
  list_length_8_eq mac8_eq_bool memRegion_16_of_two_words
  noneCap_add_one_eq_zero ofNat_cons_cons_bne_one ofNat_cons_sub_one
  okTagVec_add_two_eq_zero okTagVec_add_two_ne_zero
  pack64_byte0 pack64_byte1 pack64_byte2 pack64_byte3
  pack64_byte4 pack64_byte5 pack64_byte6 pack64_byte7
  pointsToBytes_8_bytes pointsToBytes_pack64 pointsToBytes_serialized_split
  setWidth32_and_1095216660735 setWidth32_and_4294967297 setWidth32_ite_one_zero_64
  setWidth8_and32 setWidth8_and64 setWidth8_ite_one_zero_64
  setWidth8_setWidth32 setWidth8_zext64_32 stackAt_split_ge
  verifyMacWithAddresses_fnOff zeroExtend32_ite_one_zero_8 zeroExtend64_ite_one_zero_32
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents VmPreserved
  fitsEvents_append rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWPp_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  blackBoxU8BudgetSpec blackBoxU8_of_blackBox withStack
)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (
  ComputeMacEnv SerializeAddressesEnv VerifyMacWithAddressesEnv
  computeMacEvents fitsEnv_computeMac_iff fitsEnv_serializeAddresses_iff
  fitsEnv_verifyMacWithAddresses_iff serializeAddressesEvents verifyMacWithAddressesEvents
)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs
attribute [local simp, local arm64_norm, local wp_norm]
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

@[local simp, local arm64_norm, local wp_norm]
private theorem pack64_byte1_trunc (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (pack64 m0 m1 m2 m3 m4 m5 m6 m7) >>> 8) = m1 := by
  unfold pack64; bv_bits

@[local simp, local arm64_norm, local wp_norm]
private theorem pack64_byte2_trunc (m0 m1 m2 m3 m4 m5 m6 m7 : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (pack64 m0 m1 m2 m3 m4 m5 m6 m7) >>> 16) = m2 := by
  unfold pack64; bv_bits

/-! ## `FitsEnv` and `stepEvents` lemmas -/

theorem fitsVerifyMac_compute {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {parse : UuidParser} {x : VerifyMacWithAddressesGhost}
    (h : FitsEnv M lim st (VerifyMacWithAddressesEnv F parse x)) :
    FitsEnv M lim st ComputeMacEnv := by
  rw [fitsEnv_verifyMacWithAddresses_iff] at h
  rw [fitsEnv_computeMac_iff]
  unfold verifyMacWithAddressesEvents at h
  dsimp only at h
  split at h
  · exact ((fitsEvents_append M lim _ _ st).mp h).1
  · exact h

theorem fitsVerifyMac_serialize {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {parse : UuidParser} {x : VerifyMacWithAddressesGhost}
    {ad : List (BitVec 8)}
    (h : FitsEnv M lim st (VerifyMacWithAddressesEnv F parse x))
    (hmac : (computeMac F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8)) ==
      x.msg.serialized.drop (x.msg.serialized.length - 8)) = true)
    (haddr : x.msg.addresses = some ad)
    (sg : SerializeAddressesGhost)
    (hsend : sg.sender = x.senderAddr) (hrec : sg.recipient = x.receiverAddr) :
    FitsEnv M lim (M.stepEvents computeMacEvents st) (SerializeAddressesEnv parse sg) := by
  rw [fitsEnv_verifyMacWithAddresses_iff] at h
  rw [fitsEnv_serializeAddresses_iff]
  unfold serializeAddressesEvents
  rw [hsend, hrec]
  cases hexp : serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr with
  | none =>
    simp [FitsEvents]
  | some exp =>
    unfold verifyMacWithAddressesEvents at h
    simp only [hmac, haddr, hexp, Option.isSome_some, Bool.true_and] at h
    have hrest := ((fitsEvents_append M lim computeMacEvents
      (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1) st).mp h).2
    exact ((fitsEvents_append M lim (rustAllocEvents 36 1) (rustDeallocEvents 36 1) _).mp hrest).1

theorem stepEvents_verifyMac_of_mac_false (M : AllocCostModel) (st : M.σ)
    (F : ShaCompress) (parse : UuidParser) (x : VerifyMacWithAddressesGhost)
    (hmac : (computeMac F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8)) ==
      x.msg.serialized.drop (x.msg.serialized.length - 8)) = false) :
    M.stepEvents computeMacEvents st = M.stepEvents (verifyMacWithAddressesEvents F parse x) st := by
  simp [verifyMacWithAddressesEvents, hmac]

theorem stepEvents_verifyMac_of_addrs_none (M : AllocCostModel) (st : M.σ)
    (F : ShaCompress) (parse : UuidParser) (x : VerifyMacWithAddressesGhost)
    (haddr : x.msg.addresses = none) :
    M.stepEvents computeMacEvents st = M.stepEvents (verifyMacWithAddressesEvents F parse x) st := by
  simp [verifyMacWithAddressesEvents, haddr]

theorem stepEvents_verifyMac_of_exp_none (M : AllocCostModel) (st : M.σ)
    (F : ShaCompress) (parse : UuidParser) (x : VerifyMacWithAddressesGhost)
    (sg : SerializeAddressesGhost)
    (hsend : sg.sender = x.senderAddr) (hrec : sg.recipient = x.receiverAddr)
    (hexp : serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr = none) :
    M.stepEvents (serializeAddressesEvents parse sg) (M.stepEvents computeMacEvents st) =
      M.stepEvents (verifyMacWithAddressesEvents F parse x) st := by
  simp [serializeAddressesEvents, verifyMacWithAddressesEvents, hsend, hrec, hexp]

theorem stepEvents_verifyMac_of_exp_some (M : AllocCostModel) (st : M.σ)
    (F : ShaCompress) (parse : UuidParser) (x : VerifyMacWithAddressesGhost)
    {ad exp : List (BitVec 8)}
    (sg : SerializeAddressesGhost)
    (hsend : sg.sender = x.senderAddr) (hrec : sg.recipient = x.receiverAddr)
    (hmac : (computeMac F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8)) ==
      x.msg.serialized.drop (x.msg.serialized.length - 8)) = true)
    (haddr : x.msg.addresses = some ad)
    (hexp : serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr = some exp) :
    M.stepEvents (rustDeallocEvents 36 1)
      (M.stepEvents (serializeAddressesEvents parse sg) (M.stepEvents computeMacEvents st)) =
      M.stepEvents (verifyMacWithAddressesEvents F parse x) st := by
  simp [serializeAddressesEvents, verifyMacWithAddressesEvents, hsend, hrec, hmac, haddr, hexp,
    M.stepEvents_append]

/-! ## `VmPreserved` `subtle::black_box::<u8>` placed contracts -/

def session2BlackBoxBudgetSpecX (sp_cur : BitVec 64) (n : Nat) (b : BitVec 8) : Spec Unit where
  pre := fun _ s =>
    ⌜(s.readReg64 .x0).setWidth 8 = b ∧ s.sp = sp_cur⌝ ∗ stackAt sp_cur n
  post := fun _ s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = b ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      stackAt sp_cur n

theorem blackBox_placed_budget_ok {prog : Program} {addr : BitVec 64}
    (sp_cur : BitVec 64) (n : Nat)
    (hbb_raw : subroutine_ok prog addr (withVmPreserved blackBoxSpec)) (v : BitVec 8) :
    subroutine_ok prog addr (session2BlackBoxBudgetSpecX sp_cur n v) := by
  have h := blackBoxU8_of_blackBox hbb_raw
  refine subroutine_ok_outcome_intro fun _ R s0 hpc hrun hpre hsp => ?_
  simp only [session2BlackBoxBudgetSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hv, _⟩, hmem⟩
  have hpre' : s0.mem ⊨ blackBoxU8BudgetSpec.pre (s0.readReg64 .x0) s0 ∗ (stackAt sp_cur n ∗ R) := by
    simp only [blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec, satisfies_pure_sepConj]
    exact ⟨trivial, hmem⟩
  refine h.mono_outcome (s0.readReg64 .x0) (stackAt sp_cur n ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec, session2BlackBoxBudgetSpecX,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, ⟨hx0, htr⟩, hmem'⟩
    exact ⟨⟨by rw [hx0, hv], htr, hvm⟩, hmem'⟩
  · exact (not_satisfies_false_sepConj (by simpa only [blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec] using hpan)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec] using hex)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec] using hoom)).elim

theorem blackBox_placed_budget_ok_x {prog : Program} {addr : BitVec 64}
    (sp_cur : BitVec 64) (n : Nat)
    (hbb_raw : subroutine_ok prog addr (withStack blackBoxU8BudgetSpec extHookStack))
    (v : BitVec 8) (hn : extHookStack ≤ n := by decide) (hbound : n < 2 ^ 64 := by decide) :
    subroutine_ok prog addr (session2BlackBoxBudgetSpecX sp_cur n v) := by
  have hsplit := stackAt_split_ge sp_cur n extHookStack hn hbound
  refine subroutine_ok_outcome_intro fun _ R s0 hpc hrun hpre hsp => ?_
  simp only [session2BlackBoxBudgetSpecX, hsplit, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hv, hsp_eq⟩, hmem⟩
  have hpre' : s0.mem ⊨ (withStack blackBoxU8BudgetSpec extHookStack).pre (s0.readReg64 .x0) s0 ∗
      (memRegion (sp_cur - BitVec.ofNat 64 n) (n - extHookStack) ∗ R) := by
    simp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxU8BudgetSpec,
      withVmPreserved, CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec, hsp_eq,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, hmem⟩
  refine hbb_raw.mono_outcome (s0.readReg64 .x0)
    (memRegion (sp_cur - BitVec.ofNat 64 n) (n - extHookStack) ∗ R) s0 hpc hrun hpre' hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxU8BudgetSpec,
      withVmPreserved, CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec,
      session2BlackBoxBudgetSpecX, hsp_eq, hsplit, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, ⟨hx0, htr⟩, hmem'⟩
    exact ⟨⟨by rw [hx0, hv], htr, hvm⟩, hmem'⟩
  · exact (not_satisfies_false_sepConj (by simpa only [withStack,
      CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec] using hpan)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [withStack,
      CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec] using hex)).elim
  · exact (not_satisfies_false_sepConj (by simpa only [withStack,
      CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxU8BudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec] using hoom)).elim

/-! ## `VmPreserved` MAC comparison lemmas -/

local macro "wpp_seg62 " H:term:max ppSpace mid:term:max " as " hvm:ident : tactic =>
  `(tactic| (
    apply sepWPp_seg_ls_vm
      (Q := (blkPC_62).rebase (blkPl_62).base (hooksException $H))
      blkLib_eq_62 (mid := $mid)
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real _hnsp => ?_
    have $hvm := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at $hvm ⊢))

set_option maxHeartbeats 1600000 in
theorem ctEqLoop_sepWPp_placed_budget_gen [LibsignalPlacement] (cmStack : Nat)
    (H : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb : ∀ v : BitVec 8, subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (session2BlackBoxBudgetSpecX sp_cur cmStack v))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} :
    ∀ (bs1 bs2 : List (BitVec 8)) (p1 p2 : BitVec 64) (acc : Bool) (Frame : SepProp) (s : State),
      bs1 ≠ [] →
      bs1.length = bs2.length →
      bs1.length < 2 ^ 64 →
      s.pc = (blkPl_62).base + 412#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = sp_cur →
      s.readReg64 .x25 = p1 →
      s.readReg64 .x23 = p2 →
      s.readReg64 .x24 = BitVec.ofNat 64 bs1.length →
      (s.readReg64 .x22).setWidth 8 = (if acc then 1#8 else 0#8) →
      (∀ sf,
        sf.pc = (blkPl_62).base + 444#64 →
        sf.status = .Running →
        sf.spAligned = true →
        sf.trace = s.trace →
        VmPreserved s sf →
        sf.sp = sp_cur →
        sf.readReg64 .x19 = s.readReg64 .x19 →
        sf.readReg64 .x20 = s.readReg64 .x20 →
        sf.readReg64 .x21 = s.readReg64 .x21 →
        sf.readReg64 .x26 = s.readReg64 .x26 →
        sf.readReg64 .x27 = s.readReg64 .x27 →
        sf.readReg64 .x28 = s.readReg64 .x28 →
        sf.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs sf = calleeSavedVRegs s →
        (sf.readReg64 .x22).setWidth 8 = (if (acc && (bs1 == bs2)) then 1#8 else 0#8) →
        SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret sf
          ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur cmStack ∗ Frame) Q Qp) →
      SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret s
        ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ stackAt sp_cur cmStack ∗ Frame) Q Qp := by
  intro bs1
  induction bs1 with
  | nil => intro _ _ _ _ _ _ hne; exact absurd rfl hne
  | cons b1 bs1' ih =>
    intro bs2 p1 p2 acc Frame s _ hlen hlt hpc hrun hsp hsp_eq hx25 hx23 hx24 hx22 hcont
    have hsp_orig := hsp
    simp only [wp_norm, arm64_norm, hsp_eq] at hsp
    cases bs2 with
    | nil => simp at hlen
    | cons b2 bs2' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [pointsToBytes_cons, sepConj_assoc]
      have hbb_step := hbb (if b1 == b2 then 1#8 else 0#8)
      wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s1
      apply SepWPp.of_sepWP (mid := (blkPl_62).base + 432#64)
      wp_call hbb_step ()
      have hvm_1 := hvm_s1.trans hpost; clear hpost
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      cases bs1' with
      | nil =>
        cases bs2' with
        | nil =>
          have hne_1 : (BitVec.ofNat 64 [b1].length != 1#64) = false := rfl
          wpp_seg62 H ((blkPl_62).base + 444#64) as hvm_s2
          have hvm_end := hvm_1.trans hvm_s2
          have hbeq : (([b1] : List (BitVec 8)) == [b2]) = (b1 == b2) := by simp
          refine SepWPp.weaken_pre ?_
            (hcont _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [State.spAligned, arm64_norm, *])
              (by simp only [arm64_norm, *]) hvm_end (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by rw [hbeq, Bool.and_comm acc]; simp only [arm64_norm, *]))
          simp only [pointsToBytes_cons, sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)
        | cons _ _ => simp at hlen
      | cons b1' bs1'' =>
        have hlen' : (b1' :: bs1'').length = bs2'.length := hlen
        have hlt' : (b1' :: bs1'').length < 2 ^ 64 := by simp only [List.length_cons] at hlt ⊢; omega
        have hsub := ofNat_cons_sub_one b1 (b1' :: bs1'') hlt
        have hne_z := ofNat_cons_cons_bne_one b1 b1' bs1'' hlt
        wpp_seg62 H ((blkPl_62).base + 412#64) as hvm_s2
        have hvm_step := hvm_1.trans hvm_s2
        refine SepWPp.weaken_pre ?_
          (ih bs2' (p1 + 1#64) (p2 + 1#64) (acc && (b1 == b2)) (p1 ↦₈ b1 ∗ p2 ↦₈ b2 ∗ Frame) _
            (by simp) hlen' hlt'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [State.spAligned, arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (by rw [Bool.and_comm acc]; simp only [arm64_norm, *])
            fun sf' hpc_f hrun_f hsp_f htr_f hvm_f hsp_eq' hx19_f hx20_f hx21_f hx26_f hx27_f
              hx28_f hx29_f hvregs_f hx22_f => ?_)
        · exact Entails.of_eq (by sep_ac_rfl)
        · have hbeq_cons :
              ((b1 :: b1' :: bs1'') == (b2 :: bs2')) =
                ((b1 == b2) && ((b1' :: bs1'') == bs2')) := rfl
          have hbool_assoc : ((acc && (b1 == b2)) && ((b1' :: bs1'') == bs2')) =
              (acc && ((b1 :: b1' :: bs1'') == (b2 :: bs2'))) := by
            rw [hbeq_cons, Bool.and_assoc]
          rw [hbool_assoc] at hx22_f
          refine SepWPp.weaken_pre ?_
            (hcont sf' hpc_f hrun_f hsp_f
              (by simp only [arm64_norm, *]) (hvm_step.trans hvm_f) hsp_eq'
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hx22_f)
          simp only [pointsToBytes_cons, sepConj_assoc]
          exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1600000 in
theorem macCompare8_sepWPp_placed_budget_gen [LibsignalPlacement] (cmStack : Nat)
    (H : String → Option (State → State))
    (sp_cur : BitVec 64)
    (hbb : ∀ v : BitVec 8, subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (session2BlackBoxBudgetSpecX sp_cur cmStack v))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7 : BitVec 8)
    (serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (len : Nat) (Frame : SepProp) (s : State)
    (hpc : s.pc = (blkPl_62).base + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_cur : s.sp = sp_cur)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (len - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ sf : State,
      sf.pc = (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                   [t0, t1, t2, t3, t4, t5, t6, t7]) then
                 (blkPl_62).base + 344#64
               else
                 (blkPl_62).base + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.sp = sp_cur →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret sf
        (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
         ((s.sp + 8#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
         ((s.sp + 16#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
         ((s.sp + 24#64) ↦₆₄ retA) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
         ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
         stackAt sp_cur cmStack ∗ Frame) Q Qp) :
    SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret s
      (((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
       ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (len - 8) + 7#64) ↦₈ t7) ∗
       stackAt sp_cur cmStack ∗ Frame) Q Qp := by
  have hsp_orig := hsp
  simp only [wp_norm, arm64_norm, hsp_cur] at hsp
  have hbb0 := hbb (if t0 == m0 then 1#8 else 0#8)
  have hbb1 := hbb (if t1 == m1 then 1#8 else 0#8)
  have hbb2 := hbb (if t2 == m2 then 1#8 else 0#8)
  have hbb3 := hbb (if t3 == m3 then 1#8 else 0#8)
  have hbb4 := hbb (if t4 == m4 then 1#8 else 0#8)
  have hbb5 := hbb (if t5 == m5 then 1#8 else 0#8)
  have hbb6 := hbb (if t6 == m6 then 1#8 else 0#8)
  have hbb7 := hbb (if t7 == m7 then 1#8 else 0#8)
  have hbb8 := hbb
    (if (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
         [t0, t1, t2, t3, t4, t5, t6, t7]) then 1#8 else 0#8)
  clear hbb
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s0
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 168#64)
  wp_call hbb0 ()
  have hvm0 := hvm_s0.trans hpost; clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s1
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 188#64)
  wp_call hbb1 ()
  have hvm1 := hvm0.trans (hvm_s1.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s2
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 208#64)
  wp_call hbb2 ()
  have hvm2 := hvm1.trans (hvm_s2.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s3
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 228#64)
  wp_call hbb3 ()
  have hvm3 := hvm2.trans (hvm_s3.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s4
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 252#64)
  wp_call hbb4 ()
  have hvm4 := hvm3.trans (hvm_s4.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s5
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 272#64)
  wp_call hbb5 ()
  have hvm5 := hvm4.trans (hvm_s5.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s6
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 296#64)
  wp_call hbb6 ()
  have hvm6 := hvm5.trans (hvm_s6.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s7
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 324#64)
  wp_call hbb7 ()
  have hvm7 := hvm6.trans (hvm_s7.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  wpp_seg62 H (lsρ lsBlackBoxU8Sym) as hvm_s8
  apply SepWPp.of_sepWP (mid := (blkPl_62).base + 336#64)
  wp_call hbb8 ()
  have hvm8 := hvm7.trans (hvm_s8.trans hpost); clear hpost
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  cases hmac : (([m0, m1, m2, m3, m4, m5, m6, m7] : List (BitVec 8)) ==
                [t0, t1, t2, t3, t4, t5, t6, t7])
  · simp only [hmac, Bool.false_eq_true, ↓reduceIte] at *
    wpp_seg62 H ((blkPl_62).base + 504#64) as hvm_s9
    refine SepWPp.weaken_pre ?_
      (hcont _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *]) (hvm8.trans hvm_s9) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
    rw [hsp_cur]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [hmac, ↓reduceIte] at *
    wpp_seg62 H ((blkPl_62).base + 344#64) as hvm_s9
    refine SepWPp.weaken_pre ?_
      (hcont _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, *])
        (by simp only [arm64_norm, *]) (hvm8.trans hvm_s9) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
    rw [hsp_cur]
    exact Entails.of_eq (by sep_ac_rfl)

theorem macCompare8_full_sepWPp_placed_budget_gen [LibsignalPlacement] (cmStack : Nat)
    (H : String → Option (State → State))
    (hbb : ∀ (sp_cur : BitVec 64) (v : BitVec 8), subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym) (session2BlackBoxBudgetSpecX sp_cur cmStack v))
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    (ourMac bs : List (BitVec 8))
    (sp0 serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 : BitVec 64)
    (Frame : SepProp) (s : State)
    (hour : ourMac.length = 8) (h8 : 8 ≤ bs.length)
    (hpc : s.pc = (blkPl_62).base + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = retA)
    (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = recvA)
    (hx22 : s.readReg64 .x22 = sendA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (bs.length - 8))
    (hx24 : s.readReg64 .x24 = serPtr)
    (hcont : ∀ (sf : State) (v8 v16 : BitVec 64),
      sf.pc = (if (ourMac == bs.drop (bs.length - 8)) then
                 (blkPl_62).base + 344#64
               else
                 (blkPl_62).base + 504#64) →
      sf.status = .Running →
      sf.spAligned = true →
      sf.trace = s.trace →
      VmPreserved s sf →
      sf.sp = sp0 - 288#64 →
      sf.readReg64 .x20 = msgA →
      sf.readReg64 .x21 = recvA →
      sf.readReg64 .x22 = sendA →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret sf
        (memRegion (sp0 - 208#64) 16 ∗
         (serPtr ↦ₛ bs) ∗
         ((sp0 - 280#64) ↦₆₄ v8) ∗
         ((sp0 - 272#64) ↦₆₄ v16) ∗
         ((sp0 - 264#64) ↦₆₄ retA) ∗
         stackAt (sp0 - 288#64) cmStack ∗ Frame) Q Qp) :
    SepWPp ((blkPC_62).rebase (blkPl_62).base H) ret s
      (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦ₛ ourMac) ∗
       (serPtr ↦ₛ bs.take (bs.length - 8)) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) ∗
       ((sp0 - 280#64) ↦₆₄ w_sp8) ∗ ((sp0 - 272#64) ↦₆₄ w_sp16) ∗ ((sp0 - 264#64) ↦₆₄ w_sp24) ∗
       stackAt (sp0 - 288#64) cmStack ∗ Frame) Q Qp := by
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, hour_eq⟩ := list_length_8_eq ourMac hour
  have htheir_len : (bs.drop (bs.length - 8)).length = 8 := by rw [List.length_drop]; omega
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, htheir_eq⟩ := list_length_8_eq _ htheir_len
  have ha80 : sp0 - 208#64 = s.sp + 80#64 := by rw [hsp_eq]; bv_arith
  have ha88 : sp0 - 208#64 + 8#64 = s.sp + 88#64 := by rw [hsp_eq]; bv_arith
  have ha8 : sp0 - 280#64 = s.sp + 8#64 := by rw [hsp_eq]; bv_arith
  have ha16 : sp0 - 272#64 = s.sp + 16#64 := by rw [hsp_eq]; bv_arith
  have ha24 : sp0 - 264#64 = s.sp + 24#64 := by rw [hsp_eq]; bv_arith
  rw [hour_eq, htheir_eq, pointsToBytes_pack64, pointsToBytes_8_bytes, ha88, ha80, ha8, ha16, ha24]
  apply SepWPp.weaken_pre (P' :=
    ((s.sp + 80#64) ↦₆₄ okTagVec) ∗ ((s.sp + 88#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7) ∗
    ((s.sp + 8#64) ↦₆₄ w_sp8) ∗ ((s.sp + 16#64) ↦₆₄ w_sp16) ∗ ((s.sp + 24#64) ↦₆₄ w_sp24) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
    ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7) ∗
    stackAt (sp0 - 288#64) cmStack ∗
    ((serPtr ↦ₛ bs.take (bs.length - 8)) ∗ Frame)) (Entails.of_eq (by sep_ac_rfl))
  refine macCompare8_sepWPp_placed_budget_gen cmStack H (sp0 - 288#64) (hbb (sp0 - 288#64))
    m0 m1 m2 m3 m4 m5 m6 m7 t0 t1 t2 t3 t4 t5 t6 t7
    serPtr msgA recvA sendA retA w_sp8 w_sp16 w_sp24 bs.length
    ((serPtr ↦ₛ bs.take (bs.length - 8)) ∗ Frame) s hpc hrun hsp hsp_eq hx19 hx20 hx21 hx22 hx23 hx24
    fun sf hpc_f hrun_f hsp_f htr_f hvm_f hsp_eq_f hx20_f hx21_f hx22_f hx29_f hvregs_f => ?_
  rw [← ha88, ← ha80, ← ha8, ← ha16, ← ha24]
  have htheir_back :
      ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
      ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7) =
      ((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦ₛ bs.drop (bs.length - 8)) := by
    rw [htheir_eq, pointsToBytes_8_bytes]
  apply SepWPp.weaken_pre (P' :=
    (((sp0 - 208#64) ↦₆₄ okTagVec) ∗ ((sp0 - 208#64 + 8#64) ↦₆₄ pack64 m0 m1 m2 m3 m4 m5 m6 m7)) ∗
    (((serPtr ↦ₛ bs.take (bs.length - 8)) ∗
      (((serPtr + BitVec.ofNat 64 (bs.length - 8)) ↦₈ t0) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 1#64) ↦₈ t1) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 2#64) ↦₈ t2) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 3#64) ↦₈ t3) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 4#64) ↦₈ t4) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 5#64) ↦₈ t5) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 6#64) ↦₈ t6) ∗
       ((serPtr + BitVec.ofNat 64 (bs.length - 8) + 7#64) ↦₈ t7))) ∗
     ((sp0 - 280#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)) ∗
     ((sp0 - 272#64) ↦₆₄ (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)) ∗
     ((sp0 - 264#64) ↦₆₄ retA) ∗
     stackAt (sp0 - 288#64) cmStack ∗ Frame)) (Entails.of_eq (by sep_ac_rfl))
  rw [htheir_back, ← pointsToBytes_serialized_split serPtr bs h8]
  apply SepWPp.weaken_pre
    (sepConj_mono_left (memRegion_16_of_two_words (sp0 - 208#64) okTagVec
      (pack64 m0 m1 m2 m3 m4 m5 m6 m7)))
  rw [← hour_eq, ← htheir_eq] at hpc_f
  exact hcont sf (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 48)
    (pack64 m0 m1 m2 m3 m4 m5 m6 m7 >>> 56)
    hpc_f hrun_f hsp_f htr_f hvm_f hsp_eq_f hx20_f hx21_f hx22_f hx29_f hvregs_f

end LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddressesBudgetAux
