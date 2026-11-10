/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadTrustTailsXExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1LoadExtPlaced
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1TrustExtPlaced

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local simp, local wp_norm, local arm64_norm] bfi_mask_lsr8_id evalBitfield_bfi_lsr8
attribute [local simp] extractLsb_hi_lo_append

set_option maxHeartbeats 400000 in
theorem p1_err_drop_none_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x359c#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem p1_err_drop_ss_to_call_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ssCap : BitVec 64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0xf8#64) ↦₆₄ ssCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1_std3 hcap_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

abbrev lsStringCloneSym : String :=
  "_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"

set_option maxHeartbeats 800000 in
theorem p1_untrusted_to_clone_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x6e4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 623) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = remoteAddrPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = remoteAddrPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x7e8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 0#64 := hx23
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1600000 in
theorem p1_untrusted_post_clone_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr remoteAddrPtr outPtr cap ptr len devWord
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8
    u_370 u_378 u_380 u_388 : BitVec 64)
    (u_390 : BitVec 32)
    (d0 b_390 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hpc : s.pc = stageP1EntryPlaced + 0x7e8#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = remoteAddrPtr)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x3588#64) s
      (((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       FromRecordCallees.lsLogOff ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
       ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
       ((s.sp + 0x3f8#64) ↦₈ d0) ∗
       ((s.sp + 0x3f9#64) ↦ₛ pad) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          FromRecordCallees.lsLogOff ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₃₂ len.extractLsb' 0 32) ∗
          ((s.sp + 0x3f4#64) ↦₃₂ len.extractLsb' 32 32) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ devWord) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0x800000000000000c#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ cap) ∗
          ((coroPtr + 0x260#64) ↦₆₄ ptr) ∗
          ((coroPtr + 0x268#64) ↦₆₄ len) ∗
          ((coroPtr + 0x270#64) ↦₆₄ devWord) ∗
          ((coroPtr + 0x278#64) ↦₆₄ s.readReg64 .x27) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x800000000000000c#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32) ∗
          ((s.sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0x378#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0x388#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
          ((s.sp + 0x390#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = 0x800000000000000c#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdev_pack := SegUntrusted.pointsTo64_of_cons_unpack64 (s.sp + 0x3f8#64) peer.device pad devWord hw4
  try simp only [BitVec.add_assoc] at hdev_pack; try simp only [BitVec.reduceAdd] at hdev_pack
  have hrealign_a98 := realign_40 (s.sp + 0xa98#64) cap ptr len devWord (s.readReg64 .x27)
  try simp only [BitVec.add_assoc] at hrealign_a98; try simp only [BitVec.reduceAdd] at hrealign_a98
  have hcond_err : ConditionHolds CondCode.NE (addsPState64 0x800000000000000c#64 2#64) = true :=
    cond_ne_adds64_of_ne_neg2_std3 (by decide)
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = remoteAddrPtr := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, FromRecordCallees.lsLogOff, lsLogFilterAddr] at hpc ⊢
  apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr u_268)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq hdev_pack) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr len).symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq hrealign_a98) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p3_err_tail_b_vregs_wp_ext_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (stageP1ProgPlaced ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p1_err_tail_prev_dealloc_core_wp_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64) (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (stageP1ProgPlaced ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
       memRegion prevPtr (prevCap.toNat * 24) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗ ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗ ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗ ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  have hmul1 : 24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  have hmul2 : prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hdealloc hpc ⊢
  wp_steps
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]; ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩


theorem call_raw_nopanic_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrl' : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

theorem call_lscro_nopanic_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hpre_eq : (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s = (⌜φ ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ T) := by
    dsimp only [StoreKit.withLsCodeRoLoaded]
    rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure]
  exact call_raw_nopanic_steps_frame_placed (spec := StoreKit.withLsCodeRoLoaded lsmpl spec) (x := x)
    (φ := φ ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (T := T) (F := F)
    hcrl hcall hpc hrun hsp hlr hpre_eq ⟨hφ, hcrl⟩ hP hpan_false hexit_false hnext hoom_false

theorem call_raw_oom_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrl' : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      allowPanic_oom_of_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem call_lscro_oom_steps_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm0 : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Satisfies.mono (sepConj_mono_left hpre) hm
  have hm' : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hm0⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrl' : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm hcrl' R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      allowPanic_oom_of_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim


set_option maxHeartbeats 1200000 in
theorem p1_err_drop_record_core_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Qp : State → SepProp → Prop}
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s : State) (coroPtr : BitVec 64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (stageP1ProgPlaced ext)
      (stageP1EntryPlaced + 0x359c#64) s
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       A.pool ∗
       stackAt s.sp dropSessionStructureLocal2Stack)
      (fun s2 P_m =>
        (P_m ⊢
          ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
            ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗
            ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            (if prevCap = 0 then emp
             else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
            memRegion (coroPtr + 0xf8#64) 344 ∗
            A.pool ∗
            stackAt s.sp dropSessionStructureLocal2Stack) ∧
        s2.sp = s.sp ∧
        s2.trace = s.trace ∧
        s2.readReg64 .x19 = coroPtr ∧
        s2.readReg64 .x22 = s.readReg64 .x22 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        s2.readReg64 .x28 = s.readReg64 .x28 ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  cases opt with
  | none =>
    dsimp only [p1LoadedRecordAt, sessionRecordEmptyHeaderAt]
    sep_norm
    have hstep := p1_err_drop_none_vregs_wp_ext_placed ext s coroPtr hpc hrun hsp_align hx19
    refine ret_sepWP_steps_frame_placed hcrl hstep (by sep_focus)
      fun s2 _ _ _ hcrl2 hregs2 => ?_
    rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2⟩
    refine ⟨?_, hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hcrl2⟩
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right 8#64 ?_)
    refine Entails.pure_right (by decide) ?_
    have hite0 : (0#64 = 0) = True := eq_true rfl
    simp only [hite0, ↓reduceIte]
    sep_norm
    have hf8 :
        ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
          memRegion (coroPtr + 248#64) 344 := by
      rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (Entails.trans
        (sepConj_mono_left
          (Q := ((coroPtr + 224#64) ↦₆₄ 0#64) ∗
                ((coroPtr + 232#64) ↦₆₄ 8#64) ∗
                ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                A.pool ∗
                stackAt s.sp dropSessionStructureLocal2Stack) hf8)
        (Entails.of_eq (by ac_rfl)))
  | some r =>
    dsimp only [p1LoadedRecordAt]
    sep_norm
    refine SepWPp.exists_elim fun g => ?_
    refine SepWPp.pure_elim fun _ => ?_
    rw [sessionRecordAt_eq_vecAt_sep_curSessionAt A (coroPtr + 0xe0#64) g r]
    refine SepWPp.weaken_frame (prevVecAt_unpack A coroPtr g.prevCap g.prevPtr) (by sep_focus) ?_
    sep_norm
    refine SepWPp.pure_elim fun hprev_lt => ?_
    refine SepWPp.weaken_frame
      (Entails.refl (curSessionAt A (coroPtr + 0xf8#64) g.cur r.currentSession))
      (by sep_focus) ?_
    cases hcur_g : g.cur <;> cases hcur_r : r.currentSession
    · dsimp only [curSessionAt, noneCap]
      have hstep := p1_err_drop_none_vregs_wp_ext_placed ext s coroPtr hpc hrun hsp_align hx19
      refine ret_sepWP_steps_frame_placed hcrl hstep (by sep_focus)
        fun s2 _ _ _ hcrl2 hregs2 => ?_
      rcases hregs2 with ⟨hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, _, hvregs2⟩
      refine ⟨?_, hsp2, htr2, hx19_2, hx22_2, hx25_2, hx26_2, hx28_2, hvregs2, hcrl2⟩
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      have hf8 :
          ((coroPtr + 248#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 256#64) 336 ⊢
            memRegion (coroPtr + 248#64) 344 := by
        rw [ProofLib.memRegion_split (coroPtr + 248#64) 8 336 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
      refine Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans
          (sepConj_mono_left
            (Q := ((coroPtr + 224#64) ↦₆₄ g.prevCap) ∗
                  ((coroPtr + 232#64) ↦₆₄ g.prevPtr) ∗
                  ((coroPtr + 240#64) ↦₆₄ 0#64) ∗
                  (if g.prevCap = 0 then emp
                   else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
                     memRegion g.prevPtr (g.prevCap.toNat * 24)) ∗
                  A.pool ∗
                  stackAt s.sp dropSessionStructureLocal2Stack) hf8)
          (Entails.of_eq (by ac_rfl)))
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · dsimp only [curSessionAt]
      exact SepWPp.pure_elim False.elim
    · rename_i G ses
      dsimp only [curSessionAt, sessionStateReprAt]
      sep_norm
      refine SepWPp.pure_elim fun _ => ?_
      have hss_split :
          ∃ R_ss : SepProp,
            (sessionStateAt A (coroPtr + 0xf8#64) G ses.state ⊢
              ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ ((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss) ∧
            (((coroPtr + 0xf8#64) ↦₆₄ G.localIk.cap) ∗ R_ss ⊢
              sessionStateAt A (coroPtr + 0xf8#64) G ses.state) := by
        unfold sessionStateAt
        exact pure_vecGhost_sep_split
      obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := hss_split
      refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
      sep_norm
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne : G.localIk.cap ≠ 0xffffffffffffffff#64 := by bv_omega
      have hto_call := p1_err_drop_ss_to_call_vregs_wp_ext_placed ext s coroPtr G.localIk.cap
        hcap_ne hpc hrun hsp_align hx19
      refine bind_sepWP_steps_frame_placed hcrl hto_call (by sep_focus)
        fun s1 _ hpc1 hrun1 hcrl1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1, hvregs1⟩
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
      refine SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
      refine call_lscro_nopanic_steps_frame_placed
        (spec := dropSessionStructureLocal2Spec A)
        (x := ⟨coroPtr + 0xf8#64, G, ses.state⟩)
        (T := sessionStateAt A (coroPtr + 0xf8#64) G ses.state ∗ A.pool ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
        hcrl1 hdrop_ss hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
        hx0_1 (by sep_focus)
        (hoom_false := fun _ => rfl)
        (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcrl2 => ?_)
      dsimp only [dropSessionStructureLocal2Spec]
      rw [hsp1, sepConj_assoc]
      refine SepWPp.pure_elim fun htr2_1 => ?_
      refine SepWPp.done hpc2 hrun2 ?_
      rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
      refine ⟨?_, hsp2_1.trans hsp1, htr2_1.trans htr1,
        hx19_cs2.trans hx19_1, hx22_cs2.trans hx22_1,
        hx25_cs2.trans hx25_1, hx26_cs2.trans hx26_1, hx28_cs2.trans hx28_1,
        hvregs_cs2.trans hvregs1, hcrl2⟩
      refine Entails.sepExists_right g.prevCap (Entails.sepExists_right g.prevPtr ?_)
      refine Entails.pure_right hprev_lt ?_
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))


set_option maxHeartbeats 1200000 in
theorem p1_err_tail_prev_core_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ SegUntrusted.vecU8Buf A cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hx25_s : s.readReg64 .x25 = s.sp + 0x210#64 := by rw [hsp_eq]; exact hx25
  rw [savedRegsAt_eq_sp_c70 sp s0]
  refine SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 =>
    SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c =>
    SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c =>
    SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  have hzero64 : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero64]
  let R_tail : SepProp :=
    ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
    ((sp + 0xc70#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 0xc78#64) ↦₆₄ s0.readReg64 .x30) ∗
    ((sp + 0xc80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 0xc88#64) ↦₆₄ s0.readReg64 .x27) ∗
    ((sp + 0xc90#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 0xc98#64) ↦₆₄ s0.readReg64 .x25) ∗
    ((sp + 0xca0#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 0xca8#64) ↦₆₄ s0.readReg64 .x23) ∗
    ((sp + 0xcb0#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 0xcb8#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((sp + 0xcc0#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 0xcc8#64) ↦₆₄ s0.readReg64 .x19) ∗
    A.pool ∗ stackAt sp allocHookStack
  by_cases hcap : prevCap = 0#64
  · subst hcap
    simp only [↓reduceIte]
    sep_norm
    have htail := p3_err_tail_b_vregs_wp_ext_placed
      ext s coroPtr outPtr 0x800000000000000c#64 prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine ret_sepWP_steps_frame_placed hcrl htail (by sep_focus)
      fun sf _ _ _ hcrlf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨?_, hspf, htrf, hcs_f, hvregsf, hcrlf⟩
    have hout := untrusted_out_entails A outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr 0#64 prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))
  · simp only [hcap, ↓reduceIte]
    have htail := p1_err_tail_prev_dealloc_core_wp_placed ext hdealloc s coroPtr outPtr
      0x800000000000000c#64 prevCap prevPtr
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
      (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
      (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27)
      (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      (cap.extractLsb' 0 32) (u_278.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
      hcap hprev_lt hpc hrun hsp_align hx19 hx22 hx25_s hx26 hx28
    rw [hsp_eq] at htail
    refine ret_sepWP_steps_frame_placed hcrl htail (by sep_focus)
      fun sf _ _ _ hcrlf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    have hcs_f : ClosureCalleeSaved s0 sf :=
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
        True.intro⟩
    refine ⟨?_, hspf, htrf, hcs_f, hvregsf, hcrlf⟩
    have hout := untrusted_out_entails A outPtr cap ptr devWord u_278 peer pad hpad hw4
    simp only [BitVec.add_zero] at hout
    have hcoro := coro_e0_368_fold coroPtr prevCap prevPtr 0#64
    have h370 := sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)
      (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)
      (u_278.extractLsb' 32 32)
    refine Entails.trans (Entails.of_eq (by dsimp only [R_tail]; simp only [BitVec.add_zero]; ac_rfl))
      (Entails.trans
        (sepConj_mono hcoro (sepConj_mono hout (sepConj_mono_left (Q := R_tail) h370)))
        (Entails.of_eq (by dsimp only [R_tail]; ac_rfl)))


set_option maxHeartbeats 1200000 in
theorem p1_err_drop_and_return_vregs_wp_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (s0 s3 : State) (sp coroPtr outPtr cap ptr devWord u_278 : BitVec 64)
    (b_2c0 : BitVec 8)
    (peer : AddrGhost) (pad : List (BitVec 8))
    (hpad : pad.length = 7)
    (hw4 : peer.device :: pad = unpack64 devWord)
    (hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hsp3_s : s3.sp = sp)
    (hpc3 : s3.pc = stageP1EntryPlaced + 0x3588#64)
    (hrun3 : s3.status = .Running)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx22_3 : s3.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx25_3 : s3.readReg64 .x25 = sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx28_3 : s3.readReg64 .x28 = 0x800000000000000c#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s3
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       SegUntrusted.vecU8Buf A cap ptr peer.name.bytes ∗
       ((sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((sp + 0x378#64) ↦₆₄ ((BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((sp + 0x380#64) ↦₆₄ (devWord.extractLsb' 0 32 ++ (BitVec.ofNat 64 peer.name.bytes.length).extractLsb' 32 32)) ∗
       ((sp + 0x388#64) ↦₆₄ (u_278.extractLsb' 0 32 ++ devWord.extractLsb' 32 32)) ∗
       ((sp + 0x390#64) ↦₃₂ u_278.extractLsb' 32 32) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp untrustedErrCallStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp untrustedErrCallStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s3.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s3 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt))
    (by sep_focus) ?_
  have hdrop := p1_err_drop_record_core_wp_placed (Scope := Scope) (Qp := PanicOomProp s0)
    hdrop_ss opt s3 coroPtr hcrl3 hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hdrop
  refine SepWPp.bind_sepWPp_steps_frame hdrop (by sep_focus)
    fun s4 _ hpc4 hrun4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_s, htr4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, hvregs4_3, hcrl4⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  sep_norm
  refine SepWPp.exists_elim fun prevCap => SepWPp.exists_elim fun prevPtr => ?_
  refine SepWPp.pure_elim fun hprev_lt => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_dropSS sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt))
    (by sep_focus) ?_
  have hret := p1_err_tail_prev_core_wp_placed (Qp := PanicOomProp s0)
    hdealloc s0 s4 sp coroPtr outPtr
    prevCap prevPtr cap ptr devWord u_278 b_2c0 peer pad
    hprev_lt hpad hw4 hcrl4 hsp4_s hpc4 hrun4 hsp4_align
    hx19_4 (hx22_4.trans hx22_3) (hx25_4.trans hx25_3)
    (hx26_4.trans hx26_3) (hx28_4.trans hx28_3)
  refine SepWPp.bind_sepWPp_steps_frame hret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_4, hcs_f, hvregsf_4, hcrlf⟩
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_alloc sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hspf, htrf_4.trans htr4_3, hcs_f, hvregsf_4.trans hvregs4_3, hcrlf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))


set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_err_ok_kit_x_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A 0#64}
    {ikit : IdentityStoreSpec A 0#64}
    {st : kit.StoreState} {ist : ikit.IdState}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hclone : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneSpec A)))
    (hstack_lt : untrustedErrCallStack ≤ 2 ^ 64)
    (s0 s : State)
    (outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr : BitVec 64)
    (b_2c0 b_390 : BitVec 8)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x6e4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx23 : s.readReg64 .x23 = 0#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
       p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion (s.sp + 0x3e0#64) 368 ∗
       cells (s.sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       FromRecordCallees.lsLogOff ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr
         (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt s.sp untrustedErrCallStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          memRegion (s.sp + 0x3e0#64) 368 ∗
          cells (s.sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
          FromRecordCallees.lsLogOff ∗
          kit.storeAt sessStorePtr st ∗
          ikit.identityAt idStorePtr
            (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
          A.pool ∗
          stackAt s.sp untrustedErrCallStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  have hstep1 := p1_untrusted_to_clone_vregs_wp_ext_placed ext s
    coroPtr remoteAddrPtr hpc hrun hsp_align hx19 hx20 hx23
  refine bind_sepWP_steps_frame_placed hcrl hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hcrl1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx8_1, hx19_1, hx21_1, hx25_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have htr1_pre : s0.trace <+: s1.trace := htr1 ▸ htr
  refine SepWPp.weaken_frame (memRegion_368_untrusted_entails s.sp) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun pad => ?_
  refine SepWPp.pure_elim fun hpad => ?_
  have haddr_eq :
      protocolAddressAt A peer remoteAddrPtr =
        vecGhostAt A peer.name remoteAddrPtr ∗
          ((remoteAddrPtr + 0x18#64) ↦₈ peer.device) ∗
          memRegion (remoteAddrPtr + 0x19#64) 7 := rfl
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt))
    (by sep_focus) ?_
  refine call_lscro_oom_steps_frame_placed
    (x := (remoteAddrPtr, s.sp + 0x3e0#64, peer.name))
    (P_spec := vecGhostAt A peer.name remoteAddrPtr ∗ memRegion (s.sp + 0x3e0#64) 24 ∗
      A.pool ∗ stackAt s1.sp extHookStack)
    hcrl1 htr1_pre hclone hpc1 hrun1 hsp1_al hx30_1
    (stringClone_pre_intro hx0_1 hx8_1)
    (by rw [hsp1]; sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcrl2 => ?_)
  dsimp only [stringCloneSpec]
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_untrustedErr_to_ext s.sp hstack_lt).symm)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, _, _, hx25_cs2, _, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = remoteAddrPtr := hx21_cs2.trans hx21_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  refine SepWPp.weaken_frame (vecU8_unpack_3e0 A s.sp peer.name.bytes) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (s.sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq s.sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hw4_ex : ∃ devWord : BitVec 64, peer.device :: pad = unpack64 devWord := by
    rcases pad with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | _⟩⟩⟩⟩⟩⟩⟩ <;>
      try simp at hpad
    exact ⟨p7 ++ p6 ++ p5 ++ p4 ++ p3 ++ p2 ++ p1 ++ peer.device,
      (unpack64_pack64 peer.device p1 p2 p3 p4 p5 p6 p7).symm⟩
  obtain ⟨devWord, hw4⟩ := hw4_ex
  have hstep3 := p1_untrusted_post_clone_vregs_wp_ext_placed ext s2
    coroPtr remoteAddrPtr outPtr cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord
    u250 u258 u260 u268 u270 u278
    ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390
    d0 b_390 peer pad
    hw4 hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx25_2
  rw [hsp2_s] at hstep3
  refine bind_sepWP_steps_frame_placed hcrl2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hcrl3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_s, htr3_2, hx19_3, hx22_3, hx25_3, hx26_3, hx28_3, _, hvregs3_2⟩
  refine SepWPp.weaken_frame
    (cells_3e0_entails_memRegion_368 s.sp cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord)
    (by sep_focus) ?_
  have hc250 := cells6_fold (coroPtr + 0x250#64)
    0x800000000000000c#64 cap ptr (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27)
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_a90_rejoin s.sp 0x800000000000000c#64 cap ptr
      (BitVec.ofNat 64 peer.name.bytes.length) devWord (s2.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq haddr_eq.symm) (by sep_focus) ?_
  have hdrop_ret := p1_err_drop_and_return_vregs_wp_ext_placed
    (Scope := Scope)
    hdrop_ss hdealloc hstack_lt opt s0 s3 s.sp coroPtr outPtr cap ptr devWord (s2.readReg64 .x27) b_2c0
    peer pad hpad hw4 hcrl3 hsp3_s hpc3 hrun3 hsp_align
    hx19_3 hx22_3 hx25_3 hx26_3 hx28_3
  refine SepWPp.bind_sepWPp_steps_frame hdrop_ret (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_3, hcs_f, hvregsf_3, hcrlf⟩
  refine SepWPp.done hpcf hrunf ?_
  have htr_full : sf.trace = s.trace := by
    rw [htrf_3, htr3_2, htr2_1, htr1]
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s := by
    rw [hvregsf_3, hvregs3_2, hvregs_cs2, hvregs1]
  refine ⟨htr_full, ?_, hspf, hcs_f, hvregs_full, hcrlf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))


set_option maxHeartbeats 1200000 in
theorem stageP1_untrusted_from_trust_x_ext_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {kit : SessionStoreSpec A 0#64}
    {ikit : IdentityStoreSpec A 0#64}
    {st : kit.StoreState} {ist : ikit.IdState} {Q : Prop}
    (peer : AddrGhost) (remoteIdKey : IdentityKey)
    (opt : Option (SessionRecord (List (BitVec 8))))
    (hdrop_ss : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 512)
      (StoreKit.withLsCodeRoLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hdealloc : subroutine_ok (stageP1ProgPlaced ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hclone : subroutine_ok (stageP1ProgPlaced ext)
      (lsmpl.base 623) (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneSpec A)))
    (hikit_shim : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustShimOff)
      (StoreKit.withLsRoCl lsmpl (kitTrustShimSpec ikit)))
    (hikit_poll : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustPollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitTrustPollPlacedSpecI ikit)))
    (hikit_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + ikit.trustFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec))
    (hstack_lt : stageP1UntrustedCallStack kit ikit ≤ 2 ^ 64)
    (haddr_id : ikit.addrOk peer.val)
    (htrust_false : ∀ ans, ikit.trustRel ist peer.val remoteIdKey .receiving ans → ans = .ok false)
    (s0 s6 : State)
    (sp outPtr coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     sessStorePtr idStorePtr
     preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
     kyberStorePtr kyberStoreVt
     u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0 : BitVec 64)
    (hcrl6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
    (hfs6_ikit : FsAt ikit.envOk Q (stageP1ProgPlaced ext) s6)
    (hpc6 : s6.pc = 0#64 + ikit.trustShimOff)
    (hrun6 : s6.status = .Running)
    (hsp6_eq : s6.sp = sp)
    (hsp_saved : sp + 0xcd0#64 = s0.sp)
    (hsp6_align : (s6.sp &&& 15#64 == 0#64) = true)
    (htr6_pre : s0.trace <+: s6.trace)
    (hx0_6 : s6.readReg64 .x0 = idStorePtr)
    (hx1_6 : s6.readReg64 .x1 = remoteAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3_6 : s6.readReg64 .x3 = 1#64)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = coroPtr + 0x390#64)
    (hx26_6 : s6.readReg64 .x26 = outPtr)
    (hx27_6 : s6.readReg64 .x27 = ctxPtr)
    (hx30_6 : s6.readReg64 .x30 = stageP1EntryPlaced + 0x650#64) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s6
      (p1LoadedRecordAt Scope A coroPtr opt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ 0#8) ∗
       processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
         spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
       ((coroPtr + 0x390#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x398#64) ↦₆₄ u_398) ∗
       ((coroPtr + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt s0.sp s0 ∗
       memRegion outPtr 48 ∗
       ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
       ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
       ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
       FromRecordCallees.lsLogOff ∗
       kit.storeAt sessStorePtr st ∗
       ikit.identityAt idStorePtr ist ∗
       protocolAddressAt A peer remoteAddrPtr ∗
       ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
       A.pool ∗
       stackAt sp (stageP1UntrustedCallStack kit ikit))
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ v_a8 : BitVec 64, ∃∗ v_b8 : BitVec 64, ∃∗ v_d0 : BitVec 64,
            memRegion (coroPtr + 0xe0#64) 368 ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            processPrekeyInnerInitAt coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr ikit.id_vt preKeyStorePtr preKeyStoreVt
              spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            cells (coroPtr + 0x398#64) 2 ∗
            ((sp + 0xa8#64) ↦₆₄ v_a8) ∗
            ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
            ((sp + 0xb8#64) ↦₆₄ v_b8) ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            memRegion (sp + 0x370#64) 36 ∗
            memRegion (sp + 0x3e0#64) 368 ∗
            cells (sp + 0xa90#64) 6 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            apiDecResultAt A outPtr (.error (.untrustedIdentity peer.val)) ∗
            ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
            ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
            ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
            FromRecordCallees.lsLogOff ∗
            kit.storeAt sessStorePtr st ∗
            ikit.identityAt idStorePtr
              (ikit.trustUpdate ist peer.val remoteIdKey .receiving (.ok false)) ∗
            protocolAddressAt A peer remoteAddrPtr ∗
            ((msgPtr + 0xc8#64) ↦ₛ remoteIdKey.publicKey.bytes.toList) ∗
            A.pool ∗
            stackAt sp (stageP1UntrustedCallStack kit ikit)) ∧
        ikit.trustRel ist peer.val remoteIdKey .receiving (.ok false) ∧
        sf.trace = s6.trace ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false) ∧
        sf.sp = s0.sp ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s6 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  have hp1_le : stageP1CallStack kit ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_left _ _) hstack_lt
  have herr_le : untrustedErrCallStack ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hstack_lt
  have htrust_le : trustCallStack ikit ≤ 2 ^ 64 := Nat.le_trans (Nat.le_max_right _ _) hp1_le
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le))
    (by sep_focus) ?_
  sep_norm
  have htrust_raw := stageP1_trust_call_wp_kit_x_ext_placed (ist := ist)
    peer remoteIdKey hdealloc hikit_shim hikit_poll hikit_drop htrust_le haddr_id s0 s6
    outPtr coroPtr ctxPtr msgPtr remoteAddrPtr idStorePtr
    u_a8 u_b0 u_b8 u_c0 u_c8 u_d0 u_398 u_3a0
    hcrl6 hfs6_ikit hpc6 hrun6 hsp6_align htr6_pre
    hx0_6 hx1_6 hx2_6 hx3_6 hx19_6 hx21_6 hx26_6 hx27_6 hx30_6
  have htrust := trust_call_wp_specialize_false_prog_placed htrust_false htrust_raw
  rw [hsp6_eq] at htrust
  simp only [BitVec.add_assoc] at htrust
  refine SepWPp.bind_sepWPp_steps_frame htrust (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hrel_trust, htrm, hx20_m, hx23_m, hspm, hx19_m, _, hvregsm, hcrlm⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hspm, ← hsp6_eq]; exact hsp6_align
  have htrm_pre : s0.trace <+: sm.trace := by
    rcases htr6_pre with ⟨pre, hpre⟩
    exact ⟨pre ++ ikit.trustEvs peer.val remoteIdKey .receiving (.ok false),
      by rw [htrm, ← hpre, List.append_assoc]⟩
  sep_norm
  refine SepWPp.exists_elim fun v_a8 =>
    SepWPp.exists_elim fun v_b8 =>
    SepWPp.exists_elim fun v_d0 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1_to_trust kit ikit sp hp1_le).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_p1 kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt))
    (by sep_focus) ?_
  unfold processPrekeyInnerInitAt
  sep_norm
  have herr := stageP1_untrusted_err_ok_kit_x_ext_placed
    (Scope := Scope) (kit := kit) (ikit := ikit) (st := st) (ist := ist)
    peer remoteIdKey opt hdrop_ss hdealloc hclone herr_le s0 sm
    outPtr coroPtr msgPtr remoteAddrPtr sessStorePtr idStorePtr
    0#8 0#8
    hcrlm hpcm hrunm hspm_align htrm_pre hx19_m hx20_m hx23_m
  rw [hspm, hsp_saved] at herr
  have herr_re := SepWPp.mono_run herr fun sf P_f h =>
    let ⟨htrf, hent, hregs⟩ := h
    And.intro hent (And.intro htrf hregs)
  refine SepWPp.bind_sepWPp_steps_frame herr_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcs_f, hvregsf_m, hcrlf⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_stageP1Untrusted_to_err kit ikit sp hstack_lt).symm)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hrel_trust, htrf.trans htrm, hspf, hcs_f, hvregsf_m.trans hvregsm, hcrlf⟩
  refine Entails.sepExists_right v_a8
    (Entails.sepExists_right v_b8
      (Entails.sepExists_right v_d0 ?_))
  rw [hsp_saved]
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedExtPlaced
