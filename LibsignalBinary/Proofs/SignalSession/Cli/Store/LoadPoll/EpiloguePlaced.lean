/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Epilogue
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable Epilogue & Deallocation Blocks for `load_session::{closure#0}`

Proves the shared epilogue (`+0x0e4`) and `name`/`bytes` deallocation blocks on Block `569`
(`lsProg_569 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0
  extractLsb_0_64_append extractLsb_64_64_append setWidth_64_append

/-- Shared epilogue (`+0x0e4 .. +0x12c`) on Block `569`. -/
theorem lpoll_epilogue_e4_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (x : SessLoadPollGhost) (s0 s : State)
    (w0 w1 w2 w3 w4 : BitVec 64) (q140 : BitVec 128) (bs312 : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    (hbs312 : bs312.length = 312)
    (hpc : s.pc = (blkPl_569).base + 228#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0x350#64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx27 : s.readReg64 .x27 = w0)
    (hx26 : s.readReg64 .x26 = w1)
    (hx23 : s.readReg64 .x23 = w2)
    (hx25 : s.readReg64 .x25 = w3)
    (hx22 : s.readReg64 .x22 = w4)
    (hx28 : s.readReg64 .x28 = s0.sp - 0x210#64)
    (hfoc : P ⊢ epiloguePre s0 x q140 bs312 ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 w4 q140 bs312 ∗ F) →
      post sf P_f) :
    SepWP ((blkPC_569).rebase (blkPl_569).base H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_350 hsp_align hsp
  refine SepWP.weaken_pre hfoc ?_
  unfold epiloguePre sessLoadBoxAt savedCalleeSlots
  rw [sret368_epilogue_split x.call.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun o0 => SepWP.exists_elim fun o1 =>
    SepWP.exists_elim fun o2 => SepWP.exists_elim fun o3 =>
    SepWP.exists_elim fun o4 => SepWP.exists_elim fun oq => ?_
  unfold Arm64.pointsTo128
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply StoreKit.sepWP_seq_lscro (mid := lsρ memcpyName) hcrl
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_mc
  wp_call_lscro (lpoll_memcpy_placed_ok hC) hcrl_mc (x.call.out + 0x38#64, s0.sp - 0x348#64, bs312)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine hk _ _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [CalleeSavedPreserved, arm64_norm, *]) ?_
  unfold epilogueOut savedCalleeSlots sessLoadBoxAt Arm64.pointsTo128
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_focus

/-- Name deallocation block (`+0x0d8 .. +0x0e0`) when `nameCap ≠ 0#64`, chaining into `lpoll_epilogue_e4_placed`. -/
theorem lpoll_drop_name_d8_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (x : SessLoadPollGhost) (s0 s : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (w0 w1 w2 w3 w4 : BitVec 64) (q140 : BitVec 128) (bs312 : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    (hncap : nameCap ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hbs312 : bs312.length = 312)
    (hpc : s.pc = (blkPl_569).base + 216#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0x350#64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx1 : s.readReg64 .x1 = nameCap)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx27 : s.readReg64 .x27 = w0)
    (hx26 : s.readReg64 .x26 = w1)
    (hx23 : s.readReg64 .x23 = w2)
    (hx25 : s.readReg64 .x25 = w3)
    (hx22 : s.readReg64 .x22 = w4)
    (hx28 : s.readReg64 .x28 = s0.sp - 0x210#64)
    (hfoc : P ⊢ SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      epiloguePre s0 x q140 bs312 ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 w4 q140 bs312 ∗ A.pool ∗ F) →
      post sf P_f) :
    SepWP ((blkPC_569).rebase (blkPl_569).base H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_350 hsp_align hsp
  obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
  have hep := lpoll_epilogue_e4_placed hC
  refine SepWP.weaken_pre hfoc ?_
  refine SepWP.fold (vecU8_free_ne A (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
  unfold epiloguePre
  simp only [sepConj_assoc]
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_da
  apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 228#64) hcrl_da
  wp_call_lscro (lpoll_dealloc_placed_ok hC) hcrl_da (namePtr, nameCap.toNat, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_e4
  refine hep x s0 _ w0 w1 w2 w3 w4 q140 bs312 _ (A.pool ∗ F) hbs312
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_align
    (by simp only [arm64_norm, *])
    hcrl_e4
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by unfold epiloguePre; simp only [sepConj_assoc]; sep_focus)
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hk sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
        (Entails.trans hPf (Entails.of_eq (by ac_rfl)))

/-- Tail block at `+0x14c .. +0x158` on Block `569`. -/
theorem lpoll_finish_14c_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (x : SessLoadPollGhost) (s0 s : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (w0 w1 w2 w3 w4 : BitVec 64) (q140 : BitVec 128) (bs312 : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hbs312 : bs312.length = 312)
    (hpc : s.pc = (blkPl_569).base + 332#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0x350#64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx27 : s.readReg64 .x27 = w0)
    (hx26 : s.readReg64 .x26 = w1)
    (hx25 : s.readReg64 .x25 = w3)
    (hx22 : s.readReg64 .x22 = w4)
    (hx28 : s.readReg64 .x28 = s0.sp - 0x210#64)
    (hfoc : P ⊢ ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
      ((s0.sp - 0x350#64) ↦₆₄ w2) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      epiloguePre s0 x q140 bs312 ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 w4 q140 bs312 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x350#64) ↦₆₄ w2) ∗ A.pool ∗ F) →
      post sf P_f) :
    SepWP ((blkPC_569).rebase (blkPl_569).base H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hep := lpoll_epilogue_e4_placed hC
  have hdn := lpoll_drop_name_d8_placed hC
  clear hC
  refine SepWP.weaken_pre hfoc ?_
  by_cases hncap : nameCap = 0#64
  · subst hncap
    refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 228#64) hcrl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_e4
    refine hep x s0 _ w0 w1 w2 w3 w4 q140 bs312 _
      (((s0.sp - 0x1f8#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0x350#64) ↦₆₄ w2) ∗ A.pool ∗ F)
      hbs312
      (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hcrl_e4
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))
  · have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 216#64) hcrl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_d8
    refine hdn x s0 _ nameCap namePtr nameBs
      w0 w1 w2 w3 w4 q140 bs312 _
      (((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x350#64) ↦₆₄ w2) ∗ F)
      hncap hnlen hnlt hnptr hbs312
      (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hcrl_d8
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
      (by unfold epiloguePre; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))

/-- Bytes deallocation block (`+0x13c .. +0x148`) when `bytesCap ≠ 0#64`, chaining into `lpoll_finish_14c_placed`. -/
theorem lpoll_drop_bytes_13c_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (x : SessLoadPollGhost) (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (w0 w1 w2 w3 w4 : BitVec 64) (q140 : BitVec 128) (bs312 : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    (hbcap : bytesCap ≠ 0#64)
    (hblen : bytesBs.length ≤ bytesCap.toNat)
    (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hbs312 : bs312.length = 312)
    (hpc : s.pc = (blkPl_569).base + 316#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0x350#64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx24 : s.readReg64 .x24 = bytesPtr)
    (hx23 : s.readReg64 .x23 = bytesCap)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx27 : s.readReg64 .x27 = w0)
    (hx26 : s.readReg64 .x26 = w1)
    (hx25 : s.readReg64 .x25 = w3)
    (hx22 : s.readReg64 .x22 = w4)
    (hx28 : s.readReg64 .x28 = s0.sp - 0x210#64)
    (hfoc : P ⊢ SpqrV1.ChainProofs.bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
      ((s0.sp - 0x350#64) ↦₆₄ w2) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      epiloguePre s0 x q140 bs312 ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 w4 q140 bs312 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x350#64) ↦₆₄ w2) ∗ A.pool ∗ F) →
      post sf P_f) :
    SepWP ((blkPC_569).rebase (blkPl_569).base H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_350 hsp_align hsp
  obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
  have hf14c := lpoll_finish_14c_placed hC
  refine SepWP.weaken_pre hfoc ?_
  refine SepWP.fold (vecU8_free_ne A (ptr := bytesPtr) hbcap hblen hblt) (by sep_focus) ?_
  unfold epiloguePre
  simp only [sepConj_assoc]
  apply StoreKit.sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_da
  apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 332#64) hcrl_da
  wp_call_lscro (lpoll_dealloc_placed_ok hC) hcrl_da (bytesPtr, bytesCap.toNat, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_14c
  refine hf14c x s0 _ nameCap namePtr nameBs
    w0 w1 w2 w3 w4 q140 bs312 _ F
    hnlen hnlt hnptr hbs312
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_align
    (by simp only [arm64_norm, *])
    hcrl_14c
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by unfold epiloguePre; simp only [sepConj_assoc]; sep_focus)
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hk sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
        (Entails.trans hPf (Entails.of_eq (by ac_rfl)))

end Placed

end CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
