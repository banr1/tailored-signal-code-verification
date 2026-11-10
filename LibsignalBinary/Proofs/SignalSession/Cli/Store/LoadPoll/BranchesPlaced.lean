/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.EpiloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Branches
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable `Err` and `Ok([])` Branches for `load_session::{closure#0}`

Proves `lpoll_branch_err_placed` and `lpoll_branch_ok_nil_placed` on Block `569` (`lsProg_569 H`)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
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
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

theorem lpoll_post_entails_placed [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (stk : Nat) (x : SessLoadPollGhost) (s0 sf : State)
    (gr : Except Unit (List (BitVec 8)))
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
    (hgr : gr = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧ sf.trace = s0.trace)
    (hans : SessLoadAns Scope gr ans) :
    (sessLoadOutAt A x.call.out ans ∗
      sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool ∗ stackAt s0.sp stk) ⊢
      (sessLoadPollSpecPlaced rd pathOk Scope A stk).post x s0 sf := by
  simp only [sessLoadPollSpecPlaced, StoreKit.withLsCodeRoLoaded,
    sepExists_sepConj_left, sepConj_assoc]
  exact Entails.sepExists_right gr
    (Entails.sepExists_right ans (Entails.pure_right ⟨hgr, hans⟩ (Entails.refl _)))

/-- Branch 1 (`+0x054` on `gr = .error ()`) on Block `569`. -/
theorem lpoll_branch_err_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (x : SessLoadPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (hstk : pollMinStk addrStk getStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hgr : Except.error () = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
      sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_569).base + 84#64)
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0x350#64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.call.fut)
    (hx20 : sm2.readReg64 .x20 = x.call.out)
    (hx21 : sm2.readReg64 .x21 = namePtr)
    (hx25 : sm2.readReg64 .x25 = s0.sp - 0x210#64) :
    SepWP ((blkPC_569).rebase (blkPl_569).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0x1e0#64) (.error ()) ∗
        postGetCommon A s0 x addrStk getStk stk nameCap namePtr nameBs c_sp0 q140)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (sessLoadPollSpecPlaced rd pathOk Scope A stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hne : (speWord 1 + 2#64 == 0#64) = false := speWord_one_add_two_ne_zero
  have hep := lpoll_epilogue_e4_placed hC
  have hdn := lpoll_drop_name_d8_placed hC
  clear hC
  unfold postGetCommon
  change SepWP _ _ _ (speAt A (utf8 "read") (s0.sp - 0x1e0#64) .invalidState ∗ _) _
  rw [speAt_read_invalidState_unpack A s0.sp, subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun errBs => SepWP.exists_elim fun errCap =>
    SepWP.exists_elim fun errPtr => SepWP.exists_elim fun fnPtr => ?_
  rw [ProofLib.memRegion_eq_exists_bytes (s0.sp - 0x348#64) 312 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun bs312 => ?_
  refine SepWP.weaken_pre
    (by sep_focus :
      _ ⊢
      ⌜bs312.length = 312⌝ ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ errCap) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ errPtr) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
        ((s0.sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        (⌜errBs.length ≤ errCap.toNat ∧ errCap.toNat < 2 ^ 63 ∧ errPtr ≠ 0#64⌝ ∗
          if errCap = 0#64 then emp
          else A.live errPtr errCap.toNat 1 ∗ (errPtr ↦ₛ errBs) ∗
            memRegion (errPtr + BitVec.ofNat 64 errBs.length) (errCap.toNat - errBs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗
        memRegion (s0.sp - 0x1b0#64) 320 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - extHookStack) ∗
        stackAt (s0.sp - 0x350#64) extHookStack ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A x.self x.dir ∗
        protocolAddressAt A x.call.addr x.call.addrA ∗
        A.pool) ?_
  refine SepWP.pure_elim fun hbs312 => ?_
  let F_err : SepProp :=
    ((s0.sp - 0x1e0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ errCap) ∗
    ((s0.sp - 0x1d0#64) ↦₆₄ errPtr) ∗
    ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
    ((s0.sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
    (⌜errBs.length ≤ errCap.toNat ∧ errCap.toNat < 2 ^ 63 ∧ errPtr ≠ 0#64⌝ ∗
      if errCap = 0#64 then emp
      else A.live errPtr errCap.toNat 1 ∗ (errPtr ↦ₛ errBs) ∗
        memRegion (errPtr + BitVec.ofNat 64 errBs.length) (errCap.toNat - errBs.length)) ∗
    (fnPtr ↦ᵣ utf8 "read") ∗
    memRegion (s0.sp - 0x1b0#64) 320 ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    dirAt A x.self x.dir ∗
    protocolAddressAt A x.call.addr x.call.addrA
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x 0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr
        (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 ∗
        A.pool ∗ F_err) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (sessLoadPollSpecPlaced rd pathOk Scope A stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hgr_f :
        Except.error () = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
          sf.trace = s0.trace :=
      ⟨hgr.1, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (lpoll_post_entails_placed rd pathOk Scope A stk x s0 sf (.error ()) (.error ()) hgr_f rfl)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.error ()) nameCap namePtr nameBs c_sp0
        (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr))
    have hreasm :=
      speAt_read_invalidState_reassemble A s0.sp x.call.out errBs errCap errPtr fnPtr bs312 hbs312
    have h312 : ((s0.sp - 0x348#64) ↦ₛ bs312) ⊢ memRegion (s0.sp - 0x348#64) 312 :=
      hbs312 ▸ pointsToBytes_entails_memRegion (s0.sp - 0x348#64) bs312
    have hgrp :
        epilogueOut s0 x 0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr
          (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 ∗
          A.pool ∗ F_err =
        (((x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.call.out + 8#64) ↦₆₄ speWord 1) ∗
          ((x.call.out + 0x10#64) ↦₆₄ errCap) ∗ ((x.call.out + 0x18#64) ↦₆₄ errPtr) ∗
          ((x.call.out + 0x20#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((x.call.out + 0x28#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
          ((x.call.out + 0x38#64) ↦ₛ bs312) ∗
          (⌜errBs.length ≤ errCap.toNat ∧ errCap.toNat < 2 ^ 63 ∧ errPtr ≠ 0#64⌝ ∗
            if errCap = 0#64 then emp
            else A.live errPtr errCap.toNat 1 ∗ (errPtr ↦ₛ errBs) ∗
              memRegion (errPtr + BitVec.ofNat 64 errBs.length) (errCap.toNat - errBs.length)) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗
          ((s0.sp - 0x1e0#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 0x1d8#64) ↦₆₄ errCap) ∗ ((s0.sp - 0x1d0#64) ↦₆₄ errPtr) ∗
          ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((s0.sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
          memRegion (s0.sp - 0x1b0#64) 320) ∗
        (((s0.sp - 0x348#64) ↦ₛ bs312) ∗
          ((((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
            ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
            ((s0.sp - 0x210#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
            memRegion (s0.sp - 0x200#64) 8 ∗
            memRegion (s0.sp - 0x070#64) 16 ∗
            savedCalleeSlots s0 ∗
            memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
              (subMax addrStk getStk - extHookStack) ∗
            stackAt (s0.sp - 0x350#64) extHookStack ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
            sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗
            dirAt A x.self x.dir ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            A.pool))) := by
      unfold epilogueOut F_err; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left h312)) ?_
    exact Entails.of_eq (by ac_rfl)
  unfold Arm64.pointsTo128
  simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
  by_cases hncap : nameCap = 0#64
  · subst hncap
    refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 228#64) hcrl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_e4
    refine hep x s0 _
      0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 _ (A.pool ∗ F_err)
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
      (by
        unfold epiloguePre F_err Arm64.pointsTo128
        simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))
  · have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 216#64) hcrl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_d8
    refine hdn x s0 _ nameCap namePtr nameBs
      0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 _ F_err
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
      (by
        unfold epiloguePre F_err Arm64.pointsTo128
        simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

/-- Branch 2 (`+0x054` on `gr = .ok []`) on Block `569`. -/
theorem lpoll_branch_ok_nil_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (x : SessLoadPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (hstk : pollMinStk addrStk getStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hgr : Except.ok ([] : List (BitVec 8)) =
        x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
      sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_569).base + 84#64)
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0x350#64)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.call.fut)
    (hx20 : sm2.readReg64 .x20 = x.call.out)
    (hx21 : sm2.readReg64 .x21 = namePtr)
    (hx25 : sm2.readReg64 .x25 = s0.sp - 0x210#64) :
    SepWP ((blkPC_569).rebase (blkPl_569).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0x1e0#64) (.ok []) ∗
        postGetCommon A s0 x addrStk getStk stk nameCap namePtr nameBs c_sp0 q140)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (sessLoadPollSpecPlaced rd pathOk Scope A stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hf14c := lpoll_finish_14c_placed hC
  have hdb13c := lpoll_drop_bytes_13c_placed hC
  clear hC
  unfold postGetCommon
  rw [getResultAt_ok_unpack A s0.sp [], subStack_split s0.sp hext_le hmin_hi]
  simp only [List.length_nil, sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun bytesCap => SepWP.exists_elim fun bytesPtr =>
    SepWP.pure_elim fun ⟨_hblen, hblt, hbptr⟩ => ?_
  rw [ProofLib.memRegion_eq_exists_bytes (s0.sp - 0x348#64) 312 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun bs312 => ?_
  refine SepWP.weaken_pre
    (by sep_focus :
      _ ⊢
      ⌜bs312.length = 312⌝ ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ 0#64) ∗
        SpqrV1.ChainProofs.bytesAt false bytesPtr [] ∗
        vecU8Tail A bytesCap bytesPtr [] ∗
        memRegion (s0.sp - 0x1c0#64) 16 ∗
        memRegion (s0.sp - 0x1b0#64) 320 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - extHookStack) ∗
        stackAt (s0.sp - 0x350#64) extHookStack ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A x.self x.dir ∗
        protocolAddressAt A x.call.addr x.call.addrA ∗
        A.pool) ?_
  refine SepWP.pure_elim fun hbs312 => ?_
  let F_nil : SepProp :=
    ((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x1c8#64) ↦₆₄ 0#64) ∗
    memRegion (s0.sp - 0x1c0#64) 16 ∗
    memRegion (s0.sp - 0x1b0#64) 320 ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    dirAt A x.self x.dir ∗
    protocolAddressAt A x.call.addr x.call.addrA
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x 0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
        q140 bs312 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗ A.pool ∗ F_nil) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (sessLoadPollSpecPlaced rd pathOk Scope A stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hgr_f :
        Except.ok ([] : List (BitVec 8)) =
            x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
          sf.trace = s0.trace :=
      ⟨hgr.1, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (lpoll_post_entails_placed rd pathOk Scope A stk x s0 sf (.ok []) (.ok none) hgr_f rfl)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.ok none) nameCap namePtr nameBs c_sp0 q140)
    have hnone :=
      sessLoadOutAt_none_reassemble A x.call.out okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
        q140 bs312 hbs312
    have hslot := slot170_ok_collapse s0.sp okTagVec bytesCap bytesPtr 0#64
    have h312 : ((s0.sp - 0x348#64) ↦ₛ bs312) ⊢ memRegion (s0.sp - 0x348#64) 312 :=
      hbs312 ▸ pointsToBytes_entails_memRegion (s0.sp - 0x348#64) bs312
    have hgrp :
        epilogueOut s0 x 0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
          q140 bs312 ∗
          ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗ A.pool ∗ F_nil =
        (((x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
          ((x.call.out + 8#64) ↦₆₄ okTagVec) ∗ ((x.call.out + 0x10#64) ↦₆₄ c_sp0) ∗
          ((x.call.out + 0x18#64) ↦₆₄ (s0.sp - 0x210#64)) ∗ ((x.call.out + 0x20#64) ↦₆₄ 0#64) ∗
          ((x.call.out + 0x28#64) ↦₁₂₈ q140) ∗ ((x.call.out + 0x38#64) ↦ₛ bs312)) ∗
        (((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗ ((s0.sp - 0x1c8#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 0x1c0#64) 16 ∗ memRegion (s0.sp - 0x1b0#64) 320) ∗
        ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
        ((((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
          memRegion (s0.sp - 0x200#64) 8 ∗
          memRegion (s0.sp - 0x070#64) 16 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - extHookStack) ∗
          stackAt (s0.sp - 0x350#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗
          dirAt A x.self x.dir ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗
          A.pool)) := by
      unfold epilogueOut F_nil; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hnone (sepConj_mono hslot (sepConj_mono_left h312))) ?_
    exact Entails.of_eq (by ac_rfl)
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    refine SepWP.fold (vecU8_free_zero A bytesPtr (bs := []) (Nat.zero_le _)) (by sep_focus) ?_
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 332#64) hcrl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_14c
    refine hf14c x s0 _ nameCap namePtr nameBs
      0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
      q140 bs312 _ F_nil
      hnlen hnlt hnptr hbs312
      (by simp only [arm64_norm, *]; try bv_omega)
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
      (by unfold epiloguePre F_nil; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf
  · have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    apply StoreKit.sepWP_seq_lscro (mid := (blkPl_569).base + 316#64) hcrl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_13c
    refine hdb13c x s0 _ bytesCap bytesPtr [] nameCap namePtr nameBs
      0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
      q140 bs312 _ F_nil
      hbcap (Nat.zero_le _) hblt hbptr hnlen hnlt hnptr hbs312
      (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hcrl_13c
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
      (by unfold epiloguePre F_nil; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

end Placed

end CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
