/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Assembly
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac
public import LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Binary Refinement for `RatchetState::consume_message_key`

Assembles the budget-threaded placed refinement for `RatchetState::consume_message_key` (Block 24)
under `RustCliAllocBudget M` and `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HMAC (ShaState hmacWith sha256IV)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_73 blkLib_eq_114
  blkPC_24 blkPC_73 blkPl_24 blkPl_73
  extract_withLsCodeLoaded libsignalRoLoaded_of_keepsFrozen
  libsignalSessionExterns libsignalSessionLib
  lsBlackBoxU8Sym lsNoAllocShimSym lsProg_73 lsProg_114 lsRustReallocSym
  ls_externAt?_blockProgram_eq_of_externs_eq ls_subroutine_ok_of_block
  lsmpl withLsCodeLoaded
)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  Frame HmacPlacedPre RunsTo StateH0Placed StateH1Placed StateH5
  disjointRegions_of_ro_rw hmacPlacedSpec hookMemcpy_eq_memcpyHook
  hookMemset_eq_memsetHook length_hmacWith
  lsCompress256Sym lsMemcpySym lsMemsetSym lsSha256IVAddr
  new_from_slice_placed_run rodata_placed_sha256IV
  seg0a_placed_runsTo seg1a_placed_runsTo seg1b_placed_runsTo
  seg2_placed_runsTo seg3_placed_runsTo seg4_placed_runsTo
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (GrowOnePlacedOk hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks FindIndexPlacedOk HmacPlacedOk HmacPlacedRoOk
)
open LibsignalBinary.Proofs.ConsumeMessageKey.RunOfCalleesBudget (
  CmkPlacedRunStmt consume_message_key_placed_ro_run_of consume_message_key_placed_run_of
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (
  hmacExcHooks hmacExcHooks_compress hmacExcHooks_memcpy hmacExcHooks_memset
  hmacPlacedPre_stripS runsTo_block_lift_vm
  stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw
  unstrip_frame
)

private theorem stripS_read64 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by
  cases s
  simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

private theorem stripExecOutside_hmacSt {F : ShaState → List (BitVec 8) → ShaState}
    {p : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} {key msg : List (BitVec 8)} :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
      (ProofLib.stripExecOutside p m) a F key msg ↔
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt m a F key msg := by
  unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
  simp only [stripExecOutside_readBytes, Memory.read64, ProofLib.strip_read8]

private theorem runsTo_73_to_bp [LibsignalPlacement] {X : LibsignalHooks}
    {s : State} {P : State → Prop} (h : RunsTo (lsProg_73 X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 73 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)]

private theorem steps_bp_to_73 [LibsignalPlacement] {X : LibsignalHooks} {s s' : State}
    (h : Steps (libsignalSessionLib.blockProgram lsmpl 73 X) s s') :
    Steps (lsProg_73 X) s s' := by
  rwa [IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)]

private theorem stripS_hmacSaved (p : BitVec 64 → Bool) (s0 s : State) :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSaved
      (ProofLib.stripS p s0)
      (CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp (ProofLib.stripS p s0))
      (ProofLib.stripS p s).mem ↔
    CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSaved
      s0 (CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp s0) s.mem := by
  have hsp0 : CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp (ProofLib.stripS p s0) =
      CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp s0 := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS p s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSaved
  simp only [hsp0, stripS_read64, hr]

private theorem hmac_placed_runsTo_vm [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (hpre : HmacPlacedPre F key [byte] s0)
    (hL73 : (lsProg_73 H).CodeLoaded s0.mem) :
    ∃ sf : State,
      Steps (lsProg_73 H) s0 sf ∧
      VmPreserved s0 sf ∧
      sf.trace = s0.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
      StateH5 F key byte s0 sf := by
  have heq73 : ∀ X, lsProg_73 X = libsignalSessionLib.blockProgram lsmpl 73 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_73 X)
  have heq114 : ∀ X, lsProg_114 X = libsignalSessionLib.blockProgram lsmpl 114 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)
  let Q73 := libsignalSessionLib.blockProgram lsmpl 73 (hmacExcHooks F H)
  let kp73 := ProofLib.progKeep Q73
  have hmcQ := hmacExcHooks_memcpy F H
  have hmsQ := hmacExcHooks_memset F H
  have hc256Q := hmacExcHooks_compress F H
  have hL73_bp : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s0.mem := by
    rwa [← heq73 H]
  obtain ⟨sc, hsteps0a_bp, hvm0a, htr0a, hvregs0a, hsc_or⟩ :=
    runsTo_block_lift_vm h_memcpy h_memset h_compress blkLib_eq_73 rfl rfl hL73_bp
      (runsTo_73_to_bp (seg0a_placed_runsTo (H := H) hpre))
      (runsTo_73_to_bp (seg0a_placed_runsTo (H := hmacExcHooks F H) (hmacPlacedPre_stripS kp73 hpre)))
      (fun _ (hs : StateH0Placed s0 _) => hs.common.1)
      (fun _ (hs : StateH0Placed (ProofLib.stripS kp73 s0) _) => hs.common.1)
  have hsteps0a : Steps (lsProg_73 H) s0 sc := steps_bp_to_73 hsteps0a_bp
  have hsc : StateH0Placed s0 sc := by
    rcases hsc_or with hsc_strip | hsc_real
    · rcases hsc_strip with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
        hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
      have hm0 : (ProofLib.stripS kp73 s0).mem = ProofLib.stripExecOutside kp73 s0.mem := by
        cases s0; rfl
      have hmc : (ProofLib.stripS kp73 sc).mem = ProofLib.stripExecOutside kp73 sc.mem := by
        cases sc; rfl
      rw [hm0, hmc] at hframe_c
      exact ⟨(by cases sc; exact hpc_c),
        ⟨(by cases sc; exact hstat_c),
         (by cases s0; cases sc; exact hsp_c),
         (by cases s0; cases sc; exact hx29_c),
         (by cases s0; cases sc; exact hx27_c),
         (stripS_hmacSaved kp73 s0 sc).mp hsaved_c,
         unstrip_frame hframe_c hvm0a.perm_eq⟩,
        (by cases s0; cases sc; exact hx0_c),
        (by cases s0; cases sc; exact hx1_c),
        (by cases sc; exact hx2_c),
        (by cases sc; exact hlr_c),
        (by cases s0; cases sc; exact hx19_c),
        (by cases s0; cases sc; exact hx20_c),
        (by cases sc; exact hx21_c)⟩
    · exact hsc_real
  have hcl_sc : LibsignalCodeLoaded lsmpl sc.mem := hcl.of_keepsFrozen hsteps0a.keepsFrozen
  have hL114 : (libsignalSessionLib.blockProgram lsmpl 114 H).CodeLoaded sc.mem :=
    hcl_sc 114 (by decide) (by decide) H (fun _ => none) Syscall.standard
  let Q114 := libsignalSessionLib.blockProgram lsmpl 114 (hmacExcHooks F H)
  let kp114 := ProofLib.progKeep Q114
  rcases hsc with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
    hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
  have hal_hsp : (CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp s0 &&& 0b1111#64) = 0#64 :=
    CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp_align hpre.sp_aligned
  have hkey_c : sc.mem.readBytes (sc.readReg64 .x1) (sc.readReg64 .x2).toNat = key := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl,
      hframe_c.readBytes_eq (by simp [hpre.disj_key_stack.symm]) (by decide), hpre.key_eq]
  have hiv_c : sc.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV := by
    rw [hframe_c.readBytes_eq (by simp [hpre.disj_iv_stack.symm]) (by decide), hpre.iv_eq]
  have hread_iv_c : sc.mem.Readable lsSha256IVAddr 32 :=
    (hframe_c.readable_iff _ _).mpr hpre.read_iv
  have hrw_stack_c : CryptoVerification.LibsignalSession.CryptoHmacSha256.RW sc.mem (s0.sp - 1024#64) 1024 :=
    (hframe_c.rw_iff _ _).mpr hpre.rw_stack
  have hdisj_iv_nfs : DisjointRegions lsSha256IVAddr 32 (sc.sp - 544#64) 544 := by
    rw [hsp_c, CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp_sub_544_eq]
    exact hpre.disj_iv_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hrw_out_nfs : CryptoVerification.LibsignalSession.CryptoHmacSha256.RW sc.mem (sc.readReg64 .x0) 0x98 := by
    rw [hx0_c]
    exact hrw_stack_c.sub (by
      clear * -; unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp; bv_omega)
  have hrw_stack_nfs : CryptoVerification.LibsignalSession.CryptoHmacSha256.RW sc.mem (sc.sp - 544#64) 544 := by
    rw [hsp_c, CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp_sub_544_eq]
    exact hrw_stack_c.sub (by clear * -; bv_omega)
  have hdisj_out_nfs : DisjointRegions (sc.readReg64 .x0) 0x98 (sc.sp - 544#64) 544 := by
    rw [hx0_c, hsp_c]
    clear * -; unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp DisjointRegions; bv_omega
  have hdisj_key_nfs : DisjointRegions (sc.readReg64 .x1) (sc.readReg64 .x2).toNat (sc.sp - 544#64) 544 := by
    rw [hx1_c, hx2_c, hsp_c, CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp_sub_544_eq,
      show (32#64 : BitVec 64).toNat = 32 from rfl]
    exact hpre.disj_key_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hm_sc_114 : (ProofLib.stripS kp114 sc).mem = ProofLib.stripExecOutside kp114 sc.mem := by
    cases sc; rfl
  have hruns_nfs_P := new_from_slice_placed_run (s₀ := sc) h_memcpy h_compress
    hpc_c hstat_c (by rw [hx2_c]; decide) hiv_c hread_iv_c hdisj_iv_nfs
    hrw_out_nfs hrw_stack_nfs hdisj_out_nfs (Or.inr hdisj_key_nfs)
    (by rw [hsp_c]; exact hal_hsp)
  have hruns_nfs := new_from_slice_placed_run (s₀ := ProofLib.stripS kp114 sc) hmcQ hc256Q
    (by cases sc; exact hpc_c)
    (by cases sc; exact hstat_c)
    (by have hr : (ProofLib.stripS kp114 sc).readReg64 .x2 = sc.readReg64 .x2 := by cases sc; rfl
        rw [hr, hx2_c]; decide)
    (by rw [hm_sc_114, stripExecOutside_readBytes]; exact hiv_c)
    (by rw [hm_sc_114]; exact stripExecOutside_readable kp114 sc.mem _ _ hread_iv_c)
    (by have hs : (ProofLib.stripS kp114 sc).sp = sc.sp := by cases sc; rfl
        rwa [hs])
    (by have hr : (ProofLib.stripS kp114 sc).readReg64 .x0 = sc.readReg64 .x0 := by cases sc; rfl
        rw [hm_sc_114, hr]; exact stripExecOutside_rw kp114 sc.mem _ _ hrw_out_nfs)
    (by have hs : (ProofLib.stripS kp114 sc).sp = sc.sp := by cases sc; rfl
        rw [hm_sc_114, hs]; exact stripExecOutside_rw kp114 sc.mem _ _ hrw_stack_nfs)
    (by have hr : (ProofLib.stripS kp114 sc).readReg64 .x0 = sc.readReg64 .x0 := by cases sc; rfl
        have hs : (ProofLib.stripS kp114 sc).sp = sc.sp := by cases sc; rfl
        rwa [hr, hs])
    (Or.inr (by
      have hr1 : (ProofLib.stripS kp114 sc).readReg64 .x1 = sc.readReg64 .x1 := by cases sc; rfl
      have hr2 : (ProofLib.stripS kp114 sc).readReg64 .x2 = sc.readReg64 .x2 := by cases sc; rfl
      have hs : (ProofLib.stripS kp114 sc).sp = sc.sp := by cases sc; rfl
      rwa [hr1, hr2, hs]))
    (by have hs : (ProofLib.stripS kp114 sc).sp = sc.sp := by cases sc; rfl
        rw [hs, hsp_c]; exact hal_hsp)
  obtain ⟨s1, hsteps114, hvm0b, htr0b, hvregs0b, hs1_or⟩ :=
    runsTo_block_lift_vm h_memcpy h_memset h_compress blkLib_eq_114 rfl rfl hL114
      (heq114 H ▸ hruns_nfs_P) (heq114 _ ▸ hruns_nfs)
      (fun _ hs => hs.2.1)
      (fun _ hs => hs.2.1)
  have hext_114_73 : ∀ pc, (libsignalSessionLib.blockProgram lsmpl 114 H).externAt? pc =
      (lsProg_73 H).externAt? pc := fun pc => by
    have he114 : (libsignalSessionLib.blockLib 114).text.externs = libsignalSessionExterns :=
      IsLsBlockProg.externs_eq (prog := lsProg_114 H)
    have he73 : (libsignalSessionLib.blockLib 73).text.externs = libsignalSessionExterns :=
      IsLsBlockProg.externs_eq (prog := lsProg_73 H)
    rw [heq73 H, ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
      (he114.trans he73.symm)]
  have hsteps0b : Steps (lsProg_73 H) sc s1 :=
    Steps.of_sameHooks hext_114_73 (by rw [heq73 H]; rfl) hsteps114
  have hs1_raw : s1.pc = sc.readReg64 .lr ∧ s1.status = .Running ∧
      CryptoVerification.LibsignalSession.CryptoHmacSha256.CalleeSaved sc s1 ∧
      s1.mem.read64 (sc.readReg64 .x0) = 0#64 ∧
      CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt s1.mem (sc.readReg64 .x0 + 8#64)
        F (sc.mem.readBytes (sc.readReg64 .x1) (sc.readReg64 .x2).toNat) [] ∧
      Frame sc.mem s1.mem [(sc.readReg64 .x0, 0x98), (sc.sp - 544#64, 544)] := by
    rcases hs1_or with hs1_strip | hs1_real
    · rcases hs1_strip with ⟨hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩
      have hm_s1_114 : (ProofLib.stripS kp114 s1).mem = ProofLib.stripExecOutside kp114 s1.mem := by
        cases s1; rfl
      have hr_sc0 : (ProofLib.stripS kp114 sc).readReg64 .x0 = sc.readReg64 .x0 := by cases sc; rfl
      have hr_sc1 : (ProofLib.stripS kp114 sc).readReg64 .x1 = sc.readReg64 .x1 := by cases sc; rfl
      have hr_sc2 : (ProofLib.stripS kp114 sc).readReg64 .x2 = sc.readReg64 .x2 := by cases sc; rfl
      have hr_sclr : (ProofLib.stripS kp114 sc).readReg64 .lr = sc.readReg64 .lr := by cases sc; rfl
      have hsp_sc114 : (ProofLib.stripS kp114 sc).sp = sc.sp := by cases sc; rfl
      rw [hm_sc_114, hm_s1_114, hr_sc0, hsp_sc114] at hframe1
      rw [hm_sc_114, hm_s1_114, hr_sc0, hr_sc1, hr_sc2, stripExecOutside_readBytes] at hhmac1
      exact ⟨(by rw [hr_sclr] at hpc1; cases s1; exact hpc1),
        (by cases s1; exact hstat1),
        ⟨by cases sc; cases s1; exact hcs1.1, fun r hr => by have := hcs1.2 r hr; cases sc; cases s1; exact this⟩,
        (by rw [hr_sc0, stripS_read64] at htag1; exact htag1),
        stripExecOutside_hmacSt.mp hhmac1,
        unstrip_frame hframe1 hvm0b.perm_eq⟩
    · exact hs1_real
  have hs1_real_st : StateH1Placed F key s0 s1 := by
    rcases hs1_raw with ⟨hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩
    rw [hlr_c] at hpc1; rw [hx0_c] at htag1 hhmac1 hframe1; rw [hsp_c] at hframe1; rw [hkey_c] at hhmac1
    have hhmac_addr : CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp s0 + 144#64 + 8#64 =
        CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp s0 + 152#64 := by clear * -; bv_omega
    rw [hhmac_addr] at hhmac1
    exact ⟨hpc1, ⟨hstat1, hcs1.1.trans hsp_c, (hcs1.2 .x29 (by simp)).trans hx29_c,
      (hcs1.2 .x27 (by simp)).trans hx27_c,
      CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSaved.of_frame hsaved_c hframe1 (by
        intro r hr; clear * - hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;>
          (unfold CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp DisjointRegions; bv_omega)),
      CryptoVerification.LibsignalSession.CryptoHmacSha256.Frame.trans_nfs hframe_c hframe1⟩,
      (hcs1.2 .x19 (by simp)).trans hx19_c, (hcs1.2 .x20 (by simp)).trans hx20_c,
      (hcs1.2 .x21 (by simp)).trans hx21_c, htag1, hhmac1⟩
  have hs1 : StateH1Placed F key (ProofLib.stripS kp73 s0) (ProofLib.stripS kp73 s1) := by
    rcases hs1_real_st with ⟨hpc1, ⟨hstat1, hsp1, hx29_1, hx27_1, hsaved1, hframe01⟩,
      hx19_1, hx20_1, hx21_1, htag1, hhmac1⟩
    have hframe01_73 : Frame (ProofLib.stripS kp73 s0).mem (ProofLib.stripS kp73 s1).mem
        [((ProofLib.stripS kp73 s0).sp - 1024#64, 1024)] := by
      have hm0 : (ProofLib.stripS kp73 s0).mem = ProofLib.stripExecOutside kp73 s0.mem := by cases s0; rfl
      have hm1 : (ProofLib.stripS kp73 s1).mem = ProofLib.stripExecOutside kp73 s1.mem := by cases s1; rfl
      have hs0 : (ProofLib.stripS kp73 s0).sp = s0.sp := by cases s0; rfl
      rw [hm0, hm1, hs0]
      exact ⟨fun a hout => by simpa only [ProofLib.strip_read8] using hframe01.1 a hout,
        funext fun a => by simp [ProofLib.strip_perm, (hvm0a.trans hvm0b).perm_eq a],
        fun a hout => by simpa only [ProofLib.strip_isLazyFree] using hframe01.2.2.1 a hout,
        fun a hlf => by
          simpa only [ProofLib.strip_isLazyFree] using
            hframe01.2.2.2.1 a (by simpa only [ProofLib.strip_isLazyFree] using hlf),
        fun a han => by
          simpa only [ProofLib.strip_isAnon] using
            hframe01.2.2.2.2 a (by simpa only [ProofLib.strip_isAnon] using han)⟩
    have htag1_73 : (ProofLib.stripS kp73 s1).mem.read64
        (CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp (ProofLib.stripS kp73 s0) + 144#64) = 0#64 := by
      have hsp0 : CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp (ProofLib.stripS kp73 s0) =
          CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp s0 := by cases s0; rfl
      rw [hsp0, stripS_read64]; exact htag1
    have hhmac1_73 : CryptoVerification.LibsignalSession.CryptoHmacSha256.HmacSt
        (ProofLib.stripS kp73 s1).mem
        (CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp (ProofLib.stripS kp73 s0) + 152#64)
        F key [] := by
      have hsp0 : CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp (ProofLib.stripS kp73 s0) =
          CryptoVerification.LibsignalSession.CryptoHmacSha256.hsp s0 := by cases s0; rfl
      have hm_73 : (ProofLib.stripS kp73 s1).mem = ProofLib.stripExecOutside kp73 s1.mem := by
        cases s1; rfl
      rw [hm_73, hsp0]
      exact stripExecOutside_hmacSt.mpr hhmac1
    exact ⟨(by cases s1; exact hpc1),
      ⟨(by cases s1; exact hstat1),
       (by cases s0; cases s1; exact hsp1),
       (by cases s0; cases s1; exact hx29_1),
       (by cases s0; cases s1; exact hx27_1),
       (stripS_hmacSaved kp73 s0 s1).mpr hsaved1, hframe01_73⟩,
      (by cases s0; cases s1; exact hx19_1),
      (by cases s0; cases s1; exact hx20_1),
      (by cases s1; exact hx21_1),
      htag1_73, hhmac1_73⟩
  have hpre73 := hmacPlacedPre_stripS kp73 hpre
  have hL73_s1 : (libsignalSessionLib.blockProgram lsmpl 73 H).CodeLoaded s1.mem := by
    rw [← heq73 H]; exact (hsteps0a.trans hsteps0b).codeLoaded hL73
  have hruns_tail_P : RunsTo (libsignalSessionLib.blockProgram lsmpl 73 H) s1
      (StateH5 F key byte s0) :=
    runsTo_73_to_bp (
      (seg1a_placed_runsTo hpre hs1_real_st).trans fun _ h1m =>
      (seg1b_placed_runsTo h_memcpy h_memset hpre h1m).trans fun _ h2 =>
      (seg2_placed_runsTo h_compress hpre h2).trans fun _ h3 =>
      (seg3_placed_runsTo h_compress hpre h3).trans fun _ h4 =>
      seg4_placed_runsTo hpre h4)
  have hruns_tail : RunsTo Q73 (ProofLib.stripS kp73 s1)
      (StateH5 F key byte (ProofLib.stripS kp73 s0)) :=
    runsTo_73_to_bp (
      (seg1a_placed_runsTo hpre73 hs1).trans fun _ h1m =>
      (seg1b_placed_runsTo hmcQ hmsQ hpre73 h1m).trans fun _ h2 =>
      (seg2_placed_runsTo hc256Q hpre73 h2).trans fun _ h3 =>
      (seg3_placed_runsTo hc256Q hpre73 h3).trans fun _ h4 =>
      seg4_placed_runsTo hpre73 h4)
  obtain ⟨sf, hsteps_tail_bp, hvm_tail, htr_tail, hvregs_tail, h5_or⟩ :=
    runsTo_block_lift_vm h_memcpy h_memset h_compress blkLib_eq_73 rfl rfl hL73_s1
      hruns_tail_P hruns_tail
      (fun _ hs => hs.status)
      (fun _ hs => hs.status)
  have hsteps_tail : Steps (lsProg_73 H) s1 sf := steps_bp_to_73 hsteps_tail_bp
  have hvm_all : VmPreserved s0 sf := (hvm0a.trans hvm0b).trans hvm_tail
  have h5_final : StateH5 F key byte s0 sf := by
    rcases h5_or with h5_strip | h5_real
    · rcases h5_strip with ⟨hpc_sf, hstat_sf, hcs_sf, hout_sf, hframe_sf⟩
      have hm0_73 : (ProofLib.stripS kp73 s0).mem = ProofLib.stripExecOutside kp73 s0.mem := by
        cases s0; rfl
      have hmf_73 : (ProofLib.stripS kp73 sf).mem = ProofLib.stripExecOutside kp73 sf.mem := by
        cases sf; rfl
      have hr0_73 : (ProofLib.stripS kp73 s0).readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
      have hs0_73 : (ProofLib.stripS kp73 s0).sp = s0.sp := by cases s0; rfl
      rw [hm0_73, hmf_73, hr0_73, hs0_73] at hframe_sf
      rw [hmf_73, hr0_73, stripExecOutside_readBytes] at hout_sf
      have hcs_u : CryptoVerification.LibsignalSession.CryptoHmacSha256.CalleeSaved s0 sf := by
        refine ⟨by cases s0; cases sf; exact hcs_sf.1, fun r hr => ?_⟩
        have := hcs_sf.2 r hr
        cases s0; cases sf; exact this
      exact ⟨by cases s0; cases sf; exact hpc_sf,
       by cases sf; exact hstat_sf,
       hcs_u, hout_sf, unstrip_frame hframe_sf hvm_all.perm_eq⟩
    · exact h5_real
  exact ⟨sf, (hsteps0a.trans hsteps0b).trans hsteps_tail, hvm_all,
    htr_tail.trans (htr0b.trans htr0a),
    hvregs_tail.trans (hvregs0b.trans hvregs0a),
    h5_final⟩

/-- `VmPreserved`-strengthened `hmac_sha256` contract on Block 73. -/
theorem hmac_sha256_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H lsMemcpySym = some hookMemcpy)
    (h_ms : H lsMemsetSym = some hookMemset)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl (withVmPreserved (hmacPlacedSpec F))) := by
  have h_mc' : H lsMemcpySym = some memcpyHook := hookMemcpy_eq_memcpyHook ▸ h_mc
  have h_ms' : H lsMemsetSym = some memsetHook := hookMemset_eq_memsetHook ▸ h_ms
  refine subroutine_ok_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  rw [withVmPreserved, hmacPlacedSpec] at hpre
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hkey_len, hinp_len, hro⟩, hsep⟩
  rcases inp with _ | ⟨byte, _ | _⟩ <;> try { simp at hinp_len }
  have hx2 : s0.readReg64 .x2 = 32#64 := by
    apply BitVec.eq_of_toNat_eq; simp [hx2_nat, hkey_len]
  have hx4 : s0.readReg64 .x4 = 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp at hx4_nat; simp [hx4_nat]
  have hsp_split : stackAt s0.sp 2048 =
      memRegion (s0.sp - 2048#64) 1024 ∗ memRegion (s0.sp - 1024#64) 1024 :=
    stackAt_split_bottom s0.sp 1024 1024 (by decide)
  rw [hsp_split] at hsep
  have hb_out := IsBlock.memRegion out 32
  have hb_key := IsBlock.pointsToBytes_len (a := ka) hkey_len
  have hb_inp := IsBlock.pointsToBytes_len (a := ia) (rfl : [byte].length = 1)
  have hb_stk := IsBlock.memRegion (s0.sp - 1024#64) 1024
  have hsep_key : s0.mem ⊨ (ka ↦ₛ key) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_inp : s0.mem ⊨ (ia ↦ₛ [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_out : s0.mem ⊨ memRegion out 32 ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hsep
  have hkey_eq : s0.mem.readBytes ka 32 = key := by
    have h := (hb_key.read hsep_key).2
    rwa [hkey_len] at h
  have hinp_eq : s0.mem.readBytes ia 1 = [byte] :=
    (hb_inp.read hsep_inp).2
  have hrw_out : CryptoVerification.LibsignalSession.CryptoHmacSha256.RW s0.mem out 32 :=
    fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : CryptoVerification.LibsignalSession.CryptoHmacSha256.RW s0.mem (s0.sp - 1024#64) 1024 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_inp : s0.mem.Readable ia 1 :=
    Memory.RW.readable (fun a ha => hb_inp.permNoLazy_rw hsep_inp ha)
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hpre_hmac : HmacPlacedPre F key [byte] s0 := {
    pc_eq := hpc
    status := hrun
    sp_aligned := by simpa [State.spAligned] using hsp
    x2_eq := hx2
    x4_eq := hx4
    key_len := hkey_len
    inp_len := rfl
    key_eq := by rw [hx1]; exact hkey_eq
    inp_eq := by rw [hx3]; exact hinp_eq
    iv_eq := hiv_eq
    read_iv := hread_iv
    read_inp := by rw [hx3]; exact hread_inp
    rw_out := by rw [hx0]; exact hrw_out
    rw_stack := hrw_stk
    disj_iv_stack := disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
    disj_out_stack := by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
    disj_key_stack := by rw [hx1]; exact hb_key.disjoint hb_stk (by decide) (by decide) hsep_key
    disj_inp_stack := by rw [hx3]; exact hb_inp.disjoint hb_stk (by simp) (by decide) hsep_inp
  }
  intro hL73
  obtain ⟨sf, hsteps, hvm, htr, hvregs, hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩ :=
    hmac_placed_runsTo_vm h_mc' h_ms' h_c256 hcl hpre_hmac hL73
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CryptoVerification.LibsignalSession.CryptoHmacSha256.CallingConventionPreserved_of_calleeSaved
      hcallee hvregs⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htr, libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen⟩, ?_⟩
  rw [hsp_split]
  have hb_out' := IsBlock.pointsToBytes_len (a := out) (length_hmacWith F key [byte])
  rw [hx0] at hout_sf hframe_sf
  have hpost_sep : sf.mem ⊨ (out ↦ₛ hmacWith F key [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    CryptoVerification.LibsignalSession.CryptoHmacSha256.Frame.update_two_blocks
      hb_out hb_out' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_sep

/-- `VmPreserved`-strengthened `hmac_sha256` contract on Block 73 backed by `LibsignalRoLoaded`. -/
theorem hmac_sha256_placed_ro_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H lsMemcpySym = some hookMemcpy)
    (h_ms : H lsMemsetSym = some hookMemset)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) := by
  refine subroutine_ok_mono (hmac_sha256_placed_ok F h_mc h_ms h_c256)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 hp => ?_)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 sf hq => ?_)
  · have ⟨hcl, hp'⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec, hmacSpec,
      CryptoVerification.LibsignalSession.hmacSpec] at hp' ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp' ⊢
    rcases hp' with ⟨hro, hp''⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp''
    rcases hp'' with ⟨hpure, hsep⟩
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1, hpure.2.2.2.2.1,
      hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2, hro⟩, hsep⟩
  · dsimp only [withLsCodeLoaded, withVmPreserved, hmacPlacedSpec, hmacSpec,
      CryptoVerification.LibsignalSession.hmacSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq' := hq.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq' ⊢
    exact ⟨hq'.1.1, hq'.2⟩

/-! ## Callee Lifts and Top-Level `consume_message_key` Assembly -/

theorem find_receiver_chain_index_placed_ok_at_cmk [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    FindIndexPlacedOk H A :=
  FindIndexBudget.find_receiver_chain_index_placed_ok_at_cmk A h_bb

theorem grow_one_placed_ok_at_cmk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    GrowOnePlacedOk H A lim :=
  GrowOneBudget.grow_one_placed_ok_at_cmk hA h_realloc

theorem grow_one_placed_ok_of_noop_at_cmk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hA : CmkAllocHooks A lim H) :
    GrowOnePlacedOk H A lim :=
  ls_subroutine_ok_of_block (callerProg := (blkPC_24).rebase (blkPl_24).base H)
    (GrowOneBudget.grow_one_placed_ok_of_noop h_shim hA.1 h_realloc)

theorem hmac_sha256_placed_ro_ok_at_cmk [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H lsMemcpySym = some hookMemcpy)
    (h_ms : H lsMemsetSym = some hookMemset)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    HmacPlacedRoOk H F :=
  ls_subroutine_ok_of_block (i := 24) (j := 73) (hmac_sha256_placed_ro_ok F h_mc h_ms h_c256)

/-- Budget-threaded placed refinement for `consume_message_key` (`HookSat` allocator shim). -/
theorem consume_message_key_placed_run_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hhmac : HmacPlacedOk H F) :
    CmkPlacedRunStmt F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_run_of F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk A h_bb)
    hhmac
    (grow_one_placed_ok_at_cmk hA h_realloc) hA hmm

/-- Budget-threaded placed refinement for `consume_message_key` (`hookNoop` allocator shim). -/
theorem consume_message_key_placed_run [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hhmac : HmacPlacedOk H F) :
    CmkPlacedRunStmt F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_run_of F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk A h_bb)
    hhmac
    (grow_one_placed_ok_of_noop_at_cmk h_shim h_realloc hA) hA hmm

/-- `.rodata`-backed budget-threaded placed refinement for `consume_message_key` (`HookSat` shim). -/
theorem consume_message_key_placed_ro_run_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : H lsMemcpySym = some hookMemcpy)
    (h_ms : H lsMemsetSym = some hookMemset)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    CmkPlacedRunStmt F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk F h_mc h_ms h_c256)
    (grow_one_placed_ok_at_cmk hA h_realloc) hA hmm

/-- `.rodata`-backed budget-threaded placed refinement for `consume_message_key` (`hookNoop` shim). -/
theorem consume_message_key_placed_ro_run [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : H lsNoAllocShimSym = some hookNoop)
    (h_realloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (h_mc : H lsMemcpySym = some hookMemcpy)
    (h_ms : H lsMemsetSym = some hookMemset)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    CmkPlacedRunStmt F A lim H := by
  intro hA hmm
  exact consume_message_key_placed_ro_run_of F A lim H
    (find_receiver_chain_index_placed_ok_at_cmk A h_bb)
    (hmac_sha256_placed_ro_ok_at_cmk F h_mc h_ms h_c256)
    (grow_one_placed_ok_of_noop_at_cmk h_shim h_realloc hA) hA hmm

end LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudget
