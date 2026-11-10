/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import ProofLib.OpcodeExclusion
import VerifiedLibraries.RustStd.Proofs.ExecSegSym

/-!
# Budget-Threaded Placed Contracts for `spqr::kdf::hkdf_to_slice` and `hkdf_to_vec`

Relocatable `[LibsignalPlacement]` separation-logic contracts for Block `379` (`hkdf_to_slice`,
preserving `VmPreserved`) and Block `378` (`hkdf_to_vec`, threading `RustCliAllocBudget`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudget

open Arm64 ProofLib
open CryptoGames.HMAC (hmacWith sha256IV)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_379 blkLib_402 blkLib_425 blkLib_eq_379 blkLib_eq_402 blkLib_eq_425
   blkPC_378 blkPl_378 blkPC_379 blkPl_379 blkPC_402 blkPl_402 blkPC_425 blkPl_425
   libsignalMutatedBlocks libsignalSessionLib
   ls_externAt?_blockProgram_eq_of_externs_eq lsmpl prog_eq_blockProgram)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HkdfPlacedHooks
   LibsignalCodeRoLoaded RunsTo TraceEq
   extHookStack extract_withLsCodeRoLoaded
   keys_ls_subroutine_ok_of_block_cro lsCompress256Sym lsMemcpySym lsMemsetSym
   noAllocShimSpec ro_outside_rw_shared_lb withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (KeepsFrozenNoAnon t1_length t2_length t3_length)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf
  (FinPre3 FinPre3Pfx FinPre3PfxGen
   effectiveHmacKey effectiveHmacKey_length_le fin3PlacedFakeB fin3PlacedFakeB_off_0
   hmacWith_effectiveHmacKey new_from_slice3_gen_placed_runsTo spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Kdf.FinalizeFixed3GenProof
  (finalize_fixed3_pfx_lt64_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.FinalizeFixed3Proof
  (finalize_fixed3_placed_runsTo finalize_fixed3_pfx_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HPost HPre Nfs3GenRunsToProg
   StateB1Done StateB1Fin StateB1RetFin
   StateEFin StateERetFin StateExtractDone StateLoop StateLoopC StateLoopFin
   b1_done_32_placed_runsTo b1_to_loop_placed_runsTo
   epilogue_placed_runsTo hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_64_eq hkdfExpand_96_eq
   hsp hsp_aligned iter_a1_placed_runsTo iter_a2_placed_runsTo iter_b_placed_runsTo
   iter_d_continue_placed_runsTo iter_d_done_placed_runsTo
   nfs1_runsTo nfs2_runsTo rodata_sha256IV_placed
   seg_b1a_placed_runsTo seg_b1b_placed_runsTo seg_b1d_placed_runsTo
   seg_e0_placed_runsTo seg_e1_placed_runsTo seg_e1d_placed_runsTo
   seg_e2_placed_runsTo seg_e3_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (nfs3PlacedFakeB nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (disjointRegions_of_ro_rw length_hmacWith)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
  (hkdfToVecSpec hkdf_to_vec_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (calleeSavedPreserved_of_stripS_right checkBlockSafeVm
   placedLib_rebase_allInstrs_safeVm stripS_calleeSavedVRegs
   stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace vmTrapHooks)

private theorem findSome?_symbols_none {α : Type} :
    ∀ (syms : List (String × Nat)) {off : Nat},
      (syms.findSome? fun x => if x.2 == off then (none : Option α) else none) = none
  | [], _ => rfl
  | _ :: rest, _ => by
    rw [List.findSome?_cons, ite_self]
    exact findSome?_symbols_none rest

private theorem bytesAt_read {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64)
    (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.readBytes p bs.length = bs := by
  cases ro
  · exact ((IsBlock.pointsToBytes p bs).read hsep).2
  · exact (IsBlockRO.pointsToBytesRO p bs hle).read hsep

private theorem bytesAt_outside_rw {ro : Bool} {p b_rw : BitVec 64} {bs : List (BitVec 8)}
    {n_rw : Nat} {Q R : SepProp} {Φ_rw : Memory → Prop} {m : Memory}
    (hle : bs.length ≤ 2 ^ 64) (hrw_pos : 0 < n_rw)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ bytesAt ro p bs ∗ (Q ∗ R)) :
    ∀ a, InRegion p bs.length a → OutsideRegion b_rw n_rw a := by
  cases ro
  · intro a ha
    have hpos : 0 < bs.length := by unfold InRegion at ha; omega
    have hd := (IsBlock.pointsToBytes p bs).disjoint hrw hpos hrw_pos hsep
    unfold DisjointRegions at hd
    unfold InRegion at ha
    unfold OutsideRegion
    bv_omega
  · exact ro_outside_rw_shared_lb (IsBlockRO.pointsToBytesRO p bs hle) hrw hsep

private theorem stackAt_hkdfToSlice (s₀ : State) :
    stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ memRegion (hsp s₀ - 544#64) 1232 := by
  have h1 : stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ stackAt s₀.sp 1232 :=
    ProofLib.stackAt_split_bottom s₀.sp 1232 15152 (by decide)
  have h2 : stackAt s₀.sp 1232 = memRegion (hsp s₀ - 544#64) 1232 := by
    simp only [stackAt, hsp]
    congr 1
    bv_lin
  rw [h1, h2]

private def kdfOnlyHooks (H : LibsignalHooks) : LibsignalHooks :=
  fun n =>
    if n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym then H n
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

private instance instHkdfPlacedHooks_kdfOnly (C : Crypto) {H : LibsignalHooks}
    [hH : HkdfPlacedHooks C.F H] : HkdfPlacedHooks C.F (kdfOnlyHooks H) where
  memset := by simp [kdfOnlyHooks, hH.memset]
  memcpy := by simp [kdfOnlyHooks, hH.memcpy]
  compress256 := by simp [kdfOnlyHooks, hH.compress256]

private theorem blk379_safeVm : checkBlockSafeVm blkLib_379.text = true := by decide +kernel
private theorem blk402_safeVm : checkBlockSafeVm blkLib_402.text = true := by decide +kernel
private theorem blk425_safeVm : checkBlockSafeVm blkLib_425.text = true := by decide +kernel

private noncomputable def keepKdf [LibsignalPlacement] (a : BitVec 64) : Bool :=
  ProofLib.progKeep ((blkPC_379).rebase (blkPl_379).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_402).rebase (blkPl_402).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_425).rebase (blkPl_425).base vmTrapHooks) a

private def KdfCodeLoaded [LibsignalPlacement] (m : Memory) : Prop :=
  ∀ (H : LibsignalHooks),
    ((blkPC_379).rebase (blkPl_379).base H).CodeLoaded m ∧
    ((blkPC_402).rebase (blkPl_402).base H).CodeLoaded m ∧
    ((blkPC_425).rebase (blkPl_425).base H).CodeLoaded m

private theorem KdfCodeLoaded.of_keepsFrozenNoAnon [LibsignalPlacement] {m m' : Memory}
    (hcl : KdfCodeLoaded m) (hk : KeepsFrozenNoAnon m m') : KdfCodeLoaded m' :=
  fun H =>
    let ⟨h1, h2, h3⟩ := hcl H
    ⟨CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h1 hk,
     CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h2 hk,
     CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h3 hk⟩

private theorem KdfCodeLoaded.of_keepsFrozen [LibsignalPlacement] {m m' : Memory}
    (hcl : KdfCodeLoaded m) (hk : m.KeepsFrozen m') : KdfCodeLoaded m' :=
  fun H =>
    let ⟨h1, h2, h3⟩ := hcl H
    ⟨h1.of_keepsFrozen hk, h2.of_keepsFrozen hk, h3.of_keepsFrozen hk⟩

private theorem strip_codeLoaded_of_keep_sub {R : Program} {keep : BitVec 64 → Bool} {m : Memory}
    (hsub : ∀ a, ProofLib.progKeep R a = true → keep a = true)
    (hL : R.CodeLoaded m) : R.CodeLoaded (ProofLib.stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub_add : R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : keep (R.base + BitVec.ofNat 64 i) = true := by
    apply hsub
    unfold ProofLib.progKeep
    rw [hsub_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem kdfCodeLoaded_of_ls [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) : KdfCodeLoaded m := by
  intro H
  have hI379 : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hI402 : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base H) 402 H := inferInstance
  have hI425 : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base H) 425 H := inferInstance
  exact ⟨hI379.eq_blockProgram ▸ hcl 379 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI402.eq_blockProgram ▸ hcl 402 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI425.eq_blockProgram ▸ hcl 425 (by decide) (by decide) H (fun _ => none) Syscall.standard⟩

private theorem kdfCodeLoaded_strip [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) :
    KdfCodeLoaded (ProofLib.stripExecOutside keepKdf m) := by
  intro H
  have hI379 : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hI402 : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base H) 402 H := inferInstance
  have hI425 : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base H) 425 H := inferInstance
  have hL379 : ((blkPC_379).rebase (blkPl_379).base H).CodeLoaded m :=
    hI379.eq_blockProgram ▸ hcl 379 (by decide) (by decide) H (fun _ => none) Syscall.standard
  have hL402 : ((blkPC_402).rebase (blkPl_402).base H).CodeLoaded m :=
    hI402.eq_blockProgram ▸ hcl 402 (by decide) (by decide) H (fun _ => none) Syscall.standard
  have hL425 : ((blkPC_425).rebase (blkPl_425).base H).CodeLoaded m :=
    hI425.eq_blockProgram ▸ hcl 425 (by decide) (by decide) H (fun _ => none) Syscall.standard
  refine ⟨strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL379,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL402,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL425⟩
  · have ha' : ProofLib.progKeep ((blkPC_379).rebase (blkPl_379).base vmTrapHooks) a = true := ha
    simp [keepKdf, ha']
  · have ha' : ProofLib.progKeep ((blkPC_402).rebase (blkPl_402).base vmTrapHooks) a = true := ha
    simp [keepKdf, ha']
  · have ha' : ProofLib.progKeep ((blkPC_425).rebase (blkPl_425).base vmTrapHooks) a = true := ha
    simp [keepKdf, ha']

private theorem runsTo_of_kdf_402 [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {P_post : State → Prop}
    (hcl : KdfCodeLoaded s.mem)
    (h : RunsTo ((blkPC_402).rebase (blkPl_402).base H) s P_post) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s P_post := by
  intro hL_caller
  have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base H) 402 H := inferInstance
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h (hcl H).2.1
  have hext : ∀ pc, ((blkPC_402).rebase (blkPl_402).base H).externAt? pc =
      ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : ((blkPC_402).rebase (blkPl_402).base H).svc =
      ((blkPC_379).rebase (blkPl_379).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

private theorem runsTo_of_kdf_425 [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {P_post : State → Prop}
    (hcl : KdfCodeLoaded s.mem)
    (h : RunsTo ((blkPC_425).rebase (blkPl_425).base H) s P_post) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s P_post := by
  intro hL_caller
  have hcaller : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base H) 379 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base H) 425 H := inferInstance
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h (hcl H).2.2
  have hext : ∀ pc, ((blkPC_425).rebase (blkPl_425).base H).externAt? pc =
      ((blkPC_379).rebase (blkPl_379).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : ((blkPC_425).rebase (blkPl_425).base H).svc =
      ((blkPC_379).rebase (blkPl_379).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

private theorem fin_extract_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : Nat} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (KdfCodeLoaded s₀.mem))
    (hx : StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, _hmod, hlt, hhm⟩
  have hrw_hsp := HFrame.rw_hsp hpre hx.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.common.frame
  have hfin_pre : FinPre3PfxGen fin3PlacedFakeB C.F (effectiveHmacKey C.F salt) pfx tail s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.common.status
      key_le := effectiveHmacKey_length_le C.F salt
      tail_lt := hlt
      hmac_st := by rw [hx.x1_eq]; exact hhm
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sub.sub (by bv_omega)
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned := by rw [hx.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : KdfCodeLoaded s.mem :=
    hpre.base_al.of_keepsFrozenNoAnon (HFrame.keepsFrozen hpre hx.common.frame)
  refine (runsTo_of_kdf_425 hcl_s
    (finalize_fixed3_pfx_lt64_placed_runsTo (C := C) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hpt, hmacWith_effectiveHmacKey] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (CryptoVerification.LibsignalTripleRatchet.Expand.Frame.read64_eq hfr fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  exact ⟨hpc', HCommon.of_fin_frame (outOff := 507#64) hx.common hrun' hcs hfr (by decide),
    (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', hout⟩

private theorem fin_b1_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : Nat} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (KdfCodeLoaded s₀.mem))
    (hx : StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3 fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm) (info ++ [1#8]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.exp.common.status
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide
      msg_lt := by have := hpre.info_lt; simp; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega)
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : KdfCodeLoaded s.mem :=
    hpre.base_al.of_keepsFrozenNoAnon (HFrame.keepsFrozen hpre hx.exp.common.frame)
  refine (runsTo_of_kdf_425 hcl_s
    (finalize_fixed3_placed_runsTo (C := C) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x21 hcs).trans hx.x21_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, ht1⟩

private theorem iter_fin_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {b_iv : BitVec 64} {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : Nat} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv
      (KdfCodeLoaded s₀.mem))
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have : HkdfPlacedHooks C.F H :=
    { memset := h_memset, memcpy := h_memcpy, compress256 := h_compress }
  have hrw_hsp := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_sub := HFrame.rw_sub_544 hpre hx.exp.common.frame
  have hfin_pre : FinPre3Pfx fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq
      status := hx.exp.common.status
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide
      tail_lt := by have := hpre.info_lt; simp; omega
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32
      rw_out := by rw [hx.x0_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_hm := by rw [hx.x1_eq]; exact hrw_hsp.sub (by bv_omega)
      rw_fsp := by rw [hx.exp.common.sp_eq]; exact hrw_sub.sub (by bv_omega)
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; unfold DisjointRegions; bv_omega
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq]; unfold DisjointRegions; bv_omega
      sp_aligned := by rw [hx.exp.common.sp_eq]; exact (hsp_aligned hpre.sp_aligned).2.1 }
  have hcl_s : KdfCodeLoaded s.mem :=
    hpre.base_al.of_keepsFrozenNoAnon (HFrame.keepsFrozen hpre hx.exp.common.frame)
  refine (runsTo_of_kdf_425 hcl_s
    (finalize_fixed3_pfx_placed_runsTo (C := C) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32),
      List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hokm_len := hpre.okm_len
      refine (CryptoVerification.LibsignalTripleRatchet.Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by bv_omega⟩
      · exact (hpre.disj_okm_stk.symm.sub_left (hsp s₀ - 144#64) ⟨by decide, by bv_omega⟩).sub_right
          okmA ⟨by omega, by bv_omega⟩
  exact ⟨hpc', HExpCommon.of_fin_frame hx.exp hrun' hcs hfr,
    (CalleeSaved.x20 hcs).trans hx.x20_eq, (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, hout, hokm'⟩

private theorem hkdf_to_slice_kdf_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    (hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H)
      nfs3PlacedFakeB (blkPl_402).base KdfCodeLoaded C.F)
    {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : Nat} {s₀ : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀
      nfs3PlacedFakeB (KdfCodeLoaded s₀.mem)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀ (HPost C.F salt ikm info okmA okmLen s₀) := by
  have hextract : RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateExtractDone hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) :=
    (seg_e0_placed_runsTo hpre).trans fun _ hs0 =>
    (nfs1_runsTo hNfs hpre hs0
      (fun hkf => hpre.base_al.of_keepsFrozenNoAnon hkf)).trans fun _ hs1 =>
    (seg_e1_placed_runsTo h_memcpy h_compress hpre hs1).trans fun _ hs2 =>
    (seg_e1d_placed_runsTo hpre hs2).trans fun _ hs3 =>
    (fin_extract_kdf_runsTo (C := C) h_memcpy h_memset h_compress hpre hs3).trans fun _ hs4 =>
    (seg_e2_placed_runsTo hpre hs4).trans fun _ hs5 =>
    (nfs2_runsTo hNfs hpre hs5
      (fun hkf => hpre.base_al.of_keepsFrozenNoAnon hkf)).trans fun _ hs6 =>
    seg_e3_placed_runsTo hpre hs6
  have hb1 : RunsTo ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateB1Done hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen s₀) :=
    hextract.trans fun _ hs0 =>
    (seg_b1a_placed_runsTo hpre hs0).trans fun _ hs1 =>
    (seg_b1b_placed_runsTo h_memcpy hpre hs1).trans fun _ hs2 =>
    (fin_b1_kdf_runsTo (C := C) h_memcpy h_memset h_compress hpre hs2).trans fun _ hs3 =>
    seg_b1d_placed_runsTo h_memcpy hpre hs3
  have hiter_step : ∀ {tPrev okmSoFar : List (BitVec 8)} {i rem dstOff : Nat} {s : State},
      tPrev.length = 32 → (i = 1 ∨ i = 2) → (rem = 32 ∨ rem = 64) → dstOff + 32 ≤ okmLen →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s →
      RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
        (StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) :=
    fun ht_len hi hrem hdst hx =>
      (iter_a1_placed_runsTo hpre ht_len hrem (by omega) hx).trans fun _ hs1 =>
      (iter_a2_placed_runsTo h_memcpy h_compress hpre ht_len (by omega) hs1).trans fun _ hs2 =>
      (iter_b_placed_runsTo h_memcpy hpre ht_len hi hrem hdst hs2).trans fun _ hs3 =>
      iter_fin_kdf_runsTo (C := C) h_memcpy h_memset h_compress hpre (by omega) hs3
  refine hb1.trans fun s₁ hs₁ => ?_
  rcases hpre.okm_len with rfl | rfl | rfl
  · exact (b1_done_32_placed_runsTo hpre hs₁).trans fun _ hdone =>
      epilogue_placed_runsTo hpre hdone
  · refine (b1_to_loop_placed_runsTo (Or.inl rfl) hs₁).trans fun _ hloop1 => ?_
    refine (hiter_step (t1_length _ _ _) (Or.inl rfl) (Or.inl rfl) (by decide) hloop1).trans
      fun _ hfin1 => ?_
    refine (iter_d_done_placed_runsTo h_memcpy hpre (by decide) rfl ?_ hfin1).trans
      fun _ hdone => epilogue_placed_runsTo hpre hdone
    exact (hkdfExpand_64_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
  · refine (b1_to_loop_placed_runsTo (Or.inr rfl) hs₁).trans fun _ hloop1 => ?_
    refine (hiter_step (t1_length _ _ _) (Or.inl rfl) (Or.inr rfl) (by decide) hloop1).trans
      fun _ hfin1 => ?_
    refine (iter_d_continue_placed_runsTo h_memcpy hpre rfl hfin1).trans fun _ hloop2 => ?_
    refine (hiter_step (length_hmacWith _ _ _) (Or.inr rfl) (Or.inl rfl) (by decide)
      hloop2).trans fun _ hfin2 => ?_
    refine (iter_d_done_placed_runsTo h_memcpy hpre (by decide) rfl ?_ hfin2).trans
      fun _ hdone => epilogue_placed_runsTo hpre hdone
    exact (hkdfExpand_96_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm

private theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ∀ n, (ProofLib.stripExecOutside keep m).readBytes a n = m.readBytes a n
  | 0 => rfl
  | n + 1 => by
    simp [Memory.readBytes, ProofLib.strip_read8, strip_readBytes keep m (a + 1#64) n]

private theorem strip_read32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (ProofLib.stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, ProofLib.strip_read8]

private theorem strip_readShaState (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    readShaState (ProofLib.stripExecOutside keep m) a = readShaState m a := by
  unfold readShaState
  congr 1; funext i
  exact strip_read32 keep m _

private theorem strip_writeBytes_comm (keep : BitVec 64 → Bool) :
    ∀ (bs : List (BitVec 8)) (m : Memory) (a : BitVec 64),
      (ProofLib.stripExecOutside keep m).writeBytes a bs =
        ProofLib.stripExecOutside keep (m.writeBytes a bs)
  | [], _, _ => rfl
  | b :: bs, m, a => by
    simp only [Memory.writeBytes]
    rw [ProofLib.strip_write8, strip_writeBytes_comm keep bs (m.write8 a b) (a + 1#64)]

private theorem strip_permNoLazy_rw {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (h : m.permNoLazy a = some Perm.rw) :
    (ProofLib.stripExecOutside keep m).permNoLazy a = some Perm.rw := by
  dsimp only [ProofLib.stripExecOutside, Memory.permNoLazy] at h ⊢
  rcases hc : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> simp [hc, Perm.rw] at h ⊢
  rcases h with ⟨rfl, rfl, rfl, rfl⟩; cases keep a <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem hook_writeBytes_strip_vm (keep : BitVec 64 → Bool) (s : State)
    (bs : List (BitVec 8)) :
    returnToLinkRegister ((ProofLib.stripS keep s).setMem
        ((ProofLib.stripS keep s).mem.writeBytes ((ProofLib.stripS keep s).readReg64 .x0) bs)) =
      ProofLib.stripS keep
        (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) ∧
    VmPreserved s (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) := by
  refine ⟨?_, ?_⟩
  · cases s
    dsimp only [ProofLib.stripS, returnToLinkRegister, State.setMem, State.setPC, State.readReg64]
    rw [strip_writeBytes_comm]
  · unfold returnToLinkRegister
    simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem kdfOnlyHooks_findSome?_active [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooks C.F H] :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = some f →
      ∀ s : State,
        (f (ProofLib.stripS keepKdf s)).status = .Running →
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f ∧
        f (ProofLib.stripS keepKdf s) = ProofLib.stripS keepKdf (f s) ∧
        VmPreserved s (f s)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      by_cases hn : (n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym) = true
      · have hk_eq : kdfOnlyHooks H n = H n := by simp [kdfOnlyHooks, hn]
        rw [hk_eq] at h
        intro s _hrun
        simp only [Bool.or_eq_true, beq_iff_eq] at hn
        rcases hn with (rfl | rfl) | rfl
        · rw [hH.memset] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memsetHook
          simp only [stripS_readReg64]
          exact hook_writeBytes_strip_vm keepKdf s _
        · rw [hH.memcpy] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memcpyHook
          simp only [stripS_readReg64]
          have hrd : (ProofLib.stripS keepKdf s).mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat =
              s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat := by
            cases s; exact strip_readBytes keepKdf _ _ _
          rw [hrd]
          exact hook_writeBytes_strip_vm keepKdf s _
        · rw [hH.compress256] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold compress256Hook
          dsimp only []
          simp only [stripS_readReg64]
          have hst : readShaState (ProofLib.stripS keepKdf s).mem (s.readReg64 .x0) =
              readShaState s.mem (s.readReg64 .x0) := by
            cases s; exact strip_readShaState keepKdf _ _
          have hbs : (ProofLib.stripS keepKdf s).mem.readBytes (s.readReg64 .x1)
                (64 * (s.readReg64 .x2).toNat) =
              s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat) := by
            cases s; exact strip_readBytes keepKdf _ _ _
          rw [hst, hbs]
          exact hook_writeBytes_strip_vm keepKdf s _
      · simp only [Bool.not_eq_true] at hn
        cases hHn : H n with
        | none =>
          have hk_n : kdfOnlyHooks H n = none := by unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_n] at h; dsimp only at h ⊢
          exact kdfOnlyHooks_findSome?_active (C := C) tl h
        | some g =>
          have hk_g : kdfOnlyHooks H n = some (fun s => s.setStatus (.Exception "ext")) := by
            unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_g] at h; dsimp only at h
          injection h with hf; subst hf; intro s hrun; cases s; cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_active (C := C) tl h

private theorem kdfOnlyHooks_findSome?_none {H : LibsignalHooks} :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = none →
      (l.findSome? fun (n, o) => if o == off then H n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      cases hHn : H n with
      | none =>
        have hk : kdfOnlyHooks H n = none := by
          unfold kdfOnlyHooks; split <;> simp [hHn]
        rw [hk] at h
        exact kdfOnlyHooks_findSome?_none tl h
      | some g =>
        have hk : ∃ g', kdfOnlyHooks H n = some g' := by
          unfold kdfOnlyHooks
          split
          · exact ⟨g, hHn⟩
          · exact ⟨_, by rw [hHn]; rfl⟩
        rcases hk with ⟨g', hg'⟩
        rw [hg'] at h
        cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_none tl h

private theorem kdfOnlyHooks_externAt?_active [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {pc : BitVec 64} {f : State → State}
    (hext : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? pc = some f)
    {s : State} (hrun : (f (ProofLib.stripS keepKdf s)).status = .Running) :
    ((blkPC_379).rebase (blkPl_379).base H).externAt? pc = some f ∧
    f (ProofLib.stripS keepKdf s) = ProofLib.stripS keepKdf (f s) ∧
    VmPreserved s (f s) := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  cases hm : ((blkPC_379).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_379).base).toNat then kdfOnlyHooks H n else none) with
  | none => rw [hm] at hext; cases hext
  | some g =>
    rw [hm] at hext; injection hext with hgf; subst hgf
    obtain ⟨hhk, hcomm, hvm⟩ :=
      kdfOnlyHooks_findSome?_active (C := C) (blkPC_379).stubs hm s hrun
    rw [hhk]
    exact ⟨rfl, hcomm, hvm⟩

private theorem kdfOnlyHooks_externAt?_none [LibsignalPlacement] {H : LibsignalHooks}
    {pc : BitVec 64}
    (hext : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? pc = none) :
    ((blkPC_379).rebase (blkPl_379).base H).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  have h1 : ((blkPC_379).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_379).base).toNat then kdfOnlyHooks H n else none) = none := by
    cases hm : ((blkPC_379).stubs.findSome? fun (n, o) =>
        if o == (pc - (blkPl_379).base).toNat then kdfOnlyHooks H n else none) with
    | none => rfl
    | some g => rw [hm] at hext; cases hext
  rw [kdfOnlyHooks_findSome?_none (blkPC_379).stubs h1]
  rfl

private theorem safeVm_of_block_progKeep
    (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (hchk : checkBlockSafeVm lib.text = true)
    {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hL : ((lib.program pl).rebase pl.base vmTrapHooks).CodeLoaded m)
    (hkeep : ProofLib.progKeep ((lib.program pl).rebase pl.base vmTrapHooks) pc = true)
    (hal_pc : pc.toNat % 4 = 0)
    (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  let Q := (lib.program pl).rebase pl.base (fun _ => none)
  have hall : Q.allInstrs (fun i => !(i.isSvc0 || i.isMsrTpidrEl0)) = true :=
    placedLib_rebase_allInstrs_safeVm lib pl (fun _ => none) hchk
  have hLQ : Q.CodeLoaded m := hL.of_base_code rfl rfl
  have hlen_mod4 : Q.code.length % 4 = 0 := by
    have hcode : Q.code = lib.text.patched pl := rfl
    rw [hcode, Obj.CodeBlock.length_patched]
    omega
  have hoff_lt : (pc - Q.base).toNat < Q.code.length := by
    unfold ProofLib.progKeep at hkeep
    exact of_decide_eq_true hkeep
  have hbase_al : Q.base.toNat % 4 = 0 := hLQ.aligned
  have hno_wrap : Q.base.toNat + Q.code.length ≤ 2 ^ 64 := hLQ.no_wrap
  have hpc_eq : pc = Q.base + BitVec.ofNat 64 (pc - Q.base).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm Q.base, BitVec.sub_add_cancel]
  have hpc_nat : pc.toNat = Q.base.toNat + (pc - Q.base).toNat := by
    conv_lhs => rw [hpc_eq]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := (pc - Q.base).toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hin : (pc - Q.base).toNat + 4 ≤ Q.code.length := by omega
  have hfe_Q : Q.fetchMem m pc = some inst := by
    have hext_Q : Q.externAt? pc = none := by
      unfold Q Program.externAt? Program.hookAtOff? Program.rebase
      dsimp only
      rw [findSome?_symbols_none, findSome?_symbols_none]
      rfl
    have hce_Q : m.canExec pc 4 = true := by
      unfold Memory.canExec; rw [Memory.allPerm_iff]; intro k hk
      have hk_lt : (pc - Q.base).toNat + k < Q.code.length := by omega
      have heq_addr : pc + BitVec.ofNat 64 k =
          Q.base + BitVec.ofNat 64 ((pc - Q.base).toNat + k) := by
        conv_lhs => rw [hpc_eq]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [heq_addr, hLQ.perm_eq _ hk_lt]
      rfl
    unfold Program.fetchMem
    rw [hext_Q]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
      not_true_eq_false, hce_Q, Bool.not_true]
    exact hdec
  have hboth := Program.fetchMem_of_allInstrs_holdsBytes_in_code hall hbase_al hno_wrap
    (fun k hk => ⟨hLQ.byte_eq k hk, hLQ.perm_eq k hk, hLQ.isLazyFree_eq k hk⟩) hin hfe_Q
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hboth
  exact hboth

private theorem steps_kdf_lockstep_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {s1 sf0 sf' : State}
    (hsteps0 : Steps ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)) s1 sf0)
    (hrun0 : sf0.status = .Running) :
    ∀ {s1' : State},
      s1' = ProofLib.stripS keepKdf s1 →
      Steps ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)) s1' sf' →
      sf'.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      ∃ sf : State,
        (sf = sf0 ∨ sf' = ProofLib.stripS keepKdf sf) ∧
        Steps ((blkPC_379).rebase (blkPl_379).base H) s1 sf ∧
        VmPreserved s1 sf := by
  induction hsteps0 with
  | refl =>
    intro s1' _ _ _ _
    exact ⟨_, Or.inl rfl, .refl _, VmPreserved.refl _⟩
  | @step s1 s2 sf0 h1_0 hrest0 ih =>
    intro s1' hs1' hsteps' hrun_f hcl1
    cases hsteps' with
    | refl =>
      exact ⟨s1, Or.inr hs1', .refl s1, VmPreserved.refl s1⟩
    | @step _ s2' _ h1' hrest' =>
      subst hs1'
      have hr2_0 : s2.status = .Running := by
        cases hrest0 with
        | refl => exact hrun0
        | step hs _ => cases hs <;> assumption
      have hr2' : s2'.status = .Running := by
        cases hrest' with
        | refl => exact hrun_f
        | step hs _ => cases hs <;> assumption
      cases h1_0 with
      | halt_unmapped _ _ _ => cases s1; cases hr2_0
      | extern_fault _ _ _ => cases s1; cases hr2_0
      | @extern f hr1 hext0 hkf_s1 hsym_s1 =>
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          unfold Program.fetchMem at hfe'
          rw [hpc_eq, hext0] at hfe'
          simp at hfe'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext0] at hext'
          injection hext' with hff'
          subst hff'
          obtain ⟨hext_H, hcomm, hvm1⟩ :=
            kdfOnlyHooks_externAt?_active (C := C) hext0 hr2'
          have hstep_H : Step ((blkPC_379).rebase (blkPl_379).base H) s1 (f s1) :=
            Step.extern hr1 hext_H hkf_s1 hsym_s1
          have hcl2 : LibsignalCodeLoaded lsmpl (f s1).mem := hcl1.of_keepsFrozen hkf_s1
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ := ih hrun0 hcomm hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩
      | @exec inst hr1 hfe0 =>
        let P_H := (blkPC_379).rebase (blkPl_379).base H
        have hext_kdf :
            ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? s1.pc = none := by
          cases he : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).externAt? s1.pc with
          | none => rfl
          | some g => unfold Program.fetchMem at hfe0; rw [he] at hfe0; simp at hfe0
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext_kdf] at hext'; cases hext'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keepKdf s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS keepKdf s1).mem =
              ProofLib.stripExecOutside keepKdf s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          have hext_H : P_H.externAt? s1.pc = none := kdfOnlyHooks_externAt?_none hext_kdf
          have ⟨hal_pc, hce', hdec⟩ : s1.pc.toNat % 4 = 0 ∧
              (ProofLib.stripExecOutside keepKdf s1.mem).canExec s1.pc 4 = true ∧
              Arm64.decode (s1.mem.read32 s1.pc) = some inst' := by
            unfold Program.fetchMem at hfe'
            rw [hext_kdf] at hfe'
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
            by_cases hal : s1.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
              split at hfe'
              · contradiction
              · rename_i hce_neg
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce_neg
                rw [strip_read32] at hfe'; exact ⟨hal, hce_neg, hfe'⟩
            · simp only [hal, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          have hce : s1.mem.canExec s1.pc 4 = true := by
            unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
            have hxk := hce' k hk
            rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
          have hfe0' := hfe0
          unfold Program.fetchMem at hfe0'
          rw [hext_kdf] at hfe0'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
            not_true_eq_false, hce, Bool.not_true] at hfe0'
          have hinst_eq : inst' = inst := Option.some.inj (hdec.symm.trans hfe0')
          subst hinst_eq
          have hfe_H : P_H.fetchMem s1.mem s1.pc = some inst' := by
            unfold Program.fetchMem
            rw [hext_H]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
              not_true_eq_false, hce, Bool.not_true]
            exact hdec
          have hkeep_pc : keepKdf s1.pc = true := by
            unfold Memory.canExec at hce'; rw [Memory.allPerm_iff] at hce'
            have hx0 := hce' 0 (by omega)
            simpa using (ProofLib.strip_perm_x_imp hx0).2
          have ⟨hnsvc0, hnmsr⟩ : inst'.isSvc0 = false ∧ inst'.isMsrTpidrEl0 = false := by
            unfold keepKdf at hkeep_pc
            simp only [Bool.or_eq_true] at hkeep_pc
            rcases hkeep_pc with (hk379 | hk402) | hk425
            · have hI : IsLsBlockProg ((blkPC_379).rebase (blkPl_379).base vmTrapHooks) 379 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_379).rebase (blkPl_379).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 379 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_379).rebase (blkPl_379).base vmTrapHooks =
                  (blkLib_379.program blkPl_379).rebase (blkPl_379).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_379).symm
              exact safeVm_of_block_progKeep blkLib_379 blkPl_379 blk379_safeVm
                (hEq ▸ hL) (hEq ▸ hk379) hal_pc hdec
            · have hI : IsLsBlockProg ((blkPC_402).rebase (blkPl_402).base vmTrapHooks) 402 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_402).rebase (blkPl_402).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 402 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_402).rebase (blkPl_402).base vmTrapHooks =
                  (blkLib_402.program blkPl_402).rebase (blkPl_402).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_402).symm
              exact safeVm_of_block_progKeep blkLib_402 blkPl_402 blk402_safeVm
                (hEq ▸ hL) (hEq ▸ hk402) hal_pc hdec
            · have hI : IsLsBlockProg ((blkPC_425).rebase (blkPl_425).base vmTrapHooks) 425 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_425).rebase (blkPl_425).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 425 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_425).rebase (blkPl_425).base vmTrapHooks =
                  (blkLib_425.program blkPl_425).rebase (blkPl_425).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_425).symm
              exact safeVm_of_block_progKeep blkLib_425 blkPl_425 blk425_safeVm
                (hEq ▸ hL) (hEq ▸ hk425) hal_pc hdec
          have hev0 : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1 =
              execInst inst' s1 :=
            Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
          have hev_kdf : ((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst'
              (ProofLib.stripS keepKdf s1) =
              ProofLib.stripS keepKdf
                (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0, Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
          have hstep_H : Step P_H s1
              (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            have := Step.exec (prog := P_H) hr1 hfe_H
            rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
          have hcl2 : LibsignalCodeLoaded lsmpl
              (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1).mem :=
            hcl1.of_keepsFrozen hstep_H.keepsFrozen
          have hvm1 : VmPreserved s1
              (((blkPC_379).rebase (blkPl_379).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            exact VmPreserved.of_vm_tpidr
              (VerifiedLibraries.RustStd.nonSyscallPreserved_toVmFields
                (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1))
              (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
              (LibsignalBinary.Heap.FdsHiFrame.of_fs_eq
                (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2)
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ := ih hrun0 hev_kdf hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩

/-- Block `379` (`spqr::kdf::hkdf_to_slice`, 473 instructions) meets
    `withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))` on
    `(blkPC_379).rebase (blkPl_379).base H`. -/
theorem hkdf_to_slice_spqr_placed_ok [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [hH : HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨ (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).pre x s0 ∗ R at hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  let s0' := ProofLib.stripS keepKdf s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepKdf s0.mem := by cases s0; rfl
  have hrw_strip : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha
    rw [hs0'_mem]
    exact strip_permNoLazy_rw (hrw a ha)
  have hread_iv0 : s0.mem.Readable spqrSha256IVAddr 32 := by
    intro a ha
    obtain ⟨hp, hlf⟩ := hro_iv a ha
    exact ⟨by rw [hp]; rfl, hlf⟩
  have hread_iv0_fake : s0.mem.Readable
      (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rw [nfs3PlacedFakeB_add_iv]
    exact hread_iv0
  have hread_iv' : s0'.mem.Readable spqrSha256IVAddr 32 := by
    intro a ha
    obtain ⟨hp, hlf⟩ := hro_iv a ha
    rw [hs0'_mem]
    refine ⟨?_, by rwa [ProofLib.strip_isLazyFree]⟩
    rw [ProofLib.strip_perm, hp]
    cases keepKdf a <;> rfl
  have hread_iv_fake : s0'.mem.Readable
      (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rw [nfs3PlacedFakeB_add_iv]
    exact hread_iv'
  have hout_salt_stk : ∀ a, InRegion x.saltA x.salt.length a →
      OutsideRegion (hsp s0 - 544#64) 1232 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have hhsp_eq : hsp s0' = hsp s0 := by unfold hsp; simp [s0', stripS_sp]
  have h_hpre0 : HPre hkdfCodeFakeB x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0
      nfs3PlacedFakeB (KdfCodeLoaded s0.mem) :=
    { pc_eq         := by rw [hkdfCodeFakeB, BitVec.sub_add_cancel]; exact hpc
      status        := hrun
      x0_eq         := hx0
      x1_eq         := hx1
      x2_eq         := hx2
      x3_eq         := hx3
      x4_eq         := hx4
      x5_eq         := hx5
      x6_eq         := hx6
      x7_eq         := hx7
      salt_lt       := hsalt_lt
      ikm_len       := hikm_len
      info_ge       := hinfo_ge
      info_lt       := hinfo_lt
      okm_len       := hokm_len
      base_al       := kdfCodeLoaded_of_ls hcl
      ro_iv_bytes   := by rw [nfs3PlacedFakeB_add_iv]; exact hiv_eq
      ro_iv_read    := hread_iv0_fake
      disj_iv_stk   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm
      salt_bytes    := bytesAt_read (by omega) hsep_salt_stk
      ikm_bytes     := bytesAt_read (by omega) hsep_ikm_stk
      info_bytes    := bytesAt_read (by omega) hsep_info_stk
      rw_okm        := hrw_okm
      rw_stack      := hrw_stk
      disj_okm_stk  := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_salt_stk := by
        by_cases h0 : x.salt.length = 0
        · exact Or.inl h0
        · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk)
      out_salt_stk  := hout_salt_stk
      out_salt_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
      out_ikm_stk   := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
      out_ikm_okm   := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
      out_info_stk  := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
      out_info_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
      sp_aligned    := by simpa [State.spAligned] using hsp_al }
  have h_hpre : HPre hkdfCodeFakeB x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0'
      nfs3PlacedFakeB (KdfCodeLoaded s0'.mem) :=
    { pc_eq         := by
        rw [hkdfCodeFakeB, BitVec.sub_add_cancel]
        simpa [s0', stripS_pc] using hpc
      status        := by simpa [s0', stripS_status] using hrun
      x0_eq         := by simpa [s0', stripS_readReg64] using hx0
      x1_eq         := by simpa [s0', stripS_readReg64] using hx1
      x2_eq         := by simpa [s0', stripS_readReg64] using hx2
      x3_eq         := by simpa [s0', stripS_readReg64] using hx3
      x4_eq         := by simpa [s0', stripS_readReg64] using hx4
      x5_eq         := by simpa [s0', stripS_readReg64] using hx5
      x6_eq         := by simpa [s0', stripS_readReg64] using hx6
      x7_eq         := by simpa [s0', stripS_readReg64] using hx7
      salt_lt       := hsalt_lt
      ikm_len       := hikm_len
      info_ge       := hinfo_ge
      info_lt       := hinfo_lt
      okm_len       := hokm_len
      base_al       := hs0'_mem ▸ kdfCodeLoaded_strip hcl
      ro_iv_bytes   := by
        rw [nfs3PlacedFakeB_add_iv, hs0'_mem, strip_readBytes]
        exact hiv_eq
      ro_iv_read    := hread_iv_fake
      disj_iv_stk   := by
        rw [nfs3PlacedFakeB_add_iv, hhsp_eq]
        exact CryptoVerification.LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
          (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact CryptoVerification.LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw
          (by decide) hokm_pos hro_iv hrw_okm
      salt_bytes    := by rw [hs0'_mem, strip_readBytes]; exact bytesAt_read (by omega) hsep_salt_stk
      ikm_bytes     := by rw [hs0'_mem, strip_readBytes]; exact bytesAt_read (by omega) hsep_ikm_stk
      info_bytes    := by rw [hs0'_mem, strip_readBytes]; exact bytesAt_read (by omega) hsep_info_stk
      rw_okm        := hrw_strip hrw_okm
      rw_stack      := by rw [hhsp_eq]; exact hrw_strip hrw_stk
      disj_okm_stk  := by rw [hhsp_eq]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_salt_stk := by
        rw [hhsp_eq]
        by_cases h0 : x.salt.length = 0
        · exact Or.inl h0
        · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk)
      out_salt_stk  := by rw [hhsp_eq]; exact hout_salt_stk
      out_salt_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
      out_ikm_stk   := by rw [hhsp_eq]; exact bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
      out_ikm_okm   := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
      out_info_stk  := by rw [hhsp_eq]; exact bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
      out_info_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
      sp_aligned    := by simpa [State.spAligned, s0', stripS_sp] using hsp_al }
  let H' := kdfOnlyHooks H
  have hH' : HkdfPlacedHooks C.F H' := inferInstance
  have hNfs : Nfs3GenRunsToProg ((blkPC_379).rebase (blkPl_379).base H')
      nfs3PlacedFakeB (blkPl_402).base KdfCodeLoaded C.F := by
    intro s_nfs hpc_nfs hstat_nfs hlen_nfs hiv_nfs hcl_nfs hread_iv_nfs hdisj_iv_nfs
      h_out_nfs h_stk_nfs h_out_stk_nfs h_key_stk_nfs _ hal_nfs
    rw [nfs3PlacedFakeB_add_iv] at hiv_nfs hread_iv_nfs hdisj_iv_nfs
    exact runsTo_of_kdf_402 hcl_nfs
      (new_from_slice3_gen_placed_runsTo C H' hpc_nfs hstat_nfs hlen_nfs hiv_nfs
        hread_iv_nfs hdisj_iv_nfs h_out_nfs h_stk_nfs h_out_stk_nfs h_key_stk_nfs hal_nfs)
  have hRuns0 := hkdf_to_slice_kdf_runsTo (C := C) (H := H')
    hH'.memcpy hH'.memset hH'.compress256 hNfs h_hpre0
  have hRuns := hkdf_to_slice_kdf_runsTo (C := C) (H := H')
    hH'.memcpy hH'.memset hH'.compress256 hNfs h_hpre
  intro hL0
  have hL0_kdf : ((blkPC_379).rebase (blkPl_379).base H').CodeLoaded s0.mem :=
    (kdfCodeLoaded_of_ls hcl) H' |>.1
  have hL0' : ((blkPC_379).rebase (blkPl_379).base H').CodeLoaded s0'.mem :=
    (hs0'_mem ▸ kdfCodeLoaded_strip hcl) H' |>.1
  obtain ⟨sf0, hsteps0, htr0, hpost0, _⟩ := hRuns0 hL0_kdf
  obtain ⟨sf', hsteps', htr', hpost', _⟩ := hRuns hL0'
  obtain ⟨sf, hor, hsteps_H, hvm⟩ :=
    steps_kdf_lockstep_vm (C := C) (H := H) hsteps0 hpost0.2.1 rfl hsteps' hpost'.2.1 hcl
  have ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩ :
      TraceEq s0 sf ∧ HPost C.F x.salt x.ikm x.info x.okmA x.okmLen s0 sf := by
    rcases hor with rfl | hsf_eq
    · exact ⟨htr0, hpost0⟩
    · subst hsf_eq
      rcases hpost' with ⟨hpc_sf', hstat_sf', hcallee', hokm_sf', hframe_sf'⟩
      have hpc_sf : sf.pc = s0.readReg64 .x30 := by
        simpa [s0', stripS_pc, stripS_readReg64] using hpc_sf'
      have hstat_sf : sf.status = .Running := by
        simpa [stripS_status] using hstat_sf'
      have hcallee : CalleeSaved s0 sf := by
        refine ⟨by simpa [s0', stripS_sp] using hcallee'.1, fun r hr => ?_⟩
        simpa [s0', stripS_readReg64] using hcallee'.2 r hr
      have htr : TraceEq s0 sf :=
        ⟨by simpa [s0', stripS_trace] using htr'.1,
         by simpa [s0', stripS_calleeSavedVRegs] using htr'.2⟩
      have hsf_mem : (ProofLib.stripS keepKdf sf).mem = ProofLib.stripExecOutside keepKdf sf.mem := by
        cases sf; rfl
      have hokm_sf : sf.mem.readBytes x.okmA x.okmLen =
          hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := by
        rwa [hsf_mem, strip_readBytes] at hokm_sf'
      have hframe_sf : HFrame x.okmLen s0 sf.mem := by
        unfold HFrame Frame at hframe_sf' ⊢
        rcases hframe_sf' with ⟨hfr1, _hfr2, hfr3, hfr4, hfr5⟩
        have hx6_s0' : s0'.readReg64 .x6 = s0.readReg64 .x6 :=
          stripS_readReg64 keepKdf s0 .x6
        refine ⟨?_, funext hvm.perm_eq, ?_, ?_, ?_⟩
        · intro a hout
          have h1 := hfr1 a (by rwa [hx6_s0', hhsp_eq])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_read8, ProofLib.strip_read8] at h1
        · intro a hout
          have h3 := hfr3 a (by rwa [hx6_s0', hhsp_eq])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree] at h3
        · intro a hlf
          have h4 := hfr4 a (by rwa [hs0'_mem, ProofLib.strip_isLazyFree])
          rwa [hsf_mem, ProofLib.strip_isLazyFree] at h4
        · intro a han
          have h5 := hfr5 a (by rwa [hs0'_mem, ProofLib.strip_isAnon])
          rwa [hsf_mem, ProofLib.strip_isAnon] at h5
      exact ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨sf, hsteps_H, Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩⟩
  dsimp only [withLsCodeRoLoaded, withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [t1_length, t2_length, t3_length]
  refine ⟨⟨h_exp_len, htr.1⟩, ?_⟩
  unfold HFrame at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- Any caller block `i < 619` can invoke Block `379` (`spqr::kdf::hkdf_to_slice`) at
`lsmpl.base 379` under `withLsCodeRoLoaded lsmpl` with `VmPreserved`. -/
theorem hkdf_to_slice_spqr_placed_ok_of_other_block [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_placed_ok C) hi

/-- Block `378` (`spqr::kdf::hkdf_to_vec`, 47 instructions) meets
    `withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))`, discharging the
    `hkdf_to_slice` tail call directly via `hkdf_to_slice_spqr_placed_ok_of_other_block`. -/
theorem hkdf_to_vec_spqr_placed_ok [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hshim : HookSat H spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_378).rebase (blkPl_378).base H) (blkPl_378).base
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))) :=
  hkdf_to_vec_placed_ok M A lim (spqrHkdfWith C.F) hshim hZero
    (hkdf_to_slice_spqr_placed_ok_of_other_block C)

/-- Any caller block `i < 619` can invoke Block `378` (`spqr::kdf::hkdf_to_vec`) at
`lsmpl.base 378` under `withLsCodeRoLoaded lsmpl`. -/
theorem hkdf_to_vec_spqr_placed_ok_of_other_block [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hshim : HookSat H spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_vec_spqr_placed_ok C M A lim hshim hZero) hi

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudget
