/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesStepsR
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Tight `EpochDirectionPB::merge` Verification (`Block 299` on `blkPC_325`)

Proves canonical zero-capacity execution of `EpochDirectionPB::merge` (Block `299`) on
`tlb_EpochDirDom` (`SpqrTightEvs 2 1476 32` at `0` and `SpqrTightEvs 4 181944 79236` at `79236`)
and establishes `tlb_EpochDirectionMergeBlk325TightOkOf`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement ls_subroutine_ok_of_block lsmpl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (HighCalleeSaved IsDropSuffix decodeVarint_suffix sliceCursorAfter_eq_split
   sliceCursorAt suffix_trans ule_len_of_ge)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Varint
  (skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (WppPost blkPC_299 blkPl_299 bv_len_sub_limit codecWireTypeToProto
   mergeBytes_length mergeBytes_suffix subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Top.DecodeState
  (EpochDirectionMergeGhost V1InnerHeapPred epochDirectionMergeStack epochDirectionPBCapOkAt
   vecU8CapOkAt vecU8CapOkAt_mono)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_EpochDirDom tlb_EpochDirectionGuardedEnvOf tlb_EpochDirectionMergeBlk325TightOkOf
   tlb_domHeap_of_dom tlb_domHeap_of_not_dom tlb_epochDirectionMergeTightSpecOfEnv
   tlb_epochDirectionZeroCapAt tlb_lenPrefixed tlb_vecU8ZeroCapAt
   tlb_vecU8ZeroCapAt_entails_vecU8CapOkAt)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (WppBudgetPanic wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesStepsR
  (e2ar_contractsClPlacedX_of_placedX e2ar_edLoopPre e2ar_ed_key_some_step e2ar_ed_ret_exit
   e2ar_ed_tag1_some_step e2ar_ed_tag2_zero_step e2ar_ed_tag3_zero_step
   e2ar_ls_subroutine_ok_cro_of_block e2ar_polyBytesMerge_of_signed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
  (e2ar_decodeVarint2Env_some_nil e2ar_decodeVarint_encodeKey
   e2ar_decodeVarint_encodeVarint_codec e2ar_decodeVarint_lenPrefixed
   e2ar_encodeBytesUncond_eq_key_lenPrefixed e2ar_mergeBytes_lenPrefixed
   e2ar_mergeMessage_epochDirection_lenPrefixed e2ar_raw_lt_of_lenPrefixed_lt)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (epochDirectionMergePostEnv_imp_pre epochDirectionMergeSpec epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)

private theorem e2ar_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2ar_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2ar_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2ar_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2ar_trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2ar_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2ar_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2ar_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2ar_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm]
private theorem e2ar_bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem e2ar_bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

attribute [local irreducible] Program.fetch Program.externAt?
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← Lean.getEnv
  for pfx in [`CryptoVerification.SpqrV1.Kdf,
      `CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof] do
    for sfx in ["sp_sub_688_eq_hsp", "sp_add_neg688_eq_hsp",
        "sp_sub_96_eq_hsp_592", "sp_add_neg96_eq_hsp_592",
        "hsp_592_sub_592_eq_hsp", "hsp_592_add_neg592_eq_hsp",
        "hsp_add_688_sub_688", "hsp_592_add_96_eq_sp"] do
      let nm := Lean.Name.str pfx sfx
      if env.contains nm then
        try Lean.Attribute.erase nm `arm64_norm catch _ => pure ()
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2ar_sp_setMem_pre e2ar_pc_setMem_pre e2ar_status_setMem_pre e2ar_pstate_setMem_pre
  e2ar_trace_setMem_pre e2ar_readReg64_setMem_pre e2ar_readReg32_setMem_pre
  e2ar_readReg_setMem_pre e2ar_calleeSavedVRegs_setMem_pre

private noncomputable def e2ar_epochDirDomOnlySpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EpochDirectionMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      tlb_EpochDirDom 79236 x ∧
      FitsEnv M lim st (tlb_EpochDirectionGuardedEnvOf 2 4 x)⌝ ∗
      tlb_epochDirectionZeroCapAt A.repAlloc x.msgPtr x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp epochDirectionMergeStack
  post := (tlb_epochDirectionMergeTightSpecOfEnv A lim
    (tlb_EpochDirectionGuardedEnvOf 2 4) (tlb_EpochDirectionGuardedEnvOf 2 4)).post

private theorem e2ar_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> simp_all [codecWireTypeToProto]

private theorem e2ar_truncate32_zeroExtend64 (v : BitVec 32) :
    (v.zeroExtend 64).truncate 32 = v := by
  bv_omega

private theorem e2ar_epochDirDomOnly_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (blkPl_299).base
      (withLsCodeRoLoaded lsmpl (e2ar_epochDirDomOnlySpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2ar_epochDirDomOnlySpec
  wpp_init p s0
  rcases p with ⟨x, st0⟩
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp; intro hinv0
  replace hpc : s0.pc = (blkPl_299).base := hpc
  change SepWPp _ _ _ _
    (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim
      (tlb_EpochDirectionGuardedEnvOf 2 4) (tlb_EpochDirectionGuardedEnvOf 2 4)) (x, st0) R s0)
    (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim
      (tlb_EpochDirectionGuardedEnvOf 2 4) (tlb_EpochDirectionGuardedEnvOf 2 4)) (x, st0) R s0)
  have ⟨pb, rest_out, maxPrev, Tight, hwt_ld, hmsg, hbs_eq, hnext, hprev, hmode, hFit0, hPost⟩ :
      ∃ (pb : EpochDirectionPB) (rest_out : List (BitVec 8)) (maxPrev : Nat)
        (Tight : List AllocEvent → Prop),
        x.wt = .lengthDelimited ∧ x.msg = default ∧
        x.bs = tlb_lenPrefixed (EpochDirectionPB.encodeRaw pb) rest_out ∧
        pb.next.length ≤ 32 ∧ pb.prev.length ≤ maxPrev ∧
        ((maxPrev = 0 ∧ Tight = SpqrTightEvs 2 1476 32) ∨
          (maxPrev = 79236 ∧ Tight = SpqrTightEvs 4 181944 79236)) ∧
        FitsEnv M lim st0 Tight ∧
        (∀ evs, Tight evs → tlb_EpochDirectionGuardedEnvOf 2 4 x evs) := by
    by_cases hDom0 : tlb_EpochDirDom 0 x
    · rcases hDom0 with ⟨hwt, hmsg, pb, rest_out, ⟨hnext, hprev⟩, hbs⟩
      refine ⟨pb, rest_out, 0, SpqrTightEvs 2 1476 32,
        e2ar_wt_eq_lengthDelimited hwt, hmsg, hbs, hnext, hprev, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
      · intro evs ht
        exact h evs (Or.inl ⟨⟨hwt, hmsg, pb, rest_out, ⟨hnext, hprev⟩, hbs⟩, ht⟩)
      · intro evs ht
        exact Or.inl ⟨⟨hwt, hmsg, pb, rest_out, ⟨hnext, hprev⟩, hbs⟩, ht⟩
    · rcases h_5 with ⟨hwt, hmsg, pb, rest_out, ⟨hnext, hprev⟩, hbs⟩
      refine ⟨pb, rest_out, 79236, SpqrTightEvs 4 181944 79236,
        e2ar_wt_eq_lengthDelimited hwt, hmsg, hbs, hnext, hprev, Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
      · intro evs ht
        exact h evs (Or.inr (Or.inl ⟨hDom0, ⟨hwt, hmsg, pb, rest_out, ⟨hnext, hprev⟩, hbs⟩, ht⟩))
      · intro evs ht
        exact Or.inr (Or.inl ⟨hDom0, ⟨hwt, hmsg, pb, rest_out, ⟨hnext, hprev⟩, hbs⟩, ht⟩)
  have hraw_lt : (EpochDirectionPB.encodeRaw pb).length < 2 ^ 64 := by
    apply e2ar_raw_lt_of_lenPrefixed_lt (rest := rest_out)
    rwa [← hbs_eq]
  have hsome_ed : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (pb, rest_out) := by
    rw [hwt_ld, hmsg, hbs_eq]
    exact e2ar_mergeMessage_epochDirection_lenPrefixed pb rest_out 98 (by decide) (hbs_eq ▸ h_4)
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  let raw := EpochDirectionPB.encodeRaw pb
  let rest0 := raw ++ rest_out
  let len0 : BitVec 64 := BitVec.ofNat 64 raw.length
  have hdv0 : decodeVarint x.bs = some (len0, rest0) := by
    rw [hbs_eq]
    exact e2ar_decodeVarint_lenPrefixed raw rest_out
  have hfits_dv0 : FitsEnv M lim st0 (DecodeVarint2Env x.bs) := fun evs he => by
    rw [e2ar_decodeVarint2Env_some_nil hdv0 he]; trivial
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
  (conv => arg 4; rw [epochDirectionMergeStack, stackAt_skipField3 s0.sp 98 (by decide), skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
  apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
  apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv0
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
    (ret_pc := (blkPl_299).base + 48#64) hVarintCall hinv0
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, h_3], h_4, hfits_dv0⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h_4)
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hlen0_nat : len0.toNat = raw.length := by
    dsimp only [len0, raw]
    simp only [BitVec.toNat_ofNat]
    omega
  have hlt_len : ¬ rest0.length < len0.toNat := by
    dsimp only [rest0]; rw [List.length_append, hlen0_nat]; omega
  have hule := ule_len_of_ge hlt_len hrest0_lt
  have hsub := bv_len_sub_limit hlt_len
  have hlim_eq : rest0.length - len0.toNat = rest_out.length := by
    dsimp only [rest0]; rw [List.length_append, hlen0_nat]; omega
  have hlim_raw : rest0.length - raw.length = rest_out.length := by
    rw [← hlen0_nat]; exact hlim_eq
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2ar_decodeVarint2Env_some_nil hdv0 hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
  (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc])
  wp_steps_sync_pool ((blkPl_299).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  let cur3 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 pb.prev ++ rest_out
  let cur2 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 2#32 pb.next ++ cur3
  have hrest0_eq : rest0 = CryptoVerification.LibsignalSpqrV1.Proto.encodeUint32Field 1#32 pb.ctr ++ cur2 := by
    dsimp only [rest0, raw, EpochDirectionPB.encodeRaw, cur2, cur3]
    simp only [List.append_assoc]
  suffices hAfter1 : ∀ s1 : State,
      IsDropSuffix x.bs cur2 → cur2.length ≤ x.bs.length →
      s1.pc = (blkPl_299).base + 160#64 →
      s1.status = .Running → s1.sp = s0.sp - 96#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot →
      s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_out.length →
      HighCalleeSaved s0 s1 → LibsignalCodeRoLoaded lsmpl s1.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s1
        (e2ar_edLoopPre A lim st0 s0 s1 x.msgPtr x.bufRef x.slot x.ptr
          (tlb_epochDirectionZeroCapAt A.repAlloc x.msgPtr { (default : EpochDirectionPB) with ctr := pb.ctr })
          x.bs cur2)
        (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim
          (tlb_EpochDirectionGuardedEnvOf 2 4) (tlb_EpochDirectionGuardedEnvOf 2 4)) (x, st0) R s0)
        (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim
          (tlb_EpochDirectionGuardedEnvOf 2 4) (tlb_EpochDirectionGuardedEnvOf 2 4)) (x, st0) R s0) by
    refine SepWPp.weaken_pre
      (P' := e2ar_edLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr
        (tlb_epochDirectionZeroCapAt A.repAlloc x.msgPtr default) x.bs rest0)
      (by rw [e2ar_edLoopPre, hmsg, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail) ?_
    by_cases hctr0 : (pb.ctr == 0#32) = true
    · have hctr_eq : pb.ctr = 0#32 := eq_of_beq hctr0
      have hr0_cur2 : rest0 = cur2 := by
        rw [hrest0_eq, CryptoVerification.LibsignalSpqrV1.Proto.encodeUint32Field, hctr0]; rfl
      have hm_eq : ({ (default : EpochDirectionPB) with ctr := pb.ctr } : EpochDirectionPB) = default := by
        rw [hctr_eq]; rfl
      rw [hr0_cur2] at hrest0_suf hrest0_le ⊢
      rw [← hm_eq]
      exact hAfter1 _ hrest0_suf hrest0_le
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub, hlim_eq, hlim_raw])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm
    · have hctr_false : (pb.ctr == 0#32) = false := Bool.eq_false_iff.mpr hctr0
      let rest1 := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (pb.ctr.zeroExtend 64) ++ cur2
      have hr0_key : rest0 = CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint ++ rest1 := by
        rw [hrest0_eq, CryptoVerification.LibsignalSpqrV1.Proto.encodeUint32Field, hctr_false]
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]; rfl
      obtain ⟨key1, hd_k1, hk1⟩ := e2ar_decodeVarint_encodeKey 1#32 .varint rest1 (by decide)
      have hk1_val : key1.toNat = 8 := by rw [hk1]; decide
      rw [← hr0_key] at hd_k1
      have hdv_v1 : decodeVarint rest1 = some (pb.ctr.zeroExtend 64, cur2) :=
        e2ar_decodeVarint_encodeVarint_codec (pb.ctr.zeroExtend 64) cur2
      have hgt1 : ¬ rest0.length ≤ rest_out.length := by
        have h1 : cur2.length < rest1.length := decodeVarint_length hdv_v1
        have h2 : rest1.length < rest0.length := decodeVarint_length hd_k1
        have h3 : rest_out.length ≤ cur2.length := by
          dsimp only [cur2, cur3]; simp only [List.length_append]; omega
        omega
      have hrest1_le : rest1.length ≤ x.bs.length :=
        Nat.le_trans (Nat.le_of_lt (decodeVarint_length hd_k1)) hrest0_le
      have hrest1_lt : rest1.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest1_le h_4
      have hrest1_suf : IsDropSuffix x.bs rest1 :=
        suffix_trans hrest0_le hrest0_suf (Nat.le_of_lt (decodeVarint_length hd_k1))
          (decodeVarint_suffix hd_k1)
      have hcur2_le : cur2.length ≤ x.bs.length :=
        Nat.le_trans (Nat.le_of_lt (decodeVarint_length hdv_v1)) hrest1_le
      have hcur2_suf : IsDropSuffix x.bs cur2 :=
        suffix_trans hrest1_le hrest1_suf (Nat.le_of_lt (decodeVarint_length hdv_v1))
          (decodeVarint_suffix hdv_v1)
      refine e2ar_ed_key_some_step (iwt := .varint) hVarintCall hgt1 hsp_align hrest0_le hrest0_lt
        hrest0_suf hd_k1 (by rw [hk1_val]; decide) (by rw [hk1_val]; decide)
        (by rw [hk1_val]) ?_
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub, hlim_eq, hlim_raw])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm
      intro s1' hpc1' hrun1' hsp1' htr1' hx0_1' hx1_1' hx19_1' hx20_1' hx21_1' hx22_1' hcs1' hinv1'
      have hx1_eq : BitVec.ofNat 64 (key1.toNat / 8) = 1#64 := by rw [hk1_val]
      rw [hx1_eq] at hx1_1'
      refine e2ar_ed_tag1_some_step hVarintCall hsp_align hrest1_le hrest1_lt hrest1_suf hdv_v1 ?_
        hpc1' hrun1' hsp1' htr1' hx0_1' hx1_1' hx19_1' hx20_1' hx21_1' hx22_1' hcs1' hinv1'
      intro s2' hpc2' hrun2' hsp2' htr2' hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
      rw [e2ar_truncate32_zeroExtend64]
      exact hAfter1 s2' hcur2_suf hcur2_le hpc2' hrun2' hsp2' htr2'
        hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
  intro s1 hcur2_suf hcur2_le hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
  let m1 : EpochDirectionPB := { (default : EpochDirectionPB) with ctr := pb.ctr }
  have ht2_imp_tight : ∀ evs2, SpqrTightEvs 2 1476 32 evs2 → Tight evs2 := by
    intro evs2 ht2
    rcases hmode with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ht2
    · exact ht2.mono (by decide) (by decide) (by decide)
  have hFit_t2 : FitsEnv M lim st0 (SpqrTightEvs 2 1476 32) :=
    fun evs2 ht2 => hFit0 evs2 (ht2_imp_tight evs2 ht2)
  suffices hAfter2 : ∀ (evs2 : List AllocEvent) (s2 : State),
      SpqrTightEvs 2 1476 32 evs2 →
      IsDropSuffix x.bs cur3 → cur3.length ≤ x.bs.length →
      s2.pc = (blkPl_299).base + 160#64 →
      s2.status = .Running → s2.sp = s0.sp - 96#64 → s2.trace = s0.trace →
      s2.readReg64 (Reg.gpr 19#5) = x.bufRef → s2.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s2.readReg64 (Reg.gpr 21#5) = x.slot →
      s2.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_out.length →
      HighCalleeSaved s0 s2 → LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s2
        (e2ar_edLoopPre A lim (M.stepEvents evs2 st0) s0 s2 x.msgPtr x.bufRef x.slot x.ptr
          (vecU8CapOkAt A.repAlloc x.msgPtr cur3.length pb.next ∗
            tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) ([] : List (BitVec 8)) ∗
            ((x.msgPtr + 0x30#64) ↦₃₂ pb.ctr) ∗
            memRegion (x.msgPtr + 0x34#64) 4)
          x.bs cur3)
        (WppPost (tlb_epochDirectionMergeTightSpecOfEnv A lim
          (tlb_EpochDirectionGuardedEnvOf 2 4) (tlb_EpochDirectionGuardedEnvOf 2 4)) (x, st0) R s0)
        (WppBudgetPanic (tlb_epochDirectionMergeTightSpecOfEnv A lim
          (tlb_EpochDirectionGuardedEnvOf 2 4) (tlb_EpochDirectionGuardedEnvOf 2 4)) (x, st0) R s0) by
    by_cases hnext_emp : pb.next.isEmpty = true
    · have hnext_nil : pb.next = [] := List.isEmpty_iff.mp hnext_emp
      have hc2_eq : cur2 = cur3 := by
        dsimp only [cur2]; rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hnext_emp]; rfl
      rw [hc2_eq] at hcur2_suf hcur2_le ⊢
      refine SepWPp.weaken_pre ?_
        (hAfter2 [] s1 (SpqrTightEvs.nil 2 1476 32) hcur2_suf hcur2_le
          hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1)
      dsimp only [e2ar_edLoopPre, tlb_epochDirectionZeroCapAt, m1, LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]
      rw [hnext_nil]
      exact sepConj_mono_left (sepConj_mono_left
        (tlb_vecU8ZeroCapAt_entails_vecU8CapOkAt A.repAlloc x.msgPtr cur3.length []))
    · have hnext_false : pb.next.isEmpty = false := Bool.eq_false_iff.mpr hnext_emp
      let rest2 := tlb_lenPrefixed pb.next cur3
      have hc2_key : cur2 = CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited ++ rest2 := by
        dsimp only [cur2, rest2]
        rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hnext_false]
        exact e2ar_encodeBytesUncond_eq_key_lenPrefixed 2#32 pb.next cur3
      obtain ⟨key2, hd_k2, hk2⟩ := e2ar_decodeVarint_encodeKey 2#32 .lengthDelimited rest2 (by decide)
      rw [← hc2_key] at hd_k2
      have hmb2 : mergeBytes .lengthDelimited rest2 = some (pb.next, cur3) :=
        e2ar_mergeBytes_lenPrefixed pb.next cur3 (by omega)
      have hcur2_lt : cur2.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur2_le h_4
      have hgt2 : ¬ cur2.length ≤ rest_out.length := by
        have h1 : rest2.length < cur2.length := decodeVarint_length hd_k2
        have h2 : cur3.length ≤ rest2.length := mergeBytes_length hmb2
        have h3 : rest_out.length ≤ cur3.length := by
          dsimp only [cur3]; simp only [List.length_append]; omega
        omega
      have hrest2_le : rest2.length ≤ x.bs.length :=
        Nat.le_trans (Nat.le_of_lt (decodeVarint_length hd_k2)) hcur2_le
      have hrest2_lt : rest2.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest2_le h_4
      have hrest2_suf : IsDropSuffix x.bs rest2 :=
        suffix_trans hcur2_le hcur2_suf (Nat.le_of_lt (decodeVarint_length hd_k2))
          (decodeVarint_suffix hd_k2)
      have hcur3_le : cur3.length ≤ x.bs.length :=
        Nat.le_trans (mergeBytes_length hmb2) hrest2_le
      have hcur3_suf : IsDropSuffix x.bs cur3 :=
        suffix_trans hrest2_le hrest2_suf (mergeBytes_length hmb2) (mergeBytes_suffix hmb2)
      have hk2_val : key2.toNat = 18 := by rw [hk2]; decide
      refine e2ar_ed_key_some_step (iwt := .lengthDelimited) hVarintCall hgt2 hsp_align hcur2_le
        hcur2_lt hcur2_suf hd_k2 (by rw [hk2_val]; decide) (by rw [hk2_val]; decide)
        (by rw [hk2_val]; decide) ?_
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
      intro s2' hpc2' hrun2' hsp2' htr2' hx0_2' hx1_2' hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
      have hx1_eq : BitVec.ofNat 64 (key2.toNat / 8) = 2#64 := by rw [hk2_val]
      rw [hx1_eq] at hx1_2'
      refine e2ar_ed_tag2_zero_step hBytesCall hsp_align hrest2_le hrest2_lt hrest2_suf
        hmb2 hnext hFit_t2 ?_
        hpc2' hrun2' hsp2' htr2' hx0_2' hx1_2' hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
      intro evs2 s3' ht2 hpc3' hrun3' hsp3' htr3' hx19_3' hx20_3' hx21_3' hx22_3' hcs3' hinv3'
      exact hAfter2 evs2 s3' ht2 hcur3_suf hcur3_le
        hpc3' hrun3' hsp3' htr3' hx19_3' hx20_3' hx21_3' hx22_3' hcs3' hinv3'
  intro evs2 s2 ht2 hcur3_suf hcur3_le hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hinv2
  by_cases hprev_emp : pb.prev.isEmpty = true
  · have hprev_nil : pb.prev = [] := List.isEmpty_iff.mp hprev_emp
    have hc3_eq : cur3 = rest_out := by
      dsimp only [cur3]; rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hprev_emp]; rfl
    have hpb_eq : ({ ctr := pb.ctr, next := pb.next, prev := ([] : List (BitVec 8)) } : EpochDirectionPB) = pb := by
      cases pb; subst hprev_nil; rfl
    rw [hc3_eq] at hcur3_suf hcur3_le ⊢
    refine SepWPp.weaken_pre ?_
      (e2ar_ed_ret_exit (m := pb) (evs := evs2) rfl hsp_align hcur3_le hcur3_suf hsome_ed
        (hPost evs2 (ht2_imp_tight evs2 ht2)) rfl
        hpc2 hrun2 hsp2 htr2 hx21_2 hx22_2 hcs2)
    rw [← hpb_eq]
    dsimp only [e2ar_edLoopPre, epochDirectionPBCapOkAt]
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (tlb_vecU8ZeroCapAt_entails_vecU8CapOkAt A.repAlloc (x.msgPtr + 0x18#64) rest_out.length [])))
  · have hprev_false : pb.prev.isEmpty = false := Bool.eq_false_iff.mpr hprev_emp
    have hprev_pos : 0 < pb.prev.length := by
      cases hp : pb.prev with
      | nil => simp [hp] at hprev_false
      | cons _ _ => simp
    have ⟨hmax79, hTight4⟩ : maxPrev = 79236 ∧ Tight = SpqrTightEvs 4 181944 79236 := by
      rcases hmode with ⟨hm0, _⟩ | h79
      · omega
      · exact h79
    have hprev79 : pb.prev.length ≤ 79236 := hmax79 ▸ hprev
    have ht23_imp_tight : ∀ evs3, SpqrTightEvs 2 180468 79236 evs3 → Tight (evs2 ++ evs3) := by
      intro evs3 ht3
      rw [hTight4]
      exact (ht2.append ht3).mono (by decide) (by decide) (by decide)
    have hFit_t3 : FitsEnv M lim (M.stepEvents evs2 st0) (SpqrTightEvs 2 180468 79236) :=
      fun evs3 ht3 =>
        ((fitsEvents_append M lim evs2 evs3 st0).mp
          (hFit0 (evs2 ++ evs3) (ht23_imp_tight evs3 ht3))).2
    let rest3 := tlb_lenPrefixed pb.prev rest_out
    have hc3_key : cur3 = CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited ++ rest3 := by
      dsimp only [cur3, rest3]
      rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hprev_false]
      exact e2ar_encodeBytesUncond_eq_key_lenPrefixed 3#32 pb.prev rest_out
    obtain ⟨key3, hd_k3, hk3⟩ := e2ar_decodeVarint_encodeKey 3#32 .lengthDelimited rest3 (by decide)
    rw [← hc3_key] at hd_k3
    have hmb3 : mergeBytes .lengthDelimited rest3 = some (pb.prev, rest_out) :=
      e2ar_mergeBytes_lenPrefixed pb.prev rest_out (by omega)
    have hcur3_lt : cur3.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur3_le h_4
    have hgt3 : ¬ cur3.length ≤ rest_out.length := by
      have h1 : rest3.length < cur3.length := decodeVarint_length hd_k3
      have h2 : rest_out.length ≤ rest3.length := mergeBytes_length hmb3
      omega
    have hrest3_le : rest3.length ≤ x.bs.length :=
      Nat.le_trans (Nat.le_of_lt (decodeVarint_length hd_k3)) hcur3_le
    have hrest3_lt : rest3.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest3_le h_4
    have hrest3_suf : IsDropSuffix x.bs rest3 :=
      suffix_trans hcur3_le hcur3_suf (Nat.le_of_lt (decodeVarint_length hd_k3))
        (decodeVarint_suffix hd_k3)
    have hro_le : rest_out.length ≤ x.bs.length :=
      Nat.le_trans (mergeBytes_length hmb3) hrest3_le
    have hro_suf : IsDropSuffix x.bs rest_out :=
      suffix_trans hrest3_le hrest3_suf (mergeBytes_length hmb3) (mergeBytes_suffix hmb3)
    let m2 : EpochDirectionPB := { ctr := pb.ctr, next := pb.next, prev := [] }
    have hk3_val : key3.toNat = 26 := by rw [hk3]; decide
    refine e2ar_ed_key_some_step (iwt := .lengthDelimited) hVarintCall hgt3 hsp_align hcur3_le
      hcur3_lt hcur3_suf hd_k3 (by rw [hk3_val]; decide) (by rw [hk3_val]; decide)
      (by rw [hk3_val]; decide) ?_
      hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hinv2
    intro s3' hpc3' hrun3' hsp3' htr3' hx0_3' hx1_3' hx19_3' hx20_3' hx21_3' hx22_3' hcs3' hinv3'
    have hx1_eq : BitVec.ofNat 64 (key3.toNat / 8) = 3#64 := by rw [hk3_val]
    rw [hx1_eq] at hx1_3'
    have hrest3_le_cur3 : rest3.length ≤ cur3.length := Nat.le_of_lt (decodeVarint_length hd_k3)
    refine SepWPp.weaken_pre
      (P' := e2ar_edLoopPre A lim (M.stepEvents evs2 st0) s0 s3' x.msgPtr x.bufRef x.slot x.ptr
        (vecU8CapOkAt A.repAlloc x.msgPtr rest3.length m2.next ∗
          tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) m2.prev ∗
          ((x.msgPtr + 0x30#64) ↦₃₂ m2.ctr) ∗
          memRegion (x.msgPtr + 0x34#64) 4) x.bs rest3)
      (by
        dsimp only [e2ar_edLoopPre, m2]
        exact sepConj_mono_left (sepConj_mono_left
          (@vecU8CapOkAt_mono A.repAlloc x.msgPtr cur3.length rest3.length pb.next hrest3_le_cur3))) ?_
    refine e2ar_ed_tag3_zero_step (m := m2) hBytesCall hsp_align hrest3_le hrest3_lt hrest3_suf
      hmb3 hprev79 hFit_t3 ?_
      hpc3' hrun3' hsp3' htr3' hx0_3' hx1_3' hx19_3' hx20_3' hx21_3' hx22_3' hcs3' hinv3'
    intro evs3 s4' ht3 hpc4' hrun4' hsp4' htr4' hx19_4' hx20_4' hx21_4' hx22_4' hcs4' hinv4'
    have hm2_eq : ({ m2 with prev := pb.prev } : EpochDirectionPB) = pb := by cases pb; rfl
    rw [hm2_eq]
    exact e2ar_ed_ret_exit (m := pb) (evs := evs2 ++ evs3) rfl hsp_align hro_le hro_suf hsome_ed
      (hPost (evs2 ++ evs3) (ht23_imp_tight evs3 ht3))
      (M.stepEvents_append evs2 evs3 st0).symm
      hpc4' hrun4' hsp4' htr4' hx21_4' hx22_4' hcs4'

/-- Code-loaded (`DecodeStateCalleeContractsClPlacedX`) tight Block `299`
(`EpochDirectionPB::merge`) producer on `blkPC_325`. -/
theorem e2ar_epochDirectionMerge_blk325_cl_ok_tight [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlacedX H_inner A lim ext) :
    tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext := by
  have hVarint299 : subroutine_ok
      ((blkPC_299).rebase (blkPl_299).base (Rust.withPanics ext)) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
      (ls_subroutine_ok_of_block (i := 299) (j := 325) hc.decodeVarint2)
  have hBytes299 : subroutine_ok
      ((blkPC_299).rebase (blkPl_299).base (Rust.withPanics ext)) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.bytesMerge3RawBudgetSpec A lim)) :=
    e2ar_ls_subroutine_ok_cro_of_block (i := 299) (j := 325)
      (e2ar_polyBytesMerge_of_signed hc.bytesMerge3)
  have hDom325 : subroutine_ok
      ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext)) (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl (e2ar_epochDirDomOnlySpec A lim)) :=
    e2ar_ls_subroutine_ok_cro_of_block (i := 325) (j := 299)
      (e2ar_epochDirDomOnly_cro_placed_ok hVarint299 hBytes299)
  refine subroutine_ok_intro fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hDom79 : tlb_EpochDirDom 79236 x
  · have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (e2ar_epochDirDomOnlySpec A lim)).pre (x, st0) s0 ∗ R := by
      obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
      dsimp only [withLsCodeRoLoaded, tlb_epochDirectionMergeTightSpecOfEnv,
        e2ar_epochDirDomOnlySpec] at hp ⊢
      rw [tlb_domHeap_of_dom hDom79] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcro, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hDom79, hp.1.2.2.2.2⟩, hp.2⟩
    exact subroutine_ok_apply_full hDom325 (x, st0) R hpc hrun hpre_dom hsp
  · have hpre_fb : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)).pre (x, st0) s0 ∗ R := by
      obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
      dsimp only [withLsCodeRoLoaded, tlb_epochDirectionMergeTightSpecOfEnv,
        epochDirectionMergeSpec, epochDirectionMergeSpecOfEnv] at hp ⊢
      rw [tlb_domHeap_of_not_dom hDom79] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcro, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      refine ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, ?_⟩, hp.2⟩
      exact fun evs he => hp.1.2.2.2.2 evs (Or.inr (Or.inr ⟨hDom79, he⟩))
    refine reaches_pc_mono
      (subroutine_ok_apply_full hc.epochDirectionMerge (x, st0) R hpc hrun hpre_fb hsp)
      (fun sf _ _ ⟨hpost, hcc⟩ => ⟨?_, hcc⟩)
    dsimp only [withLsCodeRoLoaded, tlb_epochDirectionMergeTightSpecOfEnv,
      epochDirectionMergeSpec, epochDirectionMergeSpecOfEnv] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 =>
          Entails.pure_right (Or.inr (Or.inr ⟨hDom79, epochDirectionMergePostEnv_imp_pre h1⟩))
            (Entails.refl _)))))) hpost

/-- Plain (`DecodeStateCalleeContractsPlacedX`) tight Block `299`
(`EpochDirectionPB::merge`) producer on `blkPC_325` (`tlb_epochDirectionMerge_blk325_ok_tight`). -/
theorem e2ar_epochDirectionMerge_blk325_ok_tight [LibsignalPlacement] {M : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsPlacedX H_inner A lim ext) :
    tlb_EpochDirectionMergeBlk325TightOkOf A lim 2 4 ext :=
  e2ar_epochDirectionMerge_blk325_cl_ok_tight (e2ar_contractsClPlacedX_of_placedX hc)

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesCountedR
