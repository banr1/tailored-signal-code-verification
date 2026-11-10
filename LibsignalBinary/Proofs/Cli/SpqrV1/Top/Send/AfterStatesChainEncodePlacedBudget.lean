/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainEncodePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainFieldsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainFields
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainPhase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `spqr::send` Phase 3d `Option<Chain>` Encoding (`+5604..+6140`)

Threads `RustCliAllocBudget` and `VmPreserved` through the `[LibsignalPlacement]` repeated
`ChainEpochPB` loop (`+5776..+5944`) and `Option<Chain>` encoding (`+5604..+6140`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainEncodePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedEntry spqrSendPlacedProg)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPl_427_ρ)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecAt vecBuf vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (ChainEpochPB ChainPB ChainParamsPB EpochDirectionPB PqRatchetState VersionNegotiationPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeInt32Field encodeMessage encodeOptMessage
   encodeRepeatedMessage encodeUint64Field encodeVarint)
open CryptoVerification.SpqrV1.ProtoRepr
  (ChainEpochPBGhost ChainPBGhost
   chainEpochPBAt chainEpochPBAt_eq_exists_pinned chainEpochPBEncodedLen
   chainEpochPBPinnedAt chainEpochPBSize chainLinksBodiesEncodedLen
   chainLinksFieldEncodedLen chainLinksVecPinnedAt chainPBEncodedLen
   chainPBPinnedAt optChainPBPinnedAt optChainParamsPBAt
   optEpochDirectionPBPinnedAt optVersionNegotiationPBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStatePBGhost StepInv bv_lsl7_sub_lsl4_eq_mul_112
   cap_beq_len_false_of_lt chainLinksBodiesEncodedLen_bounds chainPBEncodedLen_lt_of_state
   encodeMessage_epoch_3_eq encodeOptMessage_chain_some encodeToVecCalleeStackOf
   encodeVarint_length_pos noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   optChainCap optChainPB_encode_len_le optChainPBPinnedAt_eq optChainRest_cap_bounds
   optEpochDirCap optEpochDirRest_cap_bounds optEpochDirectionPBPinnedAt_eq
   optPqRatchetInnerPBPinnedAt pqRatchetStatePBEncodedLen
   pqRatchetStatePBPinnedAt vecU8At_expose_one vecU8At_pack_one withStepInv)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (chainEncodedLenPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeChainParamsExactSpecOf encodeEpochDirectionExactSpecOf encodeVarintExactSpecOf
   epochEncLenStackSpecOf etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudgetAux
  (sepWPp_extract_pure sepWPp_extract_vecU8At_bounds)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesVnEncodePlacedBudget
  (step_send_encode_varint_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainFieldsPlacedBudget
  (step_send_chain_currentEpoch_31eb8_placed step_send_chain_dir_31e84_placed
   step_send_chain_nextRoot_31f94_placed step_send_chain_params_32038_placed
   step_send_chain_push_tag_len_31e48_placed step_send_chain_sendEpoch_32000_placed
   step_send_encode_epochDirection_call_placed step_send_epoch_encLen_call_placed)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  spqrSendPlacedEntry blkPl_427_ρ

/-! ## 1. Pure Offset & Loop Arithmetic Helpers -/

omit [LibsignalPlacement] in
private theorem sp_1424_add_8 (sp : BitVec 64) : (sp + 1424#64) + 8#64 = sp + 1432#64 := by
  bv_omega

omit [LibsignalPlacement] in
private theorem sp_1424_add_16 (sp : BitVec 64) : (sp + 1424#64) + 16#64 = sp + 1440#64 := by
  bv_omega

omit [LibsignalPlacement] in
private theorem sp_4752_add_8 (sp : BitVec 64) : (sp + 4752#64) + 8#64 = sp + 4760#64 := by
  bv_omega

omit [LibsignalPlacement] in
private theorem sp_4752_add_16 (sp : BitVec 64) : (sp + 4752#64) + 16#64 = sp + 4768#64 := by
  bv_omega

omit [LibsignalPlacement] in
private theorem sp_4704_add_48 (sp : BitVec 64) : (sp + 4704#64) + 48#64 = sp + 4752#64 := by
  bv_omega

omit [LibsignalPlacement] in
private theorem send_arrayAt_epoch_cons (A : RustAlloc) (p : BitVec 64)
    (ep : ChainEpochPB) (rest : List ChainEpochPB) :
    arrayAt (fun e addr => chainEpochPBAt A addr e) 112 p (ep :: rest) =
      (chainEpochPBAt A p ep ∗
        arrayAt (fun e addr => chainEpochPBAt A addr e) 112 (p + 112#64) rest) := rfl

omit [LibsignalPlacement] in
private theorem send_vecBuf_epoch_eq_of_ne_zero (A : RustAlloc) {cap ptr : BitVec 64}
    (links : List ChainEpochPB) (hcne : cap ≠ 0) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr links =
      (⌜links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr links ∗
        memRegion (ptr + BitVec.ofNat 64 (links.length * 112)) ((cap.toNat - links.length) * 112)) := by
  unfold vecBuf; simp only [hcne, ↓reduceIte]

omit [LibsignalPlacement] in
private theorem send_mul_112_ofNat_beq_112_false {n : Nat} (hn : 2 ≤ n) (hlt : n * 112 < 2 ^ 64) :
    (BitVec.ofNat 64 (n * 112) == 112#64) = false := by
  have hne : BitVec.ofNat 64 (n * 112) ≠ 112#64 := by
    intro h
    have h1 : (BitVec.ofNat 64 (n * 112)).toNat = (112#64 : BitVec 64).toNat :=
      congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h1
    change n * 112 = 112 at h1
    omega
  exact beq_eq_false_iff_ne.mpr hne

omit [LibsignalPlacement] in
private theorem send_ofNat_beq_zero_false {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false ∧ (BitVec.ofNat 64 n != 0#64) = true := by
  have hne : BitVec.ofNat 64 n ≠ 0#64 := by
    intro h
    have h1 : (BitVec.ofNat 64 n).toNat = (0#64 : BitVec 64).toNat :=
      congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h1
    change n = 0 at h1
    omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-! ## 2. Repeated `ChainEpochPB` Loop (`+5776..+5944`) -/

/-- Step `spqrSendPlacedEntry + 5864#64 .. spqrSendPlacedEntry + 5804#64`:
encodes `ep.send` (`tag = 1`) and `ep.recv` (`tag = 2`), threading `A.pool lim σ0`. -/
theorem step_send_epoch_dirs_31f44_placed {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (cur_ptr sp cap ptr : BitVec 64) (g_ep : ChainEpochPBGhost) (ep : ChainEpochPB)
    (bs : List (BitVec 8))
    (hfit : bs.length + (encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send).length +
      (encodeOptMessage EpochDirectionPB.encodeRaw 2#32 ep.recv).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5864#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = cur_ptr) (hinv0 : StepInv s0 s)
    (hP : P = (chainEpochPBPinnedAt A.repAlloc g_ep cur_ptr ep ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5804#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = cur_ptr →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((chainEpochPBPinnedAt A.repAlloc g_ep cur_ptr ep ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            ((bs ++ encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send) ++
              encodeOptMessage EpochDirectionPB.encodeRaw 2#32 ep.recv) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP; dsimp only [chainEpochPBPinnedAt]
  suffices hrecv_step : ∀ (s1 : State),
      s1.pc = spqrSendPlacedEntry + 5892#64 → s1.status = .Running → s1.sp = sp → s1.trace = s0.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = cur_ptr →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 s1 →
      SepWPp (spqrSendPlacedProg ext) ret s1
        (((optEpochDirectionPBPinnedAt A.repAlloc g_ep.send cur_ptr ep.send ∗
          optEpochDirectionPBPinnedAt A.repAlloc g_ep.recv (cur_ptr + 0x38#64) ep.recv) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send) ∗
          A.pool lim σ0 s1 ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom by
    rw [optEpochDirectionPBPinnedAt_eq A.repAlloc g_ep.send cur_ptr ep.send]
    refine sepWPp_extract_pure
      ((optEpochDirCap g_ep.send ep.send + 1#64 == 0#64) = !ep.send.isSome ∧
       (optEpochDirCap g_ep.send ep.send + 1#64 != 0#64) = ep.send.isSome)
      (fun R' hm => by
        apply optEpochDirRest_cap_bounds (A := A.repAlloc) (g := g_ep.send) (p := cur_ptr)
          (R := (cur_ptr ↦₆₄ optEpochDirCap g_ep.send ep.send) ∗
            optEpochDirectionPBPinnedAt A.repAlloc g_ep.recv (cur_ptr + 0x38#64) ep.recv ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
            stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
      fun hsend_cap => ?_
    cases hsend : ep.send with
    | none =>
      rw [hsend] at hsend_cap; simp only [Option.isSome_none, Bool.not_false] at hsend_cap
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5892#64)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv
      refine SepWPp.weaken_pre
        (by rw [hsend, optEpochDirectionPBPinnedAt_eq A.repAlloc g_ep.send cur_ptr none,
                A.pool_of_vmPreserved hinv.2]
            dsimp only [encodeOptMessage]; rw [List.append_nil]; exact Entails.of_eq (by sep_ac_rfl))
        (hrecv_step _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
    | some d_send =>
      rw [hsend] at hsend_cap; simp only [Option.isSome_some, Bool.not_true] at hsend_cap
      have hfit_send :
          bs.length + (encodeMessage EpochDirectionPB.encodeRaw 1#32 d_send).length ≤ cap.toNat := by
        have h1 : encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send =
            encodeMessage EpochDirectionPB.encodeRaw 1#32 d_send := by rw [hsend]; rfl
        rw [h1] at hfit; omega
      dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
      apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 457)
      wp_steps
      apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv1
      refine step_send_encode_epochDirection_call_placed A lim σ0 hed_call
        1#32 cur_ptr (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5892#64) g_ep.send d_send bs
        hfit_send
        (F := optEpochDirectionPBPinnedAt A.repAlloc g_ep.recv (cur_ptr + 0x38#64) ep.recv ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [State.readReg32, arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
        (by rw [← optEpochDirectionPBPinnedAt_eq A.repAlloc g_ep.send cur_ptr (some d_send),
                A.pool_of_vmPreserved hinv1.2]
            dsimp only [optEpochDirectionPBPinnedAt]; sep_ac_rfl) ?_
      intro s1 hpcs1 hruns1 hsps1 htrs1 hcss1 hinv_s1
      rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, _, hs1_27, hs1_28, hs1_fp, _⟩
      simp only [arm64_norm, hx24] at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_27 hs1_28 hs1_fp
      refine SepWPp.weaken_pre
        (by rw [hsend]; dsimp only [optEpochDirectionPBPinnedAt, encodeOptMessage]
            exact Entails.of_eq (by sep_ac_rfl))
        (hrecv_step s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_27 hs1_28 hs1_fp hinv_s1)
  intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_27 hs1_28 hs1_fp hinv_s1
  rw [optEpochDirectionPBPinnedAt_eq A.repAlloc g_ep.recv (cur_ptr + 0x38#64) ep.recv]
  refine sepWPp_extract_pure
    ((optEpochDirCap g_ep.recv ep.recv + 1#64 == 0#64) = !ep.recv.isSome ∧
     (optEpochDirCap g_ep.recv ep.recv + 1#64 != 0#64) = ep.recv.isSome)
    (fun R' hm => by
      apply optEpochDirRest_cap_bounds (A := A.repAlloc) (g := g_ep.recv) (p := cur_ptr + 0x38#64)
        (R := optEpochDirectionPBPinnedAt A.repAlloc g_ep.send cur_ptr ep.send ∗
          ((cur_ptr + 0x38#64) ↦₆₄ optEpochDirCap g_ep.recv ep.recv) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send) ∗
          A.pool lim σ0 s1 ∗ stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
    fun hrecv_cap => ?_
  cases hrecv : ep.recv with
  | none =>
    rw [hrecv] at hrecv_cap; simp only [Option.isSome_none, Bool.not_false] at hrecv_cap
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5804#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    refine SepWPp.weaken_pre
      (by dsimp only [chainEpochPBPinnedAt]
          rw [hrecv, optEpochDirectionPBPinnedAt_eq A.repAlloc g_ep.recv (cur_ptr + 0x38#64) none,
              A.pool_of_vmPreserved hinv2.2]
          dsimp only [encodeOptMessage]; rw [List.append_nil]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s1.trans hinv2.1))
  | some d_recv =>
    rw [hrecv] at hrecv_cap; simp only [Option.isSome_some, Bool.not_true] at hrecv_cap
    have hfit_recv :
        (bs ++ encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send).length +
          (encodeMessage EpochDirectionPB.encodeRaw 2#32 d_recv).length ≤ cap.toNat := by
      rw [List.length_append]
      have h1 : encodeOptMessage EpochDirectionPB.encodeRaw 2#32 ep.recv =
          encodeMessage EpochDirectionPB.encodeRaw 2#32 d_recv := by rw [hrecv]; rfl
      rw [h1] at hfit; omega
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 457)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    refine step_send_encode_epochDirection_call_placed A lim σ0 hed_call
      2#32 (cur_ptr + 0x38#64) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5920#64) g_ep.recv d_recv
      (bs ++ encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send)
      hfit_recv
      (F := optEpochDirectionPBPinnedAt A.repAlloc g_ep.send cur_ptr ep.send ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [State.readReg32, arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv_s1.trans hinv2.1)
      (by rw [← optEpochDirectionPBPinnedAt_eq A.repAlloc g_ep.recv (cur_ptr + 0x38#64) (some d_recv),
              A.pool_of_vmPreserved hinv2.2]
          dsimp only [optEpochDirectionPBPinnedAt]; sep_ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, _, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_27, hs1_28, hs1_fp]
      at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_27 hs2_28 hs2_fp
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5804#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv3
    refine SepWPp.weaken_pre
      (by dsimp only [chainEpochPBPinnedAt]; rw [hrecv, A.pool_of_vmPreserved hinv3.2]
          dsimp only [optEpochDirectionPBPinnedAt, encodeOptMessage]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2.trans hinv3.1))

/-- Step `spqrSendPlacedEntry + 5816#64 .. spqrSendPlacedEntry + 5804#64`:
encodes one `ChainEpochPB` element (`tag = 3#32`), threading `A.pool lim σ0`. -/
theorem step_send_chain_links_one_31f14_placed {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (cur_ptr sp cap ptr : BitVec 64) (ep : ChainEpochPB) (bs : List (BitVec 8))
    (hep_len : chainEpochPBEncodedLen ep < 2 ^ 64)
    (hfit : bs.length + (encodeMessage ChainEpochPB.encodeRaw 3#32 ep).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5816#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = cur_ptr) (hx25 : s.readReg64 .x25 = 0x1a#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainEpochPBAt A.repAlloc cur_ptr ep ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5804#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = cur_ptr →
      sm.readReg64 .x25 = 0x1a#64 → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((chainEpochPBAt A.repAlloc cur_ptr ep ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeMessage ChainEpochPB.encodeRaw 3#32 ep) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  rw [chainEpochPBAt_eq_exists_pinned A.repAlloc cur_ptr ep]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g_ep => ?_
  have hfit_all :
      bs.length + 1 + (encodeVarint (BitVec.ofNat 64 (chainEpochPBEncodedLen ep))).length +
        (encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send).length +
        (encodeOptMessage EpochDirectionPB.encodeRaw 2#32 ep.recv).length ≤ cap.toNat := by
    rw [encodeMessage_epoch_3_eq ep] at hfit
    simp only [List.length_append, List.length_singleton] at hfit; omega
  have hlt_tag : bs.length < cap.toNat := by
    have := encodeVarint_length_pos (BitVec.ofNat 64 (chainEpochPBEncodedLen ep)); omega
  refine sepWPp_extract_vecU8At_bounds (v := sp + 1424#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := chainEpochPBPinnedAt A.repAlloc g_ep cur_ptr ep ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F) (by sep_ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt_tag hcap
  have h1432 := sp_1424_add_8 sp
  have h1440 := sp_1424_add_16 sp
  rw [vecU8At_expose_one A.repAlloc (sp + 1424#64) cap ptr bs hlt_tag hcap hptr, h1432, h1440]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 478)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpool1 : A.pool lim σ0 s = A.pool lim σ0 _ := (A.pool_of_vmPreserved hinv1.2).symm
    have hpack := vecU8At_pack_one A.repAlloc (sp + 1424#64) cap ptr bs 0x1a#8 hlt_tag hcap hptr
    simp only [arm64_norm, h1432, h1440] at hpack
    refine step_send_epoch_encLen_call_placed A lim σ0 hep_call
      cur_ptr sp (spqrSendPlacedEntry + 5856#64) g_ep ep hep_len
      (F := vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ [0x1a#8]) ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by simp only [arm64_norm, hx25, ← hpack, hpool1]; sep_ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hx0s1 _hvm_s1 hcss1 hinv_s1
    rcases hcss1 with ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, _, hs1_27, hs1_28, hs1_fp, _⟩
    simp only [arm64_norm, hx24, hx25] at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_27 hs1_28 hs1_fp
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 451)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv2
    refine step_send_encode_varint_call_placed A lim σ0 hvarint
      (BitVec.ofNat 64 (chainEpochPBEncodedLen ep)) (sp + 1424#64) cap ptr sp (spqrSendPlacedEntry + 5864#64)
      (bs ++ [0x1a#8]) (by simp only [List.length_append, List.length_singleton]; omega)
      (F := chainEpochPBPinnedAt A.repAlloc g_ep cur_ptr ep ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s1.trans hinv2.1)
      (by rw [A.pool_of_vmPreserved hinv2.2]; sep_ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hcss2 hinv_s2
    rcases hcss2 with ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, _, hs2_27, hs2_28, hs2_fp, _⟩
    simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_27, hs1_28, hs1_fp]
      at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_24 hs2_25 hs2_27 hs2_28 hs2_fp
    refine step_send_epoch_dirs_31f44_placed A lim σ0 ext hed_call
      cur_ptr sp cap ptr g_ep ep
      ((bs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (chainEpochPBEncodedLen ep)))
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F) hpcs2 hruns2 hsps2 htrs2 hs2_24 hinv_s2 (by sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm24 hm25 hm27 hm28 hmfp hinv_m
    rw [hs2_19] at hm19; rw [hs2_20] at hm20; rw [hs2_21] at hm21; rw [hs2_22] at hm22
    rw [hs2_23] at hm23; rw [hs2_25] at hm25; rw [hs2_27] at hm27; rw [hs2_28] at hm28; rw [hs2_fp] at hmfp
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm22 hm23 hm24 hm25 hm27 hm28 hmfp hinv_m)
    rw [chainEpochPBAt_eq_exists_pinned A.repAlloc cur_ptr ep, encodeMessage_epoch_3_eq ep]
    simp only [sepExists_sepConj_left, List.append_assoc]
    exact Entails.sepExists_right g_ep (Entails.of_eq (by sep_ac_rfl))

/-- Base case (`rest = []`) of the repeated `ChainEpochPB` loop (`+5816 .. +5944`),
threading `A.pool lim σ0`. -/
theorem step_send_chain_links_nil_31f14_placed {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 : State}
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (ep : ChainEpochPB) (cur_ptr : BitVec 64) (bs : List (BitVec 8)) (s : State) (P F : SepProp)
    (hbod : chainLinksBodiesEncodedLen [ep] < 2 ^ 64)
    (hmul : [ep].length * 112 < 2 ^ 64)
    (hfit : bs.length + (encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 [ep]).length ≤ cap.toNat)
    (hpc : s.pc = spqrSendPlacedEntry + 5816#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ([ep].length * 112))
    (hx24 : s.readReg64 .x24 = cur_ptr) (hx25 : s.readReg64 .x25 = 0x1a#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 cur_ptr [ep] ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5944#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 cur_ptr [ep] ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 [ep]) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have ⟨hep_len, _⟩ := chainLinksBodiesEncodedLen_bounds ep [] hbod
  have hrep_nil : encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 [ep] =
      encodeMessage ChainEpochPB.encodeRaw 3#32 ep := by
    dsimp only [encodeRepeatedMessage, List.foldr]
    exact List.append_nil _
  rw [hrep_nil] at hfit
  dsimp only [arrayAt]
  refine step_send_chain_links_one_31f14_placed A lim σ0 ext hep_call hvarint hed_call
    cur_ptr sp cap ptr ep bs hep_len hfit halign
    (F := emp ∗ F) hpc hrun hsp htr hx24 hx25 hinv0 (by sep_ac_rfl) ?_
  intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_27 hs1_28 hs1_fp hinv1
  rw [hx22] at hs1_22
  dsimp only [List.length_cons, List.length_nil] at hs1_22
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5944#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv2
  refine SepWPp.weaken_pre
    (by rw [hrep_nil, A.pool_of_vmPreserved hinv2.2]; dsimp only [arrayAt]
        exact Entails.of_eq (by sep_ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv1.trans hinv2.1))

omit [LibsignalPlacement] in
private theorem send_mul_112_cons_sub (ep ep2 : ChainEpochPB) (rest2 : List ChainEpochPB)
    (hmul : (ep :: ep2 :: rest2).length * 112 < 2 ^ 64) :
    (ep2 :: rest2).length * 112 < 2 ^ 64 ∧
      BitVec.ofNat 64 ((ep :: ep2 :: rest2).length * 112) - 112#64 =
        BitVec.ofNat 64 ((ep2 :: rest2).length * 112) ∧
      (BitVec.ofNat 64 ((ep :: ep2 :: rest2).length * 112) == 112#64) = false := by
  have hmul_eq : (ep :: ep2 :: rest2).length * 112 = (ep2 :: rest2).length * 112 + 112 := by
    simp only [List.length_cons]; omega
  refine ⟨by omega, ?_, send_mul_112_ofNat_beq_112_false (by simp) hmul⟩
  rw [hmul_eq, BitVec.ofNat_add]; bv_omega

omit [LibsignalPlacement] in
private theorem send_chain_links_cons_fit {cap_nat : Nat} (bs l1 l2 : List (BitVec 8))
    (h : bs.length + (l1 ++ l2).length ≤ cap_nat) :
    bs.length + l1.length ≤ cap_nat ∧ (bs ++ l1).length + l2.length ≤ cap_nat := by
  simp only [List.length_append] at h ⊢
  omega

/-- Single inductive step (`rest = ep2 :: rest2`) of the repeated `ChainEpochPB` loop (`+5816 .. +5816`),
threading `A.pool lim σ0`. -/
theorem step_send_chain_links_cons_31f14_placed {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 : State}
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (ep ep2 : ChainEpochPB) (rest2 : List ChainEpochPB)
    (cur_ptr : BitVec 64) (bs : List (BitVec 8)) (s : State) (P F : SepProp)
    (hbod : chainLinksBodiesEncodedLen (ep :: ep2 :: rest2) < 2 ^ 64)
    (hmul : (ep :: ep2 :: rest2).length * 112 < 2 ^ 64)
    (hfit : bs.length + (encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep :: ep2 :: rest2)).length ≤ cap.toNat)
    (hpc : s.pc = spqrSendPlacedEntry + 5816#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ((ep :: ep2 :: rest2).length * 112))
    (hx24 : s.readReg64 .x24 = cur_ptr) (hx25 : s.readReg64 .x25 = 0x1a#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 cur_ptr (ep :: ep2 :: rest2) ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (ih_step : ∀ (s' : State) (P' : SepProp),
      chainLinksBodiesEncodedLen (ep2 :: rest2) < 2 ^ 64 →
      (ep2 :: rest2).length * 112 < 2 ^ 64 →
      (bs ++ encodeMessage ChainEpochPB.encodeRaw 3#32 ep).length +
        (encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep2 :: rest2)).length ≤ cap.toNat →
      s'.pc = spqrSendPlacedEntry + 5816#64 → s'.status = .Running → s'.sp = sp → s'.trace = s0.trace →
      s'.readReg64 .x22 = BitVec.ofNat 64 ((ep2 :: rest2).length * 112) →
      s'.readReg64 .x24 = cur_ptr + 112#64 → s'.readReg64 .x25 = 0x1a#64 →
      StepInv s0 s' →
      P' = (arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 (cur_ptr + 112#64) (ep2 :: rest2) ∗
        vecU8At A.repAlloc (sp + 1424#64) cap ptr (bs ++ encodeMessage ChainEpochPB.encodeRaw 3#32 ep) ∗
        A.pool lim σ0 s' ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗
        (chainEpochPBAt A.repAlloc cur_ptr ep ∗ F) →
      (∀ sm : State,
        sm.pc = spqrSendPlacedEntry + 5944#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
        sm.readReg64 .x19 = s'.readReg64 .x19 → sm.readReg64 .x20 = s'.readReg64 .x20 →
        sm.readReg64 .x21 = s'.readReg64 .x21 → sm.readReg64 .x23 = s'.readReg64 .x23 →
        sm.readReg64 .x27 = s'.readReg64 .x27 → sm.readReg64 .x28 = s'.readReg64 .x28 →
        sm.readReg64 .fp = s'.readReg64 .fp → StepInv s0 sm →
        SepWPp (spqrSendPlacedProg ext) ret sm
          ((arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 (cur_ptr + 112#64) (ep2 :: rest2) ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr
              ((bs ++ encodeMessage ChainEpochPB.encodeRaw 3#32 ep) ++
                encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep2 :: rest2)) ∗
            A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗
            (chainEpochPBAt A.repAlloc cur_ptr ep ∗ F))
          Q Qp oom) →
      SepWPp (spqrSendPlacedProg ext) ret s' P' Q Qp oom)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5944#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 cur_ptr (ep :: ep2 :: rest2) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep :: ep2 :: rest2)) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have ⟨hep_len, hbod_rest⟩ := chainLinksBodiesEncodedLen_bounds ep (ep2 :: rest2) hbod
  have hrep_cons : encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep :: ep2 :: rest2) =
      encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++
        encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep2 :: rest2) := rfl
  have ⟨hfit_one, hfit_rest⟩ := send_chain_links_cons_fit bs
    (encodeMessage ChainEpochPB.encodeRaw 3#32 ep)
    (encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep2 :: rest2))
    (hrep_cons ▸ hfit)
  have ⟨hmul_rest, hsub_x22, hne_112⟩ := send_mul_112_cons_sub ep ep2 rest2 hmul
  rw [send_arrayAt_epoch_cons A.repAlloc cur_ptr ep (ep2 :: rest2)]
  refine step_send_chain_links_one_31f14_placed A lim σ0 ext hep_call hvarint hed_call
    cur_ptr sp cap ptr ep bs hep_len hfit_one halign
    (F := arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 (cur_ptr + 112#64) (ep2 :: rest2) ∗ F)
    hpc hrun hsp htr hx24 hx25 hinv0 (by sep_ac_rfl) ?_
  intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_24 hs1_25 hs1_27 hs1_28 hs1_fp hinv1
  rw [hx22] at hs1_22
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
  apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5816#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv2
  refine ih_step _ _ hbod_rest hmul_rest hfit_rest
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv1.trans hinv2.1)
    (by rw [A.pool_of_vmPreserved hinv2.2]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm27 hm28 hmfp hinv_m
  simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_23, hs1_27, hs1_28, hs1_fp]
    at hm19 hm20 hm21 hm23 hm27 hm28 hmfp
  refine SepWPp.weaken_pre
    (by rw [hrep_cons, ← List.append_assoc, send_arrayAt_epoch_cons A.repAlloc cur_ptr ep (ep2 :: rest2)]
        exact Entails.of_eq (by sep_ac_rfl))
    (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm27 hm28 hmfp hinv_m)

/-- Inductive loop theorem (`+5816 .. +5944`) over non-empty `ep :: rest`,
threading `A.pool lim σ0`. -/
theorem step_send_chain_links_loop_31f14_placed {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 : State}
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (rest : List ChainEpochPB) :
    ∀ (ep : ChainEpochPB) (cur_ptr : BitVec 64) (bs : List (BitVec 8)) (s : State) (P F : SepProp),
      chainLinksBodiesEncodedLen (ep :: rest) < 2 ^ 64 →
      (ep :: rest).length * 112 < 2 ^ 64 →
      bs.length + (encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep :: rest)).length ≤ cap.toNat →
      s.pc = spqrSendPlacedEntry + 5816#64 → s.status = .Running → s.sp = sp → s.trace = s0.trace →
      s.readReg64 .x22 = BitVec.ofNat 64 ((ep :: rest).length * 112) →
      s.readReg64 .x24 = cur_ptr → s.readReg64 .x25 = 0x1a#64 →
      StepInv s0 s →
      P = (arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 cur_ptr (ep :: rest) ∗
        vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
        stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F →
      (∀ sm : State,
        sm.pc = spqrSendPlacedEntry + 5944#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
        sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
        sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
        sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
        sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
        SepWPp (spqrSendPlacedProg ext) ret sm
          ((arrayAt (fun e addr => chainEpochPBAt A.repAlloc addr e) 112 cur_ptr (ep :: rest) ∗
            vecU8At A.repAlloc (sp + 1424#64) cap ptr
              (bs ++ encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep :: rest)) ∗
            A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
          Q Qp oom) →
      SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  induction rest with
  | nil =>
    intro ep cur_ptr bs s P F hbod hmul hfit hpc hrun hsp htr hx22 hx24 hx25 hinv0 hP hnext
    exact step_send_chain_links_nil_31f14_placed A lim σ0 ext hep_call hvarint hed_call
      sp cap ptr halign ep cur_ptr bs s P F hbod hmul hfit hpc hrun hsp htr hx22 hx24 hx25 hinv0 hP hnext
  | cons ep2 rest2 ih =>
    intro ep cur_ptr bs s P F hbod hmul hfit hpc hrun hsp htr hx22 hx24 hx25 hinv0 hP hnext
    exact step_send_chain_links_cons_31f14_placed A lim σ0 ext hep_call hvarint hed_call
      sp cap ptr halign ep ep2 rest2 cur_ptr bs s P F hbod hmul hfit
      hpc hrun hsp htr hx22 hx24 hx25 hinv0 hP
      (fun s' P' => ih ep2 (cur_ptr + 112#64) (bs ++ encodeMessage ChainEpochPB.encodeRaw 3#32 ep)
        s' P' (chainEpochPBAt A.repAlloc cur_ptr ep ∗ F))
      hnext

/-- Step `spqrSendPlacedEntry + 5776#64 .. spqrSendPlacedEntry + 5944#64`:
encodes `ch.links` (`encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links`),
threading `A.pool lim σ0`. -/
theorem step_send_chain_links_31eec_placed {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (sp cap ptr : BitVec 64) (g : ChainPBGhost) (ch : ChainPB) (bs : List (BitVec 8))
    (hch_len : chainPBEncodedLen ch < 2 ^ 64)
    (hfit : bs.length + (encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5776#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainPBPinnedAt A.repAlloc g (sp + 4752#64) ch ∗
      vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
      stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 5944#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .fp = s.readReg64 .fp → StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((chainPBPinnedAt A.repAlloc g (sp + 4752#64) ch ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr
            (bs ++ encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have h4760 := sp_4752_add_8 sp
  have h4768 := sp_4752_add_16 sp
  dsimp only [chainPBPinnedAt, chainLinksVecPinnedAt, chainEpochPBSize, vecAt, vecHeader]
  rw [h4760, h4768]
  cases hlinks : ch.links with
  | nil =>
    have hrep_empty : encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 [] = [] := rfl
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5944#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt, chainLinksVecPinnedAt, chainEpochPBSize, vecAt, vecHeader]
          rw [h4760, h4768, hlinks, hrep_empty, List.append_nil, A.pool_of_vmPreserved hinv.2]
          dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
  | cons ep rest =>
    rw [hlinks] at hfit
    have hbod_lt : chainLinksBodiesEncodedLen (ep :: rest) < 2 ^ 64 := by
      unfold chainPBEncodedLen chainLinksFieldEncodedLen at hch_len
      rw [hlinks] at hch_len; omega
    refine sepWPp_extract_pure
      ((ep :: rest).length ≤ g.links.cap.toNat ∧ g.links.cap.toNat * 112 < 2 ^ 63 ∧ g.links.cap ≠ 0)
      (fun R' hm => by
        have hm' : s.mem ⊨ vecBuf A.repAlloc 112 8 (fun ep addr => chainEpochPBAt A.repAlloc addr ep) g.links.cap g.links.ptr (ep :: rest) ∗
            ((((sp + 4752#64) ↦₆₄ g.links.cap) ∗ ((sp + 4760#64) ↦₆₄ g.links.ptr) ∗
              ((sp + 4768#64) ↦₆₄ BitVec.ofNat 64 (ep :: rest).length)) ∗
             vecU8At A.repAlloc (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
             ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
             ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
             optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
             ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction) ∗
             vecU8At A.repAlloc (sp + 1424#64) cap ptr bs ∗ A.pool lim σ0 s ∗
             stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
          convert hm using 1; sep_ac_rfl
        unfold vecBuf at hm'
        rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
        have hle := hm'.1.1
        have hmul := hm'.1.2.1
        have hcne : g.links.cap ≠ 0 := by
          intro hc0; rw [hc0] at hle
          change (ep :: rest).length ≤ 0 at hle
          simp only [List.length_cons] at hle; omega
        exact ⟨hle, hmul, hcne⟩)
      fun ⟨hle_cap, hmul_cap, hcne⟩ => ?_
    have ⟨hlen_ne, hlen_bne⟩ := send_ofNat_beq_zero_false (by simp) (by omega : (ep :: rest).length < 2 ^ 64)
    have ⟨hmul_eq1, hmul_eq2, hmul_eq3, hmul_eq4⟩ := bv_lsl7_sub_lsl4_eq_mul_112 (ep :: rest).length
    rw [send_vecBuf_epoch_eq_of_ne_zero A.repAlloc (ep :: rest) hcne]
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5816#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    refine step_send_chain_links_loop_31f14_placed A lim σ0 ext hep_call hvarint hed_call
      sp cap ptr halign rest ep g.links.ptr bs _ _
      ((((sp + 4752#64) ↦₆₄ g.links.cap) ∗ ((sp + 4760#64) ↦₆₄ g.links.ptr) ∗
        ((sp + 4768#64) ↦₆₄ BitVec.ofNat 64 (ep :: rest).length) ∗
        (⌜(ep :: rest).length ≤ g.links.cap.toNat ∧ g.links.cap.toNat * 112 < 2 ^ 63 ∧ g.links.ptr ≠ 0⌝ ∗
          A.repAlloc.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
          memRegion (g.links.ptr + BitVec.ofNat 64 ((ep :: rest).length * 112))
            ((g.links.cap.toNat - (ep :: rest).length) * 112)) ∗
        vecU8At A.repAlloc (sp + 4752#64 + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ∗
        ((sp + 4752#64 + 0x30#64) ↦₆₄ ch.currentEpoch) ∗
        ((sp + 4752#64 + 0x38#64) ↦₆₄ ch.sendEpoch) ∗
        optChainParamsPBAt (sp + 4752#64 + 0x40#64) ch.params ∗
        ((sp + 4752#64 + 0x4c#64) ↦₃₂ ch.direction)) ∗ F)
      hbod_lt (by omega) hfit
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by rw [A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm27 hm28 hmfp hinv_m
    simp only [arm64_norm] at hm19 hm20 hm21 hm23 hm27 hm28 hmfp
    refine SepWPp.weaken_pre
      (by dsimp only [chainPBPinnedAt, chainLinksVecPinnedAt, chainEpochPBSize, vecAt, vecHeader]
          rw [h4760, h4768, hlinks, send_vecBuf_epoch_eq_of_ne_zero A.repAlloc (ep :: rest) hcne]
          exact Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm htrm hm19 hm20 hm21 hm23 hm27 hm28 hmfp hinv_m)

/-! ## 3. Full Phase 3d Theorem: `step_send_chain_31e40_placed` (`+5604..+6140`) -/

/-- Step `spqrSendPlacedEntry + 5604#64 .. spqrSendPlacedEntry + 6140#64`:
encodes `st.chain` (`encodeOptMessage ChainPB.encodeRaw 2#32 st.chain`) into
`vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr bs`,
preserves `x25 = optChainCap g.chain st.chain`, and threads `A.pool lim σ0`. -/
theorem step_send_chain_31e40_placed {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (σ0 : M.σ)
    (ext : String → Option (State → State))
    {s0 s : State}
    (hChainLen : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 485)
      (withStepInv s0 (chainEncodedLenPinnedSpec A.repAlloc)))
    (hep_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 478)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hvarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 451)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (spqrSendPlacedProg ext) (lsρ "memcpy") etvMemcpyRegionSpec)
    (hed_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 457)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (hcp_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 453)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (sp ptr : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = spqrSendPlacedEntry + 5604#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = optChainCap g.chain st.chain)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
      ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
      vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
        (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation) ∗
      A.pool lim σ0 s ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = spqrSendPlacedEntry + 6140#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = optChainCap g.chain st.chain → sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrSendPlacedProg ext) ret sm
        ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) st ∗
          ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          vecU8At A.repAlloc (sp + 1424#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr
            (encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation ++
              encodeOptMessage ChainPB.encodeRaw 2#32 st.chain) ∗
          A.pool lim σ0 sm ∗ stackAt sp (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (spqrSendPlacedProg ext) ret s P Q Qp oom := by
  subst hP
  have h4752 := sp_4704_add_48 sp
  let cap := BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)
  let bs0 := encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation
  have hcap_toNat : cap.toNat = pqRatchetStatePBEncodedLen st := by
    dsimp only [cap]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_extract_pure
    ((optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
     (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome)
    (fun R' hm => by
      rw [pqRatchetStatePBPinnedAt, h4752, optChainPBPinnedAt_eq A.repAlloc g.chain (sp + 4752#64) st.chain] at hm
      apply optChainRest_cap_bounds (A := A.repAlloc) (g := g.chain) (p := sp + 4752#64)
        (R := optVersionNegotiationPBPinnedAt A.repAlloc g.vn (sp + 4704#64) st.versionNegotiation ∗
          ((sp + 4752#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          optPqRatchetInnerPBPinnedAt A.repAlloc g.inner ((sp + 4704#64) + 128#64) st.inner ∗
          ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗
          vecU8At A.repAlloc (sp + 1424#64) cap ptr bs0 ∗ A.pool lim σ0 s ∗
          stackAt sp (encodeToVecCalleeStackOf resStack) ∗ F ∗ R')
      exact Satisfies.mono (Entails.of_eq (by dsimp +zetaDelta only [cap, bs0]; sep_ac_rfl)) hm)
    fun hch_cap => ?_
  cases hch : st.chain with
  | none =>
    rw [hch] at hch_cap hx25; simp only [Option.isSome_none, Bool.not_false] at hch_cap
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 6140#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv
    refine SepWPp.weaken_pre
      (by rw [hch, A.pool_of_vmPreserved hinv.2]; dsimp +zetaDelta only [encodeOptMessage, cap, bs0]
          rw [List.append_nil]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [hch]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv.1))
  | some ch =>
    rw [hch] at hch_cap hx25; simp only [Option.isSome_some, Bool.not_true] at hch_cap
    have ⟨hch_len, _, _⟩ := chainPBEncodedLen_lt_of_state hch hlen
    have hch_fit_all :
        bs0.length + (encodeOptMessage ChainPB.encodeRaw 2#32 (some ch)).length ≤ cap.toNat := by
      rw [hcap_toNat, ← hch]; exact optChainPB_encode_len_le st
    rw [encodeOptMessage_chain_some ch] at hch_fit_all
    simp only [List.length_append, List.length_singleton] at hch_fit_all
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry] at *
    apply sepWPp_of_sepWP_cs_vm (mid := spqrSendPlacedEntry + 5612#64)
    wp_steps
    apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    let F_rest : SepProp :=
      optVersionNegotiationPBPinnedAt A.repAlloc g.vn (sp + 4704#64) st.versionNegotiation ∗
        optPqRatchetInnerPBPinnedAt A.repAlloc g.inner ((sp + 4704#64) + 128#64) st.inner ∗
        ((sp + 16#64) ↦₆₄ optChainCap g.chain st.chain) ∗ F
    refine step_send_chain_push_tag_len_31e48_placed hres A lim σ0 ext hChainLen hvarint
      sp cap ptr g.chain ch bs0 hch_len (by omega) halign
      (F := F_rest)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by unfold pqRatchetStatePBPinnedAt
          rw [h4752, hch, A.pool_of_vmPreserved hinv1.2]
          dsimp +zetaDelta only [optChainPBPinnedAt, F_rest, cap, bs0]; sep_ac_rfl) ?_
    intro s1 hpcs1 hruns1 hsps1 htrs1 hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_27 hs1_28 hs1_fp hinv_s1
    simp only [arm64_norm] at hs1_19 hs1_20 hs1_21 hs1_22 hs1_23 hs1_27 hs1_28 hs1_fp
    refine step_send_chain_dir_31e84_placed A lim σ0 ext hvarint
      sp cap ptr g.chain ch
      ((bs0 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch)))
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs1 hruns1 hsps1 htrs1 hinv_s1 (by sep_ac_rfl) ?_
    intro s2 hpcs2 hruns2 hsps2 htrs2 hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_27 hs2_28 hs2_fp hinv_s2
    rw [hs1_19] at hs2_19; rw [hs1_20] at hs2_20; rw [hs1_21] at hs2_21; rw [hs1_23] at hs2_23
    rw [hs1_27] at hs2_27; rw [hs1_28] at hs2_28; rw [hs1_fp] at hs2_fp
    refine step_send_chain_currentEpoch_31eb8_placed A lim σ0 ext hvarint
      sp cap ptr g.chain ch
      (((bs0 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        encodeInt32Field 1#32 ch.direction)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs2 hruns2 hsps2 htrs2 hinv_s2 (by sep_ac_rfl) ?_
    intro s3 hpcs3 hruns3 hsps3 htrs3 hs3_19 hs3_20 hs3_21 hs3_22 hs3_23 hs3_27 hs3_28 hs3_fp hinv_s3
    rw [hs2_19] at hs3_19; rw [hs2_20] at hs3_20; rw [hs2_21] at hs3_21; rw [hs2_23] at hs3_23
    rw [hs2_27] at hs3_27; rw [hs2_28] at hs3_28; rw [hs2_fp] at hs3_fp
    refine step_send_chain_links_31eec_placed A lim σ0 ext hep_call hvarint hed_call
      sp cap ptr g.chain ch
      ((((bs0 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        encodeInt32Field 1#32 ch.direction) ++ encodeUint64Field 2#32 ch.currentEpoch)
      hch_len (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs3 hruns3 hsps3 htrs3 hinv_s3 (by sep_ac_rfl) ?_
    intro s4 hpcs4 hruns4 hsps4 htrs4 hs4_19 hs4_20 hs4_21 hs4_23 hs4_27 hs4_28 hs4_fp hinv_s4
    rw [hs3_19] at hs4_19; rw [hs3_20] at hs4_20; rw [hs3_21] at hs4_21; rw [hs3_23] at hs4_23
    rw [hs3_27] at hs4_27; rw [hs3_28] at hs4_28; rw [hs3_fp] at hs4_fp
    refine step_send_chain_nextRoot_31f94_placed A lim σ0 ext hvarint hmemcpy
      sp cap ptr g.chain ch
      (((((bs0 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        encodeInt32Field 1#32 ch.direction) ++ encodeUint64Field 2#32 ch.currentEpoch) ++
        encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs4 hruns4 hsps4 htrs4 hinv_s4 (by sep_ac_rfl) ?_
    intro s5 hpcs5 hruns5 hsps5 htrs5 hs5_19 hs5_20 hs5_21 hs5_23 hs5_27 hs5_28 hs5_fp hinv_s5
    rw [hs4_19] at hs5_19; rw [hs4_20] at hs5_20; rw [hs4_21] at hs5_21; rw [hs4_23] at hs5_23
    rw [hs4_27] at hs5_27; rw [hs4_28] at hs5_28; rw [hs4_fp] at hs5_fp
    let F_no16 : SepProp :=
      optVersionNegotiationPBPinnedAt A.repAlloc g.vn (sp + 4704#64) st.versionNegotiation ∗
        optPqRatchetInnerPBPinnedAt A.repAlloc g.inner ((sp + 4704#64) + 128#64) st.inner ∗ F
    refine step_send_chain_sendEpoch_32000_placed A lim σ0 ext hvarint
      sp cap ptr (optChainCap g.chain st.chain) g.chain ch
      ((((((bs0 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        encodeInt32Field 1#32 ch.direction) ++ encodeUint64Field 2#32 ch.currentEpoch) ++
        encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links) ++
        encodeBytesField 4#32 ch.nextRoot)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_no16) hpcs5 hruns5 hsps5 htrs5 hinv_s5
      (by dsimp +zetaDelta only [F_rest, F_no16]; sep_ac_rfl) ?_
    intro s6 hpcs6 hruns6 hsps6 htrs6 hs6_19 hs6_20 hs6_21 hs6_23 hs6_25 hs6_27 hs6_28 hs6_fp hinv_s6
    rw [hs5_19] at hs6_19; rw [hs5_20] at hs6_20; rw [hs5_21] at hs6_21; rw [hs5_23] at hs6_23
    rw [hs5_27] at hs6_27; rw [hs5_28] at hs6_28; rw [hs5_fp] at hs6_fp
    refine step_send_chain_params_32038_placed A lim σ0 ext hcp_call
      sp cap ptr g.chain ch
      (((((((bs0 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch))) ++
        encodeInt32Field 1#32 ch.direction) ++ encodeUint64Field 2#32 ch.currentEpoch) ++
        encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links) ++
        encodeBytesField 4#32 ch.nextRoot) ++
        encodeUint64Field 5#32 ch.sendEpoch)
      (by simp only [List.length_append, List.length_singleton]; omega) halign
      (F := F_rest) hpcs6 hruns6 hsps6 htrs6 hinv_s6
      (by dsimp +zetaDelta only [F_rest, F_no16]; sep_ac_rfl) ?_
    intro s7 hpcs7 hruns7 hsps7 htrs7 hs7_19 hs7_20 hs7_21 hs7_23 hs7_25 hs7_27 hs7_28 hs7_fp hinv_s7
    rw [hs6_19] at hs7_19; rw [hs6_20] at hs7_20; rw [hs6_21] at hs7_21; rw [hs6_23] at hs7_23
    rw [hs6_25] at hs7_25; rw [hs6_27] at hs7_27; rw [hs6_28] at hs7_28; rw [hs6_fp] at hs7_fp
    refine SepWPp.weaken_pre ?_
      (hnext s7 hpcs7 hruns7 hsps7 htrs7 hs7_19 hs7_20 hs7_21 hs7_23 hs7_25 hs7_27 hs7_28 hs7_fp hinv_s7)
    unfold pqRatchetStatePBPinnedAt
    rw [h4752, hch, encodeOptMessage_chain_some ch]
    dsimp +zetaDelta only [optChainPBPinnedAt, cap, bs0, F_rest]
    simp only [List.append_assoc]
    exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainEncodePlacedBudget
