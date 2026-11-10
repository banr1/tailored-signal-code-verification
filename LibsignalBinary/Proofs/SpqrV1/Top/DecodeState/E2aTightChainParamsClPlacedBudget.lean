/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.Prost
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep
import ProofLib.Hoare.Hooks
import ProofLib.SepLogic.WPp

/-!
# Canonical Zero-Allocation `ChainParams::merge` (`Block 294`) Contract

Proves that `prost::encoding::message::merge::<ChainParams, &mut &[u8]>` (Block `294`) executes
with `evs = []` on canonical length-prefixed `ChainParamsPB.encodeRaw cp` wire slices
(`e2a_ChainParamsCanonicalDom`), delegating non-canonical inputs to `hc.chainParamsMerge`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.E2aTightChainParamsClPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (HighCalleeSaved IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_lt
   key_wt_some sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (Bytes ChainParamsPB)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeKey encodeUint32Field encodeVarint mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (chainParamsPBAt)
open CryptoVerification.SpqrV1.Varint
  (skipBelow3 skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (SepWPp.call_frame_lscl_mm SepWPp.elim_lsclProp
   SepWPp.of_sepWP_lscl_mm WppPost blkPC_294 blkPl_294 bv_len_sub_limit
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto
   protoPrefixStep_chainParamsPB_mergeField subroutine_ok_withLsCodeLoaded_of_withLsclProp
   withLsclProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Top.DecodeState
  (ChainParamsMergeGhost V1InnerHeapPred chainParamsMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1Sync.Codec
  (LoopsTo loopsTo_uint32 mergeMessage_encode)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.E2aTightBytesZeroAux
  (e2a_decodeKey_encodeKey e2a_decodeVarint_encodeVarint e2a_decodeVarint_lenPrefixed
   e2a_decodeVarint2Env_eq_nil e2a_encodeUint32Field_append_of_ne e2a_encodeUint32Field_of_zero
   e2a_encodeVarint_len_le_10 e2a_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsBudget
  (WppBudgetPanic chainParamsBudgetLoopPre wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (ChainParamsMergeEnv ChainParamsMergePostEnv chainParamsMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
  (DecodeStateCalleeContractsClPlaced)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## 1. Canonical `ChainParamsPB` Wire Round-Trip & Zero-Alloc Envelopes -/

theorem e2a_encodeUint32Field_len_le_11 (tag v : BitVec 32)
    (hkey1 : (encodeKey tag .varint).length = 1) :
    (encodeUint32Field tag v).length ≤ 11 := by
  by_cases hv : v = 0#32
  · subst hv; simp [e2a_encodeUint32Field_of_zero]
  · have hval : (encodeVarint (v.zeroExtend 64)).length ≤ 10 := e2a_encodeVarint_len_le_10 _
    have heq := e2a_encodeUint32Field_append_of_ne tag v hv []
    simp only [List.append_nil] at heq
    rw [heq, List.length_append, hkey1]
    omega

theorem e2a_chainParams_encodeRaw_len_le_22 (cp : ChainParamsPB) :
    (ChainParamsPB.encodeRaw cp).length ≤ 22 := by
  unfold ChainParamsPB.encodeRaw
  rw [List.length_append]
  have h1 := e2a_encodeUint32Field_len_le_11 1#32 cp.maxJump (by decide)
  have h2 := e2a_encodeUint32Field_len_le_11 2#32 cp.maxOooKeys (by decide)
  omega

theorem e2a_loopsTo_chainParams (cp : ChainParamsPB) :
    LoopsTo ChainParamsPB.mergeField 0 default (ChainParamsPB.encodeRaw cp) cp := by
  have hA := loopsTo_uint32 ChainParamsPB.mergeField 0 (default : ChainParamsPB) 1#32 cp.maxJump
    (fun x => { (default : ChainParamsPB) with maxJump := x }) (by decide) (by decide) rfl
    (fun _ _ _ => by simp [ChainParamsPB.mergeField])
  have hB := loopsTo_uint32 ChainParamsPB.mergeField 0
    { (default : ChainParamsPB) with maxJump := cp.maxJump } 2#32 cp.maxOooKeys
    (fun x => { (default : ChainParamsPB) with maxJump := cp.maxJump, maxOooKeys := x })
    (by decide) (by decide) rfl (fun _ _ _ => by simp [ChainParamsPB.mergeField])
  exact (LoopsTo.append protoPrefixStep_chainParamsPB_mergeField hA hB).congr_res (by cases cp; rfl)

theorem e2a_mergeMessage_chainParams_encode (cp : ChainParamsPB) (rest : Bytes) :
    mergeMessage ChainParamsPB.mergeField .lengthDelimited default
        (e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) rest) 99 =
      .ok (cp, rest) := by
  unfold e2a_lenPrefixed
  rw [List.append_assoc]
  have hlen := e2a_chainParams_encodeRaw_len_le_22 cp
  exact mergeMessage_encode ChainParamsPB.mergeField 0 ChainParamsPB.encodeRaw default cp 99 rest
    (e2a_loopsTo_chainParams cp) (by omega) (by decide)

/-- Canonical `Ok`-path domain for `ChainParams::merge` (Block `294`). -/
def e2a_ChainParamsCanonicalDom (x : ChainParamsMergeGhost) : Prop :=
  x.wt = .lengthDelimited ∧
    x.msg = default ∧
    ∃ (cp : ChainParamsPB) (rest : Bytes),
      x.bs = e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) rest

/-- Pre-envelope requiring `evs = []` on `e2a_ChainParamsCanonicalDom` and `SpecsBudget.ChainParamsMergeEnv`
outside it. -/
def E2aChainParamsCanonicalPreEnv (x : ChainParamsMergeGhost) (evs : List AllocEvent) : Prop :=
  (e2a_ChainParamsCanonicalDom x ∧ evs = []) ∨
    (¬ e2a_ChainParamsCanonicalDom x ∧ ChainParamsMergeEnv x evs)

/-- Post-envelope giving `evs = []` on `e2a_ChainParamsCanonicalDom` and `SpecsBudget.ChainParamsMergePostEnv`
outside it. -/
def E2aChainParamsCanonicalPostEnv (x : ChainParamsMergeGhost) (evs : List AllocEvent) : Prop :=
  (e2a_ChainParamsCanonicalDom x ∧ evs = []) ∨
    (¬ e2a_ChainParamsCanonicalDom x ∧ ChainParamsMergePostEnv x evs)

theorem e2a_fitsEnv_chainParams_canonical {M : AllocCostModel} {lim : BudgetLimits} (st : M.σ)
    {x : ChainParamsMergeGhost} (hdom : e2a_ChainParamsCanonicalDom x) :
    FitsEnv M lim st (E2aChainParamsCanonicalPreEnv x) := by
  intro evs hevs
  rcases hevs with ⟨_, rfl⟩ | ⟨hnd, _⟩
  · trivial
  · exact absurd hdom hnd

theorem e2a_chainParamsCanonicalPostEnv_eq_nil {x : ChainParamsMergeGhost} {evs : List AllocEvent}
    (hdom : e2a_ChainParamsCanonicalDom x) (hpost : E2aChainParamsCanonicalPostEnv x evs) :
    evs = [] := by
  rcases hpost with ⟨_, rfl⟩ | ⟨hnd, _⟩
  · rfl
  · exact absurd hdom hnd

private theorem e2a_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits}
    (st : M.σ) {bs rest : Bytes} {v : BitVec 64}
    (hd : decodeVarint bs = some (v, rest)) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs hdv
  rw [e2a_decodeVarint2Env_eq_nil hd hdv]
  trivial

/-! ## 2. Canonical Zero-Alloc Step Lemmas in Block `294` -/

private theorem e2a_chainParams_decode_key_varint_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    {spec : Spec (ChainParamsMergeGhost × M.σ)}
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {cur rest : Bytes} {limit : Nat} {tag : BitVec 32}
    (htag1 : 1 ≤ tag.toNat) (htag2 : tag.toNat < 2 ^ 29)
    (hcur_eq : cur = encodeKey tag .varint ++ rest)
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hcont : ∀ (s' : State),
      rest.length ≤ cur.length → IsDropSuffix x.bs rest →
      s'.pc = (blkPl_294).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = 0#64 →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag.toNat →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s'
        (chainParamsBudgetLoopPre A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost spec (x, st0) R s0)
        (WppBudgetPanic spec (x, st0) R s0))
    (hpc : s.pc = (blkPl_294).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost spec (x, st0) R s0)
      (WppBudgetPanic spec (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  obtain ⟨hd_eq, hkey_nat, hk_ge, hwt, hdiv8, hitag0⟩ :=
    e2a_decodeKey_encodeKey tag .varint rest htag1 htag2
  have hd : decodeVarint cur =
      some (((tag <<< 3) ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32).zeroExtend 64, rest) := by
    rw [hcur_eq]; exact hd_eq
  clear hcur_eq
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 99 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st0))
    (ret_pc := (blkPl_294).base + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, e2a_fitsEnv_decodeVarint2_of_some st0 hd⟩
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hrest_suf : IsDropSuffix x.bs rest :=
    suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
  have hshr := key_shr32_of_lt hk_ge
  have hwt_v : WireType.ofNat?
      ((((tag <<< 3) ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32).zeroExtend 64).toNat % 8) =
      some .varint := hwt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt_v
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat
    (n := (((tag <<< 3) ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32).zeroExtend 64).toNat / 8)
    (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
  have hcbz_tag64 :
      (BitVec.ofNat 64 ((((tag <<< 3) ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32).zeroExtend 64).toNat / 8) == 0#64) = false := by
    rw [hdiv8, beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tag.toNat < 2 ^ 64)] at h1
    omega
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 212#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2a_decodeVarint2Env_eq_nil hd hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
  wp_steps_sync_pool ((blkPl_294).base + 212#64)
  try simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (by dsimp only [chainParamsBudgetLoopPre]; sep_entail)
    (hcont _ hrest_le_cur hrest_suf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm])
      (by
        simp only [arm64_norm]
        have hw1' :
            (tag <<< 3 ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32) >>> 3 =
              BitVec.ofNat 32
                ((((tag <<< 3) ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32).zeroExtend 64).toNat / 8) := by
          have htr32 :
              BitVec.truncate 32
                (BitVec.zeroExtend 64 (tag <<< 3 ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32)) =
                (tag <<< 3 ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.varint.toU32) :=
            _root_.BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)
          simpa [htr32] using hw1
        rw [hw1', hw1_zext1, hdiv8])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

private theorem e2a_chainParams_tag1_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    {spec : Spec (ChainParamsMergeGhost × M.σ)}
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {cur rest' : Bytes} {limit : Nat} {v : BitVec 32}
    (hv : v ≠ 0#32)
    (hcur_eq : cur = encodeUint32Field 1#32 v ++ rest')
    (hrest'_ge : limit ≤ rest'.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hcont : ∀ (s' : State),
      rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
      s'.pc = (blkPl_294).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s'
        (chainParamsBudgetLoopPre A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with maxJump := v } x.bs rest')
        (WppPost spec (x, st0) R s0)
        (WppBudgetPanic spec (x, st0) R s0))
    (hpc : s.pc = (blkPl_294).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost spec (x, st0) R s0)
      (WppBudgetPanic spec (x, st0) R s0) := by
  let rest := encodeVarint (v.zeroExtend 64) ++ rest'
  have hcur_key : cur = encodeKey 1#32 .varint ++ rest := by
    rw [hcur_eq, e2a_encodeUint32Field_append_of_ne 1#32 v hv rest']
  have hkey_pos : 0 < (encodeKey 1#32 .varint).length := by decide
  have hgt_lim : ¬ cur.length ≤ limit := by
    rw [hcur_key, List.length_append]
    have : rest'.length ≤ rest.length := by simp [rest]
    omega
  refine e2a_chainParams_decode_key_varint_cl_placed hVarintCall
    (by decide) (by decide) hcur_key hgt_lim hsp_align hcur_le hcur_lt hcur_suf ?_
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
  intro s1 hrest_le_cur hrest_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le_cur hcur_lt
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 260#64) hinv1
  conv => arg 4; rw [chainParamsBudgetLoopPre]; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_294).base + 260#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv1
  apply SepWPp.weaken_pre
    (P' := chainParamsBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (Entails.of_eq (by dsimp only [chainParamsBudgetLoopPre]; sep_ac_rfl))
  have hdv : decodeVarint rest = some (v.zeroExtend 64, rest') :=
    e2a_decodeVarint_encodeVarint (v.zeroExtend 64) rest'
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv1
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 99 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv2
  refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st0))
    (ret_pc := (blkPl_294).base + 272#64) hVarintCall hinv2
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, arm64_norm, hsp1]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp1, hx19_1], hrest_lt, e2a_fitsEnv_decodeVarint2_of_some st0 hdv⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 160#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, chainParamsPBAt,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2a_decodeVarint2Env_eq_nil hdv hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp1]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  wp_steps_sync_pool ((blkPl_294).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (by dsimp only [chainParamsBudgetLoopPre, chainParamsPBAt]; sep_entail)
    (hcont _ (Nat.le_trans hrest'_le hrest_le)
      (suffix_trans hrest_le hrest_suf hrest'_le (decodeVarint_suffix hdv))
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

private theorem e2a_chainParams_tag2_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    {spec : Spec (ChainParamsMergeGhost × M.σ)}
    {x : ChainParamsMergeGhost} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {m : ChainParamsPB} {cur rest' : Bytes} {limit : Nat} {v : BitVec 32}
    (hv : v ≠ 0#32)
    (hcur_eq : cur = encodeUint32Field 2#32 v ++ rest')
    (hrest'_ge : limit ≤ rest'.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hcont : ∀ (s' : State),
      rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
      s'.pc = (blkPl_294).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s'
        (chainParamsBudgetLoopPre A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with maxOooKeys := v } x.bs rest')
        (WppPost spec (x, st0) R s0)
        (WppBudgetPanic spec (x, st0) R s0))
    (hpc : s.pc = (blkPl_294).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s
      (chainParamsBudgetLoopPre A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost spec (x, st0) R s0)
      (WppBudgetPanic spec (x, st0) R s0) := by
  let rest := encodeVarint (v.zeroExtend 64) ++ rest'
  have hcur_key : cur = encodeKey 2#32 .varint ++ rest := by
    rw [hcur_eq, e2a_encodeUint32Field_append_of_ne 2#32 v hv rest']
  have hkey_pos : 0 < (encodeKey 2#32 .varint).length := by decide
  have hgt_lim : ¬ cur.length ≤ limit := by
    rw [hcur_key, List.length_append]
    have : rest'.length ≤ rest.length := by simp [rest]
    omega
  refine e2a_chainParams_decode_key_varint_cl_placed hVarintCall
    (by decide) (by decide) hcur_key hgt_lim hsp_align hcur_le hcur_lt hcur_suf ?_
    hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
  intro s1 hrest_le_cur hrest_suf hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le_cur hcur_lt
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 228#64) hinv1
  conv => arg 4; rw [chainParamsBudgetLoopPre]; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_294).base + 228#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv1
  apply SepWPp.weaken_pre
    (P' := chainParamsBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
    (Entails.of_eq (by dsimp only [chainParamsBudgetLoopPre]; sep_ac_rfl))
  have hdv : decodeVarint rest = some (v.zeroExtend 64, rest') :=
    e2a_decodeVarint_encodeVarint (v.zeroExtend 64) rest'
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv1
  conv => arg 4; rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_leaf s0.sp 99 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv2
  refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st0))
    (ret_pc := (blkPl_294).base + 240#64) hVarintCall hinv2
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, arm64_norm, hsp1]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp1, hx19_1], hrest_lt, e2a_fitsEnv_decodeVarint2_of_some st0 hdv⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 160#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, chainParamsPBAt,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2a_decodeVarint2Env_eq_nil hdv hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp1]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  wp_steps_sync_pool ((blkPl_294).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (by dsimp only [chainParamsBudgetLoopPre, chainParamsPBAt]; sep_entail)
    (hcont _ (Nat.le_trans hrest'_le hrest_le)
      (suffix_trans hrest_le hrest_suf hrest'_le (decodeVarint_suffix hdv))
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

private def e2aChainParamsDomSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainParamsMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      e2a_ChainParamsCanonicalDom x⌝ ∗
      chainParamsPBAt x.msgPtr x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chainParamsMergeStack
  post :=
    (chainParamsMergeSpecOfEnv A lim E2aChainParamsCanonicalPreEnv E2aChainParamsCanonicalPostEnv).post

private theorem e2a_chainParams_dom_ok_blk294 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hVarintCall : subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim))) :
    subroutine_ok ((blkPC_294).rebase (blkPl_294).base H) (blkPl_294).base
      (withLsCodeLoaded lsmpl (e2aChainParamsDomSpec A lim)) := by
  apply subroutine_ok_withLsCodeLoaded_of_withLsclProp
  unfold withLsclProp e2aChainParamsDomSpec
  wpp_init p s0
  rcases p with ⟨x, st0⟩
  apply SepWPp.elim_lsclProp; intro hinv0
  replace hpc : s0.pc = (blkPl_294).base := hpc
  change SepWPp _ _ _ _
    (WppPost (e2aChainParamsDomSpec A lim) (x, st0) R s0)
    (WppBudgetPanic (e2aChainParamsDomSpec A lim) (x, st0) R s0)
  have hdom : e2a_ChainParamsCanonicalDom x := h
  obtain ⟨hwt_ld, hmsg_def, cp, rest, hbs_eq⟩ := h
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  have hraw_lt : (ChainParamsPB.encodeRaw cp).length < 2 ^ 64 := by
    have := e2a_chainParams_encodeRaw_len_le_22 cp; omega
  obtain ⟨hdv0_eq, hlen_toNat⟩ := e2a_decodeVarint_lenPrefixed (rest := rest) hraw_lt
  let raw := ChainParamsPB.encodeRaw cp
  let rest0 := raw ++ rest
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, rest0) := by
    rw [hbs_eq]; exact hdv0_eq
  apply SepWPp.of_sepWP_lscl_mm (mid := lsmpl.base 291) hinv0
  conv => arg 4; rw [chainParamsMergeStack, stackAt_skipField3 s0.sp 99 (by decide), skipBelow3_leaf s0.sp 99 (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
  apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
  apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv0
  refine SepWPp.call_frame_lscl_mm (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
    (ret_pc := (blkPl_294).base + 48#64) hVarintCall hinv0
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, h_3], h_4, e2a_fitsEnv_decodeVarint2_of_some st0 hdv0⟩
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
  have hnot_lt_len : ¬ rest0.length < (BitVec.ofNat 64 raw.length).toNat := by
    dsimp only [raw, rest0] at hlen_toNat ⊢; rw [hlen_toNat, List.length_append]; omega
  have hule := ule_len_of_ge hnot_lt_len hrest0_lt
  have hsub := bv_len_sub_limit hnot_lt_len
  have hlim_eq : rest0.length - (BitVec.ofNat 64 raw.length).toNat = rest.length := by
    dsimp only [raw, rest0] at hlen_toNat ⊢; rw [hlen_toNat, List.length_append]; omega
  apply SepWPp.of_sepWP_lscl_mm (mid := (blkPl_294).base + 160#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2a_decodeVarint2Env_eq_nil hdv0 hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 99 (by decide)) (by sep_focus)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_294).base + 160#64)
  try simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (P' := chainParamsBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
    (by rw [chainParamsBudgetLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail) ?_
  let cur2 := encodeUint32Field 2#32 cp.maxOooKeys ++ rest
  have hrest0_split : rest0 = encodeUint32Field 1#32 cp.maxJump ++ cur2 := by
    dsimp only [rest0, raw, ChainParamsPB.encodeRaw, cur2]
    rw [List.append_assoc]
  have hcur2_ge : rest.length ≤ cur2.length := by dsimp only [cur2]; rw [List.length_append]; omega
  have hAfterTag1 : ∀ (s1 : State),
      cur2.length ≤ x.bs.length → IsDropSuffix x.bs cur2 →
      s1.pc = (blkPl_294).base + 160#64 →
      s1.status = .Running → s1.sp = s0.sp - 96#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot → s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest.length →
      HighCalleeSaved s0 s1 → LibsignalCodeLoaded lsmpl s1.mem →
      SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s1
        (chainParamsBudgetLoopPre A lim st0 s0 s1 x.msgPtr x.bufRef x.slot x.ptr
          { (default : ChainParamsPB) with maxJump := cp.maxJump } x.bs cur2)
        (WppPost (e2aChainParamsDomSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (e2aChainParamsDomSpec A lim) (x, st0) R s0) := by
    have hExit : ∀ (s2 : State),
        rest.length ≤ x.bs.length → IsDropSuffix x.bs rest →
        s2.pc = (blkPl_294).base + 160#64 →
        s2.status = .Running → s2.sp = s0.sp - 96#64 → s2.trace = s0.trace →
        s2.readReg64 (Reg.gpr 19#5) = x.bufRef → s2.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s2.readReg64 (Reg.gpr 21#5) = x.slot → s2.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest.length →
        HighCalleeSaved s0 s2 → LibsignalCodeLoaded lsmpl s2.mem →
        SepWPp ((blkPC_294).rebase (blkPl_294).base H) (s0.readReg64 Reg.lr) s2
          (chainParamsBudgetLoopPre A lim st0 s0 s2 x.msgPtr x.bufRef x.slot x.ptr cp x.bs rest)
          (WppPost (e2aChainParamsDomSpec A lim) (x, st0) R s0)
          (WppBudgetPanic (e2aChainParamsDomSpec A lim) (x, st0) R s0) := by
      intro s2 hrest_le hrest_suf hpc2 hrun2 hsp2 htr2 _ _ hx21_2 hx22_2 hcs2 _
      obtain ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2⟩ := hcs2
      obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : rest.length = rest.length)
      have hsome :
          (mergeMessage ChainParamsPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            some (cp, rest) := by
        rw [hwt_ld, hmsg_def, hbs_eq]
        change (mergeMessage ChainParamsPB.mergeField .lengthDelimited default
          (e2a_lenPrefixed (ChainParamsPB.encodeRaw cp) rest) 99).toOption = some (cp, rest)
        rw [e2a_mergeMessage_chainParams_encode cp rest]
        rfl
      have hevs_post : E2aChainParamsCanonicalPostEnv x [] := .inl ⟨hdom, rfl⟩
      apply SepWPp.of_sepWP_ret
      unfold WppPost e2aChainParamsDomSpec chainParamsMergeSpecOfEnv
      simp only [hsome, stackAt_skipField3 _ 99 (by decide), chainParamsBudgetLoopPre,
        sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr2, hsp2]
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      conv => arg 4; rw [show st0 = M.stepEvents [] st0 from rfl]
      wp_done
    intro s1 hcur2_le hcur2_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
    by_cases hv2 : cp.maxOooKeys = 0#32
    · have hcur2_eq : cur2 = rest := by dsimp only [cur2]; rw [hv2, e2a_encodeUint32Field_of_zero, List.nil_append]
      have hm_eq : ({ (default : ChainParamsPB) with maxJump := cp.maxJump } : ChainParamsPB) = cp := by
        cases cp; dsimp only at hv2; subst hv2; rfl
      rw [hcur2_eq] at hcur2_le hcur2_suf ⊢
      rw [hm_eq]
      exact hExit s1 hcur2_le hcur2_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
    · have hcur2_lt : cur2.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur2_le h_4
      refine e2a_chainParams_tag2_ok_cl_placed hVarintCall hv2 rfl
        (Nat.le_refl rest.length) hsp_align hcur2_le hcur2_lt hcur2_suf ?_
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
      intro s2 hrest_le hrest_suf hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hinv2
      have hm_eq :
          ({ (default : ChainParamsPB) with maxJump := cp.maxJump, maxOooKeys := cp.maxOooKeys } : ChainParamsPB) = cp := by
        cases cp; rfl
      rw [hm_eq]
      exact hExit s2 hrest_le hrest_suf hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hinv2
  by_cases hv1 : cp.maxJump = 0#32
  · have hrest0_eq : rest0 = cur2 := by
      rw [hrest0_split, hv1, e2a_encodeUint32Field_of_zero, List.nil_append]
    have hm1_eq : x.msg = { (default : ChainParamsPB) with maxJump := cp.maxJump } := by
      rw [hmsg_def, hv1]; rfl
    rw [hrest0_eq, hm1_eq]
    exact hAfterTag1 _ (hrest0_eq ▸ hrest0_le) (hrest0_eq ▸ hrest0_suf)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub, hlim_eq])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · rw [hmsg_def]
    exact e2a_chainParams_tag1_ok_cl_placed hVarintCall hv1 hrest0_split
      hcur2_ge hsp_align hrest0_le hrest0_lt hrest0_suf hAfterTag1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub, hlim_eq])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Canonical zero-alloc `ChainParams::merge` (Block `294`) `subroutine_ok` on `blkPC_325`
derived solely from `hc : DecodeStateCalleeContractsClPlaced`. -/
theorem e2a_chainParamsMerge_cl_placed_ok_canonical [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsClPlaced H_inner A lim ext) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (chainParamsMergeSpecOfEnv A lim
          E2aChainParamsCanonicalPreEnv E2aChainParamsCanonicalPostEnv)) := by
  apply subroutine_ok_by_cases (fun p => e2a_ChainParamsCanonicalDom p.1)
  · have hVarint294 :
        subroutine_ok ((blkPC_294).rebase (blkPl_294).base (Rust.withPanics ext))
          (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) :=
      ls_subroutine_ok_of_block
        (callerProg := (blkPC_294).rebase (blkPl_294).base (Rust.withPanics ext))
        hc.decodeVarint2
    have h294 := e2a_chainParams_dom_ok_blk294 hVarint294
    have h325 :
        subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
          (lsmpl.base 294) (withLsCodeLoaded lsmpl (e2aChainParamsDomSpec A lim)) :=
      ls_subroutine_ok_of_block
        (callerProg := (blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
        h294
    refine subroutine_ok_mono_sp h325 (fun ⟨x, st0⟩ s0 => ?_) (fun _ _ _ _ => Entails.refl _)
    dsimp only [withLsCodeLoaded, e2aChainParamsDomSpec, chainParamsMergeSpecOfEnv]
    apply Entails.pure_left; intro hdom
    refine sepConj_mono_left ?_
    exact Entails.pure_left fun h =>
      Entails.pure_right ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hdom⟩ (Entails.refl _)
  · refine subroutine_ok_map_oom' hc.chainParamsMerge ?_
    rintro ⟨x, st0⟩ R s0 hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm
    obtain ⟨hndom, hm⟩ := hm
    refine ⟨(x, st0), R, ?_, ?_, fun _ h => h⟩
    · refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [withLsCodeLoaded, SpecsBudget.chainParamsMergeSpec, chainParamsMergeSpecOfEnv]
      refine sepConj_mono_left ?_
      exact Entails.pure_left fun h =>
        Entails.pure_right
          ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun evs hevs => h.2.2.2.2 evs (.inr ⟨hndom, hevs⟩)⟩
          (Entails.refl _)
    · intro sf hpost
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [withLsCodeLoaded, SpecsBudget.chainParamsMergeSpec, chainParamsMergeSpecOfEnv]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
      apply Entails.sepExists_elim; intro evs
      apply Entails.pure_left; intro hevs
      exact Entails.sepExists_right evs
        (Entails.pure_right (.inr ⟨hndom, hevs⟩) (Entails.refl _))
