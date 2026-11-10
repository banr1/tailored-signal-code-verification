/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesStepsR
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Step & `AuthMergeLoopEnv` Helpers for `ProtoAuthenticator::merge` (`Block 295`)

Proves pure `AuthMergeLoopEnv` step bridges, `decodeErrorPushMergeBudgetSpec` error-exit and
field steps, and zero-capacity per-field step lemmas on `tlb_AuthDom` for Block `295`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthStepsR

open Arm64 Arm64.Obj ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_295 blkPl_295 lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarintAux decodeVarint_length mergeBytes skipField)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost HighCalleeSaved IsDropSuffix SkipFieldGhost
   bv32_zeroExtend_ofNat bytesMergeCapOk_mono bytesMergeCapOk_zero decodeVarint_suffix
   key_shr32_of_lt key_wt_some pointsToBytes_prefix_join sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (Bytes ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Varint
  (skipBelow3 skipBelow3_err skipBelow3_err_entails skipBelow3_leaf skipBelow3_leaf_entails
   stackAt_skipField3)
open CryptoVerification.SpqrV1.ProtoRepr (authenticatorPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro cmp_len_limit_of_eq cmp_len_limit_of_gt
   codecWireTypeToProto decodeErrorWith_one_entails_le1 pointsTo64_memRegion40_entails_48
   skipBelow3_bytesMerge3 skipBelow3_bytesMerge3_entails)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost SepWPp.pure_elim SepWPp.pure_elim2 WppPost authMergeStack authenticatorPBCapAt
   authenticatorPBAt_entails_exists memRegion_48_split_96 mergeBytes_length setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1Sync.Codec (loopsTo_authenticator)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt tlb_lenPrefixed tlb_vecU8ZeroCapAt
   tlb_vecU8ZeroCapAt_entails_cap)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthBytesMerge3EnvCore AuthMergeLoopEnv DecodeErrorPushBoundedEnv authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
  (authBudgetErrFrame authBudgetLoopPre)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env BytesMerge3EnvCore WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
  (e2ar_bytesMerge3_zero_tight32 e2ar_decodeVarint2Env_some_nil e2ar_mergeMessage_lenPrefixed
   e2ar_raw_lt_of_lenPrefixed_lt)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

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

/-! ## 1. Pure Round-Trip & `AuthMergeLoopEnv` Step Bridges -/

theorem e2ar_mergeMessage_authenticator_lenPrefixed (m : ProtoAuthenticator) (rest : Bytes)
    (depth : Nat) (hd : 0 < depth)
    (hlt : (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw m) rest).length < 2 ^ 63) :
    (mergeMessage ProtoAuthenticator.mergeField .lengthDelimited default
      (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw m) rest) depth).toOption =
        some (m, rest) := by
  have hlen := e2ar_raw_lt_of_lenPrefixed_lt hlt
  exact e2ar_mergeMessage_lenPrefixed ProtoAuthenticator.mergeField 0
    ProtoAuthenticator.encodeRaw default m depth rest (loopsTo_authenticator m hlen) hlen hd

theorem e2ar_decodeVarintAux_append :
    ∀ {bs : List (BitVec 8)} {i : Nat} {acc v : BitVec 64} {r : List (BitVec 8)},
      decodeVarintAux i acc bs = some (v, r) →
      ∃ pfx : List (BitVec 8),
        bs = pfx ++ r ∧ 1 ≤ pfx.length ∧
        ∀ tail : List (BitVec 8), decodeVarintAux i acc (pfx ++ tail) = some (v, tail)
  | [], _, _, _, _, h => by simp [decodeVarintAux] at h
  | b :: rest, i, acc, v, r, h => by
    dsimp only [decodeVarintAux] at h
    by_cases hb : b.toNat ≤ 0x7F
    · simp only [hb, ↓reduceIte] at h
      by_cases hov : i = 9 ∧ 0x02 ≤ b.toNat
      · simp only [hov, ↓reduceIte] at h
        nomatch h
      · simp only [hov, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hacc, rfl⟩ := h
        refine ⟨[b], rfl, Nat.le_refl 1, fun tail => ?_⟩
        rw [List.singleton_append]
        simp only [decodeVarintAux, hb, hov, ↓reduceIte, hacc]
    · simp only [hb, ↓reduceIte] at h
      by_cases hi9 : i = 9
      · simp only [hi9, ↓reduceIte] at h
        nomatch h
      · simp only [hi9, ↓reduceIte] at h
        obtain ⟨pfx', rfl, hpfx_len, htail⟩ := e2ar_decodeVarintAux_append h
        refine ⟨b :: pfx', rfl, by simp, fun tail => ?_⟩
        simp only [List.cons_append, decodeVarintAux, hb, hi9, ↓reduceIte]
        exact htail tail

theorem e2ar_authMergeLoopEnv_of_decodeErrorFrom {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    AuthMergeLoopEnv 1 0 evs := by
  rw [h]
  simpa using (AuthMergeLoopEnv.errFrom (errRem := 0) (byteRem := 0) .nil)

theorem e2ar_authMergeLoopEnv_of_pushMerge0 {evs : List AllocEvent}
    (h : DecodeErrorPushMergeEnv 0 evs) :
    AuthMergeLoopEnv 1 0 evs := by
  have hb : DecodeErrorPushBoundedEnv 0 evs := h
  simpa using (AuthMergeLoopEnv.errPush (errRem := 0) (byteRem := 0) (Nat.zero_le 1) hb .nil)

theorem e2ar_authMergeLoopEnv_of_decodeVarint2 {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : DecodeVarint2Env bs evs) :
    AuthMergeLoopEnv 1 0 evs := by
  change DecodeVarintSliceEnv bs evs at h
  rw [h]; unfold decodeVarintSliceEvents
  cases decodeVarint bs
  · simpa using (AuthMergeLoopEnv.errFrom (errRem := 0) (byteRem := 0) .nil)
  · exact .nil

theorem e2ar_authMergeLoopEnv_of_skipField3 {g : SkipFieldGhost} {evs : List AllocEvent}
    (h : SkipField3Env g evs) :
    AuthMergeLoopEnv 1 0 evs := by
  change SkipFieldEnv g evs at h
  rw [h]; unfold skipFieldEventsCore
  cases skipField (2 * g.bs.length + 2) g.depth g.tag g.wt g.bs
  · simpa using (AuthMergeLoopEnv.errFrom (errRem := 0) (byteRem := 0) .nil)
  · exact .nil

theorem e2ar_authMergeLoopEnv_of_bytesMerge3_none {g : BytesMergeGhost} {evs : List AllocEvent}
    (hmb : mergeBytes g.wt g.bs = none) (h : BytesMerge3Env g evs) :
    AuthMergeLoopEnv 1 0 evs := by
  change evs = bytesMergeEventsCore g.wt g.valCap g.bs at h
  rw [h]
  simp only [bytesMergeEventsCore, hmb]
  simpa using (AuthMergeLoopEnv.errFrom (errRem := 0) (byteRem := 0) .nil)

theorem e2ar_authMergeLoopEnv_of_bytesMerge3_some {g : BytesMergeGhost}
    {v rest' : List (BitVec 8)} {evs : List AllocEvent}
    (hmb : mergeBytes g.wt g.bs = some (v, rest')) (h : BytesMerge3Env g evs) :
    AuthMergeLoopEnv 0 (g.bs.length - rest'.length) evs := by
  have hmb_orig := hmb
  unfold mergeBytes at hmb
  have hwt : g.wt = .lengthDelimited := by
    cases hwt_c : g.wt <;> simp only [hwt_c] at hmb <;> first | rfl | contradiction
  simp only [hwt, ne_self_iff_false, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hmb
  rcases hdv : decodeVarint g.bs with _ | ⟨len, r0⟩
  · simp only [hdv] at hmb
    nomatch hmb
  · simp only [hdv] at hmb
    by_cases hlt : r0.length < len.toNat
    · simp only [hlt, ↓reduceIte] at hmb
      nomatch hmb
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hmb
      have hv_eq := hmb.1
      have hrest_eq := hmb.2
      obtain ⟨pfx, hg_eq, hpfx_len, htail⟩ := e2ar_decodeVarintAux_append hdv
      let bs_c : List (BitVec 8) := pfx ++ v
      have hr0_eq : v ++ rest' = r0 := by
        rw [← hv_eq, ← hrest_eq]
        exact List.take_append_drop len.toNat r0
      have hg_bs : g.bs = bs_c ++ rest' := by
        rw [hg_eq, ← hr0_eq, List.append_assoc]
      have hlen_g : g.bs.length = bs_c.length + rest'.length := by
        rw [hg_bs]; exact List.length_append
      have hbs_c_len : bs_c.length = g.bs.length - rest'.length := by omega
      have hv_len : v.length = len.toNat := by
        rw [← hv_eq, List.length_take_of_le (by omega)]
      have hdv_c : decodeVarint bs_c = some (len, v) := htail v
      have hmb_c : mergeBytes g.wt bs_c = some (v, []) := by
        have hlt_c : ¬ v.length < len.toNat := by omega
        simp only [mergeBytes, hwt, ne_self_iff_false, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          hdv_c, hlt_c, List.take_of_length_le (Nat.le_of_eq hv_len),
          List.drop_of_length_le (Nat.le_of_eq hv_len)]
      have hcore_c : AuthBytesMerge3EnvCore g.wt g.valCap bs_c evs := by
        change evs = bytesMergeEventsCore g.wt g.valCap g.bs at h
        unfold AuthBytesMerge3EnvCore
        rw [h]
        simp only [bytesMergeEventsCore, hmb_orig, hmb_c]
      have hshr : 0 + v.length + 1 ≤ g.bs.length - rest'.length := by
        have hpv : bs_c.length = pfx.length + v.length := List.length_append
        omega
      have hstep := AuthMergeLoopEnv.bytesStep
        (errRem := 0) (byteRem := g.bs.length - rest'.length) (byteRem' := 0)
        g.wt g.valCap bs_c v [] hmb_c (Nat.le_of_eq hbs_c_len) hshr hcore_c .nil
      rwa [List.append_nil] at hstep

theorem e2ar_authMergeLoopEnv_of_bytesMerge3 {g : BytesMergeGhost} {byteRem : Nat}
    {evs : List AllocEvent} (hlen : g.bs.length ≤ byteRem) (h : BytesMerge3Env g evs) :
    AuthMergeLoopEnv 1 byteRem evs := by
  cases hmb : mergeBytes g.wt g.bs with
  | none =>
    exact (e2ar_authMergeLoopEnv_of_bytesMerge3_none hmb h).mono (Nat.le_refl 1) (Nat.zero_le _)
  | some p =>
    rcases p with ⟨v, rest'⟩
    exact (e2ar_authMergeLoopEnv_of_bytesMerge3_some hmb h).mono (Nat.zero_le 1) (by omega)

/-! ## 2. `decodeErrorPushMergeBudgetSpec` Exit and Field Steps (`Block 295`) -/

theorem e2ar_auth_push_merge_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {err : BitVec 64}
    (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur (DecodeErrorPushMergeEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_295).base + 436#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 97 ∗
        authBudgetErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authBudgetErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorPushMergeBudgetSpec M A lim)
    (x := (s0.sp - 96#64, err, 0, st_cur))
    (ret_pc := (blkPl_295).base + 440#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx0], by decide, hfits_push⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpecOfEnv
  simp only [decodeErrorPushMergeBudgetSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_p
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_p
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_push evs_p hevs_p
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

theorem e2ar_auth_tag1_merge_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_bm : ∀ cap1 ptr1 : BitVec 64, BytesMergeCapOk cap1 rest.length →
      FitsEnv M lim st_cur
        (BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hfits_push : ∀ (cap1 ptr1 : BitVec 64) (evs_bm : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (DecodeErrorPushMergeEnv 0))
    (hevs_bm_err : ∀ (cap1 ptr1 : BitVec 64) (evs_bm evs_p : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p (M.stepEvents evs_bm st_cur) = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (cap1 ptr1 : BitVec 64) (v rest' : List (BitVec 8))
      (evs_bm : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with rootKey := v } x.bs rest')
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  conv =>
    arg 4
    rw [authBudgetLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 264#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap1, hfits_bm cap1 ptr1 hcap1⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
        vecU8At A.repAlloc (x.msgPtr + 24#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A.repAlloc x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 436#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (e2ar_auth_push_merge_err_exit_cl_placed hPushCall hnone hsm0
        (hfits_push cap1 ptr1 evs_bm hmb hevs_bm)
        (fun evs_p hp => hevs_bm_err cap1 ptr1 evs_bm evs_p hmb hevs_bm hp)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap2' : BytesMergeCapOk cap2 rest'.length := bytesMergeCapOk_mono hcap2 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap1'
    apply SepWP.exists_elim; intro ptr1'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap1'
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A.repAlloc x.msgPtr cap1' ptr1' v ∗
          vecU8At A.repAlloc (x.msgPtr + 24#64) cap2 ptr2 m.macKey ⊢
          authenticatorPBCapAt A.repAlloc x.msgPtr rest'.length { m with rootKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
      (hcont cap1 ptr1 v rest' evs_bm _ hmb hevs_bm
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

theorem e2ar_auth_tag2_merge_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_bm : ∀ cap2 ptr2 : BitVec 64, BytesMergeCapOk cap2 rest.length →
      FitsEnv M lim st_cur
        (BytesMerge3Env ⟨iwt, x.msgPtr + 24#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hfits_push : ∀ (cap2 ptr2 : BitVec 64) (evs_bm : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr + 24#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (DecodeErrorPushMergeEnv 0))
    (hevs_bm_err : ∀ (cap2 ptr2 : BitVec 64) (evs_bm evs_p : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr + 24#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p (M.stepEvents evs_bm st_cur) = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (cap2 ptr2 : BitVec 64) (v rest' : List (BitVec 8))
      (evs_bm : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      BytesMerge3Env ⟨iwt, x.msgPtr + 24#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with macKey := v } x.bs rest')
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  conv =>
    arg 4
    rw [authBudgetLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr + 24#64, cap2, ptr2, m.macKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 240#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap2, hfits_bm cap2 ptr2 hcap2⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
        vecU8At A.repAlloc (x.msgPtr + 24#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A.repAlloc x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 436#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (e2ar_auth_push_merge_err_exit_cl_placed hPushCall hnone hsm0
        (hfits_push cap2 ptr2 evs_bm hmb hevs_bm)
        (fun evs_p hp => hevs_bm_err cap2 ptr2 evs_bm evs_p hmb hevs_bm hp)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap1' : BytesMergeCapOk cap1 rest'.length := bytesMergeCapOk_mono hcap1 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap2'
    apply SepWP.exists_elim; intro ptr2'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap2'
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
          vecU8At A.repAlloc (x.msgPtr + 24#64) cap2' ptr2' v ⊢
          authenticatorPBCapAt A.repAlloc x.msgPtr rest'.length { m with macKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
      (hcont cap2 ptr2 v rest' evs_bm _ hmb hevs_bm
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

/-! ## 3. Zero-Capacity Per-Field Step Lemmas on `tlb_AuthDom` (`tlb_authMergeTightSpecOfEnv`) -/

def e2ar_vecU8CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr bs

theorem e2ar_vecU8At_entails_vecU8CapAt {A : RustAlloc} {a cap ptr : BitVec 64}
    {bsLen : Nat} {bs : List (BitVec 8)} (hcap : BytesMergeCapOk cap bsLen) :
    vecU8At A a cap ptr bs ⊢ e2ar_vecU8CapAt A a bsLen bs :=
  Entails.trans (Entails.pure_right hcap (Entails.refl _))
    (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _)))

theorem e2ar_vecU8CapAt_mono {A : RustAlloc} {a : BitVec 64} {bs : List (BitVec 8)}
    {m n : Nat} (hle : m ≤ n) :
    e2ar_vecU8CapAt A a n bs ⊢ e2ar_vecU8CapAt A a m bs :=
  CryptoVerification.SpqrV1.Auth.vecU8CapAt_mono A a bs hle

def e2ar_authLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (bufRef slot ptr : BitVec 64)
    (Hmsg : SepProp) (bs cur : List (BitVec 8)) : SepProp :=
  Hmsg ∗
    memRegion (s0.sp - 96#64) 48 ∗ skipBelow3 s0.sp 97 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗ A.pool lim st s

theorem e2ar_auth_key_some_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R Hmsg : SepProp}
    {s0 s : State} {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : key.toNat < 2 ^ 32)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag_pos : 1 ≤ key.toNat / 8)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_295).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (e2ar_authLoopPre A lim st_cur s0 s' x.bufRef x.slot x.ptr Hmsg x.bs rest)
        (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (e2ar_authLoopPre A lim st_cur s0 s x.bufRef x.slot x.ptr Hmsg x.bs cur)
      (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env cur) := fun evs he => by
    rw [e2ar_decodeVarint2Env_some_nil hd he]; trivial
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [e2ar_authLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 97 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
    (ret_pc := (blkPl_295).base + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, hfits_dv⟩
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hk_ge : ¬ 2 ^ 32 ≤ key.toNat := by omega
  have hitag0 : ¬ key.toNat / 8 < 1 := by omega
  have hshr := key_shr32_of_lt hk_ge
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 212#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2ar_decodeVarint2Env_some_nil hd hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
  wp_steps_sync_pool ((blkPl_295).base + 212#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [e2ar_authLoopPre]; sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm1, hand_wt])
      (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

theorem e2ar_auth_tag1_zero_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : ProtoAuthenticator} {rest v rest' : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hmb : mergeBytes .lengthDelimited rest = some (v, rest'))
    (hv_le : v.length ≤ 32)
    (hFit_t1 : FitsEnv M lim st_cur (SpqrTightEvs 2 1476 32))
    (hcont : ∀ (evs_bm : List AllocEvent) (s' : State),
      SpqrTightEvs 2 1476 32 evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (e2ar_authLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s' x.bufRef x.slot x.ptr
          (e2ar_vecU8CapAt A.repAlloc x.msgPtr rest'.length v ∗
            tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 24#64) m.macKey)
          x.bs rest')
        (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 212#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (e2ar_authLoopPre A lim st_cur s0 s x.bufRef x.slot x.ptr
        (tlb_authenticatorZeroCapAt A.repAlloc x.msgPtr m) x.bs rest)
      (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 252#64) hinv
  (conv => arg 4; dsimp only [e2ar_authLoopPre])
  wp_steps_sync_pool ((blkPl_295).base + 252#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [tlb_authenticatorZeroCapAt,
    show tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr m.rootKey =
      (∃∗ v_ptr : BitVec 64, vecU8At A.repAlloc x.msgPtr 0#64 v_ptr m.rootKey) from rfl,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_ptr
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  have hfits_bm : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨.lengthDelimited, x.msgPtr, 0#64, v_ptr, m.rootKey, x.bufRef, x.slot, restPtr, rest⟩) :=
    fun evs he => hFit_t1 evs (e2ar_bytesMerge3_zero_tight32 hmb hv_le he)
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨.lengthDelimited, x.msgPtr, 0#64, v_ptr, m.rootKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 264#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, bytesMergeCapOk_zero, hfits_bm⟩
    (by dsimp only [sliceCursorAt, restPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
  (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_bm
  apply SepWP.exists_elim; intro cap'
  apply SepWP.exists_elim; intro ptr'
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_bm
  wp_focus_pure; intro hsm0
  wp_focus_pure; intro hcap'
  have ht1 : SpqrTightEvs 2 1476 32 evs_bm := e2ar_bytesMerge3_zero_tight32 hmb hv_le hevs_bm
  conv => arg 4; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  apply SepWP.fold (e2ar_vecU8At_entails_vecU8CapAt hcap') (by sep_focus)
  wp_steps_sync_pool ((blkPl_295).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (Entails.of_eq (by dsimp only [e2ar_authLoopPre]; sep_ac_rfl))
    (hcont evs_bm _ ht1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

theorem e2ar_auth_tag2_zero_step [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : ProtoAuthenticator} {rest v rest' : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hmb : mergeBytes .lengthDelimited rest = some (v, rest'))
    (hv_le : v.length ≤ 32)
    (hFit_t2 : FitsEnv M lim st_cur (SpqrTightEvs 2 1476 32))
    (hcont : ∀ (evs_bm : List AllocEvent) (s' : State),
      SpqrTightEvs 2 1476 32 evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (e2ar_authLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s' x.bufRef x.slot x.ptr
          (authenticatorPBCapAt A.repAlloc x.msgPtr rest'.length { m with macKey := v })
          x.bs rest')
        (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 212#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (e2ar_authLoopPre A lim st_cur s0 s x.bufRef x.slot x.ptr
        (e2ar_vecU8CapAt A.repAlloc x.msgPtr rest.length m.rootKey ∗
          tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 24#64) m.macKey) x.bs rest)
      (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 228#64) hinv
  (conv => arg 4; dsimp only [e2ar_authLoopPre])
  wp_steps_sync_pool ((blkPl_295).base + 228#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [
    show tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 24#64) m.macKey =
      (∃∗ v_ptr : BitVec 64, vecU8At A.repAlloc (x.msgPtr + 24#64) 0#64 v_ptr m.macKey) from rfl,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_ptr
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  have hfits_bm : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨.lengthDelimited, x.msgPtr + 24#64, 0#64, v_ptr, m.macKey, x.bufRef, x.slot, restPtr, rest⟩) :=
    fun evs he => hFit_t2 evs (e2ar_bytesMerge3_zero_tight32 hmb hv_le he)
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨.lengthDelimited, x.msgPtr + 24#64, 0#64, v_ptr, m.macKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 240#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, bytesMergeCapOk_zero, hfits_bm⟩
    (by dsimp only [sliceCursorAt, restPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
  (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_bm
  apply SepWP.exists_elim; intro cap'
  apply SepWP.exists_elim; intro ptr'
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_bm
  wp_focus_pure; intro hsm0
  wp_focus_pure; intro hcap'
  have ht2 : SpqrTightEvs 2 1476 32 evs_bm := e2ar_bytesMerge3_zero_tight32 hmb hv_le hevs_bm
  conv => arg 4; simp only [arm64_norm, hsp]
  apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
  apply SepWP.fold (e2ar_vecU8At_entails_vecU8CapAt hcap') (by sep_focus)
  apply SepWP.fold (e2ar_vecU8CapAt_mono (a := x.msgPtr) (bs := m.rootKey) hrest'_le) (by sep_focus)
  wp_steps_sync_pool ((blkPl_295).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (Entails.of_eq (by dsimp only [e2ar_authLoopPre, authenticatorPBCapAt, e2ar_vecU8CapAt]; sep_ac_rfl))
    (hcont evs_bm _ ht2
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm)

theorem e2ar_auth_ret_exit [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : ProtoAuthenticator} {cur : List (BitVec 8)} {limit : Nat}
    {evs : List AllocEvent}
    (heq_lim : cur.length = limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hsome : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
      some (m, cur))
    (hevs : PostEnv x evs) (hst_eq : st_cur = M.stepEvents evs st0)
    (hpc : s.pc = (blkPl_295).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (e2ar_authLoopPre A lim st_cur s0 s x.bufRef x.slot x.ptr
        (authenticatorPBCapAt A.repAlloc x.msgPtr cur.length m) x.bs cur)
      (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply SepWPp.of_sepWP_ret
  unfold WppPost tlb_authMergeTightSpecOfEnv authMergeSpecOfEnv
  simp only [hsome, authMergeStack, stackAt_skipField3 _ 97 (by decide), e2ar_authLoopPre,
    sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hst_eq, arm64_norm, htr, hsp]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  wp_done

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthStepsR
