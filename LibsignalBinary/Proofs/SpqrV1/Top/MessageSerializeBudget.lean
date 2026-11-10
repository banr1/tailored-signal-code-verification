/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.FnOffEq -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq -- shake: keep
meta import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen -- shake: keep
meta import ProofLib.SepLogic.WP.Apply -- shake: keep
meta import ProofLib.SepLogic.WPp -- shake: keep

/-!
# Budget-Threaded Verification of `<Message>::serialize`

Deterministic allocator event list (`messageSerializeEvents`), envelope (`MessageSerializeEnv`),
and correctness proof for `<spqr::v1::chunked::states::Message>::serialize` (110 instructions)
under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalSpqrV1
  (MAX_VARINT_BYTES_LEN Message MessagePayload MessageType PolyApi
   encodeVarintLoop encode_chunk encode_varint)
open CryptoVerification.SpqrV1.Poly (chunkAt chunkIndexOff)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall allocName doReserveStack reserveCap sessionShimSpec shimName
   tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost bv_len_add_one vecU8Buf vecU8Buf_eq_open_one vecU8Buf_snoc_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (false_eq_true')
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (len_beq_cap_false sp_sub_80_aligned spqrEncodeVarintName spqrEncodeVarintStackX)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost doReserve7_fnAddr_eq encodeVarintLoop_length_le encode_varint_length_le
   extractLsb_hi_append64 extractLsb_lo_append64 list_eq_unpack64_4_of_len32 memRegion_40_split_1_39
   messageAt messagePayloadAt messageSerializeName messageSerializeStackX messageSerialize_fnOff
   pointsToBytes_unpack64_4_eq rem40_ult_31_of_gt rem40_ult_31_of_le
   spqrEncodeVarint_fnAddr_eq stackAt_messageSerialize_eq stackAt_spqrEncodeVarint_to_allocHook
   stackAt_spqrEncodeVarint_to_doReserve vecU8At_eq_header_buf vecU8At_init_40_one vecU8At_sp72_eq
   vecU8Buf_append_32_eq vecU8Buf_eq_open_32)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved fitsEvents_append rustAllocEvents rustReallocEvents
   subroutine_ok_allocNoOom_of_budgetBase)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomExternSpecWithStackBase subroutine_ok_rustCliAllocNoOom_externWithStackBase)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserve7Name doReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget (do_reserve_7_ok_ext_4k)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
  (sepWP_seg_rebase_vm sepWPp_seg_rebase_vm)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (memRegion_24 session2ShimSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
  (SpqrEncodeVarintEnv SpqrEncodeVarintOkExt spqrEncodeVarintEvents_of_spare spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff noAllocShimSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  false_eq_true' extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. Deterministic Allocator Events, Envelope, and Budget Specification -/

/-- Exact deterministic `AllocEvent` list emitted by `<Message>::serialize` on `x`:
    * allocates an initial 40-byte `Vec<u8>` (`rustAllocEvents 40 1`);
    * the two header varints (`epoch` and `index`) and any chunk `index` varint fit inside capacity 40
    without reallocation (`1 + 10 + 10 + 1 + 10 = 32 ≤ 40`);
    * on chunk variants whose encoded prefix `bs4` satisfies `¬ (bs4.length + 32 ≤ 40)`,
    `do_reserve_and_handle [local#7]` grows capacity from `40` to `80`
    (`rustReallocEvents 40 80 1`). -/
def messageSerializeEvents (P_api : PolyApi) (x : MessageSerializeGhost P_api) : List AllocEvent :=
  let bs1 := encode_varint x.msg.epoch [1#8]
  let bs2 := encode_varint (x.index.zeroExtend 64) bs1
  let chunkEvs (tag : BitVec 8) (c : P_api.Chunk) : List AllocEvent :=
    let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
    if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
    else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1
  match x.msg.payload with
  | .none | .ct1Ack _ => rustAllocEvents 40 1
  | .hdr c => chunkEvs 1#8 c
  | .ek c => chunkEvs 2#8 c
  | .ekCt1Ack c => chunkEvs 3#8 c
  | .ct1 c => chunkEvs 5#8 c
  | .ct2 c => chunkEvs 6#8 c

/-- Deterministic allocator event envelope of `<spqr::v1::chunked::states::Message>::serialize`. -/
def MessageSerializeEnv (P_api : PolyApi) (x : MessageSerializeGhost P_api)
    (evs : List AllocEvent) : Prop :=
  evs = messageSerializeEvents P_api x

theorem messageSerializeEnv_events (P_api : PolyApi) (x : MessageSerializeGhost P_api) :
    MessageSerializeEnv P_api x (messageSerializeEvents P_api x) := rfl

theorem fitsEnv_messageSerialize_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (P_api : PolyApi) (x : MessageSerializeGhost P_api) :
    FitsEnv M lim st (MessageSerializeEnv P_api x) ↔
      FitsEvents M lim st (messageSerializeEvents P_api x) :=
  FitsEnv.eq_iff

private theorem fitsEvents_alloc40_of_messageSerialize {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {P_api : PolyApi} {x : MessageSerializeGhost P_api}
    (h : FitsEvents M lim st (messageSerializeEvents P_api x)) :
    FitsEvents M lim st (rustAllocEvents 40 1) := by
  unfold messageSerializeEvents at h
  cases hpay : x.msg.payload <;> simp only [hpay] at h
  · exact h
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · exact h
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1
  · split at h <;> first | exact h | exact ((fitsEvents_append M lim _ _ st).mp h).1

/-- Budget-threaded specification of `<spqr::v1::chunked::states::Message>::serialize` (110
    insns) against `Message.serialize` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEnv M
    lim st (MessageSerializeEnv P_api x)`). -/
def messageSerializeSpecX (P_api : PolyApi) {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (MessageSerializeGhost P_api × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ (s.readReg64 .x1).setWidth 32 = x.index ∧
      s.readReg64 .x8 = x.ret ∧ FitsEnv M lim st (MessageSerializeEnv P_api x)⌝ ∗
      messageAt P_api x.msgA x.msg ∗ memRegion x.ret 24 ∗ A.pool lim st s ∗
      stackAt s.sp messageSerializeStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      messageAt P_api x.msgA x.msg ∗
      vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
      (∃∗ evs : List AllocEvent, ⌜MessageSerializeEnv P_api x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp messageSerializeStackX

/-- `<Message>::serialize` meets `messageSerializeSpecX P_api A lim` on `tripleRatchetProgAtExt
    b ext`. -/
def MessageSerializeOkExt (P_api : PolyApi) (b : BitVec 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr messageSerializeName)
    (messageSerializeSpecX P_api A lim)

/-! ## 2. Bridge & Callee Call Helpers -/

private abbrev fetch_withSvc' :=
  LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux.fetch_withSvc

private theorem fnAddr_trapHooks_eq (b : BitVec 64) (ext : String → Option (State → State))
    (name : String) :
    (libsignalSessionCode.rebase b trapHooks).fnAddr name =
      (tripleRatchetProgAtExt b ext).fnAddr name := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]

private theorem shim_ok_of_contracts4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (session2ShimSpecWithStack allocHookStack) := by
  refine subroutine_ok_outcome_intro fun () R s0 hpc hrun hpre hsp => ?_
  dsimp only [session2ShimSpecWithStack] at hpre
  have hpre' : s0.mem ⊨ (withVmPreserved sessionShimSpec).pre () s0 ∗
      (stackAt s0.sp allocHookStack ∗ R) := by
    dsimp only [withVmPreserved, sessionShimSpec, noAllocShimSpec]
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine (hA.shim_ok_at name k hk).mono_outcome () (stackAt s0.sp allocHookStack ∗ R)
    s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, sessionShimSpec, noAllocShimSpec, session2ShimSpecWithStack]
      at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (by
      rcases hfail with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩ <;>
        exact (not_satisfies_false_sepConj hq).elim)

private theorem alloc_ok_of_contracts4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomExternSpecWithStackBase M A lim false allocHookStack) :=
  subroutine_ok_rustCliAllocNoOom_externWithStackBase (by decide) (by decide)
    (subroutine_ok_allocNoOom_of_budgetBase (hA.alloc_ok_at name k hk))

private theorem sepWPp_of_sepWP_mid {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hPm, hcont⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ := hcont R hPm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

def MsgSerializeCS (s0 s : State) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem MsgSerializeCS.trans {s0 s1 s2 : State}
    (h1 : MsgSerializeCS s0 s1) (h2 : MsgSerializeCS s1 s2) :
    MsgSerializeCS s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

theorem MsgSerializeCS.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) : MsgSerializeCS s1 s2 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2⟩

attribute [local irreducible] Program.fnAddr

/-- Execute a `bl spqr::encode_varint` call inside `<Message>::serialize` when `cap = 40#64` and
    `curBs.length + 10 ≤ 40`, preserving `cap = 40#64`, `ptr`, and budget state `st`. -/
theorem step_call_spqrEncodeVarint_40 {P_api : PolyApi} {M : AllocCostModel}
    (b : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (henc : SpqrEncodeVarintOkExt b A lim ext)
    (val v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (st : M.σ)
    (hlen : curBs.length + 10 ≤ 40)
    {x : MessageSerializeGhost P_api} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgSerializeCS s0 s)
    (hP : P = (vecU8At A.repAlloc v 40#64 ptr curBs ∗ A.pool lim st s ∗
      stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCS s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) sm
        ((vecU8At A.repAlloc v 40#64 ptr (encode_varint val curBs) ∗
          A.pool lim st sm ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  have hloop_le :
      curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤
        (40#64 : BitVec 64).toNat := by
    have h1 := encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN val
    have hm : MAX_VARINT_BYTES_LEN = 10 := rfl
    change curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤ 40; omega
  have hevs_nil := spqrEncodeVarintEvents_of_spare
    (x := EncodeVarintGhost.mk val v 40#64 ptr curBs) hloop_le
  have hfits_enc : FitsEnv M lim st
      (SpqrEncodeVarintEnv (EncodeVarintGhost.mk val v 40#64 ptr curBs)) := by
    intro evs hevs
    dsimp only [SpqrEncodeVarintEnv] at hevs
    rw [hevs, hevs_nil]
    trivial
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_cs
    (x := (EncodeVarintGhost.mk val v 40#64 ptr curBs, st)) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [spqrEncodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hlen, hfits_enc⟩, by convert hm using 1; sep_ac_rfl⟩
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    dsimp only [spqrEncodeVarintSpecX] at hm
    rw [sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm _
    rw [hsp] at hspm
    simp only [spqrEncodeVarintSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun cap' =>
      SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun htrm =>
      SepWPp.pure_elim fun hcap_prop => ?_
    obtain ⟨hcap_eq, hptr_eq⟩ := hcap_prop.2 hloop_le
    rw [hcap_eq, hptr_eq]
    refine SepWPp.weaken_pre (P' := ⌜evs = []⌝ ∗
        ((vecU8At A.repAlloc v 40#64 ptr (encode_varint val curBs) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F))
      (Entails.of_eq (by
        simp only [SpqrEncodeVarintEnv, hevs_nil]
        sep_ac_rfl))
      (SepWPp.pure_elim fun hevs_eq => ?_)
    subst hevs_eq
    simpa only [AllocCostModel.stepEvents_nil] using
      hnext sm hpcm hrunm hspm (htrm.trans htr)
        hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
        (hcs.trans (MsgSerializeCS.of_calleeSavedPreserved hcsm))

private theorem doReserveEvents_40_32 (v ptr : BitVec 64) (curBs : List (BitVec 8))
    (hlen : curBs.length ≤ 32) :
    doReserveEvents (DoReserveCall.mk v 40#64 ptr curBs 32) = rustReallocEvents 40 80 1 := by
  have hres : TripleRatchet.Alloc.DefsBudget.reserveCap (40#64 : BitVec 64).toNat curBs.length 32 = 80 := by
    unfold TripleRatchet.Alloc.DefsBudget.reserveCap reserveCap
    change max (max (curBs.length + 32) (2 * 40)) 8 = 80; omega
  have hne : (40#64 : BitVec 64) ≠ 0#64 := by decide
  unfold doReserveEvents
  simp only [hne, ↓reduceIte, hres]; rfl

/-- Execute `bl do_reserve_and_handle [local#7]` inside `<Message>::serialize` when `cap =
    40#64`, `curBs.length ≤ 32`, and `additional = 32`, growing capacity to `80#64`. -/
private theorem step_call_doReserve7_40 {P_api : PolyApi} {M : AllocCostModel}
    (b : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K b A lim ext)
    (v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (st1 : M.σ)
    (hlen : curBs.length ≤ 32)
    (hfits_res : FitsEvents M lim st1 (rustReallocEvents 40 80 1))
    {x : MessageSerializeGhost P_api} {st0 : M.σ} {R : SepProp}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 32#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgSerializeCS s0 s)
    (hP : P = (vecU8At A.repAlloc v 40#64 ptr curBs ∗ A.pool lim st1 s ∗
      stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ (sm : State) (ptr' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCS s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) sm
        ((vecU8At A.repAlloc v 80#64 ptr' curBs ∗
          A.pool lim (M.stepEvents (rustReallocEvents 40 80 1) st1) sm ∗
          stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  have hres_eq : reserveCap (40#64 : BitVec 64).toNat curBs.length 32 = 80 := by
    unfold reserveCap; change max (max (curBs.length + 32) (2 * 40)) 8 = 80; omega
  have hres_eq' : TripleRatchet.Alloc.DefsBudget.reserveCap (40#64 : BitVec 64).toNat curBs.length 32 = 80 := hres_eq
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  have hevs_eq := doReserveEvents_40_32 v ptr curBs hlen
  have hfits_env : FitsEnv M lim st1 (DoReserveEnv (DoReserveCall.mk v 40#64 ptr curBs 32)) := by
    rw [fitsEnv_doReserve_iff, hevs_eq]; exact hfits_res
  refine CryptoVerification.LibsignalTripleRatchet.Prost.SepWPp.call_cs
    (x := (DoReserveCall.mk v 40#64 ptr curBs 32, st1))
    (F := memRegion (sp - 80#64 - 16464#64) 12256 ∗ F)
    (do_reserve_7_ok_ext_4k hA) hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)] at hm
    simp only [doReserveSpec, TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, by rw [hres_eq']; decide, hfits_env⟩,
      by convert hm using 1; sep_ac_rfl⟩
  · intro _ _ _ _ hm; exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    dsimp only [doReserveSpec, TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack] at hm
    rw [sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm _
    rw [hsp] at hspm
    simp only [doReserveSpec, TripleRatchet.Alloc.DefsBudget.doReserveSpec,
      TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack, hsp, hres_eq, hevs_eq,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm ptr' hpcm hrunm hspm (htrm.trans htr)
      hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
      (hcs.trans (MsgSerializeCS.of_calleeSavedPreserved hcsm)))
    rw [stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Epilogue & Chunk Step Lemmas -/

private def poolPostAt (P_api : PolyApi) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (x : MessageSerializeGhost P_api)
    (st0 : M.σ) (sf : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜MessageSerializeEnv P_api x evs⌝ ∗
    A.pool lim (M.stepEvents evs st0) sf

/-- Shared return tail (`+0x168..+0x188`, `360..392`): stores `(ptrFinal, capFinal, len)` to
    `[x19]`, restores callee-saved registers & `sp`, and returns. -/
theorem step_msgSerialize_ret {P_api : PolyApi} {M : AllocCostModel}
    (b : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api) (st0 : M.σ) (evsDone : List AllocEvent)
    (capFinal ptrFinal v80 v56 r0 r1 r2 : BitVec 64) (bsFinal : List (BitVec 8))
    (hser : bsFinal = x.msg.serialize x.index)
    (hevs : MessageSerializeEnv P_api x evsDone) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 360#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 bsFinal.length) (hx19 : s.readReg64 .x19 = x.ret)
    (hcs : MsgSerializeCS s0 s)
    (hP : P = (((s0.sp - 72#64) ↦₆₄ capFinal) ∗ ((s0.sp - 64#64) ↦₆₄ ptrFinal) ∗
       ((s0.sp - 56#64) ↦₆₄ v56) ∗ vecU8Buf A.repAlloc capFinal ptrFinal bsFinal ∗
       messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents evsDone st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 360 392
  simp +singlePass only [fnAddr_trapHooks_eq b ext, fetch_withSvc' _ noSyscalls] at *
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP; rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs⟩
  apply sepWPp_seg_rebase_vm (mid := s0.readReg64 .lr)
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩; intro hm_f
  have hvec_pack : (x.ret ↦₆₄ capFinal) ∗ ((x.ret + 8#64) ↦₆₄ ptrFinal) ∗
      ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (x.msg.serialize x.index).length) ∗
      vecU8Buf A.repAlloc capFinal ptrFinal bsFinal =
      vecU8At A.repAlloc x.ret capFinal ptrFinal (x.msg.serialize x.index) := by
    rw [← hser, vecU8At_eq_header_buf]
  show _ ⊨ (⌜_ = s0.trace⌝ ∗ messageAt P_api x.msgA x.msg ∗
      vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
      poolPostAt P_api A lim x st0 _ ∗
      stackAt s0.sp messageSerializeStackX) ∗ R
  simp only [vecU8, stackAt_messageSerialize_eq, sepExists_sepConj_left,
    sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v80, capFinal, ptrFinal, v56, s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x22,
    s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19, capFinal, ptrFinal,
    by simp only [arm64_norm, *], ?_⟩
  rw [← hvec_pack]; unfold poolPostAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc]
  refine ⟨evsDone, ?_⟩
  rw [eq_true hevs, pure_true_sepConj]
  convert hm_f using 1; sep_ac_rfl

/-- Non-chunk epilogue (`+0x15c..+0x188`, `348..392`): stores `tag` and finishes via
    `step_msgSerialize_ret`. -/
theorem step_msgSerialize_epilogue_no_chunk {P_api : PolyApi} {M : AllocCostModel}
    (b : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api) (st0 : M.σ) (evsDone : List AllocEvent)
    (ptr v80 r0 r1 r2 : BitVec 64) (bs2 : List (BitVec 8)) (tag : BitVec 8)
    (hlt40 : bs2.length < (40#64 : BitVec 64).toNat)
    (hser : bs2 ++ [tag] = x.msg.serialize x.index)
    (hevs : MessageSerializeEnv P_api x evsDone) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length)
    (hx22 : (s.readReg64 .x22).setWidth 8 = tag) (hcs : MsgSerializeCS s0 s)
    (hP : P = (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗ messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents evsDone st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 348 360
  simp +singlePass only [fnAddr_trapHooks_eq b ext, fetch_withSvc' _ noSyscalls] at *
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP; have hlen1 := bv_len_add_one bs2 tag
  rw [vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs2,
    vecU8Buf_eq_open_one A.repAlloc 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_seg_rebase_vm (mid := entry + 360#64)
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
  have hvec_snoc := vecU8Buf_snoc_eq A.repAlloc 40#64 ptr bs2 tag hlt40
  exact step_msgSerialize_ret b A lim ext x st0 evsDone 40#64 ptr v80
    (BitVec.ofNat 64 bs2.length) r0 r1 r2 (bs2 ++ [tag]) hser hevs
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm]⟩)
    (by rw [← hvec_snoc]; sep_ac_rfl)

/-- Chunk 32-byte copy and epilogue (`+0x13c..+0x158` + `+0x168..+0x188`, `316..344` +
    `360..392`). -/
theorem step_msgSerialize_copy_and_epilogue {P_api : PolyApi} {M : AllocCostModel}
    (b : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api) (st0 : M.σ) (evsDone : List AllocEvent)
    (c : P_api.Chunk) (capFinal ptrFinal v80 r0 r1 r2 : BitVec 64)
    (bs4 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hle32 : bs4.length + 32 ≤ capFinal.toNat)
    (hser : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index)
    (hevs : MessageSerializeEnv P_api x evsDone)
    (hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hcs : MsgSerializeCS s0 s)
    (hP : P = (vecU8At A.repAlloc (s0.sp - 72#64) capFinal ptrFinal bs4 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents evsDone st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 316 344
  simp +singlePass only [fnAddr_trapHooks_eq b ext, fetch_withSvc' _ noSyscalls] at *
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP
  have hdata_len : (P_api.chunkData c).toList.length = 32 := (P_api.chunkData c).property
  obtain ⟨w0, w1, w2, w3, hw⟩ := list_eq_unpack64_4_of_len32 (P_api.chunkData c).toList hdata_len
  have hchunk_unfold :
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
        ((x.msgA + 0x0a#64) ↦₆₄ w0) ∗ ((x.msgA + 0x12#64) ↦₆₄ w1) ∗ ((x.msgA + 0x1a#64) ↦₆₄ w2) ∗
        ((x.msgA + 0x22#64) ↦₆₄ w3) ∗ ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; dsimp only; rw [hw, pointsToBytes_unpack64_4_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl
  have hlen32_bv :
      BitVec.ofNat 64 bs4.length + 32#64 =
        BitVec.ofNat 64 (bs4 ++ (P_api.chunkData c).toList).length := by
    simp only [List.length_append, hdata_len, BitVec.ofNat_add]
  rw [hchunk_unfold, vecU8At_sp72_eq A.repAlloc s0.sp capFinal ptrFinal bs4,
    vecU8Buf_eq_open_32 A.repAlloc capFinal ptrFinal bs4 hle32]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  apply sepWPp_seg_rebase_vm (mid := entry + 360#64)
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
  have hvec_app := vecU8Buf_append_32_eq A.repAlloc capFinal ptrFinal bs4
    (P_api.chunkData c).toList w0 w1 w2 w3 hle32 hw hdata_len
  exact step_msgSerialize_ret b A lim ext x st0 evsDone capFinal ptrFinal v80
    (BitVec.ofNat 64 bs4.length) r0 r1 r2 (bs4 ++ (P_api.chunkData c).toList) hser hevs
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm]⟩)
    (by rw [← hmsg_eq, hchunk_unfold, ← hvec_app]; sep_ac_rfl)

/-- Full chunk branch (`+0x10c..+0x188` & `+0x190..+0x1ac`, `268..392` & `400..428`): appends
    `tag` to `bs2`, calls `spqr::encode_varint` on `(P_api.chunkIndex c).zeroExtend 64`,
    reserves 32 bytes if `40 - bs4.length ≤ 31`, and finishes via
    `step_msgSerialize_copy_and_epilogue`. -/
private theorem step_msgSerialize_chunk {P_api : PolyApi} {M : AllocCostModel}
    (b : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K b A lim ext) (henc : SpqrEncodeVarintOkExt b A lim ext)
    {s0 s : State} (x : MessageSerializeGhost P_api) (st0 : M.σ)
    (c : P_api.Chunk) (ptr v80 r0 r1 r2 : BitVec 64)
    (bs2 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hlen21 : bs2.length ≤ 21)
    (hser : encode_chunk c (bs2 ++ [tag]) = x.msg.serialize x.index)
    (hevs_chunk : messageSerializeEvents P_api x =
      let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
      if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
      else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1)
    (hfits_all : FitsEvents M lim st0 (messageSerializeEvents P_api x))
    (hmsg_eq :
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg)
    {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length) (hx22 : (s.readReg64 .x22).setWidth 8 = tag)
    (hcs : MsgSerializeCS s0 s)
    (hP : P =
      (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool lim (M.stepEvents (rustAllocEvents 40 1) st0) s ∗
       stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 268 316
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 400 428
  simp +singlePass only [fnAddr_trapHooks_eq b ext, fetch_withSvc' _ noSyscalls] at *
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by change bs2.length < 40; omega
  have hlen1 := bv_len_add_one bs2 tag
  have hchunk_idx :
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
        ((x.msgA + 0x0a#64) ↦ₛ (P_api.chunkData c).toList) ∗
        ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hchunk_idx, vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs2,
    vecU8Buf_eq_open_one A.repAlloc 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_seg_rebase_vm
    (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize"))
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg1 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg1 (hnext := ?_)
  have hvec_snoc := vecU8Buf_snoc_eq A.repAlloc 40#64 ptr bs2 tag hlt40
  have hvec_bs3 := (vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr (bs2 ++ [tag])).symm
  have hpc_enc :
      entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize") =
        (tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName := by
    rw [← hentry, spqrEncodeVarint_fnAddr_eq]
  refine step_call_spqrEncodeVarint_40 (P_api := P_api) (x := x) (st0 := st0) (R := R)
    b A lim ext henc ((P_api.chunkIndex c).zeroExtend 64) (s0.sp - 72#64) ptr s0.sp (entry + 296#64)
    (bs2 ++ [tag]) (M.stepEvents (rustAllocEvents 40 1) st0)
    (by simp only [List.length_append, List.length_singleton]; omega)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm]⟩)
    (by rw [hchunk_idx, ← hvec_bs3, ← hvec_snoc]; sep_ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx19m hx20m _ _ _ hcsm
  have hx19m' : sm.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
  have hx20m' : sm.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
  let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
  have hbs4_len : bs4.length ≤ 32 := by
    have := encode_varint_length_le ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
    simp only [List.length_append, List.length_singleton] at this; dsimp only [bs4]; omega
  have hser4 : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index := hser
  change SepWPp _ _ sm ((vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs4 ∗ _) ∗ _) _ _
  rw [vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs4]
  by_cases hle32 : bs4.length + 32 ≤ 40
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_le hle32
    have hevs_le : MessageSerializeEnv P_api x (rustAllocEvents 40 1) := by
      unfold MessageSerializeEnv
      rw [hevs_chunk]; dsimp only [bs4] at hle32; simp only [hle32, ↓reduceIte]
    apply sepWPp_seg_rebase_vm (mid := entry + 316#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg2 => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg2 (hnext := ?_)
    exact step_msgSerialize_copy_and_epilogue b A lim ext x st0 (rustAllocEvents 40 1)
      c 40#64 ptr v80 r0 r1 r2 bs4 tag msgTail hle32 hser4 hevs_le hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_gt hle32 (by dsimp only [bs4] at hbs4_len ⊢; omega)
    have hevs_gt_eq : messageSerializeEvents P_api x =
        rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      rw [hevs_chunk]; dsimp only [bs4] at hle32; simp only [hle32, ↓reduceIte]
    have hevs_gt : MessageSerializeEnv P_api x
        (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1) :=
      hevs_gt_eq.symm
    have hfits_realloc :
        FitsEvents M lim (M.stepEvents (rustAllocEvents 40 1) st0) (rustReallocEvents 40 80 1) := by
      rw [hevs_gt_eq] at hfits_all
      exact ((fitsEvents_append M lim _ _ st0).mp hfits_all).2
    have hpc_res :
        entry + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"
          "<spqr::v1::chunked::states::Message>::serialize") =
          (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name := by
      rw [← hentry, doReserve7_fnAddr_eq]
    apply sepWPp_seg_rebase_vm
      (mid := entry + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"
        "<spqr::v1::chunked::states::Message>::serialize"))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg2 => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg2 (hnext := ?_)
    refine step_call_doReserve7_40 (P_api := P_api) (x := x) (st0 := st0) (R := R)
      b A lim ext hA (s0.sp - 72#64) ptr s0.sp (entry + 420#64) bs4
      (M.stepEvents (rustAllocEvents 40 1) st0) hbs4_len hfits_realloc
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl) ?_
    intro sm2 ptr' hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
    have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
    have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
    rw [vecU8At_sp72_eq A.repAlloc s0.sp 80#64 ptr' bs4, ← M.stepEvents_append]
    apply sepWPp_seg_rebase_vm (mid := entry + 316#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg3 => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg3 (hnext := ?_)
    have hle80 : bs4.length + 32 ≤ (80#64 : BitVec 64).toNat := by
      change bs4.length + 32 ≤ 80; dsimp only [bs4] at hbs4_len ⊢; omega
    exact step_msgSerialize_copy_and_epilogue b A lim ext x st0
      (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1)
      c 80#64 ptr' v80 r0 r1 r2 bs4 tag msgTail hle80 hser4 hevs_gt hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcsm2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩)
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)

/-! ## 4. Entry Block & Main Theorem -/

/-- Entry block (`+0x000..+0x060`, `0..96`): saves callee-saved registers, allocates 40-byte
    buffer via `__rust_alloc(40, 1)` under `FitsEvents M lim st0 (rustAllocEvents 40 1)`, writes
    `[1#8]`, and executes the first two `spqr::encode_varint` calls (`x.msg.epoch` and
    `x.index.zeroExtend 64`), arriving at `entry + 96#64`. -/
private theorem step_msgSerialize_entry {P_api : PolyApi} {M : AllocCostModel}
    (b : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K b A lim ext) (henc : SpqrEncodeVarintOkExt b A lim ext)
    {s0 : State} (x : MessageSerializeGhost P_api) (st0 : M.σ)
    (hfits40 : FitsEvents M lim st0 (rustAllocEvents 40 1))
    (v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2 : BitVec 64)
    {R P : SepProp} {Q : State → SepProp → Prop}
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName)
    (hrun0 : s0.status = .Running) (halign : s0.sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.msgA) (hx1 : (s0.readReg64 .x1).setWidth 32 = x.index)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hP : P =
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool lim st0 s0 ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
      ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8))
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      let bs1 := encode_varint x.msg.epoch [1#8]
      let bs2 := encode_varint (x.index.zeroExtend 64) bs1
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 96#64 →
      sm.status = .Running → sm.sp = s0.sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret → sm.readReg64 .x20 = x.msgA →
      MsgSerializeCS s0 sm → bs2.length ≤ 21 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) sm
        (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗
         (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
         (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
         A.pool lim (M.stepEvents (rustAllocEvents 40 1) st0) sm ∗
         stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        Q (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P Q
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (messageSerializeSpecX P_api A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have hfn := messageSerialize_fnOff
  have hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr messageSerializeName +
        BitVec.ofNat 64 (num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_no_alloc_shim_is_unstable_v2")))
      (session2ShimSpecWithStack allocHookStack) :=
    shim_ok_of_contracts4k hA (name := messageSerializeName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr messageSerializeName +
        BitVec.ofNat 64 (num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_alloc")))
      (rustCliAllocNoOomExternSpecWithStackBase M A lim false allocHookStack) :=
    alloc_ok_of_contracts4k hA (name := messageSerializeName)
      (k := num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_alloc"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 0 96
  simp +singlePass only [fnAddr_trapHooks_eq b ext, fetch_withSvc' _ noSyscalls] at *
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP
  rw [stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64)]
  have hsp0 : s0.spAligned = true := by simp only [State.spAligned, beq_iff_eq]; exact halign
  have hpos40 : 0 < 40 := by decide
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbound40 : 40 + 1 ≤ 2 ^ 63 := by decide
  have hal31 : 1 ≤ 2 ^ 31 := by decide
  have hlay40 : RustLayoutOk 40 1 := ⟨⟨hpos40, hpow1, hbound40⟩, hal31⟩
  rcases hfits40 with ⟨⟨hmax40, henf, hram, hva⟩, _⟩
  apply sepWPp_of_sepWP_mid (mid := entry + 52#64)
  wp_steps_rebase_pool
    (entry + bv% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_rebase_pool
    (entry + bv% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_alloc"))
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (40, 1, st0)
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  have hoom : sf_1.readReg64 .x0 ≠ 0#64 := by assumption
  have hoom_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  rw [memRegion_40_split_1_39 (sf_1.readReg64 .x0)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  apply sepWPp_seg_rebase_vm
    (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize"))
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg1 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg1 (hnext := ?_)
  have hpc_enc :
      entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize") =
        (tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName := by
    rw [← hentry, spqrEncodeVarint_fnAddr_eq]
  have hsp_sf : sf.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
  refine step_call_spqrEncodeVarint_40 (P_api := P_api) (x := x) (st0 := st0) (R := R)
    b A lim ext henc x.msg.epoch (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp (entry + 84#64)
    [1#8] (M.stepEvents (rustAllocEvents 40 1) st0) (by decide)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *])
    (by
      have hinit := vecU8At_init_40_one A.repAlloc (s0.sp - 72#64) (sf_1.readReg64 .x0) hoom
      simp only [arm64_norm] at hinit
      have hlive_eq : A.live (sf_1.readReg64 .x0) 40 1 = A.repAlloc.live (sf_1.readReg64 .x0) 40 1 := rfl
      rw [hsp_sf, hlive_eq, ← hinit, stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64),
        show s0.sp - 80#64 - 16464#64 = s0.sp - 16544#64 by bv_omega]
      simp only [arm64_norm]
      sep_ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19m1 hx20m1 hx21m1 _ _ hcsm1
  have hx19m1' : sm1.readReg64 .x19 = x.ret := by simp only [wp_norm, arm64_norm, *]
  have hx20m1' : sm1.readReg64 .x20 = x.msgA := by simp only [wp_norm, arm64_norm, *]
  have hx21m1' : (sm1.readReg64 .x21).setWidth 32 = x.index := by
    rw [hx21m1]; simp only [wp_norm, arm64_norm, *]
  let bs1 := encode_varint x.msg.epoch [1#8]
  have hbs1_len : bs1.length ≤ 11 := by
    have := encode_varint_length_le x.msg.epoch [1#8]; simp only [List.length_singleton] at this; omega
  apply sepWPp_seg_rebase_vm
    (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize"))
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg2 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg2 (hnext := ?_)
  refine step_call_spqrEncodeVarint_40 (P_api := P_api) (x := x) (st0 := st0) (R := R)
    b A lim ext henc (x.index.zeroExtend 64) (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp (entry + 96#64)
    bs1 (M.stepEvents (rustAllocEvents 40 1) st0) (by omega)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcsm1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm]⟩)
    (by sep_ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
  have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
  have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
  have hbs2_len : (encode_varint (x.index.zeroExtend 64) bs1).length ≤ 21 := by
    have := encode_varint_length_le (x.index.zeroExtend 64) bs1; omega
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext sm2 (sf_1.readReg64 .x0) hpcm2 hrunm2 hspm2 htrm2 hx19m2' hx20m2' hcsm2 hbs2_len)

/-- `<spqr::v1::chunked::states::Message>::serialize` (110 insns) meets `messageSerializeSpecX
    P_api A lim` on `tripleRatchetProgAtExt b ext` under `AllocContracts4K`. -/
theorem messageSerialize_ok_4k (P_api : PolyApi) (b : BitVec 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K b A lim ext) (henc : SpqrEncodeVarintOkExt b A lim ext) :
    MessageSerializeOkExt P_api b A lim ext := by
  unfold MessageSerializeOkExt; apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre hsp0
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp0
  simp only [messageSerializeSpecX, messageAt, memRegion_24, stackAt_messageSerialize_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with
    ⟨v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, r2, r1, r0, ⟨hx0, hx1, hx8, hfits_env⟩, hpre⟩
  have hfits_all : FitsEvents M lim st0 (messageSerializeEvents P_api x) :=
    (fitsEnv_messageSerialize_iff P_api x).mp hfits_env
  have hfits40 := fitsEvents_alloc40_of_messageSerialize hfits_all
  refine ⟨(x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool lim st0 s0 ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
      ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8),
    R, by convert hpre using 1; sep_ac_rfl,
    step_msgSerialize_entry b A lim ext hA henc x st0 hfits40
      v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2
      hpc0 hrun0 halign hx0 hx1 hx8 rfl ?_⟩
  intro sm ptr bs1 bs2 hpcm hrunm hspm htrm hx19m hx20m hcsm hbs2_len
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by
    change bs2.length < 40; dsimp only [bs2, bs1] at hbs2_len ⊢; omega
  have hbeq := len_beq_cap_false hlt40
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 96 268
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 344 348
  msgSerialize_fetches_range b trapHooks messageSerialize_fnOff 392 400
  simp +singlePass only [fnAddr_trapHooks_eq b ext, fetch_withSvc' _ noSyscalls] at *
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches
  change SepWPp _ _ sm (vecU8At A.repAlloc (s0.sp - 72#64) 40#64 ptr bs2 ∗
    (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗ _) _ _
  rw [vecU8At_sp72_eq A.repAlloc s0.sp 40#64 ptr bs2]
  cases hpay : x.msg.payload with
  | none =>
    simp only [messagePayloadAt]
    apply sepWPp_seg_rebase_vm (mid := entry + 348#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
    have hser : bs2 ++ [0#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs : MessageSerializeEnv P_api x (rustAllocEvents 40 1) := by
      unfold MessageSerializeEnv messageSerializeEvents; simp only [hpay]
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 0#8) ∗
        memRegion (x.msgA + 0x09#64) 39 = messageAt P_api x.msgA x.msg := by
      unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk b A lim ext x st0 (rustAllocEvents 40 1)
      ptr v80 r0 r1 r2 bs2 0#8 hlt40 hser hevs
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCS, arm64_norm, *]))
      (by rw [vecU8At_sp72_eq, ← hmsg_eq]; sep_ac_rfl)
  | ct1Ack b_ack =>
    simp only [messagePayloadAt]
    apply sepWPp_seg_rebase_vm (mid := entry + 348#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
    have hser : bs2 ++ [4#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs : MessageSerializeEnv P_api x (rustAllocEvents 40 1) := by
      unfold MessageSerializeEnv messageSerializeEvents; simp only [hpay]
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 4#8) ∗
        ((x.msgA + 0x09#64) ↦₈ (if b_ack then 1#8 else 0#8)) ∗ memRegion (x.msgA + 0x0a#64) 38 =
        messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk b A lim ext x st0 (rustAllocEvents 40 1)
      ptr v80 r0 r1 r2 bs2 4#8 hlt40 hser hevs
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCS, arm64_norm, *]))
      (by rw [vecU8At_sp72_eq, ← hmsg_eq]; sep_ac_rfl)
  | hdr c =>
    simp only [messagePayloadAt]
    apply sepWPp_seg_rebase_vm (mid := entry + 268#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
    have hser : encode_chunk c (bs2 ++ [1#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [1#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 1#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by
      unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A lim ext hA henc x st0 c ptr v80 r0 r1 r2 bs2 1#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hfits_all hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCS, arm64_norm, *]))
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ek c =>
    simp only [messagePayloadAt]
    apply sepWPp_seg_rebase_vm (mid := entry + 268#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
    have hser : encode_chunk c (bs2 ++ [2#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [2#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 2#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by
      unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A lim ext hA henc x st0 c ptr v80 r0 r1 r2 bs2 2#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hfits_all hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCS, arm64_norm, *]))
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ekCt1Ack c =>
    simp only [messagePayloadAt]
    apply sepWPp_seg_rebase_vm (mid := entry + 268#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
    have hser : encode_chunk c (bs2 ++ [3#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [3#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 3#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by
      unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A lim ext hA henc x st0 c ptr v80 r0 r1 r2 bs2 3#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hfits_all hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCS, arm64_norm, *]))
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ct1 c =>
    simp only [messagePayloadAt]
    apply sepWPp_seg_rebase_vm (mid := entry + 268#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
    have hser : encode_chunk c (bs2 ++ [5#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [5#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 5#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by
      unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A lim ext hA henc x st0 c ptr v80 r0 r1 r2 bs2 5#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hfits_all hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCS, arm64_norm, *]))
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)
  | ct2 c =>
    simp only [messagePayloadAt]
    apply sepWPp_seg_rebase_vm (mid := entry + 268#64)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_seg => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg (hnext := ?_)
    have hser : encode_chunk c (bs2 ++ [6#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hevs_chunk : messageSerializeEvents P_api x =
        let bs4 := encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [6#8])
        if bs4.length + 32 ≤ 40 then rustAllocEvents 40 1
        else rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 := by
      unfold messageSerializeEvents; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 6#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by
      unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A lim ext hA henc x st0 c ptr v80 r0 r1 r2 bs2 6#8
      (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hevs_chunk hfits_all hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCS, arm64_norm, *]))
      (by rw [vecU8At_sp72_eq]; sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
