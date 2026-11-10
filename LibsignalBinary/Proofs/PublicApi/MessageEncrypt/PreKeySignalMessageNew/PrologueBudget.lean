/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueClonesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeySignalMessage::new` Prologue Composition

Relocatable `[LibsignalPlacement]` wire-struct stack packing, `encoded_len` calls, `serialized`
buffer allocation, and full prologue composition (`+0x000..+0x25c` to `SeamA_placed`) on block `41`
under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (versionByte)
open CryptoGames.LibsignalSessionApi (KyberPayload)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCl
   blkPl_205 lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym ls_hook_ok_of_mem lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf)
open CryptoVerification.LibsignalPublicApiRepr (optKyberAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41 blkLib_eq_41 blkPl_119)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall preKeyMsgNewStack)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgFrameGhost PreKeyMsgWireLengthsFit preKeyMsgSubStack preKeyMsgEncodedLenStack
   optKyberCopyBuf wirePreKeySignalMessageAt preKeyMsgFrameSlotsAt preKeyMsgFrameSlotsAt'
   preKeyMsgFrameSlotsAt_one_eq_vec preKeyMsgHeapAt preKeyMsgNewEntry_placed model_serialized_length)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
  (memRegion_wire_128 pack_wirePreKeySignalMessageAt unpack_wirePreKeySignalMessageAt
   versionByte_word_eq' preKeyMsgWireLengthsFit_protoMsg preKeyMsg_encLen_overflow_checks
   pack_serPrefix0 stackAt_allocHook_split_encodedLen stackAt_preKeyMsgSubStack_to_allocHook
   stackAt_preKeyMsgNewStack_ready optKyberAt_eq_word0_and_rest optKyberAt_length_lt
   preKeyMsg_convert_344 setWidth8_setWidth32 setWidth32_zeroExtend64 kyberIdOf
   entails_of_sep_focus satisfies_of_sep_focus)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
   AllocCallPreserved VmPreserved FitsEvents fitsEvents_append rustAllocEvents
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec framelessMemcpyBudgetSpec
   publicKeySerializeEvents publicKeySerializeSpec
   subroutine_ok_noAllocShim_of_sessionShimBudget
   subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (PreKeyMsgNewEnv PreKeyMsgNewRawEnv kyberCopyEvs preKeyMsgNewRawPrologueEvents
   preKeyMsgNewRawEvents preKeyMsgNewSpec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
  (preKeyMsgEncodedLenSpec PreKeyMsgEncodedLenPlacedOk SeamA_placed PreKeyMsgSegExit_placed)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
  (preKeyMsg_seq_wpp_lscl preKeyMsg_shim_placed_ok preKeyMsg_alloc_placed_ok
   preKeyMsg_memcpy_placed_ok preKeyMsg_publicKeySerialize_placed_ok
   preKeyMsg_publicKeySerialize_placed_ok_noAllocShim preKeyMsg_encodedLen_placed_ok)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueClonesBudget
  (kyberCloneEvs pkSerialize2Evs msgCloneEvs preKeyMsg_entry_to_04c_wp_placed
   preKeyMsg_kyber_clone_wpp_placed_of_ok preKeyMsg_pk_serialize_wpp_placed_of_ok
   preKeyMsg_msg_clone_wpp_placed_of_ok)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved trapHooks
   vmPreserved_refl_iff vmPreserved_setPC vmPreserved_advancePC vmPreserved_setPState
   vmPreserved_writeReg64 vmPreserved_writeReg32 vmPreserved_writeReg
   vmPreserved_writeVReg128 vmPreserved_writeVReg64 vmPreserved_writeVReg32
   vmPreserved_applyWriteback vmPreserved_setStatus vmPreserved_appendTrace
   vmPreserved_setFs vmPreserved_stepExclLoop tpidrEl0_applyWriteback)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl h

private theorem subroutine_ok_withLsCl_of_plain [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCl lsmpl spec) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [withLsCl] at hpre
  rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre'⟩ := hpre
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre' hsp hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hsteps.keepsFrozen, hpost⟩
  · exact Or.inr hrest

private theorem preKeyMsg_seq_wp_vm_lscl [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P1 F : SepProp} {P2 : State → SepProp}
    {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P1 (fun sm P_m => VmPreserved s sm ∧ φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem →
      VmPreserved s sm → φ sm → SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hvm, hφ, hent⟩ | ⟨_, hoom⟩⟩ := h1.elim hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hvm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem entails_focus_left {P P1 P1' F Q : SepProp}
    (h1 : P1 ⊢ P1')
    (hf : P = P1 ∗ F)
    (h2 : P1' ∗ F ⊢ Q) :
    P ⊢ Q := by
  rw [hf]
  exact Entails.trans (sepConj_mono_left h1) h2

private theorem optKyberAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberAt (A.atState lim st s) a ptr kp = optKyberAt A.repAlloc a ptr kp := by
  cases kp <;> rfl

private theorem signalMessageAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g a m) :
    signalMessageAt (A.atState lim st s) g a m = signalMessageAt A.repAlloc g a m := rfl

private theorem vecU8At_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At (A.atState lim st s) v cap ptr bs = vecU8At A.repAlloc v cap ptr bs := rfl

private theorem optKyberCopyBuf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberCopyBuf (A.atState lim st s) ptr kp = optKyberCopyBuf A.repAlloc ptr kp := by
  cases kp <;> rfl

private theorem boxU8Buf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8Buf (A.atState lim st s) ptr bs = boxU8Buf A.repAlloc ptr bs := rfl

/-! ## `serialized` Buffer Allocation Events -/

def serAllocEvs (x : PreKeyMsgNewCall) : List AllocEvent :=
  rustAllocEvents (x.protoMsg.encode.length + 1) 1

private theorem prologueEvents_eq (x : PreKeyMsgNewCall) :
    preKeyMsgNewRawPrologueEvents x.kp x.msg.serialized.length x.model.serialized.length =
      kyberCloneEvs x.kp ++ pkSerialize2Evs ++ msgCloneEvs x.msg ++ serAllocEvs x := by
  have hky : kyberCopyEvs x.kp = kyberCloneEvs x.kp := by cases x.kp <;> rfl
  simp only [preKeyMsgNewRawPrologueEvents, hky, pkSerialize2Evs, publicKeySerializeEvents,
    msgCloneEvs, serAllocEvs, model_serialized_length]

/-! ## Wire Struct Stack Packing (`+0x1ac..+0x1f0`) -/

theorem preKeyMsg_store_wire_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr w352 : BitVec 64)
    (w344_32 pkId32 kyberId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hpk : ∀ v, x.preKeyId = some v → pkId32 = v)
    (hkyId : ∀ k, x.kp = some k → kyberId32 = k.preKeyId)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63) (s : State)
    (hpc : s.pc = (blkPl_41).base + 428#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ikSerPtr) (hx8 : s.readReg64 .x8 = 1#64)
    (hx19 : s.readReg64 .x19 = kyberCap) (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = x.regId.zeroExtend 64) (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64) (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (lsProg_41 H) ((blkPl_41).base + 496#64) s
      (((sp0 - 352#64) ↦₆₄ w352) ∗ ((sp0 - 344#64) ↦₃₂ w344_32) ∗ ((sp0 - 328#64) ↦₃₂ x.spk) ∗
       ((sp0 - 324#64) ↦₃₂ kyberId32) ∗ ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
       ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
       ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
       memRegion (sp0 - 272#64) 128 ∗ optKyberCopyBuf A kyberCopyPtr x.kp ∗
       boxU8Buf A bkSerPtr x.baseKey.serialize ∗ boxU8Buf A ikSerPtr x.ik.serialize ∗
       boxU8Buf A msgCopyPtr x.msg.serialized)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x0 = sp0 - 272#64 ∧
         sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x23 = x.regId.zeroExtend 64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧ sm.readReg64 .x26 = msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ((sp0 - 352#64) ↦₆₄ ikSerPtr) ∗ ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 328#64) ↦₃₂ x.spk) ∗ ((sp0 - 324#64) ↦₃₂ kyberId32) ∗
          ((sp0 - 320#64) ↦₆₄ kyberCopyPtr) ∗
          ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
          ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
          wirePreKeySignalMessageAt A (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
            (sp0 - 272#64) x.protoMsg)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx0 hx8 hx19 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
  rw [memRegion_wire_128 sp0]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · simp only [State.spAligned, wp_norm, arm64_norm, *]
    · have hpack := pack_wirePreKeySignalMessageAt A x sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr
        msgCopyPtr pkId32 kyberId32 hkyCap hpk hkyId hmsg_len
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hpack)))))))
      simp only [← hkyCap, Option.isSome, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

/-! ## `encoded_len` Calls and `serialized` Allocation (`+0x1f0..+0x25c`) -/

theorem preKeyMsg_alloc_ser_wpp_placed_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_shim : subroutine_ok (lsProg_41 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (h_alloc : subroutine_ok (lsProg_41 H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false))
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A.repAlloc H)
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
      w368 w144 w136 w128 : BitVec 64) (ver32 pkId32 : BitVec 32)
    (st : M.σ)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (hver : ver32.setWidth 8 = x.ver) (hfit : x.model.serialized.length < 2 ^ 42)
    (hfits : FitsEvents M lim st (serAllocEvs x))
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 496#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 272#64) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 604#64) s
      (((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
       wirePreKeySignalMessageAt A.repAlloc
         (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
         (sp0 - 272#64) x.protoMsg ∗
       ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ serPtr : BitVec 64,
          ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          memRegion (sp0 - 272#64) 128 ∗
          vecU8At A.repAlloc (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length)
            serPtr [versionByte x.ver] ∗
          optKyberCopyBuf A.repAlloc kyberCopyPtr x.kp ∗
          boxU8Buf A.repAlloc bkSerPtr x.baseKey.serialize ∗
          boxU8Buf A.repAlloc ikSerPtr x.ik.serialize ∗
          boxU8Buf A.repAlloc msgCopyPtr x.msg.serialized ∗
          A.pool lim (M.stepEvents (serAllocEvs x) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) := by
  have hunpack := unpack_wirePreKeySignalMessageAt A.repAlloc x sp0 kyberCap kyberCopyPtr
    bkSerPtr ikSerPtr msgCopyPtr hkyCap hky_len hmsg_len
  have hver_byte :
      BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (ver32 <<< 4)) = versionByte x.ver := by
    rw [versionByte_word_eq' ver32, hver]
  clear hkyCap hky_len hmsg_len hver
  have henc := preKeyMsg_encodedLen_placed_ok hEncLen
  have h_shim_cl := subroutine_ok_withLsCl_of_plain h_shim
  have h_alloc_cl := subroutine_ok_withLsCl_of_plain h_alloc
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have hmod_len : x.model.serialized.length = x.protoMsg.encode.length + 1 :=
    model_serialized_length x
  have hfit62 : x.protoMsg.encode.length + 1 < 2 ^ 62 := by omega
  have hwire_fit : PreKeyMsgWireLengthsFit x.protoMsg :=
    preKeyMsgWireLengthsFit_protoMsg x (by omega)
  have hlay : RustLayoutOk (x.protoMsg.encode.length + 1) 1 :=
    ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
  clear hfit
  obtain ⟨hovf_ult, hovf_msb, hovf_hi, hovf_add, hovf_toNat⟩ :=
    preKeyMsg_encLen_overflow_checks hfit62
  rw [hovf_add] at hovf_ult hovf_msb
  simp only [serAllocEvs] at hfits
  simp only [arm64_norm] at hx0 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  let wg := x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
  apply SepWPp.of_sepWP_lscl hcl (mid := (blkPl_119).base)
  wp_steps_sync_pool ((blkPl_119).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl0 => ?_
  refine SepWPp.call_wpp (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
    (F := ((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗ ((sp0 - 144#64) ↦₆₄ w144) ∗
          ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗ A.pool lim st _ ∗
          memRegion (sp0 - 368#64 - 4096#64) 4080 ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
    henc (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      rw [stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64),
          stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
      dsimp only [withLsCl, preKeyMsgEncodedLenSpec, withVmPreserved]
      rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcl0, ?_⟩
      simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.preKeyMsgEncodedLenSpec,
        sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => by
      dsimp only [withLsCl] at hm; exact not_satisfies_false_sepConj hm) ?_
  intro sf1 hpc1 hrun1 hsp1
    ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1
  simp only [wp_norm, arm64_norm, *] at h26_1 h27_1 h28_1 hfp_1 hvregs_1
  dsimp only [withLsCl, preKeyMsgEncodedLenSpec, withVmPreserved]
  simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.preKeyMsgEncodedLenSpec,
    sepConj_assoc]
  refine SepWPp.pure_elim fun hcl1 => ?_
  refine SepWPp.pure_elim fun hvm1 => ?_
  refine SepWPp.pure_elim fun ⟨hx0_1, htr1⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx0_1 htr1
  refine SepWPp.transport_budgetPool hvm1 (hnext := ?_)
  apply SepWPp.of_sepWP_lscl hcl1 (mid := lsρ lsRustNoAllocShimSym)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun hcl1' => ?_
  refine SepWPp.call_wpp (x := ())
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A.repAlloc wg (sp0 - 272#64) x.protoMsg ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
          A.pool lim st _ ∗ stackAt (sp0 - 368#64) preKeyMsgEncodedLenStack ∗
          memRegion (sp0 - 368#64 - 4096#64) 4080 ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
    h_shim_cl (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      dsimp only [withLsCl]
      rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcl1', ?_⟩
      simp only [noAllocShimBudgetSpec, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => by
      dsimp only [withLsCl] at hm; exact not_satisfies_false_sepConj hm) ?_
  intro sf2 hpc2 hrun2 hsp2
    ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2
  simp only [wp_norm, arm64_norm, *] at h26_2 h27_2 h28_2 hfp_2 hvregs_2
  dsimp only [withLsCl]
  simp only [noAllocShimBudgetSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hcl2 => ?_
  refine SepWPp.pure_elim fun ⟨htr2, hvm2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2
  refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  apply SepWPp.of_sepWP_lscl hcl2 (mid := lsρ lsRustAllocSym)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun hcl2' => ?_
  refine SepWPp.call_wpp (x := (x.protoMsg.encode.length + 1, 1, st))
    (F := ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          wirePreKeySignalMessageAt A.repAlloc wg (sp0 - 272#64) x.protoMsg ∗
          ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    h_alloc_cl (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
    (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      dsimp only [withLsCl, rustCliAllocNoOomSpec]
      rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcl2', ?_⟩
      simp only [sepConj_assoc]
      rw [satisfies_pure_sepConj]
      refine ⟨⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], hlay, hfits,
        by simp (config := { decide := true }) only [wp_norm, arm64_norm, *]⟩, ?_⟩
      simp only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
      simp only [sepConj_assoc, arm64_norm]
      exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => by
      dsimp only [withLsCl] at hm; exact not_satisfies_false_sepConj hm) ?_
  intro sf3 hpc3 hrun3 hsp3
    ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3, hvregs_3⟩
  simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3
  simp only [wp_norm, arm64_norm, *] at h26_3 h27_3 h28_3 hfp_3 hvregs_3
  dsimp only [withLsCl]
  simp only [rustCliAllocNoOomSpec, AllocCallPreserved, Bool.false_eq_true, ↓reduceIte,
    sepConj_assoc]
  refine SepWPp.pure_elim fun hcl3 => ?_
  refine SepWPp.pure_elim fun ⟨⟨_, _, htr3, _⟩, hoom, _⟩ => ?_
  have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  simp only [wp_norm, arm64_norm] at htr3 hoom hoom_beq
  rw [memRegion_split' (b := sf3.readReg64 (Reg.gpr 0#5))
        (b' := sf3.readReg64 (Reg.gpr 0#5) + 1#64)
        (n := 1) (k := x.protoMsg.encode.length) (by omega) rfl (by omega),
      ProofLib.memRegion_one (sf3.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun _b0 => ?_
  apply SepWPp.of_sepWP_lscl hcl3 (mid := (blkPl_119).base)
  wp_steps_sync_pool ((blkPl_119).base)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; rfl)
    (by simp only [wp_norm, arm64_norm, *]) fun hcl3' => ?_
  refine SepWPp.call_wpp (x := ⟨sp0 - 272#64, wg, x.protoMsg⟩)
    (F := (sf3.readReg64 (Reg.gpr 0#5) ↦₈ versionByte x.ver) ∗ ((sp0 - 128#64) ↦₆₄ 1#64) ∗
          ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 (x.protoMsg.encode.length + 1)) ∗
          ((sp0 - 136#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          A.live (sf3.readReg64 (Reg.gpr 0#5)) (x.protoMsg.encode.length + 1) 1 ∗
          memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) x.protoMsg.encode.length ∗
          A.pool lim (M.stepEvents (serAllocEvs x) st) _ ∗
          ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ memRegion (sp0 - 368#64 - 4096#64) 4080 ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    henc (by simp only [wp_norm, arm64_norm, *]; rfl) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align])
    (by simp only [arm64_norm]; rfl)
    (fun R' hm => by
      dsimp only [withLsCl, preKeyMsgEncodedLenSpec, withVmPreserved]
      rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl _⌝, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcl3', ?_⟩
      simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.preKeyMsgEncodedLenSpec,
        serAllocEvs, sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      rw [stackAt_allocHook_split_encodedLen (sp0 - 368#64)] at hm
      simp only [sepConj_assoc, arm64_norm] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus))
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => by
      dsimp only [withLsCl] at hm; exact not_satisfies_false_sepConj hm) ?_
  intro sf4 hpc4 hrun4 hsp4
    ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4, hvregs_4⟩
  simp only [wp_norm, arm64_norm, *] at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4
  simp only [wp_norm, arm64_norm, *] at h26_4 h27_4 h28_4 hfp_4 hvregs_4
  dsimp only [withLsCl, preKeyMsgEncodedLenSpec, withVmPreserved]
  simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.preKeyMsgEncodedLenSpec,
    sepConj_assoc]
  refine SepWPp.pure_elim fun _hcl4 => ?_
  refine SepWPp.pure_elim fun hvm4 => ?_
  refine SepWPp.pure_elim fun ⟨hx0_4, htr4⟩ => ?_
  simp only [wp_norm, arm64_norm] at hx0_4 htr4
  refine SepWPp.transport_budgetPool hvm4 (hnext := ?_)
  wp_steps_sync_pool ((blkPl_41).base + 604#64)
  refine SepWPp.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · simp only [State.spAligned, wp_norm, arm64_norm, *]
  · refine Entails.sepExists_right (sf3.readReg64 (Reg.gpr 0#5)) ?_
    have hser := (pack_serPrefix0 A.repAlloc sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.ver
      x.protoMsg.encode.length hfit62 hoom).symm
    simp only [RustCliAllocBudget.repAlloc_live] at hser
    rw [hmod_len, hser, stackAt_preKeyMsgSubStack_to_allocHook (sp0 - 368#64),
        stackAt_allocHook_split_encodedLen (sp0 - 368#64)]
    dsimp only [wg]
    simp only [wp_norm, arm64_norm, hsp3, sepConj_assoc]
    refine entails_focus_left hunpack (by sep_focus) ?_
    simp only [sepConj_assoc]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_alloc_ser_wpp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A.repAlloc H)
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
      w368 w144 w136 w128 : BitVec 64) (ver32 pkId32 : BitVec 32)
    (st : M.σ)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (hver : ver32.setWidth 8 = x.ver) (hfit : x.model.serialized.length < 2 ^ 42)
    (hfits : FitsEvents M lim st (serAllocEvs x))
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 496#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 272#64) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 604#64) s
      (((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
       wirePreKeySignalMessageAt A.repAlloc
         (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
         (sp0 - 272#64) x.protoMsg ∗
       ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ serPtr : BitVec 64,
          ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          memRegion (sp0 - 272#64) 128 ∗
          vecU8At A.repAlloc (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length)
            serPtr [versionByte x.ver] ∗
          optKyberCopyBuf A.repAlloc kyberCopyPtr x.kp ∗
          boxU8Buf A.repAlloc bkSerPtr x.baseKey.serialize ∗
          boxU8Buf A.repAlloc ikSerPtr x.ik.serialize ∗
          boxU8Buf A.repAlloc msgCopyPtr x.msg.serialized ∗
          A.pool lim (M.stepEvents (serAllocEvs x) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_alloc_ser_wpp_placed_of_ok
    (ls_hook_ok_of_mem hshim)
    (preKeyMsg_alloc_placed_ok halloc)
    hEncLen x sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
    w368 w144 w136 w128 ver32 pkId32 st hkyCap hky_len hmsg_len hver hfit hfits
    s hcl hpc hrun hsp hsp_align hx0 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

theorem preKeyMsg_alloc_ser_wpp_placed_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A.repAlloc H)
    (x : PreKeyMsgNewCall) (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
      w368 w144 w136 w128 : BitVec 64) (ver32 pkId32 : BitVec 32)
    (st : M.σ)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63)
    (hver : ver32.setWidth 8 = x.ver) (hfit : x.model.serialized.length < 2 ^ 42)
    (hfits : FitsEvents M lim st (serAllocEvs x))
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_41).base + 496#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 272#64) (hx19 : s.readReg64 .x19 = kyberCap)
    (hx20 : s.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.spk.zeroExtend 64) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx25 : s.readReg64 .x25 = pkId32.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H) ((blkPl_41).base + 604#64) s
      (((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
       wirePreKeySignalMessageAt A.repAlloc
         (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
         (sp0 - 272#64) x.protoMsg ∗
       ((sp0 - 144#64) ↦₆₄ w144) ∗ ((sp0 - 136#64) ↦₆₄ w136) ∗ ((sp0 - 128#64) ↦₆₄ w128) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x19 = kyberCap ∧
         sm.readReg64 .x20 = (if x.preKeyId.isSome then 1#32 else 0#32).zeroExtend 64 ∧
         sm.readReg64 .x21 = x.spk.zeroExtend 64 ∧ sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧ sm.readReg64 .x25 = pkId32.zeroExtend 64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = bkSerPtr ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ∃∗ serPtr : BitVec 64,
          ((sp0 - 368#64) ↦₆₄ msgCopyPtr) ∗ ((sp0 - 332#64) ↦₃₂ ver32) ∗
          memRegion (sp0 - 272#64) 128 ∗
          vecU8At A.repAlloc (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length)
            serPtr [versionByte x.ver] ∗
          optKyberCopyBuf A.repAlloc kyberCopyPtr x.kp ∗
          boxU8Buf A.repAlloc bkSerPtr x.baseKey.serialize ∗
          boxU8Buf A.repAlloc ikSerPtr x.ik.serialize ∗
          boxU8Buf A.repAlloc msgCopyPtr x.msg.serialized ∗
          A.pool lim (M.stepEvents (serAllocEvs x) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) :=
  preKeyMsg_alloc_ser_wpp_placed_of_ok
    (subroutine_ok_noAllocShim_of_sessionShimBudget (preKeyMsg_shim_placed_ok hshim))
    (preKeyMsg_alloc_placed_ok halloc)
    hEncLen x sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr
    w368 w144 w136 w128 ver32 pkId32 st hkyCap hky_len hmsg_len hver hfit hfits
    s hcl hpc hrun hsp hsp_align hx0 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## Prologue Composition (`+0x000..+0x25c`) -/

theorem PreKeyMsgSegExit_placed.of_sepWPp_seamA [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PreKeyMsgNewCall} {st : M.σ} {R P : SepProp} {s0 : State}
    (hm : s0.mem ⊨ P ∗ R)
    (hwpp : SepWPp (lsProg_41 H) ((blkPl_41).base + 604#64) s0 P
      (fun sf P_f => ∀ R', sf.mem ⊨ P_f ∗ R' → ∃ g, SeamA_placed A lim x st g R' s0 sf)
      (fun _ _ => False)) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s0
      (fun s => ∃ g, SeamA_placed A lim x st g R s0 s) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_hpc, _hrun, P_f, hmf, hq⟩ | ⟨_, _, _, hp⟩ | ⟨_, hoom⟩⟩ := hwpp R hm hL
  · exact ⟨sf, hsteps, Or.inl (hq R hmf)⟩
  · exact hp.elim
  · dsimp only at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem prologue_placed_ok_of_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_shim : subroutine_ok (lsProg_41 H) (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec)
    (h_alloc : subroutine_ok (lsProg_41 H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomSpec M A lim false))
    (h_memcpy : subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) framelessMemcpyBudgetSpec)
    (h_pkSer : subroutine_ok (lsProg_41 H) (blkPl_205).base
      (withLsCl lsmpl (publicKeySerializeSpec M A lim)))
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A.repAlloc H)
    (x : PreKeyMsgNewCall) (st : M.σ) (R : SepProp) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hs : s0.status = .Running)
    (hpc : s0.pc = preKeyMsgNewEntry_placed)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (preKeyMsgNewSpec M A lim).pre (x, st) s0 ∗ R) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s0
      (fun s => ∃ g, SeamA_placed A lim x st g R s0 s) := by
  dsimp only [preKeyMsgNewSpec,
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.preKeyMsgNewSpec] at hpre
  simp only [optKyberAt_atState_eq, signalMessageAt_atState_eq,
    RustCliAllocBudget.atState_pool, sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfitsEnv, hlr0⟩, hpre⟩
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfit⟩, hpre⟩
  have hfitsFull : FitsEvents M lim st
      (preKeyMsgNewRawEvents x.kp x.msg.serialized.length x.model.serialized.length) :=
    hfitsEnv _ rfl
  have hfitsPrologue : FitsEvents M lim st
      (preKeyMsgNewRawPrologueEvents x.kp x.msg.serialized.length x.model.serialized.length) := by
    dsimp only [preKeyMsgNewRawEvents] at hfitsFull
    simp only [List.append_assoc] at hfitsFull
    exact ((fitsEvents_append M lim _ _ st).mp hfitsFull).1
  rw [prologueEvents_eq x] at hfitsPrologue
  have ⟨hfits123, hfits4⟩ := (fitsEvents_append M lim _ (serAllocEvs x) st).mp hfitsPrologue
  have ⟨hfits12, hfits3⟩ := (fitsEvents_append M lim _ (msgCloneEvs x.msg) st).mp hfits123
  have ⟨hfits1, hfits2⟩ := (fitsEvents_append M lim (kyberCloneEvs x.kp) pkSerialize2Evs st).mp hfits12
  simp only [M.stepEvents_append] at hfits3 hfits4
  have hky_len := optKyberAt_length_lt hpre
  have hky_max : ∀ k, x.kp = some k → k.ciphertext.length + 1 ≤ 2 ^ 63 := fun k hk => by
    have := hky_len k hk; omega
  rw [optKyberAt_eq_word0_and_rest A.repAlloc x.kyA x.kyPtr x.kp,
      stackAt_preKeyMsgNewStack_ready s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨w368, w360, w352, w344, w332, w328, w324, w320, w312, w304,
    w296, w292, w288, w280, w144, w136, w128, hpre⟩
  simp only [← sepConj_assoc] at hpre
  let ver32 : BitVec 32 := (s0.readReg64 .x0).setWidth 32
  let pkId32 : BitVec 32 := (s0.readReg64 .x3).setWidth 32
  have hver : ver32.setWidth 8 = x.ver := by dsimp [ver32]; rw [setWidth8_setWidth32, hx0]
  have hpk : ∀ v, x.preKeyId = some v → pkId32 = v := hx3
  refine PreKeyMsgSegExit_placed.of_sepWPp_seamA hpre ?_
  refine preKeyMsg_seq_wp_vm_lscl hcl
    (preKeyMsg_entry_to_04c_wp_placed x s0.sp w304 w288 w280 w292 s0 hpc hs rfl hsp
      hx1 hx2 hx4 hx5 hx6 hx7 hx8) (by sep_focus) ?_
  intro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, hsp1_align, s1_x6, s1_x20, s1_x21, s1_x22, s1_x23,
    s1_x25, s1_x26, s1_x29, htr1, hvregs1⟩
  have hpool1 : A.pool lim st s0 = A.pool lim st s1 := (A.pool_of_vmPreserved hvm1).symm
  refine preKeyMsg_seq_wpp_lscl hcl1
    (preKeyMsg_kyber_clone_wpp_placed_of_ok h_shim h_alloc h_memcpy x s0.sp w320 w312 w324 w296
      ver32 pkId32 st s1 hky_max hfits1
      hpc1 hrun1 hsp1 hsp1_align s1_x6 s1_x20 s1_x21 s1_x22 s1_x23 s1_x25 s1_x26 s1_x29)
    (by rw [hpool1]; sep_focus) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hsp2_align, s2_x6, s2_x19, s2_x21, s2_x22, s2_x23,
    s2_x25, s2_x26, s2_x29, htr2, hvregs2⟩
  have htr20 : s2.trace = s0.trace := htr2.trans htr1
  have hvregs20 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans hvregs1
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun kyberCopyPtr => SepWPp.exists_elim fun w312' => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun _hky_ptr_ne => ?_
  refine preKeyMsg_seq_wpp_lscl hcl2
    (preKeyMsg_pk_serialize_wpp_placed_of_ok h_pkSer x s0.sp (s2.readReg64 .x19) ver32 pkId32
      (M.stepEvents (kyberCloneEvs x.kp) st) s2 hfits2
      hcl2 hpc2 hrun2 hsp2 hsp2_align s2_x6 rfl s2_x21 s2_x22 s2_x23 s2_x25 s2_x26 s2_x29)
    (by sep_focus) ?_
  intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hsp3_align, s3_x1, s3_x19, s3_x20, s3_x21, s3_x22,
    s3_x23, s3_x24, s3_x25, s3_x26, s3_x29, htr3, hvregs3⟩
  have htr30 : s3.trace = s0.trace := htr3.trans htr20
  have hvregs30 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs20
  have s3_x19' : s3.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s3_x19.trans s2_x19
  refine preKeyMsg_seq_wpp_lscl hcl3
    (preKeyMsg_msg_clone_wpp_placed_of_ok h_shim h_alloc h_memcpy x s0.sp (s3.readReg64 .x19)
      (s3.readReg64 .x28) (s3.readReg64 .x0) w360 w344 w312' w332 w328 ver32 pkId32
      (M.stepEvents pkSerialize2Evs (M.stepEvents (kyberCloneEvs x.kp) st)) s3 hfits3
      hpc3 hrun3 hsp3 hsp3_align rfl s3_x1 rfl s3_x20 s3_x21 s3_x22 s3_x23 s3_x24 s3_x25
      s3_x26 rfl s3_x29)
    (by sep_focus) ?_
  intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hsp4_align, s4_x0, s4_x8, s4_x19, s4_x22, s4_x23,
    s4_x24, s4_x25, s4_x27, s4_x28, s4_x29, htr4, hvregs4, _hmsg9, hmsg_lt40, _hmsg_ptr_ne⟩
  have htr40 : s4.trace = s0.trace := htr4.trans htr30
  have hvregs40 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hvregs4.trans hvregs30
  have s4_x19' : s4.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    s4_x19.trans s3_x19'
  have hmsg_len63 : x.msg.serialized.length < 2 ^ 63 := by omega
  have hkyId : ∀ k, x.kp = some k → kyberIdOf x.kp w324 = k.preKeyId :=
    fun k hk => by simp [kyberIdOf, hk]
  refine preKeyMsg_convert_344 s0.sp 33#64 (by sep_focus) fun w344_32 => ?_
  refine preKeyMsg_seq_wp_vm_lscl hcl4
    (preKeyMsg_store_wire_wp_placed (A := A.repAlloc) x s0.sp (s4.readReg64 .x19) kyberCopyPtr
      (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26) w352
      w344_32 pkId32 (kyberIdOf x.kp w324) s4_x19' hpk hkyId hmsg_len63 s4
      hpc4 hrun4 hsp4 hsp4_align s4_x0 s4_x8 rfl s4_x22 s4_x23 s4_x24 s4_x25 rfl s4_x27
      s4_x28 s4_x29) (by sep_focus) ?_
  intro s5 hpc5 hrun5 hcl5 hvm5 ⟨hsp5, hsp5_align, s5_x0, s5_x19, s5_x20, s5_x21, s5_x22,
    _s5_x23, s5_x24, s5_x25, s5_x26, s5_x27, s5_x28, s5_x29, htr5, hvregs5⟩
  have htr50 : s5.trace = s0.trace := htr5.trans htr40
  have hvregs50 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := hvregs5.trans hvregs40
  let st4 := M.stepEvents (msgCloneEvs x.msg)
    (M.stepEvents pkSerialize2Evs (M.stepEvents (kyberCloneEvs x.kp) st))
  have hpool5 : A.pool lim st4 s4 = A.pool lim st4 s5 := (A.pool_of_vmPreserved hvm5).symm
  refine preKeyMsg_seq_wpp_lscl hcl5
    (preKeyMsg_alloc_ser_wpp_placed_of_ok h_shim h_alloc hEncLen x s0.sp (s4.readReg64 .x19)
      kyberCopyPtr (s3.readReg64 .x28) (s3.readReg64 .x0) (s4.readReg64 .x26)
      w368 w144 w136 w128 ver32 pkId32 st4 s4_x19' hky_len hmsg_len63 hver hfit hfits4 s5 hcl5
      hpc5 hrun5 hsp5 hsp5_align s5_x0 s5_x19 s5_x20 s5_x21 s5_x22 s5_x24 s5_x25
      s5_x26 s5_x27 s5_x28 s5_x29)
    (by dsimp only [st4]; rw [hpool5]; sep_focus) ?_
  intro sf hpcf hrunf hclf ⟨hspf, hspf_align, sf_x19, sf_x20, sf_x21, sf_x22, sf_x24,
    sf_x25, sf_x27, sf_x28, sf_x29, htrf, hvregsf⟩
  have htrf0 : sf.trace = s0.trace := htrf.trans htr50
  have hvregsf0 : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregsf.trans hvregs50
  have sf_x19' : sf.readReg64 .x19 =
      match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length :=
    sf_x19.trans s4_x19'
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun serPtr => ?_
  apply SepWPp.done hpcf hrunf
  intro R' hmf
  let g : PreKeyMsgFrameGhost :=
    { serPtr := serPtr, kyberCopyPtr := kyberCopyPtr, bkSerPtr := s3.readReg64 .x28,
      ikSerPtr := s3.readReg64 .x0, msgCopyPtr := s4.readReg64 .x26, ver32 := ver32,
      preKeyVal32 := pkId32, kyberId32 := kyberIdOf x.kp w324 }
  let evs := preKeyMsgNewRawPrologueEvents x.kp x.msg.serialized.length x.model.serialized.length
  have hstep_eq : M.stepEvents (serAllocEvs x) st4 = M.stepEvents evs st := by
    dsimp only [evs, st4]
    rw [prologueEvents_eq x]
    simp only [M.stepEvents_append]
  refine ⟨g, evs, rfl, hlr0, hpcf, hclf,
    ⟨hfit, hver, hpk, fun k hk => by simp [g, kyberIdOf, hk]⟩, ?_, ?_⟩
  · refine ⟨hrunf, hspf, hsp, hspf_align, htrf0, sf_x29, sf_x19', ?_, ?_,
      sf_x22, sf_x24, ?_, sf_x27, sf_x28, hvregsf0⟩
    · rw [sf_x20, setWidth32_zeroExtend64]
    · rw [sf_x21, setWidth32_zeroExtend64]
    · rw [sf_x25, setWidth32_zeroExtend64]
  · rw [preKeyMsgFrameSlotsAt_one_eq_vec]
    rw [hstep_eq] at hmf
    simp (disch := decide) only [preKeyMsgFrameSlotsAt, preKeyMsgHeapAt,
      optKyberAt_atState_eq, signalMessageAt_atState_eq, vecU8At_atState_eq,
      optKyberCopyBuf_atState_eq, boxU8Buf_atState_eq, RustCliAllocBudget.atState_pool,
      g, bv_sub_add_lit, Nat.reduceSub, sepConj_assoc] at hmf ⊢
    exact satisfies_of_sep_focus hmf (by sep_focus)

theorem prologue_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A.repAlloc H)
    (x : PreKeyMsgNewCall) (st : M.σ) (R : SepProp) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hs : s0.status = .Running)
    (hpc : s0.pc = preKeyMsgNewEntry_placed)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (preKeyMsgNewSpec M A lim).pre (x, st) s0 ∗ R) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s0
      (fun s => ∃ g, SeamA_placed A lim x st g R s0 s) :=
  prologue_placed_ok_of_ok
    (ls_hook_ok_of_mem hshim)
    (preKeyMsg_alloc_placed_ok halloc)
    (ls_hook_ok_of_mem hmemcpy)
    (preKeyMsg_publicKeySerialize_placed_ok_noAllocShim hshim halloc)
    hEncLen x st R s0 hcl hs hpc hsp hpre

theorem prologue_placed_ok_sessionHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A.repAlloc H)
    (x : PreKeyMsgNewCall) (st : M.σ) (R : SepProp) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hs : s0.status = .Running)
    (hpc : s0.pc = preKeyMsgNewEntry_placed)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨ (preKeyMsgNewSpec M A lim).pre (x, st) s0 ∗ R) :
    PreKeyMsgSegExit_placed A lim H x st R s0 s0
      (fun s => ∃ g, SeamA_placed A lim x st g R s0 s) :=
  prologue_placed_ok_of_ok
    (subroutine_ok_noAllocShim_of_sessionShimBudget (preKeyMsg_shim_placed_ok hshim))
    (preKeyMsg_alloc_placed_ok halloc)
    (subroutine_ok_framelessMemcpy_of_sessionMemcpyRegionBudget (preKeyMsg_memcpy_placed_ok hmemcpy))
    (preKeyMsg_publicKeySerialize_placed_ok hshim halloc)
    hEncLen x st R s0 hcl hs hpc hsp hpre

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueBudget
