/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.New
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123Budget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456Budget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` (Block `63`)

Composes the budget-threaded prologue, protobuf field encoders, and MAC/packing phase into
relocatable `[LibsignalPlacement]` `subroutine_ok` theorems for `signalMessageNewSpecWithStack`,
`signalMessageNewSpec`, and `signalMessageNewSpecX` under `withLsCodeLoaded` and `withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto currentVersion versionByte)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl lsρ
   lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.RustHeap (allocHookStack vecU8At)
open CryptoVerification.LibsignalProtoCodec (encode)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SignalMessageGhost UuidParser noneCap okTagVec protocolAddressAt signalMessageAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (encodeVarintStack encodeVarintStackX encodedLenStack wireSignalMessageAt)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_63 blkPl_63 LibsignalCodeRoLoaded SignalMessageNewGhost TraceVRegsEq withLsCodeRoLoaded
   add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap add_one_eq_zero_iff_noneCap
   append64_extract_hi append64_extract_lo boxU8Buf bv_add_8_sub_self
   computeMacStack computeMacStackX encLen_overflow_checks
   encode_protoMsg_length_bounds entails_newFrameRest extHookStack
   memRegion_16_eq_cells2 memRegion_split_one model_serialized_eq model_serialized_length
   model_serialized_ne_nil
   newFrameRest newFrameRest_entails_stackAt newFrameRest_entails_stackAtX
   newSavedRegs newUnusedPad noAllocShimSpec optAddrAt optAddrBuf_extract_cap
   optPqBuf optPqBuf_extract_pin optSerializeAddressesAt optSerializeAddressesAt_unpack
   pack_serPrefix0 publicKey_serialize_length serPrefix6_length
   serializeAddressesStack serializeAddressesStackX
   signalMessageNewStack signalMessageNewStackX signalMessageNew_computeMac_length
   signalMessageNew_of_sepWP_placed signalMessageNew_vecU8Buf
   sp_add_32_add_8 sp_sub_96_add_112 sp_sub_96_add_120 sp_sub_96_add_128 sp_sub_96_add_96
   sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
   stackAt_signalMessageNewStackX_ready stackAt_signalMessageNewStack_ready
   three_words_entails_cells3 totCap_eq_serLen_add_8 vecU8At_eq_of_pos vecU8Buf_eq_boxU8Buf
   wireSignalMessageAt_unpack_for_phase3 zeroExtend32_truncate8_eq)
open CryptoVerification.LibsignalTripleRatchet.NewMacAndBoxesCallees
  (entails_of_sep_focus pull_pure_mid9 satisfies_of_sep_focus)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (publicKeySerializeSpec publicKeySerializeSpecWithStack publicKeySerializeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
  (ComputeMacEnv computeMacEvents computeMacSpec computeMacSpecWithStack computeMacSpecX
   fitsEnv_computeMac_iff serializeAddressesSpec serializeAddressesSpecWithStack
   serializeAddressesSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintSpec encodeVarintSpecX encodedLenSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv signalMessageNewEvents signalMessageNewSpec
   signalMessageNewSpecWithStack signalMessageNewSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
  (call_noPanic_placed fitsEvents_prologue_and_post_of_signalMessageNew
   fitsEvents_segments_of_prologue newAddrAndRkEvents newPostPrologueEvents newPrologueEvents
   new_addr_and_rk_wpp_placed_at new_prologue_wp_placed signalMessageNewEvents_eq_prologue_append
   stackAt_split_ge)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
  (new_ct_copy_wpp_placed_at new_pq_copy_wpp_placed_at)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (framelessMemcpyBudgetSpec new_allocNoOom_placed_ok new_shim_placed_ok noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123BudgetAux
  (encodeVarintSpecWithStack encodeVarintSpecX_eq_withStack encodeVarintSpec_eq_withStack
   encode_protoMsg_length_bounds_parse encodedLenBudgetSpec_pre_eq new_store_wire_wp_placed
   wireLengthsFit_protoMsg_parse)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123Budget
  (new_encode_tag1_wpp_placed_at new_encode_tag2_wpp_placed_at new_encode_tag3_wpp_placed_at)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags456Budget
  (new_encode_tag4_wpp_placed_at new_encode_tag56_wpp_placed_at)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudget
  (fitsEvents_segments_of_phase3 newPhase3Events newPostPrologueEvents_eq_serAlloc_append_phase3
   new_addr_into_boxed_wp_placed new_ct_clone_wpp_placed_at new_dealloc_pq_and_epilogue_wpp_placed_at
   new_dealloc_rk_and_ct_wpp_placed_at new_pq_clone_wpp_placed_at new_sret_stores_wp_placed)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  sp_sub_96_add_96 sp_sub_96_add_112 sp_sub_96_add_120 sp_sub_96_add_128 sp_add_32_add_8
  sp_sub_96_sub_56 sp_sub_96_sub_64 sp_sub_96_sub_72 sp_sub_96_sub_80
  add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap
  bv_add_8_sub_self append64_extract_lo append64_extract_hi zeroExtend32_truncate8_eq

/-! ## `Inv`-preserving call, sequencing, and `subroutine_ok` helpers -/

/-- Add a `KeepsFrozen`-stable memory invariant `Inv` to `spec`'s precondition. -/
def withMemInv {α : Type} (Inv : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => spec.pre x s ∗ ⌜Inv s.mem⌝ }

private theorem bind_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : let sc := s; SepWPp prog ret sc P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  h

private theorem of_sepWP_placed_gen {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      Inv sm.mem →
      SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨_hpcm, _hrunm, _P_m, hmm, hkont⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hkont (hInv_kf hinv hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem call_noPanic_placed_gen {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hinv : Inv s.mem)
    (hcall : subroutine_ok prog entry (withMemInv Inv spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hnext : ∀ sf : State, Inv sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
        intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (withMemInv Inv spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withMemInv]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, hpre R hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  have hinv_m : Inv sm.mem := hInv_kf hinv hsteps.keepsFrozen
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withMemInv] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hinv_m hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withMemInv] at hpost
    exact (hpanic sm (F ∗ R) hpan hpost).elim
  · dsimp only [withMemInv] at hpost
    exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withMemInv] at hpost
    exact (hoom sm (F ∗ R) hoom_s hpost).elim

private theorem seq_noPanic_inv {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, Inv sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm (hInv_kf hinv hsteps.keepsFrozen) hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hfoom).elim

private theorem seq_wp_inv {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, Inv sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  seq_noPanic_inv hInv_kf hinv (SepWPp.of_sepWP_ret h1) hfocus h2

private theorem subroutine_ok_of_sepWPp_noPanic {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {Ppost : α → State → State → SepProp}
    (hpost : ∀ x s0 sf, sf.trace = s0.trace → (Ppost x s0 sf ⊢ spec.post x s0 sf))
    (h : ∀ (x : α) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.spAligned = true →
      SepWPp prog (s0.readReg64 Reg.lr) s0 (spec.pre x s0)
        (fun sf P_f =>
          (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
          (P_f ⊢ Ppost x s0 sf))
        (fun _ _ => False)) :
    subroutine_ok prog entry spec := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  refine ⟨spec.pre x s0, R, hpre, ?_⟩
  intro R' hm hL
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf, htrf⟩, hent⟩ |
      ⟨_hpanf, _P_f, _hmf, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h x s0 hpc hrun hsp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, fun hmFr => ?_, hspf, hcsf⟩⟩
    exact Satisfies.mono (sepConj_mono_left (Entails.trans hent (hpost x s0 sf htrf))) hmFr
  · exact False.elim hqp
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## `withLsCodeLoaded`-guarded `encoded_len` and `serialized` allocation (`+0x13c → +0x1b8`) -/

private theorem new_alloc_ser_wpp_placed_cl_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle_enc : encodedLenStack ≤ cmStack := by decide)
    (hle_alloc : allocHookStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A.repAlloc)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit_ser : FitsEvents M lim st (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1))
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (_hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A.repAlloc
         (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg parse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          vecU8At A.repAlloc (sp0 - 176#64)
            (BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool lim
            (M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hshim := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
  have halloc := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (new_allocNoOom_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
  clear h_shim h_alloc
  have hfit := wireLengthsFit_protoMsg_parse parse x hct_bound hpq_bound
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds_parse parse x hct_bound hpq_bound
  have ⟨h_adds1, h_cmp9, h_tbz, h_hi, h_add9_eq, h_add9_toNat⟩ :=
    encLen_overflow_checks henc_lo henc_hi
  have h_pos9 : 0 < (encode (x.protoMsg parse)).length + 9 := by omega
  have h_le9 : (encode (x.protoMsg parse)).length + 9 ≤ 9223372036854775807 := by omega
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 108) hcl
  wp_steps_sync_pool (lsmpl.base 108)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl_el1
  refine bind_state ?_
  intro s_el1
  refine call_noPanic_placed
    (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr,
      x.protoMsg parse⟩)
    (F := ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool lim st s_el1 ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack))
    hcl_el1 hEncLen (by simp only [s_el1, wp_norm, arm64_norm])
    (by simp only [s_el1, wp_norm, arm64_norm, hrun])
    (by simp only [s_el1, State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [s_el1, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    dsimp only [s_el1] at hm ⊢
    rw [stackAt_split_ge hle_enc hbnd (sp0 - 416#64)] at hm
    rw [encodedLenBudgetSpec_pre_eq A.repAlloc _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm, hx0]) hfit
          (by simp only [wp_norm, arm64_norm, hsp])]
    simp only [sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hcl1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  dsimp only [s_el1] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [wp_norm, arm64_norm, hsp, hx19, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [encodedLenSpec, wp_norm, arm64_norm, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hvm1, hx0_1, htr1⟩ => ?_
  dsimp only [s_el1] at hvm1 htr1 ⊢
  rw [← A.pool_transport lim st _ sf1 hvm1]
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp, sepConj_assoc]
  have hfold_el1 :
      stackAt (sp0 - 416#64) encodedLenStack ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack) =
      stackAt (sp0 - 416#64) cmStack :=
    (stackAt_split_ge hle_enc hbnd (sp0 - 416#64)).symm
  conv =>
    arg 4
    rw [show wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        stackAt (sp0 - 416#64) encodedLenStack ∗
        (sp0 - 384#64) ↦₃₂ w384 ∗ (sp0 - 380#64) ↦₃₂ w380 ∗ (sp0 - 332#64) ↦₃₂ verW32 ∗
        (sp0 - 176#64) ↦₆₄ w176 ∗ (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 ∗
        A.pool lim st sf1 ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack) =
        (stackAt (sp0 - 416#64) encodedLenStack ∗
          memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack)) ∗
        wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        (sp0 - 384#64) ↦₃₂ w384 ∗ (sp0 - 380#64) ↦₃₂ w380 ∗ (sp0 - 332#64) ↦₃₂ verW32 ∗
        (sp0 - 176#64) ↦₆₄ w176 ∗ (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 ∗
        A.pool lim st sf1 by sep_ac_rfl, hfold_el1]
  simp only [wp_norm, arm64_norm] at htr1
  apply signalMessageNew_of_sepWP_placed (mid := lsρ lsRustNoAllocShimSym) hcl1
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun1])
  intro hcl_shim
  refine bind_state ?_
  intro s_shim
  refine call_noPanic_placed (x := ())
    (F := wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 176#64) ↦₆₄ w176) ∗
          ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool lim st s_shim ∗ stackAt (sp0 - 416#64) cmStack)
    hcl_shim hshim (by simp only [s_shim, wp_norm, arm64_norm])
    (by simp only [s_shim, wp_norm, arm64_norm, hrun1])
    (by simp only [s_shim, State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [s_shim, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    dsimp only [s_shim] at hm ⊢
    simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc,
      emp_sepConj, State.mem_setMem] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hcl2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  dsimp only [s_shim] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [wp_norm, arm64_norm, hsp1,
      h19_1, h21_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun hvm2 => SepWPp.pure_elim fun htr2 => ?_
  dsimp only [s_shim] at hvm2 htr2 ⊢
  rw [← A.pool_transport lim st _ sf2 hvm2]
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply signalMessageNew_of_sepWP_placed (mid := lsρ lsRustAllocSym) hcl2
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2])
  intro hcl_al
  refine call_noPanic_placed
    (x := ((encode (x.protoMsg parse)).length + 9, 1, st))
    (F := wireSignalMessageAt A.repAlloc
            (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg parse) ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 176#64) ↦₆₄ w176) ∗
          ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack))
    hcl_al halloc (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    have hlay : RustLayoutOk ((encode (x.protoMsg parse)).length + 9) 1 :=
      ⟨⟨h_pos9, ⟨0, rfl⟩, by omega⟩, by decide⟩
    rw [stackAt_split_ge hle_alloc hbnd (sp0 - 416#64)] at hm
    dsimp only [rustCliAllocNoOomSpec]
    simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm, hsp2, h_add9_toNat, hlay, hfit_ser,
      and_self, pure_true, emp_sepConj] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf3 hcl3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, hsp2, h19_2, h20_2, h21_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2]
    at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  dsimp only [rustCliAllocNoOomSpec]
  simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hpres3, hoom, _halign_ptr⟩ => ?_
  have htr3 : sf3.trace = s.trace := by
    have ht := hpres3.2.1
    simp only [wp_norm, arm64_norm, htr2] at ht
    exact ht
  have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  simp only [arm64_norm] at hoom hoom_beq
  let st' := M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st
  have hfold_alloc :
      stackAt (sp0 - 416#64) allocHookStack ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack) =
      stackAt (sp0 - 416#64) cmStack :=
    (stackAt_split_ge hle_alloc hbnd (sp0 - 416#64)).symm
  conv =>
    arg 4
    simp only [wp_norm, arm64_norm, hsp2, sepConj_assoc]
    rw [show A.pool lim (M.stepEvents (rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1) st) sf3 ∗
        stackAt (sp0 - 416#64) allocHookStack ∗
        A.live (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) 1 ∗
        memRegion (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) ∗
        wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        (sp0 - 384#64) ↦₃₂ x.counter ∗ (sp0 - 380#64) ↦₃₂ x.previousCounter ∗
        (sp0 - 332#64) ↦₃₂ verW32 ∗ (sp0 - 176#64) ↦₆₄ w176 ∗
        (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 ∗
        memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack) =
        memRegion (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) ∗
        (stackAt (sp0 - 416#64) allocHookStack ∗
          memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - allocHookStack)) ∗
        A.live (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) 1 ∗
        A.pool lim st' sf3 ∗
        wireSignalMessageAt A.repAlloc (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
          (sp0 - 288#64) (x.protoMsg parse) ∗
        (sp0 - 384#64) ↦₃₂ x.counter ∗ (sp0 - 380#64) ↦₃₂ x.previousCounter ∗
        (sp0 - 332#64) ↦₃₂ verW32 ∗ (sp0 - 176#64) ↦₆₄ w176 ∗
        (sp0 - 168#64) ↦₆₄ w168 ∗ (sp0 - 160#64) ↦₆₄ w160 by sep_ac_rfl, hfold_alloc]
  rw [memRegion_split_one (sf3.readReg64 (Reg.gpr 0#5))
        ((encode (x.protoMsg parse)).length + 9) (by omega) (by omega)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun _b0 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 108) hcl3
  wp_steps_sync_pool (lsmpl.base 108)
  apply SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun3])
  intro hcl_el2
  refine bind_state ?_
  intro s_el2
  refine call_noPanic_placed
    (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr,
      x.protoMsg parse⟩)
    (F := A.live (sf3.readReg64 (Reg.gpr 0#5)) ((encode (x.protoMsg parse)).length + 9) 1 ∗
          ((sf3.readReg64 (Reg.gpr 0#5)) ↦₈ versionByte x.messageVersion) ∗
          memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) ((encode (x.protoMsg parse)).length + 8) ∗
          A.pool lim st' s_el2 ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((encode (x.protoMsg parse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((sp0 - 160#64) ↦₆₄ 1#64) ∗
          memRegion ((sp0 - 416#64) - BitVec.ofNat 64 cmStack) (cmStack - encodedLenStack))
    hcl_el2 hEncLen (by simp only [s_el2, wp_norm, arm64_norm])
    (by simp only [s_el2, wp_norm, arm64_norm, hrun3])
    (by simp only [s_el2, State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align])
    (by simp only [s_el2, wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    have hv : BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (verW32 <<< 4)) =
        versionByte x.messageVersion := by
      rw [← hver]; unfold versionByte currentVersion; bv_kernel
    dsimp only [s_el2] at hm ⊢
    rw [stackAt_split_ge hle_enc hbnd (sp0 - 416#64), hv] at hm
    rw [encodedLenBudgetSpec_pre_eq A.repAlloc _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm]) hfit
          (by simp only [wp_norm, arm64_norm, hsp3])]
    simp only [sepConj_assoc] at hm ⊢
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf4 _hcl4 hpc4 hrun4 hsp4 ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
  dsimp only [s_el2] at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
  simp only [wp_norm, arm64_norm, hsp3, h19_3, h20_3, h21_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3]
    at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
  simp only [encodedLenSpec, wp_norm, arm64_norm, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hvm4, hx0_4, htr4⟩ => ?_
  dsimp only [s_el2] at hvm4 htr4 ⊢
  rw [← A.pool_transport lim st' _ sf4 hvm4]
  simp only [wp_norm, arm64_norm, htr3] at htr4
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp3, sepConj_assoc]
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_63).base + 440#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun4]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp4, hsp0_align, h19_4, h20_4, h21_4, h22_4, ne_eq,
      eq_false hoom, not_false_eq_true, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4,
      htr4, and_self]
  · rw [stackAt_split_ge hle_enc hbnd (sp0 - 416#64)]
    unfold SignalMessageNewGhost.serPrefix0
    simp only [wp_norm, arm64_norm, h22_4, st']
    change _ ⊢ _
    rw [← A.repAlloc_live,
        ← pack_serPrefix0 A.repAlloc sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.messageVersion
            (encode (x.protoMsg parse)).length henc_lo henc_hi hoom]
    simp only [sepConj_assoc]
    exact entails_of_sep_focus (by sep_focus)

/-! ## `Inv`-parameterized Phase 3 (`+0x3dc → s0.readReg64 .lr`) -/

private theorem new_compute_mac_and_append_wpp_placed_gen_at [LibsignalPlacement]
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withMemInv Inv (computeMacSpecWithStack M A lim C.F cmStack)))
    (x : SignalMessageNewGhost)
    (sp0 serPtr addrCap : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st computeMacEvents)
    (s : State)
    (hinv : Inv s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1088#64)
      s
      (((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = serPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          cells (sp0 - 176#64) 3 ∗
          memRegion (sp0 - 152#64) 16 ∗
          boxU8Buf A.repAlloc serPtr (x.model C.F uuidTryParse).serialized ∗
          A.pool lim (M.stepEvents computeMacEvents st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have hfit_env : FitsEnv M lim st ComputeMacEnv := fitsEnv_computeMac_iff.mpr hfit
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29
  have hser6_bounds :
      36 ≤ (x.serPrefix6 uuidTryParse).length ∧ (x.serPrefix6 uuidTryParse).length < 2 ^ 35 := by
    have ⟨_, _⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
    have := serPrefix6_length x
    omega
  have htotCap_toNat :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat =
        (x.serPrefix6 uuidTryParse).length + 8 := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hser6_toNat :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length).toNat =
        (x.serPrefix6 uuidTryParse).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrem8 :
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat -
        (x.serPrefix6 uuidTryParse).length = 8 := by omega
  have h176_8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := by bv_lin
  have h176_16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := by bv_lin
  rw [totCap_eq_serLen_add_8 x,
    vecU8At_eq_of_pos A.repAlloc (sp0 - 176#64)
      (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
      serPtr (x.serPrefix6 uuidTryParse) (by omega),
    hrem8, memRegion_eight (serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length),
    h176_8, h176_16]
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun wmac_dst => ?_
  rw [pull_pure_mid9]
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hserPtr_ne⟩ => ?_
  apply of_sepWP_placed_gen hInv_kf (mid := lsmpl.base 60) hinv
  wp_steps_sync_pool (lsmpl.base 60)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hinv0
  refine call_noPanic_placed_gen hInv_kf
    (x := (⟨sp0 - 152#64, x.senderIkA, x.senderIk, x.receiverIkA, x.receiverIk,
      x.macKeyA, x.macKey, serPtr, x.serPrefix6 uuidTryParse⟩, st))
    (F := ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 176#64) ↦₆₄ (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ∗
          (A.repAlloc).live serPtr
            (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ wmac_dst))
    hinv0 hMac (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    simp only [computeMacSpecWithStack, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine ⟨by omega, ?_⟩
    exact satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [computeMacSpecWithStack, okTagVec, bv_sub_add_lit sp0 152 8, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  obtain ⟨macW, hmacW⟩ := exists_unpack64_of_length_8
    (signalMessageNew_computeMac_length C.F x.senderIk x.receiverIk x.macKey
      (x.serPrefix6 uuidTryParse))
  rw [hmacW, ← pointsTo64_eq_pointsToBytes (sp0 - 144#64) macW]
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool ((blkPl_63).base + 1088#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [model_serialized_length, totCap_eq_serLen_add_8 x]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · simp only [hsp, arm64_norm]
    have hbox :
        A.live serPtr
            (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
          ((serPtr ↦ₛ x.serPrefix6 uuidTryParse) ∗
           ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ macW)) ⊢
        boxU8Buf A.repAlloc serPtr (x.model C.F uuidTryParse).serialized := by
      change (A.repAlloc).live serPtr
          (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64).toNat 1 ∗
        ((serPtr ↦ₛ x.serPrefix6 uuidTryParse) ∗
         ((serPtr + BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length) ↦₆₄ macW)) ⊢ _
      rw [htotCap_toNat, pointsTo64_eq_pointsToBytes, ← hmacW, ← pointsToBytes_append,
        ← model_serialized_eq]
      have hlen_ser := model_serialized_length C.F x
      have hser6_len := serPrefix6_length x
      have hne_nil := model_serialized_ne_nil C.F x
      unfold boxU8Buf
      simp only [hne_nil, ↓reduceIte, hser6_len, hlen_ser]
      refine Entails.pure_right ⟨hserPtr_ne, by omega⟩ (Entails.refl _)
    have hcells3 :=
      three_words_entails_cells3 (sp0 - 176#64)
        (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length + 8#64)
        serPtr
        (BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    rw [h176_8, h176_16] at hcells3
    have hmem16 :
        ((sp0 - 152#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((sp0 - 144#64) ↦₆₄ macW) ⊢
        memRegion (sp0 - 152#64) 16 := by
      rw [memRegion_16_eq_cells2 (sp0 - 152#64), bv_sub_add_lit sp0 152 8]
      exact sepConj_mono (Entails.sepExists_intro 0xFFFFFFFFFFFFFFFE#64)
        (Entails.sepExists_intro macW)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hcells3 (sepConj_mono hmem16 (sepConj_mono_left hbox)))))))))
    exact entails_of_sep_focus (by sep_focus)

private theorem new_phase3_wpp_placed_gen_at [LibsignalPlacement]
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {hookStack : Nat} {sp0 : BitVec 64} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ hookStack := by decide)
    (hbnd : hookStack + 944 ≤ 2 ^ 64 := by decide)
    (hst_entails : ∀ pqCap : BitVec 64,
      stackAt (sp0 - 416#64) (hookStack + 528) ∗
        newFrameRest sp0 ∗
        ((sp0 - 320#64) ↦₆₄ pqCap) ∗
        newSavedRegs sp0 s0 ⊢
      stackAt sp0 ((hookStack + 528) + 416))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withMemInv Inv (computeMacSpecWithStack M A lim C.F (hookStack + 528))))
    (x : SignalMessageNewGhost)
    (serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPhase3Events x))
    (s : State)
    (hinv : Inv s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A.repAlloc (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A.repAlloc rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A.repAlloc ctCopyPtr x.ciphertext ∗
       optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool lim st s ∗
       stackAt (sp0 - 416#64) (hookStack + 528))
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A.repAlloc g x.ret
            (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool lim (M.stepEvents (newPhase3Events x) st) sf ∗
          stackAt s0.sp ((hookStack + 528) + 416)))
      Qp := by
  have hcm_le : allocHookStack ≤ hookStack + 528 := by omega
  have hcm_bnd : hookStack + 528 ≤ 2 ^ 64 := by omega
  obtain ⟨hfit_mac, hfit_ct, hfit_pq, hstep_eq⟩ := fitsEvents_segments_of_phase3 hfit
  refine seq_noPanic_inv hInv_kf hinv
    (new_compute_mac_and_append_wpp_placed_gen_at hInv_kf hMac x sp0 serPtr addrCap hct_bound
      hpq_bound hfit_mac s hinv hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29)
    (by sep_focus) ?_
  intro s1 hinv1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx19_1, hx21_1, hx22_1, hx24_1, hx26_1, hx27_1, hx28_1, hx29_1, htr1⟩
  have htr1' : TraceVRegsEq s1 s0 := htr1.trans htr
  refine seq_noPanic_inv hInv_kf hinv1
    (new_ct_clone_wpp_placed_at hcm_le hcm_bnd h_shim h_alloc h_mc x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      addrCap hct_bound hfit_ct s1 hpc1 hrun1 hsp1 hsp_align1 hx19_1 hx21_1 hx22_1 hx24_1 hx26_1
      hx27_1 hx28_1 hx29_1)
    (by sep_focus) ?_
  intro s2 hinv2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx27_2, hx28_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1'
  refine seq_noPanic_inv hInv_kf hinv2
    (new_pq_clone_wpp_placed_at hcm_le hcm_bnd h_shim h_alloc h_mc x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) addrCap hpq_bound hfit_pq s2 hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx21_2
      hx22_2 hx24_2 rfl hx26_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus) ?_
  intro s3 hinv3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx19_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine seq_wp_inv hInv_kf hinv3
    (new_addr_into_boxed_wp_placed x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) (s3.readReg64 .x23) addrCap haddrCap s3 hpc3 hrun3 hsp3 hsp_align3
      hx19_3 hx21_3 hx22_3 rfl hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)
    (by sep_focus) ?_
  intro s4 hinv4 hpc4 hrun4 ⟨hsp4, hsp_align4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine seq_wp_inv hInv_kf hinv4
    (new_sret_stores_wp_placed x sp0 serPtr (s2.readReg64 .x25) (s3.readReg64 .x23)
      (s4.readReg64 .x0) (s4.readReg64 .x20) verW32 hver hct_bound hpq_bound s4
      hpc4 hrun4 hsp4 hsp_align4 rfl hx19_4 rfl hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4)
    (by sep_focus) ?_
  intro s5 hinv5 hpc5 hrun5 ⟨hsp5, hsp_align5, hx19_5, hx21_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  refine seq_noPanic_inv hInv_kf hinv5
    (new_dealloc_rk_and_ct_wpp_placed_at hcm_le hcm_bnd h_dealloc x sp0 rkPtr ctCopyPtr pqCopyPtr
      hct_bound s5 hpc5 hrun5 hsp5 hsp_align5 hx19_5 hx21_5 hx29_5)
    (by sep_focus) ?_
  intro s6 hinv6 hpc6 hrun6 ⟨hsp6, hsp_align6, hx20_6, _hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  have hfr := entails_newFrameRest sp0 rkPtr ctCopyPtr pqCopyPtr
    x.counter x.previousCounter verW32
    x.ciphertextA x.senderRatchetKeyA x.senderIkA x.receiverIkA x.macKeyA x.pqRatchetA
  refine SepWPp.fold hfr (by sep_focus) ?_
  refine seq_noPanic_inv hInv_kf hinv6
    (new_dealloc_pq_and_epilogue_wpp_placed_at hle hbnd hst_entails h_dealloc x pqCap pqCopyPtr
      hpq_bound s6 hpc6 hrun6 hsp6 hsp0 hsp0_align hsp_align6 hx20_6 htr6' hlr_ls)
    (by sep_focus) ?_
  intro sf _ hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  rw [hstep_eq]
  exact entails_of_sep_focus (by sep_focus)

/-! ## Relocatable `[LibsignalPlacement]` `<SignalMessage>::new` theorems -/

set_option maxHeartbeats 3200000 in
theorem signalMessageNew_placed_ok_gen_at [LibsignalPlacement]
    {Inv : Memory → Prop}
    (hInv_cl : ∀ {m}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hInv_kf : ∀ {m m'}, Inv m → Memory.KeepsFrozen m m' → Inv m')
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack saStack varStack : Nat}
    (hle_hook : allocHookStack ≤ hookStack := by decide)
    (hbnd_hook : hookStack + 944 ≤ 2 ^ 64 := by decide)
    (hsa_le : saStack ≤ hookStack + 528 := by decide)
    (hvar_le : varStack ≤ hookStack + 528 := by decide)
    (hready : ∀ sp0 : BitVec 64,
      stackAt sp0 ((hookStack + 528) + 416) =
        (∃∗ w408 : BitVec 64, ∃∗ w400 : BitVec 64, ∃∗ w392 : BitVec 64,
         ∃∗ w384 : BitVec 32, ∃∗ w380 : BitVec 32,
         ∃∗ w376 : BitVec 64, ∃∗ w368 : BitVec 64, ∃∗ w360 : BitVec 64,
         ∃∗ w352 : BitVec 64, ∃∗ w344 : BitVec 64, ∃∗ w332 : BitVec 32,
         ∃∗ w328 : BitVec 64, ∃∗ w320 : BitVec 64,
         ∃∗ w176 : BitVec 64, ∃∗ w168 : BitVec 64, ∃∗ w160 : BitVec 64,
          stackAt (sp0 - 416#64) (hookStack + 528) ∗ newUnusedPad sp0 ∗
          ((sp0 - 408#64) ↦₆₄ w408) ∗ ((sp0 - 400#64) ↦₆₄ w400) ∗ ((sp0 - 392#64) ↦₆₄ w392) ∗
          ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 376#64) ↦₆₄ w376) ∗
          ((sp0 - 368#64) ↦₆₄ w368) ∗ ((sp0 - 360#64) ↦₆₄ w360) ∗ ((sp0 - 352#64) ↦₆₄ w352) ∗
          ((sp0 - 344#64) ↦₆₄ w344) ∗ ((sp0 - 332#64) ↦₃₂ w332) ∗ ((sp0 - 328#64) ↦₆₄ w328) ∗
          ((sp0 - 320#64) ↦₆₄ w320) ∗ memRegion (sp0 - 312#64) 24 ∗ memRegion (sp0 - 288#64) 112 ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          memRegion (sp0 - 152#64) 16 ∗ cells (sp0 - 96#64) 12))
    (hst_entails : ∀ (sp0 : BitVec 64) (s0 : State) (pqCap : BitVec 64),
      stackAt (sp0 - 416#64) (hookStack + 528) ∗
        newFrameRest sp0 ∗
        ((sp0 - 320#64) ↦₆₄ pqCap) ∗
        newSavedRegs sp0 s0 ⊢
      stackAt sp0 ((hookStack + 528) + 416))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecWithStack M A lim hookStack)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A.repAlloc)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecWithStack A lim varStack)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecWithStack M A lim uuidTryParse saStack)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withMemInv Inv (computeMacSpecWithStack M A lim C.F (hookStack + 528)))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withMemInv Inv
        (signalMessageNewSpecWithStack M A lim C.F uuidTryParse ((hookStack + 528) + 416))) := by
  have hpk_le : hookStack + 32 ≤ hookStack + 528 := by omega
  have hcm_alloc_le : allocHookStack ≤ hookStack + 528 := by omega
  have henc_le : encodedLenStack ≤ hookStack + 528 := by
    have : encodedLenStack = 16 := rfl
    omega
  have hcm_bnd : hookStack + 528 ≤ 2 ^ 64 := by omega
  apply subroutine_ok_of_sepWPp_noPanic
    (Ppost := fun (x, st) s0 sf =>
      x.inputsAt A.repAlloc s0.sp ∗
        (∃∗ g : SignalMessageGhost, signalMessageAt A.repAlloc g x.ret (x.model C.F uuidTryParse)) ∗
        A.pool lim (M.stepEvents (signalMessageNewEvents uuidTryParse x) st) sf ∗
        stackAt s0.sp ((hookStack + 528) + 416))
    (fun ⟨x, st⟩ s0 sf htr => by
      dsimp only [withMemInv, signalMessageNewSpecWithStack]
      exact Entails.pure_right htr (Entails.refl _))
  intro ⟨x, st⟩ s0 hpc hrun hsp_align
  rw [show (withMemInv Inv
        (signalMessageNewSpecWithStack M A lim C.F uuidTryParse ((hookStack + 528) + 416))).pre
        (x, st) s0 =
      ⌜Inv s0.mem⌝ ∗
        (signalMessageNewSpecWithStack M A lim C.F uuidTryParse ((hookStack + 528) + 416)).pre
          (x, st) s0 from sepConj_comm _ _]
  simp only [signalMessageNewSpecWithStack, SignalMessageNewGhost.inputsAt, sepConj_assoc]
  refine SepWPp.pure_elim fun hcl0 => SepWPp.pure_elim fun
    ⟨hx0, hx1, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hx8, hct_bound, hpq_bound, hfit_env, hlr_ls⟩ => ?_
  obtain ⟨hfit_pro, hfit_post⟩ := fitsEvents_prologue_and_post_of_signalMessageNew hfit_env
  obtain ⟨hfit_ark, hfit_ct, hfit_pq, hstep_pro⟩ := fitsEvents_segments_of_prologue hfit_pro
  rw [newPostPrologueEvents_eq_serAlloc_append_phase3] at hfit_post
  obtain ⟨hfit_ser, hfit_phase3⟩ := (fitsEvents_append M lim _ _ _).mp hfit_post
  have hstep_all :
      M.stepEvents (newPhase3Events x)
        (M.stepEvents (rustAllocEvents ((encode (x.protoMsg uuidTryParse)).length + 9) 1)
          (M.stepEvents (newPrologueEvents uuidTryParse x) st)) =
      M.stepEvents (signalMessageNewEvents uuidTryParse x) st := by
    rw [signalMessageNewEvents_eq_prologue_append,
        newPostPrologueEvents_eq_serAlloc_append_phase3,
        M.stepEvents_append, M.stepEvents_append]
  conv => arg 4; rw [hready s0.sp]; simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w408 => SepWPp.exists_elim fun w400 =>
    SepWPp.exists_elim fun w392 => SepWPp.exists_elim fun w384 =>
    SepWPp.exists_elim fun w380 => SepWPp.exists_elim fun w376 =>
    SepWPp.exists_elim fun w368 => SepWPp.exists_elim fun w360 =>
    SepWPp.exists_elim fun w352 => SepWPp.exists_elim fun w344 =>
    SepWPp.exists_elim fun w332 => SepWPp.exists_elim fun w328 =>
    SepWPp.exists_elim fun w320 => SepWPp.exists_elim fun w176 =>
    SepWPp.exists_elim fun w168 => SepWPp.exists_elim fun w160 => ?_
  refine seq_wp_inv hInv_kf hcl0
    (new_prologue_wp_placed x s0.sp w368 w360 w352 w344 w328 w332 s0
      hpc hrun rfl hsp_align hx1 hx2 hx4 hx5 hx6 hx7 hx8)
    (by sep_focus) ?_
  intro s1 hcl1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx3_1, hx4_1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, htr1⟩
  refine seq_noPanic_inv hInv_kf hcl1
    (new_addr_and_rk_wpp_placed_at hpk_le hsa_le hcm_bnd hPk hSerAddr x s0.sp s1
      hfit_ark (hInv_cl hcl1) hpc1 hrun1 hsp1 hsp_align1
      (hx3_1.trans hx3) hloc_ne hx4_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1)
    (by sep_focus) ?_
  intro s2 hcl2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1
  refine seq_noPanic_inv hInv_kf hcl2
    (new_ct_copy_wpp_placed_at hcm_alloc_le hcm_bnd h_shim h_alloc h_mc x s0.sp
      (s2.readReg64 .x28) w400 hct_bound hfit_ct s2
      hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 rfl hx29_2)
    (by sep_focus) ?_
  intro s3 hcl3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, _hx25_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine seq_noPanic_inv hInv_kf hcl3
    (new_pq_copy_wpp_placed_at hcm_alloc_le hcm_bnd h_shim h_alloc h_mc x s0.sp
      (s2.readReg64 .x28) (s3.readReg64 .x26) hpq_bound hfit_pq s3
      hpc3 hrun3 hsp3 hsp_align3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 rfl hx27_3 hx28_3 hx29_3)
    (by sep_focus) ?_
  intro s4 hcl4 hpc4 hrun4 ⟨hsp4, hsp_align4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  rw [hstep_pro]
  refine SepWPp.fold (optSerializeAddressesAt_unpack A.repAlloc (s0.sp - 312#64) x) (by sep_focus) ?_
  conv => arg 4; simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun addrCap => SepWPp.exists_elim fun addrPtr => SepWPp.exists_elim fun addrLen => ?_
  refine SepWPp.fold (optPqBuf_extract_pin A.repAlloc (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hpq_pin => ?_
  refine SepWPp.fold (optAddrBuf_extract_cap A.repAlloc addrCap addrPtr addrLen (x.addresses uuidTryParse)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun haddrCap => ?_
  have hrk_buf :
      boxU8Buf A.repAlloc (s2.readReg64 .x28) x.senderRatchetKey.serialize =
        signalMessageNew_vecU8Buf A.repAlloc 33#64 (s2.readReg64 .x28) x.senderRatchetKey.serialize := by
    have hlen : x.senderRatchetKey.serialize.length = 33 := publicKey_serialize_length x.senderRatchetKey
    have h := (vecU8Buf_eq_boxU8Buf A.repAlloc (s2.readReg64 .x28) x.senderRatchetKey.serialize (by omega)).symm
    rw [hlen] at h
    exact h
  rw [hrk_buf]
  refine seq_wp_inv hInv_kf hcl4
    (new_store_wire_wp_placed x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr addrLen w376 w320
      hct_bound s4 hpc4 hrun4 hsp4 hsp_align4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4
      hx24_4 rfl hx26_4 hx27_4 hx28_4 hx29_4 rfl)
    (by sep_focus) ?_
  intro s5 hcl5 hpc5 hrun5 ⟨hsp5, hsp_align5, hx0_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  have hver32 : ((s0.readReg64 .x0).setWidth 32).setWidth 8 = x.messageVersion := by
    rw [← hx0]; bv_kernel
  refine seq_noPanic_inv hInv_kf hcl5
    (new_alloc_ser_wpp_placed_cl_at henc_le hcm_alloc_le hcm_bnd h_shim h_alloc hEncLen x s0.sp
      (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr w176 w168 w160 w384 w380 ((s0.readReg64 .x0).setWidth 32)
      hver32 hct_bound hpq_bound hfit_ser s5 (hInv_cl hcl5) hpc5 hrun5 hsp5 hsp_align5
      hx0_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5)
    (by sep_focus) ?_
  intro s6 hcl6 hpc6 hrun6 ⟨hsp6, hsp_align6, hx19_6, hx20_6, hx21_6, hx22_6, _hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  refine seq_noPanic_inv hInv_kf hcl6
    (new_encode_tag1_wpp_placed_at hvar_le hcm_bnd h_mc hVarint x s0.sp
      (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr (s6.readReg64 .x22) hct_bound hpq_bound hx22_6 s6
      (hInv_cl hcl6) hpc6 hrun6 hsp6 hsp_align6 hx19_6 hx20_6 hx21_6 rfl
      hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6)
    (by sep_focus) ?_
  intro s7 hcl7 hpc7 hrun7 ⟨hsp7, hsp_align7, hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, htr7⟩
  have htr7' : TraceVRegsEq s7 s0 := htr7.trans htr6'
  refine seq_noPanic_inv hInv_kf hcl7
    (new_encode_tag2_wpp_placed_at hvar_le hcm_bnd hVarint x s0.sp
      (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x25) (s6.readReg64 .x22)
      hct_bound hpq_bound hx22_6 s7 (hInv_cl hcl7) hpc7 hrun7 hsp7 hsp_align7
      hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hx25_7 hx26_7 hx27_7 hx28_7 hx29_7)
    (by sep_focus) ?_
  intro s8 hcl8 hpc8 hrun8 ⟨hsp8, hsp_align8, hx19_8, hx21_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8, hx29_8, htr8⟩
  have htr8' : TraceVRegsEq s8 s0 := htr8.trans htr7'
  refine seq_noPanic_inv hInv_kf hcl8
    (new_encode_tag3_wpp_placed_at hvar_le hcm_bnd hVarint x s0.sp
      (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      (s6.readReg64 .x22) hct_bound hpq_bound hx22_6 s8
      (hInv_cl hcl8) hpc8 hrun8 hsp8 hsp_align8
      hx19_8 hx21_8 hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8)
    (by sep_focus) ?_
  intro s9 hcl9 hpc9 hrun9 ⟨hsp9, hsp_align9, hx19_9, hx20_9, hx21_9, hx23_9, hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, htr9⟩
  have htr9' : TraceVRegsEq s9 s0 := htr9.trans htr8'
  refine seq_noPanic_inv hInv_kf hcl9
    (new_encode_tag4_wpp_placed_at hvar_le hcm_bnd h_mc hVarint x s0.sp
      (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr (s6.readReg64 .x22) w392 hct_bound hpq_bound hx22_6 s9
      (hInv_cl hcl9) hpc9 hrun9 hsp9 hsp_align9
      hx19_9 hx20_9 hx21_9 hx23_9 hx24_9 hx25_9 hx26_9 hx27_9 hx28_9 hx29_9)
    (by sep_focus) ?_
  intro s10 hcl10 hpc10 hrun10 ⟨hsp10, hsp_align10, hx19_10, hx20_10, hx21_10, hx23_10, hx24_10, hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, htr10⟩
  have htr10' : TraceVRegsEq s10 s0 := htr10.trans htr9'
  refine seq_noPanic_inv hInv_kf hcl10
    (new_encode_tag56_wpp_placed_at hvar_le hcm_bnd h_mc hVarint x s0.sp
      (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25)
      addrCap addrPtr (s6.readReg64 .x22) w408 hct_bound hpq_bound hx22_6 hpq_pin haddrCap s10
      (hInv_cl hcl10) hpc10 hrun10 hsp10 hsp_align10
      hx19_10 hx20_10 hx21_10 hx23_10 hx24_10 hx25_10 hx26_10 hx27_10 hx28_10 hx29_10)
    (by sep_focus) ?_
  intro s11 hcl11 hpc11 hrun11 ⟨hsp11, hsp_align11, hx19_11, hx20_11, hx21_11, hx22_11, _hx23_11, hx24_11, hx25_11, hx27_11, hx29_11, htr11⟩
  have htr11' : TraceVRegsEq s11 s0 := htr11.trans htr10'
  refine SepWPp.fold
    (wireSignalMessageAt_unpack_for_phase3 A.repAlloc x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr
      hct_bound hpq_pin haddrCap)
    (by sep_focus) ?_
  rw [show (encode (x.protoMsg uuidTryParse)).length + 9 =
      1 + (encode (x.protoMsg uuidTryParse)).length + 8 by omega]
  simp only [sepConj_assoc]
  refine seq_noPanic_inv hInv_kf hcl11
    (new_phase3_wpp_placed_gen_at hInv_kf hle_hook hbnd_hook (hst_entails s0.sp s0)
      h_shim h_alloc h_dealloc h_mc hMac x
      (s6.readReg64 .x22) (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap
      ((s0.readReg64 .x0).setWidth 32) hver32 haddrCap hct_bound hpq_bound hfit_phase3
      s11 hcl11 hpc11 hrun11 hsp11 rfl hsp_align hsp_align11
      hx19_11 hx20_11 hx21_11 hx22_11 hx24_11 hx25_11 hx27_11 hx29_11 htr11' hlr_ls)
    (by sep_focus) ?_
  intro sf _ hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  simp only [sepConj_assoc]
  rw [hstep_all]
  exact entails_of_sep_focus (by sep_focus)

/-- Relocatable `[LibsignalPlacement]` budget proof for `<SignalMessage>::new` (`signalMessageNewStack`,
`withLsCodeLoaded`). -/
theorem signalMessageNew_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A.repAlloc)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec M A lim uuidTryParse)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec M A lim C.F))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withLsCodeLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)) :=
  signalMessageNew_placed_ok_gen_at (Inv := LibsignalCodeLoaded lsmpl)
    (hookStack := allocHookStack) (saStack := serializeAddressesStack)
    (varStack := encodeVarintStack)
    (fun h => h) (fun h hkf => h.of_keepsFrozen hkf)
    (by decide) (by decide) (by decide) (by decide)
    stackAt_signalMessageNewStack_ready
    (fun sp0 s0 c => newFrameRest_entails_stackAt sp0 c s0)
    h_shim h_alloc h_dealloc h_mc hPk hEncLen
    (by rwa [← encodeVarintSpec_eq_withStack]) hSerAddr hMac

/-- Relocatable `[LibsignalPlacement]` budget proof for `<SignalMessage>::new` (`signalMessageNewStackX`,
`withLsCodeLoaded`). -/
theorem signalMessageNew_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A.repAlloc)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX M A lim uuidTryParse)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecX M A lim C.F))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withLsCodeLoaded lsmpl (signalMessageNewSpecX M A lim C.F uuidTryParse)) :=
  signalMessageNew_placed_ok_gen_at (Inv := LibsignalCodeLoaded lsmpl)
    (hookStack := extHookStack) (saStack := serializeAddressesStackX)
    (varStack := encodeVarintStackX)
    (fun h => h) (fun h hkf => h.of_keepsFrozen hkf)
    (by decide) (by decide) (by decide) (by decide)
    stackAt_signalMessageNewStackX_ready
    (fun sp0 s0 c => newFrameRest_entails_stackAtX sp0 c s0)
    h_shim h_alloc h_dealloc h_mc hPk hEncLen
    (by rwa [← encodeVarintSpecX_eq_withStack]) hSerAddr hMac

/-- Relocatable `[LibsignalPlacement]` budget proof for `<SignalMessage>::new` (`signalMessageNewStack`,
`withLsCodeRoLoaded`). -/
theorem signalMessageNew_placed_cro_ok [LibsignalPlacement]
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A.repAlloc)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec M A lim uuidTryParse)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeRoLoaded lsmpl (computeMacSpec M A lim C.F))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)) :=
  signalMessageNew_placed_ok_gen_at (Inv := LibsignalCodeRoLoaded lsmpl)
    (hookStack := allocHookStack) (saStack := serializeAddressesStack)
    (varStack := encodeVarintStack)
    (fun h => h.1) (fun h hkf => h.of_keepsFrozen hkf)
    (by decide) (by decide) (by decide) (by decide)
    stackAt_signalMessageNewStack_ready
    (fun sp0 s0 c => newFrameRest_entails_stackAt sp0 c s0)
    h_shim h_alloc h_dealloc h_mc hPk hEncLen
    (by rwa [← encodeVarintSpec_eq_withStack]) hSerAddr hMac

/-- Relocatable `[LibsignalPlacement]` budget proof for `<SignalMessage>::new` (`signalMessageNewStackX`,
`withLsCodeRoLoaded`). -/
theorem signalMessageNew_placed_cro_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108)
      (withLsCodeLoaded lsmpl (encodedLenSpec A.repAlloc)))
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX M A lim uuidTryParse)))
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeRoLoaded lsmpl (computeMacSpecX M A lim C.F))) :
    subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (blkPl_63).base
      (withLsCodeRoLoaded lsmpl (signalMessageNewSpecX M A lim C.F uuidTryParse)) :=
  signalMessageNew_placed_ok_gen_at (Inv := LibsignalCodeRoLoaded lsmpl)
    (hookStack := extHookStack) (saStack := serializeAddressesStackX)
    (varStack := encodeVarintStackX)
    (fun h => h.1) (fun h hkf => h.of_keepsFrozen hkf)
    (by decide) (by decide) (by decide) (by decide)
    stackAt_signalMessageNewStackX_ready
    (fun sp0 s0 c => newFrameRest_entails_stackAtX sp0 c s0)
    h_shim h_alloc h_dealloc h_mc hPk hEncLen
    (by rwa [← encodeVarintSpecX_eq_withStack]) hSerAddr hMac

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewBudget
