/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# SPQR V1: Budget-Threaded `Option` Field Init Helpers for `Chunked.Ct1Sampled::merge` (Block `300`)

Proves the three `Option` field initialization step helpers (`tag1_init` for `uc`,
`tag2_init` for `sendingCt1`, and `tag3_init` for `receivingEk`) for
`V1State.Chunked.Ct1Sampled::merge` (Block `300`) with `spqrPoolAt` threading.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetInit

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk sliceCursorAfter)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.ProtoRepr
  (optPolynomialDecoderPBAt optPolynomialEncoderPBAt
   polynomialDecoderPBAt polynomialEncoderPBAt vecVecU8At
   vecVecU8At_eq_exists_pin vecVecU8Buf vecVecU8PinnedAt_eq_header_buf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (cap_add_one_beq_zero_false cap_add_one_bne_zero_true
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1SampledMergeGhost ChunkedLoopRegs SepWPpLscro
   bv64_add_zero bv64_sub_zero chunkedBelow chunkedCt1SampledMerge_fnOff
   chunkedCt1SampledPBCapAt chunkedSavedRegs
   default_ct1Sent_entails_cap default_polyDecoder_entails_pb
   default_polyEncoder_entails_pb memRegion_ct1Sent_none_split
   memRegion_polyDecoder_none_split memRegion_polyEncoder_none_split
   optUnchunkedCt1SentPBCapAt unchunkedCt1SentPBCapAt
   vecU8At_eq_header_sep_buf vecU8Buf vecU8Buf_entails_cap_lt vecVecU8Buf_entails_cap_lt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_300 blkPl_300)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
  (ct1SampledLoopPre)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (chunkedCt1SampledMergeSpec ct1SampledPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse sepWPpLscro_of_vm spqrPoolAt spqrPoolAt_of_vmPreserved)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt1SampledMerge_fnOff

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_300).base

theorem ct1Sampled_tag1_init_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)}
    {v0 : BitVec 64} {limit : Nat}
    (hpc : s.pc = (blkPl_300).base + 368#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_300).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length (m.uc.getD default) ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) s' ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1SampledPolyCapBound x))
      (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases huc : m.uc with _ | u
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 404#64)
    by_vm_steps
      (conv => arg 4; rw [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, huc,
        optUnchunkedCt1SentPBCapAt, memRegion_ct1Sent_none_split x.msgPtr])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w120; apply SepWP.exists_elim; intro w72
      apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
      apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (default_ct1Sent_entails_cap A.repAlloc x.msgPtr rest.length) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length default ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.weaken_pre
      (P' := unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length u ∗
        optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
        optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
          (ct1SampledPolyCapBound x) s ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
      (by rw [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, huc, optUnchunkedCt1SentPBCapAt];
          exact Entails.of_eq (by sep_ac_rfl))
    apply sepWPpLscro_of_vm (mid := entry + 404#64)
    by_vm_steps
      (conv => arg 4; rw [unchunkedCt1SentPBCapAt])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro cap_ct1; apply SepWP.exists_elim; intro ptr_ct1
      apply SepWP.exists_elim; intro cap_es; apply SepWP.exists_elim; intro ptr_es
      apply SepWP.exists_elim; intro cap_hdr; apply SepWP.exists_elim; intro ptr_hdr
      apply SepWP.pure_elim; intro hcap_hdr
      (conv => arg 4; rw [vecU8At_eq_header_sep_buf A.repAlloc x.msgPtr cap_hdr ptr_hdr u.hdr, vecHeader])
      (conv => arg 4; simp only [sepConj_assoc])
      apply SepWP.fold (vecU8Buf_entails_cap_lt A.repAlloc cap_hdr ptr_hdr u.hdr) (by sep_focus)
      (conv => arg 4; simp only [sepConj_assoc])
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hfold_hdr : (x.msgPtr ↦₆₄ cap_hdr) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr_hdr) ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
          vecU8Buf A.repAlloc cap_hdr ptr_hdr u.hdr ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
            ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc x.msgPtr cap ptr u.hdr) := by
        refine Entails.trans ?_ (Entails.sepExists_right cap_hdr (Entails.sepExists_right ptr_hdr (Entails.refl _)))
        refine Entails.pure_right hcap_hdr ?_
        rw [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl)
      have hfold_es : ⌜BytesMergeCapOk cap_es rest.length⌝ ∗
          vecU8At A.repAlloc (x.msgPtr + 24#64) cap_es ptr_es u.es ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
            ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc (x.msgPtr + 24#64) cap ptr u.es) :=
        Entails.sepExists_right cap_es (Entails.sepExists_right ptr_es (Entails.refl _))
      have hfold_ct1 : ⌜BytesMergeCapOk cap_ct1 rest.length⌝ ∗
          vecU8At A.repAlloc (x.msgPtr + 48#64) cap_ct1 ptr_ct1 u.ct1 ⊢
          (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
            ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A.repAlloc (x.msgPtr + 48#64) cap ptr u.ct1) :=
        Entails.sepExists_right cap_ct1 (Entails.sepExists_right ptr_ct1 (Entails.refl _))
      apply SepWP.fold hfold_hdr (by sep_focus)
      apply SepWP.fold hfold_es (by sep_focus)
      apply SepWP.fold hfold_ct1 (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length u ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by dsimp only [unchunkedCt1SentPBCapAt]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩

theorem ct1Sampled_tag2_init_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)}
    {v0 : BitVec 64} {limit : Nat}
    (hpc : s.pc = (blkPl_300).base + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_300).base + 344#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (polynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) (m.sendingCt1.getD default) ∗
          optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) s' ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1SampledPolyCapBound x))
      (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hpe : m.sendingCt1 with _ | pe
  · rw [hpe] at hcont; dsimp only [Option.getD] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 344#64)
    by_vm_steps
      (conv => arg 4; rw [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, hpe,
        optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split (x.msgPtr + 128#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (default_polyEncoder_entails_pb A.repAlloc (x.msgPtr + 128#64)) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := polynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) default ∗
          optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩
  · rw [hpe] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.weaken_pre
      (P' := polynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) pe ∗
        optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
        optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
          (ct1SampledPolyCapBound x) s ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
      (by rw [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, hpe, optPolynomialEncoderPBAt];
          exact Entails.of_eq (by sep_ac_rfl))
    apply sepWPpLscro_of_vm (mid := entry + 344#64)
    by_vm_steps
      (conv => arg 4; rw [polynomialEncoderPBAt,
        vecVecU8At_eq_exists_pin A.repAlloc (x.msgPtr + 128#64) pe.pts])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro pin
      (conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc])
      apply SepWP.fold (vecVecU8Buf_entails_cap_lt A.repAlloc pin.cap pin.ptr pe.pts) (by sep_focus)
      (conv => arg 4; simp only [sepConj_assoc])
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hfold_pts : ((x.msgPtr + 128#64) ↦₆₄ pin.cap) ∗
          ((x.msgPtr + 128#64 + 8#64) ↦₆₄ pin.ptr) ∗
          ((x.msgPtr + 128#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pe.pts.length) ∗
          vecVecU8Buf A.repAlloc pin.cap pin.ptr pe.pts ⊢
          vecVecU8At A.repAlloc (x.msgPtr + 128#64) pe.pts := by
        rw [vecVecU8At_eq_exists_pin]
        refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
        rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hfold_pts (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := polynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) pe ∗
          optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by dsimp only [polynomialEncoderPBAt]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩

theorem ct1Sampled_tag3_init_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)}
    {v0 : BitVec 64} {limit : Nat}
    (hpc : s.pc = (blkPl_300).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_300).base + 292#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = v0 →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (polynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) (m.receivingEk.getD default) ∗
          optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) s' ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1SampledPolyCapBound x))
      (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hpd : m.receivingEk with _ | pd
  · rw [hpd] at hcont; dsimp only [Option.getD] at hcont
    apply sepWPpLscro_of_vm (mid := entry + 292#64)
    by_vm_steps
      (conv => arg 4; rw [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, hpd,
        optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split (x.msgPtr + 184#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (default_polyDecoder_entails_pb A.repAlloc (x.msgPtr + 184#64)) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := polynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) default ∗
          optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩
  · rw [hpd] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.weaken_pre
      (P' := polynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) pd ∗
        optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
        optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
        spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
          (ct1SampledPolyCapBound x) s ∗
        memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
      (by rw [ct1SampledLoopPre, chunkedCt1SampledPBCapAt, hpd, optPolynomialDecoderPBAt];
          exact Entails.of_eq (by sep_ac_rfl))
    apply sepWPpLscro_of_vm (mid := entry + 292#64)
    by_vm_steps
      (conv => arg 4; rw [polynomialDecoderPBAt,
        vecVecU8At_eq_exists_pin A.repAlloc (x.msgPtr + 184#64) pd.pts])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro pin
      (conv => arg 4; rw [vecVecU8PinnedAt_eq_header_buf]; simp only [sepConj_assoc])
      apply SepWP.fold (vecVecU8Buf_entails_cap_lt A.repAlloc pin.cap pin.ptr pd.pts) (by sep_focus)
      (conv => arg 4; simp only [sepConj_assoc])
      apply SepWP.pure_elim; intro hcap_lt
      have hcmn1 := cap_add_one_beq_zero_false hcap_lt
      have hcmn2 := cap_add_one_bne_zero_true hcap_lt
      wp_steps
      have hfold_pts : ((x.msgPtr + 184#64) ↦₆₄ pin.cap) ∗
          ((x.msgPtr + 184#64 + 8#64) ↦₆₄ pin.ptr) ∗
          ((x.msgPtr + 184#64 + 16#64) ↦₆₄ BitVec.ofNat 64 pd.pts.length) ∗
          vecVecU8Buf A.repAlloc pin.cap pin.ptr pd.pts ⊢
          vecVecU8At A.repAlloc (x.msgPtr + 184#64) pd.pts := by
        rw [vecVecU8At_eq_exists_pin]
        refine Entails.trans ?_ (Entails.sepExists_right pin (Entails.refl _))
        rw [vecVecU8PinnedAt_eq_header_buf]; exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hfold_pts (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := polynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) pd ∗
          optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
            (ct1SampledPolyCapBound x) _ ∗
          memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
        (by dsimp only [polynomialDecoderPBAt]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25],
         ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
          by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetInit
