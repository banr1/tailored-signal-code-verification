/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoop
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep

/-!
# Budget-Threaded Protobuf Decode Loop for `PreKeySignalMessage::try_from` (Block `111`)

Defines the deterministic loop allocator event trace `preKeyLoopEvents` and proves panic-free
`RustCliAllocBudget M` specifications for the prologue and 8-field protobuf decode loop
(`+0 → +0x460`) of Block `111` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open scoped CryptoVerification.RustHeap
open CryptoVerification (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkLib_eq_111 blkPC_111 blkPl_111 lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (PreKeyLoopRegs PreKeyTryFromArgs bv_add_neg_104 bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_16 bv_add_neg_160 bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191 bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40 bv_add_neg_48 bv_add_neg_512 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72 bv_add_neg_8 bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_sub_add_lit' bv_sub_sub_lit bytes_eq_cons_psmRem0 cond_eq_subs1_false cons_sliceCursorAfter_split cur0 cur1 cur2 cur3 cur4 cur5 cur6 cur7 cur8 memRegion152_init_cells memRegion96_split_preKeyCalleeSaved merge_field1_some merge_field2 merge_field3 merge_field4 merge_field5 merge_field6 merge_field7 merge_field8 ofNat64_cons_sub_one ofNat64_length_ne_zero opkTag pointsToBytes_psm_reassemble preKeyCalleeSavedAt psmField1 psmField1_some psmField2 psmField2_eq psmField3 psmField3_eq psmField4 psmField4_eq psmField5 psmField5_eq psmField6 psmField6_eq psmField7 psmField7_eq psmField8 psmField8_eq psmRem0 psmRem0_ne_nil psmRem1 psmRem1_ne_nil psmRem2 psmRem2_ne_nil psmRem3 psmRem3_ne_nil psmRem4 psmRem4_ne_nil psmRem5 psmRem5_ne_nil psmRem6 psmRem6_ne_nil psmRem7 psmRem7_ne_nil psmRem8 psmRem_lengths_lt spAligned_sub608 stackAt_bytesMerge_split_int32)
open CryptoVerification.LibsignalProtoCodec (encodeVarint mergeBytes mergeUint32)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk BytesMergeGhost Int32MergeGhost bytesMergeCapOk_of_len_lt32 bytesMergeStack int32MergeStack sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalTripleRatchet.Wire (entails_of_eq memRegion16_split8_8' pointsTo32_memRegion4_entails_exists_pointsTo64 pointsTo64_emptyVec_eq_vecU8At pointsTo64_one_entails_pointsTo32_memRegion4)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (vecU8At)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved fitsEvents_append)

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoopBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  Int32MergeEnv int32MergeEvents int32MergeSpec int32MergeSpecGen
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bmPostVec bmPreBoundBudget bytesMergeEventsCore bytesMergeRawSpec
  bytesMergeRawSpecGen
)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit' bv_sub_sub_lit
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## Allocator Event Trace and `SepWPp` Combinators -/

/-- Exact allocator event list of the 4 `bytes::merge` field decodes (`bk`, `ik`, `inner`,
`kyber`) in `PreKeySignalMessage::try_from`'s protobuf decode loop on `x : PreKeyTryFromArgs`. -/
def preKeyLoopEvents (x : PreKeyTryFromArgs) : List AllocEvent :=
  bytesMergeEventsCore .lengthDelimited 0#64 (encodeVarint 33#64 ++ x.bkBytes ++ psmRem2 x) ++
    bytesMergeEventsCore .lengthDelimited 0#64 (encodeVarint 33#64 ++ x.ikBytes ++ psmRem3 x) ++
    bytesMergeEventsCore .lengthDelimited 0#64
      (encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner ++ psmRem4 x) ++
    bytesMergeEventsCore .lengthDelimited 0#64
      (encodeVarint 1569#64 ++ x.kyberBytes ++ psmRem8 x)

def PreKeyLoopEnv (x : PreKeyTryFromArgs) (evs : List AllocEvent) : Prop :=
  evs = preKeyLoopEvents x

/-- Individual field `bytes::merge` event lists (`bk`, `ik`, `inner`, `kyber`). -/
abbrev psmEvs2 (x : PreKeyTryFromArgs) : List AllocEvent :=
  bytesMergeEventsCore .lengthDelimited 0#64 (encodeVarint 33#64 ++ x.bkBytes ++ psmRem2 x)

abbrev psmEvs3 (x : PreKeyTryFromArgs) : List AllocEvent :=
  bytesMergeEventsCore .lengthDelimited 0#64 (encodeVarint 33#64 ++ x.ikBytes ++ psmRem3 x)

abbrev psmEvs4 (x : PreKeyTryFromArgs) : List AllocEvent :=
  bytesMergeEventsCore .lengthDelimited 0#64
    (encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner ++ psmRem4 x)

abbrev psmEvs8 (x : PreKeyTryFromArgs) : List AllocEvent :=
  bytesMergeEventsCore .lengthDelimited 0#64 (encodeVarint 1569#64 ++ x.kyberBytes ++ psmRem8 x)

abbrev withLoopInv {α : Type} (Inv : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜Inv s0.mem⌝ }

def noPanicQp (_s0 : State) : State → SepProp → Prop :=
  fun _ _ => False

theorem sepWPp_weaken_qp {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q (noPanicQp s0)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hqf, hv⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hqf, hv⟩⟩
  · exact hqp.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_frame_noPanic {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q Q' : State → SepProp → Prop}
    (h : CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q' (noPanicQp s0))
    (hq : ∀ sf Pm, Q' sf Pm → Q sf (Pm ∗ F)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s (P ∗ F) Q (noPanicQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pm, hmm, hqm, hv⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pm ∗ F, hmm, hq sf Pm hqm, hv⟩⟩
  · exact hqp.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_bind_frame_noPanic {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P F : SepProp} {Q1 Q2 : State → SepProp → Prop}
    (h1 : CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog mid s P Q1 (noPanicQp s0))
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q1 sm Pm →
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret sm (Pm ∗ F) Q2 (noPanicQp s0)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s (P ∗ F) Q2 (noPanicQp s0) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hq1, hvm⟩ | ⟨_, _, _, hqp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hq2, hvf⟩ | hpanf⟩ :=
      h2 sm Pm hpcm hrunm hq1 R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpcf, hrunf, Pf, hmf, hq2, hvf.trans hvm⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · exact hqp.elim
  · exact (not_satisfies_false_sepConj hoom).elim

abbrev KeepsFrozenInv (Inv : Memory → Prop) : Prop :=
  ∀ ⦃m m' : Memory⦄, m.KeepsFrozen m' → Inv m → Inv m'

theorem keepsFrozenInv_codeLoaded [LibsignalPlacement] :
    KeepsFrozenInv (LibsignalCodeLoaded lsmpl) :=
  fun _ _ hkf hcl => hcl.of_keepsFrozen hkf

theorem keepsFrozenInv_codeRoLoaded [LibsignalPlacement] :
    KeepsFrozenInv (LibsignalCodeRoLoaded lsmpl) :=
  fun _ _ hkf hcro => hcro.of_keepsFrozen hkf

theorem sepWPp_of_sepWP_inv {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      CryptoVerification.LibsignalTripleRatchet.Wire.VRegsAt s sm ∧
      (Inv sm.mem → CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret sm Pm Q Qp))) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | hoom⟩
  · have hinv_m := hkf hsteps.keepsFrozen hinv
    obtain ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hq, hvf⟩ | hpan⟩ :=
      hnext hinv_m R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hq, hvf.trans hv.eq⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpan⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_of_sepWP_end_inv {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {prog : Program} {ret : BitVec 64} {s0 s : State} {P : SepProp}
    {Q : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      CryptoVerification.LibsignalTripleRatchet.Wire.VRegsAt s sf ∧
      (Inv sf.mem → Q sf Pf))) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hkf hsteps.keepsFrozen hinv), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_seg_inv_vm [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {H : LibsignalHooks} {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop} (hinv : Inv s.mem)
    (hseg : ∀ m_strip : Memory,
      ProofLib.SepWP ((blkPC_111).rebase (blkPl_111).base (hooksException H))
        mid (s.setMem m_strip) Pre (fun sm' Pm =>
          CryptoVerification.LibsignalTripleRatchet.Wire.VRegsAt (s.setMem m_strip) sm' ∧
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) → Inv m_real →
            CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ret (sm'.setMem m_real) Pm Q Qp)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ret s Pre Q Qp := by
  refine sepWPp_of_sepWP_inv hkf hinv (mid := mid) ?_
  apply sepWP_seg_ls_vm (Q := (blkPC_111).rebase (blkPl_111).base (hooksException H))
    blkLib_eq_111 (mid := mid)
  intro m_strip; refine ProofLib.SepWP.of_reaches_pc fun R hm hL => ?_
  rcases ProofLib.SepWP.to_reaches_pc (hseg m_strip) hm hL with
    ⟨sm', hsteps, ⟨hpcm', hrunm', Pm, hmm', hv, hnext⟩ | hoom⟩
  · exact ⟨sm', hsteps, Or.inl ⟨hpcm', hrunm', Pm, hmm', fun m_real hnsp =>
      ProofLib.SepWP.done (by simpa [arm64_norm] using hpcm') (by simpa [arm64_norm] using hrunm')
        ⟨⟨by simpa [arm64_norm] using hv.eq⟩, fun hinv_m => hnext m_real hnsp hinv_m⟩⟩⟩
  · exact ⟨sm', hsteps, Or.inr hoom⟩

theorem sepWPp_end_inv_vm [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {H : LibsignalHooks} {ret : BitVec 64} {s0 s : State} {Pre : SepProp}
    {Q : State → SepProp → Prop} (hinv : Inv s.mem)
    (hseg : ∀ m_strip : Memory,
      ProofLib.SepWP ((blkPC_111).rebase (blkPl_111).base (hooksException H))
        ret (s.setMem m_strip) Pre (fun sm' Pm =>
          CryptoVerification.LibsignalTripleRatchet.Wire.VRegsAt (s.setMem m_strip) sm' ∧
          ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            Inv m_real → Q (sm'.setMem m_real) Pm)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ret s Pre Q (noPanicQp s0) := by
  refine sepWPp_of_sepWP_end_inv hkf hinv ?_
  apply sepWP_seg_ls_vm (Q := (blkPC_111).rebase (blkPl_111).base (hooksException H))
    blkLib_eq_111 (mid := ret)
  intro m_strip; refine ProofLib.SepWP.of_reaches_pc fun R hm hL => ?_
  rcases ProofLib.SepWP.to_reaches_pc (hseg m_strip) hm hL with
    ⟨sm', hsteps, ⟨hpcm', hrunm', Pm, hmm', hv, hnext⟩ | hoom⟩
  · exact ⟨sm', hsteps, Or.inl ⟨hpcm', hrunm', Pm, hmm', fun m_real hnsp =>
      ProofLib.SepWP.done (by simpa [arm64_norm] using hpcm') (by simpa [arm64_norm] using hrunm')
        ⟨⟨by simpa [arm64_norm] using hv.eq⟩, fun hinv_m => hnext m_real hnsp hinv_m⟩⟩⟩
  · exact ⟨sm', hsteps, Or.inr hoom⟩

theorem sepWPp_call_noPanic_inv {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {α : Type} {prog : Program} {ret entry ret_pc : BitVec 64}
    {s0 s : State} {P T F : SepProp} {φ : Prop} {Q : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLoopInv Inv spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hinv : Inv s.mem) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → Inv sf.mem → CalleeSavedPreserved s sf →
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (noPanicQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q (noPanicQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withLoopInv Inv spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withLoopInv]; rw [hspec]
    have hcomm : ((⌜φ⌝ ∗ T) ∗ ⌜Inv s.mem⌝) ∗ (F ∗ R') = ⌜φ⌝ ∗ (⌜Inv s.mem⌝ ∗ ((T ∗ F) ∗ R')) := by
      sep_ac_rfl
    rw [hcomm, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
    rw [satisfies_pure_sepConj, ← hP]; exact ⟨hinv, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · dsimp only [withLoopInv] at hpost; rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [State.spAligned, hspm, ← State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align (hkf hsteps.keepsFrozen hinv) hcsm R' hpost
        (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withLoopInv] at hpost; rw [hpan_eq sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLoopInv] at hpost; rw [hexit sm code] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLoopInv] at hoom; rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem subroutine_ok_withLoopInv_of_cro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLoopInv (LibsignalCodeRoLoaded lsmpl) spec) := h

theorem fitsEnv_int32Merge_of_some {M : AllocCostModel} (lim : BudgetLimits) (st : M.σ)
    (g : Int32MergeGhost) {v : BitVec 32} {rest : List (BitVec 8)}
    (hm : mergeUint32 g.wt g.bs = some (v, rest)) : FitsEnv M lim st (Int32MergeEnv g) := by
  intro evs hevs; simp only [Int32MergeEnv, int32MergeEvents, hm] at hevs; subst hevs
  exact _root_.LibsignalBinary.Heap.FitsEnv.nil [] rfl

/-! ## Prologue and Field Decode Steps (Block `111`) -/

theorem prologue_to_c24_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {H : LibsignalHooks} {x : PreKeyTryFromArgs} {s0 : State} (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base) (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hinv : Inv s0.mem) (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length) (hx8 : s0.readReg64 .x8 = x.sret) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun s1 P1 =>
        PreKeyLoopRegs (s0.sp - 608#64) x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ VmPreserved s0 s1 ∧
        s1.trace = s0.trace ∧ s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem0 x).length ∧
        (P1 ⊢ (x.ptr ↦₈ 0x44#8) ∗ sliceCursorAt (s0.sp - 608#64 + 296#64) (cur0 x) (psmRem0 x) ∗
          ((s0.sp - 608#64 + 440#64) ↦₆₄ (s0.sp - 608#64 + 296#64)) ∗
          ((s0.sp - 608#64 + 312#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 320#64) 16 ∗
          ((s0.sp - 608#64 + 336#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 344#64) 16 ∗
          ((s0.sp - 608#64 + 360#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 368#64) 16 ∗
          ((s0.sp - 608#64 + 384#64) ↦₆₄ noneCap) ∗ memRegion (s0.sp - 608#64 + 392#64) 16 ∗
          ((s0.sp - 608#64 + 408#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 412#64) 4 ∗
          ((s0.sp - 608#64 + 416#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 420#64) 4 ∗
          ((s0.sp - 608#64 + 424#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 428#64) 4 ∗
          ((s0.sp - 608#64 + 432#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 608#64 + 436#64) 4 ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (noPanicQp s0) := by
  have hb := bytes_eq_cons_psmRem0 x
  have hge2 : 2 ≤ x.bytes.length := by
    have hrem0 := List.length_pos_of_ne_nil (psmRem0_ne_nil x); rw [hb, List.length_cons]; omega
  have hlen_beq : (BitVec.ofNat 64 x.bytes.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (ofNat64_length_ne_zero (by rw [hb]; simp) hlt)
  have hcond_eq := cond_eq_subs1_false hge2 hlt
  have hsub1 : BitVec.ofNat 64 x.bytes.length - 1#64 = BitVec.ofNat 64 (psmRem0 x).length := by
    rw [hb, ofNat64_cons_sub_one]
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ 0x44#8) ∗ ((x.ptr + 1#64) ↦ₛ psmRem0 x) := by
    rw [hb, pointsToBytes_cons]
  clear hb; rw [hbytes]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (memRegion152_init_cells (s0.sp - 608#64))
        (memRegion96_split_preKeyCalleeSaved (s0.sp - 608#64)))) ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w19 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w20 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w21 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w22 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w23 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w24 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w25 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w26 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w27 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w28 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w30 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w29 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w440 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w432 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w424 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w416 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w408 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w384 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w360 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w336 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w312 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c1 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun c0 => sepWPp_end_inv_vm hkf hinv fun m_strip => ?_
  wp_steps
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun m_real hnsp hinv1 => ?_
  refine ⟨⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩,
    by rw [State.spAligned]; simpa [arm64_norm] using spAligned_sub608 hsp,
    hinv1, hnsp.toVmPreserved (by simp [arm64_norm]), by simp [arm64_norm], by simp [arm64_norm], ?_⟩
  unfold sliceCursorAt preKeyCalleeSavedAt cur0 noneCap; simp only [arm64_norm]
  apply entails_of_eq; sep_ac_rfl

abbrev prologue_to_c24_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    {x : PreKeyTryFromArgs} {s0 : State} :=
  prologue_to_c24_inv_wp (H := H) (x := x) (s0 := s0) keepsFrozenInv_codeLoaded

private theorem call_int32Merge_some [LibsignalPlacement] {Inv : Memory → Prop}
    (hkf : KeepsFrozenInv Inv) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    {ret ret_pc sp' tagOff valOff curK curNext : BitVec 64} {tagByte : BitVec 8} {v : BitVec 32}
    {body remNext fieldBytes : List (BitVec 8)} {s0 s1b : State} {Q : State → SepProp → Prop}
    (hpc : s1b.pc = lsmpl.base 8) (hrun : s1b.status = .Running)
    (hsp_eq : s1b.sp = sp') (hsp : s1b.spAligned = true) (hinv : Inv s1b.mem)
    (hlr : s1b.readReg64 Reg.lr = ret_pc)
    (hx0 : (s1b.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 CryptoVerification.LibsignalProtoCodec.WireType.varint.toNat)
    (hx1 : s1b.readReg64 .x1 = sp' + valOff) (hx2 : s1b.readReg64 .x2 = sp' + 440#64)
    (hlt : (body ++ remNext).length < 2 ^ 63)
    (hm : mergeUint32 .varint (body ++ remNext) = some (v, remNext))
    (hcur_split : (curK ↦₈ tagByte) ∗
        sliceCursorAfter (sp' + 296#64) (curK + 1#64) (body ++ remNext) remNext =
      (curK ↦ₛ fieldBytes) ∗ (((sp' + 296#64) ↦₆₄ curNext) ∗
        (((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 remNext.length) ∗ (curNext ↦ₛ remNext))))
    (hnext : ∀ s2 : State, s2.pc = ret_pc → s2.status = .Running → s2.sp = s1b.sp →
      s2.spAligned = true → Inv s2.mem → CalleeSavedPreserved s1b s2 →
      s2.trace = s1b.trace → s2.readReg64 .x0 = 0#64 →
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ret s2
        ((curK ↦ₛ fieldBytes) ∗ ((sp' + 296#64) ↦₆₄ curNext) ∗
          ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 remNext.length) ∗ (curNext ↦ₛ remNext) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + tagOff) ↦₃₂ 1#32) ∗
          ((sp' + valOff) ↦₃₂ v) ∗ A.pool lim st s2 ∗ stackAt sp' int32MergeStack)
        Q (noPanicQp s0)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ret s1b
      (((sp' + tagOff) ↦₃₂ 1#32) ∗ memRegion (sp' + valOff) 4 ∗ (curK ↦₈ tagByte) ∗
        sliceCursorAt (sp' + 296#64) (curK + 1#64) (body ++ remNext) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ A.pool lim st s1b ∗ stackAt sp' int32MergeStack)
      Q (noPanicQp s0) := by
  let g : Int32MergeGhost :=
    ⟨.varint, sp' + valOff, sp' + 440#64, sp' + 296#64, curK + 1#64, body ++ remNext⟩
  refine sepWPp_call_noPanic_inv hkf (g, st) hint32 hpc hrun hsp hinv hlr
    (T := memRegion (sp' + valOff) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (curK + 1#64) (body ++ remNext) ∗ A.pool lim st s1b ∗
      stackAt sp' int32MergeStack)
    (φ := (s1b.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 CryptoVerification.LibsignalProtoCodec.WireType.varint.toNat ∧
      s1b.readReg64 .x1 = sp' + valOff ∧ s1b.readReg64 .x2 = sp' + 440#64 ∧
      (body ++ remNext).length < 2 ^ 63 ∧ FitsEnv M lim st (Int32MergeEnv g))
    (by dsimp only [int32MergeSpec, int32MergeSpecGen, int32MergeStack, g]; rw [hsp_eq])
    ⟨hx0, hx1, hx2, hlt, fitsEnv_int32Merge_of_some lim st g hm⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [int32MergeSpec, int32MergeSpecGen, g]; rw [hm]; dsimp only
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := ⌜s2.trace = s1b.trace⌝ ∗ (⌜Int32MergeEnv g evs⌝ ∗ (⌜s2.readReg64 .x0 = 0#64⌝ ∗
      (((curK ↦₈ tagByte) ∗ sliceCursorAfter (sp' + 296#64) (curK + 1#64) (body ++ remNext) remNext) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + tagOff) ↦₃₂ 1#32) ∗ ((sp' + valOff) ↦₃₂ v) ∗
      A.pool lim (M.stepEvents evs st) s2 ∗ stackAt sp' int32MergeStack))))
    (by dsimp only [int32MergeStack]; rw [hsp_eq]; apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_2 => ?_
  have hevs_nil : evs = [] := by
    dsimp only [Int32MergeEnv, int32MergeEvents, g] at hevs; rw [hm] at hevs; exact hevs
  subst hevs_nil; simp only [M.stepEvents_nil]; rw [hcur_split]; simp only [sepConj_assoc]
  exact hnext s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2 htr2 hx0_2

private theorem call_bytesMerge_some [LibsignalPlacement] {Inv : Memory → Prop}
    (hkf : KeepsFrozenInv Inv) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {ret ret_pc sp' vecOff curK curNext : BitVec 64} {tagByte : BitVec 8}
    {body remNext fieldBytes outBytes : List (BitVec 8)} {evsOut : List AllocEvent}
    {s0 s1a : State} {Q : State → SepProp → Prop}
    (hpc : s1a.pc = lsmpl.base 7) (hrun : s1a.status = .Running)
    (hsp_eq : s1a.sp = sp') (hsp : s1a.spAligned = true) (hinv : Inv s1a.mem)
    (hlr : s1a.readReg64 Reg.lr = ret_pc)
    (hx0 : (s1a.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 CryptoVerification.LibsignalProtoCodec.WireType.lengthDelimited.toNat)
    (hx1 : s1a.readReg64 .x1 = sp' + vecOff) (hx2 : s1a.readReg64 .x2 = sp' + 440#64)
    (hlt_body : (body ++ remNext).length < 2 ^ 32)
    (hevs_eq : bytesMergeEventsCore .lengthDelimited 0#64 (body ++ remNext) = evsOut)
    (hfit : FitsEvents M lim st evsOut)
    (hm : mergeBytes .lengthDelimited (body ++ remNext) = some (outBytes, remNext))
    (hcur_split : (curK ↦₈ tagByte) ∗
        sliceCursorAfter (sp' + 296#64) (curK + 1#64) (body ++ remNext) remNext =
      (curK ↦ₛ fieldBytes) ∗ (((sp' + 296#64) ↦₆₄ curNext) ∗
        (((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 remNext.length) ∗ (curNext ↦ₛ remNext))))
    (hnext : ∀ (s2 : State) (cap' ptr' : BitVec 64), s2.pc = ret_pc → s2.status = .Running →
      s2.sp = s1a.sp → s2.spAligned = true → Inv s2.mem → CalleeSavedPreserved s1a s2 →
      s2.trace = s1a.trace → s2.readReg64 .x0 = 0#64 →
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ret s2
        ((curK ↦ₛ fieldBytes) ∗ ((sp' + 296#64) ↦₆₄ curNext) ∗
          ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 remNext.length) ∗ (curNext ↦ₛ remNext) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          vecU8At A.repAlloc (sp' + vecOff) cap' ptr' outBytes ∗
          A.pool lim (M.stepEvents evsOut st) s2 ∗ stackAt sp' bytesMergeStack)
        Q (noPanicQp s0)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ret s1a
      ((curK ↦₈ tagByte) ∗ vecU8At A.repAlloc (sp' + vecOff) 0#64 1#64 [] ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        sliceCursorAt (sp' + 296#64) (curK + 1#64) (body ++ remNext) ∗ A.pool lim st s1a ∗
        stackAt sp' bytesMergeStack)
      Q (noPanicQp s0) := by
  let g : BytesMergeGhost :=
    ⟨.lengthDelimited, sp' + vecOff, 0#64, 1#64, [], sp' + 440#64, sp' + 296#64,
      curK + 1#64, body ++ remNext⟩
  have hfit_env : FitsEnv M lim st (BytesMergeEnv g) := fun _ hev => by
    dsimp only [BytesMergeEnv, g] at hev; rw [hevs_eq] at hev; exact hev ▸ hfit
  refine sepWPp_call_noPanic_inv hkf (g, st) hbytes hpc hrun hsp hinv hlr
    (T := vecU8At A.repAlloc (sp' + vecOff) 0#64 1#64 [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) (curK + 1#64) (body ++ remNext) ∗ A.pool lim st s1a ∗
      stackAt sp' bytesMergeStack)
    (φ := bmPreBoundBudget true lim st s1a g)
    (by dsimp only [bytesMergeRawSpec, bytesMergeRawSpecGen, bytesMergeStack, g]; rw [hsp_eq])
    ⟨hx0, hx1, hx2, by dsimp only [g]; omega, bytesMergeCapOk_of_len_lt32 hlt_body, hfit_env⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [bytesMergeRawSpec, bytesMergeRawSpecGen, bmPostVec, g]; rw [hm]; dsimp only
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun cap' => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ptr' =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun evs => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := ⌜s2.trace = s1a.trace⌝ ∗ (⌜BytesMergeEnv g evs⌝ ∗ (⌜s2.readReg64 .x0 = 0#64⌝ ∗
        (⌜BytesMergeCapOk cap' remNext.length⌝ ∗
          (((curK ↦₈ tagByte) ∗ sliceCursorAfter (sp' + 296#64) (curK + 1#64) (body ++ remNext) remNext) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          vecU8At A.repAlloc (sp' + vecOff) cap' ptr' outBytes ∗
          A.pool lim (M.stepEvents evs st) s2 ∗ stackAt sp' bytesMergeStack)))))
      (by dsimp only [bytesMergeStack]; rw [hsp_eq]; apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun htr2 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hevs =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hx0_2 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun _ => ?_
  have hevs_out : evs = evsOut := by dsimp only [BytesMergeEnv, g] at hevs; exact hevs.trans hevs_eq
  subst hevs_out; rw [hcur_split]; simp only [sepConj_assoc]
  exact hnext s2 cap' ptr' hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2 htr2 hx0_2

private abbrev vmTarget {s s' : State} (_ : VmPreserved s s') : State := s'

local macro "loop_regs_cs" hregs:ident hsp2:ident hcs2:ident : term =>
  `(CryptoVerification.E2E.Pqxdh.ResponderWire.PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using ($hregs).sp, by simpa [arm64_norm] using ($hregs).x29,
       by simpa [arm64_norm] using ($hregs).x28, by simpa [arm64_norm] using ($hregs).x27,
       by simpa [arm64_norm] using ($hregs).x26, by simpa [arm64_norm] using ($hregs).x25,
       by simpa [arm64_norm] using ($hregs).x23, by simpa [arm64_norm] using ($hregs).x22,
       by simpa [arm64_norm] using ($hregs).x21, by simpa [arm64_norm] using ($hregs).x20,
       by simpa [arm64_norm] using ($hregs).x19⟩ $hsp2 $hcs2)

local macro "loop_regs_end" hregs2:ident : term =>
  `(⟨by simpa [arm64_norm] using ($hregs2).sp, by simpa [arm64_norm] using ($hregs2).x29,
     by simp [arm64_norm], by simpa [arm64_norm] using ($hregs2).x27,
     by simp [arm64_norm], by simpa [arm64_norm] using ($hregs2).x25,
     by simpa [arm64_norm] using ($hregs2).x23, by simpa [arm64_norm] using ($hregs2).x22,
     by simpa [arm64_norm] using ($hregs2).x21, by simpa [arm64_norm] using ($hregs2).x20,
     by simpa [arm64_norm] using ($hregs2).x19⟩)

set_option hygiene false in
local macro "prove_int32_step" hf_tm:term "," body_tm:term "," tag_byte:term "," cur_prev:ident ","
    rem_prev:ident "," rem_next:ident "," hlt_prev:ident "," hlt_next:ident "," rem_ne:ident ","
    mid_off:term "," ret_off:term "," off_tag:term "," off_val:term "," merge_tm:term ","
    finish_tac:tactic : tactic =>
  `(tactic| (
    have hf := $hf_tm
    let body := $body_tm
    have hrem_eq : $rem_prev x = $tag_byte :: (body ++ $rem_next x) := by
      rw [$rem_prev:term, hf, List.cons_append]
    have hlt_body : (body ++ $rem_next x).length < 2 ^ 32 := by
      have hlt_p := $hlt_prev; rw [hrem_eq, List.length_cons] at hlt_p; omega
    have hsub1 : BitVec.ofNat 64 ($rem_prev x).length - 1#64 =
        BitVec.ofNat 64 (body ++ $rem_next x).length := by rw [hrem_eq, ofNat64_cons_sub_one]
    have hrem_beq : (BitVec.ofNat 64 ($rem_next x).length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr (ofNat64_length_ne_zero ($rem_ne x) $hlt_next)
    have hsp_eq := hregs.sp; have h29 := hregs.x29; have h28 := hregs.x28
    have h26 := hregs.x26; have h25 := hregs.x25; have h23 := hregs.x23
    have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 ($rem_prev x).length := hx2
    have hpts : ($cur_prev x ↦ₛ $rem_prev x) =
        ($cur_prev x ↦₈ $tag_byte) ∗ (($cur_prev x + 1#64) ↦ₛ (body ++ $rem_next x)) := by
      rw [hrem_eq, pointsToBytes_cons]
    clear hrem_eq; unfold sliceCursorAt; rw [hpts]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine sepWPp_seg_inv_vm hkf hinv (mid := (blkPl_111).base + $mid_off) fun _ => ?_
    wp_steps
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro m_real1 hnsp1 hinv1
    have hvm1 := hnsp1.toVmPreserved (by simp [arm64_norm])
    let s1a := vmTarget hvm1
    rw [← A.pool_transport lim st s s1a hvm1]
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + $off_tag) 0#32
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent1
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := (∃∗ w : BitVec 64, (sp' + $off_tag) ↦₆₄ w) ∗ (($cur_prev x ↦₈ $tag_byte) ∗
        (($cur_prev x + 1#64) ↦ₛ (body ++ $rem_next x)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ ($cur_prev x + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ BitVec.ofNat 64 (body ++ $rem_next x).length) ∗ A.pool lim st s1a ∗
        stackAt sp' int32MergeStack))
      (by refine Entails.trans ?_ (sepConj_mono_left hent1); apply entails_of_eq; sep_ac_rfl) ?_
    rw [sepExists_sepConj_left]; refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w_tag => ?_
    refine sepWPp_seg_inv_vm hkf hinv1 (mid := lsmpl.base 8) fun _ => ?_
    wp_steps
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro m_real2 hnsp2 hinv2
    have hvm2 := hnsp2.toVmPreserved (by simp [arm64_norm])
    let s1b := vmTarget hvm2
    rw [← A.pool_transport lim st s1a s1b hvm2]
    have hent2 := pointsTo64_one_entails_pointsTo32_memRegion4 (sp' + $off_tag)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hent2
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := (((sp' + $off_tag) ↦₃₂ 1#32) ∗ memRegion (sp' + $off_val) 4) ∗ (($cur_prev x ↦₈ $tag_byte) ∗
        sliceCursorAt (sp' + 296#64) ($cur_prev x + 1#64) (body ++ $rem_next x) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ A.pool lim st s1b ∗ stackAt sp' int32MergeStack))
      (by unfold sliceCursorAt; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          refine Entails.trans ?_ (sepConj_mono_left hent2); apply entails_of_eq; sep_ac_rfl) ?_
    simp only [sepConj_assoc]
    refine call_int32Merge_some hkf hint32
      (ret_pc := (blkPl_111).base + $ret_off)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp_eq, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hinv2
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by omega) $merge_tm
      (by rw [cons_sliceCursorAfter_split, ← hf]; unfold sliceCursorAt
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hinv3 hcs2 htr2 hx0_2
    have hregs2 : PreKeyLoopRegs sp' x s2 := loop_regs_cs hregs hsp2 hcs2
    have h29_2 := hregs2.x29
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine sepWPp_end_inv_vm hkf hinv3 fun _ => ?_
    wp_steps
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro m_real3 hnsp3 hinv4
    rw [← A.pool_transport lim st s2 _ (hnsp3.toVmPreserved (by simp [arm64_norm]))]; $finish_tac))

set_option hygiene false in
local macro "prove_bytes_step" hf_tm:term "," body_tm:term "," tag_byte:term "," cur_prev:ident ","
    rem_prev:ident "," rem_next:ident "," hlt_prev:ident "," hrem_tac:tactic ","
    off0:term "," off1:term "," off2:term "," evs_id:ident "," merge_tm:term ","
    ret_off:term : tactic =>
  `(tactic| (
    have hf := $hf_tm
    let body := $body_tm
    have hrem_eq : $rem_prev x = $tag_byte :: (body ++ $rem_next x) := by
      rw [$rem_prev:term, hf, List.cons_append]
    have hlt_body : (body ++ $rem_next x).length < 2 ^ 32 := by
      have hlt_p := $hlt_prev; rw [hrem_eq, List.length_cons] at hlt_p; omega
    have hsub1 : BitVec.ofNat 64 ($rem_prev x).length - 1#64 =
        BitVec.ofNat 64 (body ++ $rem_next x).length := by
      rw [hrem_eq, ofNat64_cons_sub_one]
    have _ := ()
    $hrem_tac
    have hsp_eq := hregs.sp; have h29 := hregs.x29; have h28 := hregs.x28
    have h26 := hregs.x26; have h25 := hregs.x25; have h23 := hregs.x23
    have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 ($rem_prev x).length := hx2
    have hpts : ($cur_prev x ↦ₛ $rem_prev x) =
        ($cur_prev x ↦₈ $tag_byte) ∗ (($cur_prev x + 1#64) ↦ₛ (body ++ $rem_next x)) := by
      rw [hrem_eq, pointsToBytes_cons]
    clear hrem_eq
    have hmr16 := memRegion16_split8_8' (sp' + $off1)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmr16
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
          ((sp' + $off1) ↦₆₄ w0) ∗ ((sp' + $off2) ↦₆₄ w1)) ∗
        (sliceCursorAt (sp' + 296#64) ($cur_prev x) ($rem_prev x) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + $off0) ↦₆₄ noneCap) ∗ A.pool lim st s ∗
          stackAt sp' bytesMergeStack))
      (by refine Entails.trans ?_ (sepConj_mono_left hmr16); apply entails_of_eq; sep_ac_rfl) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w1 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w2 => ?_
    unfold sliceCursorAt; rw [hpts]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine sepWPp_seg_inv_vm hkf hinv (mid := lsmpl.base 7) fun _ => ?_
    wp_steps
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro m_real1 hnsp1 hinv1
    have hvm1 := hnsp1.toVmPreserved (by simp [arm64_norm])
    let s1a := vmTarget hvm1
    rw [← A.pool_transport lim st s s1a hvm1]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (P' := ($cur_prev x ↦₈ $tag_byte) ∗ vecU8At A.repAlloc (sp' + $off0) 0#64 1#64 [] ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        sliceCursorAt (sp' + 296#64) ($cur_prev x + 1#64) (body ++ $rem_next x) ∗ A.pool lim st s1a ∗
        stackAt sp' bytesMergeStack)
      (by rw [← pointsTo64_emptyVec_eq_vecU8At A.repAlloc sp' $off0 $off1 $off2]
          unfold sliceCursorAt; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          apply entails_of_eq; sep_ac_rfl) ?_
    refine call_bytesMerge_some hkf hbytes
      (ret_pc := (blkPl_111).base + $ret_off)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp_eq, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hinv1
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      hlt_body (by simp only [body, $evs_id:term, List.append_assoc]) hfit $merge_tm
      (by rw [cons_sliceCursorAfter_split, ← hf]; unfold sliceCursorAt
          simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl) ?_
    intro s2 cap' ptr' hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2 htr2 hx0_2
    have hregs2 : PreKeyLoopRegs sp' x s2 := loop_regs_cs hregs hsp2 hcs2
    have h29_2 := hregs2.x29
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine sepWPp_end_inv_vm hkf hinv2 fun _ => ?_
    wp_steps
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro m_real2 hnsp2 hinv3
    rw [← A.pool_transport lim (M.stepEvents ($evs_id x) st) s2 _
      (hnsp2.toVmPreserved (by simp [arm64_norm]))]
    refine ⟨loop_regs_end hregs2,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hinv3, by simpa [arm64_norm] using htr2.trans htr,
      by simp [arm64_norm], cap', ptr', ?_⟩
    apply entails_of_eq; sep_ac_rfl))

theorem step_field1_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt0 : (psmRem0 x).length < 2 ^ 32) (hlt1 : (psmRem1 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem0 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s
      (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗ A.pool lim st s ∗
        stackAt sp' int32MergeStack)
      (fun s1 P1 =>
        PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem1 x).length ∧
        ∃ opkVal : BitVec 32, (∀ v, x.opkId = some v → opkVal = v) ∧
          (P1 ⊢ (cur0 x ↦ₛ psmField1 x) ∗ sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
            ((sp' + 420#64) ↦₃₂ opkVal) ∗ A.pool lim st s1 ∗ stackAt sp' int32MergeStack))
      (noPanicQp s0) := by
  cases hopk : x.opkId with
  | none =>
    have hf1 : psmField1 x = [] := by simp [psmField1, hopk, CryptoGames.LibsignalSessionApi.Prost.uint32Field]
    have hrem0 : psmRem0 x = psmRem1 x := by simp [psmRem0, hf1]
    have hcur1 : cur1 x = cur0 x := by simp [cur1, hf1]
    rw [memRegion_four (sp' + 420#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w420 => sepWPp_of_sepWP_end_inv hkf hinv ?_
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done hpc hrun fun hinv1 =>
      ⟨hregs, hsp, hinv1, htr, by rw [← hrem0]; exact hx2, w420, fun _ h => by simp at h, ?_⟩
    simp only [opkTag, hopk, hf1, hcur1, hrem0, pointsToBytes_nil, emp_sepConj]
    apply entails_of_eq; sep_ac_rfl
  | some v =>
    prove_int32_step (psmField1_some x v hopk), (encodeVarint (v.zeroExtend 64)), 0x08#8,
      cur0, psmRem0, psmRem1, hlt0, hlt1, psmRem1_ne_nil, 616#64, 632#64, 416#64, 420#64,
      (merge_field1_some x v),
      (refine ⟨loop_regs_end hregs2,
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hinv4, by simpa [arm64_norm] using htr2.trans htr,
         by simp [arm64_norm], v, fun v' hv' => Option.some.inj hv',
         by simp only [opkTag, hopk]; apply entails_of_eq; sep_ac_rfl⟩)

theorem step_field2_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H) (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hfit : FitsEvents M lim st (psmEvs2 x))
    (hlt1 : (psmRem1 x).length < 2 ^ 32) (hlt2 : (psmRem2 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem1 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s
      (sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStack)
      (fun s1 P1 => PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem2 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur1 x ↦ₛ psmField2 x) ∗ sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A.repAlloc (sp' + 336#64) cap' ptr' x.bkBytes ∗
            A.pool lim (M.stepEvents (psmEvs2 x) st) s1 ∗ stackAt sp' bytesMergeStack) (noPanicQp s0) := by
  prove_bytes_step (psmField2_eq x), (encodeVarint 33#64 ++ x.bkBytes), 0x12#8, cur1, psmRem1, psmRem2, hlt1,
    (have hrem_beq : (BitVec.ofNat 64 (psmRem2 x).length == 0#64) = false :=
       beq_eq_false_iff_ne.mpr (ofNat64_length_ne_zero (psmRem2_ne_nil x) hlt2)),
    336#64, 344#64, 352#64, psmEvs2, (merge_field2 x), 432#64

theorem step_field3_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H) (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hfit : FitsEvents M lim st (psmEvs3 x))
    (hlt2 : (psmRem2 x).length < 2 ^ 32) (hlt3 : (psmRem3 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem2 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s
      (sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStack)
      (fun s1 P1 => PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem3 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur2 x ↦ₛ psmField3 x) ∗ sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A.repAlloc (sp' + 360#64) cap' ptr' x.ikBytes ∗
            A.pool lim (M.stepEvents (psmEvs3 x) st) s1 ∗ stackAt sp' bytesMergeStack) (noPanicQp s0) := by
  prove_bytes_step (psmField3_eq x), (encodeVarint 33#64 ++ x.ikBytes), 0x1a#8, cur2, psmRem2, psmRem3, hlt2,
    (have hrem_beq : (BitVec.ofNat 64 (psmRem3 x).length == 0#64) = false :=
       beq_eq_false_iff_ne.mpr (ofNat64_length_ne_zero (psmRem3_ne_nil x) hlt3)),
    360#64, 368#64, 376#64, psmEvs3, (merge_field3 x), 704#64

theorem step_field4_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H) (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64} (hfit : FitsEvents M lim st (psmEvs4 x))
    (hlt_inner : x.inner.length < 2 ^ 32) (hlt3 : (psmRem3 x).length < 2 ^ 32) (hlt4 : (psmRem4 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem3 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s
      (sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStack)
      (fun s1 P1 => PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur3 x ↦ₛ psmField4 x) ∗ sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A.repAlloc (sp' + 384#64) cap' ptr' x.inner ∗
            A.pool lim (M.stepEvents (psmEvs4 x) st) s1 ∗ stackAt sp' bytesMergeStack) (noPanicQp s0) := by
  have hlt_inner64 : x.inner.length < 2 ^ 64 := by omega
  prove_bytes_step (psmField4_eq x hlt_inner64), (encodeVarint (BitVec.ofNat 64 x.inner.length) ++ x.inner), 0x22#8,
    cur3, psmRem3, psmRem4, hlt3,
    (have hrem_beq : (BitVec.ofNat 64 (psmRem4 x).length == 0#64) = false :=
       beq_eq_false_iff_ne.mpr (ofNat64_length_ne_zero (psmRem4_ne_nil x) hlt4)),
    384#64, 392#64, 400#64, psmEvs4, (merge_field4 x hlt_inner64), 544#64

theorem step_field5_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H) (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt4 : (psmRem4 x).length < 2 ^ 32) (hlt5 : (psmRem5 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s
      (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ A.pool lim st s ∗ stackAt sp' int32MergeStack)
      (fun s1 P1 => PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem5 x).length ∧
        (P1 ⊢ (cur4 x ↦ₛ psmField5 x) ∗ sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 408#64) ↦₃₂ 1#32) ∗
          ((sp' + 412#64) ↦₃₂ x.regId) ∗ A.pool lim st s1 ∗ stackAt sp' int32MergeStack)) (noPanicQp s0) := by
  prove_int32_step (psmField5_eq x), (encodeVarint (x.regId.zeroExtend 64)), 0x28#8,
    cur4, psmRem4, psmRem5, hlt4, hlt5, psmRem5_ne_nil, 648#64, 664#64, 408#64, 412#64, (merge_field5 x),
    (refine ⟨loop_regs_end hregs2, by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
       hinv4, by simpa [arm64_norm] using htr2.trans htr, by simp [arm64_norm], by apply entails_of_eq; sep_ac_rfl⟩)

theorem step_field6_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H) (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt5 : (psmRem5 x).length < 2 ^ 32) (hlt6 : (psmRem6 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem5 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s
      (sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ A.pool lim st s ∗ stackAt sp' int32MergeStack)
      (fun s1 P1 => PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem6 x).length ∧
        (P1 ⊢ (cur5 x ↦ₛ psmField6 x) ∗ sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 424#64) ↦₃₂ 1#32) ∗
          ((sp' + 428#64) ↦₃₂ x.spkId) ∗ A.pool lim st s1 ∗ stackAt sp' int32MergeStack)) (noPanicQp s0) := by
  prove_int32_step (psmField6_eq x), (encodeVarint (x.spkId.zeroExtend 64)), 0x30#8,
    cur5, psmRem5, psmRem6, hlt5, hlt6, psmRem6_ne_nil, 472#64, 488#64, 424#64, 428#64, (merge_field6 x),
    (refine ⟨loop_regs_end hregs2, by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
       hinv4, by simpa [arm64_norm] using htr2.trans htr, by simp [arm64_norm], by apply entails_of_eq; sep_ac_rfl⟩)

theorem step_field7_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H) (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hlt6 : (psmRem6 x).length < 2 ^ 32) (hlt7 : (psmRem7 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem6 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s
      (sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ A.pool lim st s ∗ stackAt sp' int32MergeStack)
      (fun s1 P1 => PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem7 x).length ∧
        (P1 ⊢ (cur6 x ↦ₛ psmField7 x) ∗ sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
          ((sp' + 436#64) ↦₃₂ x.kpkId) ∗ A.pool lim st s1 ∗ stackAt sp' int32MergeStack)) (noPanicQp s0) := by
  prove_int32_step (psmField7_eq x), (encodeVarint (x.kpkId.zeroExtend 64)), 0x38#8,
    cur6, psmRem6, psmRem7, hlt6, hlt7, psmRem7_ne_nil, 720#64, 224#64, 432#64, 436#64, (merge_field7 x),
    (refine ⟨loop_regs_end hregs2, by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
       hinv4, by simpa [arm64_norm] using htr2.trans htr, by simp [arm64_norm], by apply entails_of_eq; sep_ac_rfl⟩)

theorem step_field8_inv_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H) (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' : BitVec 64}
    (hfit : FitsEvents M lim st (psmEvs8 x)) (hlt7 : (psmRem7 x).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_111).base + 244#64) (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s) (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (psmRem7 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 1120#64) s
      (sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ A.pool lim st s ∗ stackAt sp' bytesMergeStack)
      (fun s1 P1 => PreKeyLoopRegs sp' x s1 ∧ s1.spAligned = true ∧ Inv s1.mem ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x24 = 0#64 ∧ ∃ cap' ptr' : BitVec 64,
          P1 ⊢ (cur7 x ↦ₛ psmField8 x) ∗ sliceCursorAt (sp' + 296#64) (cur8 x) (psmRem8 x) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ vecU8At A.repAlloc (sp' + 312#64) cap' ptr' x.kyberBytes ∗
            A.pool lim (M.stepEvents (psmEvs8 x) st) s1 ∗ stackAt sp' bytesMergeStack) (noPanicQp s0) := by
  prove_bytes_step (psmField8_eq x), (encodeVarint 1569#64 ++ x.kyberBytes), 0x42#8, cur7, psmRem7, psmRem8, hlt7,
    (have hrem_len : BitVec.ofNat 64 (psmRem8 x).length = 0#64 := rfl),
    312#64, 320#64, 328#64, psmEvs8, (merge_field8 x), 600#64

abbrev step_field1_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field1_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H
abbrev step_field2_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field2_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H
abbrev step_field3_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field3_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H
abbrev step_field4_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field4_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H
abbrev step_field5_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field5_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H
abbrev step_field6_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field6_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H
abbrev step_field7_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field7_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H
abbrev step_field8_placed_wp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} := @step_field8_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H

/-! ## Entry-to-Post-Loop Composition (`+0 → +0x460`) -/

private theorem preKey_fields_1_to_4_inv_wp [LibsignalPlacement] {Inv : Memory → Prop}
    (hkf : KeepsFrozenInv Inv) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s1 : State} {sp' : BitVec 64}
    (hfit14 : FitsEvents M lim st (psmEvs2 x ++ psmEvs3 x ++ psmEvs4 x))
    (hlt0 : (psmRem0 x).length < 2 ^ 32) (hlt1 : (psmRem1 x).length < 2 ^ 32)
    (hlt2 : (psmRem2 x).length < 2 ^ 32) (hlt3 : (psmRem3 x).length < 2 ^ 32)
    (hlt4 : (psmRem4 x).length < 2 ^ 32) (hlt_in : x.inner.length < 2 ^ 32)
    (hpc1 : s1.pc = (blkPl_111).base + 244#64) (hrun1 : s1.status = .Running)
    (hregs1 : PreKeyLoopRegs sp' x s1) (hsp1 : s1.spAligned = true)
    (hinv1 : Inv s1.mem) (htr1 : s1.trace = s0.trace)
    (hx2_1 : s1.readReg64 .x2 = BitVec.ofNat 64 (psmRem0 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 244#64) s1
      (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
        A.pool lim st s1 ∗ stackAt sp' bytesMergeStack)
      (fun s5 P5 =>
        PreKeyLoopRegs sp' x s5 ∧ s5.spAligned = true ∧ Inv s5.mem ∧ s5.trace = s0.trace ∧
        s5.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length ∧
        ∃ (opkVal : BitVec 32) (bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64),
          (∀ v, x.opkId = some v → opkVal = v) ∧
          (P5 ⊢ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
            (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗
            sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
            vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
            vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
            ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
            A.pool lim (M.stepEvents (psmEvs2 x ++ psmEvs3 x ++ psmEvs4 x) st) s5 ∗
            stackAt sp' bytesMergeStack))
      (noPanicQp s0) := by
  rcases (fitsEvents_append M lim (psmEvs2 x ++ psmEvs3 x) (psmEvs4 x) st).mp hfit14 with ⟨hfit23, hfit4⟩
  rcases (fitsEvents_append M lim (psmEvs2 x) (psmEvs3 x) st).mp hfit23 with ⟨hfit2, hfit3⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗ A.pool lim st s1 ∗ stackAt sp' int32MergeStack) ∗
      (((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗ ((sp' + 360#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 368#64) 16 ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
        memRegion (sp' - BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (step_field1_inv_wp hkf hint32 hlt0 hlt1 hpc1 hrun1 hregs1 hsp1 hinv1 htr1 hx2_1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hregs2, hsp2, hinv2, htr2, hx2_2, opkVal, hopkVal, hent2⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent2) ?_; clear hent2
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur1 x) (psmRem1 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗ A.pool lim st s2 ∗ stackAt sp' bytesMergeStack) ∗
      ((cur0 x ↦ₛ psmField1 x) ∗ ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (step_field2_inv_wp hkf hbytes hfit2 hlt1 hlt2 hpc2 hrun2 hregs2 hsp2 hinv2 htr2 hx2_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hregs3, hsp3, hinv3, htr3, hx2_3, bkCap, bkPtr, hent3⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent3) ?_; clear hent3
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur2 x) (psmRem2 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
        A.pool lim (M.stepEvents (psmEvs2 x) st) s3 ∗ stackAt sp' bytesMergeStack) ∗
      ((cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗ ((sp' + 384#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 392#64) 16 ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (step_field3_inv_wp hkf hbytes hfit3 hlt2 hlt3 hpc3 hrun3 hregs3 hsp3 hinv3 htr3 hx2_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hregs4, hsp4, hinv4, htr4, hx2_4, ikCap, ikPtr, hent4⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent4) ?_; clear hent4; rw [← M.stepEvents_append]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur3 x) (psmRem3 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
        A.pool lim (M.stepEvents (psmEvs2 x ++ psmEvs3 x) st) s4 ∗ stackAt sp' bytesMergeStack) ∗
      ((cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗ (cur2 x ↦ₛ psmField3 x) ∗
        vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_frame_noPanic
    (step_field4_inv_wp hkf hbytes hfit4 hlt_in hlt3 hlt4 hpc4 hrun4 hregs4 hsp4 hinv4 htr4 hx2_4)
    fun s5 P5 ⟨hregs5, hsp5, hinv5, htr5, hx2_5, msgCap, msgPtr, hent5⟩ =>
      ⟨hregs5, hsp5, hinv5, htr5, hx2_5, opkVal, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopkVal, ?_⟩
  refine Entails.trans (sepConj_mono_left hent5) ?_; rw [← M.stepEvents_append]
  apply entails_of_eq; sep_ac_rfl

private theorem preKey_fields_5_to_8_inv_wp [LibsignalPlacement] {Inv : Memory → Prop}
    (hkf : KeepsFrozenInv Inv) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st4 : M.σ} {H : LibsignalHooks}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 s5 : State} {sp' : BitVec 64}
    (hfit8 : FitsEvents M lim st4 (psmEvs8 x))
    (hlt4 : (psmRem4 x).length < 2 ^ 32) (hlt5 : (psmRem5 x).length < 2 ^ 32)
    (hlt6 : (psmRem6 x).length < 2 ^ 32) (hlt7 : (psmRem7 x).length < 2 ^ 32)
    (hpc5 : s5.pc = (blkPl_111).base + 244#64) (hrun5 : s5.status = .Running)
    (hregs5 : PreKeyLoopRegs sp' x s5) (hsp5 : s5.spAligned = true)
    (hinv5 : Inv s5.mem) (htr5 : s5.trace = s0.trace)
    (hx2_5 : s5.readReg64 .x2 = BitVec.ofNat 64 (psmRem4 x).length) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 1120#64) s5
      (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        A.pool lim st4 s5 ∗ stackAt sp' bytesMergeStack)
      (fun sf Pf =>
        PreKeyLoopRegs sp' x sf ∧ sf.spAligned = true ∧ Inv sf.mem ∧
        sf.trace = s0.trace ∧ sf.readReg64 .x24 = 0#64 ∧
        ∃ kyberCap kyberPtr : BitVec 64,
          Pf ⊢ (cur4 x ↦ₛ psmField5 x) ∗ (cur5 x ↦ₛ psmField6 x) ∗
            (cur6 x ↦ₛ psmField7 x) ∗ (cur7 x ↦ₛ psmField8 x) ∗
            sliceCursorAt (sp' + 296#64) (cur8 x) (psmRem8 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
            vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
            ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
            ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
            ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
            A.pool lim (M.stepEvents (psmEvs8 x) st4) sf ∗ stackAt sp' bytesMergeStack)
      (noPanicQp s0) := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗ A.pool lim st4 s5 ∗ stackAt sp' int32MergeStack) ∗
      (((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        memRegion (sp' - BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (step_field5_inv_wp hkf hint32 hlt4 hlt5 hpc5 hrun5 hregs5 hsp5 hinv5 htr5 hx2_5) ?_
  intro s6 P6 hpc6 hrun6 ⟨hregs6, hsp6, hinv6, htr6, hx2_6, hent6⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent6) ?_; clear hent6
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur5 x) (psmRem5 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗ A.pool lim st4 s6 ∗ stackAt sp' int32MergeStack) ∗
      ((cur4 x ↦ₛ psmField5 x) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        memRegion (sp' - BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (step_field6_inv_wp hkf hint32 hlt5 hlt6 hpc6 hrun6 hregs6 hsp6 hinv6 htr6 hx2_6) ?_
  intro s7 P7 hpc7 hrun7 ⟨hregs7, hsp7, hinv7, htr7, hx2_7, hent7⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent7) ?_; clear hent7
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur6 x) (psmRem6 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ A.pool lim st4 s7 ∗ stackAt sp' int32MergeStack) ∗
      ((cur4 x ↦ₛ psmField5 x) ∗ (cur5 x ↦ₛ psmField6 x) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗
        memRegion (sp' + 320#64) 16 ∗ ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        memRegion (sp' - BitVec.ofNat 64 bytesMergeStack) (bytesMergeStack - int32MergeStack)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (step_field7_inv_wp hkf hint32 hlt6 hlt7 hpc7 hrun7 hregs7 hsp7 hinv7 htr7 hx2_7) ?_
  intro s8 P8 hpc8 hrun8 ⟨hregs8, hsp8, hinv8, htr8, hx2_8, hent8⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent8) ?_; clear hent8
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur7 x) (psmRem7 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗ A.pool lim st4 s8 ∗ stackAt sp' bytesMergeStack) ∗
      ((cur4 x ↦ₛ psmField5 x) ∗ (cur5 x ↦ₛ psmField6 x) ∗ (cur6 x ↦ₛ psmField7 x) ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId)))
    (by apply entails_of_eq; rw [stackAt_bytesMerge_split_int32 sp']; sep_ac_rfl) ?_
  refine sepWPp_frame_noPanic
    (step_field8_inv_wp hkf hbytes hfit8 hlt7 hpc8 hrun8 hregs8 hsp8 hinv8 htr8 hx2_8)
    fun sf Pf ⟨hregsf, hspf, hinvf, htrf, hx24f, kyberCap, kyberPtr, hentf⟩ =>
      ⟨hregsf, hspf, hinvf, htrf, hx24f, kyberCap, kyberPtr, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  apply entails_of_eq; sep_ac_rfl

theorem preKey_entry_to_f90_inv_wp [LibsignalPlacement] {Inv : Memory → Prop}
    (hkf : KeepsFrozenInv Inv) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hint32 : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 8) (withLoopInv Inv (int32MergeSpec A lim)))
    (hbytes : subroutine_ok ((blkPC_111).rebase (blkPl_111).base H)
      (lsmpl.base 7) (withLoopInv Inv (bytesMergeRawSpec A lim)))
    {x : PreKeyTryFromArgs} {s0 : State} {sp' : BitVec 64}
    (hfit : FitsEvents M lim st (preKeyLoopEvents x))
    (hsp' : sp' = s0.sp - 608#64) (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hinv : Inv s0.mem) (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length) (hx8 : s0.readReg64 .x8 = x.sret) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp ((blkPC_111).rebase (blkPl_111).base H) ((blkPl_111).base + 1120#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96 ∗
        A.pool lim st s0 ∗ stackAt sp' bytesMergeStack)
      (fun sf Pf =>
        PreKeyLoopRegs sp' x sf ∧ sf.spAligned = true ∧ Inv sf.mem ∧
        sf.trace = s0.trace ∧ sf.readReg64 .x24 = 0#64 ∧
        ∃ (opkVal : BitVec 32) (kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64),
          (∀ v, x.opkId = some v → opkVal = v) ∧
          (Pf ⊢ (x.ptr ↦ₛ x.bytes) ∗ ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
            vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
            vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
            vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
            vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
            ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
            ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
            ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
            ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ preKeyCalleeSavedAt sp' s0 ∗
            A.pool lim (M.stepEvents (preKeyLoopEvents x) st) sf ∗ stackAt sp' bytesMergeStack))
      Qp := by
  refine sepWPp_weaken_qp (s0 := s0) ?_
  have hloop_eq : preKeyLoopEvents x = (psmEvs2 x ++ psmEvs3 x ++ psmEvs4 x) ++ psmEvs8 x := by
    simp only [preKeyLoopEvents, psmEvs2, psmEvs3, psmEvs4, psmEvs8, List.append_assoc]
  have hfit' : FitsEvents M lim st ((psmEvs2 x ++ psmEvs3 x ++ psmEvs4 x) ++ psmEvs8 x) :=
    hloop_eq ▸ hfit
  rcases (fitsEvents_append M lim (psmEvs2 x ++ psmEvs3 x ++ psmEvs4 x) (psmEvs8 x) st).mp hfit'
    with ⟨hfit14, hfit8⟩
  rcases psmRem_lengths_lt x hlt with ⟨_, hlt0, hlt1, hlt2, hlt3, hlt4, hlt5, hlt6, hlt7, hlt_in⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96) ∗
      (A.pool lim st s0 ∗ stackAt sp' bytesMergeStack))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (hsp' ▸ prologue_to_c24_inv_wp hkf hlt hpc hrun hsp hinv hx0 hx1 hx8) ?_
  intro s1 P1 hpc1 hrun1 ⟨hregs1, hsp1, hinv1, hvm1, htr1, hx2_1, hent1⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
  rw [← A.pool_transport lim st s0 s1 hvm1]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur0 x) (psmRem0 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
        A.pool lim st s1 ∗ stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (preKey_fields_1_to_4_inv_wp hkf hint32 hbytes hfit14 hlt0 hlt1 hlt2 hlt3 hlt4 hlt_in
      hpc1 hrun1 hregs1 hsp1 hinv1 htr1 hx2_1) ?_
  intro s5 P5 hpc5 hrun5
    ⟨hregs5, hsp5, hinv5, htr5, hx2_5, opkVal, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopkVal, hent5⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hent5) ?_; clear hent5
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (cur4 x) (psmRem4 x) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ∗
        A.pool lim (M.stepEvents (psmEvs2 x ++ psmEvs3 x ++ psmEvs4 x) st) s5 ∗
        stackAt sp' bytesMergeStack) ∗
      ((x.ptr ↦₈ 0x44#8) ∗ (cur0 x ↦ₛ psmField1 x) ∗ (cur1 x ↦ₛ psmField2 x) ∗
        (cur2 x ↦ₛ psmField3 x) ∗ (cur3 x ↦ₛ psmField4 x) ∗
        vecU8At A.repAlloc (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A.repAlloc (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A.repAlloc (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_frame_noPanic
    (preKey_fields_5_to_8_inv_wp hkf hint32 hbytes hfit8 hlt4 hlt5 hlt6 hlt7
      hpc5 hrun5 hregs5 hsp5 hinv5 htr5 hx2_5)
    fun sf Pf ⟨hregsf, hspf, hinvf, htrf, hx24f, kyberCap, kyberPtr, hentf⟩ =>
      ⟨hregsf, hspf, hinvf, htrf, hx24f,
        opkVal, kyberCap, kyberPtr, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopkVal, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  rw [← M.stepEvents_append, ← hloop_eq]
  have hcur8 : sliceCursorAt (sp' + 296#64) (cur8 x) (psmRem8 x) =
      ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) := by
    unfold sliceCursorAt psmRem8
    simp only [List.length_nil, pointsToBytes_nil, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  rw [hcur8, ← pointsToBytes_psm_reassemble x]
  apply entails_of_eq; sep_ac_rfl

abbrev preKey_entry_to_f90_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop} :=
  @preKey_entry_to_f90_inv_wp _ _ keepsFrozenInv_codeLoaded M A lim st H Qp

abbrev preKey_entry_to_f90_cro_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop} :=
  @preKey_entry_to_f90_inv_wp _ _ keepsFrozenInv_codeRoLoaded M A lim st H Qp

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromLoopBudget
