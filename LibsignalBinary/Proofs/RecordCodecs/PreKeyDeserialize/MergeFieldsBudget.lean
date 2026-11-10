/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFields
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Post
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `PreKeyRecord::deserialize` Field Merge Branches

`RustCliAllocBudget`-threaded relocatable CPS proofs for field merges (`id`, `public_key`,
`private_key`, `skip_field`) and error-cleanup helpers on Block `65`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFieldsBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
  hiding rustDeallocExternSpecWithStack decodeErrorFromSpecWithStack
    decodeErrorPushExternSpecWithStack decodeVarintSlowSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost
  hiding dropDecodeErrorSpecGen dropDecodeErrorSpecX decodeVarintSliceSpecGen decodeVarintSliceSpecX memRegion_split
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Wire renaming SepWP.done -> sepWPDoneWire
open scoped CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (preKeyResultAt sepWPp_of_sepWP_lscro)
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers hiding pkEpilogueMem
open scoped CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
   rustDeallocEvents rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DropDecodeErrorEnv dropDecodeErrorSpecGen dropDecodeErrorSpecX)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PortDepsPlaced OptByteFreeEnv RecordCodecErrCleanupEnv PkSubEnv
   noPanicQp sepWPp_mono_post sepWPp_of_sepWP_end_noPanic_lscro sepWPp_call_noPanic_lscro)
open LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
  (pk_dropDecodeError_placed_ok pk_dealloc_placed_ok pkEpilogueMem pkEpiloguePostPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cleanup_err_210_core_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (528)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 56#64) 56 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A.repAlloc err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PkEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 160 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
          preKeyResultAt A.repAlloc x19 out ∗ (ptr ↦ₛ bs) ∗
          (∃∗ evsD : List AllocEvent, ⌜DropDecodeErrorEnv evsD⌝ ∗
            A.pool lim (M.stepEvents evsD st) sf) ∗
          stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  have hstack := stackAt_sub_split sp' dropDecodeErrorStackX (skipFieldStackX 100)
  refine SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkMemRegion56_err_unpack x19)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w0 => SepWPp.exists_pre fun w1 =>
    SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w3 =>
    SepWPp.exists_pre fun r0 => SepWPp.exists_pre fun r1 =>
    SepWPp.exists_pre fun r5 => SepWPp.exists_pre fun r6 => ?_
  have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 4) ?_
  wp_steps
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro (err, st) (pk_dropDecodeError_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (532)) (by simpa [arm64_norm] using htr)
    (T := decodeErrorAt A.repAlloc err ∗ A.pool lim st s ∗ stackAt sp' dropDecodeErrorStackX)
    (φ := err = err ∧ LsRetAddr624 ((blkPl_65).base + bv% (532)))
    (by simp [dropDecodeErrorSpecX, dropDecodeErrorSpecGen, hsp_eq, h0, arm64_norm])
    ⟨rfl, lsRetAddr624_blockPlacement_base_add 65 (bv% (532)) (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [dropDecodeErrorSpecX, dropDecodeErrorSpecGen]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun evsD => ?_
  refine SepWPp.pure_pre fun htr2 => ?_
  refine SepWPp.pure_pre fun hevsD => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x19 := by simpa [hx19, arm64_norm] using hcs2.1
  have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
  have hsaved2 : PkSavedRegs s0 s2 :=
    ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
     by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine sepWPp_of_sepWP_end_noPanic_lscro hcrl2 ?_
  wp_steps_sync_pool ((blkPl_65).base + bv% (548))
  refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcrl3, by simp [htr2, htr, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x24, by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26, by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.sepExists_right evsD ?_
  rw [pure_true_emp hevsD, emp_sepConj]
  refine Entails.trans ?_
    (sepConj_mono (pkMemRegion160_pack sp')
      (sepConj_mono_right (sepConj_mono_left (pkSpeInvalidProto56_intro A.repAlloc x19 r0 r1 herr))))
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left (pkMemRegion40_pack sp' r0 r1 r5 r6)))
  apply entails_of_eq; rw [hstack, hsp_eq]
  simp only [errTag, skipFieldStackX, dropDecodeErrorStackX, extHookStack, arm64_norm]; sep_ac_rfl

theorem cleanup_err_210_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {fuel maxLen : Nat}
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (528)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 56#64) 56 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A.repAlloc err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  refine sepWPp_mono_post
    (cleanup_err_210_core_wp d herr hst hpc hrun hx0 hx19 hx22)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf ?_⟩
  unfold pkEpilogueMem
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left ?_))))
  refine Entails.sepExists_elim fun evsD => Entails.pure_left fun hd => ?_
  have hc : PkSubEnv fuel maxLen ([] ++ ([] ++ evsD)) :=
    PkSubEnv.of_errCleanup (RecordCodecErrCleanupEnv.of_two_drop .nil .nil hd)
  simp only [List.nil_append] at hc
  refine Entails.sepExists_right evsD ?_
  rw [pure_true_emp hc, emp_sepConj]
  exact Entails.refl _

private theorem cleanup_priv_1f4_core_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {s0 s : State}
    {sp' x19 ptr err privCap privPtr : BitVec 64}
    {privBs bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (500)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2)
    (hx20 : s.readReg64 .x20 = privCap) (hx21 : s.readReg64 .x21 = privPtr) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (vecU8Buf A.repAlloc privCap privPtr privBs ∗ memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A.repAlloc err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => PkEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ memRegion sp' 160 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
          preKeyResultAt A.repAlloc x19 out ∗ (ptr ↦ₛ bs) ∗
          (∃∗ e2 : List AllocEvent, ∃∗ evsD : List AllocEvent,
            ⌜OptByteFreeEnv e2 ∧ DropDecodeErrorEnv evsD⌝ ∗
            A.pool lim (M.stepEvents (e2 ++ evsD) st) sf) ∗
          stackAt sp' (skipFieldStackX 100)))
      (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  by_cases hcap : privCap = 0#64
  · subst hcap
    refine SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_zero_elim A.repAlloc privPtr privBs)) ?_
    rw [emp_sepConj]; have h20 : s.readReg64 (Reg.gpr 20#5) = 0#64 := hx20
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (528)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine sepWPp_mono_post
      (SepWPp.mono_pre
        (by simp only [RustCliAllocBudget.pool_setPC, arm64_norm]; exact Entails.refl _)
        (cleanup_err_210_core_wp d (st := st) (x19 := x19) (ptr := ptr) (bs := bs) (err := err) herr
          ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
           hcrl1, by simp [htr, arm64_norm],
           ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
            by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
            by simpa [arm64_norm] using hsaved.x28⟩⟩
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx22, arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left ?_))))
    refine Entails.sepExists_elim fun evsD => Entails.pure_left fun hd => ?_
    refine Entails.sepExists_right [] (Entails.sepExists_right evsD ?_)
    rw [List.nil_append, pure_true_emp ⟨OptByteFreeEnv.nil, hd⟩, emp_sepConj]
    exact Entails.refl _
  · refine SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc privCap privPtr privBs hcap)) ?_
    simp only [sepConj_assoc]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
    have h20 : s.readReg64 (Reg.gpr 20#5) = privCap := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = privPtr := hx21
    have hbeq : (privCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (privPtr, privCap.toNat, 1, st) (pk_dealloc_placed_ok d)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (524)) (by simpa [arm64_norm] using htr)
      (T := A.pool lim st s ∗ A.live privPtr privCap.toNat 1 ∗ memRegion privPtr privCap.toNat ∗ stackAt sp' extHookStack)
      (φ := privPtr = privPtr ∧ privCap.toNat = privCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        RustLayoutOk privCap.toNat 1 ∧ LsRetAddr624 ((blkPl_65).base + bv% (524)))
      (by simp [rustDeallocExternSpecWithStack, rustCliDeallocBudgetExternSpecWithStack, hsp_eq, arm64_norm])
      ⟨rfl, rfl, rfl, ⟨layoutOk_align1 hpos hlt, by decide⟩,
        lsRetAddr624_blockPlacement_base_add 65 (bv% (524)) (by decide) (by decide)⟩
      (by rw [RustCliAllocBudget.repAlloc_live, hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hx19, arm64_norm] using hcs2.1
    have hx22_2 : s2.readReg64 .x22 = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = err := by simpa [h0, arm64_norm] using hcs2.2.2.2.2.1
    have hsaved2 : PkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (528)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (SepWPp.mono_pre
        (by simp only [hsp_eq, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
            apply entails_of_eq; rw [hstack]; sep_ac_rfl)
        (cleanup_err_210_core_wp d (st := M.stepEvents (rustDeallocEvents privCap.toNat 1) st)
          (x19 := x19) (ptr := ptr) (bs := bs) (err := err) herr
          ⟨by simp [hsp2_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
           hcrl3, by simp [htr2, htr, arm64_norm],
           ⟨by simpa [arm64_norm] using hsaved2.x24, by simpa [arm64_norm] using hsaved2.x25,
            by simpa [arm64_norm] using hsaved2.x26, by simpa [arm64_norm] using hsaved2.x27,
            by simpa [arm64_norm] using hsaved2.x28⟩⟩
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          (by simp [arm64_norm]) (by simp [hx19_2, arm64_norm]) (by simp [hx22_2, arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf ?_⟩
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left ?_))))
    refine Entails.sepExists_elim fun evsD => Entails.pure_left fun hd => ?_
    rw [← M.stepEvents_append]
    refine Entails.sepExists_right (rustDeallocEvents privCap.toNat 1) (Entails.sepExists_right evsD ?_)
    rw [pure_true_emp ⟨OptByteFreeEnv.dealloc hpos hlt, hd⟩, emp_sepConj]
    exact Entails.refl _

theorem cleanup_priv_1f4_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {fuel maxLen : Nat}
    {s0 s : State} {sp' x19 ptr err privCap privPtr : BitVec 64}
    {privBs bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (500)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2)
    (hx20 : s.readReg64 .x20 = privCap) (hx21 : s.readReg64 .x21 = privPtr) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (vecU8Buf A.repAlloc privCap privPtr privBs ∗ memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A.repAlloc err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  refine sepWPp_mono_post
    (cleanup_priv_1f4_core_wp d herr hst hpc hrun hx0 hx19 hx22 hx20 hx21)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf ?_⟩
  unfold pkEpilogueMem
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left ?_))))
  refine Entails.sepExists_elim fun e2 => Entails.sepExists_elim fun evsD =>
    Entails.pure_left fun ⟨he2, hd⟩ => ?_
  have hc : PkSubEnv fuel maxLen ([] ++ (e2 ++ evsD)) :=
    PkSubEnv.of_errCleanup (RecordCodecErrCleanupEnv.of_two_drop .nil he2 hd)
  rw [List.nil_append] at hc
  refine Entails.sepExists_right (e2 ++ evsD) ?_
  rw [pure_true_emp hc, emp_sepConj]
  exact Entails.refl _

theorem post_err_1d0_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) {st : M.σ} {fuel maxLen : Nat}
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (464)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2) :
    SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (preKeyStructOf A.repAlloc (sp' + 56#64) mErr ∗ memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A.repAlloc err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr bs out) (noPanicQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  unfold preKeyStructOf; simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun ⟨⟨pubCap, pubPtr⟩, ⟨privCap, privPtr⟩⟩ => ?_
  rw [preKeyStructAt_split_pub A.repAlloc ⟨⟨pubCap, pubPtr⟩, ⟨privCap, privPtr⟩⟩ sp' mErr,
    vecU8At_eq_header_buf A.repAlloc (sp' + 56#64) pubCap pubPtr mErr.publicKey,
    vecU8At_eq_header_buf A.repAlloc (sp' + 80#64) privCap privPtr mErr.privateKey]
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun pad32 => ?_
  have h56_pack := pkStruct56_pack sp' pubCap pubPtr (BitVec.ofNat 64 mErr.publicKey.length)
    privCap privPtr (BitVec.ofNat 64 mErr.privateKey.length) mErr.id pad32
  by_cases hcap : pubCap = 0#64
  · subst hcap
    refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_left (vecU8Buf_zero_elim A.repAlloc pubPtr mErr.publicKey))) ?_
    simp only [emp_sepConj]
    refine SepWPp.mono_pre
      (P' := ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ pubPtr) ∗
        ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        ((sp' + 80#64) ↦₆₄ privCap) ∗ ((sp' + 88#64) ↦₆₄ privPtr) ∗
        ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        vecU8Buf A.repAlloc privCap privPtr mErr.privateKey ∗ ((sp' + 104#64) ↦₃₂ mErr.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) ∗
        memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ decodeErrorAt A.repAlloc err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (by dsimp only [vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (500)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine SepWPp.mono_pre ?_
      (cleanup_priv_1f4_placed_wp d (st := st) (x19 := x19) (ptr := ptr) (bs := bs)
        (err := err) (privCap := privCap) (privPtr := privPtr) (privBs := mErr.privateKey) herr
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
          by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
          by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx22, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]))
    dsimp only [vecHeader] at h56_pack; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h56_pack
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_setPC, arm64_norm]
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56_pack))))
    apply entails_of_eq; sep_ac_rfl
  · refine SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A.repAlloc pubCap pubPtr mErr.publicKey hcap))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have hbeq : (pubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
    refine SepWPp.mono_pre
      (P' := ((sp' + 56#64) ↦₆₄ pubCap) ∗ ((sp' + 64#64) ↦₆₄ pubPtr) ∗
        ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗
        ((sp' + 80#64) ↦₆₄ privCap) ∗ ((sp' + 88#64) ↦₆₄ privPtr) ∗
        ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        vecU8Buf A.repAlloc privCap privPtr mErr.privateKey ∗ ((sp' + 104#64) ↦₃₂ mErr.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) ∗
        memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ decodeErrorAt A.repAlloc err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100))
      (by dsimp only [RustCliAllocBudget.repAlloc, vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (pubPtr, pubCap.toNat, 1, st) (pk_dealloc_placed_ok d)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (496)) (by simpa [arm64_norm] using htr)
      (T := A.pool lim st s ∗ A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗ stackAt sp' extHookStack)
      (φ := pubPtr = pubPtr ∧ pubCap.toNat = pubCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧
        RustLayoutOk pubCap.toNat 1 ∧ LsRetAddr624 ((blkPl_65).base + bv% (496)))
      (by simp [rustDeallocExternSpecWithStack, rustCliDeallocBudgetExternSpecWithStack, hsp_eq, arm64_norm])
      ⟨rfl, rfl, rfl, ⟨layoutOk_align1 hpos hlt, by decide⟩,
        lsRetAddr624_blockPlacement_base_add 65 (bv% (496)) (by decide) (by decide)⟩
      (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = privCap := by simpa [hsp_eq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = privPtr := by simpa [hsp_eq, arm64_norm] using hcs2.2.2.1
    have hx22_2 : s2.readReg64 .x22 = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = err := by simpa [h0, arm64_norm] using hcs2.2.2.2.2.1
    have hsaved2 : PkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (500)) ?_
    wp_steps
    refine sepWPDoneWire (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine sepWPp_mono_post
      (SepWPp.mono_pre
        (by rw [hstack]; try simp only [hsp_eq, RustCliAllocBudget.pool_writeReg64,
              RustCliAllocBudget.pool_setPC, arm64_norm]
            dsimp only [vecHeader] at h56_pack
            simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h56_pack
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56_pack))))
            apply entails_of_eq; sep_ac_rfl)
        (cleanup_priv_1f4_core_wp d (st := M.stepEvents (rustDeallocEvents pubCap.toNat 1) st)
          (x19 := x19) (ptr := ptr) (bs := bs) (err := err)
          (privCap := privCap) (privPtr := privPtr) (privBs := mErr.privateKey) herr
          ⟨by simp [hsp2_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
           hcrl3, by simp [htr2, htr, arm64_norm],
           ⟨by simpa [arm64_norm] using hsaved2.x24, by simpa [arm64_norm] using hsaved2.x25,
            by simpa [arm64_norm] using hsaved2.x26, by simpa [arm64_norm] using hsaved2.x27,
            by simpa [arm64_norm] using hsaved2.x28⟩⟩
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          (by simp [arm64_norm]) (by simp [hx19_2, arm64_norm]) (by simp [hx22_2, arm64_norm])
          (by simp [hx20_2, arm64_norm]) (by simp [hx21_2, arm64_norm])))
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, Entails.trans hentf ?_⟩
    unfold pkEpilogueMem
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left ?_))))
    refine Entails.sepExists_elim fun e2 => Entails.sepExists_elim fun evsD =>
      Entails.pure_left fun ⟨he2, hd⟩ => ?_
    rw [← M.stepEvents_append]
    have hc : PkSubEnv fuel maxLen (rustDeallocEvents pubCap.toNat 1 ++ (e2 ++ evsD)) :=
      PkSubEnv.of_errCleanup
        (RecordCodecErrCleanupEnv.of_two_drop (OptByteFreeEnv.dealloc hpos hlt) he2 hd)
    refine Entails.sepExists_right (rustDeallocEvents pubCap.toNat 1 ++ (e2 ++ evsD)) ?_
    rw [pure_true_emp hc, emp_sepConj]
    exact Entails.refl _

end LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFieldsBudget
