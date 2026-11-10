/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.SetState4KBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Budget-Threaded Stage P3 Substage P3.5 (`Ok` and Duplicate Error)

Proves `RustCliAllocBudget M` / `VmPreserved` Substage P3.5 theorems on
`tripleRatchetProgAtExt b ext`, composing the post-`tryDecrypt` basic blocks with
`set_session_state_ok_ext_4k` and `drop_session_structure3_ok_ext_4k` for the `Ok pt` path
(`+0x1cd8 → +0x34dc`) and duplicate-message error exit (`+0x1cd8 → s0.readReg64 .x30`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters hiding
  dropChainSpec dropProtoChainSpec dropVecMessageKeySpec dropVecChainSpec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec setSessionStateSpec growOneSpeSpec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustAllocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget (
  AllocContractsMem4KBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtBudget (
  dropSessionStructureLocal2SpecBase drop_session_structure3_ok_mem4K_ext
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.SetState4KBudget (
  p3_err_dup_ext_vm_wp p3_err_tail_b_ext_vm_wp p3_err_tail_dup_a_ext_vm_wp
  p3_seg7a_x24_ext_4k_vm_wp p3_seg7b_x24_ext_vm_wp set_session_state_ok_ext_4k
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv growOneSpeSpec setSessionStateSpec
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWP_swap_vm {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {P_post : SepProp} {Q_regs : State → Prop}
    (h : SepWP prog target_pc s P (fun sm Pf => VmPreserved s sm ∧ (Pf ⊢ P_post) ∧ Q_regs sm)) :
    SepWP prog target_pc s P (fun sm Pf => (Pf ⊢ P_post) ∧ VmPreserved s sm ∧ Q_regs sm) :=
  SepWP.mono h (fun _ _ _ _ ⟨hvm, hent, hrest⟩ => ⟨hent, hvm, hrest⟩)

private theorem ret_sepWPp_frame_evs {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : List AllocEvent → State → SepProp}
    {Q_regs : List AllocEvent → State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage
      (fun sf P_m => ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧ (P_m ⊢ P_stage_post evs sf) ∧ Q_regs evs sf)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hret : ∀ (sf : State) (P_m : SepProp) (evs : List AllocEvent),
      sf.pc = ret → sf.status = .Running → FreeOnlyEvs evs →
      (P_m ∗ F ⊢ P_stage_post evs sf ∗ F) → Q_regs evs sf → Q sf (P_m ∗ F)) :
    SepWPp prog ret s P Q (PanicOomProp s0) :=
  P3P4.SepWPp.bind_sepWPp_frame_raw hstage hP
    fun sf P_m hpc hrun ⟨evs, hevs, hent, hregs⟩ =>
      SepWPp.done hpc hrun (hret sf P_m evs hpc hrun hevs (sepConj_mono_left hent) hregs)

theorem call_frame_inImage_nopanic {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.call_frame_inImage_nopanic
    hF hsym hcall hpc hrun hsp hlr hspec hφ hP hpan_false hexit_false hnext hoom_false

theorem growOneSpe_pre_zero_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v ptr : BitVec 64)
    (hx0 : s.readReg64 .x0 = v) (hptr : ptr ≠ 0)
    (hfits : FitsEnv M lim st (GrowOneSpeEnv 0#64)) :
    (growOneSpeSpec M A lim).pre ((v, 0#64, ptr, []), st) s =
      (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ A.pool lim st s ∗ stackAt s.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have hp : (s.readReg64 .x0 = v ∧ ([] : List (BitVec 8)).length = (0#64 : BitVec 64).toNat * 48 ∧
      ptr ≠ 0 ∧ max (2 * (0#64 : BitVec 64).toNat) 4 * 48 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneSpeEnv 0#64)) = True :=
    propext ⟨fun _ => trivial, fun _ => ⟨hx0, rfl, hptr, by decide, hfits⟩⟩
  have hif : ((0#64 : BitVec 64) = 0) = True := propext ⟨fun _ => trivial, fun _ => rfl⟩
  simp only [hp, pure_true, hif, ite_true, emp_sepConj, sepConj_emp, sepConj_assoc]

theorem growOneSpe_post_zero_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 sf : State) (v ptr : BitVec 64) :
    (growOneSpeSpec M A lim).post ((v, 0#64, ptr, []), st) s0 sf =
      ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗ (v ↦₆₄ 4#64) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' 192 8 ∗ memRegion p' 192) ∗
      A.pool lim (M.stepEvents (rustAllocEvents 192 8) st) sf ∗
      stackAt s0.sp growOneSpeStack := by
  dsimp only [growOneSpeSpec]
  have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.sub_zero, show max 0 4 = 4 from rfl,
    show 4 * 48 = 192 from rfl, show ([] : List (BitVec 8)).length = 0 from rfl,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, pointsToBytes_nil,
    emp_sepConj, sepConj_emp]
  apply Entails.antisymm
  · apply Entails.sepExists_elim
    intro evs
    apply Entails.pure_left
    rintro ⟨htr, ⟨_, rfl⟩ | ⟨hne, _⟩⟩
    · exact Entails.pure_right htr (Entails.refl _)
    · exact False.elim (hne rfl)
  · apply Entails.pure_left
    intro htr
    refine Entails.sepExists_right (rustAllocEvents 192 8) ?_
    exact Entails.pure_right ⟨htr, Or.inl ⟨rfl, rfl⟩⟩ (Entails.refl _)

local notation "dropSs3OffBv_pub" =>
  bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")

local notation "whitespaceLogOffBv_pub" =>
  bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)

theorem drop_session_structure3_ok_ext_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2SpecBase M A lim) :=
  drop_session_structure3_ok_mem4K_ext hA

/-! ## Common Error Epilogue (`stageP3_err_tail_common_ext_ok`) -/

set_option maxHeartbeats 1200000 in
theorem stageP3_err_tail_common_ext_4k_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4KBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr outPtr errTag prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + dropSs3OffBv_pub)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) := by
  have hdropSs3 := drop_session_structure3_ok_ext_4k (b := b) (ext := ext) hA
  have hpc_drop : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := ((⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost), st))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ A.pool lim st s ∗
          stackAt s.sp dropSessionStructure2Stack)
    hF hsym hdropSs3 hpc_drop hrun hsp_al hx30
    (by dsimp only [dropSessionStructureLocal2SpecBase, dropSessionStructure2Stack])
    hx0 (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hF1 hsym1 => ?_)
  dsimp only [dropSessionStructureLocal2SpecBase]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htr1_s, hevs⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hstep2_raw := p3_err_tail_b_ext_vm_wp b ext s1 coroPtr outPtr errTag prevStatesPtr
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
    hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
  have hstep2 := sepWP_swap_vm hstep2_raw
  rw [hsp1_s] at hstep2
  refine P3P4.SepWPp.bind_sepWP_frame hF1 hsym1 hstep2 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf ⟨hvm_f, hregsf⟩ => ?_
  rcases hregsf with ⟨hspf_s, htrf_1, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregs_f⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evs st) hvm_f).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp370_36_err_fold s.sp
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      w3 w4 (w2.extractLsb' 32 32))
    (by sep_focus) ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm)
    (by sep_focus) ?_
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At
    rw [BitVec.add_zero]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
  have hcc : ClosureCalleeSaved s0 sf :=
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩
  refine SepWPp.done hpcf hrunf ⟨evs, hevs, Entails.of_eq (eq_of_sep_emp (by sep_focus)),
    hspf_s, htrf_1.trans (htr1_s.trans htr), hcc, hFf, hsymf, hvregs_f.trans hvregs_cs1⟩

theorem stageP3_err_tail_common_ext_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr outPtr errTag prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + dropSs3OffBv_pub)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) :=
  stageP3_err_tail_common_ext_4k_ok img b ext (AllocContractsMem4KBudget.of_AllocContracts hA)
    st s0 s coroPtr outPtr errTag prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hF hsym hpc hrun hsp_align htr hx0 hx19 hx22 hx25 hx26 hx28 hx30

/-! ## Duplicate-Error Tail (`stageP3_err_tail_dup_ext_ok`) -/

set_option maxHeartbeats 1200000 in
theorem stageP3_err_tail_dup_ext_4k_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4KBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
            ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus)
    ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hstep1_raw := p3_err_tail_dup_a_ext_vm_wp b ext s coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c
    (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc hrun hsp_align hx19 hx24 hx25 hx28
  have hstep1 := sepWP_swap_vm hstep1_raw
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hvm1, hregs1⟩ => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _,
    hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved (lim := lim) (st := st) hvm1).symm)
    (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A.repAlloc recG recSt ⊢
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A.repAlloc (coroPtr + 0xf8#64) recG recSt hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000017#64 w0 w1 w2 w3 w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hsp1_s]
  have hcommon_raw := stageP3_err_tail_common_ext_4k_ok img b ext hA
    st s0 s1 coroPtr outPtr 0x8000000000000017#64 prevStatesPtr
    w0 w1 w2 w3 w4 b_2c0 recG recSt
    hF1 hsym1 hpc1 hrun1 hsp1_align (htr1_s.trans htr)
    hx0_1 hx19_1 hx22_1 hx25_1' (hx26_1.trans hx26) hx28_1 hx30_1
  rw [hsp1_s] at hcommon_raw
  refine ret_sepWPp_frame_evs hcommon_raw (by sep_focus)
    fun sf _ evs _ _ hevs hent ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  exact ⟨evs, hevs, Entails.trans hent (Entails.of_eq (eq_of_sep_emp (by sep_focus))),
    hspf, htrf, hcc, hFf, hsymf, hvregs_f.trans hvregs_1⟩

theorem stageP3_err_tail_dup_ext_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr
    w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
       ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
            ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) :=
  stageP3_err_tail_dup_ext_4k_ok img b ext (AllocContractsMem4KBudget.of_AllocContracts hA)
    st s0 s coroPtr outPtr errsPtr prevStatesPtr w0 w1 w2 w3 w4 b_2c0 recG recSt
    hF hsym hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28

/-! ## Substage P3.5 Duplicate-Message Error Path (`stageP3_sub5_err_dup_ext_ok`) -/

set_option maxHeartbeats 1200000 in
theorem stageP3_sub5_err_dup_ext_4k_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4KBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (ratVer counter : BitVec 32)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
            ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) := by
  have hdecomp :
      vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64,
          words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
            speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝ ∗
        ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64) ∗ ((s.sp + 0x278#64) ↦₆₄ w0) ∗
        ((s.sp + 0x280#64) ↦₆₄ w1) ∗ ((s.sp + 0x288#64) ↦₆₄ w2) ∗
        ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗ H := by
    have h1 := speAt_decomp6 A.repAlloc (utf8 "decrypt") (s.sp + 0x270#64)
      (.duplicatedMessage ratVer counter) (by nofun)
    dsimp only [vecResultAt, speTag, speWord] at h1 ⊢
    refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64,
      words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (P₂ := ⌜∀ c : BitVec 64,
      words6At c 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A.repAlloc (utf8 "decrypt") c (.duplicatedMessage ratVer counter)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  have hstep1_raw := p3_err_dup_ext_vm_wp b ext s coroPtr outPtr
    hpc hrun hsp_align hx19 hx24
  have hstep1 := sepWP_swap_vm hstep1_raw
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hvm1, hregs1⟩ => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1,
    hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved (lim := lim) (st := st) hvm1).symm)
    (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hdropSs3 := drop_session_structure3_ok_ext_4k (b := b) (ext := ext) hA
  have hpc1_drop : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc1, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := ((⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost), st))
    (T := sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool lim st s1 ∗
      stackAt s.sp dropSessionStructure2Stack)
    hF1 hsym1 hdropSs3 hpc1_drop hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructureLocal2SpecBase, dropSessionStructure2Stack]; rw [hsp1_s])
    hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [dropSessionStructureLocal2SpecBase]
  rw [hsp1_s]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs₁ => ?_
  refine SepWPp.pure_elim fun ⟨htr2_1, hevs₁⟩ => ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000017#64 := hx28_cs2.trans hx28_1
  have htail_raw := stageP3_err_tail_dup_ext_4k_ok img b ext hA
    (M.stepEvents evs₁ st) s0 s2 coroPtr outPtr errsPtr prevStatesPtr
    w0 w1 w2 w3 w4 b_2c0 recG recSt
    hF2 hsym2 hpc2 hrun2 hsp2_align (htr2_1.trans (htr1_s.trans htr))
    hx19_2 hx24_2 hx25_2 hx26_2 hx28_2
  rw [hsp2_s] at htail_raw
  refine ret_sepWPp_frame_evs htail_raw (by sep_focus)
    fun sf _ evs₂ _ _ hevs₂ hent ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  have hrec : words6At outPtr 0x8000000000000017#64 w0 w1 w2 w3 w4 ∗ H ⊢
      recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) :=
    hreassemble outPtr
  refine ⟨evs₁ ++ evs₂, FreeOnlyEvs.append hevs₁ hevs₂, ?_,
    hspf, htrf, hcc, hFf, hsymf, by rw [hvregs_f, hvregs_cs2, hvregs_1]⟩
  rw [M.stepEvents_append evs₁ evs₂ st]
  exact Entails.trans hent (entails_replace_sub hrec (by sep_focus) (eq_of_sep_emp (by sep_focus)))

theorem stageP3_sub5_err_dup_ext_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr outPtr errsPtr prevStatesPtr : BitVec 64)
    (ratVer counter : BitVec 32)
    (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.error (.duplicatedMessage ratVer counter)) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (s.sp + 0xa90#64) 344 ∗ memRegion (coroPtr + 0xf8#64) 344 ∗
            ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
            ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
            recordResultAt A.repAlloc outPtr (.error (.duplicatedMessage ratVer counter)) ∗
            memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) :=
  stageP3_sub5_err_dup_ext_4k_ok img b ext (AllocContractsMem4KBudget.of_AllocContracts hA)
    st s0 s coroPtr outPtr errsPtr prevStatesPtr ratVer counter b_2c0 G₂ recG st₂ recSt
    hF hsym hpc hrun hsp_align htr hx19 hx24

/-! ## Success Path (`+0x1cd8 → +0x34dc`): `stageP3_sub5_ext_ok` & `stageP3_sub5_decResult_ext_ok` -/

theorem stageP3_sub5_ext_4k_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4KBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr retPtr : BitVec 64)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       A.pool lim st s ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
            ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp setSessionStateStack) ∧
          sf.sp = s.sp ∧ sf.trace = s0.trace ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) := by
  have hset := set_session_state_ok_ext_4k hA
  rw [sessionStateAt_eq_inline_sep_heap A.repAlloc (s.sp + 0xa90#64) G₂ st₂]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bs => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs.length = 344 ∧ SessionInline G₂ st₂ bs⌝)
    (P₂ := ⌜bs.length = 344 ∧ SessionInline G₂ st₂ bs⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hbs_len, hinl⟩ => ?_
  have hstk : stackAt s.sp setSessionStateStack =
      memRegion (s.sp - 4256#64) 160 ∗ stackAt s.sp allocHookStack := by
    rw [show setSessionStateStack = allocHookStack + 160 from rfl,
        stackAt_split_bottom' s.sp allocHookStack 160 (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk) (by sep_focus) ?_
  have hstep1_raw := p3_seg7a_x24_ext_4k_vm_wp b ext hA s coroPtr retPtr bs hb hbs_len
    hpc hrun hsp_align hx19
  have hstep1 := sepWP_swap_vm hstep1_raw
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hvm1, hregs1⟩ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved (lim := lim) (st := st) hvm1).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstk.symm) (by sep_focus) ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx1_1, hx19_1, hx24_1, hx25_1, hx26_1, hx27_1, hx29_1,
    hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hpc1_set : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr setSessionStateName := by
    rw [hpc1, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")]
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := ((⟨coroPtr + 0xe0#64, s.sp + 0x3e0#64, some (recG, recSt), bs⟩ : SetSessionStateGhost), st))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xe0#64 + 0x18#64) recG recSt ∗
          ((s.sp + 0x3e0#64) ↦ₛ bs) ∗ A.pool lim st s1 ∗ stackAt s.sp setSessionStateStack)
    hF1 hsym1 hset hpc1_set hrun1 hsp1_al hx30_1
    (by dsimp only [setSessionStateSpec]; rw [hsp1_s])
    (And.intro hx0_1 (And.intro hx1_1 hbs_len))
    (by
      have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
      rw [h18]; sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [setSessionStateSpec]
  rw [hsp1_s]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htr2_1, hevs, _⟩ => ?_
  have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
  rw [h18]
  have hmove := RawByteMove.sessionStateAt_move_bytes_twice A.repAlloc
    (s.sp + 0xa90#64) (s.sp + 0x3e0#64) (coroPtr + 0xf8#64) G₂ st₂ hinl
  refine P3P4.SepWPp.weaken_frame hmove (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, _, hx29_cs2,
    hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hstep3_raw := p3_seg7b_x24_ext_vm_wp b ext s2 coroPtr hpc2 hrun2 hx19_2
  have hstep3 := sepWP_swap_vm hstep3_raw
  refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf ⟨hvm3, hregsf⟩ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evs st) hvm3).symm)
    (by sep_focus) ?_
  rcases hregsf with ⟨hspf_2, htrf_2, hx19_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
    hvregs_f⟩
  refine SepWPp.done hpcf hrunf ⟨evs, hevs, Entails.of_eq (eq_of_sep_emp (by sep_focus)),
    hspf_2.trans hsp2_s,
    htrf_2.trans (htr2_1.trans (htr1_s.trans htr)),
    hFf, hsymf, hx19_f,
    hx24_f.trans (hx24_cs2.trans hx24_1),
    hx25_f.trans (hx25_cs2.trans hx25_1),
    hx26_f.trans (hx26_cs2.trans hx26_1),
    hx27_f.trans (hx27_cs2.trans hx27_1),
    hx28_f, hx29_f.trans (hx29_cs2.trans hx29_1),
    hvregs_f.trans (hvregs_cs2.trans hvregs_1)⟩

theorem stageP3_sub5_ext_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr retPtr : BitVec 64)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       A.pool lim st s ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
            ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s.sp setSessionStateStack) ∧
          sf.sp = s.sp ∧ sf.trace = s0.trace ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
          sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) :=
  stageP3_sub5_ext_4k_ok img b ext (AllocContractsMem4KBudget.of_AllocContracts hA)
    st s0 s coroPtr retPtr G₂ recG st₂ recSt hb hF hsym hpc hrun hsp_align htr hx19

theorem stageP3_sub5_decResult_ext_4k_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4KBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr retPtr : BitVec 64)
    (pt : List (BitVec 8)) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) ∗
       ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       A.pool lim st s ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent, ∃ ptCap ptPtr : BitVec 64,
          FreeOnlyEvs evs ∧
          pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64 ∧
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
            ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
            memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
            (if ptCap = 0#64 then emp
             else A.live ptPtr ptCap.toNat 1 ∗
               memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
            ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G₂ st₂ ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp setSessionStateStack) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧ sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
          sf.readReg64 .x26 = retPtr ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame (decResultAt_ok_unpack A.repAlloc (s.sp + 0x270#64) pt) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    RustCliAllocBudget.repAlloc_live]
  refine SepWPp.exists_elim fun ptCap => SepWPp.exists_elim fun ptPtr => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (P₂ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hpt_le, hpt_lt, hpt_ne⟩ => ?_
  have hsub_raw := stageP3_sub5_ext_4k_ok img b ext hA st s0 s coroPtr retPtr G₂ recG st₂ recSt
    hb hF hsym hpc hrun hsp_align htr hx19
  refine ret_sepWPp_frame_evs hsub_raw (by sep_focus)
    fun sf _ evs _ _ hevs hent ⟨hspf, htrf, hFf, hsymf, hx19f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f,
      hvregsf⟩ => ?_
  refine ⟨evs, ptCap, ptPtr, hevs, hpt_le, hpt_lt, hpt_ne, ?_,
    hspf, htrf, hFf, hsymf, hx19f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩
  exact Entails.trans hent (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

theorem stageP3_sub5_decResult_ext_ok {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsBudget b M A lim ext)
    (st : M.σ) (s0 s : State) (coroPtr retPtr : BitVec 64)
    (pt : List (BitVec 8)) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) ∗
       ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       A.pool lim st s ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent, ∃ ptCap ptPtr : BitVec 64,
          FreeOnlyEvs evs ∧
          pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64 ∧
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
            ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
            memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
            (if ptCap = 0#64 then emp
             else A.live ptPtr ptCap.toNat 1 ∗
               memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
            ((b + whitespaceLogOffBv_pub) ↦₆₄ 0#64) ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G₂ st₂ ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp setSessionStateStack) ∧
          sf.sp = s.sp ∧
          sf.trace = s0.trace ∧ img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧ sf.readReg64 .x19 = coroPtr ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
          sf.readReg64 .x26 = retPtr ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s)
      (PanicOomProp s0) :=
  stageP3_sub5_decResult_ext_4k_ok img b ext (AllocContractsMem4KBudget.of_AllocContracts hA)
    st s0 s coroPtr retPtr pt G₂ recG st₂ recSt hb hF hsym hpc hrun hsp_align htr hx19

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5Budget
