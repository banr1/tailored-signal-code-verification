/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPoly
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.DecodesPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `Option<proto::pq_ratchet::PolynomialEncoder>` Drop Glue (Block `435`)

Proves `drop_glue_opt_proto_poly_encoder_placed_ok` and `drop_opt_proto_poly_encoder_placed_ok`
(plus `HookSat` and `withPanics` wrappers) on Block `435` (`lsProg_435 H`) under
`RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.Cli.SpqrV1.Drop.Placed (blkPC_435 blkPl_435 lsProg_435)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (
  DropOptProtoPolyEncoderGhost Saved64Preserved
  add_24_add_8 cap_add_one_beq_zero_false cap_mul_24 cons_len_mul dropStack64
  header_cells_entails_memRegion_24 ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24
  ofNat_succ_eq_add_one optProtoPolyEncoder_none_entails_memRegion_56
  protoPolyEncoderAt_entails_dealloc protoPolyEncoderHeaders_entails_memRegion_56
  sep_pull_body sep_push_body sep_rejoin_loop
  stackAt_dropStack64_split stackAt_dropStack64_split_bottom
  stack_restore_64_allocHook tail_len_mul_lt vecCapPtrDealloc
  vecU8_entails_capPtr_dealloc
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialEncoderAt optProtoPolynomialEncoderNoneTailSize
  protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (dropOptProtoPolyEncoderSpec)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoPolyPlacedBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P = P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) := by
  subst h; exact hwp

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, LibsignalBinary.Heap.FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem sepWP_close_drop {prog : Program} {s0 s : State} {P : SepProp}
    {Post : State → SepProp → Prop}
    (Q_out : State → SepProp)
    (h : SepWP prog (s0.readReg64 .lr) s P (fun sf Pf =>
      (Pf ⊢ Q_out sf) ∧
      sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
      AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))
    (hpost : ∀ sf Pf, (Pf ⊢ Q_out sf) → sf.sp = s0.sp → sf.trace = s0.trace →
      AllocCallPreserved s0 sf → CalleeSavedPreserved s0 sf → Post sf Pf) :
    SepWP prog (s0.readReg64 .lr) s P Post :=
  SepWP.mono h fun sf Pf _ _ ⟨hp, hsp_f, htr_f, hacp_f, hcs_f⟩ =>
    hpost sf Pf hp hsp_f htr_f hacp_f hcs_f

@[local simp]
private theorem optProtoPolynomialEncoderAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoPolynomialEncoderAt A a none =
      ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) optProtoPolynomialEncoderNoneTailSize) := rfl

@[local simp]
private theorem optProtoPolynomialEncoderAt_some (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    optProtoPolynomialEncoderAt A a (some pb) = protoPolynomialEncoderAt A a pb := rfl

private theorem drop_opt_proto_poly_encoder_cli_placed_body1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_435).base + 64#64 → s.status = .Running →
      Saved64Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = cnt → s.readReg64 .x23 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 52#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
          sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hacp hx19 hx20 hx21 hx22 hx23
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 52#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
          sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
      wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 52#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
          sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = cnt ∧ sm.readReg64 .x23 = cur + 8#64) := by
      wp_steps
      wp_apply
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      rw [hsp]
      wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

private theorem drop_opt_proto_poly_encoder_cli_placed_loop1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp a ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_435).base + 64#64 → s.status = .Running →
      Saved64Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = ptsPtr → s.readReg64 .x21 = ptsCap →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length → s.readReg64 .x23 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 88#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap) := by
  have hbody := drop_opt_proto_poly_encoder_cli_placed_body1 hdealloc s0 fsp a ptsPtr ptsCap hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20 hx21 hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := (blkPl_435).base + 52#64)
      (P_evs := fun evs sm => memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
        stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧
        sm.readReg64 .x21 = ptsCap ∧ sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x23 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hacp hx19 hx20 hx21 hx22 hx23) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx22_1 ⊢
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      have hfin : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 88#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx22_1
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      rw [sep_push_body]
      refine seq_vm_clean (mid := (blkPl_435).base + 64#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun s2 => Saved64Preserved s0 s2 fsp ∧ AllocCallPreserved s0 s2 ∧
          s2.readReg64 .x19 = a ∧ s2.readReg64 .x20 = ptsPtr ∧ s2.readReg64 .x21 = ptsCap ∧
          s2.readReg64 .x22 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ s2.readReg64 .x23 = cur + 32#64)
        ?_ ?_
      · wp_steps_vm
      · intro s2 hpc2 hrun2 hvm2 ⟨hpres2, hacp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2⟩
        rw [← A.pool_of_vmPreserved hvm2]
        have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hacp2 hx19_2 hx20_2 hx21_2 hx22_2
          (by simp only [hx23_2, add_24_add_8, wp_norm, arm64_norm])
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

private theorem drop_opt_proto_poly_encoder_cli_placed_body2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_435).base + 140#64 → s.status = .Running →
      Saved64Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 128#64) s
        (vecU8 A.repAlloc cur bs ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  clear hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  intro cur cnt bs st s Frame hpc hrun hpres hacp hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A.repAlloc cur bs)) ?_
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro cap
  rw [sepExists_sepConj_left]; apply SepWP.exists_left; intro vptr
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hcap : (cap == 0#64) = true <;>
    simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    have hstep : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 128#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      wp_steps; wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩
  · apply sepWP_evs_dealloc cap.toNat 1
    have hstep : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 128#64) s
        (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
          (A.live vptr cap.toNat 1 ∗ memRegion vptr cap.toNat)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
      wp_steps
      wp_apply
      have hacp' : AllocCallPreserved s0 sf := hacp.trans (by assumption)
      rcases hacp' with ⟨_, _, _, _, _, _, _⟩
      wp_steps
      rw [hsp]
      wp_done
    exact SepWP.mono hstep fun sm _Pm _ _ ⟨hp, hq⟩ =>
      ⟨Entails.trans hp (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)), hq⟩

private theorem drop_opt_proto_poly_encoder_cli_placed_loop2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp a polysPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_435).base + 140#64 → s.status = .Running →
      Saved64Preserved s0 s fsp → AllocCallPreserved s0 s →
      s.readReg64 .x19 = a → s.readReg64 .x20 = polysPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 164#64) s
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 cur rest ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          ∃ evs, FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr) := by
  have hbody := drop_opt_proto_poly_encoder_cli_placed_body2 hdealloc s0 fsp a polysPtr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur st s Frame _ hlen hpc hrun hpres hacp hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean_evs (mid := (blkPl_435).base + 128#64)
      (P_evs := fun evs sm => memRegion cur 24 ∗ A.pool lim (M.stepEvents evs st) sm ∗
        stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs st s _ hpc hrun hpres hacp hx19 hx20 hx21 hx22) ?_
    intro evs_hd s1 hevs_hd hpc1 hrun1 ⟨hpres1, hacp1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp1
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      have hfin : SepWP ((blkPC_435).rebase (blkPl_435).base H) ((blkPl_435).base + 164#64) s1
          (memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ memRegion cur 24 ∗ A.pool lim (M.stepEvents evs_hd st) sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved64Preserved s0 sm fsp ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = polysPtr) := by
        wp_steps; wp_done
      exact SepWP.mono hfin fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs_hd, hevs_hd, hp, hq⟩
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      rcases hpres1 with ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      rw [sep_push_body]
      refine seq_vm_clean (mid := (blkPl_435).base + 140#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool lim (M.stepEvents evs_hd st) s1 ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun s2 => Saved64Preserved s0 s2 fsp ∧ AllocCallPreserved s0 s2 ∧
          s2.readReg64 .x19 = a ∧ s2.readReg64 .x20 = polysPtr ∧
          s2.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ s2.readReg64 .x22 = cur + 32#64)
        ?_ ?_
      · wp_steps_vm
      · intro s2 hpc2 hrun2 hvm2 ⟨hpres2, hacp2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        rw [← A.pool_of_vmPreserved hvm2]
        have hrec := ih (cur + 24#64) (M.stepEvents evs_hd st) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hacp2 hx19_2 hx20_2 hx21_2
          (by simp only [hx22_2, add_24_add_8, wp_norm, arm64_norm])
        refine SepWP.mono hrec fun sf _Pf _ _ ⟨evs_tl, hevs_tl, hp, hq⟩ => ?_
        refine ⟨evs_hd ++ evs_tl, hevs_hd.append hevs_tl, ?_, hq⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine Entails.trans hp ?_
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Relocatable `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>>`
(Block `435`) satisfies `dropOptProtoPolyEncoderSpec M A lim` under `[LibsignalPlacement]`. -/
theorem drop_glue_opt_proto_poly_encoder_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_435).rebase (blkPl_435).base H)
      (blkPl_435).base (dropOptProtoPolyEncoderSpec M A lim) := by
  simp only [dropOptProtoPolyEncoderSpec]
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hloop1 := drop_opt_proto_poly_encoder_cli_placed_loop1 hdealloc
  have hloop2 := drop_opt_proto_poly_encoder_cli_placed_loop2 hdealloc
  dsimp only [protoPolynomialEncoderSize, optProtoPolynomialEncoderNoneTailSize] at *
  wp_init x_st s0
  rcases x_st with ⟨⟨a, optPb⟩, st⟩
  dsimp only [DropOptProtoPolyEncoderGhost.a, DropOptProtoPolyEncoderGhost.optPb] at *
  nth_rw 1 [stackAt_dropStack64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x23 v_w3 v_x22 v_x21 v_x20 v_x19
  have hfsp_align : ((s0.sp - 64#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 64#64 (by assumption) (by decide)
  cases optPb with
  | none =>
    rw [optProtoPolynomialEncoderAt_none]; dsimp only [optProtoPolynomialEncoderNoneTailSize]
    refine seq_vm_clean (mid := s0.readReg64 .lr)
      (P_mid := memRegion a 56 ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStack64)
      (Q := fun sf => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
        AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (optProtoPolyEncoder_none_entails_memRegion_56 a) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
            (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_
        wp_done)
    · intro sf hpcf hrunf hvmf ⟨hsp_f, htr_f, hacp_f, hcs_f⟩
      rw [← A.pool_of_vmPreserved hvmf]
      apply SepWP.done hpcf hrunf
      refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
      rw [satisfies_sepExists]; refine ⟨[], ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  | some pb =>
    rw [optProtoPolynomialEncoderAt_some]
    refine SepWP.weaken_pre (sepConj_mono_left (protoPolyEncoderAt_entails_dealloc A.repAlloc a pb)) ?_
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    wp_pull_exists; rename_i g; wp_focus_pure
    rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne, hpolys_le, hpolys_cap_lt, hpolys_ptr_ne⟩
    have hpts_cap_pow : g.pts.cap.toNat < 2 ^ 63 := by omega
    have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
    refine seq_clean_evs (mid := (blkPl_435).base + 88#64)
      (P_evs := fun evs sm =>
        (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if g.pts.cap = 0 then emp
         else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗ memRegion g.pts.ptr (g.pts.cap.toNat * 24)) ∗
        ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        (if g.polys.cap = 0 then emp
         else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
           memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
             ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
        memRegion (a + 48#64) 8 ∗ A.pool lim (M.stepEvents evs st) sm ∗
        stackAt (s0.sp - 64#64) allocHookStack ∗
        (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧ sm.readReg64 .x21 = g.pts.cap) ?_ ?_
    · generalize hxs : pb.pts = xs at hpts_le ⊢
      cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, arrayAt, emp_sepConj]
        refine seq_vm_clean (mid := (blkPl_435).base + 88#64)
          (P_mid :=
            (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
            (if g.pts.cap = 0 then emp
             else A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗ memRegion g.pts.ptr (g.pts.cap.toNat * 24)) ∗
            ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
            ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
            (if g.polys.cap = 0 then emp
             else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
               arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
               memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
                 ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
            memRegion (a + 48#64) 8 ∗ A.pool lim st s0 ∗
            stackAt (s0.sp - 64#64) allocHookStack ∗
            (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧ sm.readReg64 .x21 = g.pts.cap) ?_ ?_
        · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
        · intro sm hpcm hrunm hvmm ⟨⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacpm, hx19m, hx20m, hx21m⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacpm
          rw [← A.pool_of_vmPreserved hvmm]
          apply sepWP_evs_nil
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_done
      | cons bs tl =>
        have hlen_pos : 0 < (bs :: tl).length := by simp
        have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
          have : (bs :: tl).length * 24 ≤ g.pts.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
        have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
        have hcap_ne : g.pts.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
        simp only [hcap_ne, ↓reduceIte]
        refine seq_vm_clean (mid := (blkPl_435).base + 64#64)
          (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.pts.ptr (bs :: tl) ∗
            A.pool lim st s0 ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
            ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
             ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
             A.live g.pts.ptr (g.pts.cap.toNat * 24) 8 ∗
             memRegion (g.pts.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((g.pts.cap.toNat - (bs :: tl).length) * 24) ∗
             ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
             ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
             (if g.polys.cap = 0 then emp
              else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
                arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
                memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
                  ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
             memRegion (a + 48#64) 8 ∗
             (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.pts.ptr ∧ sm.readReg64 .x21 = g.pts.cap ∧
            sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x23 = g.pts.ptr + 8#64) ?_ ?_
        · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
        · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop, hx23_loop⟩
          rw [← A.pool_of_vmPreserved hvm_loop]
          refine SepWP.mono
            (hloop1 s0 (s0.sp - 64#64) a g.pts.ptr g.pts.cap hfsp_align (bs :: tl) g.pts.ptr st s_loop _
              (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
              hx19_loop hx20_loop hx21_loop hx22_loop hx23_loop) ?_
          intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
          refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
          have hsplit : g.pts.cap.toNat * 24 =
              (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 := by
            rw [← Nat.add_mul]; congr 1; omega
          have hbound : (bs :: tl).length * 24 + (g.pts.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
            rw [← hsplit]; omega
          conv_rhs =>
            arg 2; arg 2; arg 2; arg 1; arg 2
            rw [hsplit, ProofLib.memRegion_split g.pts.ptr ((bs :: tl).length * 24)
                  ((g.pts.cap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by sep_ac_rfl)
    · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx20_1, hx21_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      let st1 := M.stepEvents evs1 st
      refine seq_clean_evs (mid := (blkPl_435).base + 112#64)
        (P_evs := fun evs sm =>
          (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
          (if g.polys.cap = 0 then emp
           else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr pb.polys ∗
             memRegion (g.polys.ptr + BitVec.ofNat 64 (pb.polys.length * 24))
               ((g.polys.cap.toNat - pb.polys.length) * 24)) ∗
          memRegion (a + 48#64) 8 ∗ A.pool lim (M.stepEvents evs st1) sm ∗
          stackAt (s0.sp - 64#64) allocHookStack ∗
          (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a) ?_ ?_
      · by_cases hc : g.pts.cap = 0
        · have hc_beq : (g.pts.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21_1 ⊢
          apply sepWP_evs_nil
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps; wp_done
        · have hc_beq : ¬((g.pts.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]
          apply sepWP_evs_dealloc (g.pts.cap.toNat * 24) 8
          wp_steps
          wp_call hdealloc_fo (g.pts.ptr, g.pts.cap.toNat * 24, 8, st1)
          rw [hsp_1]
          have hacp' : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          wp_done
      · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        let st2 := M.stepEvents evs2 st1
        refine seq_clean_evs (mid := (blkPl_435).base + 164#64)
          (P_evs := fun evs sm =>
            (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
            ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
            ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
            (if g.polys.cap = 0 then emp
             else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
            memRegion (a + 48#64) 8 ∗ A.pool lim (M.stepEvents evs st2) sm ∗
            stackAt (s0.sp - 64#64) allocHookStack ∗
            (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr) ?_ ?_
        · generalize hys : pb.polys = ys at hpolys_le ⊢
          cases ys with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
              BitVec.add_zero, arrayAt, emp_sepConj]
            refine seq_vm_clean (mid := (blkPl_435).base + 164#64)
              (P_mid :=
                (a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
                ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
                ((a + 40#64) ↦₆₄ 0#64) ∗
                (if g.polys.cap = 0 then emp
                 else A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗ memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
                memRegion (a + 48#64) 8 ∗ A.pool lim st2 s2 ∗
                stackAt (s0.sp - 64#64) allocHookStack ∗
                (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr) ?_ ?_
            · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
            · intro sm hpcm hrunm hvmm ⟨⟨hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hacpm, hx19m, hx20m⟩
              have ⟨_, _, _, _, _, _, _⟩ := hacpm
              rw [← A.pool_of_vmPreserved hvmm]
              apply sepWP_evs_nil
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
              wp_done
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.polys.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpolys_le; omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.polys.cap ≠ 0 := by intro hc0; rw [hc0] at hpolys_le; simp at hpolys_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_vm_clean (mid := (blkPl_435).base + 140#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.polys.ptr (bs :: tl) ∗
                A.pool lim st2 s2 ∗ stackAt (s0.sp - 64#64) allocHookStack ∗
                ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
                 ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                 ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
                 ((a + 40#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
                 A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
                 memRegion (g.polys.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24))
                   ((g.polys.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 48#64) 8 ∗
                 (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sm => Saved64Preserved s0 sm (s0.sp - 64#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.polys.ptr ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.polys.ptr + 8#64) ?_ ?_
            · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
            · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              rw [← A.pool_of_vmPreserved hvm_loop]
              refine SepWP.mono
                (hloop2 s0 (s0.sp - 64#64) a g.polys.ptr hfsp_align (bs :: tl) g.polys.ptr st2 s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop
                  hx19_loop hx20_loop hx21_loop hx22_loop) ?_
              intro sm _Pm _ _ ⟨evs, hevs, hp, hq⟩
              refine ⟨evs, hevs, Entails.trans hp ?_, hq⟩
              have hsplit : g.polys.cap.toNat * 24 =
                  (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.polys.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
                rw [← hsplit]; omega
              conv_rhs =>
                arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
                rw [hsplit, ProofLib.memRegion_split g.polys.ptr ((bs :: tl).length * 24)
                      ((g.polys.cap.toNat - (bs :: tl).length) * 24) hbound]
              exact Entails.of_eq (by sep_ac_rfl)
        · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3, hx20_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          let st3 := M.stepEvents evs3 st2
          by_cases hc : g.polys.cap = 0
          · have hc_beq : (g.polys.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]
            refine sepWP_close_drop
              (fun sf => memRegion a 56 ∗
                A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3) st) sf ∗ stackAt s0.sp dropStack64) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st3 : M.stepEvents (evs1 ++ evs2 ++ evs3) st = st3 := by
                simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st3]
              wp_steps
              refine SepWP.focus_weaken
                (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                  (BitVec.ofNat 64 pb.pts.length) 0#64 g.polys.ptr (BitVec.ofNat 64 pb.polys.length))
                (by sep_focus) ?_
              refine SepWP.focus_weaken
                (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                  (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
                  (s0.readReg64 .x20) (s0.readReg64 .x19))
                (by sep_focus) ?_
              wp_done
            · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ evs3, ?_⟩
              rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append hevs3⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
          · have hc_beq : ¬((g.polys.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpolys_cap_lt
            simp only [hc, ↓reduceIte]
            refine sepWP_close_drop
              (fun sf => memRegion a 56 ∗
                A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents (g.polys.cap.toNat * 24) 8) st) sf ∗
                stackAt s0.sp dropStack64) ?_
              (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · have heq_st4 : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents (g.polys.cap.toNat * 24) 8) st =
                  M.stepEvents (rustDeallocEvents (g.polys.cap.toNat * 24) 8) st3 := by
                simp only [st1, st2, st3, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st4]
              have htail : SepWP ((blkPC_435).rebase (blkPl_435).base H) (s0.readReg64 .lr) s3
                  ((a ↦₆₄ g.pts.cap) ∗ ((a + 8#64) ↦₆₄ g.pts.ptr) ∗
                    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
                    ((a + 24#64) ↦₆₄ g.polys.cap) ∗ ((a + 32#64) ↦₆₄ g.polys.ptr) ∗
                    ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
                    (A.live g.polys.ptr (g.polys.cap.toNat * 24) 8 ∗
                      memRegion g.polys.ptr (g.polys.cap.toNat * 24)) ∗
                    memRegion (a + 48#64) 8 ∗ A.pool lim st3 s3 ∗
                    stackAt (s0.sp - 64#64) allocHookStack ∗
                    (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
                     ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ v_w3) ∗
                     ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                     ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
                  (fun sf Pf =>
                    (Pf ⊢ memRegion a 56 ∗
                      A.pool lim (M.stepEvents (rustDeallocEvents (g.polys.cap.toNat * 24) 8) st3) sf ∗
                      stackAt s0.sp dropStack64) ∧
                    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                    AllocCallPreserved s3 sf ∧ CalleeSavedPreserved s0 sf) := by
                wp_steps
                refine SepWP.focus_weaken
                  (protoPolyEncoderHeaders_entails_memRegion_56 a g.pts.cap g.pts.ptr
                    (BitVec.ofNat 64 pb.pts.length) g.polys.cap g.polys.ptr (BitVec.ofNat 64 pb.polys.length))
                  (by sep_focus) ?_
                refine SepWP.focus_weaken
                  (stack_restore_64_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                    (s0.readReg64 .x23) v_w3 (s0.readReg64 .x22) (s0.readReg64 .x21)
                    (s0.readReg64 .x20) (s0.readReg64 .x19))
                  (by sep_focus) ?_
                rw [stackAt_dropStack64_split_bottom s0.sp]
                wp_call hdealloc_fo (g.polys.ptr, g.polys.cap.toNat * 24, 8, st3)
                have hpost3 : AllocCallPreserved s3 sf := by assumption
                rcases hpost3 with ⟨_, _, _, _, _, _, _⟩
                wp_done
              exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_3f, hcs_f⟩ =>
                ⟨hp, hsp_f, htr_f, hacp_3.trans hacp_3f, hcs_f⟩
            · rw [satisfies_sepExists]
              refine ⟨evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents (g.polys.cap.toNat * 24) 8, ?_⟩
              rw [satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, ((hevs1.append hevs2).append hevs3).append
                (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.polys.cap.toNat * 24))⟩, ?_⟩
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_opt_proto_poly_encoder_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok (lsProg_435 H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_435 H) (blkPl_435).base (dropOptProtoPolyEncoderSpec M A lim) :=
  drop_glue_opt_proto_poly_encoder_placed_ok hdealloc

theorem drop_opt_proto_poly_encoder_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_435 H) (blkPl_435).base (dropOptProtoPolyEncoderSpec M A lim) :=
  drop_glue_opt_proto_poly_encoder_placed_ok
    (CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem hdealloc)

theorem drop_glue_opt_proto_poly_encoder_placed
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_435 H) (blkPl_435).base (dropOptProtoPolyEncoderSpec M A lim) :=
  drop_opt_proto_poly_encoder_placed hdealloc

private theorem hookSat_dealloc_withPanics [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim) := by
  rcases hdealloc with ⟨f, hf, hok⟩
  exact ⟨f, by simp [Rust.withPanics, Rust.isPanicSymbol, hf], hok⟩

theorem drop_opt_proto_poly_encoder_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_435 (Rust.withPanics ext)) (blkPl_435).base
      (dropOptProtoPolyEncoderSpec M A lim) :=
  drop_opt_proto_poly_encoder_placed (hookSat_dealloc_withPanics hdealloc)

theorem drop_glue_opt_proto_poly_encoder_placed_x
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat ext "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_435 (Rust.withPanics ext)) (blkPl_435).base
      (dropOptProtoPolyEncoderSpec M A lim) :=
  drop_opt_proto_poly_encoder_placed_x hdealloc

theorem drop_opt_proto_poly_encoder_placed_lscl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 435)
      (CryptoVerification.withLsCodeLoaded CryptoVerification.lsmpl
        (dropOptProtoPolyEncoderSpec M A lim)) :=
  CryptoVerification.ls_subroutine_ok_of_block (callerProg := callerProg)
    (CryptoVerification.subroutine_ok_withLsCodeLoaded_of_plain
      (drop_opt_proto_poly_encoder_placed hdealloc)) hi

theorem drop_opt_proto_poly_encoder_placed_cl
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CryptoVerification.IsLsBlockProg callerProg i H]
    (hdealloc : HookSat H "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (CryptoVerification.lsmpl.base 435)
      (CryptoVerification.withLsCl CryptoVerification.lsmpl
        (dropOptProtoPolyEncoderSpec M A lim)) :=
  CryptoVerification.ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (drop_opt_proto_poly_encoder_placed hdealloc) hi

end LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoPolyPlacedBudget
