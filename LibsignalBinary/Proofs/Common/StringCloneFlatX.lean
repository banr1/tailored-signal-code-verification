/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.StringCloneFlat
public import LibsignalBinary.Proofs.Common.InImageKit
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import ProofLib.Hoare.OutcomeSteps
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stack-Parameterized and `.inImage` `<String as Clone>::clone` Proofs

Proves a unified stack- and state-invariant-parameterized correctness theorem
(`stringClone_withInv_fetches_ok`) for `<alloc::string::String as core::clone::Clone>::clone` and
specializes it to:
- `stringClone_4k_ok`: `stringCloneSpec A` on `tripleRatchetProgAtExt` from `4,096`-byte
  (`allocHookStack`) `memcpy`.
- `stringClone_inImage_4k_ok`: `(stringCloneSpec A).inImage img` on `tripleRatchetProgAtExt` carving
  `allocHookStack` out of `extHookStack` (`16,384` B) below the `48`-byte frame.
- `stringClone2x_inImage_of_allocContractsX`: `(stringCloneSpecWithStack A (2 * extHookStack)).inImage img`
  from `AllocContractsX`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.Common.StringCloneFlatX

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.ProgramReflection
open ProofLib.StdStartup
open ProofLib.StdStartup.Stage1Internal (step_str64_perm)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap
  (RustAlloc vecHeader vecU8 vecU8At allocHookStack LayoutOk
   allocFailedEvent allocFailedIn rustAllocSpec)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalPublicApi (stringCloneHookName stringCloneSpec)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack shimName allocName memcpyName handleErrorName
   sessionShimSpec sessionMemcpyRegionSpec framelessMemcpySpec
   withStack subroutine_ok_withStack_of_subroutine_ok rustAllocSpecWithStack
   tripleRatchetProgAtExt panic_at_handle_error_ext AllocContractsX ImgCallInv)
open LibsignalBinary.Proofs.Common.StringCloneFlat
  (rustStringCloneInstrs stringCloneName_fnOff)

/-! ## Stack-Parameterized Spec and Invariant Combinators -/

/-- `stringCloneSpec A` parameterized by callee stack budget `calleeStk` (`= stringCloneSpec A` at
    `extHookStack`, and definitionally equal to `Initiate.Stage1Lemmas.stringCloneAtStkSpec`). -/
def stringCloneSpecWithStack (A : RustAlloc) (calleeStk : Nat) :
    Spec (BitVec 64 × BitVec 64 × VecGhost) where
  pre := fun (p, ret, g) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗ vecGhostAt A g p ∗ memRegion ret 24 ∗
      A.pool ∗ stackAt s.sp calleeStk
  post := fun (p, ret, g) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecGhostAt A g p ∗ vecU8 A ret g.bytes ∗ A.pool ∗
      stackAt s0.sp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Enrich `spec` with state invariant `Inv` in `pre` (`= spec.inImage img` at `Inv := ImgCallInv img`). -/
private def withInv {α : Type} (Inv : State → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s => ⌜Inv s⌝ ∗ spec.pre x s }

private theorem subroutine_ok_withInv_true {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr spec) :
    subroutine_ok P addr (withInv (fun _ => True) spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [withInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal (fun _ hout => hout)

private theorem subroutine_ok_of_withInv_true {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr (withInv (fun _ => True) spec)) :
    subroutine_ok P addr spec := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withInv (fun _ => True) spec).pre x s0 ∗ R := by
    dsimp only [withInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, hpre⟩
  exact h.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)

private theorem sepWPp_of_sepWP_inv {P : Program} {Inv : State → Prop}
    (hStep : ∀ {s s' : State}, Steps P s s' → Inv s → Inv s')
    {ret mid : BitVec 64} {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : Inv s)
    (h : SepWP P mid s Pre (fun sm Pm => Inv sm → SepWPp P ret sm Pm Q Qp)) :
    SepWPp P ret s Pre Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hf⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hStep hsteps hinv) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hf⟩)⟩

private theorem sepWP_done_let_inv {P : Program} {Inv : State → Prop} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → Inv sm → SepWPp P ret sm Pre Q Qp) :
    SepWP P mid s Pre (fun sm Pm => Inv sm → SepWPp P ret sm Pm Q Qp) :=
  SepWP.done hpc hrun (fun hinv => h s rfl hpc hrun hinv)

private def withInvPost {α : Type} (Inv : State → Prop) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => ⌜Inv s⌝ ∗ spec.pre x s
    post := fun x s0 sf => ⌜Inv sf⌝ ∗ spec.post x s0 sf }

private theorem subroutine_ok_withInvPost {α : Type} {P : Program} {Inv : State → Prop}
    (hStep : ∀ {s s' : State}, Steps P s s' → Inv s → Inv s')
    {entry : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok P entry (withInv Inv spec)) :
    subroutine_ok P entry (withInvPost Inv spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hinv0 : Inv s0 := by
    dsimp only [withInvPost] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1
  refine (hcall.to_outcome x R s0 hpc hrun hpre hal).mono_outcome_steps fun sf hsteps hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withInvPost]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hStep hsteps hinv0, hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hq⟩))

private theorem sepWPp_call_withInv {α : Type} {P : Program} {Inv : State → Prop}
    (hStep : ∀ {s s' : State}, Steps P s s' → Inv s → Inv s')
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {Pre F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok P entry (withInv Inv spec)) (hinv : Inv s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Inv sf →
      SepWPp P ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R')) :
    SepWPp P ret s Pre Q Qp := by
  refine SepWPp.call (x := x) (F := F)
    (subroutine_ok_withInvPost hStep hcall) hpc hrun hsp hlr
    (fun R hm => by
      dsimp only [withInvPost]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hinv, hpre R hm⟩)
    hexit hpanic ?_ h_no_oom
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  dsimp only [withInvPost]
  rw [sepConj_assoc]
  exact SepWPp.pure_elim (hnext sf hpc_sf hrun_sf hsp_sf hcs_sf)

/-! ## Arithmetic, Memory, and Stack Helpers -/

private theorem bv_sub_add_cancel48 (sp : BitVec 64) : sp - 48#64 + 48#64 = sp := by bv_omega
private theorem bv_add_neg48 (sp : BitVec 64) : sp + (-48#64) = sp - 48#64 := by bv_omega
private theorem bv_add_neg16 (sp : BitVec 64) : sp + (-16#64) = sp - 16#64 := by bv_omega
private theorem sub_add_base_cancel (b x y d : BitVec 64) :
    (b + x) - ((b + y) + d) = x - (y + d) := by bv_omega

@[local simp, local arm64_norm]
private theorem setMem_setMem_eq (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by cases s; rfl
@[local simp, local arm64_norm]
private theorem setPC_setMem_eq (s : State) (m : Memory) (pc : BitVec 64) :
    (s.setMem m).setPC pc = (s.setPC pc).setMem m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setMem_eq (s : State) (m : Memory) : (s.setMem m).mem = m := by cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_setPC_eq (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl
@[local simp, local arm64_norm]
private theorem mem_writeReg64_eq (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl

private theorem step_stp64_perm {prog : Program} {target_pc pc ea ea2 v1 v2 : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1; let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm; have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setMem, State.setPC, State.writeReg64, hsp, haddr,
      hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 (funext fun a => by rw [Memory.perm_write64, Memory.perm_write64])) hm2

local macro "wp_str64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

local macro "wp_stp64 " hf:term:max m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm $hf; (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal | bv_lin))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_norm_lhs); (· wp_focus_close wp_norm_lhs)
  (· wp_focus_close wp_sep_access); (· wp_focus_close wp_sep_access)
  (· wp_focus_close wp_norm_lhs); intro $m $hm; try wp_norm_state))

attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_cancel48 bv_add_neg48 bv_add_neg16

private theorem spAligned_sub48 {sp : BitVec 64} (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 48#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_robdd

private theorem extHookStack_split_48 (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackFrameAt sp 48 ∗
        (stackAt (sp - 48#64) allocHookStack ∗
          stackFrameAt (sp - 48#64 - 4096#64) 12240) := by
  unfold stackAt extHookStack allocHookStack
  change memRegion (sp - 16384#64) 16384 = _
  rw [← stackFrameAt_eq_memRegion sp 16384 (by decide),
      ← stackFrameAt_eq_memRegion (sp - 48#64) 4096 (by decide),
      show (16384 : Nat) = 48 + 16336 from rfl,
      stackFrameAt_split sp 48 16336 (by decide),
      show (16336 : Nat) = 4096 + 12240 from rfl,
      stackFrameAt_split (sp - 48#64) 4096 12240 (by decide)]

private theorem stack2x_split_48 (sp : BitVec 64) :
    stackAt sp (2 * extHookStack) =
      stackFrameAt sp 48 ∗
        (stackAt (sp - 48#64) extHookStack ∗
          stackFrameAt (sp - 48#64 - 16384#64) 16336) := by
  unfold stackAt extHookStack
  change memRegion (sp - 32768#64) 32768 =
    stackFrameAt sp 48 ∗
      (memRegion (sp - 48#64 - 16384#64) 16384 ∗
        stackFrameAt (sp - 48#64 - 16384#64) 16336)
  rw [← stackFrameAt_eq_memRegion sp 32768 (by decide),
      ← stackFrameAt_eq_memRegion (sp - 48#64) 16384 (by decide),
      show (32768 : Nat) = 48 + 32720 from rfl,
      stackFrameAt_split sp 48 32720 (by decide),
      show (32720 : Nat) = 16384 + 16336 from rfl,
      stackFrameAt_split (sp - 48#64) 16384 16336 (by decide)]

private theorem stackFrameAt48_eq (sp : BitVec 64) :
    stackFrameAt sp 48 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
        ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
        ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) := by
  simp [stackFrameAt, stackFrameSlotsFrom, stackFrameSlotsCont]

private theorem pack_stack48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp - 48#64) ↦₆₄ w0) ∗ ((sp - 40#64) ↦₆₄ w1) ∗
     ((sp - 32#64) ↦₆₄ w2) ∗ ((sp - 24#64) ↦₆₄ w3) ∗
     ((sp - 16#64) ↦₆₄ w4) ∗ ((sp - 8#64) ↦₆₄ w5)) ⊢ stackFrameAt sp 48 := by
  rw [stackFrameAt48_eq sp]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.refl _))))))

private theorem sepWP_done_let {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (h : ∀ sm, sm = s → sm.pc = mid → sm.status = .Running → SepWPp prog ret sm P Q Qp oom) :
    SepWP prog mid s P (fun sm Pm => SepWPp prog ret sm Pm Q Qp oom) oom :=
  SepWP.done hpc hrun (h s rfl hpc hrun)

private theorem memRegion24_eq_exists_pts (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
        (a ↦₆₄ r0) ∗ ((a + 8#64) ↦₆₄ r1) ∗ ((a + 16#64) ↦₆₄ r2)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) from rfl,
      memRegion_split a 8 (8 + 8) (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide),
      memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right, sepExists_sepConj_right]

private abbrev FetchSeq (P : Program) (fnAddr : BitVec 64) (ls : List Instr) : Prop :=
  ∀ (i : Nat) (hi : i < ls.length),
    P.fetch (fnAddr + BitVec.ofNat 64 (4 * i)) = some ls[i]

private theorem fetch_seq_at {P : Program} {fnAddr off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (hf : FetchSeq P fnAddr ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (fnAddr + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have h := hf i hlt
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  rwa [hoff] at h

private theorem fetch_seq_at0 {P : Program} {fnAddr : BitVec 64} {ls : List Instr} {inst : Instr}
    (hf : FetchSeq P fnAddr ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch fnAddr = some inst := by
  simpa using fetch_seq_at 0 hf hi rfl

private theorem vecGhostAt_bytes_lt_2pow63 {A : RustAlloc}
    {m : Memory} {g : VecGhost} {p : BitVec 64} {R : SepProp}
    (hm : m ⊨ vecGhostAt A g p ∗ R) :
    g.bytes.length < 2 ^ 63 := by
  unfold vecGhostAt vecU8At at hm
  have hPull :
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (if g.cap = 0 then emp
         else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))) ∗ R =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
          (if g.cap = 0 then emp
           else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
             memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗ R) := by
    sep_ac_rfl
  rw [hPull, satisfies_pure_sepConj] at hm
  omega

private def vecGhostPayload (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_eq_header_payload (A : RustAlloc) (g : VecGhost) (p : BitVec 64) :
    vecGhostAt A g p =
      (((p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)) ∗
        vecGhostPayload A g) := by
  unfold vecGhostAt vecU8At vecHeader vecGhostPayload; sep_ac_rfl

private def vecGhostPayloadRest (A : RustAlloc) (g : VecGhost) : SepProp :=
  ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗ A.live g.ptr g.cap.toNat 1 ∗
  memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)

private theorem vecGhostPayload_nonempty_entails (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    vecGhostPayload A g ⊢ (g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g := by
  unfold vecGhostPayload vecGhostPayloadRest; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by
    intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
    omega
  simp only [hcapNe, ↓reduceIte]
  have hEq :
      A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) =
      (g.ptr ↦ₛ g.bytes) ∗ (A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hEq]; exact sepConj_mono_right (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl)))

private theorem vecGhostPayload_nonempty_pack (A : RustAlloc) (g : VecGhost)
    (hpos : 0 < g.bytes.length) :
    ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g) ⊢ vecGhostPayload A g := by
  unfold vecGhostPayloadRest vecGhostPayload
  have hPull :
      (g.ptr ↦ₛ g.bytes) ∗ (⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        A.live g.ptr g.cap.toNat 1 ∗
        memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
        ((g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
          memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) := by
    sep_ac_rfl
  rw [hPull]; refine Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
  have hcapNe : g.cap ≠ 0 := by
    intro hc0; have : g.cap.toNat = 0 := by rw [hc0]; rfl
    omega
  simp only [hcapNe, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_empty_pack (A : RustAlloc) (ret : BitVec 64) :
    ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64)) ⊢ vecU8 A ret [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  have hZero : (0#64 : BitVec 64) = 0 := rfl
  simp only [hZero, ↓reduceIte, sepConj_emp, List.length_nil]
  refine Entails.trans (Entails.pure_right
    (φ := 0 ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0)
    (by decide) (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private theorem vecU8_nonempty_pack (A : RustAlloc)
    (ret newPtr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt63 : bs.length < 2 ^ 63) (hne0 : newPtr ≠ 0#64) :
    let lenBv := BitVec.ofNat 64 bs.length
    (((ret ↦₆₄ lenBv) ∗ ((ret + 8#64) ↦₆₄ newPtr) ∗ ((ret + 16#64) ↦₆₄ lenBv)) ∗
      A.live newPtr bs.length 1 ∗ (newPtr ↦ₛ bs)) ⊢ vecU8 A ret bs := by
  intro lenBv
  have hlenNat : lenBv.toNat = bs.length := by
    dsimp only [lenBv]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcapNe : lenBv ≠ 0 := by
    intro h0; have := congrArg BitVec.toNat h0; rw [hlenNat] at this; change bs.length = 0 at this; omega
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right lenBv (Entails.sepExists_right newPtr ?_)
  simp only [hcapNe, ↓reduceIte, hlenNat, Nat.sub_self, memRegion_zero, sepConj_emp]
  refine Entails.trans (Entails.pure_right (φ := bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ newPtr ≠ 0)
    ⟨Nat.le_refl _, hlt63, hne0⟩ (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

/-! ## Abstract-Program Stepping Proof -/

private abbrev savedStack48 (s0 : State) : SepProp :=
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)

private abbrev vecHdrPts (p : BitVec 64) (g : VecGhost) : SepProp :=
  (p ↦₆₄ g.cap) ∗ ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length)

private abbrev retPts (ret r0 r1 r2 : BitVec 64) : SepProp :=
  (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2)

private abbrev csUpperPreserved (s0 sm : State) : Prop :=
  ∀ r ∈ ([.x23, .x24, .x25, .x26, .x27, .x28] : List Reg), sm.readReg64 r = s0.readReg64 r

private theorem csUpperPreserved_trans {s0 sm sf : State}
    (h1 : csUpperPreserved s0 sm) (h2 : CalleeSavedPreserved sm sf) :
    csUpperPreserved s0 sf := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2.readReg64_x23.trans (h1 .x23 (by simp))
  · exact h2.readReg64_x24.trans (h1 .x24 (by simp))
  · exact h2.readReg64_x25.trans (h1 .x25 (by simp))
  · exact h2.readReg64_x26.trans (h1 .x26 (by simp))
  · exact h2.readReg64_x27.trans (h1 .x27 (by simp))
  · exact h2.readReg64_x28.trans (h1 .x28 (by simp))

private abbrev cloneFrameGen (remOff : BitVec 64) (remStk : Nat) (s0 : State) : SepProp :=
  stackFrameAt (s0.sp - 48#64 - remOff) remStk

private abbrev clonePostGen (A : RustAlloc) (callerStk : Nat) (remOff : BitVec 64) (remStk : Nat)
    (p ret : BitVec 64) (g : VecGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ (cloneFrameGen remOff remStk s0 ∗ R)) →
      sf.mem ⊨ (stringCloneSpecWithStack A callerStk).post (p, ret, g) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev clonePanicGen (A : RustAlloc) (callerStk : Nat) (remOff : BitVec 64) (remStk : Nat)
    (p ret : BitVec 64) (g : VecGhost) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ (cloneFrameGen remOff remStk s0 ∗ R)) →
      sf.mem ⊨ (stringCloneSpecWithStack A callerStk).onPanic (p, ret, g) s0 sf ∗ R

private theorem clone_panic_tail_any {Q : State → SepProp → Prop} (A : RustAlloc) (calleeStk : Nat)
    {P : Program} {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hHandleErr : P.externAt? handleErrorAddr = some Rust.panicked)
    (p ret : BitVec 64) (g : VecGhost)
    (Rest FrameRem R : SepProp) (s0 sf2 : State)
    (hpc2 : sf2.pc = fnAddr + 0x30#64) (hrun2 : sf2.status = .Running)
    (hx0_0 : sf2.readReg64 .x0 = 0#64) (htr2 : sf2.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp P (s0.readReg64 .lr) sf2 Rest Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (FrameRem ∗ R)) →
        sf.mem ⊨ (stringCloneSpecWithStack A calleeStk).onPanic (p, ret, g) s0 sf ∗ R) := by
  have hf12 := fetch_seq_at 12 hCode; have hf30 := fetch_seq_at 30 hCode
  have hf31 := fetch_seq_at 31 hCode; have hf32 := fetch_seq_at 32 hCode
  apply SepWPp.of_sepWP (mid := handleErrorAddr)
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm_pan hsm hpc_pan hrun_pan => ?_
  have htr_pan : sm_pan.trace = s0.trace ++ [allocFailedEvent] := by
    rw [hsm]; simp [arm64_norm, htr2]
  clear hsm
  refine SepWPp.panic hrun_pan (hpc_pan ▸ hHandleErr) fun hmp => ?_
  dsimp only [stringCloneSpecWithStack] at hmp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨LibsignalBinary.Proofs.Common.SharedHelpers.allocFailedIn_and_prefix_of_trace_append_singleton
    (by simp [Rust.panicked, htr_pan]), ?_⟩
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _))
    (Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmp)

private theorem clone_empty_epilogue_gen (A : RustAlloc)
    (callerStk subStk remStk : Nat) (remOff : BitVec 64)
    (hSplit : ∀ sp : BitVec 64,
      stackAt sp callerStk =
        stackFrameAt sp 48 ∗ (stackAt (sp - 48#64) subStk ∗ stackFrameAt (sp - 48#64 - remOff) remStk))
    {P : Program} {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (p ret : BitVec 64) (g : VecGhost)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm : State)
    (hg_empty : g.bytes = []) (hsp0 : s0.spAligned = true)
    (hpcm : sm.pc = fnAddr + 0x5c#64) (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 48#64) (hx19 : sm.readReg64 .x19 = 0#64)
    (hx20 : sm.readReg64 .x20 = ret) (hcsm : csUpperPreserved s0 sm)
    (hvm : calleeSavedVRegs sm = calleeSavedVRegs s0) (htrm : sm.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sm
      (retPts ret r0 r1 r2 ∗ savedStack48 s0 ∗
        (vecHdrPts p g ∗ vecGhostPayload A g) ∗
        A.pool ∗ stackAt (s0.sp - 48#64) subStk)
      (clonePostGen A callerStk remOff remStk p ret g R s0)
      (clonePanicGen A callerStk remOff remStk p ret g R s0) := by
  have hf23 := fetch_seq_at 23 hCode; have hf24 := fetch_seq_at 24 hCode
  have hf25 := fetch_seq_at 25 hCode; have hf26 := fetch_seq_at 26 hCode
  have hf27 := fetch_seq_at 27 hCode; have hf28 := fetch_seq_at 28 hCode
  have hf29 := fetch_seq_at 29 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide (sm.sp &&& 15#64 = 0#64) = true := by
    rw [hspm]; exact decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_stp64 hf24 m1 hm1; wp_str64 hf25 m2 hm2
  wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrunm])
    fun sf hsf hpcf hrunf => ?_
  have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
  have htrf : sf.trace = s0.trace := by rw [hsf]; simp [arm64_norm, htrm]
  have hcsf : CalleeSavedPreserved s0 sf := by
    rw [hsf]
    refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hcsm .x23 (by simp), by simpa [arm64_norm] using hcsm .x24 (by simp),
      by simpa [arm64_norm] using hcsm .x25 (by simp), by simpa [arm64_norm] using hcsm .x26 (by simp),
      by simpa [arm64_norm] using hcsm .x27 (by simp), by simpa [arm64_norm] using hcsm .x28 (by simp),
      by simp [arm64_norm], by simpa [calleeSavedVRegs, arm64_norm] using hvm⟩
  clear hsf
  refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
  dsimp only [clonePostGen, cloneFrameGen, stringCloneSpecWithStack] at hmf ⊢
  rw [hSplit s0.sp]
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = 0#64 := hx19
  have hx20' : sm.readReg64 (Reg.gpr 20#5) = ret := hx20
  try simp only [hx19', hx20', BitVec.add_zero] at hmf
  have hVecEq : (vecHdrPts p g ∗ vecGhostPayload A g) = vecGhostAt A g p :=
    (vecGhostAt_eq_header_payload A g p).symm
  have hmf1 : sf.mem ⊨
      (vecGhostAt A g p ∗
        (retPts ret 0#64 1#64 0#64 ∗ A.pool ∗
          (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) subStk ∗ stackFrameAt (s0.sp - 48#64 - remOff) remStk)))) ∗ R := by
    rw [← hVecEq]; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmf
  rw [hg_empty]
  refine Satisfies.mono (sepConj_mono_left ?_) hmf1
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (vecU8_empty_pack A ret)
        (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
  exact Entails.pure_right htrf (Entails.of_eq (by sep_ac_rfl))

private theorem clone_memcpy_epilogue_inv {P : Program} {Inv : State → Prop}
    (hInvStep : ∀ {s s' : State}, Steps P s s' → Inv s → Inv s')
    (A : RustAlloc) (callerStk subStk remStk : Nat) (remOff : BitVec 64)
    (hSplit : ∀ sp : BitVec 64,
      stackAt sp callerStk =
        stackFrameAt sp 48 ∗ (stackAt (sp - 48#64) subStk ∗ stackFrameAt (sp - 48#64 - remOff) remStk))
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hMemcpy : subroutine_ok P memcpyAddr (withInv Inv (withStack sessionMemcpyRegionSpec subStk)))
    (p ret newPtr : BitVec 64) (g : VecGhost)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sf2 : State)
    (hinv2 : Inv sf2)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63)
    (hsp0 : s0.spAligned = true) (hpNe0 : newPtr ≠ 0#64)
    (hpc2 : sf2.pc = fnAddr + 0x30#64) (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 48#64) (hx0_2 : sf2.readReg64 .x0 = newPtr)
    (hx19_2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_2 : sf2.readReg64 .x20 = ret) (hx22_2 : sf2.readReg64 .x22 = g.ptr)
    (hcs2 : csUpperPreserved s0 sf2) (hv2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (htr2 : sf2.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sf2
      (memRegion newPtr g.bytes.length ∗ vecGhostPayload A g ∗
        A.live newPtr g.bytes.length 1 ∗ A.pool ∗
        stackAt (s0.sp - 48#64) subStk ∗ retPts ret r0 r1 r2 ∗
        vecHdrPts p g ∗ savedStack48 s0)
      (clonePostGen A callerStk remOff remStk p ret g R s0)
      (clonePanicGen A callerStk remOff remStk p ret g R s0) := by
  have hf12 := fetch_seq_at 12 hCode; have hf13 := fetch_seq_at 13 hCode
  have hf14 := fetch_seq_at 14 hCode; have hf15 := fetch_seq_at 15 hCode
  have hf16 := fetch_seq_at 16 hCode; have hf17 := fetch_seq_at 17 hCode
  have hf18 := fetch_seq_at 18 hCode; have hf19 := fetch_seq_at 19 hCode
  have hf20 := fetch_seq_at 20 hCode; have hf21 := fetch_seq_at 21 hCode
  have hf22 := fetch_seq_at 22 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (vecGhostPayload_nonempty_entails A g hpos))) ?_
  apply sepWPp_of_sepWP_inv hInvStep (mid := memcpyAddr) hinv2
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step; wp_step; wp_step; wp_step
  refine sepWP_done_let_inv (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun2]) fun sm3 hsm hpc3 hrun3 hinv3 => ?_
  have hsp3 : sm3.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm, hsp2]
  have hlr3 : sm3.readReg64 .lr = fnAddr + 0x44#64 := by
    rw [hsm]; simp only [arm64_norm]; try bv_omega
  have hx0_3 : sm3.readReg64 .x0 = newPtr := by rw [hsm]; simp [arm64_norm, hx0_2]
  have hx1_3 : sm3.readReg64 .x1 = g.ptr := by rw [hsm]; simp [arm64_norm]
  have hx2_3 : (sm3.readReg64 .x2).toNat = g.bytes.length := by
    rw [hsm]; simp only [arm64_norm]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx19_3 : sm3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm]; simp [arm64_norm, hx19_2]
  have hx20_3 : sm3.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm, hx20_2]
  have hx21_3 : sm3.readReg64 .x21 = newPtr := by rw [hsm]; simp [arm64_norm]
  have hcs3 : csUpperPreserved s0 sm3 := by
    rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs2 _ (by simp)
  have hv3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
    rw [hsm]; simpa [calleeSavedVRegs, arm64_norm] using hv2
  have htr3 : sm3.trace = s0.trace := by rw [hsm]; simp [arm64_norm, htr2]
  clear hsm
  let FrameMc :=
    vecGhostPayloadRest A g ∗ A.live newPtr g.bytes.length 1 ∗
    A.pool ∗ retPts ret r0 r1 r2 ∗ vecHdrPts p g ∗ savedStack48 s0
  refine sepWPp_call_withInv hInvStep (x := (newPtr, g.ptr, g.bytes)) (ret_pc := fnAddr + 0x44#64)
    (F := FrameMc) hMemcpy hinv3 hpc3 hrun3
    (by simpa [State.spAligned, hsp3] using hspAl48b) hlr3 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ hp => by
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at hp
      rw [sepConj_assoc] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, FrameMc]
    rw [hsp3, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx1_3, hx2_3⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 hcs_sf3 _hinv_sf3
    dsimp only [withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, FrameMc]
    rw [hsp3, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htr_mc⟩ => ?_
    have hsp3' : sf3.sp = s0.sp - 48#64 := hsp_sf3.trans hsp3
    have hspAl48 : decide (sf3.sp &&& 15#64 = 0#64) = true := by
      rw [hsp3']; exact decide_eq_true (beq_iff_eq.mp hspAl48b)
    have hx19_sf3 : sf3.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf3.readReg64_x19.trans hx19_3
    have hx20_sf3 : sf3.readReg64 .x20 = ret := hcs_sf3.readReg64_x20.trans hx20_3
    have hx21_sf3 : sf3.readReg64 .x21 = newPtr := hcs_sf3.readReg64_x21.trans hx21_3
    have hcs_sf3_s0 : csUpperPreserved s0 sf3 := csUpperPreserved_trans hcs3 hcs_sf3
    have htr_sf3 : sf3.trace = s0.trace := htr_mc.trans htr3
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    dsimp only [retPts, savedStack48, vecHdrPts]
    wp_stp64 hf17 m1 hm1; wp_str64 hf18 m2 hm2
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp [arm64_norm]) (by simp [arm64_norm, hrun_sf3])
      fun sf hsf hpcf hrunf => ?_
    have hspf : sf.sp = s0.sp := by rw [hsf]; simp [arm64_norm]
    have htrf : sf.trace = s0.trace := by rw [hsf]; simp [arm64_norm, htr_sf3]
    have hcsf : CalleeSavedPreserved s0 sf := by
      rw [hsf]
      refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simpa [arm64_norm] using hcs_sf3_s0 .x23 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x24 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x25 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x26 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x27 (by simp),
        by simpa [arm64_norm] using hcs_sf3_s0 .x28 (by simp),
        by simp [arm64_norm],
        by simpa [calleeSavedVRegs, arm64_norm] using hcs_sf3.vregs.trans hv3⟩
    clear hsf
    refine SepWPp.done hpcf hrunf ⟨fun hmf => ?_, hspf, hcsf⟩
    dsimp only [clonePostGen, cloneFrameGen, stringCloneSpecWithStack] at hmf ⊢
    rw [hSplit s0.sp]
    have hx19' : sf3.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 g.bytes.length := hx19_sf3
    have hx20' : sf3.readReg64 (Reg.gpr 20#5) = ret := hx20_sf3
    have hx21' : sf3.readReg64 (Reg.gpr 21#5) = newPtr := hx21_sf3
    try simp only [hx19', hx20', hx21', BitVec.add_zero] at hmf
    let lenBv := BitVec.ofNat 64 g.bytes.length
    have hmf1 : sf.mem ⊨
        ((vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g)) ∗
          ((retPts ret lenBv newPtr lenBv ∗
            A.live newPtr g.bytes.length 1 ∗ (newPtr ↦ₛ g.bytes)) ∗
           A.pool ∗
           (savedStack48 s0 ∗
            (stackAt (s0.sp - 48#64) subStk ∗ stackFrameAt (s0.sp - 48#64 - remOff) remStk)))) ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp only [lenBv]; sep_ac_rfl)) hmf
    refine Satisfies.mono (sepConj_mono_left ?_) hmf1
    have hGhostEnt :
        (vecHdrPts p g ∗ ((g.ptr ↦ₛ g.bytes) ∗ vecGhostPayloadRest A g)) ⊢
        vecGhostAt A g p := by
      rw [vecGhostAt_eq_header_payload A g p]
      exact sepConj_mono_right (vecGhostPayload_nonempty_pack A g hpos)
    refine Entails.trans
      (sepConj_mono hGhostEnt
        (sepConj_mono (vecU8_nonempty_pack A ret newPtr g.bytes hpos hlt63 hpNe0)
          (sepConj_mono_right (sepConj_mono_left (pack_stack48 s0.sp _ _ _ _ _ _))))) ?_
    exact Entails.pure_right htrf (Entails.of_eq (by sep_ac_rfl))

private theorem clone_nonempty_branch_inv {P : Program} {Inv : State → Prop}
    (hInvStep : ∀ {s s' : State}, Steps P s s' → Inv s → Inv s')
    (A : RustAlloc) (callerStk subStk remStk : Nat) (remOff : BitVec 64)
    (hSplit : ∀ sp : BitVec 64,
      stackAt sp callerStk =
        stackFrameAt sp 48 ∗ (stackAt (sp - 48#64) subStk ∗ stackFrameAt (sp - 48#64 - remOff) remStk))
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr (withInv Inv (withStack sessionShimSpec subStk)))
    (hAlloc : subroutine_ok P allocAddr (withInv Inv (rustAllocSpecWithStack A subStk)))
    (hMemcpy : subroutine_ok P memcpyAddr (withInv Inv (withStack sessionMemcpyRegionSpec subStk)))
    (hHandleErr : P.externAt? handleErrorAddr = some Rust.panicked)
    (p ret : BitVec 64) (g : VecGhost)
    (r0 r1 r2 : BitVec 64) (R : SepProp) (s0 sm0 : State)
    (hinvm0 : Inv sm0)
    (hpos : 0 < g.bytes.length) (hlt63 : g.bytes.length < 2 ^ 63) (hsp0 : s0.spAligned = true)
    (hpcm0 : sm0.pc = fnAddr + 0x1c#64) (hrunm0 : sm0.status = .Running)
    (hspm0 : sm0.sp = s0.sp - 48#64) (hx0_m0 : sm0.readReg64 .x0 = p)
    (hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length)
    (hx20_m0 : sm0.readReg64 .x20 = ret) (hcsm0 : csUpperPreserved s0 sm0)
    (hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0) (htrm0 : sm0.trace = s0.trace) :
    SepWPp P (s0.readReg64 .lr) sm0
      (vecHdrPts p g ∗ vecGhostPayload A g ∗ A.pool ∗
        stackAt (s0.sp - 48#64) subStk ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0)
      (clonePostGen A callerStk remOff remStk p ret g R s0)
      (clonePanicGen A callerStk remOff remStk p ret g R s0) := by
  have hf7 := fetch_seq_at 7 hCode; have hf8 := fetch_seq_at 8 hCode
  have hf9 := fetch_seq_at 9 hCode; have hf10 := fetch_seq_at 10 hCode
  have hf11 := fetch_seq_at 11 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48b : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub48 hspAl0
  apply sepWPp_of_sepWP_inv hInvStep (mid := shimAddr) hinvm0
  dsimp only [retPts, savedStack48, vecHdrPts]
  wp_step; wp_step
  refine sepWP_done_let_inv (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrunm0]) fun sm1 hsm1 hpc1 hrun1 hinv1 => ?_
  have hsp1 : sm1.sp = s0.sp - 48#64 := by rw [hsm1]; simp [arm64_norm, hspm0]
  have hlr1 : sm1.readReg64 .lr = fnAddr + 0x24#64 := by
    rw [hsm1]; simp only [arm64_norm]; try bv_omega
  have hx19_1 : sm1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm1]; simp [arm64_norm, hx19_m0]
  have hx20_1 : sm1.readReg64 .x20 = ret := by
    rw [hsm1]; simp [arm64_norm, hx20_m0]
  have hx22_1 : sm1.readReg64 .x22 = g.ptr := by rw [hsm1]; simp [arm64_norm]
  have hcs1 : csUpperPreserved s0 sm1 := by
    rw [hsm1]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcsm0 _ (by simp)
  have hv1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := by
    rw [hsm1]; simpa [calleeSavedVRegs, arm64_norm] using hvm0
  have htr1 : sm1.trace = s0.trace := by rw [hsm1]; simp [arm64_norm, htrm0]
  clear hsm1
  let FrameShim :=
    vecHdrPts p g ∗ vecGhostPayload A g ∗ A.pool ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  refine sepWPp_call_withInv hInvStep (x := ()) (ret_pc := fnAddr + 0x24#64)
    (F := FrameShim) hShim hinv1 hpc1 hrun1
    (by simpa [State.spAligned, hsp1] using hspAl48b) hlr1
    (fun _ hm' => by
      dsimp only [withStack, sessionShimSpec, FrameShim]
      rw [emp_sepConj, hsp1]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm')
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ hp => by
      dsimp only [withStack, sessionShimSpec] at hp
      rw [sepConj_assoc] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [withStack, sessionShimSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1 hinv_sf1
  dsimp only [withStack, sessionShimSpec, FrameShim]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sh => ?_
  have hsp_sf1' : sf1.sp = s0.sp - 48#64 := hsp_sf1.trans hsp1
  have hx19_sf1 : sf1.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
    hcs_sf1.readReg64_x19.trans hx19_1
  have hx20_sf1 : sf1.readReg64 .x20 = ret := hcs_sf1.readReg64_x20.trans hx20_1
  have hx22_sf1 : sf1.readReg64 .x22 = g.ptr := hcs_sf1.readReg64_x22.trans hx22_1
  have hcs_sf1_s0 : csUpperPreserved s0 sf1 := csUpperPreserved_trans hcs1 hcs_sf1
  have htr_sf1 : sf1.trace = s0.trace := htr_sh.trans htr1
  apply sepWPp_of_sepWP_inv hInvStep (mid := allocAddr) hinv_sf1
  wp_step; wp_step; wp_step
  refine sepWP_done_let_inv (by simp only [arm64_norm]; try bv_omega)
    (by simp [arm64_norm, hrun_sf1]) fun sm2 hsm2 hpc2 hrun2 hinv2 => ?_
  have hsp2 : sm2.sp = s0.sp - 48#64 := by rw [hsm2]; simp [arm64_norm, hsp_sf1']
  have hlr2 : sm2.readReg64 .lr = fnAddr + 0x30#64 := by
    rw [hsm2]; simp only [arm64_norm]; try bv_omega
  have hx0_2 : sm2.readReg64 .x0 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm]
  have hx1_2 : sm2.readReg64 .x1 = 1#64 := by rw [hsm2]; simp [arm64_norm]
  have hx19_2 : sm2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
    rw [hsm2]; simp [arm64_norm, hx19_sf1]
  have hx20_2 : sm2.readReg64 .x20 = ret := by rw [hsm2]; simp [arm64_norm, hx20_sf1]
  have hx22_2 : sm2.readReg64 .x22 = g.ptr := by rw [hsm2]; simp [arm64_norm, hx22_sf1]
  have hcs2 : csUpperPreserved s0 sm2 := by
    rw [hsm2]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [arm64_norm] using hcs_sf1_s0 _ (by simp)
  have hv2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := by
    rw [hsm2]; simpa [calleeSavedVRegs, arm64_norm] using hcs_sf1.vregs.trans hv1
  have htr2 : sm2.trace = s0.trace := by rw [hsm2]; simp [arm64_norm, htr_sf1]
  clear hsm2
  let FrameAl :=
    vecHdrPts p g ∗ vecGhostPayload A g ∗ retPts ret r0 r1 r2 ∗ savedStack48 s0
  have hx0_nat : (sm2.readReg64 .x0).toNat = g.bytes.length := by
    rw [hx0_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx1_nat : (sm2.readReg64 .x1).toNat = 1 := by rw [hx1_2]; rfl
  have hLay : LayoutOk g.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  refine sepWPp_call_withInv hInvStep (x := (g.bytes.length, 1)) (ret_pc := fnAddr + 0x30#64)
    (F := FrameAl) hAlloc hinv2 hpc2 hrun2
    (by simpa [State.spAligned, hsp2] using hspAl48b) hlr2 ?_
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ hp => by
      dsimp only [rustAllocSpecWithStack] at hp
      rw [sepConj_assoc] at hp
      exact False.elim (not_satisfies_false_sepConj hp))
    ?_
    (fun _ _ _ ho => by
      dsimp only [rustAllocSpecWithStack] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R' hm'
    dsimp only [rustAllocSpecWithStack, FrameAl]
    rw [hsp2, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_nat, hx1_nat, hLay⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩
  · intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2 hinv_sf2
    dsimp only [rustAllocSpecWithStack, FrameAl]
    rw [hsp2]
    have hsp_sf2' : sf2.sp = s0.sp - 48#64 := hsp_sf2.trans hsp2
    have hx19_sf2 : sf2.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length :=
      hcs_sf2.readReg64_x19.trans hx19_2
    have hx20_sf2 : sf2.readReg64 .x20 = ret := hcs_sf2.readReg64_x20.trans hx20_2
    have hx22_sf2 : sf2.readReg64 .x22 = g.ptr := hcs_sf2.readReg64_x22.trans hx22_2
    have hcs_s0_sf2 : csUpperPreserved s0 sf2 := csUpperPreserved_trans hcs2 hcs_sf2
    have hv_s0_sf2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
      hcs_sf2.vregs.trans hv2
    by_cases hnull : sf2.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte]
      have hPullNull :
          (A.pool ∗ stackAt (s0.sp - 48#64) subStk ∗
            ⌜sf2.trace = sm2.trace ++ [allocFailedEvent]⌝) ∗ FrameAl =
          ⌜sf2.trace = sm2.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt (s0.sp - 48#64) subStk ∗ FrameAl) := by
        dsimp only [FrameAl]; sep_ac_rfl
      rw [hPullNull]
      refine SepWPp.pure_elim fun htr_al => ?_
      exact clone_panic_tail_any A callerStk hCode hHandleErr p ret g
        (A.pool ∗ stackAt (s0.sp - 48#64) subStk ∗ FrameAl) (cloneFrameGen remOff remStk s0) R s0 sf2
        hpc_sf2 hrun_sf2 hnull (by rw [htr_al, htr2])
    · simp only [hnull, ↓reduceIte]
      let newPtr := sf2.readReg64 .x0
      have hpNe0 : newPtr ≠ 0#64 := hnull
      have hPullOk :
          (A.pool ∗ stackAt (s0.sp - 48#64) subStk ∗
            (⌜newPtr.toNat % 1 = 0 ∧ sf2.trace = sm2.trace⌝ ∗
              A.live newPtr g.bytes.length 1 ∗ memRegion newPtr g.bytes.length)) ∗ FrameAl =
          ⌜newPtr.toNat % 1 = 0 ∧ sf2.trace = sm2.trace⌝ ∗
            (memRegion newPtr g.bytes.length ∗ vecGhostPayload A g ∗
              A.live newPtr g.bytes.length 1 ∗ A.pool ∗
              stackAt (s0.sp - 48#64) subStk ∗ retPts ret r0 r1 r2 ∗
              vecHdrPts p g ∗ savedStack48 s0) := by
        dsimp only [FrameAl, newPtr]; sep_ac_rfl
      rw [hPullOk]
      refine SepWPp.pure_elim fun ⟨_, htr_al⟩ => ?_
      exact clone_memcpy_epilogue_inv hInvStep A callerStk subStk remStk remOff hSplit
        hCode hMemcpy p ret newPtr g
        r0 r1 r2 R s0 sf2 hinv_sf2 hpos hlt63 hsp0 hpNe0
        hpc_sf2 hrun_sf2 hsp_sf2' rfl hx19_sf2 hx20_sf2 hx22_sf2
        hcs_s0_sf2 hv_s0_sf2 (htr_al.trans htr2)

/-- Unified stack- and invariant-parameterized `<String as Clone>::clone` correctness over an
    abstract `Program`: carves `<String as Clone>::clone`'s `48`-byte frame plus `subStk` of callee
    stack out of `callerStk` via `hSplit`, threading `Inv` across calls. -/
private theorem stringClone_withInv_fetches_ok {P : Program} {Inv : State → Prop}
    (hInvStep : ∀ {s s' : State}, Steps P s s' → Inv s → Inv s')
    (A : RustAlloc) (callerStk subStk remStk : Nat) (remOff : BitVec 64)
    (hSplit : ∀ sp : BitVec 64,
      stackAt sp callerStk =
        stackFrameAt sp 48 ∗ (stackAt (sp - 48#64) subStk ∗ stackFrameAt (sp - 48#64 - remOff) remStk))
    {fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : FetchSeq P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddr memcpyAddr handleErrorAddr))
    (hShim : subroutine_ok P shimAddr (withInv Inv (withStack sessionShimSpec subStk)))
    (hAlloc : subroutine_ok P allocAddr (withInv Inv (rustAllocSpecWithStack A subStk)))
    (hMemcpy : subroutine_ok P memcpyAddr (withInv Inv (withStack sessionMemcpyRegionSpec subStk)))
    (hHandleErr : P.externAt? handleErrorAddr = some Rust.panicked) :
    subroutine_ok P fnAddr (withInv Inv (stringCloneSpecWithStack A callerStk)) := by
  apply subroutine_ok_of_sepWPp_pure_oom (φ := fun _ _ _ => False)
    (by rintro ⟨_, _, _⟩ _ _; rfl)
  rintro ⟨p, ret, g⟩ R s0 hpc hrun hpre hsp0
  dsimp only [withInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  dsimp only [stringCloneSpecWithStack] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hrest⟩
  have hlt63 : g.bytes.length < 2 ^ 63 := by
    refine vecGhostAt_bytes_lt_2pow63 (A := A) (m := s0.mem) (p := p)
      (R := memRegion ret 24 ∗ (A.pool ∗ (stackAt s0.sp callerStk ∗ R))) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  let P0 :=
    stackFrameAt s0.sp 48 ∗ memRegion ret 24 ∗ vecGhostAt A g p ∗
    A.pool ∗ stackAt (s0.sp - 48#64) subStk
  have hm0 : s0.mem ⊨ P0 ∗ (cloneFrameGen remOff remStk s0 ∗ R) := by
    dsimp only [P0, cloneFrameGen]
    rw [hSplit s0.sp] at hrest
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine ⟨P0, cloneFrameGen remOff remStk s0, hm0, ?_⟩
  dsimp only [P0]
  rw [stackFrameAt48_eq s0.sp, memRegion24_eq_exists_pts ret,
      vecGhostAt_eq_header_payload A g p]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun r0 => SepWPp.exists_elim fun r1 =>
    SepWPp.exists_elim fun r2 => SepWPp.exists_elim fun st0 =>
    SepWPp.exists_elim fun st1 => SepWPp.exists_elim fun st2 =>
    SepWPp.exists_elim fun st3 => SepWPp.exists_elim fun st4 =>
    SepWPp.exists_elim fun st5 => ?_
  have hf0 := fetch_seq_at0 hCode; have hf1 := fetch_seq_at 1 hCode
  have hf2 := fetch_seq_at 2 hCode; have hf3 := fetch_seq_at 3 hCode
  have hf4 := fetch_seq_at 4 hCode; have hf5 := fetch_seq_at 5 hCode
  have hf6 := fetch_seq_at 6 hCode
  have hspAl0 : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hsp0
  have hspAl48 : decide ((s0.sp - 48#64) &&& 15#64 = 0#64) = true :=
    decide_eq_true (beq_iff_eq.mp (spAligned_sub48 hspAl0))
  by_cases hbs : g.bytes = []
  · have hlen0 : BitVec.ofNat 64 g.bytes.length = 0#64 := by simp [hbs]
    apply SepWPp.of_sepWP (mid := fnAddr + 0x5c#64)
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let (by simp only [arm64_norm]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm hsm hpcm hrunm => ?_
    have hspm : sm.sp = s0.sp - 48#64 := by rw [hsm]; simp [arm64_norm]
    have hx19m : sm.readReg64 .x19 = 0#64 := by rw [hsm]; simp [arm64_norm]
    have hx20m : sm.readReg64 .x20 = ret := by rw [hsm]; simp [arm64_norm]
    have hcsm : csUpperPreserved s0 sm := by
      rw [hsm]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      rw [hsm]; simp [calleeSavedVRegs, arm64_norm]
    have htrm : sm.trace = s0.trace := by rw [hsm]; simp [arm64_norm]
    clear hsm
    refine SepWPp.weaken_pre ?_
      (clone_empty_epilogue_gen A callerStk subStk remStk remOff hSplit hCode p ret g r0 r1 r2 R s0 sm
        hbs hsp0 hpcm hrunm hspm hx19m hx20m hcsm hvm htrm)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)
  · have hpos : 0 < g.bytes.length := List.length_pos_iff.mpr hbs
    have hlenNe0 : BitVec.ofNat 64 g.bytes.length ≠ 0#64 := by
      intro h0; have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      change g.bytes.length = 0 at this; omega
    apply sepWPp_of_sepWP_inv hInvStep (mid := fnAddr + 0x1c#64) hinv0
    wp_stp64 hf0 m1 hm1; wp_stp64 hf1 m2 hm2; wp_stp64 hf2 m3 hm3
    wp_step; wp_step; wp_step; wp_step
    refine sepWP_done_let_inv (by simp [arm64_norm, beq_false_of_ne hlenNe0]; try bv_omega)
      (by simp [arm64_norm, hrun]) fun sm0 hsm0 hpcm0 hrunm0 hinvm0 => ?_
    have hspm0 : sm0.sp = s0.sp - 48#64 := by rw [hsm0]; simp [arm64_norm]
    have hx0_m0 : sm0.readReg64 .x0 = p := by rw [hsm0]; simp [arm64_norm, hx0]
    have hx19_m0 : sm0.readReg64 .x19 = BitVec.ofNat 64 g.bytes.length := by
      rw [hsm0]; simp [arm64_norm]
    have hx20_m0 : sm0.readReg64 .x20 = ret := by rw [hsm0]; simp [arm64_norm]
    have hcsm0 : csUpperPreserved s0 sm0 := by
      rw [hsm0]; intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [arm64_norm]
    have hvm0 : calleeSavedVRegs sm0 = calleeSavedVRegs s0 := by
      rw [hsm0]; simp [calleeSavedVRegs, arm64_norm]
    have htrm0 : sm0.trace = s0.trace := by rw [hsm0]; simp [arm64_norm]
    clear hsm0
    refine SepWPp.weaken_pre ?_
      (clone_nonempty_branch_inv hInvStep A callerStk subStk remStk remOff hSplit hCode
        hShim hAlloc hMemcpy hHandleErr
        p ret g r0 r1 r2 R s0 sm0 hinvm0 hpos hlt63 hsp0 hpcm0 hrunm0 hspm0 hx0_m0 hx19_m0 hx20_m0
        hcsm0 hvm0 htrm0)
    exact Entails.of_eq (by
      dsimp only [retPts, savedStack48, vecHdrPts, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x29, Reg.lr]
      sep_ac_rfl)

/-! ## Rebase Decode Fetches and Exported Specializations -/

section RebaseWrappers

attribute [local irreducible]
  CryptoVerification.libsignalSessionCode Program.rebase
  Program.fetch Program.externAt? Program.fnAddr Program.fnOff

local macro "close_fetch " h:ident : tactic =>
  `(tactic| (dsimp only [Nat.reduceMul, List.getElem_cons_zero, List.getElem_cons_succ]; exact $h))

private theorem stringClone_rebase_fetches (b : BitVec 64) (H : String → Option (State → State)) :
    FetchSeq (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName)
      (rustStringCloneInstrs
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName)
        ((libsignalSessionCode.rebase b H).fnAddr shimName)
        ((libsignalSessionCode.rebase b H).fnAddr allocName)
        ((libsignalSessionCode.rebase b H).fnAddr memcpyName)
        ((libsignalSessionCode.rebase b H).fnAddr handleErrorName)) := by
  have hBlShim :
      (libsignalSessionCode.rebase b H).fnAddr shimName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x20#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff shimName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x20#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  have hBlAlloc :
      (libsignalSessionCode.rebase b H).fnAddr allocName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x2c#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff allocName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x2c#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  have hBlMemcpy :
      (libsignalSessionCode.rebase b H).fnAddr memcpyName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x40#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff memcpyName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x40#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  have hBlHandle :
      (libsignalSessionCode.rebase b H).fnAddr handleErrorName -
        ((libsignalSessionCode.rebase b H).fnAddr stringCloneHookName + 0x80#64) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff handleErrorName) -
        (BitVec.ofNat 64 (libsignalSessionCode.fnOff stringCloneHookName) + 0x80#64) := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, sub_add_base_cancel]
  rw [stringCloneName_fnOff] at hBlShim hBlAlloc hBlMemcpy hBlHandle
  dsimp only [shimName] at hBlShim
  rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")] at hBlShim
  dsimp only [allocName] at hBlAlloc
  rw [(ls_stub% "__rustc::__rust_alloc")] at hBlAlloc
  dsimp only [memcpyName] at hBlMemcpy
  rw [(ls_stub% "memcpy")] at hBlMemcpy
  dsimp only [handleErrorName] at hBlHandle
  rw [(ls_stub% "alloc::raw_vec::handle_error")] at hBlHandle
  simp only [BitVec.reduceAdd, BitVec.reduceSub] at hBlShim hBlAlloc hBlMemcpy hBlHandle
  code_fetches CryptoVerification.libsignalSessionCode
    LibsignalBinary.Proofs.Common.StringCloneFlat.scFlatDec b H
    (ls_lemma% fnOff "<alloc::string::String as core::clone::Clone>::clone")
    (ls_off% "<alloc::string::String as core::clone::Clone>::clone") 132
  let hf32 := this
  rename_i hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hf10
    hf11 hf12 hf13 hf14 hf15 hf16 hf17 hf18 hf19 hf20 hf21
    hf22 hf23 hf24 hf25 hf26 hf27 hf28 hf29 hf30 hf31
  intro i hi
  dsimp only [rustStringCloneInstrs, List.length_cons, List.length_nil] at hi
  dsimp only [rustStringCloneInstrs]
  rw [hBlShim, hBlAlloc, hBlMemcpy, hBlHandle]
  dsimp only [stringCloneHookName]
  match i, hi with
  | 0, _ =>
    rw [show BitVec.ofNat 64 (4 * 0) = 0#64 from rfl, BitVec.add_zero]
    dsimp only [List.getElem_cons_zero]
    exact hf0
  | 1, _ => close_fetch hf1
  | 2, _ => close_fetch hf2
  | 3, _ => close_fetch hf3
  | 4, _ => close_fetch hf4
  | 5, _ => close_fetch hf5
  | 6, _ => close_fetch hf6
  | 7, _ => close_fetch hf7
  | 8, _ => close_fetch hf8
  | 9, _ => close_fetch hf9
  | 10, _ => close_fetch hf10
  | 11, _ => close_fetch hf11
  | 12, _ => close_fetch hf12
  | 13, _ => close_fetch hf13
  | 14, _ => close_fetch hf14
  | 15, _ => close_fetch hf15
  | 16, _ => close_fetch hf16
  | 17, _ => close_fetch hf17
  | 18, _ => close_fetch hf18
  | 19, _ => close_fetch hf19
  | 20, _ => close_fetch hf20
  | 21, _ => close_fetch hf21
  | 22, _ => close_fetch hf22
  | 23, _ => close_fetch hf23
  | 24, _ => close_fetch hf24
  | 25, _ => close_fetch hf25
  | 26, _ => close_fetch hf26
  | 27, _ => close_fetch hf27
  | 28, _ => close_fetch hf28
  | 29, _ => close_fetch hf29
  | 30, _ => close_fetch hf30
  | 31, _ => close_fetch hf31
  | 32, _ => close_fetch hf32
  | n + 33, hi => omega

private theorem handle_error_ext_at0 (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr handleErrorName) = some Rust.panicked := by
  have h := panic_at_handle_error_ext b ext handleErrorName 0 (Nat.add_zero _)
  rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h

private theorem imgCallInv_steps {P : Program} {img : Obj.Image} {s s' : State}
    (hs : Steps P s s') (h : ImgCallInv img s) : ImgCallInv img s' :=
  ⟨hs.frozenLoaded h.1, hs.symtab_eq.trans h.2⟩

/-- `<String as Clone>::clone` meets `stringCloneSpec A` on `tripleRatchetProgAtExt b ext` from
`sessionShimSpec`, `rustAllocSpec A`, and `4,096`-byte (`allocHookStack`) `memcpy`. -/
theorem stringClone_4k_ok {b : BitVec 64} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hShim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hAlloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack framelessMemcpySpec allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr stringCloneHookName)
      (stringCloneSpec A) :=
  subroutine_ok_of_withInv_true
    (stringClone_withInv_fetches_ok (fun _ _ => trivial)
      A extHookStack allocHookStack 12240 4096#64 extHookStack_split_48
      (stringClone_rebase_fetches b (Rust.withPanics ext))
      (subroutine_ok_withInv_true (subroutine_ok_withStack_of_subroutine_ok hShim allocHookStack))
      (subroutine_ok_withInv_true hAlloc)
      (subroutine_ok_withInv_true hMemcpy)
      (handle_error_ext_at0 b ext))

/-- `<String as Clone>::clone` meets `(stringCloneSpec A).inImage img` on
`tripleRatchetProgAtExt img.base ext` from `4,096`-byte `.inImage img` extern contracts. -/
theorem stringClone_inImage_4k_ok {img : Obj.Image} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hShim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr shimName)
      ((withStack sessionShimSpec allocHookStack).inImage img))
    (hAlloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocName)
      ((rustAllocSpec A).inImage img))
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((withStack sessionMemcpyRegionSpec allocHookStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr stringCloneHookName)
      ((stringCloneSpec A).inImage img) :=
  stringClone_withInv_fetches_ok imgCallInv_steps
    A extHookStack allocHookStack 12240 4096#64 extHookStack_split_48
    (stringClone_rebase_fetches img.base (Rust.withPanics ext))
    hShim hAlloc hMemcpy (handle_error_ext_at0 img.base ext)

theorem stringClone2x_inImage_of_allocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr stringCloneHookName)
      ((stringCloneSpecWithStack A (2 * extHookStack)).inImage img) :=
  stringClone_withInv_fetches_ok imgCallInv_steps
    A (2 * extHookStack) extHookStack 16336 16384#64 stack2x_split_48
    (stringClone_rebase_fetches img.base (Rust.withPanics ext))
    (hA.shim extHookStack (Nat.le_refl _) (by decide))
    hA.alloc
    (hA.session_memcpy_region extHookStack (Nat.le_refl _) (by decide))
    (handle_error_ext_at0 img.base ext)

end RebaseWrappers

end LibsignalBinary.Proofs.Common.StringCloneFlatX
