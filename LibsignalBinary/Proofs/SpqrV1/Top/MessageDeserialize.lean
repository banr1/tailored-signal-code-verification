/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Base
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Top-Level Verification of `<Message>::deserialize`

Proves the `format_inner` unknown-tag error branch (`0x5f6f0..0x5f780`, `+700..+844`), entry
dispatch, and top-level correctness theorems (`MessageDeserializeOkX`) for
`<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L25

open Lean Meta Elab Term Command Tactic ProofLib ProofLib.CodeLookup
open CryptoVerification.CodeLayout

scoped elab (name := codeFetchesRangeLenDeser) "code_fetches_range_len " codeId:ident decPrefix:ident b:term:max H:term:max
    hfn:ident sym:str k0:num len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches_range $codeId $decPrefix $b $H $hfn $offStx $k0 $len))

scoped syntax:max (name := lsFnXrefDeserStx) "ls_fn_xref% " str num num : term

@[term_elab lsFnXrefDeserStx] meta def elabLsFnXrefDeser : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_fn_xref% $sym:str $k1:num $k2:num) =>
    let codeName := `CryptoVerification.libsignalSessionCode
    let treeName := `CryptoVerification.libsignalSessionCode_tree
    let eOff ← lookup codeName .fnOff sym.getString
    let v ← xrefTarget treeName (eOff.val + k1.getNat) (some (eOff.val + k2.getNat))
    elabTerm (Syntax.mkNumLit (toString v)) expectedType?
  | _ => throwUnsupportedSyntax

end CryptoVerification.SpqrV1.Layout.L25

namespace CryptoVerification.SpqrV1.Top.MessageDeserialize

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open ChainFromVNNorm
open CryptoVerification.LibsignalSpqr
open CryptoVerification.SpqrV1.Layout.L25

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  msgDeserialize_fnOff
  (ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::deserialize")

theorem formatInner_fnOff :
    libsignalSessionCode.fnOff formatInnerName = ls_off% "alloc::fmt::format::format_inner" :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "alloc::fmt::format::format_inner")

theorem dealloc_fnOff :
    libsignalSessionCode.fnOff deallocName = ls_off% "__rustc::__rust_dealloc" :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_dealloc")

theorem add_one_beq_zero_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 : cap = 0xffffffffffffffff#64 := by bv_omega
  subst h1
  revert h; decide

theorem vecU8_live_entails_dealloc (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (cap : BitVec 64) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  have hm1 := pointsToBytes_entails_memRegion ptr bs
  have hm2 : memRegion ptr bs.length ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
      memRegion ptr cap.toNat := by
    rw [← ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
      (N := cap.toNat) (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)]
  rw [← hm2]
  exact sepConj_mono_right (sepConj_mono_left hm1)

theorem stackAt_extHookStack_split_alloc (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12288 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 12288 (by decide)

/-- Framed call rule for `formatInnerSpec A` inside `SepWPp` when the continuation after
    `format_inner` does not panic (`SepWP`). -/
theorem SepWPp.call_formatInner_then_sepWP {prog : Program} {A : RustAlloc}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (formatInnerSpec A))
    (ret sp_cur : BitVec 64) {s0 s : State} {P F R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = ret)
    (hP : P = (memRegion ret 24 ∗ A.pool ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ (sf : State) (bs : List (BitVec 8)) (cap ptr : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWP prog target_pc sf
        (((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool ∗ stackAt sp_cur extHookStack) ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have halign : s.spAligned = true := by dsimp only [State.spAligned]; rw [hsp]; exact hsp_align
  refine SepWPp.call (x := ret) (F := F) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [formatInnerSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx8, ?_⟩
    rwa [← sepConj_assoc, ← hP]
  · intro sm _ R' _ hpost
    dsimp only [formatInnerSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm _ hm'
    exact Satisfies.mono (sepConj_mono_left (onPanic_entails_of_trace_eq htr)) hm'
  · intro sm hpcm hrunm hspm hcsm R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [formatInnerSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [htr] at htrm
    rw [hsp] at hspm
    dsimp only [vecU8, vecU8At, vecHeader] at hpost
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨bs, cap, ptr, hpost⟩
    have hpost' : sm.mem ⊨
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((((ret ↦₆₄ cap) ∗ ((ret + 8#64) ↦₆₄ ptr) ∗ ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0#64 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          A.pool ∗ stackAt sp_cur extHookStack) ∗ F) ∗ R') := by
      refine Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨⟨hle, hlt, hptr⟩, hpost'⟩
    exact (SepWPp.of_sepWP_ret (hnext sm bs cap ptr hpcm hrunm hspm htrm hcsm hle hlt hptr)) R' hpost' hL
  · intro sm R' _ hpost
    dsimp only [formatInnerSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

/-- Framed call rule for `rustDeallocSpec A` inside `SepWP` using `extHookStack`. -/
theorem SepWP.call_dealloc {prog : Program} {A : RustAlloc}
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustDeallocSpec A))
    (ptr sp_cur : BitVec 64) (size : Nat) {s0 s : State} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_cur)
    (hsp_align : (sp_cur &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = 1)
    (hP : P = (A.live ptr size 1 ∗ memRegion ptr size ∗ A.pool ∗ stackAt sp_cur extHookStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_cur → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf ((A.pool ∗ stackAt sp_cur extHookStack) ∗ F) post) :
    SepWP prog target_pc s P post := by
  let F_ext := memRegion (sp_cur - 16384#64) 12288 ∗ F
  have halign : s.spAligned = true := by dsimp only [State.spAligned]; rw [hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame (x := (ptr, size, 1)) (F := F_ext) hcall hpc hrun halign hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [hP, stackAt_extHookStack_split_alloc sp_cur] at hm
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [F_ext]; ac_rfl
  · intro R' sm _ hpost
    dsimp only [rustDeallocSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro R' code sm _ hpost
    dsimp only [rustDeallocSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm
    unfold SepWP
    intro R' hpost hL
    rw [sepConj_assoc] at hpost
    dsimp only [rustDeallocSpec] at hpost
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [htr] at htrm
    rw [hsp] at hspm
    have hpost' : sm.mem ⊨ ((A.pool ∗ stackAt sp_cur extHookStack) ∗ F) ∗ R' := by
      rw [stackAt_extHookStack_split_alloc sp_cur]
      refine Satisfies.mono (Entails.of_eq ?_) hpost
      dsimp only [F_ext]; ac_rfl
    have hnext' := hnext sm hpcm hrunm hspm htrm hcsm
    unfold SepWP at hnext'
    exact hnext' R' hpost' hL
  · intro R' sm _ hpost
    dsimp only [rustDeallocSpec] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

set_option maxHeartbeats 1600000 in
/-- Error branch for invalid tag `tag > 6` (`0x5f6f0..0x5f780`, `+700..+844`, 37 insns): calls
    `alloc::fmt::format::format_inner` (`0x78ae8`), drops the formatted `String` via
    `__rustc::__rust_dealloc` (`0x78a28`) if `cap ≠ 0`, writes `Error::MsgDecode` (`0xff` at
    `+0x08`, `2` at `+0x10`), restores callee-saved registers and stack, and returns. -/
theorem step_err_fmt (P_poly : PolyApi) (base : BitVec 64) (ext : String → Option (State → State))
    (A : RustAlloc)
    (hFmt : subroutine_ok (tripleRatchetProgAtExt base ext)
      ((tripleRatchetProgAtExt base ext).fnAddr formatInnerName) (formatInnerSpec A))
    (hDealloc : subroutine_ok (tripleRatchetProgAtExt base ext)
      ((tripleRatchetProgAtExt base ext).fnAddr deallocName) (rustDeallocSpec A))
    (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode)
    (hpc : s.pc = (tripleRatchetProgAtExt base ext).fnAddr messageDeserializeName + 700#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hsp_align : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hcs_hi : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .x29) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWPp (tripleRatchetProgAtExt base ext) (s0.readReg64 .lr) s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly A).onPanic call s0 sf ∗ R)) := by
  unfold tripleRatchetProgAtExt at hFmt hDealloc hpc ⊢
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base (Rust.withPanics ext) msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 700 148
  have h_fmt := sub_ok_at_rebase (name := messageDeserializeName) (callee := formatInnerName)
    (k := num% (ls_rel% "<spqr::v1::chunked::states::Message>::deserialize" "alloc::fmt::format::format_inner"))
    (by rw [msgDeserialize_fnOff, formatInner_fnOff]) hFmt
  have h_dealloc := sub_ok_at_rebase (name := messageDeserializeName) (callee := deallocName)
    (k := num% (ls_rel% "<spqr::v1::chunked::states::Message>::deserialize" "__rustc::__rust_dealloc"))
    (by rw [msgDeserialize_fnOff, dealloc_fnOff]) hDealloc
  clear hFmt hDealloc
  have hsp_sub_align : (s0.sp - 144#64 &&& 15#64 == 0#64) = true := sp_sub_144_aligned s0 hsp_align
  rcases hcs_hi with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  subst hP hpost
  unfold msgDeserFramePad msgDeserScratchAt msgDeserSavedAt
  dsimp only [messageDeserializeName] at hpc h_fmt h_dealloc ⊢
  generalize_entry
    (libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::Message>::deserialize" = entry
  generalize_entry
    (libsignalSessionCode.rebase base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  refine SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::states::Message>::deserialize" "alloc::fmt::format::format_inner")) ?_
  wp_steps
  refine SepWP.fold (msgDeser_fmt_slot_fold s0.sp f08 f10 f18) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  apply (SepWPp.call_formatInner_then_sepWP h_fmt (s0.sp - 136#64) (s0.sp - 144#64) (s0 := s0))
  · wp_focus_close wp_norm_goal
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · exact hsp_sub_align
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · sep_focus
  · intro s1 bs cap ptr hpc1 hrun1 hsp1 htr1 hcs1 hle hlt hptr
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    have ha8 : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_omega
    have ha16 : s0.sp - 136#64 + 16#64 = s0.sp - 120#64 := by bv_omega
    rw [ha8, ha16]
    by_cases hcap : cap = 0#64
    · subst hcap
      simp only [↓reduceIte, emp_sepConj]
      refine SepWP.fold (pointsTo64_entails_byte_memRegion7 s0.sp ptr) (by sep_focus) ?_
      refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
        (by sep_focus) ?_
      wp_steps
      dsimp only [messageDeserializeSpecX]
      rw [herr]
      dsimp only [messageResultAt]
      refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
      refine SepWP.fold (msgDeser_stack_restore s0.sp 0#64 (ptr.extractLsb' 0 8)
        (BitVec.ofNat 64 bs.length) st3 st4 st5 st6 st0 st1 fb0
        (s0.sp - 68#64) ((entry + 704#64 &&& 18446744073709547520#64) +
          bv% (ls_fn_xref% "<spqr::v1::chunked::states::Message>::deserialize" 704 708 -
            page% (ls_off% "<spqr::v1::chunked::states::Message>::deserialize" + 704)))
        (s0.readReg64 .x29) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by unfold msgDeserFramePad msgDeserScratchAt msgDeserSavedAt; sep_focus) ?_
      wp_done
    · have hcbz : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      have hcmn : (cap + 1#64 == 0#64) = false := add_one_beq_zero_of_lt hlt
      simp only [hcap, ↓reduceIte]
      wp_steps
      refine SepWP.fold (vecU8_live_entails_dealloc A ptr bs cap hle hlt) (by sep_focus) ?_
      apply (SepWP.call_dealloc h_dealloc ptr (s0.sp - 144#64) cap.toNat (s0 := s0))
      · wp_focus_close wp_norm_goal
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · exact hsp_sub_align
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · wp_focus_close wp_norm_lhs
      · sep_focus
      · intro s2 hpc2 hrun2 hsp2 htr2 hcs2
        rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
        simp only [arm64_norm, wp_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2
        refine SepWP.fold (pointsTo64_entails_byte_memRegion7 s0.sp ptr) (by sep_focus) ?_
        refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
          (by sep_focus) ?_
        wp_steps
        dsimp only [messageDeserializeSpecX]
        rw [herr]
        dsimp only [messageResultAt]
        refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
        refine SepWP.fold (msgDeser_stack_restore s0.sp cap (ptr.extractLsb' 0 8)
          (BitVec.ofNat 64 bs.length) st3 st4 st5 st6 st0 st1 fb0
          (s0.sp - 68#64) ((entry + 704#64 &&& 18446744073709547520#64) +
            bv% (ls_fn_xref% "<spqr::v1::chunked::states::Message>::deserialize" 704 708 -
              page% (ls_off% "<spqr::v1::chunked::states::Message>::deserialize" + 704)))
          (s0.readReg64 .x29) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by unfold msgDeserFramePad msgDeserScratchAt msgDeserSavedAt; sep_focus) ?_
        wp_done

/-! ## Top-Level Entry Dispatch and `MessageDeserializeOkX` -/

theorem tag_cases (tag : BitVec 8) :
    tag = 0#8 ∨ tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨
      tag = 4#8 ∨ tag = 5#8 ∨ tag = 6#8 ∨ 6 < tag.toNat := by
  by_cases h0 : tag = 0#8; · exact Or.inl h0
  by_cases h1 : tag = 1#8; · exact Or.inr (Or.inl h1)
  by_cases h2 : tag = 2#8; · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : tag = 3#8; · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : tag = 4#8; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  by_cases h5 : tag = 5#8; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  by_cases h6 : tag = 6#8; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6))))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
  have h0' : tag.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have h1' : tag.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
  have h2' : tag.toNat ≠ 2 := fun h => h2 (BitVec.eq_of_toNat_eq h)
  have h3' : tag.toNat ≠ 3 := fun h => h3 (BitVec.eq_of_toNat_eq h)
  have h4' : tag.toNat ≠ 4 := fun h => h4 (BitVec.eq_of_toNat_eq h)
  have h5' : tag.toNat ≠ 5 := fun h => h5 (BitVec.eq_of_toNat_eq h)
  have h6' : tag.toNat ≠ 6 := fun h => h6 (BitVec.eq_of_toNat_eq h)
  omega

theorem deserialize_err_of_gt_6 (P : PolyApi) (epoch : Epoch) (tag : BitVec 8)
    (rest : List (BitVec 8)) (htag : 6 < tag.toNat) :
    Message.deserialize P epoch (tag :: rest) = .error .msgDecode := by
  have h0 : (tag == 0#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h1 : (tag == 1#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h2 : (tag == 2#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h3 : (tag == 3#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h4 : (tag == 4#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h5 : (tag == 5#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  have h6 : (tag == 6#8) = false := by rw [beq_eq_false_iff_ne]; intro rfl; revert htag; decide
  unfold Message.deserialize MessageType.tryFromU8
  simp [h0, h1, h2, h3, h4, h5, h6]

theorem ofNat_cons_length_beq_zero (tag : BitVec 8) (rest : List (BitVec 8))
    (hlen : (tag :: rest).length < 2 ^ 63) :
    (BitVec.ofNat 64 (tag :: rest).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h0 : (BitVec.ofNat 64 (tag :: rest).length).toNat = 0 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0
  simp at h0

theorem toNat_sub_five_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    (BitVec.zeroExtend 32 tag - 5#32).toNat = tag.toNat - 5 := by
  have hle : 5#32 ≤ BitVec.zeroExtend 32 tag := by
    rw [BitVec.le_def]
    change 5 ≤ (BitVec.zeroExtend 32 tag).toNat
    rw [BitVec.toNat_setWidth_of_le (by decide)]
    omega
  rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_setWidth_of_le (by decide)]
  rfl

@[local simp, local arm64_norm, local wp_norm]
theorem ule_five_64_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ule 5#64 (BitVec.zeroExtend 64 tag) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  change 5 ≤ (BitVec.zeroExtend 64 tag).toNat
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ule_five_32_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ule 5#32 (BitVec.zeroExtend 32 tag) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  change 5 ≤ (BitVec.zeroExtend 32 tag).toNat
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_five_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ult (BitVec.zeroExtend 32 tag) 5#32 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  change ¬ (BitVec.zeroExtend 32 tag).toNat < 5
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ule_sub_five_one_32_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ule (BitVec.zeroExtend 32 tag - 5#32) 1#32 = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
  change ¬ (BitVec.zeroExtend 32 tag - 5#32).toNat ≤ 1
  rw [toNat_sub_five_of_gt_6 tag htag]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_one_sub_five_32_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ult 1#32 (BitVec.zeroExtend 32 tag - 5#32) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  change 1 < (BitVec.zeroExtend 32 tag - 5#32).toNat
  rw [toNat_sub_five_of_gt_6 tag htag]
  omega

@[local simp, local arm64_norm, local wp_norm]
theorem ult_one_sub_five_64_of_gt_6 (tag : BitVec 8) (htag : 6 < tag.toNat) :
    BitVec.ult 1#64 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 tag - 5#32)) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  change 1 < (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 tag - 5#32)).toNat
  rw [BitVec.toNat_setWidth_of_le (by decide), toNat_sub_five_of_gt_6 tag htag]
  omega

theorem memRegion_48_eq_rawOutBufAt (out : BitVec 64) :
    memRegion out 48 =
      ∃∗ idx16 : BitVec 16, ∃∗ c6 : BitVec 64, ∃∗ c5 : BitVec 64,
      ∃∗ c4 : BitVec 8, ∃∗ c3 : BitVec 64, ∃∗ c2 : BitVec 8,
      ∃∗ c1 : BitVec 16, ∃∗ c0 : BitVec 32, ∃∗ b9 : BitVec 8,
      ∃∗ b8 : BitVec 8, ∃∗ w0 : BitVec 64,
        rawOutBufAt out w0 b8 b9 c0 c1 c2 c3 c4 c5 c6 idx16 := by
  rw [memRegion_48_ok_split out]
  simp only [rawOutBufAt, chunk32AtomsAt, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem spqrPolyApi_chunkLaw : PolyApiChunkLaw spqrPolyApi :=
  fun _ _ => ⟨rfl, rfl⟩

/-- Entry dispatch for `call.fromBytes = []` (`+0: cbz x3, +144` → `+144..+160`). -/
theorem step_entry_empty (P_poly : PolyApi) (base : BitVec 64)
    (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hempty : call.fromBytes = [])
    (hpc : s0.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = call.out)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      stackAt s0.sp messageDeserializeStackX) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s0 P post := by
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base hooks msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 0 4
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base hooks msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 144 20
  have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
    rw [hempty]; rfl
  have hx3_0 : s0.readReg64 .x3 = 0#64 := by rw [hx3, hempty]; rfl
  subst hP hpost
  dsimp only [messageDeserializeName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  refine SepWP.fold (rawOutBufAt_entails_err_split call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a)
    (by sep_focus) ?_
  wp_steps
  dsimp only [messageDeserializeSpecX]
  rw [herr]
  dsimp only [messageResultAt]
  refine SepWP.fold (fold_messageErrorAt_region call.out) (by sep_focus) ?_
  wp_done

set_option maxHeartbeats 1200000 in
/-- Entry dispatch for `call.fromBytes = tag :: rest` with `6 < tag.toNat` (`+0..+36` →
    `+164..+168` → `+700..+844`). -/
theorem step_entry_tag_gt_6 (P_poly : PolyApi) (base : BitVec 64)
    (ext : String → Option (State → State))
    (A : RustAlloc)
    (hFmt : subroutine_ok (tripleRatchetProgAtExt base ext)
      ((tripleRatchetProgAtExt base ext).fnAddr formatInnerName) (formatInnerSpec A))
    (hDealloc : subroutine_ok (tripleRatchetProgAtExt base ext)
      ((tripleRatchetProgAtExt base ext).fnAddr deallocName) (rustDeallocSpec A))
    (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s29 s30 s22 s21 s20 s19 : BitVec 64)
    (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hbytes : call.fromBytes = tag :: rest)
    (htag : 6 < tag.toNat)
    (hlen : call.fromBytes.length < 2 ^ 63)
    (hpc : s0.pc = (libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr messageDeserializeName)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = call.out)
    (hx2 : s0.readReg64 .x2 = call.fromPtr)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp s29 s30 s22 s21 s20 s19) :
    SepWPp (libsignalSessionCode.rebase base (Rust.withPanics ext)) (s0.readReg64 .lr)
      s0 P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (messageDeserializeSpecX P_poly A).onPanic call s0 sf ∗ R)) := by
  have hlen' : (tag :: rest).length < 2 ^ 63 := hbytes ▸ hlen
  have hcbz : (BitVec.ofNat 64 (tag :: rest).length == 0#64) = false :=
    ofNat_cons_length_beq_zero tag rest hlen'
  have h1 := ule_five_64_of_gt_6 tag htag
  have h2 := ule_five_32_of_gt_6 tag htag
  have h3 := ult_five_of_gt_6 tag htag
  have h4 := ule_sub_five_one_32_of_gt_6 tag htag
  have h5 := ult_one_sub_five_32_of_gt_6 tag htag
  have h6 := ult_one_sub_five_64_of_gt_6 tag htag
  have herr : Message.deserialize P_poly call.epoch call.fromBytes = .error .msgDecode := by
    rw [hbytes]; exact deserialize_err_of_gt_6 P_poly call.epoch tag rest htag
  have h_cont := step_err_fmt P_poly base ext A hFmt hDealloc call
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
    f08 f10 f18 st3 st4 st5 st6 st0 st1 tag f50 f58 s0
  unfold tripleRatchetProgAtExt at h_cont
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base (Rust.withPanics ext) msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 0 40
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base (Rust.withPanics ext) msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 164 8
  subst hP
  rw [hbytes, pointsToBytes_cons]
  rw [hbytes] at hx3
  unfold msgDeserScratchAt msgDeserSavedAt
  dsimp only [messageDeserializeName] at h_cont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP (mid := entry + 700#64) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  apply h_cont _ _ R post hpost herr
  · wp_focus_close wp_norm_goal
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · exact hsp_align
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · wp_focus_close wp_norm_lhs
  · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
  · rw [hbytes, pointsToBytes_cons]
    unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl

set_option maxHeartbeats 1200000 in
/-- Direct `Ok` epilogue (`0x5f680..0x5f6c8`, `+588..+660`) for non-chunk tags (`0#8`, `4#8`)
    where `x10` holds an arbitrary value rather than `c2.zeroExtend 64`. -/
theorem step_ok_tail_direct (P_poly : PolyApi) (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall)
    (tag : BitVec 8)
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hok : ∀ (c2 : BitVec 8) (idx16 : BitVec 16),
      rawOkOutAt call.out call.epoch tag st0 st1 c2 st3 st4 st5 st6 idx16 ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes))
    (hpc : s.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName + 588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64)
    (hs0A : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = call.out)
    (hx1 : s.readReg64 .x1 = call.epoch)
    (hx8 : s.readReg64 .x8 = tag.zeroExtend 64)
    (hx29 : s.readReg64 .fp = s0.sp - 48#64)
    (hcs : DeserHighCalleeSaved s0 s)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s P post := by
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base hooks msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 588 76
  have hspA : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_144_aligned s0 hs0A
  rcases hcs with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
  subst hP hpost
  dsimp only [messageDeserializeName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  unfold rawOutBufAt chunk32AtomsAt msgDeserScratchAt msgDeserSavedAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 5
  have hswap_st : (((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5)) ⊢
      ((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5) := by
    have h1 := byte_word64_swap (s0.sp - 104#64) st4 st5
    have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
    have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
    rw [ha1, ha8] at h1
    exact Entails.of_eq h1
  have hunswap_st : (((s0.sp - 104#64) ↦₆₄ shiftWord st4 st5) ∗ ((s0.sp - 96#64) ↦₈ hiByte st5)) ⊢
      ((s0.sp - 104#64) ↦₈ st4) ∗ ((s0.sp - 103#64) ↦₆₄ st5) := by
    have h1 := (byte_word64_swap (s0.sp - 104#64) st4 st5).symm
    have ha1 : s0.sp - 104#64 + 1#64 = s0.sp - 103#64 := by bv_omega
    have ha8 : s0.sp - 104#64 + 8#64 = s0.sp - 96#64 := by bv_omega
    rw [ha1, ha8] at h1
    exact Entails.of_eq h1
  refine SepWP.fold hswap_st (by sep_focus) ?_
  wp_steps 1
  refine SepWP.fold hunswap_st (by sep_focus) ?_
  wp_steps 5
  have hswap_out : (((call.out + 25#64) ↦₈ oc4) ∗ ((call.out + 26#64) ↦₆₄ oc5)) ⊢
      ((call.out + 25#64) ↦₆₄ shiftWord oc4 oc5) ∗ ((call.out + 33#64) ↦₈ hiByte oc5) := by
    have h1 := byte_word64_swap (call.out + 25#64) oc4 oc5
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
    exact Entails.of_eq h1
  refine SepWP.fold hswap_out (by sep_focus) ?_
  wp_steps 1
  have hunswap_out : (((call.out + 25#64) ↦₆₄ shiftWord st4 st5) ∗ ((call.out + 33#64) ↦₈ hiByte oc5)) ⊢
      ((call.out + 25#64) ↦₈ st4) ∗ ((call.out + 26#64) ↦₆₄ unshiftWord (shiftWord st4 st5) (hiByte oc5)) := by
    have h1 := shiftWord_byte_swap (call.out + 25#64) st4 st5 (hiByte oc5)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
    exact Entails.of_eq h1
  refine SepWP.fold hunswap_out (by sep_focus) ?_
  wp_steps
  dsimp only [messageDeserializeSpecX]
  let c2_val : BitVec 8 := BitVec.zeroExtend 8 (s.readReg64 (Reg.gpr 10#5))
  let idx16_val : BitVec 16 := BitVec.truncate 16 (BitVec.truncate 32 (s.readReg64 (Reg.gpr 9#5)))
  have hfold_ok :
      ((call.out ↦₆₄ call.epoch) ∗ ((call.out + 8#64) ↦₈ tag) ∗ ((call.out + 9#64) ↦₈ 1#8) ∗
        ((call.out + 10#64) ↦₃₂ st0) ∗ ((call.out + 14#64) ↦₁₆ st1) ∗
        ((call.out + 16#64) ↦₈ c2_val) ∗
        ((call.out + 17#64) ↦₆₄ st3) ∗ ((call.out + 25#64) ↦₈ st4) ∗
        ((call.out + 26#64) ↦₆₄ st5) ∗ ((call.out + 34#64) ↦₆₄ st6) ∗
        ((call.out + 42#64) ↦₁₆ idx16_val) ∗
        memRegion (call.out + 44#64) 4) ⊢
      messageResultAt P_poly call.out (Message.deserialize P_poly call.epoch call.fromBytes) := by
    refine Entails.trans ?_ (hok c2_val idx16_val)
    unfold rawOkOutAt chunk32AtomsAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.fold hfold_ok (by sep_focus) ?_
  refine SepWP.fold (msgDeser_stack_restore s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by
    unfold msgDeserScratchAt msgDeserSavedAt
    sep_focus) ?_
  wp_done

set_option maxHeartbeats 1600000 in
/-- Entry dispatch for `call.fromBytes = tag :: rest` with `tag ∈ {0#8, 1#8, 2#8, 3#8, 4#8, 5#8,
    6#8}`. -/
theorem step_entry_tag_le_6 (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (call : MessageDeserializeCall) (tag : BitVec 8) (rest : List (BitVec 8))
    (o0 : BitVec 64) (o8 o9 : BitVec 8)
    (oc0 : BitVec 32) (oc1 : BitVec 16) (oc2 : BitVec 8)
    (oc3 : BitVec 64) (oc4 : BitVec 8) (oc5 oc6 : BitVec 64) (o2a : BitVec 16)
    (f08 : BitVec 64) (f10 : BitVec 8) (f18 : BitVec 64)
    (st3 : BitVec 64) (st4 : BitVec 8) (st5 st6 : BitVec 64)
    (st0 : BitVec 32) (st1 : BitVec 16) (fb0 : BitVec 8) (f50 f58 : BitVec 64)
    (s29 s30 s22 s21 s20 s19 : BitVec 64)
    (s0 : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageDeserializeSpecX P_poly A).post call s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (hbytes : call.fromBytes = tag :: rest)
    (htag : tag = 0#8 ∨ tag = 1#8 ∨ tag = 2#8 ∨ tag = 3#8 ∨
      tag = 4#8 ∨ tag = 5#8 ∨ tag = 6#8)
    (hlen : call.fromBytes.length < 2 ^ 63)
    (hpc : s0.pc = (libsignalSessionCode.rebase base hooks).fnAddr messageDeserializeName)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = call.out)
    (hx1 : s0.readReg64 .x1 = call.epoch)
    (hx2 : s0.readReg64 .x2 = call.fromPtr)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length)
    (hP : P =
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      rawOutBufAt call.out o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a ∗
      A.pool ∗
      msgDeserFramePad s0.sp ∗
      msgDeserScratchAt s0.sp f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58 ∗
      msgDeserSavedAt s0.sp s29 s30 s22 s21 s20 s19) :
    SepWP (libsignalSessionCode.rebase base hooks) (s0.readReg64 .lr) s0 P post := by
  have hlen' : (tag :: rest).length < 2 ^ 63 := hbytes ▸ hlen
  have hcbz : (BitVec.ofNat 64 (tag :: rest).length == 0#64) = false :=
    ofNat_cons_length_beq_zero tag rest hlen'
  have h_ok0 := step_ok_tail_direct P_poly base hooks A call 0#8
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 0#8 f50 f58 s0
  have h_ok4 := step_ok_tail_direct P_poly base hooks A call 4#8
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 4#8 f50 f58 s0
  have h_pre3 := step_varint_pre_3 P_poly hPoly base hooks A call 3#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 3#8 f50 f58 s0
  have h_pre1 := step_varint_pre_1 P_poly hPoly base hooks A call 1#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 1#8 f50 f58 s0
  have h_pre2 := step_varint_pre_2 P_poly hPoly base hooks A call 2#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 f10 f18 st3 st4 st5 st6 st0 st1 2#8 f50 f58 s0
  have h_pre5 := step_varint_pre_5 P_poly hPoly base hooks A call 5#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 5#8 f18 st3 st4 st5 st6 st0 st1 5#8 f50 f58 s0
  have h_pre6 := step_varint_pre_6 P_poly hPoly base hooks A call 6#8 rest
    o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a f08 6#8 f18 st3 st4 st5 st6 st0 st1 6#8 f50 f58 s0
  unfold VarintPreStmt at h_pre3 h_pre1 h_pre2 h_pre5 h_pre6
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base hooks msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 0 64
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base hooks msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 164 32
  code_fetches_range_len libsignalSessionCode libsignalSessionBin base hooks msgDeserialize_fnOff "<spqr::v1::chunked::states::Message>::deserialize" 276 8
  subst hP
  rw [hbytes, pointsToBytes_cons]
  rw [hbytes] at hx3
  unfold msgDeserScratchAt msgDeserSavedAt
  dsimp only [messageDeserializeName] at h_ok0 h_ok4 h_pre3 h_pre1 h_pre2 h_pre5 h_pre6 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase base hooks).fnAddr
    "<spqr::v1::chunked::states::Message>::deserialize" = entry
  examples_hide_fetches
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · wp_steps
    apply h_ok0 _ _ R post hpost
    · intro c2 idx16
      have hres : Message.deserialize P_poly call.epoch call.fromBytes =
          .ok { epoch := call.epoch, payload := .none } := by rw [hbytes]; rfl
      rw [hres]; dsimp only [messageResultAt]
      exact rawOkOutAt_entails_none P_poly call.out call.epoch st0 st1 c2 st3 st4 st5 st6 idx16
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl
  · wp_steps
    have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
        deserAfterVarint P_poly call.epoch 1#8 (decodeVarintLoop 0 0#64 rest) := by
      rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 1#8 rest (Or.inl rfl),
        decodeVarintLoop_eq_spqrVarintAux]
      rfl
    apply h_pre1 _ _ R post hpost (Or.inl rfl) hbytes hlen hdeser
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rw [hbytes]; wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl
  · wp_steps
    have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
        deserAfterVarint P_poly call.epoch 2#8 (decodeVarintLoop 0 0#64 rest) := by
      rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 2#8 rest (Or.inr (Or.inl rfl)),
        decodeVarintLoop_eq_spqrVarintAux]
      rfl
    apply h_pre2 _ _ R post hpost (Or.inr (Or.inl rfl)) hbytes hlen hdeser
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rw [hbytes]; wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl
  · wp_steps
    have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
        deserAfterVarint P_poly call.epoch 3#8 (decodeVarintLoop 0 0#64 rest) := by
      rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 3#8 rest (Or.inr (Or.inr (Or.inl rfl))),
        decodeVarintLoop_eq_spqrVarintAux]
      rfl
    apply h_pre3 _ _ R post hpost (Or.inr (Or.inr (Or.inl rfl))) hbytes hlen hdeser
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rw [hbytes]; wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl
  · wp_steps
    apply h_ok4 _ _ R post hpost
    · intro c2 idx16
      have hres : Message.deserialize P_poly call.epoch call.fromBytes =
          .ok { epoch := call.epoch, payload := .ct1Ack true } := by rw [hbytes]; rfl
      rw [hres]; dsimp only [messageResultAt]
      exact rawOkOutAt_entails_ct1Ack P_poly call.out call.epoch st0 st1 c2 st3 st4 st5 st6 idx16
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl
  · wp_steps
    have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
        deserAfterVarint P_poly call.epoch 5#8 (decodeVarintLoop 0 0#64 rest) := by
      rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 5#8 rest (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        decodeVarintLoop_eq_spqrVarintAux]
      rfl
    apply h_pre5 _ _ R post hpost (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hbytes hlen hdeser
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rw [hbytes]; wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl
  · wp_steps
    have hdeser : Message.deserialize P_poly call.epoch call.fromBytes =
        deserAfterVarint P_poly call.epoch 6#8 (decodeVarintLoop 0 0#64 rest) := by
      rw [hbytes, deserialize_eq_deserAfterVarint P_poly call.epoch 6#8 rest (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        decodeVarintLoop_eq_spqrVarintAux]
      rfl
    apply h_pre6 _ _ R post hpost (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hbytes hlen hdeser
    · wp_focus_close wp_norm_goal
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact hsp_align
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · rw [hbytes]; wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · wp_focus_close wp_norm_lhs
    · exact ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
    · rw [hbytes, pointsToBytes_cons]
      unfold msgDeserScratchAt msgDeserSavedAt; ac_rfl

attribute [local irreducible] rawOutBufAt msgDeserFramePad msgDeserScratchAt
  msgDeserSavedAt messageResultAt Message.deserialize

set_option maxHeartbeats 1600000 in
/-- Entry-point verification of `<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434`,
    212 insns) on `tripleRatchetProgAtExt base ext`. -/
theorem messageDeserialize_ok_ext (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (base : BitVec 64) (ext : String → Option (State → State)) (A : RustAlloc)
    (hFmt : subroutine_ok (tripleRatchetProgAtExt base ext)
      ((tripleRatchetProgAtExt base ext).fnAddr formatInnerName) (formatInnerSpec A))
    (hDealloc : subroutine_ok (tripleRatchetProgAtExt base ext)
      ((tripleRatchetProgAtExt base ext).fnAddr deallocName) (rustDeallocSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt base ext)
      ((tripleRatchetProgAtExt base ext).fnAddr messageDeserializeName)
      (messageDeserializeSpecX P_poly A) := by
  unfold tripleRatchetProgAtExt
  apply subroutine_ok_of_sepWPp
  intro call R s0 hpc hrun hpre hsp_align
  change s0.mem ⊨
    (⌜s0.readReg64 .x0 = call.out ∧
      s0.readReg64 .x1 = call.epoch ∧
      s0.readReg64 .x2 = call.fromPtr ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 call.fromBytes.length ∧
      call.fromBytes.length < 2 ^ 63⌝ ∗
     (memRegion call.out 48 ∗
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      A.pool ∗
      stackAt s0.sp messageDeserializeStackX)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen⟩, hpre⟩
  refine ⟨memRegion call.out 48 ∗
      (call.fromPtr ↦ₛ call.fromBytes) ∗
      A.pool ∗
      stackAt s0.sp messageDeserializeStackX, R, hpre, ?_⟩
  refine SepWPp.rw_pre (by
    simp only [memRegion_48_eq_rawOutBufAt call.out, sepExists_sepConj_left]
    rfl) ?_
  apply SepWPp.exists_elim; intro o2a
  apply SepWPp.exists_elim; intro oc6
  apply SepWPp.exists_elim; intro oc5
  apply SepWPp.exists_elim; intro oc4
  apply SepWPp.exists_elim; intro oc3
  apply SepWPp.exists_elim; intro oc2
  apply SepWPp.exists_elim; intro oc1
  apply SepWPp.exists_elim; intro oc0
  apply SepWPp.exists_elim; intro o9
  apply SepWPp.exists_elim; intro o8
  apply SepWPp.exists_elim; intro o0
  have hbytes_cases : call.fromBytes = [] ∨ ∃ tag rest, call.fromBytes = tag :: rest := by
    cases call.fromBytes with
    | nil => exact Or.inl rfl
    | cons t r => exact Or.inr ⟨t, r, rfl⟩
  rcases hbytes_cases with hbytes | ⟨tag, rest, hbytes⟩
  · apply SepWPp.of_sepWP_ret
    exact step_entry_empty P_poly base (Rust.withPanics ext) A call
      o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a s0 _ R _ rfl
      hbytes hpc hrun hx0 hx3 (by ac_rfl)
  · refine SepWPp.rw_pre (by
      simp only [stackAt_msgDeser_split s0.sp, sepExists_sepConj_right]
      rfl) ?_
    apply SepWPp.exists_elim; intro s19
    apply SepWPp.exists_elim; intro s20
    apply SepWPp.exists_elim; intro s21
    apply SepWPp.exists_elim; intro s22
    apply SepWPp.exists_elim; intro s30
    apply SepWPp.exists_elim; intro s29
    apply SepWPp.exists_elim; intro f58
    apply SepWPp.exists_elim; intro f50
    apply SepWPp.exists_elim; intro fb0
    apply SepWPp.exists_elim; intro st1
    apply SepWPp.exists_elim; intro st0
    apply SepWPp.exists_elim; intro st6
    apply SepWPp.exists_elim; intro st5
    apply SepWPp.exists_elim; intro st4
    apply SepWPp.exists_elim; intro st3
    apply SepWPp.exists_elim; intro f18
    apply SepWPp.exists_elim; intro f10
    apply SepWPp.exists_elim; intro f08
    rcases tag_cases tag with h0 | h1 | h2 | h3 | h4 | h5 | h6 | hgt6
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6 P_poly hPoly base (Rust.withPanics ext) A call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inl h0) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6 P_poly hPoly base (Rust.withPanics ext) A call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inl h1)) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6 P_poly hPoly base (Rust.withPanics ext) A call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inl h2))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6 P_poly hPoly base (Rust.withPanics ext) A call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inl h3)))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6 P_poly hPoly base (Rust.withPanics ext) A call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6 P_poly hPoly base (Rust.withPanics ext) A call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5)))))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by ac_rfl)
    · apply SepWPp.of_sepWP_ret
      exact step_entry_tag_le_6 P_poly hPoly base (Rust.withPanics ext) A call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6)))))) hlen hpc hrun hsp_align
        hx0 hx1 hx2 hx3 (by ac_rfl)
    · exact step_entry_tag_gt_6 P_poly base ext A hFmt hDealloc call tag rest
        o0 o8 o9 oc0 oc1 oc2 oc3 oc4 oc5 oc6 o2a
        f08 f10 f18 st3 st4 st5 st6 st0 st1 fb0 f50 f58
        s29 s30 s22 s21 s20 s19 s0 _ R _ rfl hbytes hgt6 hlen hpc hrun hsp_align
        hx0 hx2 hx3 (by ac_rfl)

/-- `<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434`, 212 insns) meets
    `(messageDeserializeSpecX P_poly A).inImage img` (`MessageDeserializeOkX P_poly img A ext`). -/
theorem messageDeserialize_ok_x (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hFmt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr formatInnerName) (formatInnerSpec A))
    (hDealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A)) :
    MessageDeserializeOkX P_poly img A ext := by
  refine subroutine_ok_outcome_intro fun call R s0 hpc0 hrun0 hpre hsp0 => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (messageDeserializeSpecX P_poly A).pre call s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (messageDeserialize_ok_ext P_poly hPoly img.base ext A hFmt hDealloc).to_outcome
    call R s0 hpc0 hrun0 hpre.2 hsp0 |>.mono_outcome fun _ hout => hout

theorem messageDeserialize_spqrPolyApi_ok_x
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hFmt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr formatInnerName) (formatInnerSpec A))
    (hDealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A)) :
    MessageDeserializeOkX spqrPolyApi img A ext :=
  messageDeserialize_ok_x spqrPolyApi spqrPolyApi_chunkLaw img A ext hFmt hDealloc

theorem messageDeserialize_ok_of_contracts_x (P_poly : PolyApi) (hPoly : PolyApiChunkLaw P_poly)
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hFmt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr formatInnerName) (formatInnerSpec A)) :
    MessageDeserializeOkX P_poly img A ext :=
  messageDeserialize_ok_x P_poly hPoly img A ext hFmt hA.dealloc

theorem messageDeserialize_spqrPolyApi_ok_of_contracts_x
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hFmt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr formatInnerName) (formatInnerSpec A)) :
    MessageDeserializeOkX spqrPolyApi img A ext :=
  messageDeserialize_ok_of_contracts_x spqrPolyApi spqrPolyApi_chunkLaw img A ext hA hFmt

end CryptoVerification.SpqrV1.Top.MessageDeserialize

