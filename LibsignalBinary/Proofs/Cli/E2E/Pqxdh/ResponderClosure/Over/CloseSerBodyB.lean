/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneX
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SessionRecord::serialize` with One Previous Session: Epilogue Tail and Framing Helpers

Proves `serPrev1Tail_ok : SerPrev1TailStmt img A ext` (`+692 .. ret`), dropping the cloned
`SessionStructure` and temporary `Vec<Vec<u8>>`, together with local heap-folding and branch
helpers consumed by `CloseSerBody`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open Proofs.libsignal.Hooks2

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Instruction decodes for the inline `Vec<Vec<u8>>` drop -/

private gen_decodes libsignalSessionCode_tree k5tBin
  [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 740) →
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 780),
   (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 792) →
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 808)]

/-! ## Call and precondition-folding tactics -/

theorem k5t_false_left {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False :=
  not_satisfies_false_sepConj h

theorem sepWPpIn_fold {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hf : P = T ∗ F) (h : SepWPpIn img prog ret s (T' ∗ F) Q Qp) :
    SepWPpIn img prog ret s P Q Qp :=
  SepWPpIn.weaken_pre (hf ▸ sepConj_mono_left hent) h

open Lean Meta Elab Tactic in
/-- `k5t_call hcall ghost`: `wppin_call` for a callee whose `onPanic` is `⌜False⌝`, under a
generic `Qp` with a local `hQp : ∀ sf P_f, PanicAllocPost s0 sf P_f → Qp sf P_f`. -/
elab "k5t_call " hcall:term:max arg?:(ppSpace colGt term:max)? : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hQpId := mkIdent `hQp
  let applyStx ← match arg? with
    | some a => `(tactic| apply (SepWPpIn.call_inImage $hcall (x := $a)))
    | none => `(tactic| apply (SepWPpIn.call_inImage $hcall))
  evalTactic applyStx
  closeWppinCallSiteSetupSubgoals
  let gsAfterSetup ← getGoals
  let gPre :: gExit :: gPanic :: gCont :: rest := gsAfterSetup
    | throwError "k5t_call: unexpected subgoals after `SepWPpIn.call_inImage`"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gExit :: gPanic :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _ _ _ _ _he; exact not_satisfies_false_sepConj _he)
    wp_focus_close (
      intro _sfp _hstp
      apply $hQpId:ident
      intro _Rp _hmp
      exfalso
      first
        | exact k5t_false_left _hmp
        | exact k5t_false_left (by simpa only [sepConj_assoc] using _hmp)
        | (simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at _hmp
           exact _hmp.1.elim)
        | (simp only [Spec.inImage, dropLocal1SubSpecX, deallocSubSpecX, sepConj_assoc,
             satisfies_pure_sepConj] at _hmp
           exact _hmp.1.elim))
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wppinElimSpatialContext hspId

/-- `k5t_callc h S ghost`: refold `h` to `subroutine_ok _ _ S`, call it with `k5t_call`, then
normalize `sp`. -/
macro "k5t_callc " h:ident S:term:max g:term:max : tactic =>
  `(tactic| (change subroutine_ok _ _ $S at $h:ident; k5t_call $h $g; try wppin_sp_norm))

/-! ## Shared epilogue (`+812 .. ret`) and tail (`+692 .. ret`) -/

set_option maxHeartbeats 400000 in
theorem serPrev1Tail_epilogue {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (out q' cap' ptr' : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s0 s : State} {P Fx : SepProp} {Q Qp : State → SepProp → Prop}
    (hQ : ∀ sf : State, sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) bs ∗ A.pool ∗
        stackAt s0.sp serializeStackX) ∗ Fx))
    (hal0 : s0.sp &&& 15#64 = 0#64)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr serializeName + bv% (812))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 800#64)
    (htr : s.trace = s0.trace)
    (hvr : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P =
      (stackAt (s0.sp - 800#64) serializeSubStackX ∗
        ((s0.sp - 800#64) ↦₆₄ 1#64) ∗ ((s0.sp - 792#64) ↦₆₄ q') ∗
        ((s0.sp - 784#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 776#64) 344 ∗
        ((s0.sp - 432#64) ↦₆₄ cap') ∗ ((s0.sp - 424#64) ↦₆₄ ptr') ∗
        ((s0.sp - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap' ptr' bs ∗
        memRegion (s0.sp - 408#64) 312 ∗
        (out ↦₆₄ okTagVec) ∗ ((out + 8#64) ↦₆₄ cap') ∗
        ((out + 16#64) ↦₆₄ ptr') ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.pool ∗ serSavedCells s0 ret) ∗ Fx) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q Qp := by
  have hfn : libsignalSessionCode.fnOff serializeName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") :=
    libsignalSessionCode_fnOff_serialize
  have hal0' : (s0.sp &&& 15#64 == 0#64) = true := by simp only [hal0, beq_self_eq_true]
  have hal : ((s0.sp - 800#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 800#64 hal0'
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 812 32
  clear hfn
  subst hP
  unfold serSavedCells
  simp only [sepConj_assoc]
  generalize_entry (SP2Ext img.base ext).fnAddr serializeName = entry
  examples_hide_fetches
  apply SepWPpIn.of_sepWP_ret
  wp_steps
  refine SepWP.fold (vecU8_from_out_cellsX A out cap' ptr' bs) (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  refine SepWP.fold (repack_stack_hdr_cellsX s0.sp 1#64 q' 1#64 cap' ptr'
    (BitVec.ofNat 64 bs.length)) (by sep_frame) ?_
  refine SepWP.weaken_pre (P' := ((out ↦₆₄ okTagVec) ∗ vecU8 A (out + 8#64) bs ∗ A.pool ∗
    stackAt s0.sp serializeStackX) ∗ Fx) ?_ ?_
  · exact Entails.of_eq (by ac_rfl)
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) (hQ _ ?_ ?_ ?_)
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]

set_option maxHeartbeats 800000 in
theorem serPrev1Tail_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) (hDrop : DropSessionStructureLocal1OkX img A ext) :
    SerPrev1TailStmt img A ext := by
  intro out q' capE ptrE cap' ptr' o0 o1 o2 o3 bs enc w sess' ret s0 sm Fx Q Qp
    hQp hQ hal0 hpc hrun hsp htr hx19 hx23 hx24 hvr
  have hEpi := @serPrev1Tail_epilogue img A ext
  have hfn : libsignalSessionCode.fnOff serializeName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") :=
    libsignalSessionCode_fnOff_serialize
  have hdrop := dropLocal1_sub_okX hDrop
  have hdealloc := dealloc_sub_okX (img := img) (A := A) (ext := ext) hC
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = out := hx19
  have hx23' : (sm.readReg64 (Reg.gpr 23#5) + 1#64 == 0#64) = false := hx23
  have hx24' : sm.readReg64 (Reg.gpr 24#5) = s0.sp - 800#64 := hx24
  have hal0' : (s0.sp &&& 15#64 == 0#64) = true := by simp only [hal0, beq_self_eq_true]
  have hal : ((s0.sp - 800#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 800#64 hal0'
  have hl24 : LayoutOk 24 8 := layoutOk_24_8_ser
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  clear hx19 hx23 hx24
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 692 48
  code_fetches_from CryptoVerification.libsignalSessionCode k5tBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 740 44
  code_fetches_from CryptoVerification.libsignalSessionCode serializeBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 784 8
  code_fetches_from CryptoVerification.libsignalSessionCode k5tBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 792 20
  clear hfn
  rw [vecU8At_unpack_cells_432X, vecU8At_cells A q' capE ptrE enc]
  simp only [sepConj_assoc]
  generalize_entry (SP2Ext img.base ext).fnAddr serializeName = entry
  examples_hide_fetches
  refine sepWPpIn_fold (vecU8Buf_drop_view A capE ptrE enc) (by sep_frame) ?_
  simp only [sepConj_assoc]
  refine SepWPpIn.pure_elim fun hcapE63 => ?_
  apply SepWPpIn.of_sepWP
    (mid := entry + bv% (2 ^ 64 +
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") -
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
  wp_steps
  refine SepWP.fold (sessionAt_entails_sessionStateAt A (s0.sp - 776#64) w sess') (by sep_frame) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  k5t_callc hdrop ((dropLocal1SubSpecX A).inImage img) ⟨s0.sp - 776#64, w, sess'.state⟩
  by_cases hc : capE = 0#64
  · rw [ite_eq_left hc, emp_sepConj]
    subst hc
    apply SepWPpIn.of_sepWP
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    wp_steps
    refine SepWP.fold (prevVec1_cap1_merge q' 0#64 ptrE (BitVec.ofNat 64 enc.length))
      (by sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    k5t_callc hdealloc ((deallocSubSpecX A).inImage img) (q', 24, 8)
    exact hEpi out q' cap' ptr' bs hQ hal0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [okTagVec]; sep_frame)
  · have hlE : LayoutOk capE.toNat 1 := layoutOk_cap_u8_ser hc hcapE63
    have hcE : (capE == 0#64) = false := beq_false_of_ne hc
    rw [ite_eq_right hc]
    simp only [sepConj_assoc]
    apply SepWPpIn.of_sepWP
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    k5t_callc hdealloc ((deallocSubSpecX A).inImage img) (ptrE, capE.toNat, 1)
    apply SepWPpIn.of_sepWP
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    wp_steps
    refine SepWP.fold (prevVec1_cap1_merge q' capE ptrE (BitVec.ofNat 64 enc.length))
      (by sep_frame) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    k5t_callc hdealloc ((deallocSubSpecX A).inImage img) (q', 24, 8)
    exact hEpi out q' cap' ptr' bs hQ hal0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [okTagVec]; sep_frame)

/-! ## Heap-shape and arithmetic helpers -/

theorem prevVecAt_one_fold_ser (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8))
    (h : cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
        A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A) 24 q [enc] ∗
        memRegion (q + 24#64) ((cap.toNat - 1) * 24)) ⊢
      prevVecAt A r cap q [enc] := by
  rw [prevVecAt_one_cells_ser]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.pure_right h (Entails.refl _))))

theorem prevVecAt_one_pure_first (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A r cap q [enc] =
      ⌜cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
          A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A) 24 q [enc] ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  rw [prevVecAt_one_cells_ser]
  ac_rfl

/-- `vecVecClone1`'s result at `sp - 800`, opened down to the element header cells at `q`. -/
theorem prevVecAt_800_open (A : RustAlloc) (sp q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A (sp - 800#64) 1#64 q [enc] =
      (∃∗ capE : BitVec 64, ∃∗ ptrE : BitVec 64,
        ⌜q ≠ 0#64⌝ ∗
          (((sp - 800#64) ↦₆₄ 1#64) ∗ ((sp - 792#64) ↦₆₄ q) ∗ ((sp - 784#64) ↦₆₄ 1#64) ∗
            A.live q 24 8 ∗
            (q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
            ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
            RustHeap.vecU8Buf A capE ptrE enc)) := by
  have e8 : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800 8
  have e16 : sp - 800#64 + 16#64 = sp - 784#64 := bv_sub_add_lit sp 800 16
  rw [prevVecAt_cap1_cells, e8, e16]
  unfold vecU8
  simp only [vecU8At_cells, sepExists_sepConj_right]
  refine ProofLib.sepExists_congr fun capE => ProofLib.sepExists_congr fun ptrE => ?_
  ac_rfl

/-- No unsigned carry out of `ofNat a + ofNat b` (the `adds` / `b.hs` branch). -/
theorem ult_ofNat_add_false {a b : Nat} (h : a + b < 2 ^ 63) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  rw [← BitVec.ofNat_add]
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  have h1 : (a + b) % 2 ^ 64 = a + b := Nat.mod_eq_of_lt (by omega)
  have h2 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  exact decide_eq_false (by omega)

/-- Bit 63 clear and nonzero for `ofNat a + ofNat b` (the `tbz` / `cbz` branches). -/
theorem ofNat_add_bits {a b : Nat} (h : a + b < 2 ^ 63) (h1 : 1 ≤ a + b) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).getLsbD 63 = false ∧
      (BitVec.ofNat 64 a + BitVec.ofNat 64 b == 0#64) = false := by
  rw [← BitVec.ofNat_add]
  refine ⟨?_, ?_⟩
  · rw [BitVec.getLsbD_ofNat]
    simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  · apply beq_false_of_ne
    intro heq
    have h1' : (BitVec.ofNat 64 (a + b)).toNat = 0 := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1'
    omega

theorem memRegion_out32_pool_stack_swap (A : RustAlloc) (out sp : BitVec 64) :
    (memRegion out 32 ∗ A.pool ∗ stackAt sp serializeStackX) =
      (A.pool ∗ (memRegion out 32 ∗ stackAt sp serializeStackX)) := by
  ac_rfl

theorem vecU8At_init_byte_432_cap (A : RustAlloc) (sp ptr c : BitVec 64) (n : Nat)
    (b0 : BitVec 8) (hc : c.toNat = n) (hpos : 1 ≤ n) (hlt : n < 2 ^ 32) (hptr : ptr ≠ 0) :
    (((sp - 432#64) ↦₆₄ c) ∗ ((sp - 424#64) ↦₆₄ ptr) ∗ ((sp - 416#64) ↦₆₄ 1#64) ∗
      A.live ptr n 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (n - 1)) ⊢
      vecU8At A (sp - 432#64) (BitVec.ofNat 64 n) ptr [b0] := by
  have e : c = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  subst e
  exact vecU8At_init_byte_432X A sp ptr n b0 hpos hlt hptr

theorem k5_fold_q {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {Q Qp : State → SepProp → Prop} (A : RustAlloc) (q capE ptrE : BitVec 64)
    (enc : List (BitVec 8)) {P F : SepProp}
    (hP : P = ((q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
      ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ RustHeap.vecU8Buf A capE ptrE enc) ∗ F)
    (h : SepWPpIn img prog ret s (vecU8At A q capE ptrE enc ∗ F) Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  subst hP
  exact SepWPpIn.weaken_pre (sepConj_mono_left (Entails.of_eq (vecU8At_cells A q capE ptrE enc).symm)) h

/-- Side goals of the `hF2` / `hTail` applications (pc, sp, trace, registers). -/
macro "k5_side" : tactic =>
  `(tactic| first
    | (wp_norm_lhs; done)
    | (wp_norm_goal; done)
    | (simp only [wp_norm, arm64_norm, *]; done))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
