/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1
public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `HeaderReceived` Arm & `OptCallInv` Epilogue

**Checked by Lean.** Word-grid relocation combinators, `OptCallInv`-generalized `+18996` epilogue,
and the `States.headerReceived` arm (`0x55d30`, `+2268`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr CryptoVerification.InImageLift
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.LibsignalSpqrV1.PolyDecoder CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Top CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local wp_norm] private theorem simple2_exists_two_pow_zero : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local wp_norm] private theorem simple2_exists_two_pow_one : (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local wp_norm] private theorem optCallInv_writeReg64_s2 (oimg : Option Obj.Image)
    (s : State) (r : Reg) (v : BitVec 64) :
    OptCallInv oimg (s.writeReg64 r v) ↔ OptCallInv oimg s := by
  cases oimg with
  | none => rfl
  | some img =>
    have hmem : (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
    have hsym : (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl
    dsimp only [OptCallInv]
    rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem, hsym]

@[local wp_norm] private theorem optCallInv_setPC_s2 (oimg : Option Obj.Image)
    (s : State) (pc : BitVec 64) :
    OptCallInv oimg (s.setPC pc) ↔ OptCallInv oimg s := by
  cases oimg with
  | none => rfl
  | some img =>
    have hmem : (s.setPC pc).mem = s.mem := by cases s; rfl
    have hsym : (s.setPC pc).symtab = s.symtab := by cases s; rfl
    dsimp only [OptCallInv]
    rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem, hsym]

@[local wp_norm] private theorem optCallInv_setPState_s2 (oimg : Option Obj.Image)
    (s : State) (ps : PState) :
    OptCallInv oimg (s.setPState ps) ↔ OptCallInv oimg s := by
  cases oimg with
  | none => rfl
  | some img =>
    have hmem : (s.setPState ps).mem = s.mem := by cases s; rfl
    have hsym : (s.setPState ps).symtab = s.symtab := by cases s; rfl
    dsimp only [OptCallInv]
    rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem, hsym]

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")

/-- Unified hook bundle for simple `<States>::recv` arms (`HeaderReceived` and `Ct2Sampled`),
parameterised over `oimg : Option Obj.Image` (`none` for `AllocContracts`, `some img` for `AllocContractsX`). -/
structure SimpleRecvHooks (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (oimg : Option Obj.Image) : Prop where
  memcpy_ok_at : ∀ (name : String) (k : Nat),
    libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (specWithOptInv oimg (sessionMemcpySpec extHookStack))
  dealloc_ok_at : ∀ (name : String) (k : Nat),
    libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff LibsignalTripleRatchet.deallocName →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A extHookStack))
  dealloc : DeallocOkExt b A ext

theorem SimpleRecvHooks.of_allocContracts {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) : SimpleRecvHooks b A ext none where
  memcpy_ok_at name k hk := subroutine_ok_to_optNone (hA.session_memcpy_ok_at name k extHookStack (hk := hk))
  dealloc_ok_at name k hk := subroutine_ok_to_optNone (rustDeallocExternWithStack_of_rustDealloc (hA.dealloc_ok_at name k hk))
  dealloc := hA.dealloc

theorem SimpleRecvHooks.of_allocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hdealloc : DeallocOkExt img.base A ext) : SimpleRecvHooks img.base A ext (some img) where
  memcpy_ok_at name k hk := hA.session_memcpy_ok_at name k extHookStack (by decide) (by decide) hk
  dealloc_ok_at name k hk := hA.dealloc_ok_at name k hk
  dealloc := hdealloc

theorem seq_clean_opt_sr {prog : Program} {oimg : Option Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop} (hinv : OptCallInv oimg s)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → OptCallInv oimg sm → Q sm → SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq_optImage hinv (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ hinv_m => SepWP.weaken_pre hent (h2 sm hpc hrun hinv_m hq))

theorem stackAt_statesRecvCallee_eq_extHook_sr (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX = memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

theorem fnAddr_statesRecv_rel_sr {b : BitVec 64} {ext : String → Option (State → State)} (targetName : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff targetName + k = libsignalSessionCode.fnOff statesRecvName := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).fnAddr statesRecvName - BitVec.ofNat 64 k =
      (tripleRatchetProgAtExt b ext).fnAddr targetName := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, ← hk]; bv_omega

theorem fnAddr_statesRecv_fwd_sr {b : BitVec 64} {ext : String → Option (State → State)} (targetName : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff statesRecvName + k = libsignalSessionCode.fnOff targetName := by fnoff_eq) :
    (tripleRatchetProgAtExt b ext).fnAddr targetName =
      (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + BitVec.ofNat 64 k := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, ← hk]; bv_omega

theorem subroutine_ok_statesRecvVariantSpec_opt_of_sepWP_sr
    {oimg : Option Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hwp : ∀ (outA selfA msgA : BitVec 64) (s0 : State),
      s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName → s0.status = .Running → OptCallInv oimg s0 →
      (s0.sp &&& 15#64 == 0#64) = true → b &&& 0xfff#64 = 0#64 →
      s0.readReg64 .x0 = outA → s0.readReg64 .x1 = selfA → s0.readReg64 .x2 = msgA → statesRecvPreInv self →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
        (stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA self ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool))
        (fun sf Pf =>
          (Pf ⊢ resultV1RecvAt A (F := F) outA (self.recv K msg) ∗ memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (specWithOptInv oimg (statesRecvVariantSpec A F K b self msg)) := by
  apply subroutine_ok_of_sepWPp; intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  dsimp only [specWithOptInv, statesRecvVariantSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA self ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool), R,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [specWithOptInv, statesRecvVariantSpec]
  refine SepWPp.of_sepWP (SepWP.mono (hwp outA selfA msgA s0 hpc0 hrun0 hinv0 hsp0_align hb hx0 hx1 hx2 hinv) ?_)
  intro sf Pf hpc_f hrun_f ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine SepWPp.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_f, hcs_f⟩
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right htr_f (Entails.refl _)))
    (Satisfies.mono (sepConj_mono_left hPf) hsat)

private theorem epilogue_step_19280_19324_opt_sr
    {oimg : Option Obj.Image} {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg) (s : State) (fsp out : BitVec 64)
    (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376)
    (uq888 uq904 uq944 q512 q528 q544 : BitVec 128) (u920 u928 u936 w232 w560 : BitVec 64) (Frame : SepProp)
    (_hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19280#64)
    (hrun : s.status = .Running) (hinv : OptCallInv oimg s) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64) (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx2 : s.readReg64 .x2 = 376#64) (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64) s
      (stackAt fsp extHookStack ∗ memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗ ((out + 920#64) ↦₆₄ u920) ∗
       ((out + 928#64) ↦₆₄ u928) ∗ ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
       ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt fsp extHookStack ∗ ((out + 512#64) ↦ₛ bs576) ∗
          ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ∗
          ((out + 928#64) ↦₆₄ w232) ∗ ((out + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((out + 944#64) ↦₁₂₈ q512) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
          ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  subst hsp hx19
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (specWithOptInv oimg (sessionMemcpySpec extHookStack)) :=
    hH.memcpy_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")) (by simp only [arm64_norm])
  simp only [specWithOptInv, sessionMemcpySpec, extHookStack] at hmemcpy ⊢; rw [← hbs576]
  states_recv_fetches_range b (Rust.withPanics ext) 19280 44
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; wp_simp_pre [pointsTo128, sepConj_assoc]
  wp_steps; wp_call hmemcpy (s.readReg64 .x19 + 512#64, s.sp + 576#64, bs576); wp_steps
  simp only [pointsTo128, sepConj_assoc]; wp_done

set_option maxHeartbeats 1600000 in
theorem epilogue_18996_exit_none_488_opt_sr
    {oimg : Option Obj.Image} {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg)
    (s0 s1 : State) (out : BitVec 64)
    (w224 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
    (hrun1 : s1.status = .Running)
    (hinv1 : OptCallInv oimg s1)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    let fsp := s0.sp - 4240#64
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗ memRegion out v1RecvSize ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueRecvOutPartA out
            w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
            (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
            (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
            (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
            (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14) ∗
          epilogueRecvOutPartB488 out
            w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
            w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
            w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20) ∗
          memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  intro fsp
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hout0 : memRegion out 488 = existsWordsAtOff out 61 0 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul] using memRegion_off_eq_existsWordsAtOff out 61 0 (by decide)
  rw [memRegion_out_960_split_488_472 out, hout0]
  have hpre :
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗
       (existsWordsAtOff out 61 0 ∗ memRegion (out + 488#64) 472) ∗ Rest ⊢
      ((∃∗ q512 : BitVec 128, (fsp + 512#64) ↦₁₂₈ q512) ∗ (∃∗ q528 : BitVec 128, (fsp + 528#64) ↦₁₂₈ q528) ∗
       (∃∗ q544 : BitVec 128, (fsp + 544#64) ↦₁₂₈ q544) ∗ (∃∗ w560 : BitVec 64, (fsp + 560#64) ↦₆₄ w560) ∗
       (∃∗ bs576 : List (BitVec 8), ⌜bs576.length = 376⌝ ∗ ((fsp + 576#64) ↦ₛ bs576)) ∗
       (∃∗ q960 : BitVec 128, (fsp + 960#64) ↦₁₂₈ q960) ∗ (∃∗ uq488 : BitVec 128, (out + 488#64) ↦₁₂₈ uq488) ∗
       (∃∗ u504 : BitVec 64, (out + 504#64) ↦₆₄ u504) ∗ (∃∗ uq888 : BitVec 128, (out + 888#64) ↦₁₂₈ uq888) ∗
       (∃∗ uq904 : BitVec 128, (out + 904#64) ↦₁₂₈ uq904) ∗ (∃∗ u920 : BitVec 64, (out + 920#64) ↦₆₄ u920) ∗
       (∃∗ u928 : BitVec 64, (out + 928#64) ↦₆₄ u928) ∗ (∃∗ u936 : BitVec 64, (out + 936#64) ↦₆₄ u936) ∗
       (∃∗ uq944 : BitVec 128, (out + 944#64) ↦₁₂₈ uq944) ∗ existsWordsAtOff out 61 0) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ memRegion (out + 512#64) 376 ∗ Rest) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono (memRegion_3632_entails_epilogue fsp)
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (memRegion_472_entails_epilogue out)))))))))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]
  apply sepWP_intro_ex; intro q512; apply sepWP_intro_ex; intro q528; apply sepWP_intro_ex; intro q544; apply sepWP_intro_ex; intro w560; apply sepWP_intro_ex_pure; intro bs576 hbs576; apply sepWP_intro_ex; intro q960; apply sepWP_intro_ex; intro uq488; apply sepWP_intro_ex; intro u504
  apply sepWP_intro_ex; intro uq888; apply sepWP_intro_ex; intro uq904; apply sepWP_intro_ex; intro u920; apply sepWP_intro_ex; intro u928; apply sepWP_intro_ex; intro u936; apply sepWP_intro_ex; intro uq944; apply sepWP_intro_ex; intro u0; apply sepWP_intro_ex; intro u8
  apply sepWP_intro_ex; intro u16; apply sepWP_intro_ex; intro u24; apply sepWP_intro_ex; intro u32; apply sepWP_intro_ex; intro u40; apply sepWP_intro_ex; intro u48; apply sepWP_intro_ex; intro u56; apply sepWP_intro_ex; intro u64; apply sepWP_intro_ex; intro u72
  apply sepWP_intro_ex; intro u80; apply sepWP_intro_ex; intro u88; apply sepWP_intro_ex; intro u96; apply sepWP_intro_ex; intro u104; apply sepWP_intro_ex; intro u112; apply sepWP_intro_ex; intro u120; apply sepWP_intro_ex; intro u128; apply sepWP_intro_ex; intro u136
  apply sepWP_intro_ex; intro u144; apply sepWP_intro_ex; intro u152; apply sepWP_intro_ex; intro u160; apply sepWP_intro_ex; intro u168; apply sepWP_intro_ex; intro u176; apply sepWP_intro_ex; intro u184; apply sepWP_intro_ex; intro u192; apply sepWP_intro_ex; intro u200
  apply sepWP_intro_ex; intro u208; apply sepWP_intro_ex; intro u216; apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232; apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264
  apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280; apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312; apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328
  apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360; apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376; apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392
  apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408; apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424; apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456
  apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472; apply sepWP_intro_ex; intro u480; rw [emp_sepConj]
  have hstepA := epilogue_step_18996_19128 (b := b) (ext := ext) s1 fsp out
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
    u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432
    w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960
    (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
     epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
     ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
     memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
     statesRecvSavedCells s0 ∗
     epilogueRecvOutPartB out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
       u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504 ∗
     memRegion (out + 512#64) 376 ∗ ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
     ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗ ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx19
  refine seq_clean_opt_sr hinv1 (SepWP.weaken_pre ?_ hstepA) ?_
  · rw [epilogueRecvStackPartA_eq_488, epilogueRecvOutPartB_eq_488]; refine Entails.of_eq ?_
    trans (wordsAtOff out
      [u0, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104, u112,
       u120, u128, u136, u144, u152, u160, u168, u176, u184, u192, u200, u208, u216, u224, u232, u240, u248, u256,
       u264, u272, u280, u288, u296, u304, u312, u320, u328, u336, u344, u352,
       u360, u368, u376, u384, u392, u400, u408, u416, u424, u432, u440, u448, u456, u464, u472, u480] 0 ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 960#64) ↦₁₂₈ q960) ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ ((out + 488#64) ↦₁₂₈ uq488) ∗ ((out + 504#64) ↦₆₄ u504) ∗ memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗ ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest))
    · dsimp only [wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]; ac_rfl
    · rw [wordsAtOff_out_488_eq_epilogueOut]; ac_rfl
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx16_2, hx17_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx29_2, hv0_2, htr2⟩
    let outPartA := epilogueRecvOutPartA out
      w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
      (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
      (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
      (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
      (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14)
    have hstepB := epilogue_step_19128_19280 (b := b) (ext := ext) s2 fsp out
      u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
      u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504
      w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
      (outPartA ∗ epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ memRegion (out + 512#64) 376 ∗ ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗ ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2
    refine seq_clean_opt_sr hinv2 (SepWP.weaken_pre (Entails.of_eq (by dsimp only [outPartA]; ac_rfl)) hstepB) ?_
    intro s3 hpc3 hrun3 hinv3 ⟨hsp3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx29_3, htr3⟩
    rw [hx23_2, hx27_2, hx3_2, hx24_2, hx17_2, hx26_2, hx22_2, hx16_2, hx2_2, hx20_2, hv0_2]
    let outPartB488 := epilogueRecvOutPartB488 out
      w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
      w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
      w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20)
    have hstepC := epilogue_step_19280_19324_opt_sr hH s3 fsp out bs576 hbs576 uq888 uq904 uq944 q512 q528 q544 u920 u928 u936 noneCap w560
      (memRegion (fsp - 19552#64) 3168 ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗
       memRegion (fsp + 976#64) 3168 ∗ statesRecvSavedCells s0 ∗
       outPartA ∗ outPartB488 ∗ ((out + 488#64) ↦₁₂₈ q960) ∗ ((out + 504#64) ↦₆₄ w256) ∗ Rest)
      hfsp_align hpc3 hrun3 hinv3 hsp3 hx0_3 hx1_3 hx2_3 hx19_3
    refine seq_clean (SepWP.weaken_pre ?_ hstepC) ?_
    · rw [epilogueRecvOutPartB_eq_488, epilogueRecvStackPartA_eq_488, stackAt_statesRecvCallee_eq_extHook_sr fsp]
      exact Entails.of_eq (by dsimp only [outPartB488]; ac_rfl)
    · intro s4 hpc4 hrun4 ⟨hsp4, htr4⟩
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans (htr3.trans (htr2.trans htr1))
      have hepil := states_recv_epilogue_19324 (b := b) (ext := ext) s0 s4
        (outPartA ∗ outPartB488 ∗ memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗ Rest)
        hsp0_align hpc4 hrun4 hsp4 htr40
      refine SepWP.mono (SepWP.weaken_pre ?_ hepil) ?_
      · have hstk288 := epilogueStack_224_512_entails_memRegion fsp
          w224 noneCap w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504
          w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
        have hstk3632 := epilogue_entails_memRegion_3632 fsp q512 q528 q544 q960 w560 bs576 hbs576
        have hout440 := epilogue_out_488_960_entails_memRegion_and_optNone A out q960 q528 q544 q512 w256 w560 (s3.readReg64 .x20) bs576 hbs576
        rw [← stack_recombine_4144 fsp, stackAt_statesRecvCallee_eq_extHook_sr fsp]
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack ∗ memRegion fsp 224) ∗
          (epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
           ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
           epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488) ∗
          (((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
           memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗
           memRegion (fsp + 976#64) 3168) ∗
          (statesRecvSavedCells s0 ∗ outPartA ∗ outPartB488) ∗
          (((out + 488#64) ↦₁₂₈ q960) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗ ((out + 888#64) ↦₁₂₈ q528) ∗
           ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
           ((out + 944#64) ↦₁₂₈ q512)) ∗ Rest by ac_rfl))
          (Entails.trans (sepConj_mono_right (sepConj_mono hstk288
            (sepConj_mono hstk3632 (sepConj_mono_right (sepConj_mono_left hout440))))) (Entails.of_eq (by ac_rfl)))
      · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by dsimp only [outPartA, outPartB488]; ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem Relocatable.of_unchunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)) :
    Relocatable 80 (fun a => unchunkedHeaderReceivedAt A a st) := by
  simp only [unchunkedHeaderReceivedAt_eq_ekSentAt]
  exact Relocatable.of_unchunkedEkSentAt A { epoch := st.epoch, auth := st.auth, dk := st.hdr }

theorem Relocatable.of_chunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 480 (fun a => chunkedHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 80#64) (m := 480) rfl rfl
    (Relocatable.of_unchunkedHeaderReceivedAt A st.uc) (Relocatable.of_polyDecoderAt A st.receiving_ek)

theorem chunkedStatesAt_headerReceived_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a (.headerReceived st) =
      ((a ↦₆₄ 8#64) ∗ chunkedHeaderReceivedAt A (a + 8#64) st ∗ memRegion (a + 488#64) 440) := rfl

theorem chunkedStatesAt_ct2Sampled_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a (.ct2Sampled st) =
      ((a ↦₆₄ 12#64) ∗ chunkedCt2SampledAt A (a + 8#64) st ∗ memRegion (a + 464#64) 464) := rfl

/-! ## Word-Grid Relocation Combinators (`existsWordsWithBytesAtOff`) -/

def existsWordsWithBytesAtOff (a : BitVec 64) (F : List (BitVec 8) → SepProp) : Nat → Nat → SepProp
  | 0, _ => F []
  | n + 1, off =>
      ∃∗ w : BitVec 64, ((a + BitVec.ofNat 64 off) ↦₆₄ w) ∗
        existsWordsWithBytesAtOff a (fun bs => F (unpack64 w ++ bs)) n (off + 8)

theorem pointsToBytes_entails_existsWordsWithBytesAtOff (a : BitVec 64) :
    ∀ (n off : Nat) (F : List (BitVec 8) → SepProp) (bs : List (BitVec 8)), bs.length = 8 * n →
      ((a + BitVec.ofNat 64 off) ↦ₛ bs) ∗ F bs ⊢ existsWordsWithBytesAtOff a F n off := by
  intro n; induction n with
  | zero =>
    intro off F bs hlen; have hbs := List.eq_nil_of_length_eq_zero hlen; subst hbs
    simp only [existsWordsWithBytesAtOff, pointsToBytes_nil, emp_sepConj]; exact Entails.refl _
  | succ n ih =>
    intro off F bs hlen
    have htake : (bs.take 8).length = 8 := by simp; omega
    have hdrop : (bs.drop 8).length = 8 * n := by simp; omega
    obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 htake
    have hbs : bs = unpack64 w ++ bs.drop 8 := by rw [← hw, List.take_append_drop 8 bs]
    rw [hbs, pointsToBytes_append (a + BitVec.ofNat 64 off) (unpack64 w) (bs.drop 8),
        unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, ← BitVec.ofNat_add]
    dsimp only [existsWordsWithBytesAtOff]; refine Entails.sepExists_right w ?_; rw [sepConj_assoc]
    exact sepConj_mono_right (ih (off + 8) (fun bs' => F (unpack64 w ++ bs')) (bs.drop 8) hdrop)

theorem Relocatable.entails_existsWordsWithBytesAtOff {n : Nat} {G : BitVec 64 → SepProp}
    (hrel : Relocatable (8 * n) G) (a : BitVec 64) (off : Nat) :
    G (a + BitVec.ofNat 64 off) ⊢ existsWordsWithBytesAtOff a (relocatedHeap G) n off := by
  refine Entails.trans (hrel (a + BitVec.ofNat 64 off)) ?_
  apply Entails.sepExists_elim; intro bs; apply Entails.pure_left; intro hlen
  exact pointsToBytes_entails_existsWordsWithBytesAtOff a n off (relocatedHeap G) bs hlen

theorem wordsAtOff_recompose_relocatedHeap {G : BitVec 64 → SepProp}
    (a : BitVec 64) (off : Nat) (ws : List (BitVec 64)) :
    wordsAtOff a ws off ∗ relocatedHeap G (wordsBytes ws) ⊢ G (a + BitVec.ofNat 64 off) := by
  rw [wordsAtOff_eq_wordsAt a ws off]; exact relocatedHeap_recompose_words G ws (a + BitVec.ofNat 64 off)

/-! ## `States.headerReceived` (`tag = 8#64`, `+2268` / `0x55d30`) -/

theorem headerReceived_memcpy_2268_2284
    {oimg : Option Obj.Image} {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg) (s : State) (fsp selfA : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2268#64)
    (hrun : s.status = .Running) (hinv : OptCallInv oimg s)
    (hsp : s.sp = fsp) (hx1 : s.readReg64 .x1 = selfA) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2284#64) s
      (stackAt fsp extHookStack ∗ memRegion (fsp + 1856#64) 480 ∗ chunkedHeaderReceivedAt A (selfA + 8#64) st ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt fsp extHookStack ∗ chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗
              memRegion (selfA + 8#64) 480 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx1
  have hpre : stackAt s.sp extHookStack ∗ memRegion (s.sp + 1856#64) 480 ∗
      chunkedHeaderReceivedAt A (s.readReg64 .x1 + 8#64) st ∗ Frame ⊢
      ((∃∗ bs : List (BitVec 8), ⌜bs.length = 480⌝ ∗
          (((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗ relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs)) ∗
       stackAt s.sp extHookStack) ∗ (memRegion (s.sp + 1856#64) 480 ∗ Frame) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Relocatable.of_chunkedHeaderReceivedAt A st (s.readReg64 .x1 + 8#64)))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_; apply sepWP_intro_ex_pure; intro bs hbs
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (specWithOptInv oimg (sessionMemcpySpec extHookStack)) :=
    hH.memcpy_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      (by simp only [arm64_norm])
  have hpost : ∀ n : Nat, stackAt s.sp n ∗ ((s.sp + 1856#64) ↦ₛ bs) ∗ ((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗
      relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs ∗ Frame ⊢
      stackAt s.sp n ∗ chunkedHeaderReceivedAt A (s.sp + 1856#64) st ∗
        memRegion (s.readReg64 .x1 + 8#64) bs.length ∗ Frame := by
    intro n
    refine Entails.trans (Entails.of_eq (show _ = stackAt s.sp n ∗
      (((s.sp + 1856#64) ↦ₛ bs) ∗ relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs) ∗
      ((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗ Frame by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono
      (relocatedHeap_recompose (fun a => chunkedHeaderReceivedAt A a st) bs (s.sp + 1856#64))
      (sepConj_mono_left (pointsToBytes_entails_memRegion (s.readReg64 .x1 + 8#64) bs)))
  simp only [specWithOptInv, sessionMemcpySpec, extHookStack] at hmemcpy hpost ⊢; rw [← hbs]
  states_recv_fetches_range b (Rust.withPanics ext) 2268 16
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; wp_steps; wp_call hmemcpy (s.sp + 1856#64, s.readReg64 .x1 + 8#64, bs)
  refine Recv.align_pre (Entails.trans (Entails.of_eq (by ac_rfl)) (hpost _)) ?_; wp_done

theorem memRegion_4144_split_1856_480 (fsp : BitVec 64) :
    memRegion fsp 4144 = memRegion fsp 1856 ∗ memRegion (fsp + 1856#64) 480 ∗ memRegion (fsp + 2336#64) 1808 := by
  rw [ProofLib.memRegion_split fsp 1856 2288 (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 480) (k := 1808) (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)]

theorem selfA_headerReceived_entails_memRegion_928 (selfA : BitVec 64) :
    (selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 8#64) 480 ∗ memRegion (selfA + 488#64) 440 ⊢ memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 480) (k := 440) (b' := selfA + 488#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA 8#64)

theorem sepWP_intro_ex_nest {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {post : State → SepProp → Prop} {rest R : SepProp} {P Q : α → SepProp}
    (h : ∀ v : α, SepWP prog target_pc s ((Q v ∗ rest) ∗ (P v ∗ R)) post) :
    SepWP prog target_pc s (((∃∗ v : α, P v ∗ Q v) ∗ rest) ∗ R) post := by
  rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro v
  rw [sepConj_assoc (P v), sepConj_assoc, sepConj_left_comm (P v)]; exact h v

def words50List
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) : List (BitVec 64) :=
  w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: w21 :: w22 :: w23 :: w24 :: w25 :: w26 :: w27 :: w28 :: w29 :: w30 :: w31 :: w32 :: w33 :: w34 :: w35 :: w36 :: w37 :: w38 :: w39 :: w40 :: w41 :: w42 :: w43 :: w44 :: w45 :: w46 :: w47 :: w48 :: w49 :: w50 :: w51 :: w52 :: w53 :: w54 :: w55 :: w56 :: w57 :: w58 :: w59 :: []

def headerReceivedStackWords (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) : SepProp :=
  wordsAtOff fsp (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: st_epoch :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: w21 :: w22 :: w23 :: w24 :: w25 :: w26 :: w27 :: w28 :: w29 :: w30 :: w31 :: w32 :: w33 :: w34 :: w35 :: w36 :: w37 :: w38 :: w39 :: w40 :: w41 :: w42 :: w43 :: w44 :: w45 :: w46 :: w47 :: w48 :: w49 :: w50 :: w51 :: w52 :: w53 :: w54 :: w55 :: w56 :: w57 :: w58 :: w59 :: []) 1856

theorem headerReceivedStackWords_entails_memRegion (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) :
    headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ⊢ memRegion (fsp + 1856#64) 480 :=
  wordsAtOff_entails_memRegion fsp _ 1856 480 rfl

theorem memRegion_1856_split_224_288 (fsp : BitVec 64) :
    memRegion fsp 1856 = memRegion fsp 224 ∗ existsWordsAtOff fsp 36 224 ∗ memRegion (fsp + 512#64) 1344 := by
  rw [ProofLib.memRegion_split fsp 224 1632 (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 288) (k := 1344) (b' := fsp + 512#64) rfl (by bv_omega) (by decide),
      memRegion_off_eq_existsWordsAtOff fsp 36 224 (by decide)]

theorem headerReceived_stack_entails_3632 (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) :
    memRegion (fsp + 512#64) 1344 ∗
    headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
    memRegion (fsp + 2336#64) 1808 ⊢ memRegion (fsp + 512#64) 3632 := by
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 1344) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 480) (k := 1808) (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (headerReceivedStackWords_entails_memRegion fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59))

set_option maxHeartbeats 1600000 in
theorem headerReceived_ok_step_2284_18996
    {b : BitVec 64} {ext : String → Option (State → State)} (s : State) (fsp msgA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch msg_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64)
    (u224 u232 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 : BitVec 64)
    (u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 : BitVec 64)
    (Frame : SepProp) (hle : ¬ (msg_epoch > st_epoch)) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s
      (headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
       (msgA ↦₆₄ msg_epoch) ∗
       epilogueRecvStackPartA488 fsp u224 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 ∗
       ((fsp + 232#64) ↦₆₄ u232) ∗
       epilogueRecvStackPartB fsp u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
          (msgA ↦₆₄ msg_epoch) ∗
          epilogueRecvStackPartA488 fsp 8#64 w7 w13 w12 w10 w5 w4 w11 st_epoch w8 w3 w2 w6 ∗
          ((fsp + 232#64) ↦₆₄ noneCap) ∗
          epilogueRecvStackPartB fsp w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56 ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w39 ∧ sm.readReg64 .x1 = w0 ∧ sm.readReg64 .x2 = w57 ∧ sm.readReg64 .x3 = w29 ∧
        sm.readReg64 .x4 = w49 ∧ sm.readReg64 .x5 = w48 ∧ sm.readReg64 .x6 = w40 ∧ sm.readReg64 .x7 = w38 ∧
        sm.readReg64 .x8 = w1 ∧ sm.readReg64 .x9 = w43 ∧ sm.readReg64 .x10 = w35 ∧ sm.readReg64 .x11 = w34 ∧
        sm.readReg64 .x12 = w33 ∧ sm.readReg64 .x13 = w52 ∧ sm.readReg64 .x14 = w53 ∧ sm.readReg64 .x15 = w36 ∧
        sm.readReg64 .x16 = w55 ∧ sm.readReg64 .x17 = w45 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = w59 ∧ sm.readReg64 .x21 = w42 ∧ sm.readReg64 .x22 = w51 ∧ sm.readReg64 .x23 = w15 ∧
        sm.readReg64 .x24 = w31 ∧ sm.readReg64 .x25 = w32 ∧ sm.readReg64 .x26 = w47 ∧ sm.readReg64 .x27 = w16 ∧
        sm.readReg64 .x28 = w37 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w41 ∧
        TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch st_epoch = true := ule_true_of_not_gt hle
  states_recv_fetches_range b (Rust.withPanics ext) 2284 16
  states_recv_fetches_range b (Rust.withPanics ext) 3816 360
  dsimp only [tripleRatchetProgAtExt, statesRecvName, headerReceivedStackWords,
    wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB, noneCap, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp hx24; wp_steps; wp_done

theorem chunkedHeaderReceivedAt_extract_1856 (A : RustAlloc) {F : ShaCompress}
    (fsp : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A (fsp + 1856#64) st ⊢
      (∃∗ g : ThreeVecWords, wordsAtOff fsp (ekSentWordsList g st.uc.epoch) 1856 ∗
        relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch))) ∗
      existsWordsWithBytesAtOff fsp (relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek)) 50 1936 := by
  unfold chunkedHeaderReceivedAt
  have h1936 : (fsp + 1856#64) + 80#64 = fsp + BitVec.ofNat 64 1936 := by bv_omega
  rw [h1936]
  have hdec_rel : Relocatable (8 * 50) (fun dst => polyDecoderAt A dst st.receiving_ek) :=
    Relocatable.of_polyDecoderAt A st.receiving_ek
  refine sepConj_mono ?_ (Relocatable.entails_existsWordsWithBytesAtOff hdec_rel fsp 1936)
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine Entails.trans (unchunkedEkSentAt_extract A (fsp + 1856#64) { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr }) ?_
  apply Entails.sepExists_elim; intro g; refine Entails.sepExists_right g ?_
  rw [← wordsAtOff_eq_wordsAt fsp (ekSentWordsList g st.uc.epoch) 1856]
  exact sepConj_mono_right (relocatedHeap_congr fun dst => (unchunkedHeaderReceivedAt_eq_ekSentAt A dst st.uc).symm)

theorem headerReceived_out_recompose (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (g : ThreeVecWords)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) :
    epilogueRecvOutPartA out 8#64 g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0
      g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13
      w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w48 w49 w52 w53 ∗
    epilogueRecvOutPartB488 out w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
      w44 w45 w46 w47 w50 w51 w54 w55 w56 w57 w58 w59 ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗
    relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
    relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ⊢
    resultV1RecvAt A (F := F) out (.ok ⟨none, .headerReceived st⟩) := by
  rw [resultV1RecvAt_ok, chunkedStatesAt_headerReceived_unfold]; unfold chunkedHeaderReceivedAt
  have h88 : (out + 8#64) + 80#64 = out + BitVec.ofNat 64 88 := by bv_omega
  rw [h88]
  have huc := wordsAtOff_recompose_relocatedHeap out 8 (ekSentWordsList g st.uc.epoch) (G := fun dst => unchunkedHeaderReceivedAt A dst st.uc)
  have hdec := wordsAtOff_recompose_relocatedHeap out 88 (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59) (G := fun dst => polyDecoderAt A dst st.receiving_ek)
  refine Entails.trans (Entails.of_eq (show _ = (out ↦₆₄ 8#64) ∗
    (wordsAtOff out (ekSentWordsList g st.uc.epoch) 8 ∗
     relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch))) ∗
    (wordsAtOff out (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59) 88 ∗
     relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59))) ∗
    (memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none) by
    dsimp only [ekSentWordsList, vecWordsList, ct2SentWordsList, authWordsList, words50List,
      HAppend.hAppend, Append.append, List.append, wordsAtOff, epilogueRecvOutPartA, epilogueRecvOutPartB488,
      Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl))
    (Entails.trans (sepConj_mono_right (sepConj_mono huc (sepConj_mono_left hdec))) (Entails.of_eq (by ac_rfl)))

set_option maxHeartbeats 1600000 in
theorem states_recv_headerReceived_ok_2284
    {oimg : Option Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg) (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2284#64)
    (hrun : s.status = .Running) (hinv : OptCallInv oimg s) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗
       chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.headerReceived st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.headerReceived st).recv K msg = .ok ⟨none, .headerReceived st⟩ := by
    simp only [States.recv, Chunked.SendCt.HeaderReceived.epoch, Unchunked.SendCt.HeaderReceived.epoch, hle, ↓reduceIte]
  rw [hrecv, memRegion_1856_split_224_288 fsp]
  have hpre : stackAt fsp statesRecvCalleeStackX ∗
      (memRegion fsp 224 ∗ existsWordsAtOff fsp 36 224 ∗ memRegion (fsp + 512#64) 1344) ∗
      chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
      statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ⊢
      (existsWordsWithBytesAtOff fsp (relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek)) 50 1936 ∗
       ((∃∗ g : ThreeVecWords, wordsAtOff fsp (ekSentWordsList g st.uc.epoch) 1856 ∗
           relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch))) ∗
        existsWordsAtOff fsp 36 224)) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 1344 ∗
       memRegion (fsp + 2336#64) 1808 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (chunkedHeaderReceivedAt_extract_1856 A fsp st)))) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsWithBytesAtOff, existsWordsAtOff, wordsBytes, HAppend.hAppend, Append.append, List.append,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  apply sepWP_intro_ex_nest; intro w10; apply sepWP_intro_ex_nest; intro w11; apply sepWP_intro_ex_nest; intro w12; apply sepWP_intro_ex_nest; intro w13; apply sepWP_intro_ex_nest; intro w14; apply sepWP_intro_ex_nest; intro w15
  apply sepWP_intro_ex_nest; intro w16; apply sepWP_intro_ex_nest; intro w17; apply sepWP_intro_ex_nest; intro w18; apply sepWP_intro_ex_nest; intro w19; apply sepWP_intro_ex_nest; intro w20; apply sepWP_intro_ex_nest; intro w21
  apply sepWP_intro_ex_nest; intro w22; apply sepWP_intro_ex_nest; intro w23; apply sepWP_intro_ex_nest; intro w24; apply sepWP_intro_ex_nest; intro w25; apply sepWP_intro_ex_nest; intro w26; apply sepWP_intro_ex_nest; intro w27
  apply sepWP_intro_ex_nest; intro w28; apply sepWP_intro_ex_nest; intro w29; apply sepWP_intro_ex_nest; intro w30; apply sepWP_intro_ex_nest; intro w31; apply sepWP_intro_ex_nest; intro w32; apply sepWP_intro_ex_nest; intro w33
  apply sepWP_intro_ex_nest; intro w34; apply sepWP_intro_ex_nest; intro w35; apply sepWP_intro_ex_nest; intro w36; apply sepWP_intro_ex_nest; intro w37; apply sepWP_intro_ex_nest; intro w38; apply sepWP_intro_ex_nest; intro w39
  apply sepWP_intro_ex_nest; intro w40; apply sepWP_intro_ex_nest; intro w41; apply sepWP_intro_ex_nest; intro w42; apply sepWP_intro_ex_nest; intro w43; apply sepWP_intro_ex_nest; intro w44; apply sepWP_intro_ex_nest; intro w45
  apply sepWP_intro_ex_nest; intro w46; apply sepWP_intro_ex_nest; intro w47; apply sepWP_intro_ex_nest; intro w48; apply sepWP_intro_ex_nest; intro w49; apply sepWP_intro_ex_nest; intro w50; apply sepWP_intro_ex_nest; intro w51
  apply sepWP_intro_ex_nest; intro w52; apply sepWP_intro_ex_nest; intro w53; apply sepWP_intro_ex_nest; intro w54; apply sepWP_intro_ex_nest; intro w55; apply sepWP_intro_ex_nest; intro w56; apply sepWP_intro_ex_nest; intro w57
  apply sepWP_intro_ex_nest; intro w58; apply sepWP_intro_ex_nest; intro w59
  rw [sepConj_assoc (relocatedHeap _ _), sepConj_left_comm (relocatedHeap _ _)]
  apply sepWP_intro_ex; intro g
  apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232; apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264
  apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280; apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312
  apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328; apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360
  apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376; apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392; apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408
  apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424; apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456
  apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472; apply sepWP_intro_ex; intro u480; apply sepWP_intro_ex; intro u488; apply sepWP_intro_ex; intro u496; apply sepWP_intro_ex; intro u504
  rw [emp_sepConj]; unfold messageAt
  have hstep1 := headerReceived_ok_step_2284_18996 (b := b) (ext := ext) s fsp msgA
    g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2
    st.uc.epoch msg.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
    u224 u232 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504
    u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488
    (((fsp + 240#64) ↦₆₄ u240) ∗
     relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
     relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗
     stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 1344 ∗
     memRegion (fsp + 2336#64) 1808 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
     memRegion selfA chunkedStatesSize ∗ statesRecvRoAt b ∗ A.pool)
    hle hfsp_align hpc hrun hsp hx24
  refine seq_clean_opt_sr hinv (SepWP.weaken_pre (Entails.of_eq ?_) hstep1) ?_
  · dsimp only [headerReceivedStackWords, words50List, ekSentWordsList, vecWordsList, ct2SentWordsList, authWordsList,
      wordsBytes, HAppend.hAppend, Append.append, List.append, wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB,
      Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl
  · intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
      hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, htr1⟩
    rw [hx19] at hx19_1
    have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
    have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
    have hexit := epilogue_18996_exit_none_488_opt_sr hH s0 s1 outA
      8#64 u240 g.auth.v2.w1 w13 w12 w10 g.auth.v1.w2 g.auth.v1.w1 w11 st.uc.epoch g.auth.v2.w2 g.auth.v1.w0 g.v1.w2 g.auth.v2.w0
      w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56
      (relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
      hsp0_align hpc1 hrun1 hinv1 hsp10 hx19_1 htr10
    dsimp only at hexit; rw [← hfsp_eq] at hexit
    refine SepWP.mono (SepWP.weaken_pre ?_ hexit) ?_
    · have hstk3632 := headerReceived_stack_entails_3632 fsp
        g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2
        st.uc.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
      unfold messageAt
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (fsp + 512#64) 1344 ∗
         headerReceivedStackWords fsp g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
         memRegion (fsp + 2336#64) 1808) ∗
        (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
         epilogueRecvStackPartA488 fsp 8#64 g.auth.v2.w1 w13 w12 w10 g.auth.v1.w2 g.auth.v1.w1 w11 st.uc.epoch g.auth.v2.w2 g.auth.v1.w0 g.v1.w2 g.auth.v2.w0 ∗
         ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ u240) ∗
         epilogueRecvStackPartB fsp w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56 ∗
         statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
         (relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
          relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          statesRecvRoAt b ∗ A.pool)) by ac_rfl))
        (Entails.trans (sepConj_mono_left hstk3632) (Entails.of_eq (by ac_rfl)))
    · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      rw [hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
          hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx20_1, hx21_1,
          hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx30_1] at hPf
      have hrec := headerReceived_out_recompose A outA st g w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
      refine ⟨Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
        (epilogueRecvOutPartA outA 8#64 g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0
           g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13
           w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w48 w49 w52 w53 ∗
         epilogueRecvOutPartB488 outA w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
           w44 w45 w46 w47 w50 w51 w54 w55 w56 w57 w58 w59 ∗
         memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
         relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
         relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59))) ∗
        (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
         statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) by ac_rfl))
        (sepConj_mono_left hrec)), hsp_f, hcs_f, htr_f⟩

theorem stackAt_statesRecvCallee_eq_dropGluePoly16 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropGluePoly16Stack :=
  stackAt_split_bottom fsp dropGluePoly16Stack 15424 (by decide)

private theorem toNat_ne_zero_of_beq_false_s2 {c : BitVec 64} (hc : ¬ ((c == 0#64) = true)) :
    c.toNat ≠ 0 := by
  intro h; apply hc
  have h0 : c = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h)
  subst h0; rfl

private theorem layoutOk_one_of_ne_zero_s2 {n : Nat} (hne : n ≠ 0) (hlt : n < 2 ^ 63) :
    LayoutOk n 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩

private theorem protoAuthenticatorAt_entails_dealloc_lt_s2 (A : RustAlloc) (a : BitVec 64)
    (auth : ProtoAuthenticator) :
    protoAuthenticatorAt A a auth ⊢
      ∃∗ g : TwoVecGhost, ⌜g.v1.cap.toNat < 2 ^ 63 ∧ g.v2.cap.toNat < 2 ^ 63⌝ ∗
        twoVecHeadersAt a g ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  unfold protoAuthenticatorAt vecU8
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_bound A a c1 p1 auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc_bound A (a + 24#64) c2 p2 auth.macKey
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  refine Entails.trans (sepConj_mono h1 h2) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c1.toNat < 2 ^ 63⌝ ∗ (⌜c2.toNat < 2 ^ 63⌝ ∗
      (twoVecHeadersAt a ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ∗ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2)) by
    unfold twoVecHeadersAt; dsimp only; ac_rfl)) ?_
  apply Entails.pure_left; intro hlt1; apply Entails.pure_left; intro hlt2
  exact Entails.pure_right ⟨hlt1, hlt2⟩ (Entails.refl _)

theorem chunkedHeaderReceivedAt_1856_entails_err (A : RustAlloc) {F : ShaCompress}
    (fsp : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A (fsp + 1856#64) st ⊢
      ∃∗ g12 : TwoVecGhost, ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64, ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS ∧ g12.v1.cap.toNat < 2 ^ 63 ∧ g12.v2.cap.toNat < 2 ^ 63 ∧ c3.toNat < 2 ^ 63⌝ ∗
        (((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ memRegion (fsp + 1872#64) 8 ∗
         ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ memRegion (fsp + 1896#64) 8 ∗
         ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗
         ((fsp + 1928#64) ↦₆₄ st.uc.epoch)) ∗
        vecCapPtrDealloc A g12.v1.cap g12.v1.ptr ∗ vecCapPtrDealloc A g12.v2.cap g12.v2.ptr ∗
        vecCapPtrDealloc A c3 p3 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 := by
  unfold chunkedHeaderReceivedAt; rw [unchunkedHeaderReceivedAt_eq_ekSentAt]; unfold unchunkedEkSentAt
  have hauth : authenticatorAt A (fsp + 1856#64) st.uc.auth =
      protoAuthenticatorAt A (fsp + 1856#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩ := rfl
  have h1904 : (fsp + 1856#64) + 48#64 = fsp + 1904#64 := by bv_omega
  have h1928 : (fsp + 1856#64) + 72#64 = fsp + 1928#64 := by bv_omega
  have h1936 : (fsp + 1856#64) + 80#64 = fsp + 1936#64 := by bv_omega
  rw [hauth, h1904, h1928, h1936]
  have hv3 : vecU8 A (fsp + 1904#64) st.uc.hdr ⊢ ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64,
      ⌜c3.toNat < 2 ^ 63⌝ ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗ vecCapPtrDealloc A c3 p3 := by
    unfold vecU8; apply Entails.sepExists_elim; intro c3; apply Entails.sepExists_elim; intro p3
    refine Entails.sepExists_right c3 (Entails.sepExists_right p3 ?_)
    have h := vecU8At_entails_capPtr_dealloc_bound A (fsp + 1904#64) c3 p3 st.uc.hdr
    have h1912 : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    have h1920 : (fsp + 1904#64) + 16#64 = fsp + 1920#64 := by bv_omega
    rw [h1912, h1920] at h; exact h
  have hdec : polyDecoderAt A (fsp + 1936#64) st.receiving_ek ⊢ ∃∗ vecs : List (List Pt),
      ⌜vecs.length = NUM_POLYS⌝ ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 := by
    refine Entails.trans (polyDecoderAt_entails_vecs_tail A (fsp + 1936#64) st.receiving_ek) ?_
    apply Entails.sepExists_elim; intro vecs; refine Entails.sepExists_right vecs ?_
    have h2320 : (fsp + 1936#64) + 384#64 = fsp + 2320#64 := by bv_omega
    rw [h2320]; exact Entails.refl _
  refine Entails.trans (sepConj_mono
    (sepConj_mono (protoAuthenticatorAt_entails_dealloc_lt_s2 A (fsp + 1856#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩)
      (sepConj_mono_left hv3)) hdec) ?_
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro vecs
  rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g12
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro c3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p3
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜g12.v1.cap.toNat < 2 ^ 63 ∧ g12.v2.cap.toNat < 2 ^ 63⌝ ∗
    (⌜c3.toNat < 2 ^ 63⌝ ∗ (⌜vecs.length = NUM_POLYS⌝ ∗
      ((twoVecHeadersAt (fsp + 1856#64) g12 ∗
        ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch)) ∗
       vecCapPtrDealloc A g12.v1.cap g12.v1.ptr ∗ vecCapPtrDealloc A g12.v2.cap g12.v2.ptr ∗
       vecCapPtrDealloc A c3 p3 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlt1, hlt2⟩; apply Entails.pure_left; intro hlt3; apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right g12 (Entails.sepExists_right c3 (Entails.sepExists_right p3 (Entails.sepExists_right vecs ?_)))
  refine Entails.pure_right ⟨hlen, hlt1, hlt2, hlt3⟩ ?_; unfold twoVecHeadersAt
  have h1864 : (fsp + 1856#64) + 8#64 = fsp + 1864#64 := by bv_omega
  have h1872 : (fsp + 1856#64) + 16#64 = fsp + 1872#64 := by bv_omega
  have h1880 : (fsp + 1856#64) + 24#64 = fsp + 1880#64 := by bv_omega
  have h1888 : (fsp + 1856#64) + 32#64 = fsp + 1888#64 := by bv_omega
  have h1896 : (fsp + 1856#64) + 40#64 = fsp + 1896#64 := by bv_omega
  rw [h1864, h1872, h1880, h1888, h1896]; exact Entails.of_eq (by ac_rfl)

theorem headerReceived_err_stack_combine (fsp : BitVec 64) (g12 : TwoVecGhost) (c3 p3 ep : BitVec 64) :
    memRegion fsp 1856 ∗
    (((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ memRegion (fsp + 1872#64) 8 ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ memRegion (fsp + 1896#64) 8 ∗
     ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗ ((fsp + 1928#64) ↦₆₄ ep)) ∗
    memRegion (fsp + 1936#64) polyArrayBytes ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ⊢
    memRegion fsp 4144 := by
  have h48 := twoVecHeadersAt_entails_memRegion_48 (fsp + 1856#64) g12; unfold twoVecHeadersAt at h48
  have h1864 : (fsp + 1856#64) + 8#64 = fsp + 1864#64 := by bv_omega
  have h1872 : (fsp + 1856#64) + 16#64 = fsp + 1872#64 := by bv_omega
  have h1880 : (fsp + 1856#64) + 24#64 = fsp + 1880#64 := by bv_omega
  have h1888 : (fsp + 1856#64) + 32#64 = fsp + 1888#64 := by bv_omega
  have h1896 : (fsp + 1856#64) + 40#64 = fsp + 1896#64 := by bv_omega
  rw [h1864, h1872, h1880, h1888, h1896] at h48
  have h24 := Drop.header_cells_entails_memRegion_24 (fsp + 1904#64) c3 p3
  have h1912 : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
  have h1920 : (fsp + 1904#64) + 16#64 = fsp + 1920#64 := by bv_omega
  rw [h1912, h1920] at h24
  have h8 := ProofLib.pointsTo64_entails_memRegion (fsp + 1928#64) ep
  have h400 : memRegion (fsp + 1936#64) polyArrayBytes ∗ memRegion (fsp + 2320#64) 16 ⊢ memRegion (fsp + 1936#64) 400 := by
    have h2320 : fsp + 2320#64 = (fsp + 1936#64) + 384#64 := by bv_omega
    rw [h2320]; exact polyDecoder_post_join (fsp + 1936#64)
  rw [memRegion_4144_split_1856_480 fsp,
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 48) (k := 432) (b' := fsp + 1904#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1904#64) (n := 24) (k := 408) (b' := fsp + 1928#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1928#64) (n := 8) (k := 400) (b' := fsp + 1936#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ = memRegion fsp 1856 ∗
    ((((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ memRegion (fsp + 1872#64) 8 ∗
      ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ memRegion (fsp + 1896#64) 8) ∗
     (((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8) ∗
     ((fsp + 1928#64) ↦₆₄ ep) ∗ (memRegion (fsp + 1936#64) polyArrayBytes ∗ memRegion (fsp + 2320#64) 16)) ∗
    memRegion (fsp + 2336#64) 1808 by ac_rfl))
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono h48 (sepConj_mono h24 (sepConj_mono h8 h400)))))

theorem headerReceived_err_step_2284_2340
    {oimg : Option Obj.Image} {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg)
    (s : State) (fsp outA msgA st_epoch msg_epoch c1 p1 v_out0 v_out16 : BitVec 64) (b_out8 : BitVec 8)
    (Frame : SepProp) (hc1_lt : c1.toNat < 2 ^ 63) (hgt : msg_epoch > st_epoch) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2284#64)
    (hrun : s.status = .Running) (hinv : OptCallInv oimg s) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2340#64) s
      (((outA ↦₆₄ v_out0) ∗ ((outA + 8#64) ↦₈ b_out8) ∗ ((outA + 16#64) ↦₆₄ v_out16)) ∗
       ((fsp + 1856#64) ↦₆₄ c1) ∗ ((fsp + 1864#64) ↦₆₄ p1) ∗ ((fsp + 1928#64) ↦₆₄ st_epoch) ∗
       vecCapPtrDealloc A c1 p1 ∗ (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_epoch)) ∗
          ((fsp + 1856#64) ↦₆₄ c1) ∗ ((fsp + 1864#64) ↦₆₄ p1) ∗ ((fsp + 1928#64) ↦₆₄ st_epoch) ∗
          (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A extHookStack)) :=
    hH.dealloc_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
  simp only [specWithOptInv, rustDeallocExternSpecWithStack, extHookStack] at hdealloc_raw ⊢
  have hule : BitVec.ule msg_epoch st_epoch = false := ule_false_of_gt hgt
  states_recv_fetches_range b (Rust.withPanics ext) 2284 56
  dsimp only [tripleRatchetProgAtExt, statesRecvName, vecCapPtrDealloc, noneCap, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp hx19 hx24
  by_cases hc1 : (c1 == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
  · wp_steps; refine Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · have hlay : LayoutOk c1.toNat 1 := layoutOk_one_of_ne_zero_s2 (toNat_ne_zero_of_beq_false_s2 hc1) hc1_lt
    apply SepWP.seq_optImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc")) hinv
    wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hinv1
    wp_apply; refine Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem headerReceived_err_step_2340_2360
    {oimg : Option Obj.Image} {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg)
    (s : State) (fsp c2 p2 : BitVec 64) (Frame : SepProp) (hc2_lt : c2.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2340#64)
    (hrun : s.status = .Running) (hinv : OptCallInv oimg s) (hsp : s.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2360#64) s
      (((fsp + 1880#64) ↦₆₄ c2) ∗ ((fsp + 1888#64) ↦₆₄ p2) ∗
       vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1880#64) ↦₆₄ c2) ∗ ((fsp + 1888#64) ↦₆₄ p2) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A extHookStack)) :=
    hH.dealloc_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
  simp only [specWithOptInv, rustDeallocExternSpecWithStack, extHookStack] at hdealloc_raw ⊢
  states_recv_fetches_range b (Rust.withPanics ext) 2340 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp
  by_cases hc2 : (c2 == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
  · wp_steps; refine Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · have hlay : LayoutOk c2.toNat 1 := layoutOk_one_of_ne_zero_s2 (toNat_ne_zero_of_beq_false_s2 hc2) hc2_lt
    wp_steps; wp_apply; refine Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem headerReceived_err_step_2360_2380
    {oimg : Option Obj.Image} {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg)
    (s : State) (fsp c3 p3 : BitVec 64) (Frame : SepProp) (hc3_lt : c3.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2360#64)
    (hrun : s.status = .Running) (hinv : OptCallInv oimg s) (hsp : s.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2380#64) s
      (((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
       vecCapPtrDealloc A c3 p3 ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ A.pool ∗ stackAt fsp extHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A extHookStack)) :=
    hH.dealloc_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc")) (by simp only [arm64_norm])
  simp only [specWithOptInv, rustDeallocExternSpecWithStack, extHookStack] at hdealloc_raw ⊢
  states_recv_fetches_range b (Rust.withPanics ext) 2360 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp
  by_cases hc3 : (c3 == 0#64) = true <;> simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
  · wp_steps; refine Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · have hlay : LayoutOk c3.toNat 1 := layoutOk_one_of_ne_zero_s2 (toNat_ne_zero_of_beq_false_s2 hc3) hc3_lt
    wp_steps; wp_apply; refine Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem headerReceived_err_step_2380_19324
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (s : State) (fsp : BitVec 64) (vecs : List (List Pt)) (hvecs : vecs.length = NUM_POLYS)
    (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2380#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64) s
      (vecPtListOf A (fsp + 1936#64) vecs ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 1936#64) polyArrayBytes ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  have hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + (0#64 - 38716#64))
      (dropGlueSortedSetPt16Spec A) := by
    have hrel := fnAddr_statesRecv_rel_sr (b := b) (ext := ext) dropSortedSetPt16Name 38716
    refine Drop.sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
    dsimp only [dropProgAtExt] at *; rw [← hrel]; bv_omega
  simp only [dropGlueSortedSetPt16Spec] at hdrop
  states_recv_fetches_range b (Rust.withPanics ext) 2380 16
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp; wp_steps; wp_call hdrop ⟨s.sp + 1936#64, vecs⟩; wp_steps
  refine Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

set_option maxHeartbeats 1200000 in
theorem states_recv_headerReceived_err_2284
    {oimg : Option Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg) (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 2284#64)
    (hrun : s.status = .Running) (hinv : OptCallInv oimg s) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗ chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗
       memRegion (fsp + 2336#64) 1808 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.headerReceived st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.headerReceived st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
    simp only [States.recv, Chunked.SendCt.HeaderReceived.epoch, Unchunked.SendCt.HeaderReceived.epoch, hgt, ↓reduceIte]
  rw [hrecv, memRegion_out_960_split_err outA, stackAt_statesRecvCallee_eq_extHook_sr fsp]
  refine SepWP.fold (chunkedHeaderReceivedAt_1856_entails_err A fsp st) (by sep_focus) ?_
  unfold messageAt; wp_pull_exists; rename_i v_out16 b_out8 v_out0 g12 c3 p3 vecs
  wp_focus_pure; intro ⟨hvecs, hc1_lt, hc2_lt, hc3_lt⟩
  let Rest0 := statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
    messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt b
  let ErrRes := resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch)))
  have hstep1 := headerReceived_err_step_2284_2340 hH s fsp outA msgA st.uc.epoch msg.epoch
    g12.v1.cap g12.v1.ptr v_out0 v_out16 b_out8
    (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗ memRegion (fsp - 19552#64) 3168 ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
     memRegion (fsp + 1896#64) 8 ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗
     vecCapPtrDealloc A g12.v2.cap g12.v2.ptr ∗ vecCapPtrDealloc A c3 p3 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗
     memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗ Rest0)
    hc1_lt hgt hfsp_align hpc hrun hinv hsp hx19 hx24
  refine seq_clean_opt_sr hinv (SepWP.weaken_pre (Entails.of_eq (by dsimp only [Rest0]; ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, htr1⟩
  refine SepWP.fold (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg.epoch) (by sep_focus) ?_
  have hstep2 := headerReceived_err_step_2340_2360 hH s1 fsp g12.v2.cap g12.v2.ptr
    (ErrRes ∗ ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     (msgA ↦₆₄ msg.epoch) ∗ memRegion (fsp - 19552#64) 3168 ∗ memRegion fsp 1856 ∗ memRegion (fsp + 1872#64) 8 ∗
     memRegion (fsp + 1896#64) 8 ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗
     vecCapPtrDealloc A c3 p3 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗
     memRegion (fsp + 2336#64) 1808 ∗ Rest0)
    hc2_lt hfsp_align hpc1 hrun1 hinv1 hsp1
  refine seq_clean_opt_sr hinv1 (SepWP.weaken_pre (Entails.of_eq (by dsimp only [ErrRes]; ac_rfl)) hstep2) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, htr2⟩
  have hstep3 := headerReceived_err_step_2360_2380 hH s2 fsp c3 p3
    (ErrRes ∗ ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ (msgA ↦₆₄ msg.epoch) ∗
     memRegion (fsp - 19552#64) 3168 ∗ memRegion fsp 1856 ∗ memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗
     memRegion (fsp + 1920#64) 8 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗
     memRegion (fsp + 2336#64) 1808 ∗ Rest0)
    hc3_lt hfsp_align hpc2 hrun2 hinv2 hsp2
  refine seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep3) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, htr3⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_extHook_sr fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_dropGluePoly16 fsp)) (by sep_focus) ?_
  have hstep4 := headerReceived_err_step_2380_19324 hH.dealloc s3 fsp vecs hvecs
    (memRegion (fsp - 19552#64) 15424 ∗ ErrRes ∗
     ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗
     ((fsp + 1912#64) ↦₆₄ p3) ∗ (msgA ↦₆₄ msg.epoch) ∗ memRegion fsp 1856 ∗ memRegion (fsp + 1872#64) 8 ∗
     memRegion (fsp + 1896#64) 8 ∗ memRegion (fsp + 1920#64) 8 ∗ memRegion (fsp + 2320#64) 16 ∗
     memRegion (fsp + 2336#64) 1808 ∗ Rest0)
    hfsp_align hpc3 hrun3 hsp3
  refine seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep4) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, htr4⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_dropGluePoly16 fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (headerReceived_err_stack_combine fsp g12 c3 p3 st.uc.epoch) (by sep_focus) ?_
  have htr40 : TraceCalleeSaved s4 s0 := htr4.trans (htr3.trans (htr2.trans (htr1.trans htr)))
  have hsp40 : s4.sp = s0.sp - 4240#64 := by rw [hsp4, hfsp_eq]
  have hepil := states_recv_epilogue_19324 (b := b) (ext := ext) s0 s4
    (ErrRes ∗ memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
    hsp0_align hpc4 hrun4 hsp40 htr40
  rw [← hfsp_eq] at hepil
  refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by dsimp only [Rest0, ErrRes]; unfold messageAt; ac_rfl)) hepil) ?_
  intro sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by dsimp only [ErrRes]; unfold messageAt; ac_rfl)), hspf, hcs, htrf⟩

private theorem states_recv_headerReceived_ok_opt
    {oimg : Option Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hH : SimpleRecvHooks b A ext oimg)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (specWithOptInv oimg (statesRecvVariantSpec A F K b (.headerReceived st) msg)) := by
  refine subroutine_ok_statesRecvVariantSpec_opt_of_sepWP_sr (.headerReceived st) msg ?_
  intro outA selfA msgA s0 hpc0 hrun0 hinv0 hsp0_align hb hx0 hx1 hx2 _
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue (b := b) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerReceived st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) hsp0_align hpc0 hrun0
  refine seq_clean_opt_sr hinv0 hpro ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; rw [chunkedStatesAt_headerReceived_unfold]
  have hdisp := states_recv_dispatch (b := b) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 8#64
    (chunkedHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 488#64) 440 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine seq_clean_opt_sr hinv1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  rw [memRegion_4144_split_1856_480 (s0.sp - 4240#64), stackAt_statesRecvCallee_eq_extHook_sr (s0.sp - 4240#64)]
  have hmc := headerReceived_memcpy_2268_2284 hH s2 (s0.sp - 4240#64) selfA st
    ((selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 488#64) 440 ∗ statesRecvRoAt b ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     memRegion ((s0.sp - 4240#64) - 19552#64) 3168 ∗ memRegion (s0.sp - 4240#64) 1856 ∗
     memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗ statesRecvSavedCells s0)
    hfsp_align hpc2 hrun2 hinv2 hsp2 hx1_2
  refine seq_clean_opt_sr hinv2 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hmc) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hsp3, hx19_3, hx24_3, _, htr3⟩
  rw [hx19_2] at hx19_3; rw [hx24_2] at hx24_3
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans (htr2.trans htr1)
  have hself2 :
      stackAt (s0.sp - 4240#64) extHookStack ∗ chunkedHeaderReceivedAt A (s0.sp - 4240#64 + 1856#64) st ∗
      memRegion (selfA + 8#64) 480 ∗ (selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 488#64) 440 ∗
      statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
      memRegion ((s0.sp - 4240#64) - 19552#64) 3168 ∗
      memRegion (s0.sp - 4240#64) 1856 ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗ statesRecvSavedCells s0 ⊢
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 1856 ∗
      chunkedHeaderReceivedAt A (s0.sp - 4240#64 + 1856#64) st ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗
      statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool := by
    rw [stackAt_statesRecvCallee_eq_extHook_sr (s0.sp - 4240#64)]
    refine Entails.trans (Entails.of_eq (show _ =
      ((selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 8#64) 480 ∗ memRegion (selfA + 488#64) 440) ∗
      (memRegion ((s0.sp - 4240#64) - 19552#64) 3168 ∗ stackAt (s0.sp - 4240#64) extHookStack ∗
       memRegion (s0.sp - 4240#64) 1856 ∗
       chunkedHeaderReceivedAt A (s0.sp - 4240#64 + 1856#64) st ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) by ac_rfl))
      (Entails.trans (sepConj_mono_left (selfA_headerReceived_entails_memRegion_928 selfA)) (Entails.of_eq (by ac_rfl)))
  refine SepWP.weaken_pre hself2 ?_
  by_cases hgt : msg.epoch > st.uc.epoch
  · exact states_recv_headerReceived_err_2284 hH s0 s3 (s0.sp - 4240#64) outA selfA msgA st msg
      hgt rfl hsp0_align hfsp_align hpc3 hrun3 hinv3 hsp3 hx19_3 hx24_3 htr30
  · exact states_recv_headerReceived_ok_2284 hH s0 s3 (s0.sp - 4240#64) outA selfA msgA st msg
      hgt rfl hsp0_align hfsp_align hpc3 hrun3 hinv3 hsp3 hx19_3 hx24_3 htr30

theorem states_recv_headerReceived_ok_ext
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (statesRecvVariantSpec A F K b (.headerReceived st) msg) :=
  subroutine_ok_of_optNone (states_recv_headerReceived_ok_opt (SimpleRecvHooks.of_allocContracts hA) st msg)

theorem states_recv_headerReceived_ok_x
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpec A F K img.base (.headerReceived st) msg).inImage img) :=
  states_recv_headerReceived_ok_opt (SimpleRecvHooks.of_allocContractsX hA hdealloc) st msg

/-- `.headerReceived` arm of `<States>::recv` lifted to `statesRecvVariantSpecExt` (`40176`B stack)
    under `AllocContractsX img A ext` and `DeallocOkExt img.base A ext`. -/
theorem states_recv_headerReceived_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hAx : AllocContractsX img A ext) (hdealloc : DeallocOkExt img.base A ext)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.headerReceived st) msg).inImage img) :=
  statesRecvVariant_inImage_grow_stack (states_recv_headerReceived_ok_x hAx hdealloc st msg)

end CryptoVerification.SpqrV1.States.Recv
