/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `KeysUnsampled` Arm under `AllocContractsX`

Contract-backed (`AllocContractsX`, `extHookStack = 16384` B) proofs of the shared `+18996`
`Ok(V1Recv)` epilogue and the `States.keysUnsampled` arm (`0x554b4`, `+96`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth
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

@[local wp_norm] private theorem simple1_exists_two_pow_zero : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local wp_norm] private theorem simple1_exists_two_pow_one : (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local wp_norm] private theorem frozenLoaded_writeReg64_s1 (img : Obj.Image) (s : State) (r : Reg) (v : BitVec 64) :
    img.FrozenLoaded (s.writeReg64 r v) ↔ img.FrozenLoaded s := by
  have hmem : (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem frozenLoaded_setPC_s1 (img : Obj.Image) (s : State) (pc : BitVec 64) :
    img.FrozenLoaded (s.setPC pc) ↔ img.FrozenLoaded s := by
  have hmem : (s.setPC pc).mem = s.mem := by cases s; rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem frozenLoaded_setPState_s1 (img : Obj.Image) (s : State) (ps : PState) :
    img.FrozenLoaded (s.setPState ps) ↔ img.FrozenLoaded s := by
  have hmem : (s.setPState ps).mem = s.mem := by cases s; rfl
  rw [Obj.Image.frozenLoaded_iff, Obj.Image.frozenLoaded_iff, hmem]

@[local wp_norm] private theorem symtab_writeReg64_s1 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[local wp_norm] private theorem symtab_setPC_s1 (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

@[local wp_norm] private theorem symtab_setPState_s1 (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")

private theorem seq_clean_inImage_s1 {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q sm →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq_inImage ⟨hfrozen, hsym⟩
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ ⟨hfrozen_m, hsym_m⟩ =>
      SepWP.weaken_pre hent (h2 sm hpc hrun hfrozen_m hsym_m hq))

theorem stackAt_statesRecvCallee_eq_extHook_simple (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

theorem stackAt_statesRecvStackX_eq_extHook_simple (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 7408 ∗ stackAt sp extHookStack :=
  ProofLib.stackAt_split_bottom sp extHookStack 7408 (by decide)

theorem layoutOk_one_of_ne_zero_simple {n : Nat} (hne : n ≠ 0) (hlt : n < 2 ^ 63) :
    LayoutOk n 1 :=
  ⟨by omega, ⟨0, rfl⟩, by omega⟩

theorem subroutine_ok_statesRecvVariantSpec_inImage_of_sepWP
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hwp : ∀ (outA selfA msgA : BitVec 64) (s0 : State),
      s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName → s0.status = .Running →
      img.FrozenLoaded s0 → s0.symtab = img.symtab →
      (s0.sp &&& 15#64 == 0#64) = true → img.base &&& 0xfff#64 = 0#64 →
      s0.readReg64 .x0 = outA → s0.readReg64 .x1 = selfA → s0.readReg64 .x2 = msgA →
      statesRecvPreInv self →
      SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s0
        (stackAt s0.sp statesRecvStackX ∗
         (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA self ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool))
        (fun sf Pf =>
          (Pf ⊢ resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
            statesRecvRoAt img.base ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpec A F K img.base self msg).inImage img) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [Spec.inImage, statesRecvVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, ⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA self ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool), R,
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [Spec.inImage, statesRecvVariantSpec]
  refine SepWPp.of_sepWP (SepWP.mono (hwp outA selfA msgA s0 hpc0 hrun0 hfrozen0 hsym0 hsp0_align hb hx0 hx1 hx2 hinv) ?_)
  intro sf Pf hpc_f hrun_f ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine SepWPp.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_f, hcs_f⟩
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right htr_f (Entails.refl _)))
    (Satisfies.mono (sepConj_mono_left hPf) hsat)

/-! ## Shared `+18996` `Ok(V1Recv)` Epilogue under `AllocContractsX` -/

theorem epilogue_step_19280_19324_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s : State) (fsp out : BitVec 64)
    (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376)
    (uq888 uq904 uq944 q512 q528 q544 : BitVec 128)
    (u920 u928 u936 w232 w560 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19280#64)
    (hrun : s.status = .Running)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx2 : s.readReg64 .x2 = 376#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 19324#64)
      s
      (stackAt fsp extHookStack ∗
       memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
       ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       ((fsp + 576#64) ↦ₛ bs576) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp extHookStack ∗
          ((out + 512#64) ↦ₛ bs576) ∗
          ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗
          ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ w232) ∗
          ((out + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((out + 944#64) ↦₁₂₈ q512) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
          ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
          ((fsp + 576#64) ↦ₛ bs576) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img) :=
    hA.session_memcpy_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))
  simp only [sessionMemcpySpec, extHookStack, Spec.inImage] at hmemcpy ⊢
  rw [← hbs576]
  states_recv_fetches_range img.base (Rust.withPanics ext) 19280 44
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_simp_pre [pointsTo128, sepConj_assoc]
  wp_steps
  wp_call hmemcpy (s.readReg64 .x19 + 512#64, s.sp + 576#64, bs576)
  wp_steps
  simp only [pointsTo128, sepConj_assoc]
  wp_done

set_option maxHeartbeats 1600000 in
theorem epilogue_18996_exit_none_488_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s0 s1 : State) (out : BitVec 64)
    (w224 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 18996#64)
    (hrun1 : s1.status = .Running)
    (hfrozen1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    let fsp := s0.sp - 4240#64
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
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
  apply sepWP_intro_ex; intro q512; apply sepWP_intro_ex; intro q528; apply sepWP_intro_ex; intro q544; apply sepWP_intro_ex; intro w560
  apply sepWP_intro_ex_pure; intro bs576 hbs576; apply sepWP_intro_ex; intro q960; apply sepWP_intro_ex; intro uq488; apply sepWP_intro_ex; intro u504
  apply sepWP_intro_ex; intro uq888; apply sepWP_intro_ex; intro uq904; apply sepWP_intro_ex; intro u920; apply sepWP_intro_ex; intro u928
  apply sepWP_intro_ex; intro u936; apply sepWP_intro_ex; intro uq944
  apply sepWP_intro_ex; intro u0; apply sepWP_intro_ex; intro u8; apply sepWP_intro_ex; intro u16; apply sepWP_intro_ex; intro u24; apply sepWP_intro_ex; intro u32; apply sepWP_intro_ex; intro u40
  apply sepWP_intro_ex; intro u48; apply sepWP_intro_ex; intro u56; apply sepWP_intro_ex; intro u64; apply sepWP_intro_ex; intro u72; apply sepWP_intro_ex; intro u80; apply sepWP_intro_ex; intro u88
  apply sepWP_intro_ex; intro u96; apply sepWP_intro_ex; intro u104; apply sepWP_intro_ex; intro u112; apply sepWP_intro_ex; intro u120; apply sepWP_intro_ex; intro u128; apply sepWP_intro_ex; intro u136
  apply sepWP_intro_ex; intro u144; apply sepWP_intro_ex; intro u152; apply sepWP_intro_ex; intro u160; apply sepWP_intro_ex; intro u168; apply sepWP_intro_ex; intro u176; apply sepWP_intro_ex; intro u184
  apply sepWP_intro_ex; intro u192; apply sepWP_intro_ex; intro u200; apply sepWP_intro_ex; intro u208; apply sepWP_intro_ex; intro u216; apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232
  apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264; apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280
  apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312; apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328
  apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360; apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376
  apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392; apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408; apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424
  apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456; apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472
  apply sepWP_intro_ex; intro u480; rw [emp_sepConj]
  have hstepA := epilogue_step_18996_19128 (b := img.base) (ext := ext) s1 fsp out
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
  refine seq_clean_inImage_s1 hfrozen1 hsym1 (SepWP.weaken_pre ?_ hstepA) ?_
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
  · intro s2 hpc2 hrun2 hfrozen2 hsym2 ⟨hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx16_2, hx17_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx29_2, hv0_2, htr2⟩
    let outPartA := epilogueRecvOutPartA out
      w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
      (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
      (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
      (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
      (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14)
    have hstepB := epilogue_step_19128_19280 (b := img.base) (ext := ext) s2 fsp out
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
    refine seq_clean_inImage_s1 hfrozen2 hsym2 (SepWP.weaken_pre (Entails.of_eq (by dsimp only [outPartA]; ac_rfl)) hstepB) ?_
    intro s3 hpc3 hrun3 hfrozen3 hsym3 ⟨hsp3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx29_3, htr3⟩
    rw [hx23_2, hx27_2, hx3_2, hx24_2, hx17_2, hx26_2, hx22_2, hx16_2, hx2_2, hx20_2, hv0_2]
    let outPartB488 := epilogueRecvOutPartB488 out
      w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
      w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
      w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20)
    have hstepC := epilogue_step_19280_19324_ext hA s3 fsp out bs576 hbs576 uq888 uq904 uq944 q512 q528 q544 u920 u928 u936 noneCap w560
      (memRegion (fsp - 19552#64) 3168 ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗
       memRegion (fsp + 976#64) 3168 ∗ statesRecvSavedCells s0 ∗
       outPartA ∗ outPartB488 ∗ ((out + 488#64) ↦₁₂₈ q960) ∗ ((out + 504#64) ↦₆₄ w256) ∗ Rest)
      hfsp_align hpc3 hrun3 hfrozen3 hsym3 hsp3 hx0_3 hx1_3 hx2_3 hx19_3
    refine seq_clean (SepWP.weaken_pre ?_ hstepC) ?_
    · rw [epilogueRecvOutPartB_eq_488, epilogueRecvStackPartA_eq_488, stackAt_statesRecvCallee_eq_extHook_simple fsp]
      exact Entails.of_eq (by dsimp only [outPartB488]; ac_rfl)
    · intro s4 hpc4 hrun4 ⟨hsp4, htr4⟩
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans (htr3.trans (htr2.trans htr1))
      have hepil := states_recv_epilogue_19324 (b := img.base) (ext := ext) s0 s4
        (outPartA ∗ outPartB488 ∗ memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗ Rest)
        hsp0_align hpc4 hrun4 hsp4 htr40
      refine SepWP.mono (SepWP.weaken_pre ?_ hepil) ?_
      · have hstk288 := epilogueStack_224_512_entails_memRegion fsp
          w224 noneCap w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504
          w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
        have hstk3632 := epilogue_entails_memRegion_3632 fsp q512 q528 q544 q960 w560 bs576 hbs576
        have hout440 := epilogue_out_488_960_entails_memRegion_and_optNone A out q960 q528 q544 q512 w256 w560 (s3.readReg64 .x20) bs576 hbs576
        rw [← stack_recombine_4144 fsp, stackAt_statesRecvCallee_eq_extHook_simple fsp]
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

/-! ## `States.keysUnsampled` (`tag = 2#64`, `+96` / `0x554b4`) under `AllocContractsX` -/

theorem protoAuthenticatorAt_entails_dealloc_lt_simple (A : RustAlloc) (a : BitVec 64)
    (auth : ProtoAuthenticator) :
    protoAuthenticatorAt A a auth ⊢
      ∃∗ g : TwoVecGhost,
        ⌜g.v1.cap.toNat < 2 ^ 63 ∧ g.v2.cap.toNat < 2 ^ 63⌝ ∗
        twoVecHeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
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
      (twoVecHeadersAt a ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ∗
       vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2)) by
    unfold twoVecHeadersAt; dsimp only; ac_rfl)) ?_
  apply Entails.pure_left; intro hlt1
  apply Entails.pure_left; intro hlt2
  exact Entails.pure_right ⟨hlt1, hlt2⟩ (Entails.refl _)

private theorem chunkedStatesAt_keysUnsampled_entails_dealloc_lt (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) ⊢
      ∃∗ g : TwoVecGhost,
        ⌜g.v1.cap.toNat < 2 ^ 63 ∧ g.v2.cap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
        ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
        ((a + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (a + 64#64) 864 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  have hauth : authenticatorAt A (a + 8#64) st.uc.auth =
      protoAuthenticatorAt A (a + 8#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩ := rfl
  rw [chunkedStatesAt_keysUnsampled_unfold, hauth]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (protoAuthenticatorAt_entails_dealloc_lt_simple A (a + 8#64)
      ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
  rw [sepConj_assoc (⌜g.v1.cap.toNat < 2 ^ 63 ∧ g.v2.cap.toNat < 2 ^ 63⌝),
    sepConj_left_comm (a ↦₆₄ 2#64)]
  apply Entails.pure_left; intro hlt; refine Entails.sepExists_right g (Entails.pure_right hlt ?_)
  simp only [twoVecHeadersAt, BitVec.add_assoc,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (8#64 + 16#64 : BitVec 64) = 24#64 from rfl,
    show (8#64 + 24#64 : BitVec 64) = 32#64 from rfl, show (8#64 + 32#64 : BitVec 64) = 40#64 from rfl,
    show (8#64 + 40#64 : BitVec 64) = 48#64 from rfl]; exact Entails.of_eq (by ac_rfl)

theorem states_recv_tail_dealloc_192_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    (s0 s1 : State) (ptr cap : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 192#64)
    (hrun1 : s1.status = .Running)
    (hfrozen1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = ptr)
    (hx1_1 : s1.readReg64 .x1 = cap)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (hcap : cap.toNat ≠ 0) (hcap_lt : cap.toNat < 2 ^ 63)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live ptr cap.toNat 1 ∗
        memRegion ptr cap.toNat ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hlay : LayoutOk cap.toNat 1 := layoutOk_one_of_ne_zero_simple hcap hcap_lt
  have hdealloc := hA.dealloc_ok_at statesRecvName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
  simp only [rustDeallocExternSpecWithStack, extHookStack, Spec.inImage] at hdealloc
  states_recv_fetches_range img.base (Rust.withPanics ext) 192 36
  dsimp only [contractProg, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_frame) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_extHook_simple s0.sp)) (by sep_frame) ?_
  wp_call hdealloc (ptr, cap.toNat, 1)
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_extHook_simple s0.sp).symm) (by sep_frame) ?_
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

private theorem keysUnsampled_err_step_96_176_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (s : State) (fsp outA selfA msgA st_epoch msg_epoch v_out0 v_out16 v_fsp456 v_fsp504 : BitVec 64)
    (b_out8 : BitVec 8) (g : TwoVecGhost) (Frame : SepProp)
    (hc1_lt : g.v1.cap.toNat < 2 ^ 63)
    (hgt : msg_epoch > st_epoch) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 96#64) (hrun : s.status = .Running)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 176#64) s
      (((outA ↦₆₄ v_out0) ∗ ((outA + 8#64) ↦₈ b_out8) ∗ ((outA + 16#64) ↦₆₄ v_out16)) ∗
       (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
        ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
       vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗
       stackAt fsp extHookStack ∗ ((fsp + 456#64) ↦₆₄ v_fsp456) ∗ ((fsp + 504#64) ↦₆₄ v_fsp504) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_epoch)) ∗
          (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
           ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
          (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗ stackAt fsp extHookStack ∗
          ((fsp + 456#64) ↦₆₄ g.v2.cap) ∗ ((fsp + 504#64) ↦₆₄ st_epoch) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = g.v2.ptr ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) := by
    have h := hA.dealloc_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
    simpa only [contractProg] using h
  simp only [rustDeallocExternSpecWithStack, extHookStack, Spec.inImage] at hdealloc_raw ⊢
  have hule : BitVec.ule msg_epoch st_epoch = false := ule_false_of_gt hgt
  states_recv_fetches_range img.base (Rust.withPanics ext) 96 80
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp hx19 hx1 hx24; dsimp only [vecCapPtrDealloc, noneCap]
  by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · have hlay : LayoutOk g.v1.cap.toNat 1 :=
      layoutOk_one_of_ne_zero_simple (ne_zero_of_beq_false (Bool.eq_false_iff.mpr hc1)) hc1_lt
    apply SepWP.seq_inImage (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc")) ⟨hfrozen, hsym⟩
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro ⟨hfrozen1, hsym1⟩
    wp_apply; wp_steps; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

set_option maxHeartbeats 1200000 in
theorem states_recv_keysUnsampled_err_96_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s : State) (fsp outA selfA msgA v48 : BitVec 64)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 96#64)
    (hrun : s.status = .Running) (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp : s.sp = fsp) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt img.base ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.keysUnsampled st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
    simp only [States.recv, Chunked.SendEk.KeysUnsampled.epoch, Unchunked.SendEk.KeysUnsampled.epoch, hgt, ↓reduceIte]
  rw [hrecv, memRegion_out_960_split_err outA, memRegion_4088_split_456_504 fsp, stackAt_statesRecvCallee_eq_extHook_simple fsp]
  refine SepWP.fold (chunkedStatesAt_keysUnsampled_entails_dealloc_lt A selfA st) (by sep_frame) ?_
  unfold messageAt; wp_pull_exists; rename_i v_fsp504 v_fsp456 v_out16 b_out8 v_out0 g
  wp_focus_pure; intro ⟨hc1_lt, hc2_lt⟩
  have hstep1 := keysUnsampled_err_step_96_176_ext hA s fsp outA selfA msgA st.uc.epoch msg.epoch
    v_out0 v_out16 v_fsp456 v_fsp504 b_out8 g
    (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
     (selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 24#64) 8 ∗ memRegion (selfA + 48#64) 8 ∗
     memRegion (selfA + 64#64) 864 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt img.base ∗
     memRegion (fsp - 19552#64) 3168 ∗ memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
     memRegion (fsp + 56#64) 400 ∗ memRegion (fsp + 464#64) 40 ∗ memRegion (fsp + 512#64) 3632 ∗
     statesRecvSavedCells s0) hc1_lt hgt hfsp_align hpc hrun hfrozen hsym hsp hx19 hx1 hx24
  refine seq_clean_inImage_s1 hfrozen hsym (mid := (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 176#64)
    (P_mid :=
      ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg.epoch)) ∗
      (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
       ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch)) ∗
      (msgA ↦₆₄ msg.epoch) ∗ A.pool ∗ stackAt fsp extHookStack ∗
      ((fsp + 456#64) ↦₆₄ g.v2.cap) ∗ ((fsp + 504#64) ↦₆₄ st.uc.epoch) ∗
      (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
       (selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 24#64) 8 ∗ memRegion (selfA + 48#64) 8 ∗
       memRegion (selfA + 64#64) 864 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt img.base ∗
       memRegion (fsp - 19552#64) 3168 ∗ memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
       memRegion (fsp + 56#64) 400 ∗ memRegion (fsp + 464#64) 40 ∗ memRegion (fsp + 512#64) 3632 ∗
       statesRecvSavedCells s0))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = g.v2.ptr ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ TraceCalleeSaved sm s0)
    (by unfold TraceCalleeSaved at hstep1 ⊢; rw [hx29, htr.1, htr.2] at hstep1; exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨hsp1, hx0_1, hx29_1, htr1⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_extHook_simple fsp).symm) (by sep_frame) ?_
  refine SepWP.fold (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg.epoch) (by sep_frame) ?_
  refine SepWP.fold (keysUnsampled_selfA_err_combine selfA g.v1.cap g.v1.ptr g.v2.cap g.v2.ptr st.uc.epoch) (by sep_frame) ?_
  have hepil_fn := @states_recv_epilogue_19324 img.base ext s0
  have htail_fn := @states_recv_tail_dealloc_192_ext img A ext hA s0
  states_recv_fetches_range img.base (Rust.withPanics ext) 176 16
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hepil_fn htail_fn ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp1; dsimp only [vecCapPtrDealloc]
  by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine SepWP.fold (cells_456_504_entails_memRegion_4088 s1.sp g.v2.cap st.uc.epoch) (by sep_frame) ?_
    refine SepWP.fold (cell48_4088_entails_memRegion_4144 s1.sp v48) (by sep_frame) ?_
    refine SepWP.mono (SepWP.weaken_pre ?_ (hepil_fn _
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
      hsp0_align rfl (by simpa only [arm64_norm] using hrun1)
      (by simpa only [State.sp, arm64_norm] using hfsp_eq) ⟨by simpa only [arm64_norm] using htr1.1, by simpa only [arm64_norm] using htr1.2⟩))
      fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ⟨Entails.trans hPf (Entails.of_eq (by unfold messageAt; ac_rfl)), hspf, hcs, htrf⟩
    rw [← hfsp_eq]; exact Entails.of_eq (by unfold messageAt; ac_rfl)
  · wp_steps
    refine SepWP.fold (cells_456_504_entails_memRegion_4088 s1.sp g.v2.cap st.uc.epoch) (by sep_frame) ?_
    refine SepWP.fold (cell48_4088_entails_memRegion_4144 s1.sp v48) (by sep_frame) ?_
    refine SepWP.mono (SepWP.weaken_pre ?_ (htail_fn _ g.v2.ptr g.v2.cap
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base)
      hsp0_align rfl (by simpa only [arm64_norm] using hrun1)
      (by simpa only [wp_norm, arm64_norm] using hfrozen1)
      (by simpa only [wp_norm, arm64_norm] using hsym1)
      (by simpa only [State.sp, arm64_norm] using hfsp_eq) (by simpa only [arm64_norm] using hx0_1) rfl rfl
      (ne_zero_of_beq_false (Bool.eq_false_iff.mpr hc2)) hc2_lt ⟨by simpa only [arm64_norm] using htr1.1, by simpa only [arm64_norm] using htr1.2⟩))
      fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ⟨Entails.trans hPf (Entails.of_eq (by unfold messageAt; ac_rfl)), hspf, hcs, htrf⟩
    rw [← hfsp_eq]; exact Entails.of_eq (by unfold messageAt; ac_rfl)

set_option maxHeartbeats 1600000 in
theorem states_recv_keysUnsampled_ok_96_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) (s0 s : State) (fsp outA selfA msgA v48 : BitVec 64)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 96#64)
    (hrun : s.status = .Running) (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt img.base ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.keysUnsampled st).recv K msg = .ok ⟨none, .keysUnsampled st⟩ := by
    simp only [States.recv, Chunked.SendEk.KeysUnsampled.epoch, Unchunked.SendEk.KeysUnsampled.epoch, hle, ↓reduceIte]
  rw [hrecv]
  have hstk288 : memRegion (fsp + 224#64) 288 = existsWordsAtOff fsp 36 224 :=
    memRegion_off_eq_existsWordsAtOff fsp 36 224 (by decide)
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0 ⊢
      ((∃∗ g : AuthWords,
          (selfA ↦₆₄ 2#64) ∗ ((selfA + 8#64) ↦₆₄ g.v1.w0) ∗ ((selfA + 16#64) ↦₆₄ g.v1.w1) ∗ ((selfA + 24#64) ↦₆₄ g.v1.w2) ∗
          ((selfA + 32#64) ↦₆₄ g.v2.w0) ∗ ((selfA + 40#64) ↦₆₄ g.v2.w1) ∗ ((selfA + 48#64) ↦₆₄ g.v2.w2) ∗
          ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (selfA + 64#64) 864 ∗
          relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
       existsWordsAtOff fsp 36 224) ∗
      (memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 3632 ∗
       statesRecvSavedCells s0) := by
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedStatesAt A selfA (.keysUnsampled st) ∗
      (memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088) ∗
      (memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       statesRecvRoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (chunkedStatesAt_keysUnsampled_extract A selfA st)
      (sepConj_mono_left (cell48_4088_entails_memRegion_4144 fsp v48))) ?_
    rw [← stack_recombine_4144 fsp, hstk288]; exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  apply sepWP_intro_ex; intro g
  apply sepWP_intro_ex; intro w224; apply sepWP_intro_ex; intro w232; apply sepWP_intro_ex; intro w240; apply sepWP_intro_ex; intro w248; apply sepWP_intro_ex; intro w256; apply sepWP_intro_ex; intro w264
  apply sepWP_intro_ex; intro w272; apply sepWP_intro_ex; intro w280; apply sepWP_intro_ex; intro w288; apply sepWP_intro_ex; intro w296; apply sepWP_intro_ex; intro w304; apply sepWP_intro_ex; intro w312
  apply sepWP_intro_ex; intro w320; apply sepWP_intro_ex; intro w328; apply sepWP_intro_ex; intro w336; apply sepWP_intro_ex; intro w344; apply sepWP_intro_ex; intro w352; apply sepWP_intro_ex; intro w360
  apply sepWP_intro_ex; intro w368; apply sepWP_intro_ex; intro w376; apply sepWP_intro_ex; intro w384; apply sepWP_intro_ex; intro w392; apply sepWP_intro_ex; intro w400; apply sepWP_intro_ex; intro w408
  apply sepWP_intro_ex; intro w416; apply sepWP_intro_ex; intro w424; apply sepWP_intro_ex; intro w432; apply sepWP_intro_ex; intro w440; apply sepWP_intro_ex; intro w448; apply sepWP_intro_ex; intro w456
  apply sepWP_intro_ex; intro w464; apply sepWP_intro_ex; intro w472; apply sepWP_intro_ex; intro w480; apply sepWP_intro_ex; intro w488; apply sepWP_intro_ex; intro w496; apply sepWP_intro_ex; intro w504
  rw [emp_sepConj]; unfold messageAt
  have hstep1 := keysUnsampled_ok_step_96_18996 (b := img.base) (ext := ext) s fsp outA selfA msgA
    g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch msg.epoch w224 w232 w368 w376 w456 w496 w504
    ((selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 64#64) 864 ∗
     relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗
     ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
     ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗
     ((fsp + 408#64) ↦₆₄ w408) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
     epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
     memRegion outA v1RecvSize ∗ statesRecvRoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
     memRegion fsp 224 ∗ memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0)
    hle hfsp_align hpc hrun hsp hx19 hx1 hx24
  refine seq_clean_inImage_s1 hfrozen hsym (SepWP.weaken_pre (Entails.of_eq (by dsimp only [epilogueRecvStackPartB]; ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨hsp1, hx1_1, hx8_1, hx19_1, hx29_1, htr1⟩
  have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
  have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
  have hexit := epilogue_18996_exit_none_488_ext hA s0 s1 outA
    2#64 w240 w288 w296 w336 w352 g.v2.w2 g.v2.w1 w384 w408 w432 g.v2.w0 g.v1.w2 st.uc.epoch
    w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
    (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
     memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool)
    hsp0_align hpc1 hrun1 hfrozen1 hsym1 hsp10 hx19_1 htr10
  dsimp only at hexit; rw [← hfsp_eq] at hexit
  refine SepWP.mono (SepWP.weaken_pre ?_ hexit) ?_
  · have hself := selfA_8words_entails_memRegion_928 selfA 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
    unfold messageAt epilogueRecvStackPartA488
    refine Entails.trans (Entails.of_eq (show _ =
      ((selfA ↦₆₄ 2#64) ∗ ((selfA + 8#64) ↦₆₄ g.v1.w0) ∗ ((selfA + 16#64) ↦₆₄ g.v1.w1) ∗
       ((selfA + 24#64) ↦₆₄ g.v1.w2) ∗ ((selfA + 32#64) ↦₆₄ g.v2.w0) ∗ ((selfA + 40#64) ↦₆₄ g.v2.w1) ∗
       ((selfA + 48#64) ↦₆₄ g.v2.w2) ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (selfA + 64#64) 864) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       (((fsp + 224#64) ↦₆₄ 2#64) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
        ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 368#64) ↦₆₄ g.v2.w2) ∗
        ((fsp + 376#64) ↦₆₄ g.v2.w1) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗ ((fsp + 408#64) ↦₆₄ w408) ∗
        ((fsp + 432#64) ↦₆₄ w432) ∗ ((fsp + 456#64) ↦₆₄ g.v2.w0) ∗ ((fsp + 496#64) ↦₆₄ g.v1.w2) ∗
        ((fsp + 504#64) ↦₆₄ st.uc.epoch)) ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        statesRecvRoAt img.base ∗ A.pool)) by ac_rfl)) (Entails.trans (sepConj_mono_left hself) (Entails.of_eq (by ac_rfl)))
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    rw [hx1_1, hx8_1] at hPf
    have hrec := keysUnsampled_out_recompose A outA st g w288 w432 w408 w352 w384 w336 w296
      (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
      (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
      (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
      (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14)
      w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440
      w264 w344 w392 w272 w360 w400 w464 w304 w328 w280 w320 (s1.readReg64 .x3)
      w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
      w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20)
    refine ⟨Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
      (epilogueRecvOutPartA outA 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
         w288 w432 w408 w352 w384 w336 w296
         (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
         (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
         (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
         (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14) ∗
       epilogueRecvOutPartB488 outA w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440
         w264 w344 w392 w272 w360 w400 w464 w304 w328 w280 w320 (s1.readReg64 .x3)
         w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
         w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20) ∗
       memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
       relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
      (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
       statesRecvRoAt img.base ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) by ac_rfl))
      (sepConj_mono_left hrec)), hsp_f, hcs_f, htr_f⟩

/-- Per-variant `.inImage img` specification proof at `statesRecvStackX` (`23792` B) for
    `States.keysUnsampled st` (`tag = 2#64`) under `AllocContractsX`. -/
theorem states_recv_keysUnsampled_ok_x
    (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpec A F K img.base (.keysUnsampled st) msg).inImage img) := by
  refine subroutine_ok_statesRecvVariantSpec_inImage_of_sepWP (.keysUnsampled st) msg ?_
  intro outA selfA msgA s0 hpc0 hrun0 hfrozen0 hsym0 hsp0_align hb hx0 hx1 hx2 _
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue (b := img.base) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool) hsp0_align hpc0 hrun0
  refine seq_clean_inImage_s1 hfrozen0 hsym0 hpro ?_
  intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; rw [chunkedStatesAt_keysUnsampled_unfold]
  have hdisp := states_recv_dispatch (b := img.base) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 2#64
    (authenticatorAt A (selfA + 8#64) st.uc.auth ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗
     memRegion (selfA + 64#64) 864 ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inl rfl))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine seq_clean_inImage_s1 hfrozen1 hsym1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hfrozen2 hsym2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2; rw [hx29_1] at hx29_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  have hpre2 :
      (selfA ↦₆₄ 2#64) ∗ statesRecvRoAt img.base ∗
      (authenticatorAt A (selfA + 8#64) st.uc.auth ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (selfA + 64#64) 864 ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ v48 : BitVec 64, (((s0.sp - 4240#64) + 48#64) ↦₆₄ v48)) ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt img.base ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 48 ∗
       memRegion ((s0.sp - 4240#64) + 56#64) 4088 ∗ statesRecvSavedCells s0) := by
    rw [chunkedStatesAt_keysUnsampled_unfold, memRegion_4144_split_cell48 (s0.sp - 4240#64)]; exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre2 ?_; rw [sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro v48
  by_cases hgt : msg.epoch > st.uc.epoch
  · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (states_recv_keysUnsampled_err_96_ext hA s0 s2 (s0.sp - 4240#64) outA selfA msgA v48 st msg
        hgt rfl hsp0_align hfsp_align hpc2 hrun2 hfrozen2 hsym2 hsp2 hx29_2 hx19_2 hx1_2 hx24_2 htr20)
  · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (states_recv_keysUnsampled_ok_96_ext hA s0 s2 (s0.sp - 4240#64) outA selfA msgA v48 st msg
        hgt rfl hsp0_align hfsp_align hpc2 hrun2 hfrozen2 hsym2 hsp2 hx19_2 hx1_2 hx24_2 htr20)

/-- Per-variant `.inImage img` specification proof at `statesRecvStackXExt` (`40176` B) for
    `States.keysUnsampled st` (`tag = 2#64`) under `AllocContractsX`. -/
theorem states_recv_keysUnsampled_ok_x_ext
    (img : Obj.Image) (A : RustAlloc) (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName)
      ((statesRecvVariantSpecExt A F K img.base (.keysUnsampled st) msg).inImage img) :=
  statesRecvVariant_inImage_grow_stack (states_recv_keysUnsampled_ok_x img A F K ext hA st msg)

end CryptoVerification.SpqrV1.States.Recv
