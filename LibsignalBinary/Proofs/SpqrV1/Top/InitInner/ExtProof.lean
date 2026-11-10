/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ExtHelpers
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbOuter
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Extended-Stack (`*Ext`) Verification of `spqr::init_inner`

Proves `InitInnerBaseOkExt` and `InitInnerOkXExt` (`initInnerStackExt = 18912`B) from
`AllocContracts` or 4K extern hooks together with `AuthNewOkExt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit' sessionMemcpySpec libcMemcpySpec

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::init_inner")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::into_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## 1. Contract-Backed `spqr::init_inner` (`initInnerStackExt = 18912`B) -/

private theorem call_authNew_base_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      (authNewSpecExt F A))
    (authKey : Bytes) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = s0.sp - 104#64) (hx1 : s.readReg64 .x1 = s0.sp - 1032#64)
    (hsplit : P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A (s0.sp - 1032#64) authKey ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗ Frame)
    (hnext : ∀ (sf : State) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗ Frame)
        Q (InitInnerPanicExt s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q (InitInnerPanicExt s0 R) := by
  refine SepWPp.call hauth_raw (x := ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [authNewSpecExt]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx0, hx1, hlt⟩, hm⟩
  · change (sf.mem ⊨ ((authNewSpecExt F A).onPanic ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem; dsimp only [authNewSpecExt] at hmem; rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [authNewSpecExt]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    refine SepWPp.weaken_pre (authenticatorAt_expose_frame_ext A F s0.sp authKey Frame) ?_
    refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
      SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
      SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
    exact hnext sf a0 a1 a2 a3 a4 a5 hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])

private theorem call_authNew_x_ext {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      ((authNewSpecExt F A).inImage img))
    (authKey : Bytes) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp) (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = s0.sp - 104#64) (hx1 : s.readReg64 .x1 = s0.sp - 1032#64)
    (hsplit : P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A (s0.sp - 1032#64) authKey ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗ Frame)
    (hnext : ∀ (sf : State) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗ Frame)
        Q (InitInnerPanicExt s0 R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P Q (InitInnerPanicExt s0 R) := by
  refine SepWPp.call hauth_raw (x := ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [Spec.inImage, authNewSpecExt]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨hinv, ⟨hx0, hx1, hlt⟩, hm⟩
  · change (sf.mem ⊨ (((authNewSpecExt F A).inImage img).onPanic ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem; dsimp only [Spec.inImage, authNewSpecExt] at hmem; rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [Spec.inImage, authNewSpecExt]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    refine SepWPp.weaken_pre (authenticatorAt_expose_frame_ext A F s0.sp authKey Frame) ?_
    refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
      SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
      SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
    exact hnext sf a0 a1 a2 a3 a4 a5 hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])

private theorem call_statesIntoPb_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} {st : States spqrPolyApi (spqrAuthApi F)}
    (hinto_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb"))
      (statesIntoPbVariantSpec A F b st))
    (out : BitVec 64) {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop} (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb"))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hsplit : P = (memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A (s0.sp - 1032#64) st ∗ statesIntoPbJumpTableAt b ∗ A.pool ∗
      stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A out st.into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTableAt b ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
        Q (InitInnerPanicExt s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q (InitInnerPanicExt s0 R) := by
  refine SepWPp.call hinto_raw (x := ⟨out, s0.sp - 1032#64⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [statesIntoPbVariantSpec]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx8, hx0, hb⟩, hm⟩
  · change (sf.mem ⊨ ((statesIntoPbVariantSpec A F b st).onPanic ⟨out, s0.sp - 1032#64⟩ s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem; dsimp only [statesIntoPbVariantSpec, statesIntoPbOnPanic] at hmem; rw [← sepConj_assoc]
    have hpan := allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [statesIntoPbVariantSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

private theorem init_inner_panic_436_ext {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 436#64)
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q (InitInnerPanicExt s0 R) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext) (name := initInnerName)
    (k := num% (ls_rel% "spqr::init_inner" "alloc::raw_vec::handle_error"))
  init_inner_fetches_range b (Rust.withPanics ext) 436 12
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "spqr::init_inner" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [InitInnerPanicExt, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

private theorem cells_1032_3_expose_ext (sp : BitVec 64) (Rest : SepProp) :
    cells (sp - 1032#64) 3 ∗ Rest ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp - 1032#64) ↦₆₄ w0) ∗ ((sp - 1024#64) ↦₆₄ w1) ∗ ((sp - 1016#64) ↦₆₄ w2) ∗ Rest := by
  cells_unfold; simp only [sepExists_sepConj_left, arm64_norm]
  apply Entails.sepExists_elim; intro w0; apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 ?_))
  exact Entails.of_eq (by ac_rfl)

private theorem init_inner_clone_a2b_of_sub
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (halloc_base : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hshim_base : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hmemcpy4k_base : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hlt : authKey.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32) (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64 →
      sm.status = .Running → (∀ img, ImgCallInv img s → ImgCallInv img sm) →
      sm.sp = s0.sp - 1040#64 → sm.readReg64 .x29 = s0.sp - 48#64 →
      sm.readReg64 .x19 = out → sm.readReg64 .x0 = s0.sp - 104#64 →
      sm.readReg64 .x1 = s0.sp - 1032#64 →
      (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
       sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
       sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      sm.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
        (vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerPanicExt s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerPanicExt s0 R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases hlen_zero : authKey.length = 0
  · have hnil : authKey = [] := List.eq_nil_of_length_eq_zero hlen_zero
    subst hnil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx20 hnext ⊢
    refine initInner_seq_sepWP_ext
      (init_inner_a2b_empty_to_364 (A := A) s0 s out
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htrace) ?_
    intro sm hpcm hrunm hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
    exact hnext sm hpcm hrunm hinvm hspm hx29m hx19m hx0m hx1m hcsm htrm
  · refine SepWPp.weaken_pre (cells_1032_3_expose_ext s0.sp _) ?_
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 => ?_
    have hpos : 0 < authKey.length := Nat.pos_of_ne_zero hlen_zero
    have hbeq0 : (BitVec.ofNat 64 authKey.length == 0#64) = false := ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 authKey.length != 0#64) = true := ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 authKey.length).toNat = authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk authKey.length 1 := ⟨hpos, hpow2, by omega⟩
    have hshim := sub_ok_at_of_fnAddr hshim_base initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := sub_ok_at_of_fnAddr halloc_base initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_alloc"))
    have hmemcpy := sub_ok_at_of_fnAddr hmemcpy4k_base initInnerName
      (num% (ls_rel% "spqr::init_inner" "memcpy"))
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 436#64 →
        sm.status = .Running → sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm P_mid Q (InitInnerPanicExt s0 R) :=
      fun sm P_mid hpcm hrunm htrm => init_inner_panic_436_ext s0 sm P_mid R hpcm hrunm htrm
    simp only [sessionShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [sessionMemcpySpec, libcMemcpySpec] at hmemcpy
    rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
    init_inner_fetches_range b (Rust.withPanics ext) 36 4
    init_inner_fetches_range b (Rust.withPanics ext) 120 52
    init_inner_fetches_range b (Rust.withPanics ext) 356 8
    dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
      State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 hshim halloc hmemcpy hpanic ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
    examples_hide_fetches
    refine sepWPp_of_sepWP_keepInv_ext (mid := entry + 144#64) ?_
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_sf1
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.SepWPp.seq_clean (mid := entry + 436#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ ((s0.sp - 1032#64) ↦₆₄ w0) ∗
          ((s0.sp - 1024#64) ↦₆₄ w1) ∗ ((s0.sp - 1016#64) ↦₆₄ w2) ∗ (akPtr ↦ₛ authKey) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro sm hpcm hrunm htrm; exact hpanic sm _ hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len]; simp only [sepConj_assoc]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine initInner_seq_sepWP_ext (mid := entry + 364#64)
        (P' := vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        (Post := fun sm => sm.sp = s0.sp - 1040#64 ∧ sm.readReg64 .x29 = s0.sp - 48#64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x0 = s0.sp - 104#64 ∧
          sm.readReg64 .x1 = s0.sp - 1032#64 ∧
          (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
           sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
           sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) ∧
          sm.trace = s0.trace) ?_ ?_
      · wp_steps; wp_apply; wp_steps
        have hvec := vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr_c authKey hpos hlt hoom
        simp only [arm64_norm] at hvec
        have hent :
            (ptr_c ↦ₛ authKey) ∗ (akPtr ↦ₛ authKey) ∗ stackAt sf_1.sp allocHookStack ∗ A.pool ∗
            A.live ptr_c authKey.length 1 ∗ ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
            ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗ ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ Frame ⊢
            vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
            A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
          rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗
             ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ A.live ptr_c authKey.length 1 ∗
             (ptr_c ↦ₛ authKey)) ∗
            ((akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) by ac_rfl)) ?_
          exact sepConj_mono_left hvec
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hent) (by wp_done)
      · intro sm hpcm hrunm hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
        exact hnext sm hpcm hrunm (fun img hinv => hinvm img (hinv_sf1 img hinv))
          hspm hx29m hx19m hx0m hx1m hcsm htrm

private theorem init_inner_clone_b2a_of_sub
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (halloc_base : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hshim_base : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hmemcpy4k_base : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hlt : authKey.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32) (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 192#64 →
      sm.status = .Running → (∀ img, ImgCallInv img s → ImgCallInv img sm) →
      sm.sp = s0.sp - 1040#64 → sm.readReg64 .x29 = s0.sp - 48#64 →
      sm.readReg64 .x19 = out → sm.readReg64 .x0 = s0.sp - 104#64 →
      sm.readReg64 .x1 = s0.sp - 1032#64 →
      (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
       sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
       sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) →
      sm.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm
        (vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerPanicExt s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerPanicExt s0 R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases hlen_zero : authKey.length = 0
  · have hnil : authKey = [] := List.eq_nil_of_length_eq_zero hlen_zero
    subst hnil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx20 hnext ⊢
    refine initInner_seq_sepWP_ext
      (init_inner_b2a_empty_to_192 (A := A) s0 s out
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htrace) ?_
    intro sm hpcm hrunm hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
    exact hnext sm hpcm hrunm hinvm hspm hx29m hx19m hx0m hx1m hcsm htrm
  · refine SepWPp.weaken_pre (cells_1032_3_expose_ext s0.sp _) ?_
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => SepWPp.exists_elim fun w2 => ?_
    have hpos : 0 < authKey.length := Nat.pos_of_ne_zero hlen_zero
    have hbeq0 : (BitVec.ofNat 64 authKey.length == 0#64) = false := ofNat_beq_zero_false' hpos (by omega)
    have hne0 : (BitVec.ofNat 64 authKey.length != 0#64) = true := ofNat_ne_zero_true hpos (by omega)
    have htoNat_len : (BitVec.ofNat 64 authKey.length).toNat = authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk authKey.length 1 := ⟨hpos, hpow2, by omega⟩
    have hshim := sub_ok_at_of_fnAddr hshim_base initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    have halloc := sub_ok_at_of_fnAddr halloc_base initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_alloc"))
    have hmemcpy := sub_ok_at_of_fnAddr hmemcpy4k_base initInnerName
      (num% (ls_rel% "spqr::init_inner" "memcpy"))
    have hpanic : ∀ (sm : State) (P_mid : SepProp),
        sm.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 436#64 →
        sm.status = .Running → sm.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sm P_mid Q (InitInnerPanicExt s0 R) :=
      fun sm P_mid hpcm hrunm htrm => init_inner_panic_436_ext s0 sm P_mid R hpcm hrunm htrm
    simp only [sessionShimSpec] at hshim
    simp only [rustAllocSpec] at halloc
    simp only [sessionMemcpySpec, libcMemcpySpec] at hmemcpy
    rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
    init_inner_fetches_range b (Rust.withPanics ext) 36 56
    init_inner_fetches_range b (Rust.withPanics ext) 176 16
    dsimp only [tripleRatchetProgAtExt, initInnerName, Direction.toI32,
      State.readReg32, Reg.x2, BitVec.ofNat_eq_ofNat] at hpc hw2 hshim halloc hmemcpy hpanic ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
    examples_hide_fetches
    refine sepWPp_of_sepWP_keepInv_ext (mid := entry + 64#64) ?_
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_sf1
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom, ↓reduceIte]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun htr_oom => ?_
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.SepWPp.seq_clean (mid := entry + 436#64)
        (P_mid := A.pool ∗ stackAt sf.sp allocHookStack ∗ ((s0.sp - 1032#64) ↦₆₄ w0) ∗
          ((s0.sp - 1024#64) ↦₆₄ w1) ∗ ((s0.sp - 1016#64) ↦₆₄ w2) ∗ (akPtr ↦ₛ authKey) ∗ Frame)
        (Q_mid := fun sm => sm.trace = s0.trace ++ [allocFailedEvent]) ?_ ?_
      · wp_steps; wp_done
      · intro sm hpcm hrunm htrm; exact hpanic sm _ hpcm hrunm htrm
    · have hoom_beq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      have hoom_bne : (sf_1.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hoom
      conv => arg 4; simp only [hoom, ↓reduceIte, htoNat_len]; simp only [sepConj_assoc]
      refine CryptoVerification.SpqrV1.Poly.DecoderPb.sepWPp_pure_mid fun ⟨_, htr_ok⟩ => ?_
      let ptr_c := sf_1.readReg64 (Reg.gpr 0#5)
      refine initInner_seq_sepWP_ext (mid := entry + 192#64)
        (P' := vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        (Post := fun sm => sm.sp = s0.sp - 1040#64 ∧ sm.readReg64 .x29 = s0.sp - 48#64 ∧
          sm.readReg64 .x19 = out ∧ sm.readReg64 .x0 = s0.sp - 104#64 ∧
          sm.readReg64 .x1 = s0.sp - 1032#64 ∧
          (sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x23 = s0.readReg64 .x23 ∧
           sm.readReg64 .x24 = s0.readReg64 .x24 ∧ sm.readReg64 .x25 = s0.readReg64 .x25 ∧
           sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) ∧
          sm.trace = s0.trace) ?_ ?_
      · wp_steps; wp_apply; wp_steps
        have hvec := vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr_c authKey hpos hlt hoom
        simp only [arm64_norm] at hvec
        have hent :
            (ptr_c ↦ₛ authKey) ∗ (akPtr ↦ₛ authKey) ∗ stackAt sf_1.sp allocHookStack ∗ A.pool ∗
            A.live ptr_c authKey.length 1 ∗ ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
            ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗ ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ Frame ⊢
            vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
            A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
          rw [‹sf_1.sp = sf.sp›, ‹sf.sp = s.sp›, hsp]
          refine Entails.trans (Entails.of_eq (show _ =
            (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr_c) ∗
             ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗ A.live ptr_c authKey.length 1 ∗
             (ptr_c ↦ₛ authKey)) ∗
            ((akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) by ac_rfl)) ?_
          exact sepConj_mono_left hvec
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hent) (by wp_done)
      · intro sm hpcm hrunm hinvm ⟨hspm, hx29m, hx19m, hx0m, hx1m, hcsm, htrm⟩
        exact hnext sm hpcm hrunm (fun img hinv => hinvm img (hinv_sf1 img hinv))
          hspm hx29m hx19m hx0m hx1m hcsm htrm

private theorem init_inner_bl_364_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 368#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_range b (Rust.withPanics ext) 364 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

private theorem init_inner_bl_192_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 192#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 196#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_range b (Rust.withPanics ext) 192 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

private theorem init_inner_bl_412_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb")) s P
      (fun s' P1 => (P1 ⊢ P) ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 416#64 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x0 = s.readReg64 .x0 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  init_inner_fetches_range b (Rust.withPanics ext) 412 4
  dsimp only [tripleRatchetProgAtExt, initInnerName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::init_inner" = entry
  examples_hide_fetches; wp_steps; wp_done

private theorem calleeSaved_chain_hi_ext {s0 s sf : State}
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcs : CalleeSavedPreserved s sf) :
    sf.readReg64 .x22 = s0.readReg64 .x22 ∧ sf.readReg64 .x23 = s0.readReg64 .x23 ∧
    sf.readReg64 .x24 = s0.readReg64 .x24 ∧ sf.readReg64 .x25 = s0.readReg64 .x25 ∧
    sf.readReg64 .x26 = s0.readReg64 .x26 ∧ sf.readReg64 .x27 = s0.readReg64 .x27 ∧
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  dsimp only [CalleeSavedPreserved] at hcs
  rcases hcs_hi with ⟨h22, h23, h24, h25, h26, h27, hvregs⟩
  exact ⟨by simp only [hcs, h22], by simp only [hcs, h23], by simp only [hcs, h24],
         by simp only [hcs, h25], by simp only [hcs, h26], by simp only [hcs, h27],
         by simp only [hcs, hvregs]⟩

private theorem calleeSaved_x29_ext {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x29 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x29 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

private theorem calleeSaved_x19_ext {s sf : State} {v : BitVec 64}
    (h : s.readReg64 .x19 = v) (hcs : CalleeSavedPreserved s sf) : sf.readReg64 .x19 = v := by
  dsimp only [CalleeSavedPreserved] at hcs; simp only [hcs, h]

private theorem init_inner_from_412_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    {d : Direction} {authKey : Bytes}
    (hinto : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (initV1State F d authKey)))
    (s0 s : State) (out akPtr : BitVec 64) (R : SepProp)
    (hb : b &&& 0xfff#64 = 0#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hcs_hi : s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (chunkedStatesAt A (s0.sp - 1032#64) (initV1State F d authKey) ∗
       memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackExt ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool)
      (InitInnerPostExt A F b s0 ⟨out, .v1, d, akPtr, authKey⟩) (InitInnerPanicExt s0 R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  have hinto_raw := sub_ok_of_addr_eq
    (fnAddr_rel64_ext (b := b) (H := Rust.withPanics ext)
      (rel := bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb"))
      initInner_fnOff (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb") (by decide)).symm hinto
  refine initInner_seq_sepWP_ext (init_inner_bl_412_ext s _ hpc hrun) ?_
  intro s1 hpc1 hrun1 _ ⟨hsp1, hlr1, hx8_1, hx0_1, hcs1, htr1⟩
  have hcs_hi1 := calleeSaved_chain_hi_ext hcs_hi hcs1
  have hsplit_pb :
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F d authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackExt ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTableAt b ∗ A.pool =
      (memRegion out optProtoInnerStateSize ∗
       chunkedStatesAt A (s0.sp - 1032#64) (initV1State F d authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 17872#64) 12000 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) := by
    rw [stackAt_authNewExt_split_statesIntoPb (s0.sp - 1040#64)]; ac_rfl
  refine call_statesIntoPb_ext hinto_raw
    out (s0 := s0) (s := s1) (ret_pc := (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 416#64)
    (R := R) hb hpc1 hrun1 (hsp1.trans hsp) hfsp_align hlr1 (htr1.trans htr)
    (hx8_1.trans hx8) (hx0_1.trans hx0) hsplit_pb ?_
  intro s2 hpc2 hrun2 hsp2 hcs2 htr2
  have hcs_hi2 := calleeSaved_chain_hi_ext hcs_hi1 hcs2
  have hrejoin_ep :
      (optProtoInnerStateAt A out (initV1State F d authKey).into_pb.innerState ∗
       memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTableAt b ∗ A.pool ∗
       stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 17872#64) 12000 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) ⊢
      stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992 ∗
      initInnerSavedCells s0 ∗ (memRegion (s0.sp - 18912#64) 1232 ∗
        initInnerResultAt A (F := F) out .v1 d authKey ∗
        (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗ A.pool) := by
    dsimp only [initInnerResultAt]
    have hstk : stackAt (s0.sp - 1040#64) statesIntoPbStack ∗
        memRegion (s0.sp - 1040#64 - 17872#64) 12000 =
        stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 18912#64) 1232 := by
      have hsub1232 : (s0.sp - 1040#64) - 17872#64 = s0.sp - 18912#64 := by bv_omega
      rw [← stackAt_authNewExt_split_statesIntoPb (s0.sp - 1040#64),
          stackAt_authNewExt_split_authNewX (s0.sp - 1040#64), hsub1232]
    have h1 :
        (optProtoInnerStateAt A out (initV1State F d authKey).into_pb.innerState ∗
         memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTableAt b ∗ A.pool ∗
         stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
        (memRegion (s0.sp - 1040#64 - 17872#64) 12000 ∗ memRegion (s0.sp - 1040#64) 8 ∗
         memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) =
        (stackAt (s0.sp - 1040#64) statesIntoPbStack ∗
         memRegion (s0.sp - 1040#64 - 17872#64) 12000) ∗
        (memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ memRegion (s0.sp - 104#64) 56 ∗
         memRegion (s0.sp - 1040#64) 8) ∗
        (optProtoInnerStateAt A out (initV1State F d authKey).into_pb.innerState ∗
         statesIntoPbJumpTableAt b ∗ A.pool ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) := by ac_rfl
    rw [h1, hstk, memRegion_992_rejoin_b2a_ext s0.sp]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hrejoin_ep ?_
  refine initInner_seq_sepWP_ext
    (init_inner_epilogue s0 s2
      (memRegion (s0.sp - 18912#64) 1232 ∗
       initInnerResultAt A (F := F) out .v1 d authKey ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗ A.pool)
      hsp0_align hpc2 hrun2 hsp2 hcs_hi2 htr2) ?_
  intro sf hpcf hrunf _ ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, hcsf, htrf⟩
  rw [stackAt_initInnerExt_split_base s0.sp]
  exact Entails.of_eq (by ac_rfl)

private def AuthCallAtExt (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (ext : String → Option (State → State))
    (s0 : State) (authKey : Bytes) (Q : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (s : State) (ret_pc : BitVec 64) (P Frame : SepProp),
    (∀ img, ImgCallInv img s0 → ImgCallInv img s) →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new") →
    s.status = .Running → s.sp = s0.sp - 1040#64 →
    s.readReg64 .x30 = ret_pc → s.trace = s0.trace →
    s.readReg64 .x0 = s0.sp - 104#64 → s.readReg64 .x1 = s0.sp - 1032#64 →
    P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A (s0.sp - 1032#64) authKey ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗ Frame →
    (∀ (sf : State) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗
           ((s0.sp - 88#64) ↦₆₄ a2) ∗ ((s0.sp - 80#64) ↦₆₄ a3) ∗
           ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗ Frame)
        Q (InitInnerPanicExt s0 R)) →
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q (InitInnerPanicExt s0 R)

private theorem init_inner_v1_a2b_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hmemcpy4k : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (s0 s1 : State) (out akPtr : BitVec 64) (authKey : Bytes) (R : SepProp)
    (hcall_auth : AuthCallAtExt A F b ext s0 authKey
      (InitInnerPostExt A F b s0 ⟨out, .v1, .a2b, akPtr, authKey⟩) R)
    (hb : b &&& 0xfff#64 = 0#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63) (hinv1 : ∀ img, ImgCallInv img s0 → ImgCallInv img s1)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.a2b.toI32) (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 : s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt ∗
        memRegion (s0.sp - 1040#64) 992))
      (InitInnerPostExt A F b s0 ⟨out, .v1, .a2b, akPtr, authKey⟩) (InitInnerPanicExt s0 R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt ∗
       memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 17872#64) 13776 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b) := by
    rw [memRegion_992_split_a2b_ext s0.sp, stackAt_authNewExt_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_a2b_of_sub halloc hshim hmemcpy4k s0 s1 out akPtr authKey _ R
    hsp0_align hlt hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP_ext (init_inner_bl_364_ext s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
  have hcs_hi3 := calleeSaved_chain_hi_ext hcs2 hcs3
  have hx29_3 := calleeSaved_x29_ext hx29_2 hcs3
  have hx19_3 := calleeSaved_x19_ext hx19_2 hcs3
  have hsplit_auth :
      vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 17872#64) 13776 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗ vecU8 A (s0.sp - 1032#64) authKey ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗
      (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b) := by
    rw [stackAt_authNewExt_split_allocHook (s0.sp - 1040#64)]; ac_rfl
  refine hcall_auth s3 ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 368#64) _ _
    (fun img h0 => hinv3 img (hinv2 img (hinv1 img h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3 (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hsplit_auth ?_
  intro s4 a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcs4 htr4
  have hcs_hi4 := calleeSaved_chain_hi_ext hcs_hi3 hcs4
  have hx29_4 := calleeSaved_x29_ext hx29_3 hcs4
  have hx19_4 := calleeSaved_x19_ext hx19_3 hcs4
  have hpre_post_auth :
      (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
         ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗
       (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
        memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
        (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 1032#64) 8 ∗ memRegion (s0.sp - 968#64) 864 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackExt ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool) := by
    rw [← memRegion_24_and_cells_5_eq_cells_8_ext s0.sp]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine initInner_seq_sepWP_ext
    (init_inner_a2b_post_auth s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 hpc5 hrun5 _ ⟨hsp5, hx8_5, hx0_5, hcs5, htr5⟩
  have h56 :
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 48 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackExt ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool) ⊢
      chunkedStatesAt A (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackExt ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTableAt b ∗ A.pool := by
    rw [← memRegion_48_and_8_eq_56_ext s0.sp]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre h56 ?_
  exact init_inner_from_412_ext (d := .a2b) (authKey := authKey)
    (states_into_pb_keysUnsampled _)
    s0 s5 out akPtr R hb hsp0_align
    hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

private theorem init_inner_v1_b2a_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hdealloc : DeallocOkExt b A ext)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hmemcpy4k : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (s0 s1 : State) (out akPtr : BitVec 64) (authKey : Bytes) (R : SepProp)
    (hcall_auth : AuthCallAtExt A F b ext s0 authKey
      (InitInnerPostExt A F b s0 ⟨out, .v1, .b2a, akPtr, authKey⟩) R)
    (hb : b &&& 0xfff#64 = 0#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63) (hinv1 : ∀ img, ImgCallInv img s0 → ImgCallInv img s1)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.b2a.toI32) (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 : s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt ∗
        memRegion (s0.sp - 1040#64) 992))
      (InitInnerPostExt A F b s0 ⟨out, .v1, .b2a, akPtr, authKey⟩) (InitInnerPanicExt s0 R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt ∗
       memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 17872#64) 13776 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b) := by
    rw [memRegion_992_split_b2a_ext s0.sp, stackAt_authNewExt_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_b2a_of_sub halloc hshim hmemcpy4k s0 s1 out akPtr authKey _ R
    hsp0_align hlt hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP_ext (init_inner_bl_192_ext s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
  have hcs_hi3 := calleeSaved_chain_hi_ext hcs2 hcs3
  have hx29_3 := calleeSaved_x29_ext hx29_2 hcs3
  have hx19_3 := calleeSaved_x19_ext hx19_2 hcs3
  have hsplit_auth :
      vecU8 A (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗ A.pool ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 17872#64) 13776 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗ vecU8 A (s0.sp - 1032#64) authKey ∗
       A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗
      (cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b) := by
    rw [stackAt_authNewExt_split_allocHook (s0.sp - 1040#64)]; ac_rfl
  refine hcall_auth s3 ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 196#64) _ _
    (fun img h0 => hinv3 img (hinv2 img (hinv1 img h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3 (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hsplit_auth ?_
  intro s4 a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcs4 htr4
  have hcs_hi4 := calleeSaved_chain_hi_ext hcs_hi3 hcs4
  have hx29_4 := calleeSaved_x29_ext hx29_3 hcs4
  have hx19_4 := calleeSaved_x19_ext hx19_3 hcs4
  have hpre_post_auth :
      (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
         ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (s0.sp - 1032#64) 24 ∗ A.pool ∗ stackAt (s0.sp - 1040#64) authNewStackExt) ∗
       (cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
        cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
        memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
        memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1032#64) 20 ∗
      cells (s0.sp - 872#64) 20 ∗ cells (s0.sp - 712#64) 17 ∗
      (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
      memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
      (memRegion (s0.sp - 1040#64) 8 ∗ stackAt (s0.sp - 1040#64) authNewStackExt ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗ A.pool) := by
    rw [← memRegion_24_and_cells_17_eq_cells_20_ext s0.sp]; exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine initInner_seq_sepWP_ext
    (init_inner_b2a_post_auth s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 hpc5 hrun5 _ ⟨hsp5, hx8_5, hx0_5, hcs5, htr5⟩
  exact init_inner_from_412_ext
    (states_into_pb_initV1State_of_sub halloc hdealloc hshim hmemcpy4k .b2a authKey)
    s0 s5 out akPtr R hb hsp0_align
    hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

private theorem init_inner_body_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hdealloc : DeallocOkExt b A ext)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hmemcpy4k : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (s0 : State) (x : InitInnerGhost) (R : SepProp)
    (hcall_auth : AuthCallAtExt A F b ext s0 x.authKey (InitInnerPostExt A F b s0 x) R)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (hrun : s0.status = .Running)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpure :
      s0.readReg64 .x0 = x.out ∧ s0.readReg32 .x1 = x.v.toI32 ∧
      s0.readReg32 .x2 = x.d.toI32 ∧ s0.readReg64 .x3 = x.akPtr ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧ 32 + x.authKey.length < 2 ^ 63 ∧ b &&& 0xfff#64 = 0#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
      (memRegion x.out optProtoInnerStateSize ∗ (x.akPtr ↦ₛ x.authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp initInnerStackExt)
      (InitInnerPostExt A F b s0 x)
      (InitInnerPanicExt s0 R) := by
  rcases x with ⟨out, v, d, akPtr, authKey⟩
  rcases hpure with ⟨hx0, hw1, hw2, hx3, hx4, _, hlt32, hb⟩
  cases v
  · have hpre_v0 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp initInnerStackExt ⊢
        memRegion out optProtoInnerStateSize ∗ stackAt s0.sp initInnerStack ∗
        (memRegion (s0.sp - 18912#64) 1232 ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗ A.pool) := by
      rw [stackAt_initInnerExt_split_base s0.sp]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpre_v0 ?_
    refine initInner_seq_sepWP_ext
      (init_inner_v0 (A := A) (F := F) s0 out d authKey
        (memRegion (s0.sp - 18912#64) 1232 ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗ A.pool)
        hsp0_align hpc hrun hx0 hw1) ?_
    intro sf hpcf hrunf _ ⟨hspf, hcsf, htrf⟩
    refine SepWPp.done hpcf hrunf ⟨?_, hspf, hcsf, htrf⟩
    rw [stackAt_initInnerExt_split_base s0.sp]
    exact Entails.of_eq (by ac_rfl)
  · have hpre_v1 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp initInnerStackExt ⊢
        cells (s0.sp - 48#64) 6 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTableAt b ∗ A.pool ∗
         stackAt (s0.sp - 1040#64) authNewStackExt ∗ memRegion (s0.sp - 1040#64) 992) := by
      rw [stackAt_initInnerExt_split s0.sp]
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpre_v1 ?_
    refine initInner_seq_sepWP_ext
      (init_inner_prologue_v1 s0 out akPtr d authKey _
        hsp0_align hpc hrun hx0 hw1 hw2 hx3 hx4) ?_
    intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx29_1, hx19_1, hx20_1, hw2_1, hx3_1, hcs1, htr1⟩
    cases d
    · exact init_inner_v1_a2b_ext halloc hshim hmemcpy4k s0 s1 out akPtr authKey R hcall_auth hb hsp0_align
        (by dsimp at hlt32; omega) hinv1 hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1
    · exact init_inner_v1_b2a_ext halloc hdealloc hshim hmemcpy4k s0 s1 out akPtr authKey R hcall_auth hb hsp0_align
        (by dsimp at hlt32; omega) hinv1 hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1

/-- Top-level verification of `spqr::init_inner` (`0x532dc`) against `initInnerSpecExt A F b`. -/
theorem init_inner_ok_base_ext
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hauth : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr authNewName)
      (authNewSpecExt F A)) :
    InitInnerBaseOkExt b A F ext := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0_align
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [initInnerSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2.1
  have hauth_raw := sub_ok_of_addr_eq
    (fnAddr_rel64_ext (b := b) (H := Rust.withPanics ext)
      (rel := bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      initInner_fnOff (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new") (by decide)).symm hauth
  have hcall_auth : AuthCallAtExt A F b ext s0 x.authKey (InitInnerPostExt A F b s0 x) R :=
    fun s ret_pc P Frame _ hpcs hruns hsps hlrs htrs hx0s hx1s hsplits hnext =>
      call_authNew_base_ext hauth_raw x.authKey hlt32 s0 s ret_pc P Frame R
        hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hsplits hnext
  exact ⟨_, R, hm, sepWPp_of_init_inner_wpp_ext s0 s0 x _ R
    (init_inner_body_ext hA.alloc hA.dealloc hA.shim (hA.session_memcpy allocHookStack)
      s0 x R hcall_auth hpc hrun hsp0_align hpure)⟩

/-- Top-level 4K-hook verification of `spqr::init_inner` (`0x532dc`) against
    `(initInnerSpecExt A F img.base).inImage img` from `AllocHooks`, `sessionShimSpec`,
    `sessionMemcpySpec allocHookStack`, and `AuthNewOkExt`. -/
theorem init_inner_ok_x_ext_of_hooks4k
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext shimName sessionShimSpec)
    (hMemcpy : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (hauth : AuthNewOkExt img F A ext) :
    InitInnerOkXExt img A F ext := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0_align
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [Spec.inImage, initInnerSpecExt] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2.1
  have halloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocName) (rustAllocSpec A) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      alloc_ok_at_ext img.base A ext hAlloc allocName 0 (Nat.add_zero _)
  have hdealloc : DeallocOkExt img.base A ext := by
    simpa only [DeallocOkExt, dropProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext img.base A ext hAlloc LibsignalTripleRatchet.deallocName 0 (Nat.add_zero _)
  have hshim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr shimName) sessionShimSpec := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (hook_ok_at (hname := shimName) rfl (Nat.add_zero _) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by decide +kernel) hShim :
        subroutine_ok (tripleRatchetProgAtExt img.base ext)
          ((tripleRatchetProgAtExt img.base ext).fnAddr shimName + BitVec.ofNat 64 0) sessionShimSpec)
  have hmemcpy4k : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (hook_ok_at (hname := memcpyName) rfl (Nat.add_zero _) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by decide +kernel) hMemcpy :
        subroutine_ok (tripleRatchetProgAtExt img.base ext)
          ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName + BitVec.ofNat 64 0)
          (sessionMemcpySpec allocHookStack))
  have hauth_raw := sub_ok_of_addr_eq
    (fnAddr_rel64_ext (b := img.base) (H := Rust.withPanics ext)
      (rel := bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      initInner_fnOff (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new") (by decide)).symm hauth
  have hcall_auth : AuthCallAtExt A F img.base ext s0 x.authKey (InitInnerPostExt A F img.base s0 x) R :=
    fun s ret_pc P Frame hinv_s hpcs hruns hsps hlrs htrs hx0s hx1s hsplits hnext =>
      call_authNew_x_ext hauth_raw x.authKey hlt32 s0 s ret_pc P Frame R
        (hinv_s img hinv0) hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hsplits hnext
  exact ⟨_, R, hm, sepWPp_of_init_inner_wpp_ext s0 s0 x _ R
    (init_inner_body_ext halloc hdealloc hshim hmemcpy4k
      s0 x R hcall_auth hpc hrun hsp0_align hpure)⟩

/-- Top-level verification of `spqr::init_inner` (`0x532dc`) against
    `(initInnerSpecExt A F img.base).inImage img` given `AllocContracts` + `AuthNewOkExt`. -/
theorem init_inner_ok_x_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hauth : AuthNewOkExt img F A ext) :
    InitInnerOkXExt img A F ext := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0_align
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [Spec.inImage, initInnerSpecExt] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2.1
  have hauth_raw := sub_ok_of_addr_eq
    (fnAddr_rel64_ext (b := img.base) (H := Rust.withPanics ext)
      (rel := bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      initInner_fnOff (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new") (by decide)).symm hauth
  have hcall_auth : AuthCallAtExt A F img.base ext s0 x.authKey (InitInnerPostExt A F img.base s0 x) R :=
    fun s ret_pc P Frame hinv_s hpcs hruns hsps hlrs htrs hx0s hx1s hsplits hnext =>
      call_authNew_x_ext hauth_raw x.authKey hlt32 s0 s ret_pc P Frame R
        (hinv_s img hinv0) hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hsplits hnext
  exact ⟨_, R, hm, sepWPp_of_init_inner_wpp_ext s0 s0 x _ R
    (init_inner_body_ext hA.alloc hA.dealloc hA.shim (hA.session_memcpy allocHookStack)
      s0 x R hcall_auth hpc hrun hsp0_align hpure)⟩

end CryptoVerification.SpqrV1.Top.InitInner
