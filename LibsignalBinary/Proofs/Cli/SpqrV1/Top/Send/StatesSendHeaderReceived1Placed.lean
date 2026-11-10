/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived1
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Inlined `States::send` `.headerReceived` Arm (Part 1: `+1312..+1680`, Block `427`)

Proves ML-KEM encapsulation, `ct1` / `info` allocation, HKDF derivation, and authenticator
update (`+1312..+1680`) in Block `427` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
open KeysUnsampledHelpers

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-- `hkdf_to_vec` (Block `378`) meets `withLsCodeRoLoaded lsmpl (hkdfToVecSpqrSpec A HkdfFn)`
    on `spqrSendPlacedProg ext`. -/
def HkdfToVecPlacedOkX (A : RustAlloc) (HkdfFn : Bytes → Bytes → Bytes → Nat → Bytes)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
    (withLsCodeRoLoaded lsmpl (hkdfToVecSpqrSpec A HkdfFn))

/-- `<Authenticator>::update` (Block `341`) meets
    `withLsCodeRoLoaded lsmpl (authUpdateSpec F A)` on `spqrSendPlacedProg ext`. -/
def AuthUpdatePlacedOkX (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
    (withLsCodeRoLoaded lsmpl (authUpdateSpec F A))

abbrev spqrRustAllocZeroedSym : String := "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed"

theorem spqrSend_allocZeroed_ok_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedSpec A)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocZeroedSym) (rustAllocZeroedSpec A) :=
  spqr_hook_ok_of_mem hZero

/-- Call rule for `__rust_alloc_zeroed(size, 1)` inside `spqrSendPlacedProg ext` under `LibsignalCodeRoLoaded`. -/
theorem call_rustAllocZeroed_lscro {A : RustAlloc} {prog : Program}
    {entry_alloc ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry_alloc (rustAllocZeroedSpec A))
    (size : Nat) (hlay : LayoutOk size 1)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry_alloc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size)
    (hx1 : (s.readReg64 Reg.x1).toNat = 1)
    (hsplit : P = (A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hoom : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) = 0 →
      sf.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp prog target_pc sf
        ((A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))
    (hok : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 →
      (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false →
      sf.trace = s0.trace →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rw [hsplit]
  refine of_sepWP_lscro (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall (x := (size, 1))
    (F := memRegion (sp_call - 123008#64) 118912 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  · intro R' hm
    dsimp only [rustAllocZeroedSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    rw [show ((memRegion (sp_call - 123008#64) 118912 ∗ stackAt sp_call allocHookStack) ∗ A.pool ∗ Frame) ∗ R' =
        (A.pool ∗ stackAt sp_call allocHookStack) ∗ (memRegion (sp_call - 123008#64) 118912 ∗ Frame) ∗ R' by ac_rfl] at hm
    exact ⟨⟨hx0, hx1, hlay⟩, hm⟩
  · dsimp only [rustAllocZeroedSpec]
    rw [hsp, htrace]
    refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
    apply SepWP.done hpc1 hrun1
    intro hcrl1
    by_cases h0 : sf1.readReg64 (Reg.gpr 0#5) = 0
    · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
      have hassoc :
          stackAt sp_call spqrSendCalleeStack ∗
            A.pool ∗ ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ Frame =
          ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
      rw [hassoc]
      refine ProofLib.SepWPp.pure_elim fun htr_oom => ?_
      exact hoom sf1 hcrl1 hpc1 hrun1 (hsp1.trans hsp) hcs1 h0 htr_oom
    · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
      have hassoc :
          stackAt sp_call spqrSendCalleeStack ∗
            A.pool ∗
            ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
            A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ List.replicate size 0#8) ∗
            Frame =
          ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
            ((A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
              (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ List.replicate size 0#8) ∗
              A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
      rw [hassoc]
      refine ProofLib.SepWPp.pure_elim fun htr_ok => ?_
      have h0b : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne h0
      refine of_sepWP_lscro (mid := ret_pc) hcrl1 ?_
      refine SepWP.fold (zeroed_entails_memRegion (sf1.readReg64 (Reg.gpr 0#5)) size) (by sep_focus) ?_
      apply SepWP.done hpc1 hrun1
      intro hcrl2
      have hframe :
          memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
            A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            A.pool ∗ stackAt sp_call spqrSendCalleeStack ∗ Frame =
          (A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
            A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame := by ac_rfl
      rw [hframe]
      exact hok sf1 hcrl2 hpc1 hrun1 (hsp1.trans hsp) hcs1 h0 h0b htr_ok.2

/-- Relocatable Sub-step 1a (`spqrSendPlacedEntry + 1312#64 -> spqrSendPlacedEntry + 1504#64`)
    on `K.encaps1 = some (ct1, es, ss)`. -/
theorem step_headerReceived_1312_to_1504_placed
    {K : MlKem} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedSpec A))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (mlkemEncaps1Spec K))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32)
    (hrand_val : rand.toList = tape.take 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (hencaps : K.encaps1 hdr rand = some (ct1, es, ss))
    (d4056 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
      ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
      (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗
      memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗
      memRegion (sp + 7536#64) 32 ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (es_ptr ss_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      es_ptr ≠ 0 → (es_ptr == 0#64) = false →
      ss_ptr ≠ 0 → (ss_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 1504#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = hdr_cap →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length →
      sf.readReg64 .x28 = sp + 4192#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((authInlineWordsAt g (sp + 4192#64) auth ∗
          authHeapBufs A g auth ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
          ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
          ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
          (hdr_ptr ↦ₛ hdr) ∗
          ((sp + 2464#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ((sp + 4704#64) ↦₈ 0#8) ∗
          ((sp + 4705#64) ↦ₛ ct1.toList) ∗
          RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗
          A.live ss_ptr 32 1 ∗
          (ss_ptr ↦ₛ ss.toList) ∗
          memRegion (sp + 7136#64) 32 ∗
          memRegion (sp + 7536#64) 32 ∗
          spqrCoinsAfterPlaced ctl cur tape 32 ∗
          A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := spqrSend_shim_ok_placed hA
  have hallocz := spqrSend_allocZeroed_ok_placed hZero
  have hrng_call := spqrCoinsFillAtPlaced_of_after0_cro (cur := cur) (rest := tape) hcoinsFill
  have henc1_call := spqrSend_encapsulate1_ok_placed henc1
  have haerr := spqrSend_handle_error_placed hA
  have hhdr_toNat : (BitVec.ofNat 64 hdr.length).toNat = hdr.length := Nat.mod_eq_of_lt (by omega)
  have hes_len : es.toList.length = 2080 := List.Vector.toList_length _
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hshim hallocz hrng_call henc1_call haerr ⊢
  subst hP
  simp only [Reg.x24, Reg.x26, Reg.x28] at hx24 hx26 hx28
  apply of_sepWP_lscro (mid := lsρ spqrRustAllocZeroedSym) hinv
  apply sepWP_seq_lscro (mid := (blkPl_427).base + 1380#64) hinv
  rw [memRegion_48_eq_words6 (sp + 4192#64),
      memRegion_32_eq_words4 (sp + 7136#64),
      memRegion_32_eq_words4 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine SepWP.fold (words4At_entails_memRegion (sp + 7136#64) _ _ _ _)
    (by dsimp only [words4At]; sep_focus) ?_
  have hcoins_zero : spqrCoinsAtPlaced ctl cur tape ⊢ spqrCoinsAfterPlaced 0#64 cur tape 0 :=
    spqrCoinsAtPlaced_entails_after_zero 0#64 cur tape
  refine SepWP.fold hcoins_zero (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  rintro ⟨hcl_call, hro_call⟩
  wp_apply
  have hcoins_after_ctl : spqrCoinsAfterPlaced 0#64 cur tape 32 = spqrCoinsAfterPlaced ctl cur tape 32 := rfl
  wp_conv_pre => rw [List.take_append_of_le_length h32, Nat.min_eq_left h32, hcoins_after_ctl, ← hrand_val]
  wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  refine call_rustAllocZeroed_lscro hallocz 2080 ⟨by decide, ⟨0, rfl⟩, by decide⟩
    (s0 := s0) (ret_pc := (blkPl_427).base + 1400#64) (sp_call := sp) hinv1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hinv_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
    (fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
  · apply of_sepWP_lscro (mid := lsρ spqrHandleErrorSym) hinv_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_lscro (mid := lsρ spqrRustAllocZeroedSym) hinv_ok1
    wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hinv2
    refine call_rustAllocZeroed_lscro hallocz 32 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      (s0 := s0) (ret_pc := (blkPl_427).base + 1424#64) (sp_call := sp) hinv2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf2 hinv_oom2 hpc2 hrun2 hsp2 _ h0_2 htr_oom2 => ?_)
      (fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
    · apply of_sepWP_lscro (mid := lsρ spqrHandleErrorSym) hinv_oom2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [arm64_norm, *])
    · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply of_sepWP_lscro (mid := (blkPl_427).base + 1504#64) hinv_ok2
      obtain ⟨rw0, rw1, rw2, rw3, hrand_words⟩ :=
        exists_words4_of_len32 rand.toList (List.Vector.toList_length rand)
      wp_conv_pre => rw [hrand_words (sp + 7136#64)]; dsimp only [words4At]
      wp_steps
      have hfold_rand_7536 :
          words4At (sp + 7536#64) rw0 rw1 rw2 rw3 ⊢ ((sp + 7536#64) ↦ₛ rand.toList) := by
        rw [hrand_words (sp + 7536#64)]
        exact Entails.refl _
      refine SepWP.fold hfold_rand_7536 (by dsimp only [words4At]; sep_focus) ?_
      refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
      wp_apply
      wp_conv_pre => simp only [hencaps, sepConj_assoc]
      wp_steps
      refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp)
        (by simp only [hsp2]; sep_focus) ?_
      have hfold_end :
          words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗
          ((sp + 7536#64) ↦ₛ rand.toList) ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 2080 1 ∗
          ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ es.toList) ⊢
          memRegion (sp + 7136#64) 32 ∗
          memRegion (sp + 7536#64) 32 ∗
          RustHeap.vecU8Buf A 2080#64 (sf1.readReg64 (Reg.gpr 0#5)) es.toList := by
        have h7536 := pointsToBytes_entails_memRegion (sp + 7536#64) rand.toList
        rw [List.Vector.toList_length] at h7536
        have hes_buf := live_pointsTo_entails_vecU8Buf (A := A) (sf1.readReg64 (Reg.gpr 0#5)) es.toList
          2080 hes_len (by decide) (by decide) hne0_1
        rw [show words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗ ((sp + 7536#64) ↦ₛ rand.toList) ∗
              A.live (sf1.readReg64 (Reg.gpr 0#5)) 2080 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ es.toList) =
            words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗ ((sp + 7536#64) ↦ₛ rand.toList) ∗
            (A.live (sf1.readReg64 (Reg.gpr 0#5)) 2080 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ es.toList)) by ac_rfl]
        exact sepConj_mono (words4At_entails_memRegion (sp + 7136#64) rw0 rw1 rw2 rw3)
          (sepConj_mono h7536 hes_buf)
      refine SepWP.fold hfold_end
        (by dsimp only [words4At]; sep_focus) ?_
      refine finish_sepWP_lscro (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (fun hinv3 => hnext _ (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5))
          hinv3 hne0_1 h0b_1 hne0_2 h0b_2
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, arm64_norm, *])
          (by simp only [Reg.x19, arm64_norm, *])
          (by simp only [Reg.x20, arm64_norm, *])
          (by simp only [Reg.x21, arm64_norm, *])
          (by simp only [Reg.x22, arm64_norm, *])
          (by simp only [Reg.x23, arm64_norm, *])
          (by simp only [Reg.x24, arm64_norm, *])
          (by simp only [Reg.x25, arm64_norm, *])
          (by simp only [Reg.x26, arm64_norm, *])
          (by simp only [Reg.x27, arm64_norm, *])
          (by simp only [Reg.x28, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; exact Entails.of_eq (by ac_rfl))

/-! ## Sub-step 2 (`(blkPl_427).base + 1504#64 -> (blkPl_427).base + 1680#64`) -/

theorem finish_sepWP_lscro_drop_ro {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P' Ro : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWPp prog ret s P' Q Qp)
    (himp : P ⊢ Ro ∗ P') :
    SepWP prog mid s P (fun sf P_f => LibsignalCodeRoLoaded lsmpl sf.mem → SepWPp prog ret sf P_f Q Qp) := by
  refine SepWP.fold himp (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  apply SepWP.done hpc hrun
  intro hinv R hsat hL
  apply hnext hinv R ?_ hL
  rw [sepConj_assoc] at hsat
  exact Satisfies.of_sep_right hsat

theorem rodata_sckaKeyInfoPrefix_placed {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29") ↦ᵣ sckaKeyInfoPrefix) ∗ P :=
  lsro_intro_chk (sym := "libsignal_cli_ratchet:.rodata..Lanon.29") (bs := sckaKeyInfoPrefix)
    hro (by decide +kernel) hP

theorem rodata_zeros32_send_placed {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8) ∗ P :=
  lsro_intro_chk (sym := "libsignal_cli_ratchet:.rodata.cst32+0x0") (bs := List.replicate 32 0#8)
    hro (by decide +kernel) hP

omit [LibsignalPlacement] in
theorem sckaKeyInfoPrefix_ro_split (a : BitVec 64) :
    (a ↦ᵣ sckaKeyInfoPrefix) =
    (a ↦₆₄ᵣ sckaInfoW0) ∗
    ((a + 8#64) ↦₆₄ᵣ sckaInfoW1) ∗
    ((a + 16#64) ↦₆₄ᵣ sckaInfoW2) ∗
    ((a + 24#64) ↦₆₄ᵣ sckaInfoW3) ∗
    ((a + 32#64) ↦ᵣ [0x79#8]) := by
  rw [sckaKeyInfoPrefix_eq_unpack64]
  rw [ProofLib.pointsToBytesRO_append a (unpack64 sckaInfoW0), unpack64_length,
      ProofLib.pointsToBytesRO_append (a + 8#64) (unpack64 sckaInfoW1), unpack64_length,
      show (a + 8#64) + 8#64 = a + 16#64 by bv_omega,
      ProofLib.pointsToBytesRO_append (a + 16#64) (unpack64 sckaInfoW2), unpack64_length,
      show (a + 16#64) + 8#64 = a + 24#64 by bv_omega,
      ProofLib.pointsToBytesRO_append (a + 24#64) (unpack64 sckaInfoW3), unpack64_length,
      show (a + 24#64) + 8#64 = a + 32#64 by bv_omega,
      ← pointsTo64RO_eq_pointsToBytesRO a sckaInfoW0,
      ← pointsTo64RO_eq_pointsToBytesRO (a + 8#64) sckaInfoW1,
      ← pointsTo64RO_eq_pointsToBytesRO (a + 16#64) sckaInfoW2,
      ← pointsTo64RO_eq_pointsToBytesRO (a + 24#64) sckaInfoW3]

theorem step_headerReceived_1504_to_1680_placed {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hhkdf : HkdfToVecPlacedOkX A (hkdfToVecUnchecked F) ext)
    (hupd : AuthUpdatePlacedOkX F A ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ss_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (hdr : Header)
    (ct1 : List.Vector (BitVec 8) 960)
    (ss : List.Vector (BitVec 8) 32)
    (hroot_len : auth.rootKey.length + 32 < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr)
    (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = hdr_cap)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      memRegion (sp + 32#64) 16 ∗ authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 4704#64) ↦₈ 0#8) ∗ ((sp + 4705#64) ↦ₛ ct1.toList) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7536#64) 32 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (ct1_ptr info_ptr secret_cap secret_ptr : BitVec 64),
      let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      let auth' := auth.update F epoch secret
      LibsignalCodeRoLoaded lsmpl sf.mem →
      ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false →
      info_ptr ≠ 0 → (info_ptr == 0#64) = false →
      secret_ptr ≠ 0 → (secret_cap == 0#64) = false →
      32 ≤ secret_cap.toNat → secret_cap.toNat < 2 ^ 63 →
      sf.pc = spqrSendPlacedEntry + 1680#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length → sf.readReg64 .x28 = info_ptr →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authenticatorAt A (sp + 4192#64) auth' ∗ memRegion (sp + 4704#64) 961 ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := spqrSend_shim_ok_placed hA
  have halloc := spqrSend_alloc_ok_placed hA
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have haerr := spqrSend_handle_error_placed hA
  have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length _
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length _
  have hhkdf_call : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 378) (withLsCodeRoLoaded lsmpl (hkdfToVecSpqrSpec A (hkdfToVecUnchecked F))) := hhkdf
  have hupd_call : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 341) (withLsCodeRoLoaded lsmpl (authUpdateSpec F A)) := hupd
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x27]
    at hx20 hx21 hx22 hx24 hx25 hx26 hx27
  apply of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hinv
  rw [memRegion_32_16_eq_words2 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 2 (apply SepWP.exists_elim; intro _)
  wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  refine call_rustAlloc_lscro halloc 960 ⟨by decide, ⟨0, rfl⟩, by decide⟩
    (s0 := s0) (ret_pc := (blkPl_427).base + 1524#64) (sp_call := sp) hinv1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hinv_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
    (fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
  · apply of_sepWP_lscro (mid := lsρ spqrHandleErrorSym) hinv_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hinv_ok1
    have hct1_mem : memRegion (sf1.readReg64 (Reg.gpr 0#5)) 960 =
        memRegion (sf1.readReg64 (Reg.gpr 0#5)) ct1.toList.length := by rw [hct1_len]
    wp_conv_pre => rw [hct1_mem, ← sp_add_4704_orr_1_eq hsp_align]
    wp_steps; wp_apply; wp_steps
    wp_conv_pre => rw [sp_add_4704_orr_1_eq hsp_align]
    refine SepWP.fold (pointsTo8_and_ct1_entails_memRegion_961 sp 0#8 ct1) (by sep_focus) ?_
    wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hinv2
    refine call_rustAlloc_lscro halloc 41 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      (s0 := s0) (ret_pc := (blkPl_427).base + 1572#64) (sp_call := sp) hinv2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf2 hinv_oom2 hpc2 hrun2 hsp2 _ h0_2 htr_oom2 => ?_)
      (fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
    · apply of_sepWP_lscro (mid := lsρ spqrHandleErrorSym) hinv_oom2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [arm64_norm, *])
    · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply sepWPp_intro_rodata (rodata_sckaKeyInfoPrefix_placed hinv_ok2.2)
      apply sepWPp_intro_rodata (rodata_zeros32_send_placed hinv_ok2.2)
      apply of_sepWP_lscro (mid := lsmpl.base 378) hinv_ok2
      rw [sckaKeyInfoPrefix_ro_split (lsρ "libsignal_cli_ratchet:.rodata..Lanon.29"),
          memRegion_41_eq_infoSlots (sf2.readReg64 (Reg.gpr 0#5)),
          memRegion_32_split_24_8 (sp + 7536#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      iterate 6 (apply SepWP.exists_elim; intro _)
      wp_conv_pre => simp only [BitVec.add_assoc, arm64_norm]
      wp_steps
      refine SepWP.fold (infoSlots_entails_pointsToBytes (sf2.readReg64 (Reg.gpr 0#5)) epoch)
        (by sep_focus) ?_
      refine finish_sepWP_lscro_drop_ro (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (Ro := ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29") ↦₆₄ᵣ sckaInfoW0) ∗
               ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 8#64) ↦₆₄ᵣ sckaInfoW1) ∗
               ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 16#64) ↦₆₄ᵣ sckaInfoW2) ∗
               ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 24#64) ↦₆₄ᵣ sckaInfoW3) ∗
               ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 32#64) ↦₈ᵣ 0x79#8))
        (P' := (((lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8) ∗
          ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A g auth ∗
          memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗
          ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ (sckaKeyInfoPrefix ++ epochBeBytes epoch)) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          memRegion (sp + 7536#64) 24 ∗ memRegion (sp + 7560#64) 8 ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
        (fun hinv3 => ?_) (Entails.of_eq (by ac_rfl))
      have hpre_len : sckaKeyInfoPrefix.length = 33 := rfl
      have hinfo_len : (sckaKeyInfoPrefix ++ epochBeBytes epoch).length = 41 := by
        rw [List.length_append, hpre_len, epochBeBytes_length]
      let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      refine call_lscro_calleeStack (entry := lsmpl.base 378)
        (spec := hkdfToVecSpec A (hkdfToVecUnchecked F))
        (x := ({
          outVec := sp + 7536#64,
          saltRO := true, saltA := lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0", salt := List.replicate 32 0#8,
          ikmRO := false, ikmA := ss_ptr, ikm := ss.toList,
          infoRO := false, infoA := sf2.readReg64 (Reg.gpr 0#5), info := info,
          okmLen := 32 } : HkdfToVecGhost))
        (s0 := s0) sp extHookStack (by decide)
        (T_pre := memRegion (sp + 7536#64) 24 ∗ ((lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8) ∗
          (ss_ptr ↦ₛ ss.toList) ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗ A.pool)
        (T_post := fun _ => vecU8 A (sp + 7536#64) secret ∗ ((lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8) ∗
          (ss_ptr ↦ₛ ss.toList) ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗ A.pool)
        (F := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A g auth ∗ memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗ A.live ss_ptr 32 1 ∗
          memRegion (sp + 7560#64) 8 ∗ Frame)
        (φ_pre := _) (φ_post := _) hhkdf_call hinv3
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
        hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_427).base + 1656#64) (by simp only [Reg.lr, arm64_norm, *])
        (by simp only [hkdfToVecSpec, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte]; ac_rfl)
        (by
          dsimp only [info]; rw [hss_len, hinfo_len]
          simp only [Reg.x8, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
            List.length_replicate, wp_norm, arm64_norm, *])
        (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
        (by intro _; simp only [hkdfToVecSpec, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte, secret]; ac_rfl) ?_
      intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 hφ_sm1 hinv_sm1
        hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
      have hsec_len : secret.length = 32 := by simp only [secret, hφ_sm1]
      have htr_sm1 : sm1.trace = s0.trace := by
        simp only [secret, wp_norm, arm64_norm, *] at hφ_sm1; exact hφ_sm1
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        wp_norm, arm64_norm, *] at hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
      apply of_sepWP_lscro (mid := lsmpl.base 341) hinv_sm1
      refine SepWP.fold (vecU8_len32_expose_7536 sp secret hsec_len) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro secret_cap
      apply SepWP.exists_elim; intro secret_ptr
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨hsec_cap_ge, hsec_cap_lt, hsec_ptr_ne, hsec_cap_b⟩ => ?_
      refine SepWP.fold (fold_authenticatorAt_of_inline_local A g (sp + 4192#64) auth)
        (by sep_focus) ?_
      wp_steps
      refine finish_sepWP_lscro_drop_ro (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (Ro := (lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8)
        (P' := (((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authenticatorAt A (sp + 4192#64) auth ∗ memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
        (fun hinv4 => ?_) (Entails.of_eq (by ac_rfl))
      refine call_lscro_calleeStack (entry := lsmpl.base 341)
        (spec := authUpdateSpec F A)
        (x := ({
          selfA := sp + 4192#64, auth := auth, ep := epoch,
          kRO := false, kA := secret_ptr, k := secret } : AuthUpdateGhost))
        (s0 := s0) sp authUpdateStackX (by decide)
        (T_pre := authenticatorAt A (sp + 4192#64) auth ∗ (secret_ptr ↦ₛ secret) ∗ A.pool)
        (T_post := fun _ => authenticatorAt A (sp + 4192#64) (auth.update F epoch secret) ∗
          (secret_ptr ↦ₛ secret) ∗ A.pool)
        (F := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗ Frame)
        (φ_pre := _) (φ_post := _) hupd_call hinv4
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
        hsp_align (by simp only [arm64_norm, *]) (ret_pc := (blkPl_427).base + 1680#64) (by simp only [Reg.lr, arm64_norm, *])
        (by simp only [authUpdateSpec, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte]; ac_rfl)
        (by
          rw [hsec_len]
          simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, wp_norm, arm64_norm, *]; omega)
        (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
        (by intro _; simp only [authUpdateSpec, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte]; ac_rfl) ?_
      intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2 hinv_sm2
        hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        wp_norm, arm64_norm, *] at htr_sm2 hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
      apply of_sepWP_lscro (mid := (blkPl_427).base + 1680#64) hinv_sm2
      refine finish_sepWP_lscro hpc_sm2 hrun_sm2
        (fun hinv5 => hnext sm2 (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) secret_cap secret_ptr
          hinv5 hne0_1 h0b_1 hne0_2 h0b_2 hsec_ptr_ne hsec_cap_b hsec_cap_ge hsec_cap_lt
          hpc_sm2 hrun_sm2 hsp_sm2
          hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 htr_sm2
          (by simp only [wp_norm, arm64_norm, *]))
        (Entails.of_eq (by ac_rfl))

end CryptoVerification.Cli.SpqrV1.Top.Send
