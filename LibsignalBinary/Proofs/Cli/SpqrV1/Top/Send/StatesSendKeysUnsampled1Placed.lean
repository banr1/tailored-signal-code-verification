/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Inlined `.keysUnsampled` Sub-Steps (`+372..+684`, Block `427`)

Proves `signal_session_coins_fill` randomness extraction, ML-KEM key generation, and
`hdr` / `ek` / `dk` heap allocations (`+372..+684`) under `[LibsignalPlacement]`.
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
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout
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

abbrev spqrMlkemFromSeedSym : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes9from_seed"

abbrev spqrMlkemPk1Sym : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk1"

abbrev spqrMlkemPk2Sym : String :=
  "_RNvMs0_NtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incrementalNtB5_22KeyPairCompressedBytes3pk2"

abbrev spqrMlkemEncaps1Sym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental12encapsulate1"

theorem spqrSend_mlkemFromSeed_ok_placed {K : MlKem} {ext : String → Option (State → State)}
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (mlkemFromSeedSpec K)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemFromSeedSym) (mlkemFromSeedSpec K) :=
  spqr_hook_ok_of_mem hseed

theorem spqrSend_mlkemPk1_ok_placed {ext : String → Option (State → State)}
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym mlkemPk1Spec) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemPk1Sym) mlkemPk1Spec :=
  spqr_hook_ok_of_mem hpk1

theorem spqrSend_mlkemPk2_ok_placed {ext : String → Option (State → State)}
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym mlkemPk2Spec) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemPk2Sym) mlkemPk2Spec :=
  spqr_hook_ok_of_mem hpk2

theorem spqrSend_encapsulate1_ok_placed {K : MlKem} {ext : String → Option (State → State)}
    (henc : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (mlkemEncaps1Spec K)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemEncaps1Sym) (mlkemEncaps1Spec K) :=
  spqr_hook_ok_of_mem henc

theorem spqrSend_shim_ok_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
  spqr_hook_ok_of_mem hA.shim

theorem spqrSend_alloc_ok_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
  spqr_hook_ok_of_mem hA.alloc

theorem spqrSend_dealloc_ok_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ ComputeAt.spqrRustDeallocSym) (rustDeallocSpec A) :=
  spqr_hook_ok_of_mem hA.dealloc

theorem spqrSend_handle_error_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    (spqrSendPlacedProg ext).externAt? (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  (spqr_externAt?_of_mem).trans hA.handle_error

theorem call_rustAlloc_lscro {A : RustAlloc} {prog : Program}
    {entry_alloc ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry_alloc (rustAllocSpec A))
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
  refine call_rustAlloc hcall size 1 hlay (s0 := s0) (ret_pc := ret_pc) (sp_call := sp_call)
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
  apply SepWP.done hpc1 hrun1
  intro hcrl1
  by_cases h0 : sf1.readReg64 (Reg.gpr 0#5) = 0
  · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
    have hassoc :
        stackAt sp_call spqrSendCalleeStack ∗
          ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ A.pool ∗ Frame =
        ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
    rw [hassoc]
    refine ProofLib.SepWPp.pure_elim fun htr_oom => ?_
    exact hoom sf1 hcrl1 hpc1 hrun1 hsp1 hcs1 h0 htr_oom
  · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
    have hassoc :
        stackAt sp_call spqrSendCalleeStack ∗
          ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool ∗ Frame =
        ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
          ((A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
            A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
    rw [hassoc]
    refine ProofLib.SepWPp.pure_elim fun htr_ok => ?_
    have h0b : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne h0
    exact hok sf1 hcrl1 hpc1 hrun1 hsp1 hcs1 h0 h0b htr_ok.2

/-- Relocatable sub-step 1a (`spqrSendPlacedEntry + 372#64 -> spqrSendPlacedEntry + 512#64`):
    copies `epoch` and inline `Authenticator` words, fills 64-byte `seed` via `signal_session_coins_fill`,
    generates 2400-byte ML-KEM keypair via `from_seed` at `sp + 4704#64`, and calls `pk1`. -/
theorem step_keysUnsampled_372_to_512_placed
    {K : MlKem} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (mlkemFromSeedSpec K))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym mlkemPk1Spec)
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64)
    (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = spqrSendPlacedEntry + 512#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext)
        (spqrSendPlacedEntry + 3068#64) sf
        ((authenticatorPinAt A g (sp + 7136#64) auth ∗
          memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
          memRegion (sp + 7536#64) 400 ∗
          spqrCoinsAfterPlaced ctl cur tape 64 ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 3068#64) s P post := by
  have hrng_call := spqrCoinsFillAtPlaced_of_after0_cro (cur := cur) (rest := tape) hcoinsFill
  have hseed_call := spqrSend_mlkemFromSeed_ok_placed hseed
  have hpk1_call := spqrSend_mlkemPk1_ok_placed hpk1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hrng_call hseed_call hpk1_call hnext ⊢
  subst hP
  apply sepWP_seq_lscro (mid := (blkPl_427).base + 440#64) hcrl
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 48) (k := 352) (b' := sp + 7184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 7184#64),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by bv_omega) (by decide),
      memRegion_64_eq_words8 (sp + 4192#64),
      memRegion_48_eq_words6 (sp + 7136#64),
      memRegion_64_eq_words8 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 23 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine SepWP.fold (words8At_entails_memRegion (sp + 7536#64) _ _ _ _ _ _ _ _)
    (by dsimp only [words8At]; sep_focus) ?_
  have hcoins_zero : spqrCoinsAtPlaced ctl cur tape ⊢ spqrCoinsAfterPlaced 0#64 cur tape 0 :=
    spqrCoinsAtPlaced_entails_after_zero 0#64 cur tape
  refine SepWP.fold hcoins_zero (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  rintro ⟨hcl_call, hro_call⟩
  wp_apply
  have hcoins_after_ctl : spqrCoinsAfterPlaced 0#64 cur tape 64 = spqrCoinsAfterPlaced ctl cur tape 64 := rfl
  wp_conv_pre => rw [List.take_append_of_le_length h64, Nat.min_eq_left h64, hcoins_after_ctl, ← hseed_val]
  obtain ⟨sw0, sw1, sw2, sw3, sw4, sw5, sw6, sw7, hseed_words⟩ :=
    exists_words8_of_len64 seed.toList (List.Vector.toList_length seed)
  wp_conv_pre => rw [hseed_words (sp + 7536#64)]; dsimp only [words8At]
  wp_steps
  have hfold_seed_4192 :
      words8At (sp + 4192#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ⊢ ((sp + 4192#64) ↦ₛ seed.toList) := by
    rw [hseed_words (sp + 4192#64)]
    exact Entails.refl _
  refine SepWP.fold hfold_seed_4192 (by dsimp only [words8At]; sep_focus) ?_
  clear hseed_words hfold_seed_4192
  refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
  wp_apply; wp_steps; wp_apply; wp_step
  refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp)
    (by simp only [‹sf_1.sp = _›, ‹sf.sp = _›, hsp]; sep_focus) ?_
  have hfold_end :
      authInlineWordsAt g (sp + 7136#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 7184#64) ↦₆₄ epoch) ∗
      memRegion (sp + 7192#64) 344 ∗
      ((sp + 4192#64) ↦ₛ seed.toList) ∗
      memRegion (sp + 4256#64) 440 ∗
      words8At (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ∗
      memRegion (sp + 7600#64) 336 ⊢
      authenticatorPinAt A g (sp + 7136#64) auth ∗
      memRegion (sp + 7184#64) 352 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 7536#64) 400 := by
    rw [authenticatorPinAt_eq_inline_heap A g (sp + 7136#64) auth,
        ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (sp + 7184#64),
        ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by bv_omega) (by decide)]
    have h7184 : ((sp + 7184#64) ↦₆₄ epoch) ⊢ ∃∗ d : BitVec 64, (sp + 7184#64) ↦₆₄ d :=
      Entails.sepExists_right _ (Entails.refl _)
    have h4192 := pointsToBytes_entails_memRegion (sp + 4192#64) seed.toList
    rw [List.Vector.toList_length] at h4192
    simp only [sepConj_assoc]
    exact sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono h7184
          (sepConj_mono (Entails.refl _)
            (sepConj_mono h4192
              (sepConj_mono (Entails.refl _)
                (sepConj_mono (words8At_entails_memRegion (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7)
                  (Entails.refl _)))))))
  refine SepWP.fold hfold_end
    (by dsimp only [authInlineWordsAt, words8At]; sep_focus) ?_
  refine finish_sepWP
    (hnext _
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *])
      (by simp only [Reg.x19, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *])
      (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; exact Entails.of_eq (by ac_rfl))

/-- Relocatable sub-step 1b (`spqrSendPlacedEntry + 512#64 -> spqrSendPlacedEntry + 684#64`):
    allocates 64-byte `hdr` buffer, 1152-byte `ek` buffer, and 2400-byte `dk` buffer,
    copies `pk1`, `pk2`, and `dk` from `sp + 4704#64`, and prepares arguments for `mac_hdr`. -/
theorem step_keysUnsampled_512_to_684_placed
    {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym mlkemPk2Spec)
    (sp epoch : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64)
    (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 684#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 →
      sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr →
      sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr →
      sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((A.live hdr_ptr 64 1 ∗
          (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗
          A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := spqrSend_shim_ok_placed hA
  have halloc := spqrSend_alloc_ok_placed hA
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hpk2_call := spqrSend_mlkemPk2_ok_placed hpk2
  have haerr := spqrSend_handle_error_placed hA
  have hek_len : (K.fromSeed seed).2.1.toList.length = 1152 := List.Vector.toList_length _
  have hdk_len : (K.fromSeed seed).2.2.toList.length = 2400 := List.Vector.toList_length _
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hmemcpy hpk2_call haerr ⊢
  subst hP
  apply of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hcrl
  wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hcrl1
  refine call_rustAlloc_lscro halloc 64 ⟨by decide, ⟨0, rfl⟩, by decide⟩
    (s0 := s0) (ret_pc := (blkPl_427).base + 528#64) (sp_call := sp) hcrl1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hcrl_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
    (fun sf1 hcrl_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
  · apply of_sepWP_lscro (mid := lsρ spqrHandleErrorSym) hcrl_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hcrl_ok1
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hpk1_words⟩ :=
      exists_words8_of_len64 (K.fromSeed seed).1.toList (List.Vector.toList_length _)
    wp_conv_pre =>
      rw [pointsToBytes_2400_expose_pk1 sp seed hpk1_slice,
          hpk1_words (sp + 7008#64),
          memRegion_64_eq_words8 (sf1.readReg64 (Reg.gpr 0#5))]
      dsimp only [words8At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 8 (apply SepWP.exists_elim; intro _)
    wp_steps
    have hfold_pk1 :
        words8At (sf1.readReg64 (Reg.gpr 0#5)) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
        words8At (sp + 7008#64) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
        (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 2304)) ∗
         ((sp + 7072#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 2304).drop 64))) ⊢
        ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗
        ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
      rw [← hpk1_words (sf1.readReg64 (Reg.gpr 0#5)),
          ← hpk1_words (sp + 7008#64),
          pointsToBytes_2400_expose_pk1 sp seed hpk1_slice]
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.fold hfold_pk1 (by dsimp only [words8At]; sep_focus) ?_
    clear hpk1_words hfold_pk1
    refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
    wp_apply; wp_steps
    refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp)
      (by simp only [hsp1]; sep_focus) ?_
    wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hcrl2
    refine call_rustAlloc_lscro halloc 1152 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      (s0 := s0) (ret_pc := (blkPl_427).base + 584#64) (sp_call := sp) hcrl2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf2 hcrl_oom2 hpc2 hrun2 hsp2 _ h0_2 htr_oom2 => ?_)
      (fun sf2 hcrl_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
    · apply of_sepWP_lscro (mid := lsρ spqrHandleErrorSym) hcrl_oom2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [arm64_norm, *])
    · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hcrl_ok2
      have hek_mem : memRegion (sf2.readReg64 (Reg.gpr 0#5)) 1152 =
          memRegion (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList.length := by
        rw [hek_len]
      wp_conv_pre => rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, hek_mem]
      wp_steps; wp_apply; wp_steps
      have hfold_ek :
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 1152 1 ∗
          ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
          ((sp + 5856#64) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
          (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 1152)) ∗
           ((sp + 7008#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 1152).drop 1152))) ⊢
          RustHeap.vecU8Buf A 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
        rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, ← sepConj_assoc]
        exact sepConj_mono
          (live_pointsTo_entails_vecU8Buf (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList
            1152 hek_len (by decide) (by decide) hne0_2)
          (Entails.refl _)
      refine SepWP.fold hfold_ek (by sep_focus) ?_
      wp_apply; wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hcrl3
      refine call_rustAlloc_lscro halloc 2400 ⟨by decide, ⟨0, rfl⟩, by decide⟩
        (s0 := s0) (ret_pc := (blkPl_427).base + 620#64) (sp_call := sp) hcrl3
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) hsp_align
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
        (by sep_focus)
        (fun sf3 hcrl_oom3 hpc3 hrun3 hsp3 _ h0_3 htr_oom3 => ?_)
        (fun sf3 hcrl_ok3 hpc3 hrun3 hsp3 hcs3 hne0_3 h0b_3 htr_ok3 => ?_)
      · apply of_sepWP_lscro (mid := lsρ spqrHandleErrorSym) hcrl_oom3
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        intro _
        exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [arm64_norm, *])
      · rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
        simp only [wp_norm, arm64_norm, *] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
        apply of_sepWP_lscro (mid := (blkPl_427).base + 684#64) hcrl_ok3
        have hdk_mem : memRegion (sf3.readReg64 (Reg.gpr 0#5)) 2400 =
            memRegion (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList.length := by
          rw [hdk_len]
        wp_conv_pre => rw [hdk_mem]
        wp_steps; wp_apply; wp_steps
        have hfold_dk :
            A.live (sf3.readReg64 (Reg.gpr 0#5)) 2400 1 ∗
            ((sf3.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
            ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ⊢
            RustHeap.vecU8Buf A 2400#64 (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList ∗
            memRegion (sp + 4704#64) 2400 := by
          have h4704 := pointsToBytes_entails_memRegion (sp + 4704#64) (K.fromSeed seed).2.2.toList
          rw [hdk_len] at h4704
          rw [← sepConj_assoc]
          exact sepConj_mono
            (live_pointsTo_entails_vecU8Buf (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList
              2400 hdk_len (by decide) (by decide) hne0_3)
            h4704
        refine SepWP.fold hfold_dk (by sep_focus) ?_
        refine finish_sepWP_lscro (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (fun hcrl4 => hnext _ (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) (sf3.readReg64 (Reg.gpr 0#5))
            hcrl4 hne0_1 h0b_1
            (by simp only [spqrSendPlacedEntry, wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
            (by simp only [State.sp, arm64_norm, *])
            (by simp only [Reg.x0, arm64_norm, *])
            (by simp only [Reg.x1, arm64_norm, *])
            (by simp only [Reg.x2, arm64_norm, *])
            (by simp only [Reg.x3, arm64_norm, *])
            (by simp only [Reg.x8, arm64_norm, *])
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
          (Entails.of_eq (by ac_rfl))

end CryptoVerification.Cli.SpqrV1.Top.Send
