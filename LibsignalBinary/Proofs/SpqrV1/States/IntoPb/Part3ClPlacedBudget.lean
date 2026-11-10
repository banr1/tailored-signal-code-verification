/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<States>::into_pb` (Block `334`) — Part 3 `withLsCodeLoaded`: Arm 1 (`States.keysSampled`)

Proves `withLsCodeLoaded` relocatable `RustCliAllocBudget M` contracts for Arm 1
(`States.keysSampled`, tag `3`, Block `334`) under `KeysSampledEnv` and `StatesIntoPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3ClPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded
   libsignalSessionCode lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (KeysSampled)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
   optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved authenticatorHeap bv_add_add_lit bv_sub_sub_lit
   chunkedKeysSampled_expose statesIntoPbJumpTablePlacedAt
   statesIntoPbSavedCells statesIntoPbStack vecU8Heap)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv encoderIntoPbSpec encoderIntoPbVecs)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (sepWPp_of_states_into_pb_exit_cl_placed statesIntoPbVariantPlacedSpec
   statesIntoPbVariantPlacedSpecOfEnv states_into_pb_prologue_60_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlacedBudget
  (call_encoderIntoPb_expose_wp_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget
  (KeysSampledEnv chunkedCt1Received_expose_generic
   chunkedKeysSampled_expose_generic fitsEnv_encoder_of_keysSampledEnv
   keysSampledEnv_imp_spqrBoundedEvs outWords28_entails_ct1Received_generic
   outWords28_entails_keysSampled_generic stA_sendEk_enc_entails_928_generic
   states_into_pb_keysSampled_post_vm_placed
   states_into_pb_keysSampled_pre_vm_placed
   unchunkedEkSentCt1Received_expose_generic)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5PlacedBudget
  (StatesIntoPbAllocPlacedBudget)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget
  (KeysSampledEnv fitsEnv_encoder_of_keysSampledEnv
   keysSampledEnv_imp_spqrBoundedEvs unchunkedEkSentCt1Received_expose_generic
   chunkedCt1Received_expose_generic chunkedKeysSampled_expose_generic
   stA_sendEk_enc_entails_928_generic outWords28_entails_ct1Received_generic
   outWords28_entails_keysSampled_generic)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit bv_add_add_lit
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-- Tight relocatable per-variant budget spec for `<States>::into_pb` on
    `.keysSampled s` over `KeysSampledEnv s`. -/
abbrev statesIntoPbKeysSampledPlacedSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (s : KeysSampled spqrPolyApi (spqrAuthApi F)) :
    Spec ((BitVec 64 × BitVec 64) × M.σ) :=
  statesIntoPbVariantPlacedSpecOfEnv M A lim F (.keysSampled s) (KeysSampledEnv s)

private theorem sepWP_seq_lscl [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State} {P : SepProp}
    {post1 post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → post1 sm Pm →
      SepWP prog target sm Pm post) :
    SepWP prog target s P post :=
  SepWP.seq_frozen (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpcm hrunm hp1 hclm => h2 sm Pm hpcm hrunm hclm hp1)

private theorem seq_clean_wp_lscl [LibsignalPlacement] {prog : Program}
    {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  sepWP_seq_lscl hcl h1 fun sm _Pm hpcm hrunm hclm ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

/-! ## Relocatable `withLsCodeLoaded` Main Theorems for Arm 1 (`States.keysSampled`) -/

/-- Envelope-parametric relocatable `subroutine_ok` for `<States>::into_pb` (Block `334`) on Arm 1
    (`States.keysSampled`, tag `3`, `+0 -> +60 -> +896 -> +1000 -> +1544 -> ret`) taking
    `withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)` on `<PolyEncoder>::into_pb` (`lsmpl.base 375`). -/
theorem states_into_pb_keysSampled_of_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : KeysSampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, KeysSampledEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.keysSampled s) Env)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, stA⟩, st⟩ R s0 hpc hrun hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesIntoPbVariantPlacedSpecOfEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hfit⟩, hmem⟩
  have hfit_enc : FitsEnv M lim st (EncoderIntoPbAllocEnv s.sending_hdr) :=
    fitsEnv_encoder_of_keysSampledEnv hEnv hfit
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc stA (.keysSampled s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · dsimp only [statesIntoPbJumpTablePlacedAt,
      CryptoVerification.SpqrV1.Top.InitInner.statesIntoPbJumpTablePlacedAt] at hmem ⊢
    simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_exit_cl_placed st s0 s0 out stA (.keysSampled s) Env _ R ?_
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedKeysSampled_expose A.repAlloc stA s))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  rename_i a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2
  have hpro := states_into_pb_prologue_60_placed (ext := ext) A lim st s0 out stA 3#64
    (polyEncoderAt A.repAlloc (stA + 8#64) s.sending_hdr ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
     ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
     ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.ek ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.dk ∗
     memRegion (stA + 512#64) 416 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt)
    hsp0_align hpc hrun hx8 hx0
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp_lscl hcl0 hpro fun s1 hpc1 hrun1 hcl1
      ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1, _⟩ => ?_)
  have h1416 : memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 104 ∗
      memRegion (s0.sp - 1256#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 1200#64) 720 ∗
      memRegion (s0.sp - 480#64) 96 ∗
      memRegion (s0.sp - 384#64) 80 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 := by
    change memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 104 ∗
      memRegion (s0.sp - 1256#64) 56 ∗
      memRegion (s0.sp - 1200#64) 720 ∗
      memRegion (s0.sp - 480#64) 96 ∗
      memRegion (s0.sp - 384#64) 80 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160
    rw [ProofLib.memRegion_split' (b := s0.sp - 1512#64) (n := 152) (k := 1264)
          (b' := s0.sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 104) (k := 1160)
          (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1256#64) (n := 56) (k := 1104)
          (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 720) (k := 384)
          (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 96) (k := 288)
          (b' := s0.sp - 384#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 384#64) (n := 80) (k := 208)
          (b' := s0.sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 304#64) (n := 48) (k := 160)
          (b' := s0.sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  have hpre_raw := states_into_pb_keysSampled_pre_vm_placed (ext := ext) s0 s1 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 s.uc.epoch
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) 104 ∗
     memRegion (s0.sp - 1256#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 1200#64) 720 ∗
     memRegion (s0.sp - 384#64) 80 ∗
     cells (s0.sp - 304#64) 6 ∗
     statesIntoPbSavedCells s0 ∗
     polyEncoderAt A.repAlloc (stA + 8#64) s.sending_hdr ∗
     authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A.repAlloc k0 k1 k2 s.uc.ek ∗
     vecU8Heap A.repAlloc d0 d1 d2 s.uc.dk ∗
     memRegion (stA + 512#64) 416 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool lim st s1)
  have hpre_step : SepWP ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) s1 _
      (fun s2 P2 =>
        (P2 ⊢
          (((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
           ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
           ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
           ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
           ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
           ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
           memRegion (s0.sp - 256#64) 160 ∗
           (stA ↦₆₄ 3#64) ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
           ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
           ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
           statesIntoPbJumpTablePlacedAt ∗
           (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
            ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
            cells (s0.sp - 1512#64) 19 ∗
            memRegion (s0.sp - 1360#64) 104 ∗
            memRegion (s0.sp - 1256#64) protoPolynomialEncoderSize ∗
            memRegion (s0.sp - 1200#64) 720 ∗
            memRegion (s0.sp - 384#64) 80 ∗
            cells (s0.sp - 304#64) 6 ∗
            statesIntoPbSavedCells s0 ∗
            polyEncoderAt A.repAlloc (stA + 8#64) s.sending_hdr ∗
            authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
            vecU8Heap A.repAlloc k0 k1 k2 s.uc.ek ∗
            vecU8Heap A.repAlloc d0 d1 d2 s.uc.dk ∗
            memRegion (stA + 512#64) 416 ∗
            memRegion out optProtoInnerStateSize ∗
            A.pool lim st s2))) ∧
        (s2.sp = s0.sp - 1520#64 ∧
         s2.readReg64 .x30 = (blkPl_334).base + 1000#64 ∧
         s2.readReg64 .x0 = s0.sp - 1256#64 ∧
         s2.readReg64 .x1 = stA + 8#64 ∧
         s2.readReg64 .x29 = s0.sp - 96#64 ∧
         s2.readReg64 .x27 = s0.sp - 1360#64 ∧
         s2.readReg64 .x21 = s.uc.epoch ∧
         s2.readReg64 .x19 = out ∧
         TraceCalleeSaved s2 s0)) :=
    SepWP.mono hpre_raw fun s2 _P2 _ _ ⟨hvm2, hP2, hregs⟩ =>
      ⟨by rw [A.pool_of_vmPreserved hvm2]; exact hP2, hregs⟩
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_clean_wp_lscl hcl1 hpre_step fun s2 hpc2 hrun2 hcl2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx29_2, hx27_2, hx21_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  refine call_encoderIntoPb_expose_wp_cl_placed henc_cl st
    (s0.sp - 1256#64) (stA + 8#64) s.sending_hdr
    hcl2 hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hfit_enc
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 104 ∗
      cells (s0.sp - 304#64) 6 ∗
      ((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
      ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ d0) ∗
      ((s0.sp - 448#64) ↦₆₄ d1) ∗ ((s0.sp - 440#64) ↦₆₄ d2) ∗
      ((s0.sp - 432#64) ↦₆₄ a0) ∗ ((s0.sp - 424#64) ↦₆₄ a1) ∗
      ((s0.sp - 416#64) ↦₆₄ a2) ∗ ((s0.sp - 408#64) ↦₆₄ a3) ∗
      ((s0.sp - 400#64) ↦₆₄ a4) ∗ ((s0.sp - 392#64) ↦₆₄ a5) ∗
      memRegion (s0.sp - 384#64) 80 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1200#64) 720 ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 3#64) ∗
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
      ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
      ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2) ∗
      ((stA + 480#64) ↦₆₄ d0) ∗ ((stA + 488#64) ↦₆₄ d1) ∗ ((stA + 496#64) ↦₆₄ d2) ∗
      ((stA + 504#64) ↦₆₄ s.uc.epoch) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A.repAlloc k0 k1 k2 s.uc.ek ∗
      vecU8Heap A.repAlloc d0 d1 d2 s.uc.dk ∗
      memRegion (stA + 512#64) 416 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTablePlacedAt)
    (by sep_ac_rfl)
    (fun sf evs e0 e1 e2 e3 e4 e5 e6 hpcf hrunf hspf hcsf _hacp htrf henv => ?_)
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_2
  have hx21_f : sf.readReg64 .x21 = s.uc.epoch := hcsf.2.2.1.trans hx21_2
  have hx27_f : sf.readReg64 .x27 = s0.sp - 1360#64 := hcsf.2.2.2.2.2.2.2.2.1.trans hx27_2
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpost_step := states_into_pb_keysSampled_post_vm_placed (ext := ext)
    A lim (M.stepEvents evs st) F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 k0 k1 k2 d0 d1 d2 e0 e1 e2 e3 e4 e5 e6
    hsp0_align hpcf hrunf hspf hx29_f hx27_f hx21_f hx19_f htrf
  refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq ?_) hpost_step)
    (fun sr Pr _ _ ⟨hPr, hspr, hcsr, htrr⟩ =>
      ⟨⟨evs, hEnv evs henv, hPr⟩, hspr, hcsr, htrr⟩)
  try simp only [arm64_norm]
  try sep_ac_rfl

theorem states_into_pb_keysSampled_of_env_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (_hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : KeysSampled spqrPolyApi (spqrAuthApi F))
    (hEnv : ∀ evs, KeysSampledEnv s evs → Env evs) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpecOfEnv M A lim F (.keysSampled s) Env)) :=
  states_into_pb_keysSampled_of_env_cl_placed henc_cl s hEnv

/-- Tight `KeysSampledEnv` `withLsCodeLoaded` relocatable `subroutine_ok` for Arm 1
    (`States.keysSampled`) taking `withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)`. -/
theorem states_into_pb_keysSampled_env_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbKeysSampledPlacedSpec M A lim F s)) :=
  states_into_pb_keysSampled_of_env_cl_placed henc_cl s (fun _ h => h)

/-- Complete `withLsCodeLoaded` budget-threaded relocatable proof of `<States>::into_pb`
    (Block `334`) on `.keysSampled s` (Arm 1, tag `3`). -/
theorem states_into_pb_keysSampled_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbKeysSampledPlacedSpec M A lim F s)) :=
  states_into_pb_keysSampled_env_cl_placed henc_cl s

theorem states_into_pb_keysSampled_env_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (_hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbKeysSampledPlacedSpec M A lim F s)) :=
  states_into_pb_keysSampled_env_cl_placed henc_cl s

/-- Default `statesIntoPbVariantPlacedSpec` (`SpqrBoundedEvs 64 (2 * |encodeRaw| + 1024)`)
    `withLsCodeLoaded` relocatable `subroutine_ok` for Arm 1 (`States.keysSampled`) taking
    `withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)` under explicit slot size bounds. -/
theorem states_into_pb_keysSampled_of_bounds_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : KeysSampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + (encoderIntoPbVecs s.sending_hdr).length ≤ 64)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_hdr,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.keysSampled (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F (.keysSampled s))) :=
  states_into_pb_keysSampled_of_env_cl_placed henc_cl s
    (fun _ => keysSampledEnv_imp_spqrBoundedEvs hcnt (by omega) hslots)

theorem states_into_pb_keysSampled_of_bounds_of_alloc_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (_hA : StatesIntoPbAllocPlacedBudget M A lim ext)
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)))
    (s : KeysSampled spqrPolyApi (spqrAuthApi F))
    (hcnt : 2 + (encoderIntoPbVecs s.sending_hdr).length ≤ 64)
    (hslots : ∀ cs ∈ encoderIntoPbVecs s.sending_hdr,
      2 * cs.length ≤ MallocngMaxAllocSize ∧
      2 * cs.length ≤
        2 * (V1State.encodeRaw (States.keysSampled (P := spqrPolyApi) s).into_pb).length + 1024) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl
        (statesIntoPbVariantPlacedSpec M A lim F (.keysSampled s))) :=
  states_into_pb_keysSampled_of_bounds_cl_placed henc_cl s hcnt hslots

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3ClPlacedBudget
