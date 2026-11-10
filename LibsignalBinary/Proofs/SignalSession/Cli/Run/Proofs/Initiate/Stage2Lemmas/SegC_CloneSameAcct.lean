/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Stage 2 `pqspkB` Clone and `is_same_account` Check (`0x0650 → 0x068c`)

Verifies Step C2 (`segC_step2_clone`: 1568-byte `pqspkB` allocation and `memcpy`, with OOM exit via
`alloc::raw_vec::handle_error`) and Step C3 (`segC_step3_sameAcct`: `<IdentityKey>::is_same_account`
returning `false` under `InitOk₀.distinctAcct`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm ↓, local wp_norm ↓]
  CliStage2Norm.sp_setPC_pre CliStage2Norm.sp_setMem_setPC_pre CliStage2Norm.sp_writeVReg128_pre
  CliStage2Norm.fs_setPC_pre CliStage2Norm.fs_setMem_pre CliStage2Norm.fs_setPState_pre
  CliStage2Norm.fs_writeReg64_pre CliStage2Norm.fs_writeReg32_pre CliStage2Norm.fs_writeReg_pre
  CliStage2Norm.fs_writeVReg128_pre
  CliStage2Norm.trace_writeVReg128_pre CliStage2Norm.trace_writeReg32_pre
  CliStage2Norm.trace_writeReg_pre
  CliStage2Norm.readReg64_setPC_pre CliStage2Norm.readReg64_setMem_setPC_pre
  CliStage2Norm.readReg64_writeVReg128_pre
  CliStage2Norm.readReg32_setPC_pre CliStage2Norm.readReg32_setMem_setPC_pre
  CliStage2Norm.readReg32_writeVReg128_pre
  CliStage2Norm.readReg_setPC_pre CliStage2Norm.readReg_setMem_setPC_pre
  CliStage2Norm.readReg_writeVReg128_pre
  CliStage2Norm.readVReg128_setPC_pre CliStage2Norm.readVReg128_setMem_setPC_pre
  CliStage2Norm.readVReg128_setMem_pre CliStage2Norm.readVReg128_setPState_pre
  CliStage2Norm.readVReg128_writeReg64_pre CliStage2Norm.readVReg128_writeReg32_pre
  CliStage2Norm.readVReg128_writeReg_pre
  CliStage2Norm.extractLsb_append_lo CliStage2Norm.extractLsb_append_hi
  CliStage2Norm.extractLsb_pack32_0 CliStage2Norm.extractLsb_pack32_8
  CliStage2Norm.extractLsb_pack32_16 CliStage2Norm.extractLsb_pack32_24
  CliStage2Norm.extractLsb_pack32_0_16 CliStage2Norm.extractLsb_pack32_16_16
  symtab_setPC_pre symtab_setMem_pre symtab_setPState_pre
  symtab_writeReg64_pre symtab_writeReg32_pre symtab_writeReg_pre symtab_writeVReg128_pre

theorem mr_280_staging_split (sp : BitVec 64) :
    memRegion (sp + 840#64) 280 =
      memRegion (sp + 840#64) 32 ∗
      memRegion (sp + 872#64) 32 ∗
      memRegion (sp + 904#64) 32 ∗
      memRegion (sp + 936#64) 32 ∗
      memRegion (sp + 968#64) 32 ∗
      memRegion (sp + 1000#64) 32 ∗
      memRegion (sp + 1032#64) 32 ∗
      memRegion (sp + 1064#64) 8 ∗
      memRegion (sp + 1072#64) 8 ∗
      memRegion (sp + 1080#64) 1 ∗
      memRegion (sp + 1081#64) 32 ∗
      memRegion (sp + 1113#64) 1 ∗
      memRegion (sp + 1114#64) 6 := by
  rw [mr_split (sp + 840#64) (sp + 872#64) 32 248 280 rfl (by bv_omega),
      mr_split (sp + 872#64) (sp + 904#64) 32 216 248 rfl (by bv_omega),
      mr_split (sp + 904#64) (sp + 936#64) 32 184 216 rfl (by bv_omega),
      mr_split (sp + 936#64) (sp + 968#64) 32 152 184 rfl (by bv_omega),
      mr_split (sp + 968#64) (sp + 1000#64) 32 120 152 rfl (by bv_omega),
      mr_split (sp + 1000#64) (sp + 1032#64) 32 88 120 rfl (by bv_omega),
      mr_split (sp + 1032#64) (sp + 1064#64) 32 56 88 rfl (by bv_omega),
      mr_split (sp + 1064#64) (sp + 1072#64) 8 48 56 rfl (by bv_omega),
      mr_split (sp + 1072#64) (sp + 1080#64) 8 40 48 rfl (by bv_omega),
      mr_split (sp + 1080#64) (sp + 1081#64) 1 39 40 rfl (by bv_omega),
      mr_split (sp + 1081#64) (sp + 1113#64) 32 7 39 rfl (by bv_omega),
      mr_split (sp + 1113#64) (sp + 1114#64) 1 6 7 rfl (by bv_omega)]

set_option maxHeartbeats 1600000 in
/-- Stage 2 Step C2 (`+1616 → +1664` and OOM branch `+6436..+6444`, `initProgExt`): allocates
1568 bytes for `pqspkB` and copies `x.bundle.kpk` via `memcpy`. -/
theorem segC_step2_clone_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x0650)
    (htrace : s.trace = s0.trace)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hx20 : s.readReg64 (.gpr 20#5) = x.kpkPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (pqspkPtr : BitVec 64),
      InInitiateExt img ext s0 sf 0x0680 →
      sf.trace = s0.trace →
      pqspkPtr ≠ 0#64 →
      sf.readReg64 .x2 = x.bundleA + 120#64 →
      sf.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 25#5) = 1568#64 →
      sf.readReg64 (.gpr 26#5) = pqspkPtr →
      sf.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (A.pool ∗ A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ x.bundle.kpk) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
          (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (A.pool ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  apply sepWPp_of_sepWP_fs hh.fs
    (mid := (initProgExt img ext).fnAddr shimName)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 1616 4
    have hpc0 : s.pc = (initProgExt img ext).fnAddr cliInitiateName + 1616#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    have hcall_eq := shim_fnAddr_eq img.base (cliExternsWith ext)
    have hent : initEntryExt img ext =
        (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
    have hprog : initProgExt img ext =
        libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc0 hcall_eq ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog] at hcall_eq ⊢
    refine sepWPp_call_cli hh.fs
      (hh.alloc.shim (stk - cliInitiateFrame) (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64))
      (x := ())
      (F := A.pool ∗ ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F)
      (ret_pc := initPcExt img ext 0x0654)
      (by simp only [arm64_norm, hcall_eq]; try bv_omega)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (by simp only [arm64_norm, initPcExt, hent]; try bv_omega)
      (by
        have hinv1 : ImgCallInv img _ :=
          imgCallInv_of_keepsFrozen hctrl.inv hkf1 (by simp only [arm64_norm])
        dsimp only [Spec.inImage, withStack, sessionShimSpec]
        simp only [sepConj_assoc]
        refine Entails.pure_right ⟨hinv1.1, hinv1.2⟩ ?_
        try simp only [arm64_norm, emp_sepConj]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
      (fun _ _ => rfl)
      (fun _ => by dsimp only [Spec.inImage, withStack, sessionShimSpec]; exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
    dsimp only [Spec.inImage, withStack, sessionShimSpec]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; intro htr2
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiateExt img ext s0 s2 0x0654 :=
      inInitiateExt_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 hsym2 (hf2 htr2)
    rcases hcs2 with ⟨_, hx20_2, _, hx22_2, hx23_2, _, hx25_2, _, hx27_2, _, _, _⟩
    simp only [arm64_norm, hx20, hx22, hx23, hx25, hx27] at hx20_2 hx22_2 hx23_2 hx25_2 hx27_2
    rw [stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
    apply sepWPp_of_sepWP_fs hh.fs
      (mid := (initProgExt img ext).fnAddr allocName)
    · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
        (Rust.withPanics (cliExternsWith ext)) hfn
        (num% (ls_off% "libsignal_cli_handshake::initiate")) 1620 12
      have hpc2' : s2.pc = (initProgExt img ext).fnAddr cliInitiateName + 1620#64 := hpc2
      have hcall_alloc := alloc_fnAddr_eq img.base (cliExternsWith ext)
      have hent2 : initEntryExt img ext =
          (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
      have hprog2 : initProgExt img ext =
          libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
      dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc2' hcall_alloc ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase2
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))) = prog2
        reverting [Program.fetch, Program.externAt?, Program.rebase]
      examples_hide_fetches
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine ⟨by simp only [arm64_norm], fun hkf3 hfiles3 => ?_⟩
      rw [← hprog2] at hcall_alloc ⊢
      refine sepWPp_call_cli hh.fs
        hh.alloc.alloc
        (x := (1568, 1))
        (F := memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - extHookStack) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
          (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F)
        (ret_pc := initPcExt img ext 0x0660)
        (by simp only [arm64_norm, hcall_alloc]; try bv_omega)
        (by simp only [arm64_norm, *])
        (by simpa only [arm64_norm, hsp2] using hsp_al)
        (by simp only [arm64_norm, initPcExt, hent2]; try bv_omega)
        (by
          have hinv3 : ImgCallInv img _ :=
            imgCallInv_of_keepsFrozen hctrl2.inv hkf3 (by simp only [arm64_norm])
          dsimp only [Spec.inImage, rustAllocSpecWithStack]
          simp only [sepConj_assoc]
          refine Entails.pure_right ⟨hinv3.1, hinv3.2⟩ ?_
          refine Entails.pure_right ⟨by simp only [arm64_norm],
            by simp only [arm64_norm], layoutOk_1568_1⟩ ?_
          try simp only [arm64_norm, hsp2]
          sep_frame)
        (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
        (fun _ _ => rfl)
        (fun _ => by dsimp only [Spec.inImage, rustAllocSpecWithStack]; exact Entails.pure_left False.elim)
        fun s4 hpc4 hrun4 hsp4 hcs4 hkf4 hsym4 hf4 => ?_
      dsimp only [Spec.inImage, rustAllocSpecWithStack]
      simp only [arm64_norm, hsp2] at hsp4 ⊢
      obtain ⟨_, hx20_4, _, hx22_4, hx23_4, _, hx25_4, _, hx27_4, _, _, _⟩ := id hcs4
      simp only [arm64_norm, hx20_2, hx22_2, hx23_2, hx25_2, hx27_2]
        at hx20_4 hx22_4 hx23_4 hx25_4 hx27_4
      by_cases hnull : s4.readReg64 (.gpr 0#5) = 0#64
      · -- Null allocation (`CBZ X0` → `handle_error` panic)
        simp only [hnull]
        apply sepWPp_weaken_pre (P' :=
          ⌜s4.trace = s2.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt s.sp extHookStack ∗
              memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                (stk - cliInitiateFrame - extHookStack) ∗
              ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
              (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F))
          (Entails.of_eq (by simp only [arm64_norm]; try ac_rfl))
        apply sepWPp_pure_left; intro htr4
        have hfail4 : allocFailedIn s0 s4 := by
          rw [allocFailedIn, htr4, htr2_eq]
          simp
        apply sepWPp_of_sepWP_fs hh.fs
          (mid := (initProgExt img ext).fnAddr handleErrorName)
        · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
            (Rust.withPanics (cliExternsWith ext)) hfn
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 1632 4
          code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
            (Rust.withPanics (cliExternsWith ext)) hfn
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 6436 12
          have hpc4' : s4.pc = (initProgExt img ext).fnAddr cliInitiateName + 1632#64 := hpc4
          have hcall_he := handleError_fnAddr_eq img.base (cliExternsWith ext)
          have hprog3 : initProgExt img ext =
              libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
          dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc4' hcall_he ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase3
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))) = prog3
            reverting [Program.fetch, Program.externAt?, Program.rebase]
          examples_hide_fetches
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
          refine ⟨by simp only [arm64_norm], fun _ _ => ?_⟩
          rw [← hprog3] at hcall_he ⊢
          apply sepWPp_panic_handleError_ext
            (by simp only [arm64_norm, hcall_he]; try bv_omega)
            (by simp only [arm64_norm, *])
          apply hpanic
          apply initPanicPost_of_panicked A img S x stk
          simpa only [allocFailedIn, arm64_norm] using hfail4
      · -- Non-null allocation (`memcpy` → `0x0680`)
        set pqspkPtr := s4.readReg64 (.gpr 0#5)
        have hnull0 : pqspkPtr ≠ 0 := hnull
        simp only [hnull0, ↓reduceIte]
        apply sepWPp_weaken_pre (P' :=
          ⌜pqspkPtr.toNat % 1 = 0 ∧ s4.trace = s2.trace⌝ ∗
            (A.pool ∗ A.live pqspkPtr 1568 1 ∗ memRegion pqspkPtr 1568 ∗
              (memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
                (stk - cliInitiateFrame - extHookStack) ∗ stackAt s.sp extHookStack) ∗
              ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
              (x.kpkPtr ↦ₛ x.bundle.kpk) ∗ F))
          (Entails.of_eq (by simp only [arm64_norm, sepConj_assoc]; try ac_rfl))
        apply sepWPp_pure_left; rintro ⟨_, htr4⟩
        rw [← stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
        have htr4_eq : s4.trace = s0.trace := by simpa only [arm64_norm, htr2_eq] using htr4
        have hctrl4 : InInitiateExt img ext s0 s4 0x0660 :=
          inInitiateExt_after_call hctrl2
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [calleeSavedVRegs, arm64_norm]) hkf3 hfiles3
            hpc4 hrun4 (by simp only [arm64_norm, *]) hcs4 hkf4 hsym4 (hf4 htr4)
        have hnull_beq : (pqspkPtr == 0#64) = false := beq_false_of_ne hnull
        have hnull_dec : decide (pqspkPtr = 0#64) = false := decide_eq_false hnull
        apply sepWPp_of_sepWP_fs hh.fs
          (mid := (initProgExt img ext).fnAddr memcpyName)
        · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
            (Rust.withPanics (cliExternsWith ext)) hfn
            (num% (ls_off% "libsignal_cli_handshake::initiate")) 1632 20
          have hpc4' : s4.pc = (initProgExt img ext).fnAddr cliInitiateName + 1632#64 := hpc4
          have hcall_mc := memcpy_fnAddr_eq img.base (cliExternsWith ext)
          have hent3 : initEntryExt img ext =
              (libsignalSessionCode.rebase img.base
                (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
          have hprog3 : initProgExt img ext =
              libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
          dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc4' hcall_mc ⊢
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase3
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))) = prog3
            reverting [Program.fetch, Program.externAt?, Program.rebase]
          examples_hide_fetches
          wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
          refine ⟨by simp only [arm64_norm], fun hkf5 hfiles5 => ?_⟩
          rw [← hprog3] at hcall_mc ⊢
          refine sepWPp_call_cli hh.fs
            (hh.alloc.session_memcpy_region (stk - cliInitiateFrame)
              (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64))
            (x := (pqspkPtr, x.kpkPtr, x.bundle.kpk))
            (F := A.pool ∗ A.live pqspkPtr 1568 1 ∗
              ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗ F)
            (ret_pc := initPcExt img ext 0x0674)
            (by simp only [arm64_norm, hcall_mc]; try bv_omega)
            (by simp only [arm64_norm, *])
            (by simpa only [arm64_norm, hsp4] using hsp_al)
            (by simp only [arm64_norm, initPcExt, hent3]; try bv_omega)
            (by
              have hinv5 : ImgCallInv img _ :=
                imgCallInv_of_keepsFrozen hctrl4.inv hkf5 (by simp only [arm64_norm])
              dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
              simp only [hkpkLen, sepConj_assoc]
              refine Entails.pure_right ⟨hinv5.1, hinv5.2⟩ ?_
              refine Entails.pure_right ⟨by simp only [arm64_norm]; try rfl,
                by simp only [arm64_norm], by simp only [arm64_norm]⟩ ?_
              try simp only [arm64_norm, hsp4]
              sep_frame)
            (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
            (fun _ _ => rfl)
            (fun _ => by
              dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
              exact Entails.pure_left False.elim)
            fun s6 hpc6 hrun6 hsp6 hcs6 hkf6 hsym6 hf6 => ?_
          dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec]
          simp only [arm64_norm, hsp4, sepConj_assoc] at hsp6 ⊢
          apply sepWPp_pure_left; rintro ⟨_, htr6⟩
          have htr6_eq : s6.trace = s0.trace := by simpa only [arm64_norm, htr4_eq] using htr6
          have hctrl6 : InInitiateExt img ext s0 s6 0x0674 :=
            inInitiateExt_after_call hctrl4
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [calleeSavedVRegs, arm64_norm]) hkf5 hfiles5
              hpc6 hrun6 (by simp only [arm64_norm, *]) hcs6 hkf6 hsym6 (hf6 htr6)
          rcases hcs6 with ⟨_, _, _, hx22_6, hx23_6, _, hx25_6, hx26_6, hx27_6, _, _, _⟩
          simp only [arm64_norm, hx22_4, hx23_4, hx25_4, hx27_4]
            at hx22_6 hx23_6 hx25_6 hx26_6 hx27_6
          apply sepWPp_of_sepWP_fs hh.fs
            (mid := initPcExt img ext 0x0680)
          · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
              (Rust.withPanics (cliExternsWith ext)) hfn
              (num% (ls_off% "libsignal_cli_handshake::initiate")) 1652 8
            have hpc6' : s6.pc = (initProgExt img ext).fnAddr cliInitiateName + 1652#64 := hpc6
            have hent4 : initEntryExt img ext =
                (libsignalSessionCode.rebase img.base
                  (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
            have hprog4 : initProgExt img ext =
                libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
            dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc6' ⊢
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase4
            generalize_entry (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))) = prog4
              reverting [Program.fetch, Program.externAt?, Program.rebase]
            examples_hide_fetches
            wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
            refine ⟨by simp only [arm64_norm], fun hkf7 hfiles7 => ?_⟩
            rw [← hprog4]
            have hctrl7 : InInitiateExt img ext s0 _ 0x0680 :=
              inInitiateExt_of_step hctrl6 (by simp only [initPcExt, hent4, arm64_norm]; try bv_omega)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, hsp6])
                (by simp only [arm64_norm]) (by simp only [arm64_norm])
                (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm]) hkf7 hfiles7
            refine sepWPp_weaken_pre ?_
              (hnext _ pqspkPtr hctrl7
                (by simpa only [arm64_norm] using htr6_eq)
                hnull
                (by simp only [arm64_norm])
                (by simp only [arm64_norm, hx22_6])
                (by simp only [arm64_norm, hx23_6])
                (by simp only [arm64_norm, hx25_6])
                (by simp only [arm64_norm, hx26_6]; rfl)
                (by simp only [arm64_norm, hx27_6]))
            try simp only [arm64_norm, hsp6, sepConj_assoc]
            sep_frame

/-- Stage 2 Step C2 (`+1616 → +1664` and OOM branch `+6436..+6444`, `initProg`). -/
theorem segC_step2_clone {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hh : RunHooks img A (cliExterns W))
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiate img W s0 s 0x0650)
    (htrace : s.trace = s0.trace)
    (hkpkLen : x.bundle.kpk.length = 1568)
    (hx20 : s.readReg64 (.gpr 20#5) = x.kpkPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (pqspkPtr : BitVec 64),
      InInitiate img W s0 sf 0x0680 →
      sf.trace = s0.trace →
      pqspkPtr ≠ 0#64 →
      sf.readReg64 .x2 = x.bundleA + 120#64 →
      sf.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 25#5) = 1568#64 →
      sf.readReg64 (.gpr 26#5) = pqspkPtr →
      sf.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (A.pool ∗ A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ x.bundle.kpk) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
          (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (A.pool ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        (x.kpkPtr ↦ₛ x.bundle.kpk) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) :=
  segC_step2_clone_ext (ext := cliHookExterns W) hh.toExt hstk hstk64 (InInitiate.toExt hctrl) htrace hkpkLen
    hx20 hx22 hx23 hx25 hx27 hpanic
    (fun sf pqspkPtr hctrl7 => hnext sf pqspkPtr (InInitiateExt.toLegacy hctrl7))

set_option maxHeartbeats 1200000 in
/-- Stage 2 Step C3 (`+1664 → +1676`, `initProgExt`): invokes `is_same_account` and establishes
`w0 = 0` via `InitOk₀.distinctAcct`. -/
theorem segC_step3_sameAcct_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {pqspkPtr : BitVec 64}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hFs : TraceFsSound (initProgExt img ext))
    (hLocal : Stage2CalleesExt img P A ext)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x0680)
    (htrace : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = x.bundleA + 120#64)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx26 : s.readReg64 (.gpr 26#5) = pqspkPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiateExt img ext s0 sf 0x068c →
      sf.trace = s0.trace →
      (sf.readReg64 .x0).setWidth 32 = 0#32 →
      sf.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 25#5) = 1568#64 →
      sf.readReg64 (.gpr 26#5) = pqspkPtr →
      sf.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (initArgsAt img s.sp x s0 ∗
          ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          protocolAddressAt A x.me x.meA ∗
          ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          protocolAddressAt A x.peer x.peerA ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (initArgsAt img s.sp x s0 ∗
        ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        protocolAddressAt A x.peer x.peerA ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  unfold initArgsAt
  apply sepWPp_of_sepWP_fs hFs
    (mid := (initProgExt img ext).fnAddr cliIsSameAccountName)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 1664 12
    have hpc0 : s.pc = initEntryExt img ext + 1664#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    have hcall_isa := isSameAccount_fnAddr_eq img.base (cliExternsWith ext)
    have hent : initEntryExt img ext =
        (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
    have hprog : initProgExt img ext =
        libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc0 hcall_isa ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog] at hcall_isa ⊢
    let isaG : Pqxdh.WireEntries.IsSameAccountDistinctGhost :=
      { localIkA := s.sp + 776#64
        localIk := kp.identityKey
        locA := x.meA
        loc := x.me
        remoteIkA := x.bundleA + 120#64
        remoteIk := x.bundle.idKey
        remA := x.peerA
        rem := x.peer }
    refine sepWPp_call_cli hFs
      (hLocal.isSameAccount_withStack (stk_sub_ge_base hstk) (sub_frame_le_64 hstk64))
      (x := isaG)
      (F := ((s.sp + 0xd0#64) ↦₆₄ x.peerA) ∗ ((s.sp + 0xd8#64) ↦₆₄ x.meA) ∗
        ((s.sp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗ ((s.sp + 0xe8#64) ↦₆₄ sessVt img) ∗
        ((s.sp + 0xf0#64) ↦₆₄ x.stores) ∗ ((s.sp + 0xf8#64) ↦₆₄ idVt img) ∗
        ((s.sp + 0x100#64) ↦₆₄ x.bundleA) ∗ ((s.sp + 0x108#64) ↦₆₄ 0#64) ∗
        ((s.sp + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (s.sp + 0x114#64) 4 ∗
        ((s.sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
        ((s.sp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗ F)
      (ret_pc := initPcExt img ext 0x068c)
      (by simp only [arm64_norm, hcall_isa]; try bv_omega)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (by simp only [arm64_norm, initPcExt, hent]; try bv_omega)
      (by
        have hinv1 : ImgCallInv img _ :=
          imgCallInv_of_keepsFrozen hctrl.inv hkf1 (by simp only [arm64_norm])
        dsimp only [Spec.inImage, isSameAccountDistinctAtSpec, isaG]
        have hdist := distinctSid_of_not_sameServiceId hinitOk.distinctAcct
        simp only [sepConj_assoc]
        refine Entails.pure_right ⟨hinv1.1, hinv1.2⟩ ?_
        refine Entails.pure_right
          ⟨by simp only [arm64_norm]; try bv_omega,
           by simp only [arm64_norm],
           by simp only [arm64_norm, hx2],
           by simp only [arm64_norm],
           Or.inr (fun v h1 h2 => hdist v v h1 h2 rfl)⟩ ?_
        try simp only [arm64_norm]
        sep_frame)
      (fun sf => by
        dsimp only [Spec.inImage, isSameAccountDistinctAtSpec]
        exact hpanic sf _ (initPanicPost_of_false A img S x stk _))
      (fun _ _ => rfl)
      (fun _ => by
        dsimp only [Spec.inImage, isSameAccountDistinctAtSpec]
        exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
    dsimp only [Spec.inImage, isSameAccountDistinctAtSpec, isaG]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; rintro ⟨hw0, htr2⟩
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiateExt img ext s0 s2 0x068c :=
      inInitiateExt_after_call hctrl
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 hsym2 (hf2 htr2)
    rcases hcs2 with ⟨_, _, _, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, _, _, _⟩
    simp only [arm64_norm, hx22, hx23, hx25, hx26, hx27]
      at hx22_2 hx23_2 hx25_2 hx26_2 hx27_2
    refine sepWPp_weaken_pre ?_
      (hnext s2 hctrl2 htr2_eq hw0 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2)
    unfold initArgsAt
    try simp only [arm64_norm, sepConj_assoc]
    sep_frame

/-- Stage 2 Step C3 (`+1664 → +1676`, `initProg`). -/
theorem segC_step3_sameAcct {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {pqspkPtr : BitVec 64}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hLocal : InitLocalCallees img A W stk)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiate img W s0 s 0x0680)
    (htrace : s.trace = s0.trace)
    (hx2 : s.readReg64 .x2 = x.bundleA + 120#64)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx26 : s.readReg64 (.gpr 26#5) = pqspkPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiate img W s0 sf 0x068c →
      sf.trace = s0.trace →
      (sf.readReg64 .x0).setWidth 32 = 0#32 →
      sf.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sf.readReg64 (.gpr 25#5) = 1568#64 →
      sf.readReg64 (.gpr 26#5) = pqspkPtr →
      sf.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (initArgsAt img s.sp x s0 ∗
          ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          protocolAddressAt A x.me x.meA ∗
          ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          protocolAddressAt A x.peer x.peerA ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (initArgsAt img s.sp x s0 ∗
        ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        protocolAddressAt A x.me x.meA ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        protocolAddressAt A x.peer x.peerA ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) :=
  segC_step3_sameAcct_ext (ext := cliHookExterns W) (RunGlue.traceFsSound_cli W img.base)
    (stage2CalleesExt_of_localCallees hLocal) hinitOk hstk hstk64 (InInitiate.toExt hctrl) htrace hx2
    hx22 hx23 hx25 hx26 hx27 hpanic (fun sf hctrl2 => hnext sf (InInitiateExt.toLegacy hctrl2))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
