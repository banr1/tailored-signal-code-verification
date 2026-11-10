/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SpeSplit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 2 `get_identity_key_pair` Future Teardown and Error Branch (`0x0464 → 0x0584`)

Verifies the shared `idKeyPairFut` optional drop + `__rust_dealloc(box, 16, 8)` sequence
(`segA_drop_and_dealloc`) and the `ans = .error ()` branch (`segA_step4_err`) handing off to
`segB_err_ok` at `0x0584`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
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

theorem sepWPp_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P Sub Target Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hfoc : P ⊢ Sub ∗ Rest) (hsub : Sub ⊢ Target)
    (h : SepWPp prog ret s (Target ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  sepWPp_weaken_pre (Entails.trans hfoc (sepConj_mono_left hsub)) h

theorem idOwnFutBox_entails_mr16 (box self : BitVec 64) (st : BitVec 8) :
    idOwnFutBoxAt box self st ⊢ memRegion box 16 := by
  unfold idOwnFutBoxAt
  refine mr_fold box (box + 8#64) 8 8 16 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
  exact mr_fold (box + 8#64) (box + 9#64) 1 7 8 (mr_of_u8 _ _) (Entails.refl _) rfl (by bv_omega)

set_option maxHeartbeats 1200000 in
/-- Optional future drop and 16-byte future box deallocation (`+1380 → +1412`, `0x0584`) on
`initProgExt img ext`. -/
theorem segA_drop_and_dealloc_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {box : BitVec 64}
    {v22 v26 v27 v25 v28 v24 v21 : BitVec 64}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x0564)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = (initProgExt img ext).fnAddr KitInst.cliIdFutDropName)
    (hx20 : s.readReg64 (.gpr 20#5) = box)
    (hx23 : s.readReg64 (.gpr 23#5) = img.base + idKeyPairFutVtOff)
    (hx22 : s.readReg64 (.gpr 22#5) = v22)
    (hx26 : s.readReg64 (.gpr 26#5) = v26)
    (hx27 : s.readReg64 (.gpr 27#5) = v27)
    (hx25 : s.readReg64 (.gpr 25#5) = v25)
    (hx28 : s.readReg64 (.gpr 28#5) = v28)
    (hx24 : s.readReg64 (.gpr 24#5) = v24)
    (hx21 : s.readReg64 (.gpr 21#5) = v21)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiateExt img ext s0 sf 0x0584 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 22#5) = v22 →
      sf.readReg64 (.gpr 26#5) = v26 →
      sf.readReg64 (.gpr 27#5) = v27 →
      sf.readReg64 (.gpr 25#5) = v25 →
      sf.readReg64 (.gpr 28#5) = v28 →
      sf.readReg64 (.gpr 24#5) = v24 →
      sf.readReg64 (.gpr 21#5) = v21 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (A.pool ∗ stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  suffices h0570 : ∀ sd : State,
      InInitiateExt img ext s0 sd 0x0570 →
      sd.trace = s0.trace →
      sd.sp = s.sp →
      sd.readReg64 (.gpr 20#5) = box →
      sd.readReg64 (.gpr 23#5) = img.base + idKeyPairFutVtOff →
      sd.readReg64 (.gpr 22#5) = v22 →
      sd.readReg64 (.gpr 26#5) = v26 →
      sd.readReg64 (.gpr 27#5) = v27 →
      sd.readReg64 (.gpr 25#5) = v25 →
      sd.readReg64 (.gpr 28#5) = v28 →
      sd.readReg64 (.gpr 24#5) = v24 →
      sd.readReg64 (.gpr 21#5) = v21 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sd
        (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0) by
    by_cases hz : (initProgExt img ext).fnAddr KitInst.cliIdFutDropName = 0#64
    · -- Null drop slot (`CBZ X8` taken)
      apply sepWPp_of_sepWP_fs hh.fs (mid := initPcExt img ext 0x0570)
      · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
          (Rust.withPanics (cliExternsWith ext)) hfn
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 1380 4
        have hpc0 : s.pc = initEntryExt img ext + 1380#64 := hctrl.pc
        have hrun0 : s.status = .Running := hctrl.run
        have hx8z : s.readReg64 .x8 = 0#64 := hx8.trans hz
        clear hx8 hz
        have hent : initEntryExt img ext =
            (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
        have hprog : initProgExt img ext =
            libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
        dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt, initPcExt] at hpc0 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))) = prog
          reverting [Program.fetch, Program.externAt?, Program.rebase]
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
        rw [← hprog]
        exact h0570 _
          (inInitiateExt_of_step hctrl (by simp only [initPcExt, hent, arm64_norm]; try bv_omega)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1)
          (by simpa only [arm64_norm] using htrace)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm, hx20])
          (by simp only [arm64_norm, hx23])
          (by simp only [arm64_norm, hx22])
          (by simp only [arm64_norm, hx26])
          (by simp only [arm64_norm, hx27])
          (by simp only [arm64_norm, hx25])
          (by simp only [arm64_norm, hx28])
          (by simp only [arm64_norm, hx24])
          (by simp only [arm64_norm, hx21])
    · -- Non-null drop function (`BLR futDrop`)
      apply sepWPp_of_sepWP_fs hh.fs
        (mid := (initProgExt img ext).fnAddr KitInst.cliIdFutDropName)
      · generalize hdrop : (initProgExt img ext).fnAddr KitInst.cliIdFutDropName = dropAddr at hx8 hz ⊢
        have hz_beq : (dropAddr == 0#64) = false := beq_false_of_ne hz
        have hz_dec : decide (dropAddr = 0#64) = false := decide_eq_false hz
        code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
          (Rust.withPanics (cliExternsWith ext)) hfn
          (num% (ls_off% "libsignal_cli_handshake::initiate")) 1380 12
        have hpc0 : s.pc = initEntryExt img ext + 1380#64 := hctrl.pc
        have hrun0 : s.status = .Running := hctrl.run
        have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
        have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
        have hent : initEntryExt img ext =
            (libsignalSessionCode.rebase img.base
              (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
        have hprog : initProgExt img ext =
            libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
        dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc0 ⊢
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))) = prog
          reverting [Program.fetch, Program.externAt?, Program.rebase]
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
        rw [← hprog]
        refine sepWPp_call_cli hh.fs
          hStore.futDrop
          (x := ())
          (F := A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
            stackAt s.sp (stk - cliInitiateFrame) ∗ F)
          (ret_pc := initPcExt img ext 0x0570)
          (by simp only [arm64_norm, hdrop])
          (by simp only [arm64_norm, *])
          (by simpa only [arm64_norm] using hsp_al)
          (by simp only [arm64_norm, initPcExt, hent]; try bv_omega)
          (by dsimp only [futDropSpec]; rw [emp_sepConj]; exact Entails.refl _)
          (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
          (fun _ _ => rfl)
          (fun _ => by dsimp only [futDropSpec]; exact Entails.pure_left False.elim)
          fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
        dsimp only [futDropSpec]
        simp only [arm64_norm] at hsp2 ⊢
        apply sepWPp_pure_left; intro htr2
        have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
        have hctrl2 : InInitiateExt img ext s0 s2 0x0570 :=
          inInitiateExt_after_call hctrl
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
            hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 hsym2 (hf2 htr2)
        rcases hcs2 with
          ⟨_, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, _⟩
        simp only [arm64_norm, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28]
          at hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
        exact h0570 s2 hctrl2 htr2_eq hsp2 hx20_2 hx23_2 hx22_2 hx26_2 hx27_2 hx25_2 hx28_2
          hx24_2 hx21_2
  intro sd hctrld htrd hspd hx20d hx23d hx22d hx26d hx27d hx25d hx28d hx24d hx21d
  have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
  apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutSize himg hctrld.inv.1)
  apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutAlign himg hctrld.inv.1)
  rw [stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
  apply sepWPp_weaken_pre (P' :=
    ((img.base + idKeyPairFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((img.base + idKeyPairFutVtOff + 8#64) ↦₆₄ᵣ 16#64) ∗
      A.pool ∗ A.live box 16 8 ∗ memRegion box 16 ∗
      stackAt s.sp extHookStack ∗
      memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ∗ F) (by
    have hboxMr := idOwnFutBox_entails_mr16 box x.stores 1#8
    simp only [sepConj_assoc]
    refine entails_by_focus (by sep_frame) hboxMr ?_
    sep_frame)
  apply sepWPp_of_sepWP_fs hh.fs
    (mid := (initProgExt img ext).fnAddr deallocName)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 1392 20
    have hpcd : sd.pc = initEntryExt img ext + 1392#64 := hctrld.pc
    have hrund : sd.status = .Running := hctrld.run
    have hcall_da := dealloc_fnAddr_eq img.base (cliExternsWith ext)
    have hent : initEntryExt img ext =
        (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
    have hprog : initProgExt img ext =
        libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpcd hcall_da ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    try simp only [sepConj_assoc]
    apply sepWP_drop_left
    apply sepWP_drop_left
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog] at hcall_da ⊢
    refine sepWPp_call_cli hh.fs
      hh.alloc.dealloc
      (x := (box, 16, 8))
      (F := memRegion (s.sp - BitVec.ofNat 64 (stk - cliInitiateFrame))
        (stk - cliInitiateFrame - extHookStack) ∗ F)
      (ret_pc := initPcExt img ext 0x0584)
      (by simp only [arm64_norm, hcall_da]; try bv_omega)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm, hspd] using hsp_al)
      (by simp only [arm64_norm, initPcExt, hent]; try bv_omega)
      (by
        have hinv1 : ImgCallInv img _ :=
          imgCallInv_of_keepsFrozen hctrld.inv hkf1 (by simp only [arm64_norm])
        dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]
        simp only [sepConj_assoc]
        refine Entails.pure_right ⟨hinv1.1, hinv1.2⟩ ?_
        refine Entails.pure_right
          ⟨by simp only [arm64_norm],
           by simp only [arm64_norm],
           by simp only [arm64_norm],
           layoutOk_16_8⟩ ?_
        simp only [arm64_norm, hspd]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
      (fun _ _ => rfl)
      (fun _ => by dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]; exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
    dsimp only [rustDeallocExternSpecWithStack, Spec.inImage]
    simp only [arm64_norm, hspd, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; intro htr2
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrd] using htr2
    have hctrl2 : InInitiateExt img ext s0 s2 0x0584 :=
      inInitiateExt_after_call hctrld
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, hspd, hsp2]) hcs2 hkf2 hsym2 (hf2 htr2)
    rcases hcs2 with
      ⟨_, _, hx21_2, hx22_2, _, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, _⟩
    simp only [arm64_norm, hx21d, hx22d, hx24d, hx25d, hx26d, hx27d, hx28d]
      at hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
    apply sepWPp_weaken_pre (P' := A.pool ∗ stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      (Entails.of_eq (by
        rw [stackAt_sub_split_need s.sp (extHookStack_le_sub hstk) (sub_frame_le_64 hstk64)]
        ac_rfl))
    exact hnext s2 hctrl2 htr2_eq hx22_2 hx26_2 hx27_2 hx25_2 hx28_2 hx24_2 hx21_2

/-- Optional future drop and 16-byte future box deallocation (`+1380 → +1412`, `0x0584`) on `initProg img W`. -/
theorem segA_drop_and_dealloc {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {box : BitVec 64}
    {v22 v26 v27 v25 v28 v24 v21 : BitVec 64}
    {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiate img W s0 s 0x0564)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = (initProg img W).fnAddr KitInst.cliIdFutDropName)
    (hx20 : s.readReg64 (.gpr 20#5) = box)
    (hx23 : s.readReg64 (.gpr 23#5) = img.base + idKeyPairFutVtOff)
    (hx22 : s.readReg64 (.gpr 22#5) = v22)
    (hx26 : s.readReg64 (.gpr 26#5) = v26)
    (hx27 : s.readReg64 (.gpr 27#5) = v27)
    (hx25 : s.readReg64 (.gpr 25#5) = v25)
    (hx28 : s.readReg64 (.gpr 28#5) = v28)
    (hx24 : s.readReg64 (.gpr 24#5) = v24)
    (hx21 : s.readReg64 (.gpr 21#5) = v21)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiate img W s0 sf 0x0584 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 22#5) = v22 →
      sf.readReg64 (.gpr 26#5) = v26 →
      sf.readReg64 (.gpr 27#5) = v27 →
      sf.readReg64 (.gpr 25#5) = v25 →
      sf.readReg64 (.gpr 28#5) = v28 →
      sf.readReg64 (.gpr 24#5) = v24 →
      sf.readReg64 (.gpr 21#5) = v21 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (A.pool ∗ stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) :=
  segA_drop_and_dealloc_ext (ext := cliHookExterns W) himg hh.toExt
    { futDrop := hStore.futDrop
      idTrustShim := hStore.idTrustShim
      idTrustPoll := hStore.idTrustPoll
      sessLoadShim := hStore.sessLoadShim
      sessLoadPoll := hStore.sessLoadPoll
      idKeyPairShim := hStore.idKeyPairShim
      idKeyPairPoll := hStore.idKeyPairPoll
      idRegIdShim := hStore.idRegIdShim
      idRegIdPoll := hStore.idRegIdPoll
      idSaveShim := hStore.idSaveShim
      idSavePoll := hStore.idSavePoll
      sessStoreShim := hStore.sessStoreShim
      sessStorePoll := hStore.sessStorePoll }
    hstk hstk64 (InInitiate.toExt hctrl) htrace hx8 hx20 hx23 hx22 hx26 hx27 hx25 hx28 hx24 hx21 hpanic
    (fun sf hctrlf => hnext sf (InInitiateExt.toLegacy hctrlf))

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 400000 in
/-- Stage 2 `get_identity_key_pair` error branch (`+1124 → +1412` on `ans = .error ()`,
`initProgExt`): moves the 6 `SpeOwned` words into `(X26, X27, X25, X28, X24, X21)`, drops and frees
`box`, and hands off to `segB_err_ext_ok`. -/
theorem segA_step4_err_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {box : BitVec 64} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x0464)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 4064#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (k : RunDrop.SpeOwned) (w0 w1 w2 w3 w4 w5 : BitVec 64)
        (R_spe : SepProp),
      InInitiateExt img ext s0 sf 0x0584 →
      sf.trace = s0.trace →
      w0 ≠ 0#64 - 3#64 →
      (((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        RunDrop.speOwnedAt A x.ret k) →
      sf.readReg64 (.gpr 22#5) = 1#64 →
      sf.readReg64 (.gpr 26#5) = w0 →
      sf.readReg64 (.gpr 27#5) = w1 →
      sf.readReg64 (.gpr 25#5) = w2 →
      sf.readReg64 (.gpr 28#5) = w3 →
      sf.readReg64 (.gpr 24#5) = w4 →
      sf.readReg64 (.gpr 21#5) = w5 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (A.pool ∗ R_spe ∗
          memRegion (s.sp + 120#64) 8 ∗
          memRegion (s.sp + 1472#64) 16 ∗
          memRegion (s.sp + 1864#64) 24 ∗
          memRegion (s.sp + 5632#64) 72 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        memRegion (s.sp + 120#64) 8 ∗
        ((s.sp + 1472#64) ↦₆₄ box) ∗
        ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗
        memRegion (s.sp + 1864#64) 24 ∗
        idKeyPairOutAt A (s.sp + 5632#64) (.error ()) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutDrop_ext ext himg hctrl.inv.1)
  unfold idKeyPairOutAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply sepWPp_exists_left; intro k
  rw [mr_split (s.sp + 1864#64) (s.sp + 1872#64) 8 16 24 rfl (by bv_omega),
      mr_split (s.sp + 1872#64) (s.sp + 1880#64) 8 8 16 rfl (by bv_omega),
      mr_split (s.sp + 1872#64) (s.sp + 1873#64) 1 7 8 rfl (by bv_omega),
      mr_split (s.sp + 1880#64) (s.sp + 1887#64) 7 1 8 rfl (by bv_omega),
      mr_split (s.sp + 5688#64) (s.sp + 5696#64) 8 8 16 rfl (by bv_omega),
      mr_split (s.sp + 5696#64) (s.sp + 5697#64) 1 7 8 rfl (by bv_omega),
      memRegion_8_eq_exists (s.sp + 120#64),
      memRegion_8_eq_exists (s.sp + 1864#64),
      memRegion_1_eq_exists (s.sp + 1872#64),
      memRegion_8_eq_exists (s.sp + 5688#64),
      memRegion_1_eq_exists (s.sp + 5696#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply sepWPp_exists_left; intro c96
  apply sepWPp_exists_left; intro c88
  apply sepWPp_exists_left; intro c72
  apply sepWPp_exists_left; intro c64
  apply sepWPp_exists_left; intro c120
  refine sepWPp_focus (by sep_frame) (sevenHi_of_memRegion7 (s.sp + 1880#64)) ?_
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_exists_left; intro c6
  apply sepWPp_exists_left; intro c5
  apply sepWPp_exists_left; intro c4
  apply sepWPp_exists_left; intro c3
  apply sepWPp_exists_left; intro c2
  apply sepWPp_exists_left; intro c1
  apply sepWPp_exists_left; intro c0
  refine sepWPp_focus (by sep_frame) (sevenHi_of_memRegion7 (s.sp + 5633#64)) ?_
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_exists_left; intro d6
  apply sepWPp_exists_left; intro d5
  apply sepWPp_exists_left; intro d4
  apply sepWPp_exists_left; intro d3
  apply sepWPp_exists_left; intro d2
  apply sepWPp_exists_left; intro d1
  apply sepWPp_exists_left; intro d0
  refine sepWPp_focus (by sep_frame) (speOwnedAt_split_move A (s.sp + 5640#64) x.ret k) ?_
  simp only [sepExists_sepConj_left, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWPp_exists_left; intro w0
  apply sepWPp_exists_left; intro w1
  apply sepWPp_exists_left; intro w2
  apply sepWPp_exists_left; intro w3
  apply sepWPp_exists_left; intro w4
  apply sepWPp_exists_left; intro w5
  apply sepWPp_exists_left; intro R_spe
  apply sepWPp_pure_left; rintro ⟨hw0_ne3, hspe_move⟩
  apply sepWPp_of_sepWP_fs hh.fs (mid := initPcExt img ext 0x0564)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 1124 12
    code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 1296 84
    have hpc0 : s.pc = initEntryExt img ext + 1124#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
      spAligned_mask_of_frame hctrl.sp hctrl.spAligned
    generalize hdrop : (initProgExt img ext).fnAddr KitInst.cliIdFutDropName = dropAddr
    have hent : initEntryExt img ext =
        (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
    have hprog : initProgExt img ext =
        libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt, initPcExt] at hpc0 ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    -- Reassociate `sp + 5633` from `sevenHi` to `sevenLo` for `LDUR W8, [X10, #1]`
    conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 5633#64 5634#64 5635#64 5636#64 5637#64 5638#64 5639#64 d0 d1 d2 d3 d4 d5 d6,
      sepConj_assoc]
    wp_steps
    -- Reassociate `sp + 1880` from `sevenHi` to `sevenLo` for `STR W8, [SP, #1880]`
    conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 c0 c1 c2 c3 c4 c5 c6,
      sepConj_assoc]
    wp_steps
    -- Restore `sp + 1880` to `sevenHi` for `STUR W9, [X8, #3]`
    conv => arg 4; simp only [← sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 d0 d1 d2 d3 c4 c5 c6,
      sepConj_assoc]
    wp_steps
    refine SepWP.weaken_pre (P' :=
      ((img.base + idKeyPairFutVtOff) ↦₆₄ᵣ dropAddr) ∗
        (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗
          R_spe ∗
          memRegion (s.sp + 120#64) 8 ∗
          memRegion (s.sp + 1472#64) 16 ∗
          memRegion (s.sp + 1864#64) 24 ∗
          memRegion (s.sp + 5632#64) 72 ∗ F)) (by
      have hm120 := mr_of_u64 (s.sp + 120#64) (s.sp + 664#64)
      have hm1472 := mr_fold (s.sp + 1472#64) (s.sp + 1480#64) 8 8 16
        (mr_of_u64 _ box) (mr_of_u64 _ (img.base + idKeyPairFutVtOff)) rfl (by bv_omega)
      have hm1864 :
          ((s.sp + 1864#64) ↦₆₄ c88) ∗ (((s.sp + 1872#64) ↦₈ c96) ∗
            (memRegion (s.sp + 1873#64) 7 ∗
              ((((s.sp + 1880#64) ↦₈ d0) ∗ ((s.sp + 1881#64) ↦₈ d1) ∗
                ((s.sp + 1882#64) ↦₈ d2) ∗ ((s.sp + 1883#64) ↦₃₂ (d6 ++ d5 ++ d4 ++ d3))) ∗
                memRegion (s.sp + 1887#64) 1))) ⊢
          memRegion (s.sp + 1864#64) 24 := by
        refine mr_fold (s.sp + 1864#64) (s.sp + 1872#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 1872#64) (s.sp + 1873#64) 1 15 16 (mr_of_u8 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 1873#64) (s.sp + 1880#64) 7 8 15 (Entails.refl _) ?_ rfl (by bv_omega)
        exact mr_fold (s.sp + 1880#64) (s.sp + 1887#64) 7 1 8
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            sevenHi_entails_mr7 (s.sp + 1880#64) d0 d1 d2 (d6 ++ d5 ++ d4 ++ d3))
          (Entails.refl _) rfl (by bv_omega)
      have hm5632 :
          ((s.sp + 5632#64) ↦₈ 1#8) ∗
            ((((s.sp + 5633#64) ↦₃₂ (d3 ++ d2 ++ d1 ++ d0)) ∗ ((s.sp + 5637#64) ↦₈ d4) ∗
              ((s.sp + 5638#64) ↦₈ d5) ∗ ((s.sp + 5639#64) ↦₈ d6)) ∗
              ((((s.sp + 5640#64) ↦₆₄ w0) ∗ ((s.sp + 5648#64) ↦₆₄ w1) ∗
                ((s.sp + 5656#64) ↦₆₄ w2) ∗ ((s.sp + 5664#64) ↦₆₄ w3)) ∗
                (((s.sp + 5672#64) ↦₆₄ w4) ∗ (((s.sp + 5680#64) ↦₆₄ w5) ∗
                  (((s.sp + 5688#64) ↦₆₄ c88) ∗
                    (((s.sp + 5696#64) ↦₈ c96) ∗ memRegion (s.sp + 5697#64) 7)))))) ⊢
          memRegion (s.sp + 5632#64) 72 := by
        refine mr_fold (s.sp + 5632#64) (s.sp + 5633#64) 1 71 72 (mr_of_u8 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 5633#64) (s.sp + 5640#64) 7 64 71
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            sevenLo_entails_mr7 (s.sp + 5633#64) (d3 ++ d2 ++ d1 ++ d0) d4 d5 d6) ?_
          rfl (by bv_omega)
        refine mr_fold (s.sp + 5640#64) (s.sp + 5672#64) 32 32 64
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            words4_entails_mr32 (s.sp + 5640#64) w0 w1 w2 w3) ?_
          rfl (by bv_omega)
        refine mr_fold (s.sp + 5672#64) (s.sp + 5680#64) 8 24 32 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 5680#64) (s.sp + 5688#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 5688#64) (s.sp + 5696#64) 8 8 16 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        exact mr_fold (s.sp + 5696#64) (s.sp + 5697#64) 1 7 8
          (mr_of_u8 _ _) (Entails.refl _) rfl (by bv_omega)
      simp only [sepConj_assoc] at hm120 hm1472 hm1864 hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm120 ?_
      refine entails_by_focus (by sep_frame) hm1472 ?_
      refine entails_by_focus (by sep_frame) hm1864 ?_
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply sepWP_drop_left
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog]
    have hctrl1 : InInitiateExt img ext s0 _ 0x0564 :=
      inInitiateExt_of_step hctrl (by simp only [initPcExt, hent, arm64_norm]; try bv_omega)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
    refine segA_drop_and_dealloc_ext (v22 := 1#64) (v26 := w0) (v27 := w1) (v25 := w2)
      (v28 := w3) (v24 := w4) (v21 := w5) himg hh hStore hstk hstk64 hctrl1
      (by simpa only [arm64_norm] using htrace)
      (by simp only [arm64_norm, hdrop])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      hpanic
      fun sf hctrlf htrf hx22f hx26f hx27f hx25f hx28f hx24f hx21f => ?_
    refine sepWPp_weaken_pre ?_
      (hnext sf k w0 w1 w2 w3 w4 w5 R_spe hctrlf htrf hw0_ne3 hspe_move hx22f hx26f hx27f hx25f
        hx28f hx24f hx21f)
    try simp only [arm64_norm]
    sep_frame

/-- Stage 2 `get_identity_key_pair` error branch (`+1124 → +1412` on `ans = .error ()`, `initProg`). -/
theorem segA_step4_err {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {box : BitVec 64} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiate img W s0 s 0x0464)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 4064#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (k : RunDrop.SpeOwned) (w0 w1 w2 w3 w4 w5 : BitVec 64)
        (R_spe : SepProp),
      InInitiate img W s0 sf 0x0584 →
      sf.trace = s0.trace →
      w0 ≠ 0#64 - 3#64 →
      (((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₆₄ w2) ∗
        ((x.ret + 24#64) ↦₆₄ w3) ∗ ((x.ret + 32#64) ↦₆₄ w4) ∗ ((x.ret + 40#64) ↦₆₄ w5) ∗ R_spe) ⊢
        RunDrop.speOwnedAt A x.ret k) →
      sf.readReg64 (.gpr 22#5) = 1#64 →
      sf.readReg64 (.gpr 26#5) = w0 →
      sf.readReg64 (.gpr 27#5) = w1 →
      sf.readReg64 (.gpr 25#5) = w2 →
      sf.readReg64 (.gpr 28#5) = w3 →
      sf.readReg64 (.gpr 24#5) = w4 →
      sf.readReg64 (.gpr 21#5) = w5 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (A.pool ∗ R_spe ∗
          memRegion (s.sp + 120#64) 8 ∗
          memRegion (s.sp + 1472#64) 16 ∗
          memRegion (s.sp + 1864#64) 24 ∗
          memRegion (s.sp + 5632#64) 72 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        memRegion (s.sp + 120#64) 8 ∗
        ((s.sp + 1472#64) ↦₆₄ box) ∗
        ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗
        memRegion (s.sp + 1864#64) 24 ∗
        idKeyPairOutAt A (s.sp + 5632#64) (.error ()) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) :=
  segA_step4_err_ext (ext := cliHookExterns W) himg hh.toExt
    { futDrop := hStore.futDrop
      idTrustShim := hStore.idTrustShim
      idTrustPoll := hStore.idTrustPoll
      sessLoadShim := hStore.sessLoadShim
      sessLoadPoll := hStore.sessLoadPoll
      idKeyPairShim := hStore.idKeyPairShim
      idKeyPairPoll := hStore.idKeyPairPoll
      idRegIdShim := hStore.idRegIdShim
      idRegIdPoll := hStore.idRegIdPoll
      idSaveShim := hStore.idSaveShim
      idSavePoll := hStore.idSavePoll
      sessStoreShim := hStore.sessStoreShim
      sessStorePoll := hStore.sessStorePoll }
    hstk hstk64 (InInitiate.toExt hctrl) htrace hx20 hx21 hpanic
    (fun sf k w0 w1 w2 w3 w4 w5 R_spe hctrlf =>
      hnext sf k w0 w1 w2 w3 w4 w5 R_spe (InInitiateExt.toLegacy hctrlf))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
