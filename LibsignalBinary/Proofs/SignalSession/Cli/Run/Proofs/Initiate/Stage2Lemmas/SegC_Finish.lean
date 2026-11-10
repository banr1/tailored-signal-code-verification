/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_CloneSameAcct
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 2 Segment C Completion (`0x0584 → 0x0760`): `opk` Unpacking and `AtStage3` Handoff

Verifies Step C4 (`segC_step4_opk`: staging Alice's parameters and unpacking optional `bundle.opk`)
and composes Steps C1–C4 into `segC_ok` and `segC_ok_ext` reaching `AtStage3` (`0x0760`).
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

private def bundleOpkSlot (a : BitVec 64) : Option (BitVec 32 × PublicKey) → SepProp
  | some (_, k) => (a + 157#64) ↦ₛ k.bytes.toList
  | none => memRegion (a + 157#64) 32

private theorem cliBundleBodyAt_eq_slot (a : BitVec 64) (b : BundleV)
    (spkSigPtr kpkSigPtr kpkPtr : BitVec 64) (opkId : BitVec 32) :
    cliBundleBodyAt a b spkSigPtr kpkSigPtr kpkPtr opkId =
      let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
      ((a + 24#64) ↦ₛ b.spk.bytes.toList) ∗
        ((a + 88#64) ↦₆₄ kpkPtr) ∗ ((a + 96#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ b.kpk) ∗
        ((a + 112#64) ↦₃₂ opkFlag) ∗ ((a + 116#64) ↦₃₂ opkId) ∗
        ((a + 120#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
        ((a + 156#64) ↦₈ opkFlag.truncate 8) ∗
        bundleOpkSlot a b.opk ∗
        cliBundleRestAt a b spkSigPtr kpkSigPtr := by
  unfold cliBundleBodyAt bundleOpkSlot
  rcases b.opk with _ | ⟨_, _⟩ <;> rfl

set_option maxHeartbeats 2400000 in
/-- Stage 2 Step C4 (`+1676 → +1888`, `initProgExt`): stages Alice's parameters and unpacks optional `bundle.opk` to `0x0760`. -/
private theorem segC_step4_opk_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32} {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hctrl : InInitiateExt img ext s0 s 0x068c)
    (hw0 : (s.readReg64 .x0).setWidth 32 = 0#32)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx26 : s.readReg64 (.gpr 26#5) = pqspkPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hekPkLen : ekAPk.length = 32)
    (hekSkLen : ekASk.length = 32)
    (hk : ∀ sm : State,
      (s.mem.KeepsFrozen sm.mem → sm.fs.files = s.fs.files → InInitiateExt img ext s0 sm 0x0760) →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64 →
      sm.readReg64 (.gpr 22#5) = s.sp + 0x408#64 →
      sm.readReg64 (.gpr 23#5) = s.sp + 0x80#64 →
      sm.readReg64 (.gpr 24#5) = s.sp + 0x3e8#64 →
      post sm
        (((s.sp + 0x78#64) ↦₆₄ (s.sp + 0x3c8#64)) ∗
          initArgsAt img s.sp x s0 ∗
          stage3KeySlotsAt A s.sp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (s.sp + 1904#64) 32 ∗
          memRegion (s.sp + 2336#64) 32 ∗
          memRegion (s.sp + 2496#64) 32 ∗
          memRegion (s.sp + 4064#64) 64 ∗
          memRegion (s.sp + 5632#64) 64 ∗
          ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
          bundleOpkSlot x.bundleA x.bundle.opk ∗
          F)) :
    SepWP (initProgExt img ext) (initPcExt img ext 0x0760) s
      (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        initArgsAt img s.sp x s0 ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        memRegion (s.sp + 696#64) 72 ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        memRegion (s.sp + 840#64) 280 ∗
        A.live pqspkPtr 1568 1 ∗
        (pqspkPtr ↦ₛ x.bundle.kpk) ∗
        ((s.sp + 1904#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 2336#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((s.sp + 2496#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 4064#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 4096#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((s.sp + 5632#64) ↦ₛ ekAPk) ∗
        ((s.sp + 5664#64) ↦ₛ ekASk) ∗
        ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        bundleOpkSlot x.bundleA x.bundle.opk ∗
        F)
      post (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "libsignal_cli_handshake::initiate"))
    1676 212
  clear hfn
  obtain ⟨hw0_328, hw0_8, hw0_ext⟩ := w0_low_byte_zero hw0
  obtain ⟨ekp0, ekp1, ekp2, ekp3, hekp⟩ := exists_keyWords4_of_len32 hekPkLen
  obtain ⟨eks0, eks1, eks2, eks3, heks⟩ := exists_keyWords4_of_len32 hekSkLen
  obtain ⟨kpp0, kpp1, kpp2, kpp3, hkpp⟩ :=
    exists_keyWords4_of_len32 (bs := kp.identityKey.publicKey.bytes.toList)
      kp.identityKey.publicKey.bytes.property
  obtain ⟨kps0, kps1, kps2, kps3, hkps⟩ :=
    exists_keyWords4_of_len32 (bs := kp.privateKey.bytes.toList) kp.privateKey.bytes.property
  obtain ⟨spk0, spk1, spk2, spk3, hspk⟩ :=
    exists_keyWords4_of_len32 (bs := x.bundle.spk.bytes.toList) x.bundle.spk.bytes.property
  obtain ⟨idk0, idk1, idk2, idk3, hidk⟩ :=
    exists_keyWords4_of_len32 (bs := x.bundle.idKey.publicKey.bytes.toList)
      x.bundle.idKey.publicKey.bytes.property
  have hpc : s.pc = initEntryExt img ext + 1676#64 := hctrl.pc
  have hrun : s.status = .Running := hctrl.run
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hctrl.sp hctrl.spAligned
  have hent : initEntryExt img ext =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
  have hm776_fold :
      ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ⊢
      memRegion (s.sp + 776#64) 64 :=
    mr_fold (s.sp + 776#64) (s.sp + 808#64) 32 32 64
      (mr_of_bytes _ _ _ kp.identityKey.publicKey.bytes.property)
      (mr_of_bytes _ _ _ kp.privateKey.bytes.property) rfl (by bv_omega)
  have hm1904 :
      ((s.sp + 1904#64) ↦₆₄ spk0) ∗ (((s.sp + 1912#64) ↦₆₄ spk1) ∗
        (((s.sp + 1920#64) ↦₆₄ spk2) ∗ ((s.sp + 1928#64) ↦₆₄ spk3))) ⊢
      memRegion (s.sp + 1904#64) 32 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words4_entails_mr32 (s.sp + 1904#64) spk0 spk1 spk2 spk3
  have hm2336 :
      ((s.sp + 2336#64) ↦₆₄ idk0) ∗ (((s.sp + 2344#64) ↦₆₄ idk1) ∗
        (((s.sp + 2352#64) ↦₆₄ idk2) ∗ ((s.sp + 2360#64) ↦₆₄ idk3))) ⊢
      memRegion (s.sp + 2336#64) 32 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words4_entails_mr32 (s.sp + 2336#64) idk0 idk1 idk2 idk3
  have hm2496 :
      ((s.sp + 2496#64) ↦₆₄ spk0) ∗ (((s.sp + 2504#64) ↦₆₄ spk1) ∗
        (((s.sp + 2512#64) ↦₆₄ spk2) ∗ ((s.sp + 2520#64) ↦₆₄ spk3))) ⊢
      memRegion (s.sp + 2496#64) 32 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words4_entails_mr32 (s.sp + 2496#64) spk0 spk1 spk2 spk3
  have hm4064 :
      ((s.sp + 4064#64) ↦₆₄ kpp0) ∗ (((s.sp + 4072#64) ↦₆₄ kpp1) ∗
        (((s.sp + 4080#64) ↦₆₄ kpp2) ∗ (((s.sp + 4088#64) ↦₆₄ kpp3) ∗
          (((s.sp + 4096#64) ↦₆₄ kps0) ∗ (((s.sp + 4104#64) ↦₆₄ kps1) ∗
            (((s.sp + 4112#64) ↦₆₄ kps2) ∗ ((s.sp + 4120#64) ↦₆₄ kps3))))))) ⊢
      memRegion (s.sp + 4064#64) 64 := by
    have h1 := words4_entails_mr32 (s.sp + 4064#64) kpp0 kpp1 kpp2 kpp3
    have h2 := words4_entails_mr32 (s.sp + 4096#64) kps0 kps1 kps2 kps3
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      mr_fold (s.sp + 4064#64) (s.sp + 4096#64) 32 32 64 h1 h2 rfl (by bv_omega)
  have hm5632 :
      ((s.sp + 5632#64) ↦₆₄ ekp0) ∗ (((s.sp + 5640#64) ↦₆₄ ekp1) ∗
        (((s.sp + 5648#64) ↦₆₄ ekp2) ∗ (((s.sp + 5656#64) ↦₆₄ ekp3) ∗
          (((s.sp + 5664#64) ↦₆₄ eks0) ∗ (((s.sp + 5672#64) ↦₆₄ eks1) ∗
            (((s.sp + 5680#64) ↦₆₄ eks2) ∗ ((s.sp + 5688#64) ↦₆₄ eks3))))))) ⊢
      memRegion (s.sp + 5632#64) 64 := by
    have h1 := words4_entails_mr32 (s.sp + 5632#64) ekp0 ekp1 ekp2 ekp3
    have h2 := words4_entails_mr32 (s.sp + 5664#64) eks0 eks1 eks2 eks3
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      mr_fold (s.sp + 5632#64) (s.sp + 5664#64) 32 32 64 h1 h2 rfl (by bv_omega)
  unfold initArgsAt
  rw [mr_280_staging_split s.sp,
      mr_32_eq_words4 (s.sp + 840#64), mr_32_eq_words4 (s.sp + 872#64),
      mr_32_eq_words4 (s.sp + 904#64), mr_32_eq_words4 (s.sp + 936#64),
      mr_32_eq_words4 (s.sp + 968#64), mr_32_eq_words4 (s.sp + 1000#64),
      mr_32_eq_words4 (s.sp + 1032#64),
      memRegion_8_eq_exists (s.sp + 1064#64), memRegion_8_eq_exists (s.sp + 1072#64),
      memRegion_1_eq_exists (s.sp + 1080#64), memRegion_1_eq_exists (s.sp + 1113#64),
      hspk (s.sp + 1904#64) (s.sp + 1912#64) (s.sp + 1920#64) (s.sp + 1928#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hidk (s.sp + 2336#64) (s.sp + 2344#64) (s.sp + 2352#64) (s.sp + 2360#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hspk (s.sp + 2496#64) (s.sp + 2504#64) (s.sp + 2512#64) (s.sp + 2520#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hkpp (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hkps (s.sp + 4096#64) (s.sp + 4104#64) (s.sp + 4112#64) (s.sp + 4120#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hekp (s.sp + 5632#64) (s.sp + 5640#64) (s.sp + 5648#64) (s.sp + 5656#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      heks (s.sp + 5664#64) (s.sp + 5672#64) (s.sp + 5680#64) (s.sp + 5688#64)
        (by bv_omega) (by bv_omega) (by bv_omega)]
  cases hopk : x.bundle.opk with
  | none =>
    simp only [bundleOpkSlot, opkFlag_none, sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 32 (apply SepWP.exists_left; intro _)
    try simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt, initPcExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    refine SepWP.weaken_pre ?_
      (SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        (hk _ (fun hkf hfiles => inInitiateExt_of_step hctrl
          (by simp only [initPcExt, hent, arm64_norm]; try bv_omega)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm])
          hkf hfiles)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; try bv_omega)
          (by simp only [arm64_norm]; try bv_omega)
          (by simp only [arm64_norm]; try bv_omega)
          (by simp only [arm64_norm, hx23]; try bv_omega)
          (by simp only [arm64_norm]; try bv_omega)))
    unfold initArgsAt
    rw [← stage3KeySlotsAt_none A s.sp x.bundle kp ekASk ekAPk pqspkPtr opkId hopk,
        hkpp (s.sp + 840#64) (s.sp + 848#64) (s.sp + 856#64) (s.sp + 864#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hkps (s.sp + 872#64) (s.sp + 880#64) (s.sp + 888#64) (s.sp + 896#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hekp (s.sp + 904#64) (s.sp + 912#64) (s.sp + 920#64) (s.sp + 928#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        heks (s.sp + 936#64) (s.sp + 944#64) (s.sp + 952#64) (s.sp + 960#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hidk (s.sp + 968#64) (s.sp + 976#64) (s.sp + 984#64) (s.sp + 992#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hspk (s.sp + 1000#64) (s.sp + 1008#64) (s.sp + 1016#64) (s.sp + 1024#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hspk (s.sp + 1032#64) (s.sp + 1040#64) (s.sp + 1048#64) (s.sp + 1056#64)
          (by bv_omega) (by bv_omega) (by bv_omega)]
    try simp only [hopk, bundleOpkSlot, opkFlag_none,
      sepConj_assoc]
    refine entails_by_focus (by sep_frame) hm776_fold ?_
    refine entails_by_focus (by sep_frame) hm1904 ?_
    refine entails_by_focus (by sep_frame) hm2336 ?_
    refine entails_by_focus (by sep_frame) hm2496 ?_
    refine entails_by_focus (by sep_frame) hm4064 ?_
    refine entails_by_focus (by sep_frame) hm5632 ?_
    sep_frame
  | some p =>
    rcases p with ⟨id, k⟩
    dsimp only [bundleOpkSlot]
    obtain ⟨ov0, ov1, ov2, ov3, ov4, ov5, ov6, hopk_sp⟩ :=
      exists_opkSplit32 (bs := k.bytes.toList) k.bytes.property
    rw [mr_opk_32_eq (s.sp + 1081#64),
        hopk_sp (x.bundleA + 157#64) (x.bundleA + 161#64) (x.bundleA + 163#64)
          (x.bundleA + 164#64) (x.bundleA + 172#64) (x.bundleA + 180#64) (x.bundleA + 188#64)
          (by bv_omega) (by bv_omega) (by bv_omega)
          (by bv_omega) (by bv_omega) (by bv_omega)]
    simp (config := { maxSteps := 200000 }) only
      [opkFlag_some, sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 39 (apply SepWP.exists_left; intro _)
    try simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt, initPcExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    refine SepWP.weaken_pre ?_
      (SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
        (hk _ (fun hkf hfiles => inInitiateExt_of_step hctrl
          (by simp only [initPcExt, hent, arm64_norm]; try bv_omega)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [calleeSavedVRegs, arm64_norm])
          hkf hfiles)
          (by simp only [arm64_norm])
          (by simp only [arm64_norm]; try bv_omega)
          (by simp only [arm64_norm]; try bv_omega)
          (by simp only [arm64_norm]; try bv_omega)
          (by simp only [arm64_norm, hx23]; try bv_omega)
          (by simp only [arm64_norm]; try bv_omega)))
    unfold initArgsAt
    rw [← stage3KeySlotsAt_some A s.sp x.bundle kp ekASk ekAPk pqspkPtr opkId id k hopk]
    simp only [hopk, bundleOpkSlot, opkFlag_some]
    rw [hopk_sp (x.bundleA + 157#64) (x.bundleA + 161#64) (x.bundleA + 163#64)
          (x.bundleA + 164#64) (x.bundleA + 172#64) (x.bundleA + 180#64) (x.bundleA + 188#64)
          (by bv_omega) (by bv_omega) (by bv_omega)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hopk_sp (s.sp + 1081#64) (s.sp + 1085#64) (s.sp + 1087#64)
          (s.sp + 1088#64) (s.sp + 1096#64) (s.sp + 1104#64) (s.sp + 1112#64)
          (by bv_omega) (by bv_omega) (by bv_omega)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hkpp (s.sp + 840#64) (s.sp + 848#64) (s.sp + 856#64) (s.sp + 864#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hkps (s.sp + 872#64) (s.sp + 880#64) (s.sp + 888#64) (s.sp + 896#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hekp (s.sp + 904#64) (s.sp + 912#64) (s.sp + 920#64) (s.sp + 928#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        heks (s.sp + 936#64) (s.sp + 944#64) (s.sp + 952#64) (s.sp + 960#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hidk (s.sp + 968#64) (s.sp + 976#64) (s.sp + 984#64) (s.sp + 992#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hspk (s.sp + 1000#64) (s.sp + 1008#64) (s.sp + 1016#64) (s.sp + 1024#64)
          (by bv_omega) (by bv_omega) (by bv_omega),
        hspk (s.sp + 1032#64) (s.sp + 1040#64) (s.sp + 1048#64) (s.sp + 1056#64)
          (by bv_omega) (by bv_omega) (by bv_omega)]
    try simp only [sepConj_assoc]
    refine entails_by_focus (by sep_frame) hm776_fold ?_
    refine entails_by_focus (by sep_frame) hm1904 ?_
    refine entails_by_focus (by sep_frame) hm2336 ?_
    refine entails_by_focus (by sep_frame) hm2496 ?_
    refine entails_by_focus (by sep_frame) hm4064 ?_
    refine entails_by_focus (by sep_frame) hm5632 ?_
    sep_frame

private theorem segC_step4_opk {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32} {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hctrl : InInitiate img W s0 s 0x068c)
    (hw0 : (s.readReg64 .x0).setWidth 32 = 0#32)
    (hx22 : s.readReg64 (.gpr 22#5) = s.sp + 128#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 1568#64)
    (hx26 : s.readReg64 (.gpr 26#5) = pqspkPtr)
    (hx27 : s.readReg64 (.gpr 27#5) = s.sp + 783#64)
    (hekPkLen : ekAPk.length = 32)
    (hekSkLen : ekASk.length = 32)
    (hk : ∀ sm : State,
      (s.mem.KeepsFrozen sm.mem → sm.fs.files = s.fs.files → InInitiate img W s0 sm 0x0760) →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 20#5) = s.sp + 0x348#64 →
      sm.readReg64 (.gpr 21#5) = s.sp + 0x388#64 →
      sm.readReg64 (.gpr 22#5) = s.sp + 0x408#64 →
      sm.readReg64 (.gpr 23#5) = s.sp + 0x80#64 →
      sm.readReg64 (.gpr 24#5) = s.sp + 0x3e8#64 →
      post sm
        (((s.sp + 0x78#64) ↦₆₄ (s.sp + 0x3c8#64)) ∗
          initArgsAt img s.sp x s0 ∗
          stage3KeySlotsAt A s.sp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (s.sp + 1904#64) 32 ∗
          memRegion (s.sp + 2336#64) 32 ∗
          memRegion (s.sp + 2496#64) 32 ∗
          memRegion (s.sp + 4064#64) 64 ∗
          memRegion (s.sp + 5632#64) 64 ∗
          ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
          bundleOpkSlot x.bundleA x.bundle.opk ∗
          F)) :
    SepWP (initProg img W) (initPc img W 0x0760) s
      (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        initArgsAt img s.sp x s0 ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        memRegion (s.sp + 696#64) 72 ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        memRegion (s.sp + 840#64) 280 ∗
        A.live pqspkPtr 1568 1 ∗
        (pqspkPtr ↦ₛ x.bundle.kpk) ∗
        ((s.sp + 1904#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 2336#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((s.sp + 2496#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 4064#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 4096#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((s.sp + 5632#64) ↦ₛ ekAPk) ∗
        ((s.sp + 5664#64) ↦ₛ ekASk) ∗
        ((x.bundleA + 156#64) ↦₈ (if x.bundle.opk.isSome then 1#32 else 0#32).truncate 8) ∗
        bundleOpkSlot x.bundleA x.bundle.opk ∗
        F)
      post (initOom s0) :=
  segC_step4_opk_ext (ext := cliHookExterns W) (InInitiate.toExt hctrl) hw0 hx22 hx23 hx25 hx26 hx27
    hekPkLen hekSkLen
    (fun sm hctrlm => hk sm (fun hkf hfiles => InInitiateExt.toLegacy (hctrlm hkf hfiles)))

set_option maxHeartbeats 1200000 in
/-- Full Segment C (`0x0584 → 0x0760`, `initProgExt`) from `Ok(kp)` to `AtStage3Ext` and `stage3Mem`. -/
theorem segC_ok_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {opkId : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8} {u1 u2 u3 u4 u5 u6 u7 : BitVec 64}
    {stk : Nat} {s0 s2 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hLocal : Stage2CalleesExt img P A ext)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs2 : AtStage2Ext img P ext X x be s0 s2)
    (hctrl : InInitiateExt img ext s0 s 0x0584)
    (htr : s.trace = s0.trace)
    (hkpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hekPair :
      let ekKP := keyPairOf P.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
      ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList)
    (hbPure : x.bundle.spkSig.length = 64 ∧ x.bundle.kpkSig.length = 64 ∧
      x.bundle.kpk.length = 1568 ∧ ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = u1)
    (hx27 : s.readReg64 (.gpr 27#5) = u2)
    (hx25 : s.readReg64 (.gpr 25#5) = u3)
    (hx28 : s.readReg64 (.gpr 28#5) = u4)
    (hx24 : s.readReg64 (.gpr 24#5) = u5)
    (hx21 : s.readReg64 (.gpr 21#5) = u6)
    (hkpLo : ∀ a : BitVec 64,
      (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
        ((a + 7#64) ↦₆₄ u1) ∗ ((a + 15#64) ↦₆₄ u2) ∗
        ((a + 23#64) ↦₆₄ u3) ∗ ((a + 31#64) ↦₆₄ u4) =
        (a ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((a + 32#64) ↦ₛ kp.privateKey.bytes.toList.take 7))
    (hkpHi : ∀ a : BitVec 64,
      (a ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
        ((a + 7#64) ↦₆₄ u5) ∗ ((a + 15#64) ↦₆₄ u6) ∗
        ((a + 23#64) ↦₆₄ u7) ∗ ((a + 31#64) ↦₈ b63) =
        (a ↦ₛ kp.privateKey.bytes.toList))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32),
      AtStage3Ext img P ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
        (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        coinsCursorAt img x.coinsP x.coins 32 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion s.sp 0x78 ∗ ((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        memRegion (s.sp + 0x80#64) 0x50 ∗
        initArgsAt img s.sp x s0 ∗
        initFreshRecAt s.sp ∗
        memRegion (s.sp + 0x148#64) 0x150 ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        ((s.sp + 696#64) ↦ₛ ekASk) ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        memRegion (s.sp + 776#64) 344 ∗
        memRegion (s.sp + 0x460#64) 0x158 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 1472#64) 16 ∗
        ((s.sp + 1864#64) ↦₆₄ u7) ∗ ((s.sp + 1872#64) ↦₈ b63) ∗
        memRegion (s.sp + 1873#64) 7 ∗
        ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
        ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
        memRegion (s.sp + 1887#64) 1 ∗
        memRegion (s.sp + 1904#64) 32 ∗
        memRegion (s.sp + 2336#64) 32 ∗
        memRegion (s.sp + 2496#64) 32 ∗
        memRegion (s.sp + 4064#64) 64 ∗
        memRegion (s.sp + 5632#64) 64 ∗
        memRegion (s.sp + 5696#64) 8 ∗
        scratch5baGaps s.sp ∗
        stackAt s.sp (stk - cliInitiateFrame))
      Q Qp (initOom s0) := by
  have hekPkLen : ekAPk.length = 32 := by rw [hekPair.2]; exact List.Vector.toList_length _
  have hekSkLen : ekASk.length = 32 := by rw [hekPair.1]; exact List.Vector.toList_length _
  rw [cliBundleBodyAt_eq_slot]
  unfold initArgsAt
  dsimp only
  rw [mr_split (s.sp + 776#64) (s.sp + 840#64) 64 280 344 rfl (by bv_omega)]
  refine' sepWPp_weaken_pre ?_
    (sepWPp_of_sepWP_fs hh.fs (mid := initPcExt img ext 0x0650)
      (segC_step1_unpack_ext (x := x) hctrl hx22 hx26 hx27 hx25 hx28 hx24 hx21 hkpLo hkpHi
        hekPkLen hekSkLen
        fun sm hpcm hrunm hspm hfpm hx19m hsymm hvregsm htrm hx20m hx22m hx23m hx25m hx27m => ?_))
  · try simp only [sepConj_assoc]
    sep_frame
  refine ⟨htrm, fun hkfm hfilesm => ?_⟩
  have hctrlm : InInitiateExt img ext s0 sm 0x0650 :=
    inInitiateExt_of_step hctrl hpcm hrunm hspm hfpm hx19m hsymm hvregsm hkfm hfilesm
  have htrm0 : sm.trace = s0.trace := htrm.trans htr
  rw [← hspm] at hx22m hx23m hx27m ⊢
  refine' sepWPp_weaken_pre ?_
    (segC_step2_clone_ext hh hstk hstk64 hctrlm htrm0 hbPure.2.2.1 hx20m hx22m hx23m hx25m hx27m
      hpanic fun s_c2 pqspkPtr hctrl_c2 htr_c2 hpq_nn hx2_c2 hx22_c2 hx23_c2 hx25_c2 hx26_c2 hx27_c2 => ?_)
  · try simp only [sepConj_assoc]
    sep_frame
  have hsp_c2 : s_c2.sp = sm.sp := hctrl_c2.sp.trans hctrlm.sp.symm
  rw [← hsp_c2] at hx22_c2 hx23_c2 hx27_c2 ⊢
  refine' sepWPp_weaken_pre ?_
    (segC_step3_sameAcct_ext (kp := kp) hh.fs hLocal hinitOk hstk hstk64 hctrl_c2 htr_c2 hx2_c2
      hx22_c2 hx23_c2 hx25_c2 hx26_c2 hx27_c2 hpanic
      fun s_c3 hctrl_c3 htr_c3 hw0_c3 hx22_c3 hx23_c3 hx25_c3 hx26_c3 hx27_c3 => ?_)
  · unfold initArgsAt
    try simp only [sepConj_assoc]
    sep_frame
  have hsp_c3 : s_c3.sp = s_c2.sp := hctrl_c3.sp.trans hctrl_c2.sp.symm
  rw [← hsp_c3] at hx22_c3 hx23_c3 hx27_c3 ⊢
  refine' sepWPp_weaken_pre ?_
    (sepWPp_of_sepWP_fs hh.fs (mid := initPcExt img ext 0x0760)
      (segC_step4_opk_ext (A := A) (x := x) (kp := kp) (opkId := opkId)
        hctrl_c3 hw0_c3 hx22_c3 hx23_c3 hx25_c3 hx26_c3 hx27_c3 hekPkLen hekSkLen
        fun s3 hctrl3 htr3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 => ?_))
  · try simp only [sepConj_assoc]
    sep_frame
  refine ⟨htr3, fun hkf3 hfiles3 => ?_⟩
  have hctrl3' : InInitiateExt img ext s0 s3 0x0760 := hctrl3 hkf3 hfiles3
  have hsp3 : s3.sp = s_c3.sp := hctrl3'.sp.trans hctrl_c3.sp.symm
  have hfsp : s_c3.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame := hctrl_c3.sp
  have hfiles3_x : s3.fs.files = x.F := hctrl3'.files0.trans (hs2.ctrl.files0.symm.trans hs2.files)
  have hs3 : AtStage3Ext img P ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 :=
    { ctrl := hctrl3'
      trace := htr3.trans htr_c3
      files := hfiles3_x
      x8 := hs2.x8
      bundleEq := hs2.bundleEq
      trustedOk := hs2.trustedOk
      signaturesVerify := hs2.signaturesVerify
      kpOk := hkpOk
      ekPairEq := hekPair
      opkIdEq := hbPure.2.2.2
      pqspkNonNull := hpq_nn
      x20 := by rw [← hfsp]; exact hx20_3
      x21 := by rw [← hfsp]; exact hx21_3
      x22 := by rw [← hfsp]; exact hx22_3
      x23 := by rw [← hfsp]; exact hx23_3
      x24 := by rw [← hfsp]; exact hx24_3 }
  refine sepWPp_weaken_pre (P' := stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) ?_
    (hnext s3 kp ekASk ekAPk pqspkPtr opkId hs3)
  have hm5ba :
      memRegion (s_c3.sp + 1472#64) 16 ∗
        (memRegion (s_c3.sp + 1864#64) 24 ∗
          (memRegion (s_c3.sp + 1904#64) 32 ∗
            (memRegion (s_c3.sp + 2336#64) 32 ∗
              (memRegion (s_c3.sp + 2496#64) 32 ∗
                (memRegion (s_c3.sp + 4064#64) 64 ∗
                  ((memRegion (s_c3.sp + 5632#64) 64 ∗ memRegion (s_c3.sp + 5696#64) 8) ∗
                    scratch5baGaps s_c3.sp)))))) ⊢
      memRegion (s_c3.sp + 0x5ba#64) (initLocalsSize - 0x5ba) := by
    have hm5632 := mr_fold (s_c3.sp + 5632#64) (s_c3.sp + 5696#64) 64 8 72
      (Entails.refl _) (Entails.refl _) rfl (by bv_omega)
    rw [scratch5ba_split s_c3.sp]
    try simp only [sepConj_assoc] at hm5632 ⊢
    refine entails_by_focus (by sep_frame) hm5632 ?_
    sep_frame
  have hBundle :=
    cliBundleBody_entails x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId hbPure
  dsimp only [cliBundleBodyAt] at hBundle
  unfold stage3Mem
  dsimp only
  rw [← hfsp]
  cases hopk_fin : x.bundle.opk with
  | none =>
    simp only [hopk_fin, bundleOpkSlot, sepConj_assoc] at hm5ba hBundle ⊢
    refine entails_by_focus (by sep_frame) hm5ba ?_
    refine entails_by_focus (by sep_frame) hBundle ?_
    sep_frame
  | some p =>
    rcases p with ⟨_, _⟩
    simp only [hopk_fin, bundleOpkSlot, sepConj_assoc] at hm5ba hBundle ⊢
    refine entails_by_focus (by sep_frame) hm5ba ?_
    refine entails_by_focus (by sep_frame) hBundle ?_
    sep_frame

/-- Full Segment C (`0x0584 → 0x0760`, `initProg`) from `Ok(kp)` to `AtStage3` and `stage3Mem`. -/
theorem segC_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {opkId : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8} {u1 u2 u3 u4 u5 u6 u7 : BitVec 64}
    {stk : Nat} {s0 s2 s : State} {Q Qp : State → SepProp → Prop}
    (hh : RunHooks img A (cliExterns W))
    (hLocal : InitLocalCallees img A W stk)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs2 : AtStage2 img W X x be s0 s2)
    (hctrl : InInitiate img W s0 s 0x0584)
    (htr : s.trace = s0.trace)
    (hkpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp)
    (hekPair :
      let ekKP := keyPairOf W.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
      ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList)
    (hbPure : x.bundle.spkSig.length = 64 ∧ x.bundle.kpkSig.length = 64 ∧
      x.bundle.kpk.length = 1568 ∧ ∀ p, x.bundle.opk = some p → opkId = p.1)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx26 : s.readReg64 (.gpr 26#5) = u1)
    (hx27 : s.readReg64 (.gpr 27#5) = u2)
    (hx25 : s.readReg64 (.gpr 25#5) = u3)
    (hx28 : s.readReg64 (.gpr 28#5) = u4)
    (hx24 : s.readReg64 (.gpr 24#5) = u5)
    (hx21 : s.readReg64 (.gpr 21#5) = u6)
    (hkpLo : ∀ a : BitVec 64,
      (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
        ((a + 7#64) ↦₆₄ u1) ∗ ((a + 15#64) ↦₆₄ u2) ∗
        ((a + 23#64) ↦₆₄ u3) ∗ ((a + 31#64) ↦₆₄ u4) =
        (a ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((a + 32#64) ↦ₛ kp.privateKey.bytes.toList.take 7))
    (hkpHi : ∀ a : BitVec 64,
      (a ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
        ((a + 7#64) ↦₆₄ u5) ∗ ((a + 15#64) ↦₆₄ u6) ∗
        ((a + 23#64) ↦₆₄ u7) ∗ ((a + 31#64) ↦₈ b63) =
        (a ↦ₛ kp.privateKey.bytes.toList))
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32),
      AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s3
        (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        coinsCursorAt img x.coinsP x.coins 32 ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
        logOff img ∗ A.pool ∗ initSaved s0 ∗
        memRegion s.sp 0x78 ∗ ((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        memRegion (s.sp + 0x80#64) 0x50 ∗
        initArgsAt img s.sp x s0 ∗
        initFreshRecAt s.sp ∗
        memRegion (s.sp + 0x148#64) 0x150 ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        ((s.sp + 696#64) ↦ₛ ekASk) ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        memRegion (s.sp + 776#64) 344 ∗
        memRegion (s.sp + 0x460#64) 0x158 ∗
        ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
        memRegion (s.sp + 1472#64) 16 ∗
        ((s.sp + 1864#64) ↦₆₄ u7) ∗ ((s.sp + 1872#64) ↦₈ b63) ∗
        memRegion (s.sp + 1873#64) 7 ∗
        ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
        ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
        memRegion (s.sp + 1887#64) 1 ∗
        memRegion (s.sp + 1904#64) 32 ∗
        memRegion (s.sp + 2336#64) 32 ∗
        memRegion (s.sp + 2496#64) 32 ∗
        memRegion (s.sp + 4064#64) 64 ∗
        memRegion (s.sp + 5632#64) 64 ∗
        memRegion (s.sp + 5696#64) 8 ∗
        scratch5baGaps s.sp ∗
        stackAt s.sp (stk - cliInitiateFrame))
      Q Qp (initOom s0) :=
  segC_ok_ext (P := ⟨W.C, W.Q⟩) (ext := cliHookExterns W) hh.toExt
    (stage2CalleesExt_of_localCallees hLocal) hinitOk hstk hstk64
    ⟨InInitiate.toExt hs2.ctrl, hs2.trace, hs2.files, hs2.x8, hs2.bundleEq, hs2.trustedOk, hs2.signaturesVerify,
      hs2.x22, hs2.x23, hs2.x25, hs2.x26, hs2.x27⟩
    (InInitiate.toExt hctrl) htr hkpOk hekPair hbPure hx22 hx26 hx27 hx25 hx28 hx24 hx21 hkpLo hkpHi hpanic
    (fun s3 kp ekASk ekAPk pqspkPtr opkId hs3 =>
      hnext s3 kp ekASk ekAPk pqspkPtr opkId
        ⟨InInitiateExt.toLegacy hs3.ctrl, hs3.trace, hs3.files, hs3.x8, hs3.bundleEq, hs3.trustedOk, hs3.signaturesVerify,
          hs3.kpOk, hs3.ekPairEq, hs3.opkIdEq, hs3.pqspkNonNull, hs3.x20, hs3.x21, hs3.x22,
          hs3.x23, hs3.x24⟩)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
