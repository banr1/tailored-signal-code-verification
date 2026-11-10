/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.LayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 2 Segment C Step C1 (`0x0584 → 0x0650`)

Provides `stage2MemPlaced_eq_sp`, `segC_step1_unpack_placed`, and `withLsCodeRoLoaded` call
combinators (`sepWPp_call_fs_lscro`, `sepWPp_call_cli_lscro`) on `initProgPlaced`.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedTactic false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt?

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

theorem stage2MemPlaced_eq_sp [LibsignalPlacement] (A : RustAlloc) (x : InitGhost) (stk : Nat)
    {s0 s : State} (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) :
    stage2MemPlaced A x stk s0 =
      storesAt A x.stores StoresGhost.opened ∗
      protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
      coinsCursorAtPlaced x.coinsP x.coins 0 ∗
      SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
      (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
      FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
      memRegion s.sp 0x78 ∗ memRegion (s.sp + 120#64) 8 ∗ memRegion (s.sp + 0x80#64) 0x50 ∗
      initArgsAtPlaced s.sp x s0 ∗
      memRegion (s.sp + 296#64) 32 ∗
      memRegion (s.sp + 0x148#64) 0x150 ∗
      memRegion (s.sp + 664#64) 456 ∗
      memRegion (s.sp + 0x460#64) 0x158 ∗
      ((s.sp + 0x5b8#64) ↦₈ 0#8) ∗ ((s.sp + 0x5b9#64) ↦₈ 0#8) ∗
      memRegion (s.sp + 1472#64) 16 ∗
      memRegion (s.sp + 1864#64) 24 ∗
      memRegion (s.sp + 1904#64) 32 ∗
      memRegion (s.sp + 2336#64) 32 ∗
      memRegion (s.sp + 2496#64) 32 ∗
      memRegion (s.sp + 4064#64) 64 ∗
      memRegion (s.sp + 5632#64) 72 ∗
      scratch5baGaps s.sp ∗
      stackAt s.sp (stk - cliInitiateFrame) := by
  unfold stage2MemPlaced
  dsimp only
  rw [← hsp,
      mr_split s.sp (s.sp + 120#64) 120 88 208 rfl rfl,
      mr_split (s.sp + 120#64) (s.sp + 128#64) 8 80 88 rfl (by bv_omega),
      mr_split (s.sp + 296#64) (s.sp + 328#64) 32 1136 1168 rfl (by bv_omega),
      mr_split (s.sp + 328#64) (s.sp + 664#64) 336 800 1136 rfl (by bv_omega),
      mr_split (s.sp + 664#64) (s.sp + 1120#64) 456 344 800 rfl (by bv_omega),
      scratch5ba_split s.sp]
  ac_rfl

theorem inInitiatePlaced_of_step [LibsignalPlacement] {s0 s sm : State} {k0 k1 : Nat}
    (hctrl : InInitiatePlaced s0 s k0)
    (hpc : sm.pc = initPcPlaced k1)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s.sp)
    (hfp : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s)
    (hkf : s.mem.KeepsFrozen sm.mem)
    (hfiles : sm.fs.files = s.fs.files) :
    InInitiatePlaced s0 sm k1 :=
  { pc := hpc
    run := hrun
    sp := hsp.trans hctrl.sp
    fp := hfp.trans hctrl.fp
    x19 := hx19.trans hctrl.x19
    files0 := hfiles.trans hctrl.files0
    inv := hctrl.inv.of_keepsFrozen hkf
    vregs := hvregs.trans hctrl.vregs
    spAligned := hctrl.spAligned }

set_option maxHeartbeats 1600000 in
/-- Relocatable Stage 2 Step C1 (`+1412 → +1616`): reassembles `(kp.pk, kp.sk)` and stages key slices on `initProgPlaced`. -/
theorem segC_step1_unpack_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {x : InitGhost} {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
    {b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8} {u1 u2 u3 u4 u5 u6 u7 : BitVec 64}
    {s0 s : State} {F : SepProp}
    {post : State → SepProp → Prop}
    (hctrl : InInitiatePlaced s0 s 0x0584)
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
    (hekPkLen : ekAPk.length = 32)
    (hekSkLen : ekASk.length = 32)
    (hk : ∀ sm : State,
      sm.pc = initPcPlaced 0x0650 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.readReg64 .fp = s.readReg64 .fp →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.symtab = s.symtab →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.trace = s.trace →
      sm.readReg64 (.gpr 20#5) = x.kpkPtr →
      sm.readReg64 (.gpr 22#5) = s.sp + 128#64 →
      sm.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      sm.readReg64 (.gpr 25#5) = 1568#64 →
      sm.readReg64 (.gpr 27#5) = s.sp + 783#64 →
      post sm
        (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
          ((s.sp + 288#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
          ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          memRegion (s.sp + 696#64) 72 ∗
          ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          memRegion (s.sp + 1864#64) 24 ∗
          ((s.sp + 1904#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 2336#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((s.sp + 2496#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 4064#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 4096#64) ↦ₛ kp.privateKey.bytes.toList) ∗
          ((s.sp + 5632#64) ↦ₛ ekAPk) ∗
          ((s.sp + 5664#64) ↦ₛ ekASk) ∗
          ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
          ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
          ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          F)) :
    SepWP (initProgPlaced mmpl gh W) (initPcPlaced 0x0650) s
      (((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        ((s.sp + 696#64) ↦ₛ ekASk) ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        memRegion (s.sp + 776#64) 64 ∗
        ((s.sp + 1864#64) ↦₆₄ u7) ∗
        ((s.sp + 1872#64) ↦₈ b63) ∗
        memRegion (s.sp + 1873#64) 7 ∗
        ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
        ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
        memRegion (s.sp + 1887#64) 1 ∗
        memRegion (s.sp + 1904#64) 32 ∗
        memRegion (s.sp + 2336#64) 32 ∗
        memRegion (s.sp + 2496#64) 32 ∗
        memRegion (s.sp + 4064#64) 64 ∗
        memRegion (s.sp + 5632#64) 64 ∗
        ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
        ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        F)
      post (initOom s0) := by
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
  have hpc : s.pc = (blkPl_521).base + 1412#64 := hctrl.pc
  have hrun : s.status = .Running := hctrl.run
  have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true :=
    spAligned_mask_of_frame hctrl.sp hctrl.spAligned
  have h776_split :
      memRegion (s.sp + 776#64) 64 ⊢
        (∃∗ db63 : BitVec 8,
         ∃∗ q7 : BitVec 64, ∃∗ q6 : BitVec 64, ∃∗ q5 : BitVec 64,
         ∃∗ q4 : BitVec 64, ∃∗ q3 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q1 : BitVec 64,
         ∃∗ d6 : BitVec 8, ∃∗ d5 : BitVec 8, ∃∗ d4 : BitVec 8, ∃∗ d3 : BitVec 8,
         ∃∗ d2 : BitVec 8, ∃∗ d1 : BitVec 8, ∃∗ d0 : BitVec 8,
           ((s.sp + 776#64) ↦₈ d0) ∗ ((s.sp + 777#64) ↦₈ d1) ∗ ((s.sp + 778#64) ↦₈ d2) ∗
           ((s.sp + 779#64) ↦₃₂ (d6 ++ d5 ++ d4 ++ d3)) ∗
           ((s.sp + 783#64) ↦₆₄ q1) ∗ ((s.sp + 791#64) ↦₆₄ q2) ∗
           ((s.sp + 799#64) ↦₆₄ q3) ∗ ((s.sp + 807#64) ↦₆₄ q4) ∗
           ((s.sp + 815#64) ↦₆₄ q5) ∗ ((s.sp + 823#64) ↦₆₄ q6) ∗
           ((s.sp + 831#64) ↦₆₄ q7) ∗ ((s.sp + 839#64) ↦₈ db63)) := by
    rw [mr_split (s.sp + 776#64) (s.sp + 783#64) 7 57 64 rfl (by bv_omega),
        mr_split (s.sp + 783#64) (s.sp + 791#64) 8 49 57 rfl (by bv_omega),
        mr_split (s.sp + 791#64) (s.sp + 799#64) 8 41 49 rfl (by bv_omega),
        mr_split (s.sp + 799#64) (s.sp + 807#64) 8 33 41 rfl (by bv_omega),
        mr_split (s.sp + 807#64) (s.sp + 815#64) 8 25 33 rfl (by bv_omega),
        mr_split (s.sp + 815#64) (s.sp + 823#64) 8 17 25 rfl (by bv_omega),
        mr_split (s.sp + 823#64) (s.sp + 831#64) 8 9 17 rfl (by bv_omega),
        mr_split (s.sp + 831#64) (s.sp + 839#64) 8 1 9 rfl (by bv_omega),
        memRegion_8_eq_exists (s.sp + 783#64), memRegion_8_eq_exists (s.sp + 791#64),
        memRegion_8_eq_exists (s.sp + 799#64), memRegion_8_eq_exists (s.sp + 807#64),
        memRegion_8_eq_exists (s.sp + 815#64), memRegion_8_eq_exists (s.sp + 823#64),
        memRegion_8_eq_exists (s.sp + 831#64), memRegion_1_eq_exists (s.sp + 839#64)]
    refine Entails.trans (sepConj_mono_left (sevenHi_of_memRegion7 (s.sp + 776#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    exact Entails.refl _
  refine SepWP.weaken_pre
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (Entails.refl _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (Entails.refl _)
              (sepConj_mono (Entails.refl _)
                (sepConj_mono_left h776_split))))))) ?_
  rw [hekp (s.sp + 664#64) (s.sp + 672#64) (s.sp + 680#64) (s.sp + 688#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      heks (s.sp + 696#64) (s.sp + 704#64) (s.sp + 712#64) (s.sp + 720#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hspk (s.sp + 728#64) (s.sp + 736#64) (s.sp + 744#64) (s.sp + 752#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      hidk (x.bundleA + 120#64) (x.bundleA + 128#64) (x.bundleA + 136#64) (x.bundleA + 144#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 b0 b1 b2 b3 b4 b5 b6,
      mr_32_eq_words4 (s.sp + 1904#64),
      mr_32_eq_words4 (s.sp + 2336#64),
      mr_32_eq_words4 (s.sp + 2496#64),
      mr_split (s.sp + 4064#64) (s.sp + 4096#64) 32 32 64 rfl (by bv_omega),
      mr_32_eq_words4 (s.sp + 4064#64), mr_32_eq_words4 (s.sp + 4096#64),
      mr_split (s.sp + 5632#64) (s.sp + 5664#64) 32 32 64 rfl (by bv_omega),
      mr_32_eq_words4 (s.sp + 5632#64), mr_32_eq_words4 (s.sp + 5664#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  simp (config := { maxSteps := 2000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 43 (apply SepWP.exists_left; intro _)
  simp only [sepConj_assoc]
  rw [show initPcPlaced 0x0650 = (blkPl_521).base + 1616#64 from rfl] at hk ⊢
  dsimp only [initProgPlaced, lsProg_521]
  wp_steps
  conv => arg 4; simp only [← sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 b0 b1 b2 b3 b4 b5 b6,
    sepConj_assoc]
  wp_steps
  conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 776#64 777#64 778#64 779#64 780#64 781#64 782#64,
    sepConj_assoc]
  wp_steps
  have hkpLoWords : ∀ rest : SepProp,
      ((s.sp + 776#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        (((s.sp + 780#64) ↦₈ b4) ∗ (((s.sp + 781#64) ↦₈ b5) ∗ (((s.sp + 782#64) ↦₈ b6) ∗
          (((s.sp + 783#64) ↦₆₄ u1) ∗ (((s.sp + 791#64) ↦₆₄ u2) ∗
            (((s.sp + 799#64) ↦₆₄ u3) ∗ (((s.sp + 807#64) ↦₆₄ u4) ∗ rest))))))) =
      ((s.sp + 776#64) ↦₆₄ kpp0) ∗ (((s.sp + 784#64) ↦₆₄ kpp1) ∗
        (((s.sp + 792#64) ↦₆₄ kpp2) ∗ (((s.sp + 800#64) ↦₆₄ kpp3) ∗
          (((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList.take 7) ∗ rest)))) := fun rest => by
    have hL := hkpLo (s.sp + 776#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hL
    rw [hkpp (s.sp + 776#64) (s.sp + 784#64) (s.sp + 792#64) (s.sp + 800#64)
      (by bv_omega) (by bv_omega) (by bv_omega)] at hL
    simpa only [sepConj_assoc] using congrArg (· ∗ rest) hL
  have hkpHiWords : ∀ rest : SepProp,
      ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
        (((s.sp + 815#64) ↦₆₄ u5) ∗ (((s.sp + 823#64) ↦₆₄ u6) ∗
          (((s.sp + 831#64) ↦₆₄ u7) ∗ (((s.sp + 839#64) ↦₈ b63) ∗ rest)))) =
      ((s.sp + 808#64) ↦₆₄ kps0) ∗ (((s.sp + 816#64) ↦₆₄ kps1) ∗
        (((s.sp + 824#64) ↦₆₄ kps2) ∗ (((s.sp + 832#64) ↦₆₄ kps3) ∗ rest))) := fun rest => by
    have hH := hkpHi (s.sp + 808#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hH
    rw [hkps (s.sp + 808#64) (s.sp + 816#64) (s.sp + 824#64) (s.sp + 832#64)
      (by bv_omega) (by bv_omega) (by bv_omega)] at hH
    simpa only [sepConj_assoc] using congrArg (· ∗ rest) hH
  conv => arg 4; simp only [sepConj_assoc]; rw [hkpLoWords]
  wp_steps
  conv => arg 4; simp only [sepConj_assoc]; rw [hkpHiWords]
  wp_steps
  refine SepWP.weaken_pre (P' :=
      ((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
        ((s.sp + 288#64) ↦₆₄ (x.bundleA + 120#64)) ∗
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
        memRegion (s.sp + 696#64) 72 ∗
        ((s.sp + 776#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 808#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        memRegion (s.sp + 1864#64) 24 ∗
        ((s.sp + 1904#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 2336#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((s.sp + 2496#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 4064#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 4096#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((s.sp + 5632#64) ↦ₛ ekAPk) ∗
        ((s.sp + 5664#64) ↦ₛ ekASk) ∗
        ((x.bundleA + 88#64) ↦₆₄ x.kpkPtr) ∗
        ((x.bundleA + 96#64) ↦₆₄ 1568#64) ∗
        ((x.bundleA + 120#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        F) (by
    try simp only [sepConj_assoc]
    rw [words4_to_slice_rest (hkpp (s.sp + 776#64) (s.sp + 784#64) (s.sp + 792#64) (s.sp + 800#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hkps (s.sp + 808#64) (s.sp + 816#64) (s.sp + 824#64) (s.sp + 832#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hekp (s.sp + 664#64) (s.sp + 672#64) (s.sp + 680#64) (s.sp + 688#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hspk (s.sp + 1904#64) (s.sp + 1912#64) (s.sp + 1920#64) (s.sp + 1928#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hidk (s.sp + 2336#64) (s.sp + 2344#64) (s.sp + 2352#64) (s.sp + 2360#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hspk (s.sp + 2496#64) (s.sp + 2504#64) (s.sp + 2512#64) (s.sp + 2520#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hkpp (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hkps (s.sp + 4096#64) (s.sp + 4104#64) (s.sp + 4112#64) (s.sp + 4120#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hekp (s.sp + 5632#64) (s.sp + 5640#64) (s.sp + 5648#64) (s.sp + 5656#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (heks (s.sp + 5664#64) (s.sp + 5672#64) (s.sp + 5680#64) (s.sp + 5688#64)
          (by bv_omega) (by bv_omega) (by bv_omega)),
        words4_to_slice_rest (hidk (x.bundleA + 120#64) (x.bundleA + 128#64) (x.bundleA + 136#64) (x.bundleA + 144#64)
          (by bv_omega) (by bv_omega) (by bv_omega))]
    have hm696 :
        ((s.sp + 696#64) ↦₆₄ eks0) ∗ (((s.sp + 704#64) ↦₆₄ eks1) ∗
          (((s.sp + 712#64) ↦₆₄ eks2) ∗ (((s.sp + 720#64) ↦₆₄ eks3) ∗
            (((s.sp + 728#64) ↦₆₄ spk0) ∗ (((s.sp + 736#64) ↦₆₄ spk1) ∗
              (((s.sp + 744#64) ↦₆₄ spk2) ∗ (((s.sp + 752#64) ↦₆₄ spk3) ∗
                ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64))))))))) ⊢
        memRegion (s.sp + 696#64) 72 := by
      have h1 :
          (((s.sp + 696#64) ↦₆₄ eks0) ∗ ((s.sp + 704#64) ↦₆₄ eks1) ∗
            ((s.sp + 712#64) ↦₆₄ eks2) ∗ ((s.sp + 720#64) ↦₆₄ eks3)) ⊢
          memRegion (s.sp + 696#64) 32 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
          words4_entails_mr32 (s.sp + 696#64) eks0 eks1 eks2 eks3
      have h2 :
          (((s.sp + 728#64) ↦₆₄ spk0) ∗ ((s.sp + 736#64) ↦₆₄ spk1) ∗
            ((s.sp + 744#64) ↦₆₄ spk2) ∗ ((s.sp + 752#64) ↦₆₄ spk3)) ⊢
          memRegion (s.sp + 728#64) 32 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
          words4_entails_mr32 (s.sp + 728#64) spk0 spk1 spk2 spk3
      simpa only [sepConj_assoc] using
        mr_fold (s.sp + 696#64) (s.sp + 728#64) 32 40 72 h1
          (mr_fold (s.sp + 728#64) (s.sp + 760#64) 32 8 40 h2 (mr_of_u64 _ _) rfl (by bv_omega))
          rfl (by bv_omega)
    have hm1864 :
        ((s.sp + 1864#64) ↦₆₄ u7) ∗ (((s.sp + 1872#64) ↦₈ b63) ∗
          (memRegion (s.sp + 1873#64) 7 ∗
            (((s.sp + 1880#64) ↦₈ b0) ∗ (((s.sp + 1881#64) ↦₈ b1) ∗
              (((s.sp + 1882#64) ↦₈ b2) ∗
                (((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
                  memRegion (s.sp + 1887#64) 1)))))) ⊢
        memRegion (s.sp + 1864#64) 24 := by
      have h7 :
          (((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗
            ((s.sp + 1882#64) ↦₈ b2) ∗ ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) ⊢
          memRegion (s.sp + 1880#64) 7 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
          sevenHi_entails_mr7 (s.sp + 1880#64) b0 b1 b2 (b6 ++ b5 ++ b4 ++ b3)
      simpa only [sepConj_assoc] using
        mr_fold (s.sp + 1864#64) (s.sp + 1872#64) 8 16 24 (mr_of_u64 _ _)
          (mr_fold (s.sp + 1872#64) (s.sp + 1873#64) 1 15 16 (mr_of_u8 _ _)
            (mr_fold (s.sp + 1873#64) (s.sp + 1880#64) 7 8 15 (Entails.refl _)
              (mr_fold (s.sp + 1880#64) (s.sp + 1887#64) 7 1 8 h7 (Entails.refl _) rfl (by bv_omega))
              rfl (by bv_omega))
            rfl (by bv_omega))
          rfl (by bv_omega)
    try simp only [sepConj_assoc]
    refine entails_by_focus (by sep_frame) hm696 ?_
    refine entails_by_focus (by sep_frame) hm1864 ?_
    sep_frame) ?_
  have hbase : (blkPl_521).base = lsmpl.base 521 := rfl
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [calleeSavedVRegs, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem sepWPp_call_fs_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ∗ F ⊢ oom sf)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      (sf.trace = s.trace → sf.fs.files = s.fs.files) →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom :=
  sepWPp_call_fs hFs hcall hpc hrun hsp_align hlr
    (Entails.trans hpre (sepConj_mono_left
      (Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (sepConj_comm _ _)))))
    hpan hexit hoom hnext

theorem sepWPp_call_cli_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ∗ F ⊢ oom sf)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      sf.symtab = s.symtab →
      (sf.trace = s.trace → sf.fs.files = s.fs.files) →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom :=
  sepWPp_call_cli hFs hcall hpc hrun hsp_align hlr
    (Entails.trans hpre (sepConj_mono_left
      (Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (sepConj_comm _ _)))))
    hpan hexit hoom hnext

theorem inInitiatePlaced_of_call [LibsignalPlacement] {s0 s sf : State} {k0 k1 : Nat}
    (hctrl : InInitiatePlaced s0 s k0)
    (hpc : sf.pc = initPcPlaced k1)
    (hrun : sf.status = .Running)
    (hsp : sf.sp = s.sp)
    (hcs : CalleeSavedPreserved s sf)
    (hkf : s.mem.KeepsFrozen sf.mem)
    (hfiles : sf.fs.files = s.fs.files) :
    InInitiatePlaced s0 sf k1 := by
  rcases hcs with ⟨hx19, _, _, _, _, _, _, _, _, _, hfp, hvregs⟩
  exact inInitiatePlaced_of_step hctrl hpc hrun hsp hfp hx19 hvregs hkf hfiles

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
end
