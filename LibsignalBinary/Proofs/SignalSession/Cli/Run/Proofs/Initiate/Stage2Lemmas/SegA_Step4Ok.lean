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
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA_DropErr
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 2 `get_identity_key_pair` Success Unpacking (`0x0464 → 0x0584`)

Verifies `segA_step4_ok` and `segA_step4_ok_ext` when `get_identity_key_pair` returns `ans = .ok kp`,
unpacking the 64-byte `(kp.pk, kp.sk)` payload, dropping and deallocating `box`, and reaching
`0x0584` for `segC_ok`.
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

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 400000 in
/-- Stage 2 `get_identity_key_pair` success branch (`+1124 → +1412` on `ans = .ok kp`,
`initProgExt`): unpacks `(kp.pk, kp.sk)`, drops and frees `box`, and reaches `0x0584`. -/
theorem segA_step4_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {box : BitVec 64}
    {stk : Nat} {s0 s : State}
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
    (hnext : ∀ (sf : State) (b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8)
        (u1 u2 u3 u4 u5 u6 u7 : BitVec 64),
      InInitiateExt img ext s0 sf 0x0584 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 22#5) = 0#64 →
      sf.readReg64 (.gpr 26#5) = u1 →
      sf.readReg64 (.gpr 27#5) = u2 →
      sf.readReg64 (.gpr 25#5) = u3 →
      sf.readReg64 (.gpr 28#5) = u4 →
      sf.readReg64 (.gpr 24#5) = u5 →
      sf.readReg64 (.gpr 21#5) = u6 →
      (∀ a : BitVec 64,
        (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
          ((a + 7#64) ↦₆₄ u1) ∗ ((a + 15#64) ↦₆₄ u2) ∗
          ((a + 23#64) ↦₆₄ u3) ∗ ((a + 31#64) ↦₆₄ u4) =
          (a ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((a + 32#64) ↦ₛ kp.privateKey.bytes.toList.take 7)) →
      (∀ a : BitVec 64,
        (a ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
          ((a + 7#64) ↦₆₄ u5) ∗ ((a + 15#64) ↦₆₄ u6) ∗
          ((a + 23#64) ↦₆₄ u7) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦ₛ kp.privateKey.bytes.toList)) →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (A.pool ∗
          ((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
          memRegion (s.sp + 1472#64) 16 ∗
          ((s.sp + 1864#64) ↦₆₄ u7) ∗
          ((s.sp + 1872#64) ↦₈ b63) ∗
          memRegion (s.sp + 1873#64) 7 ∗
          ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
          ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
          memRegion (s.sp + 1887#64) 1 ∗
          memRegion (s.sp + 5632#64) 64 ∗
          memRegion (s.sp + 5696#64) 8 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        memRegion (s.sp + 120#64) 8 ∗
        ((s.sp + 1472#64) ↦₆₄ box) ∗
        ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗
        memRegion (s.sp + 1864#64) 24 ∗
        idKeyPairOutAt A (s.sp + 5632#64) (.ok kp) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b63, u1, u2, u3, u4, u5, u6, u7, hkpOut, hkpLo, hkpHi⟩ :=
    exists_kpSplit (List.Vector.toList_length kp.identityKey.publicKey.bytes)
      (List.Vector.toList_length kp.privateKey.bytes)
  apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutDrop_ext ext himg hctrl.inv.1)
  unfold idKeyPairOutAt
  have h5633_eq : ∀ rest : SepProp,
      ((s.sp + 5633#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((s.sp + 5665#64) ↦ₛ kp.privateKey.bytes.toList) ∗ rest =
      ((s.sp + 5633#64) ↦₈ b0) ∗ ((s.sp + 5634#64) ↦₈ b1) ∗ ((s.sp + 5635#64) ↦₈ b2) ∗
        ((s.sp + 5636#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
        ((s.sp + 5640#64) ↦₆₄ u1) ∗ ((s.sp + 5648#64) ↦₆₄ u2) ∗
        ((s.sp + 5656#64) ↦₆₄ u3) ∗ ((s.sp + 5664#64) ↦₆₄ u4) ∗
        ((s.sp + 5672#64) ↦₆₄ u5) ∗ ((s.sp + 5680#64) ↦₆₄ u6) ∗
        ((s.sp + 5688#64) ↦₆₄ u7) ∗ ((s.sp + 5696#64) ↦₈ b63) ∗ rest := fun rest => by
    have hO := hkpOut (s.sp + 5632#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hO
    simpa only [sepConj_assoc] using congrArg (· ∗ rest) hO
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [h5633_eq,
      mr_split (s.sp + 1864#64) (s.sp + 1872#64) 8 16 24 rfl (by bv_omega),
      mr_split (s.sp + 1872#64) (s.sp + 1880#64) 8 8 16 rfl (by bv_omega),
      mr_split (s.sp + 1872#64) (s.sp + 1873#64) 1 7 8 rfl (by bv_omega),
      mr_split (s.sp + 1880#64) (s.sp + 1887#64) 7 1 8 rfl (by bv_omega),
      memRegion_8_eq_exists (s.sp + 120#64),
      memRegion_8_eq_exists (s.sp + 1864#64),
      memRegion_1_eq_exists (s.sp + 1872#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
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
    conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 5633#64 5634#64 5635#64 5636#64 5637#64 5638#64 5639#64 b0 b1 b2 b3 b4 b5 b6,
      sepConj_assoc]
    wp_steps
    -- Reassociate `sp + 1880` from `sevenHi` to `sevenLo` for `STR W8, [SP, #1880]`
    conv => arg 4; simp only [sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 c0 c1 c2 c3 c4 c5 c6,
      sepConj_assoc]
    wp_steps
    -- Restore `sp + 1880` to `sevenHi` for `STUR W9, [X8, #3]`
    conv => arg 4; simp only [← sevenHi_to_Lo_rest s.sp 1880#64 1881#64 1882#64 1883#64 1884#64 1885#64 1886#64 b0 b1 b2 b3 c4 c5 c6,
      sepConj_assoc]
    wp_steps
    refine SepWP.weaken_pre (P' :=
      ((img.base + idKeyPairFutVtOff) ↦₆₄ᵣ dropAddr) ∗
        (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗
          ((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
          memRegion (s.sp + 1472#64) 16 ∗
          ((s.sp + 1864#64) ↦₆₄ u7) ∗
          ((s.sp + 1872#64) ↦₈ b63) ∗
          memRegion (s.sp + 1873#64) 7 ∗
          ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
          ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
          memRegion (s.sp + 1887#64) 1 ∗
          memRegion (s.sp + 5632#64) 64 ∗
          memRegion (s.sp + 5696#64) 8 ∗ F)) (by
      have hm1472 := mr_fold (s.sp + 1472#64) (s.sp + 1480#64) 8 8 16
        (mr_of_u64 _ box) (mr_of_u64 _ (img.base + idKeyPairFutVtOff)) rfl (by bv_omega)
      have hm5632 :
          ((s.sp + 5632#64) ↦₈ 0#8) ∗
            ((((s.sp + 5633#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
              ((s.sp + 5637#64) ↦₈ b4) ∗ ((s.sp + 5638#64) ↦₈ b5) ∗ ((s.sp + 5639#64) ↦₈ b6)) ∗
              ((((s.sp + 5640#64) ↦₆₄ u1) ∗ ((s.sp + 5648#64) ↦₆₄ u2) ∗
                ((s.sp + 5656#64) ↦₆₄ u3) ∗ ((s.sp + 5664#64) ↦₆₄ u4)) ∗
                (((s.sp + 5672#64) ↦₆₄ u5) ∗ (((s.sp + 5680#64) ↦₆₄ u6) ∗
                  ((s.sp + 5688#64) ↦₆₄ u7))))) ⊢
          memRegion (s.sp + 5632#64) 64 := by
        refine mr_fold (s.sp + 5632#64) (s.sp + 5633#64) 1 63 64 (mr_of_u8 _ _) ?_ rfl (by bv_omega)
        refine mr_fold (s.sp + 5633#64) (s.sp + 5640#64) 7 56 63
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            sevenLo_entails_mr7 (s.sp + 5633#64) (b3 ++ b2 ++ b1 ++ b0) b4 b5 b6) ?_
          rfl (by bv_omega)
        refine mr_fold (s.sp + 5640#64) (s.sp + 5672#64) 32 24 56
          (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
            words4_entails_mr32 (s.sp + 5640#64) u1 u2 u3 u4) ?_
          rfl (by bv_omega)
        refine mr_fold (s.sp + 5672#64) (s.sp + 5680#64) 8 16 24 (mr_of_u64 _ _) ?_ rfl (by bv_omega)
        exact mr_fold (s.sp + 5680#64) (s.sp + 5688#64) 8 8 16
          (mr_of_u64 _ _) (mr_of_u64 _ _) rfl (by bv_omega)
      have hm5696 : ((s.sp + 5696#64) ↦₈ b63) ∗ memRegion (s.sp + 5697#64) 7 ⊢
          memRegion (s.sp + 5696#64) 8 :=
        mr_fold (s.sp + 5696#64) (s.sp + 5697#64) 1 7 8
          (mr_of_u8 _ _) (Entails.refl _) rfl (by bv_omega)
      simp only [sepConj_assoc] at hm1472 hm5632 hm5696 ⊢
      refine entails_by_focus (by sep_frame) hm1472 ?_
      refine entails_by_focus (by sep_frame) hm5632 ?_
      refine entails_by_focus (by sep_frame) hm5696 ?_
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
    refine segA_drop_and_dealloc_ext (v22 := 0#64) (v26 := u1) (v27 := u2) (v25 := u3)
      (v28 := u4) (v24 := u5) (v21 := u6) himg hh hStore hstk hstk64 hctrl1
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
      (hnext sf b0 b1 b2 b3 b4 b5 b6 b63 u1 u2 u3 u4 u5 u6 u7 hctrlf htrf
        hx22f hx26f hx27f hx25f hx28f hx24f hx21f hkpLo hkpHi)
    try simp only [arm64_norm]
    sep_frame

/-- Stage 2 `get_identity_key_pair` success branch (`+1124 → +1412` on `ans = .ok kp`, `initProg`). -/
theorem segA_step4_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {kp : IdentityKeyPair} {box : BitVec 64}
    {stk : Nat} {s0 s : State}
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
    (hnext : ∀ (sf : State) (b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8)
        (u1 u2 u3 u4 u5 u6 u7 : BitVec 64),
      InInitiate img W s0 sf 0x0584 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 22#5) = 0#64 →
      sf.readReg64 (.gpr 26#5) = u1 →
      sf.readReg64 (.gpr 27#5) = u2 →
      sf.readReg64 (.gpr 25#5) = u3 →
      sf.readReg64 (.gpr 28#5) = u4 →
      sf.readReg64 (.gpr 24#5) = u5 →
      sf.readReg64 (.gpr 21#5) = u6 →
      (∀ a : BitVec 64,
        (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
          ((a + 7#64) ↦₆₄ u1) ∗ ((a + 15#64) ↦₆₄ u2) ∗
          ((a + 23#64) ↦₆₄ u3) ∗ ((a + 31#64) ↦₆₄ u4) =
          (a ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((a + 32#64) ↦ₛ kp.privateKey.bytes.toList.take 7)) →
      (∀ a : BitVec 64,
        (a ↦ₛ kp.privateKey.bytes.toList.take 7) ∗
          ((a + 7#64) ↦₆₄ u5) ∗ ((a + 15#64) ↦₆₄ u6) ∗
          ((a + 23#64) ↦₆₄ u7) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦ₛ kp.privateKey.bytes.toList)) →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (A.pool ∗
          ((s.sp + 120#64) ↦₆₄ (s.sp + 664#64)) ∗
          memRegion (s.sp + 1472#64) 16 ∗
          ((s.sp + 1864#64) ↦₆₄ u7) ∗
          ((s.sp + 1872#64) ↦₈ b63) ∗
          memRegion (s.sp + 1873#64) 7 ∗
          ((s.sp + 1880#64) ↦₈ b0) ∗ ((s.sp + 1881#64) ↦₈ b1) ∗ ((s.sp + 1882#64) ↦₈ b2) ∗
          ((s.sp + 1883#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗
          memRegion (s.sp + 1887#64) 1 ∗
          memRegion (s.sp + 5632#64) 64 ∗
          memRegion (s.sp + 5696#64) 8 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (A.pool ∗ A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
        memRegion (s.sp + 120#64) 8 ∗
        ((s.sp + 1472#64) ↦₆₄ box) ∗
        ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗
        memRegion (s.sp + 1864#64) 24 ∗
        idKeyPairOutAt A (s.sp + 5632#64) (.ok kp) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) :=
  segA_step4_ok_ext (ext := cliHookExterns W) himg hh.toExt
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
    (fun sf b0 b1 b2 b3 b4 b5 b6 b63 u1 u2 u3 u4 u5 u6 u7 hctrlf =>
      hnext sf b0 b1 b2 b3 b4 b5 b6 b63 u1 u2 u3 u4 u5 u6 u7 (InInitiateExt.toLegacy hctrlf))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
