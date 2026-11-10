/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegC_Ok
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Helpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage 2 Prefix Steps (`0x0390 → 0x0464`): Ephemeral Key Derivation and `get_identity_key_pair` Poll

Verifies the three Stage 2 preparation steps on `initProg` and `initProgExt`:
1. `segA_step1_coins` (`+912 → +952`): fresh `SessionRecord` header and 32-byte `coins_fill`.
2. `segA_step2_ek` (`+952 → +1036`): X25519 scalar clamping, `derive_public_key_bytes`, and `StaticSecret::drop`.
3. `segA_step3_poll` (`+1036 → +1124`): `get_identity_key_pair` shim and poll.
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

set_option maxHeartbeats 1200000 in
/-- Stage 2 Step A1 (`+912 → +952`, `initProgExt`): initializes `initFreshRecAt s.sp`, zeroes
`[s.sp + 5632 .. 5664)`, and invokes `signal_session_coins_fill` (`pos: 0 → 32`). -/
theorem segA_step1_coins_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hFs : TraceFsSound (initProgExt img ext))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x0390)
    (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 0#64 - 1#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 8#64)
    (hx27 : s.readReg64 (.gpr 27#5) = 0#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiateExt img ext s0 sf 0x03b8 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (initFreshRecAt s.sp ∗
          coinsCursorAt img x.coinsP x.coins 32 ∗
          ((s.sp + 5632#64) ↦ₛ (padCoins x.coins).toList.take 32) ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (coinsCursorAt img x.coinsP x.coins 0 ∗
        memRegion (s.sp + 296#64) 32 ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  rw [mr_32_eq_words4 (s.sp + 296#64), mr_32_eq_words4 (s.sp + 5632#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  iterate 8 (apply sepWPp_exists_left; intro _)
  apply sepWPp_of_sepWP_fs hFs
    (mid := (initProgExt img ext).fnAddr cliCoinsFillName)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 912 40
    have hpc0 : s.pc = (initProgExt img ext).fnAddr cliInitiateName + 912#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    have hcall_cf := coinsFill_fnAddr_eq img.base (cliExternsWith ext)
    have hent : initEntryExt img ext =
        (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
    have hprog : initProgExt img ext =
        libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc0 hcall_cf ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    refine SepWP.weaken_pre (P' :=
      coinsCursorAt img x.coinsP x.coins 0 ∗
        initFreshRecAt s.sp ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F) (by
      have hm5632 := words4_entails_mr32 (s.sp + 5632#64) 0#64 0#64 0#64 0#64
      rw [initFreshRecAt_eq_fsp s.sp]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        at hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog] at hcall_cf ⊢
    let cfG : CoinsFillGhost :=
      { dst := s.sp + 5632#64, len := 32, p₀ := x.coinsP, coins := x.coins, pos := 0 }
    refine sepWPp_call_cli hFs
      (hCoins (coinsFillStack_le_sub hstk) (sub_frame_le_63 hstk64))
      (x := cfG)
      (F := initFreshRecAt s.sp ∗ F)
      (ret_pc := initPcExt img ext 0x03b8)
      (by simp only [arm64_norm, hcall_cf]; try bv_omega)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (by simp only [arm64_norm, initPcExt, hent]; try bv_omega)
      (by
        have hinv1 : ImgCallInv img _ :=
          imgCallInv_of_keepsFrozen hctrl.inv hkf1 (by simp only [arm64_norm])
        dsimp only [coinsFillSpec, Spec.inImage, cfG]
        simp only [sepConj_assoc]
        refine Entails.pure_right ⟨hinv1.1, hinv1.2⟩ ?_
        refine Entails.pure_right
          ⟨by simp only [arm64_norm]; try bv_omega,
           by simp only [arm64_norm],
           hcoinsLt, by decide⟩ ?_
        try simp only [arm64_norm]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
      (fun _ _ => rfl)
      (fun _ => by dsimp only [coinsFillSpec, Spec.inImage]; exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
    dsimp only [coinsFillSpec, Spec.inImage, cfG]
    simp only [arm64_norm, Nat.zero_add, List.drop_zero, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; rintro ⟨htr2, _⟩
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiateExt img ext s0 s2 0x03b8 :=
      inInitiateExt_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 hsym2 (hf2 htr2)
    rcases hcs2 with ⟨_, _, hx21_2, _, hx23_2, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx23] at hx21_2 hx23_2
    refine sepWPp_weaken_pre ?_
      (hnext s2 hctrl2 htr2_eq (by bv_omega) hx23_2)
    try simp only [hsp2, sepConj_assoc]
    sep_frame

/-- Stage 2 Step A1 (`+912 → +952`, `initProg`). -/
theorem segA_step1_coins {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiate img W s0 s 0x0390)
    (htrace : s.trace = s0.trace)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hx25 : s.readReg64 (.gpr 25#5) = 0#64 - 1#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 8#64)
    (hx27 : s.readReg64 (.gpr 27#5) = 0#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ sf : State,
      InInitiate img W s0 sf 0x03b8 →
      sf.trace = s0.trace →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (initFreshRecAt s.sp ∗
          coinsCursorAt img x.coinsP x.coins 32 ∗
          ((s.sp + 5632#64) ↦ₛ (padCoins x.coins).toList.take 32) ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (coinsCursorAt img x.coinsP x.coins 0 ∗
        memRegion (s.sp + 296#64) 32 ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) :=
  segA_step1_coins_ext (ext := cliHookExterns W) (RunGlue.traceFsSound_cli W img.base)
    hCoins hcoinsLt hstk hstk64 (InInitiate.toExt hctrl) htrace hx22 hx23 hx25 hx26 hx27 hpanic
    (fun sf hctrl2 => hnext sf (InInitiateExt.toLegacy hctrl2))

set_option maxHeartbeats 1600000 in
/-- Stage 2 Step A2 (`+952 → +1036`, `initProgExt`): clamps 32 coin bytes into `ekASk`, derives
`ekAPk` at `s.sp + 664#64`, stores `ekASk` at `s.sp + 696#64`, and zeroizes `s.sp + 4064#64`. -/
theorem segA_step2_ek_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {S : RunSem} {B : RunBudgets}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hFs : TraceFsSound (initProgExt img ext))
    (hLocal : Stage2CalleesExt img P A ext)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hctrl : InInitiateExt img ext s0 s 0x03b8)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (ekASk ekAPk : List (BitVec 8)),
      InInitiateExt img ext s0 sf 0x040c →
      sf.trace = s0.trace →
      (let ekKP := keyPairOf P.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
       ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList) →
      sf.readReg64 (.gpr 20#5) = s.sp + 4064#64 →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 4064#64) 32 ∗
          memRegion (s.sp + 5632#64) 32 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        memRegion (s.sp + 4064#64) 32 ∗
        ((s.sp + 5632#64) ↦ₛ (padCoins x.coins).toList.take 32) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hbase_stk : 516880 ≤ stk - cliInitiateFrame := stk_sub_ge_base hstk
  have hext_fits : extHookStack ≤ 516880 := by dsimp only [extHookStack]; decide
  have hext_stk : extHookStack ≤ stk - cliInitiateFrame := Nat.le_trans hext_fits hbase_stk
  have hstk_le64 : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  let rawVec : List.Vector (BitVec 8) 32 :=
    ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
  let ekKP := keyPairOf P.C rawVec
  let ekASk := ekKP.privateKey.bytes.toList
  let ekAPk := ekKP.publicKey.bytes.toList
  have hkpEq := keyPairOf_eq P.C rawVec
  obtain ⟨b0, b31, mid, hmid, hraw, hclamp⟩ := clampScalar_split rawVec
  have hekSkLen : ekASk.length = 32 := ekKP.privateKey.bytes.property
  obtain ⟨eks0, eks1, eks2, eks3, heks⟩ := exists_keyWords4_of_len32 (bs := ekASk) hekSkLen
  have hrawList : (padCoins x.coins).toList.take 32 = [b0] ++ mid ++ [b31] := hraw
  have hclampSk : ekASk = [b0 &&& 0xf8#8] ++ mid ++ [(b31 &&& 0x7f#8) ||| 0x40#8] := by
    dsimp only [ekASk]; rw [hkpEq.1]; exact hclamp
  rw [hrawList, pointsToBytes_ends (s.sp + 5632#64) b0 b31 mid hmid,
      mr_32_eq_words4 (s.sp + 4064#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply sepWPp_exists_left; intro t3
  apply sepWPp_exists_left; intro t2
  apply sepWPp_exists_left; intro t1
  apply sepWPp_exists_left; intro t0
  apply sepWPp_of_sepWP_fs hFs
    (mid := (initProgExt img ext).fnAddr cliDerivePubKeyBytesName)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 952 60
    have hpc0 : s.pc = (initProgExt img ext).fnAddr cliInitiateName + 952#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    have hcall_dp := derivePubKeyBytes_fnAddr_eq img.base (cliExternsWith ext)
    have hent : initEntryExt img ext =
        (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
    have hprog : initProgExt img ext =
        libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
    dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc0 hcall_dp ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExternsWith ext))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    refine SepWP.weaken_pre (P' :=
      memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        ((s.sp + 4064#64) ↦₆₄ t0) ∗ ((s.sp + 4072#64) ↦₆₄ t1) ∗
        ((s.sp + 4080#64) ↦₆₄ t2) ∗ ((s.sp + 4088#64) ↦₆₄ t3) ∗
        ((s.sp + 5632#64) ↦₆₄ eks0) ∗ ((s.sp + 5640#64) ↦₆₄ eks1) ∗
        ((s.sp + 5648#64) ↦₆₄ eks2) ∗ ((s.sp + 5656#64) ↦₆₄ eks3) ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F) (by
      have hends :
          ((s.sp + 5632#64) ↦₈ (b0 &&& 0xf8#8)) ∗
            (((s.sp + 5633#64) ↦ₛ mid) ∗
              ((s.sp + 5663#64) ↦₈ ((b31 &&& 0x7f#8) ||| 0x40#8))) ⊢
          ((s.sp + 5632#64) ↦₆₄ eks0) ∗
            (((s.sp + 5640#64) ↦₆₄ eks1) ∗
              (((s.sp + 5648#64) ↦₆₄ eks2) ∗ ((s.sp + 5656#64) ↦₆₄ eks3))) := by
        apply Entails.of_eq
        have h1 := (pointsToBytes_ends (s.sp + 5632#64) (b0 &&& 0xf8#8)
          ((b31 &&& 0x7f#8) ||| 0x40#8) mid hmid).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
        rw [h1, ← hclampSk,
            heks (s.sp + 5632#64) (s.sp + 5640#64) (s.sp + 5648#64) (s.sp + 5656#64)
              (by bv_omega) (by bv_omega) (by bv_omega)]
      have hclamp0 :
          BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b0 &&& 1065151889656#64) = b0 &&& 0xf8#8 := by
        bv_bits
      have hclamp31 :
          BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b31 >>> 0 &&& 63#64) =
            (b31 &&& 0x7f#8) ||| 0x40#8 := by
        bv_bits
      rw [hclamp0, hclamp31]
      try simp only [sepConj_assoc] at hends ⊢
      refine entails_by_focus (by sep_frame) hends ?_
      sep_frame) ?_
    wp_steps
    refine SepWP.weaken_pre (P' :=
      ((s.sp + 4064#64) ↦ₛ (Ratchet.clampScalar rawVec).toList) ∗
        memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        memRegion (s.sp + 5632#64) 32 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F) (by
      have hm5632 := words4_entails_mr32 (s.sp + 5632#64) eks0 eks1 eks2 eks3
      rw [← hkpEq.1]
      change _ ⊢ ((s.sp + 4064#64) ↦ₛ ekASk) ∗ _
      rw [heks (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
        (by bv_omega) (by bv_omega) (by bv_omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog] at hcall_dp ⊢
    refine sepWPp_call_cli hFs
      (hLocal.derivePubKeyBytes_withStack hext_stk hstk_le64)
      (x := { secret := s.sp + 4064#64, sec := Ratchet.clampScalar rawVec, out := s.sp + 664#64 })
      (F := memRegion (s.sp + 696#64) 32 ∗ memRegion (s.sp + 5632#64) 32 ∗ F)
      (ret_pc := initPcExt img ext 0x03f4)
      (by simp only [arm64_norm, hcall_dp]; try bv_omega)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (by simp only [arm64_norm, initPcExt, hent]; try bv_omega)
      (by
        have hinv1 : ImgCallInv img _ :=
          imgCallInv_of_keepsFrozen hctrl.inv hkf1 (by simp only [arm64_norm])
        dsimp only [derivePublicKeyBytesStackSpec, Spec.inImage]
        simp only [sepConj_assoc]
        refine Entails.pure_right ⟨hinv1.1, hinv1.2⟩ ?_
        refine Entails.pure_right
          ⟨by simp only [arm64_norm], by simp only [arm64_norm]; try bv_omega⟩ ?_
        try simp only [arm64_norm]
        sep_frame)
      (fun sf => by
        dsimp only [derivePublicKeyBytesStackSpec, Spec.inImage]
        exact hpanic sf _ (initPanicPost_of_false A img S x stk _))
      (fun _ _ => rfl)
      (fun _ => by
        dsimp only [derivePublicKeyBytesStackSpec, Spec.inImage]
        exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
    dsimp only [derivePublicKeyBytesStackSpec, Spec.inImage]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; intro htr2
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiateExt img ext s0 s2 0x03f4 :=
      inInitiateExt_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 hsym2 (hf2 htr2)
    rcases hcs2 with ⟨_, hx20_2, hx21_2, _, hx23_2, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx21, hx23] at hx20_2 hx21_2 hx23_2
    have h4064_eq : ((s.sp + 4064#64) ↦ₛ (Ratchet.clampScalar rawVec).toList) =
        ((s.sp + 4064#64) ↦₆₄ eks0) ∗ ((s.sp + 4072#64) ↦₆₄ eks1) ∗
        ((s.sp + 4080#64) ↦₆₄ eks2) ∗ ((s.sp + 4088#64) ↦₆₄ eks3) := by
      rw [← hkpEq.1]
      exact heks (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
        (by bv_omega) (by bv_omega) (by bv_omega)
    have h664_eq : ((s.sp + 664#64) ↦ₛ (P.C.pubKey (Ratchet.clampScalar rawVec)).toList) =
        ((s.sp + 664#64) ↦ₛ ekAPk) := by
      dsimp only [ekAPk]; rw [hkpEq.2]
    rw [h4064_eq, h664_eq, mr_32_eq_words4 (s.sp + 696#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    iterate 4 (apply sepWPp_exists_left; intro _)
    rw [← hsp2] at hx20_2 hx21_2 hx23_2 ⊢
    apply sepWPp_of_sepWP_fs hFs
      (mid := (initProgExt img ext).fnAddr staticSecretDropName)
    · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
        (Rust.withPanics (cliExternsWith ext)) hfn
        (num% (ls_off% "libsignal_cli_handshake::initiate")) 1012 24
      replace hpc2 : s2.pc = (initProgExt img ext).fnAddr cliInitiateName + 1012#64 := hpc2
      have hsp_al2 : s2.spAligned = true := by simpa only [arm64_norm, hsp2] using hsp_al
      have hsp_mask2 : ((s2.sp &&& 15#64) == 0#64) = true := hsp_al2
      have hcall_sd := staticSecretDrop_fnAddr_eq img.base (cliExternsWith ext)
      have hent2 : initEntryExt img ext =
          (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
      have hprog2 : initProgExt img ext =
          libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
      dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc2 hcall_sd ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase2
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))) = prog2
        reverting [Program.fetch, Program.externAt?, Program.rebase]
      examples_hide_fetches
      wp_steps
      refine SepWP.weaken_pre (P' :=
        memRegion (s.sp + 4064#64) 32 ∗
          ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 5632#64) 32 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F) (by
        have hm4064 := words4_entails_mr32 (s.sp + 4064#64) eks0 eks1 eks2 eks3
        rw [heks (s.sp + 696#64) (s.sp + 704#64) (s.sp + 712#64) (s.sp + 720#64)
          (by bv_omega) (by bv_omega) (by bv_omega)]
        simp only [hsp2, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          at hm4064 ⊢
        refine entails_by_focus (by sep_frame) hm4064 ?_
        sep_frame) ?_
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine ⟨by simp only [arm64_norm], fun hkf3 hfiles3 => ?_⟩
      rw [← hprog2] at hcall_sd ⊢
      rw [hsp2] at hx20_2 hx21_2 hx23_2
      refine sepWPp_call_cli hFs
        (hLocal.staticSecretDrop hext_stk hstk_le64)
        (x := s.sp + 4064#64)
        (F := ((s.sp + 664#64) ↦ₛ ekAPk) ∗ ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 5632#64) 32 ∗ F)
        (ret_pc := initPcExt img ext 0x040c)
        (by simp only [arm64_norm, hcall_sd]; try bv_omega)
        (by simp only [arm64_norm, *])
        (by simpa only [arm64_norm, hsp2] using hsp_al)
        (by simp only [arm64_norm, initPcExt, hent2]; try bv_omega)
        (by
          have hinv3 : ImgCallInv img _ :=
            imgCallInv_of_keepsFrozen hctrl2.inv hkf3 (by simp only [arm64_norm])
          dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, zeroizeSecretSpec]
          simp only [sepConj_assoc]
          refine Entails.pure_right ⟨hinv3.1, hinv3.2⟩ ?_
          refine Entails.pure_right (by simp only [arm64_norm]) ?_
          try simp only [arm64_norm, hsp2]
          sep_frame)
        (fun sf => by
          dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, zeroizeSecretSpec]
          exact hpanic sf _ (initPanicPost_of_false A img S x stk _))
        (fun _ _ => rfl)
        (fun _ => by
          dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, zeroizeSecretSpec]
          exact Entails.pure_left False.elim)
        fun s4 hpc4 hrun4 hsp4 hcs4 hkf4 hsym4 hf4 => ?_
      dsimp only [Spec.inImage, LibsignalTripleRatchet.withStack, zeroizeSecretSpec]
      simp only [arm64_norm, hsp2, sepConj_assoc] at hsp4 ⊢
      apply sepWPp_pure_left; intro htr4
      have htr4_eq : s4.trace = s0.trace := by simpa only [arm64_norm, htr2_eq] using htr4
      have hctrl4 : InInitiateExt img ext s0 s4 0x040c :=
        inInitiateExt_after_call hctrl2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [calleeSavedVRegs, arm64_norm]) hkf3 hfiles3
          hpc4 hrun4 (by simp only [arm64_norm, *]) hcs4 hkf4 hsym4 (hf4 htr4)
      rcases hcs4 with ⟨_, hx20_4, hx21_4, _, hx23_4, _, _, _, _, _, _, _⟩
      simp only [arm64_norm, hx20_2, hx21_2, hx23_2] at hx20_4 hx21_4 hx23_4
      apply sepWPp_weaken_pre (P' :=
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 4064#64) 32 ∗
          memRegion (s.sp + 5632#64) 32 ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F) (by
        have hmZero : ((s.sp + 4064#64) ↦ₛ List.replicate 32 0#8) ⊢ memRegion (s.sp + 4064#64) 32 :=
          mr_of_bytes _ _ 32 (by simp)
        refine entails_by_focus (by sep_frame) hmZero ?_
        sep_frame)
      exact hnext s4 ekASk ekAPk hctrl4 htr4_eq ⟨rfl, rfl⟩ hx20_4 hx21_4 hx23_4

set_option maxHeartbeats 1600000 in
/-- Stage 2 Step A2 (`+952 → +1036`, `initProg`). -/
theorem segA_step2_ek {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (hLocal : InitLocalCallees img A W stk)
    (hctrl : InInitiate img W s0 s 0x03b8)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (ekASk ekAPk : List (BitVec 8)),
      InInitiate img W s0 sf 0x040c →
      sf.trace = s0.trace →
      (let ekKP := keyPairOf W.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
       ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList) →
      sf.readReg64 (.gpr 20#5) = s.sp + 4064#64 →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      sf.readReg64 (.gpr 23#5) = s.sp + 128#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 4064#64) 32 ∗
          memRegion (s.sp + 5632#64) 32 ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        memRegion (s.sp + 4064#64) 32 ∗
        ((s.sp + 5632#64) ↦ₛ (padCoins x.coins).toList.take 32) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  let rawVec : List.Vector (BitVec 8) 32 :=
    ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
  let ekKP := keyPairOf W.C rawVec
  let ekASk := ekKP.privateKey.bytes.toList
  let ekAPk := ekKP.publicKey.bytes.toList
  have hkpEq := keyPairOf_eq W.C rawVec
  obtain ⟨b0, b31, mid, hmid, hraw, hclamp⟩ := clampScalar_split rawVec
  have hekSkLen : ekASk.length = 32 := ekKP.privateKey.bytes.property
  obtain ⟨eks0, eks1, eks2, eks3, heks⟩ := exists_keyWords4_of_len32 (bs := ekASk) hekSkLen
  have hrawList : (padCoins x.coins).toList.take 32 = [b0] ++ mid ++ [b31] := hraw
  have hclampSk : ekASk = [b0 &&& 0xf8#8] ++ mid ++ [(b31 &&& 0x7f#8) ||| 0x40#8] := by
    dsimp only [ekASk]; rw [hkpEq.1]; exact hclamp
  rw [hrawList, pointsToBytes_ends (s.sp + 5632#64) b0 b31 mid hmid,
      mr_32_eq_words4 (s.sp + 4064#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply sepWPp_exists_left; intro t3
  apply sepWPp_exists_left; intro t2
  apply sepWPp_exists_left; intro t1
  apply sepWPp_exists_left; intro t0
  apply sepWPp_of_sepWP_fs (RunGlue.traceFsSound_cli W img.base)
    (mid := (initProg img W).fnAddr cliDerivePubKeyBytesName)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExterns W)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 952 60
    have hpc0 : s.pc = (initProg img W).fnAddr cliInitiateName + 952#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    have hcall_dp := derivePubKeyBytes_fnAddr_eq img.base (cliExterns W)
    have hent : initEntry img W =
        (libsignalSessionCode.rebase img.base
          (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName := rfl
    have hprog : initProg img W =
        libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W)) := rfl
    dsimp only [initEntry, initProg, tripleRatchetProgAtExt] at hpc0 hcall_dp ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = fnBase
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (cliExterns W))) = prog
      reverting [Program.fetch, Program.externAt?, Program.rebase]
    examples_hide_fetches
    wp_steps
    refine SepWP.weaken_pre (P' :=
      memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        ((s.sp + 4064#64) ↦₆₄ t0) ∗ ((s.sp + 4072#64) ↦₆₄ t1) ∗
        ((s.sp + 4080#64) ↦₆₄ t2) ∗ ((s.sp + 4088#64) ↦₆₄ t3) ∗
        ((s.sp + 5632#64) ↦₆₄ eks0) ∗ ((s.sp + 5640#64) ↦₆₄ eks1) ∗
        ((s.sp + 5648#64) ↦₆₄ eks2) ∗ ((s.sp + 5656#64) ↦₆₄ eks3) ∗ F) (by
      have hends :
          ((s.sp + 5632#64) ↦₈ (b0 &&& 0xf8#8)) ∗
            (((s.sp + 5633#64) ↦ₛ mid) ∗
              ((s.sp + 5663#64) ↦₈ ((b31 &&& 0x7f#8) ||| 0x40#8))) ⊢
          ((s.sp + 5632#64) ↦₆₄ eks0) ∗
            (((s.sp + 5640#64) ↦₆₄ eks1) ∗
              (((s.sp + 5648#64) ↦₆₄ eks2) ∗ ((s.sp + 5656#64) ↦₆₄ eks3))) := by
        apply Entails.of_eq
        have h1 := (pointsToBytes_ends (s.sp + 5632#64) (b0 &&& 0xf8#8)
          ((b31 &&& 0x7f#8) ||| 0x40#8) mid hmid).symm
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
        rw [h1, ← hclampSk,
            heks (s.sp + 5632#64) (s.sp + 5640#64) (s.sp + 5648#64) (s.sp + 5656#64)
              (by bv_omega) (by bv_omega) (by bv_omega)]
      have hclamp0 :
          BitVec.zeroExtend 8 (BitVec.zeroExtend 64 b0 &&& 1065151889656#64) = b0 &&& 0xf8#8 := by
        bv_bits
      have hclamp31 :
          BitVec.zeroExtend 8 (64#64 ||| BitVec.zeroExtend 64 b31 >>> 0 &&& 63#64) =
            (b31 &&& 0x7f#8) ||| 0x40#8 := by
        bv_bits
      rw [hclamp0, hclamp31]
      try simp only [sepConj_assoc] at hends ⊢
      refine entails_by_focus (by sep_frame) hends ?_
      sep_frame) ?_
    wp_steps
    refine SepWP.weaken_pre (P' :=
      ((s.sp + 4064#64) ↦ₛ (Ratchet.clampScalar rawVec).toList) ∗
        memRegion (s.sp + 664#64) 32 ∗
        memRegion (s.sp + 696#64) 32 ∗
        memRegion (s.sp + 5632#64) 32 ∗ F) (by
      have hm5632 := words4_entails_mr32 (s.sp + 5632#64) eks0 eks1 eks2 eks3
      rw [← hkpEq.1]
      change _ ⊢ ((s.sp + 4064#64) ↦ₛ ekASk) ∗ _
      rw [heks (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
        (by bv_omega) (by bv_omega) (by bv_omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hm5632 ⊢
      refine entails_by_focus (by sep_frame) hm5632 ?_
      sep_frame) ?_
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog] at hcall_dp ⊢
    refine sepWPp_call_cli (RunGlue.traceFsSound_cli W img.base)
      hLocal.derivePubKeyBytes
      (x := { secret := s.sp + 4064#64, sec := Ratchet.clampScalar rawVec, out := s.sp + 664#64 })
      (F := memRegion (s.sp + 696#64) 32 ∗ memRegion (s.sp + 5632#64) 32 ∗ F)
      (ret_pc := initPc img W 0x03f4)
      (by simp only [arm64_norm, hcall_dp]; try bv_omega)
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (by simp only [arm64_norm, initPc, hent]; try bv_omega)
      (by
        dsimp only [derivePublicKeyBytesSpec]
        simp only [sepConj_assoc]
        refine Entails.pure_right
          ⟨by simp only [arm64_norm], by simp only [arm64_norm]; try bv_omega⟩ ?_
        try simp only [arm64_norm, sepConj_assoc]
        sep_frame)
      (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
      (fun _ _ => rfl)
      (fun _ => by dsimp only [derivePublicKeyBytesSpec]; exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
    dsimp only [derivePublicKeyBytesSpec]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; intro htr2
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiate img W s0 s2 0x03f4 :=
      inInitiate_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 hsym2 (hf2 htr2)
    rcases hcs2 with ⟨_, hx20_2, hx21_2, _, hx23_2, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx21, hx23] at hx20_2 hx21_2 hx23_2
    have h4064_eq : ((s.sp + 4064#64) ↦ₛ (Ratchet.clampScalar rawVec).toList) =
        ((s.sp + 4064#64) ↦₆₄ eks0) ∗ ((s.sp + 4072#64) ↦₆₄ eks1) ∗
        ((s.sp + 4080#64) ↦₆₄ eks2) ∗ ((s.sp + 4088#64) ↦₆₄ eks3) := by
      rw [← hkpEq.1]
      exact heks (s.sp + 4064#64) (s.sp + 4072#64) (s.sp + 4080#64) (s.sp + 4088#64)
        (by bv_omega) (by bv_omega) (by bv_omega)
    have h664_eq : ((s.sp + 664#64) ↦ₛ (W.C.pubKey (Ratchet.clampScalar rawVec)).toList) =
        ((s.sp + 664#64) ↦ₛ ekAPk) := by
      dsimp only [ekAPk]; rw [hkpEq.2]
    rw [h4064_eq, h664_eq, mr_32_eq_words4 (s.sp + 696#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    iterate 4 (apply sepWPp_exists_left; intro _)
    rw [← hsp2] at hx20_2 hx21_2 hx23_2 ⊢
    apply sepWPp_of_sepWP_fs (RunGlue.traceFsSound_cli W img.base)
      (mid := (initProg img W).fnAddr staticSecretDropName)
    · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
        (Rust.withPanics (cliExterns W)) hfn
        (num% (ls_off% "libsignal_cli_handshake::initiate")) 1012 24
      replace hpc2 : s2.pc = (initProg img W).fnAddr cliInitiateName + 1012#64 := hpc2
      have hsp_al2 : s2.spAligned = true := by simpa only [arm64_norm, hsp2] using hsp_al
      have hsp_mask2 : ((s2.sp &&& 15#64) == 0#64) = true := hsp_al2
      have hcall_sd := staticSecretDrop_fnAddr_eq img.base (cliExterns W)
      have hent2 : initEntry img W =
          (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName := rfl
      have hprog2 : initProg img W =
          libsignalSessionCode.rebase img.base (Rust.withPanics (cliExterns W)) := rfl
      dsimp only [initEntry, initProg, tripleRatchetProgAtExt] at hpc2 hcall_sd ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))).fnAddr cliInitiateName = fnBase2
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExterns W))) = prog2
        reverting [Program.fetch, Program.externAt?, Program.rebase]
      examples_hide_fetches
      wp_steps
      refine SepWP.weaken_pre (P' :=
        memRegion (s.sp + 4064#64) 32 ∗
          ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 5632#64) 32 ∗ F) (by
        have hm4064 := words4_entails_mr32 (s.sp + 4064#64) eks0 eks1 eks2 eks3
        rw [heks (s.sp + 696#64) (s.sp + 704#64) (s.sp + 712#64) (s.sp + 720#64)
          (by bv_omega) (by bv_omega) (by bv_omega)]
        simp only [hsp2, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
          at hm4064 ⊢
        refine entails_by_focus (by sep_frame) hm4064 ?_
        sep_frame) ?_
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine ⟨by simp only [arm64_norm], fun hkf3 hfiles3 => ?_⟩
      rw [← hprog2] at hcall_sd ⊢
      rw [hsp2] at hx20_2 hx21_2 hx23_2
      refine sepWPp_call_cli (RunGlue.traceFsSound_cli W img.base)
        (staticSecretDrop_cli_ok W img)
        (x := s.sp + 4064#64)
        (F := ((s.sp + 664#64) ↦ₛ ekAPk) ∗ ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 5632#64) 32 ∗ F)
        (ret_pc := initPc img W 0x040c)
        (by simp only [arm64_norm, hcall_sd]; try bv_omega)
        (by simp only [arm64_norm, *])
        (by simpa only [arm64_norm, hsp2] using hsp_al)
        (by simp only [arm64_norm, initPc, hent2]; try bv_omega)
        (by
          dsimp only [zeroizeSecretSpec]
          simp only [sepConj_assoc]
          refine Entails.pure_right (by simp only [arm64_norm]) ?_
          try simp only [sepConj_assoc]
          sep_frame)
        (fun sf => hpanic sf _ (initPanicPost_of_false A img S x stk _))
        (fun _ _ => rfl)
        (fun _ => by dsimp only [zeroizeSecretSpec]; exact Entails.pure_left False.elim)
        fun s4 hpc4 hrun4 hsp4 hcs4 hkf4 hsym4 hf4 => ?_
      dsimp only [zeroizeSecretSpec]
      simp only [arm64_norm, hsp2, sepConj_assoc] at hsp4 ⊢
      apply sepWPp_pure_left; intro htr4
      have htr4_eq : s4.trace = s0.trace := by simpa only [arm64_norm, htr2_eq] using htr4
      have hctrl4 : InInitiate img W s0 s4 0x040c :=
        inInitiate_after_call hctrl2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [calleeSavedVRegs, arm64_norm]) hkf3 hfiles3
          hpc4 hrun4 (by simp only [arm64_norm, *]) hcs4 hkf4 hsym4 (hf4 htr4)
      rcases hcs4 with ⟨_, hx20_4, hx21_4, _, hx23_4, _, _, _, _, _, _, _⟩
      simp only [arm64_norm, hx20_2, hx21_2, hx23_2] at hx20_4 hx21_4 hx23_4
      apply sepWPp_weaken_pre (P' :=
        ((s.sp + 664#64) ↦ₛ ekAPk) ∗
          ((s.sp + 696#64) ↦ₛ ekASk) ∗
          memRegion (s.sp + 4064#64) 32 ∗
          memRegion (s.sp + 5632#64) 32 ∗ F) (by
        have hmZero : ((s.sp + 4064#64) ↦ₛ List.replicate 32 0#8) ⊢ memRegion (s.sp + 4064#64) 32 :=
          mr_of_bytes _ _ 32 (by simp)
        refine entails_by_focus (by sep_frame) hmZero ?_
        sep_frame)
      exact hnext s4 ekASk ekAPk hctrl4 htr4_eq ⟨rfl, rfl⟩ hx20_4 hx21_4 hx23_4

set_option maxHeartbeats 1600000 in
/-- Stage 2 Step A3 (`+1036 → +1124`, `initProgExt`): stages bundle fields onto the stack and
invokes `idKeyPairShim` (`idVt + 0x18`) and `idKeyPairPoll` (`futVt + 0x18`). -/
theorem segA_step3_poll_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {opkId : BitVec 32} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (initProgExt img ext))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hctrl : InInitiateExt img ext s0 s 0x040c)
    (htrace : s.trace = s0.trace)
    (hfiles : s0.fs.files = x.F)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 4064#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (box : BitVec 64) (ans : Except Unit IdentityKeyPair),
      InInitiateExt img ext s0 sf 0x0464 →
      sf.trace = s0.trace →
      box ≠ 0#64 →
      ans = StoresGhost.opened.identity.keyPair cliIo.rd x.F →
      sf.readReg64 (.gpr 20#5) = s.sp + 4064#64 →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) sf
        (storesAt A x.stores StoresGhost.opened ∗
          cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
          logOff img ∗ A.pool ∗ initArgsAt img s.sp x s0 ∗
          ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
          ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((s.sp + 772#64) ↦₃₂ opkId) ∗
          A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
          ((s.sp + 1472#64) ↦₆₄ box) ∗
          ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗
          idKeyPairOutAt A (s.sp + 5632#64) ans ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        logOff img ∗ A.pool ∗ initArgsAt img s.sp x s0 ∗
        memRegion (s.sp + 728#64) 48 ∗
        memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 5632#64) 72 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) := by
  have hfn : libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") := cliInitiate_fnOff
  obtain ⟨spk0, spk1, spk2, spk3, hspk⟩ :=
    exists_keyWords4_of_len32 (bs := x.bundle.spk.bytes.toList) x.bundle.spk.bytes.property
  apply sepWPp_with_rodata (fun _ => rodata_idVt_getKeyPairShim_ext ext himg hctrl.inv.1)
  unfold cliBundleBodyAt initArgsAt
  rw [hspk (x.bundleA + 24#64) (x.bundleA + 32#64) (x.bundleA + 40#64) (x.bundleA + 48#64)
        (by bv_omega) (by bv_omega) (by bv_omega),
      mr_split (s.sp + 728#64) (s.sp + 760#64) 32 16 48 rfl (by bv_omega),
      mr_split (s.sp + 760#64) (s.sp + 768#64) 8 8 16 rfl (by bv_omega),
      mr_split (s.sp + 768#64) (s.sp + 772#64) 4 4 8 rfl (by bv_omega),
      mr_32_eq_words4 (s.sp + 728#64),
      memRegion_8_eq_exists (s.sp + 760#64),
      memRegion_4_eq_exists (s.sp + 768#64),
      memRegion_4_eq_exists (s.sp + 772#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  iterate 7 (apply sepWPp_exists_left; intro _)
  apply sepWPp_of_sepWP_fs hFs
    (mid := (initProgExt img ext).fnAddr idKeyPairShimName)
  · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
      (Rust.withPanics (cliExternsWith ext)) hfn
      (num% (ls_off% "libsignal_cli_handshake::initiate")) 1036 60
    have hpc0 : s.pc = (initProgExt img ext).fnAddr cliInitiateName + 1036#64 := hctrl.pc
    have hrun0 : s.status = .Running := hctrl.run
    have hsp_al : s.spAligned = true := spAligned_of_frame hctrl.sp hctrl.spAligned
    have hsp_mask : ((s.sp &&& 15#64) == 0#64) = true := hsp_al
    generalize hshim : (initProgExt img ext).fnAddr idKeyPairShimName = shimAddr
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
    apply sepWP_drop_left
    refine SepWP.weaken_pre (P' :=
      A.pool ∗ stackAt s.sp (stk - cliInitiateFrame) ∗
        storesAt A x.stores StoresGhost.opened ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        logOff img ∗ initArgsAt img s.sp x s0 ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 5632#64) 72 ∗ F) (by
      unfold cliBundleBodyAt initArgsAt
      dsimp only
      rw [hspk (x.bundleA + 24#64) (x.bundleA + 32#64) (x.bundleA + 40#64) (x.bundleA + 48#64)
            (by bv_omega) (by bv_omega) (by bv_omega),
          hspk (s.sp + 728#64) (s.sp + 736#64) (s.sp + 744#64) (s.sp + 752#64)
            (by bv_omega) (by bv_omega) (by bv_omega)]
      simp only [Option.isSome, sepConj_assoc]
      sep_frame) ?_
    apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
    refine ⟨by simp only [arm64_norm], fun hkf1 hfiles1 => ?_⟩
    rw [← hprog]
    refine sepWPp_call_cli hFs
      hStore.idKeyPairShim
      (x := x.stores)
      (F := storesAt A x.stores StoresGhost.opened ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        logOff img ∗ initArgsAt img s.sp x s0 ∗
        ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
        ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
        ((s.sp + 772#64) ↦₃₂ opkId) ∗
        memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 5632#64) 72 ∗ F)
      (ret_pc := initPcExt img ext 0x0448)
      (by simp only [arm64_norm, hshim])
      (by simp only [arm64_norm, *])
      (by simpa only [arm64_norm] using hsp_al)
      (by simp only [arm64_norm, initPcExt, hent]; try bv_omega)
      (by
        have hinv1 : ImgCallInv img _ :=
          imgCallInv_of_keepsFrozen hctrl.inv hkf1 (by simp only [arm64_norm])
        dsimp only [idOwnShimSpec, Spec.inImage]
        simp only [sepConj_assoc]
        refine Entails.pure_right ⟨hinv1.1, hinv1.2⟩ ?_
        refine Entails.pure_right (by simp only [arm64_norm]) ?_
        simp only [arm64_norm]
        sep_frame)
      (fun sf => by
        dsimp only [idOwnShimSpec, Spec.inImage]
        exact hpanic sf _ (initPanicPost_of_allocFailed A img S x stk
          (by simpa only [arm64_norm] using htrace) _))
      (fun _ _ => rfl)
      (fun _ => by dsimp only [idOwnShimSpec, Spec.inImage]; exact Entails.pure_left False.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hkf2 hsym2 hf2 => ?_
    dsimp only [idOwnShimSpec, Spec.inImage]
    simp only [arm64_norm, sepConj_assoc] at hsp2 ⊢
    apply sepWPp_pure_left; rintro ⟨hx1_2, hbox_ne, _, htr2⟩
    set box := s2.readReg64 .x0
    have htr2_eq : s2.trace = s0.trace := by simpa only [arm64_norm, htrace] using htr2
    have hctrl2 : InInitiateExt img ext s0 s2 0x0448 :=
      inInitiateExt_after_call hctrl
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [calleeSavedVRegs, arm64_norm]) hkf1 hfiles1
        hpc2 hrun2 (by simp only [arm64_norm, *]) hcs2 hkf2 hsym2 (hf2 htr2)
    rcases hcs2 with ⟨_, hx20_2, hx21_2, _, _, _, _, _, _, _, _, _⟩
    simp only [arm64_norm, hx20, hx21] at hx20_2 hx21_2
    apply sepWPp_with_rodata (fun _ => rodata_idKeyPairFutPoll_ext ext himg hctrl2.inv.1)
    rw [mr_split (s.sp + 1472#64) (s.sp + 1480#64) 8 8 16 rfl (by bv_omega),
        memRegion_8_eq_exists (s.sp + 1472#64),
        memRegion_8_eq_exists (s.sp + 1480#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    iterate 2 (apply sepWPp_exists_left; intro _)
    apply sepWPp_of_sepWP_fs hFs
      (mid := (initProgExt img ext).fnAddr idKeyPairPollName)
    · code_fetches_range CryptoVerification.libsignalSessionCode cliInitiateStage2Bin img.base
        (Rust.withPanics (cliExternsWith ext)) hfn
        (num% (ls_off% "libsignal_cli_handshake::initiate")) 1096 28
      have hpc2' : s2.pc = (initProgExt img ext).fnAddr cliInitiateName + 1096#64 := hpc2
      generalize hpoll : (initProgExt img ext).fnAddr idKeyPairPollName = pollAddr
      have hent2 : initEntryExt img ext =
          (libsignalSessionCode.rebase img.base
            (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName := rfl
      have hprog2 : initProgExt img ext =
          libsignalSessionCode.rebase img.base (Rust.withPanics (cliExternsWith ext)) := rfl
      dsimp only [initEntryExt, initProgExt, tripleRatchetProgAtExt] at hpc2' ⊢
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))).fnAddr cliInitiateName = fnBase2
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics (cliExternsWith ext))) = prog2
        reverting [Program.fetch, Program.externAt?, Program.rebase]
      examples_hide_fetches
      wp_steps
      apply sepWP_drop_left
      refine SepWP.weaken_pre (P' :=
        idOwnFutBoxAt box x.stores 0#8 ∗
          dirAt A x.stores StoresGhost.opened.identity.own ∗
          memRegion (s.sp + 5632#64) 72 ∗
          logOff img ∗ A.pool ∗ stackAt s.sp (stk - cliInitiateFrame) ∗
          storesRestAt A x.stores StoresGhost.opened ∗
          cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
          initArgsAt img s.sp x s0 ∗
          ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
          ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((s.sp + 772#64) ↦₃₂ opkId) ∗
          A.live box 16 8 ∗
          ((s.sp + 1472#64) ↦₆₄ box) ∗
          ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗ F) (by
        rw [storesAt_eq_own_sep]
        simp only [Option.isSome, sepConj_assoc]
        sep_frame) ?_
      apply SepWP.done (by simp only [arm64_norm, *]; try bv_omega) (by simp only [arm64_norm, *])
      refine ⟨by simp only [arm64_norm], fun hkf3 hfiles3 => ?_⟩
      rw [← hprog2]
      obtain ⟨hownLen, hownWr, hownGetLt, hownEq⟩ := idKeyPairPoll_own_facts hinitOk
      let pollG : IdOwnPollGhost :=
        { fut := box
          out := s.sp + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own }
      refine sepWPp_call_cli hFs
        hStore.idKeyPairPoll
        (x := pollG)
        (F := storesRestAt A x.stores StoresGhost.opened ∗
          cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
          initArgsAt img s.sp x s0 ∗
          ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
          ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((s.sp + 772#64) ↦₃₂ opkId) ∗
          A.live box 16 8 ∗
          ((s.sp + 1472#64) ↦₆₄ box) ∗
          ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗ F)
        (ret_pc := initPcExt img ext 0x0464)
        (by simp only [arm64_norm, hpoll])
        (by simp only [arm64_norm, *])
        (by simpa only [arm64_norm, hsp2] using hsp_al)
        (by simp only [arm64_norm, initPcExt, hent2]; try bv_omega)
        (by
          have hinv3 : ImgCallInv img _ :=
            imgCallInv_of_keepsFrozen hctrl2.inv hkf3 (by simp only [arm64_norm])
          have hf3_x := hfiles3.trans (hctrl2.files0.trans hfiles)
          dsimp only [idKeyPairPollSpec, Spec.inImage, pollG]
          simp only [sepConj_assoc]
          refine Entails.pure_right ⟨hinv3.1, hinv3.2⟩ ?_
          refine Entails.pure_right
            ⟨by simp only [arm64_norm]; rfl,
             by simp only [arm64_norm]; try bv_omega,
             hownLen, hownWr, by rw [hf3_x]; exact hownGetLt⟩ ?_
          try simp only [arm64_norm, hsp2]
          sep_frame)
        (fun sf => by
          dsimp only [idKeyPairPollSpec, Spec.inImage]
          exact hpanic sf _ (initPanicPost_of_allocFailed A img S x stk
            (by simpa only [arm64_norm] using htr2_eq) _))
        (fun _ _ => rfl)
        (fun _ => by dsimp only [idKeyPairPollSpec, Spec.inImage]; exact Entails.pure_left False.elim)
        fun s4 hpc4 hrun4 hsp4 hcs4 hkf4 hsym4 hf4 => ?_
      dsimp only [idKeyPairPollSpec, Spec.inImage, pollG]
      simp only [arm64_norm, hsp2, sepExists_sepConj_left, sepConj_assoc] at hsp4 ⊢
      apply sepWPp_exists_left; intro ans
      apply sepWPp_pure_left; rintro ⟨hans, htr4⟩
      have htr4_eq : s4.trace = s0.trace := by simpa only [arm64_norm, htr2_eq] using htr4
      have hf2_x : s2.fs.files = x.F := hctrl2.files0.trans hfiles
      have hans_eq : ans = StoresGhost.opened.identity.keyPair cliIo.rd x.F := by
        rw [hans, hf2_x]; exact hownEq
      have hctrl4 : InInitiateExt img ext s0 s4 0x0464 :=
        inInitiateExt_after_call hctrl2
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [calleeSavedVRegs, arm64_norm]) hkf3 hfiles3
          hpc4 hrun4 (by simp only [arm64_norm, *]) hcs4 hkf4 hsym4 (hf4 htr4)
      rcases hcs4 with ⟨_, hx20_4, hx21_4, _, _, _, _, _, _, _, _, _⟩
      simp only [arm64_norm, hx20_2, hx21_2] at hx20_4 hx21_4
      refine sepWPp_weaken_pre ?_
        (hnext s4 box ans hctrl4 htr4_eq hbox_ne hans_eq hx20_4 hx21_4)
      rw [storesAt_eq_own_sep]
      try simp only [Option.isSome, sepConj_assoc]
      sep_frame

/-- Stage 2 Step A3 (`+1036 → +1124`, `initProg`). -/
theorem segA_step3_poll {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {opkId : BitVec 32} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {F : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hStore : InitStoreCallees img A W B stk)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hctrl : InInitiate img W s0 s 0x040c)
    (htrace : s.trace = s0.trace)
    (hfiles : s0.fs.files = x.F)
    (hx20 : s.readReg64 (.gpr 20#5) = s.sp + 4064#64)
    (hx21 : s.readReg64 (.gpr 21#5) = s.sp + 664#64)
    (hx23 : s.readReg64 (.gpr 23#5) = s.sp + 128#64)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (sf : State) (box : BitVec 64) (ans : Except Unit IdentityKeyPair),
      InInitiate img W s0 sf 0x0464 →
      sf.trace = s0.trace →
      box ≠ 0#64 →
      ans = StoresGhost.opened.identity.keyPair cliIo.rd x.F →
      sf.readReg64 (.gpr 20#5) = s.sp + 4064#64 →
      sf.readReg64 (.gpr 21#5) = s.sp + 664#64 →
      SepWPp (initProg img W) (s0.readReg64 .lr) sf
        (storesAt A x.stores StoresGhost.opened ∗
          cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
          logOff img ∗ A.pool ∗ initArgsAt img s.sp x s0 ∗
          ((s.sp + 728#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
          ((s.sp + 760#64) ↦₆₄ (x.bundleA + 88#64)) ∗
          ((s.sp + 768#64) ↦₃₂ (if x.bundle.opk.isSome then 1#32 else 0#32)) ∗
          ((s.sp + 772#64) ↦₃₂ opkId) ∗
          A.live box 16 8 ∗ idOwnFutBoxAt box x.stores 1#8 ∗
          ((s.sp + 1472#64) ↦₆₄ box) ∗
          ((s.sp + 1480#64) ↦₆₄ (img.base + idKeyPairFutVtOff)) ∗
          idKeyPairOutAt A (s.sp + 5632#64) ans ∗
          stackAt s.sp (stk - cliInitiateFrame) ∗ F)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s
      (storesAt A x.stores StoresGhost.opened ∗
        cliBundleBodyAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr opkId ∗
        logOff img ∗ A.pool ∗ initArgsAt img s.sp x s0 ∗
        memRegion (s.sp + 728#64) 48 ∗
        memRegion (s.sp + 1472#64) 16 ∗
        memRegion (s.sp + 5632#64) 72 ∗
        stackAt s.sp (stk - cliInitiateFrame) ∗ F)
      Q Qp (initOom s0) :=
  segA_step3_poll_ext (B := B) (ext := cliHookExterns W) himg (RunGlue.traceFsSound_cli W img.base)
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
    hinitOk (InInitiate.toExt hctrl) htrace hfiles hx20 hx21 hx23 hpanic
    (fun sf box ans hctrl4 => hnext sf box ans (InInitiateExt.toLegacy hctrl4))

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
