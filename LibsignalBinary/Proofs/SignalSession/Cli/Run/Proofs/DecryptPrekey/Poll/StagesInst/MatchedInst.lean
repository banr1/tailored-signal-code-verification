/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathBMain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Path B Stage P2 Instantiation

Proves `stageP2Matched_framed_cli_ok : StageP2MatchedFramedCliStmt` and
`stageP2Matched_framed_ext_ok : StageP2MatchedFramedExtStmt` by unpacking the post-`StageP1`
spatial bundle, invoking `Matched.stageP2_matched_ok_framed`, and folding both the `hmismatch` exit
and the `hmatch` Stage P3 continuation.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false

private theorem cliExterns_blackBox_raw (W : CliHooks) :
    cliExterns W "subtle::black_box::<u8>" =
      some CryptoVerification.LibsignalSession.blackBoxHook := by
  simpa [Rust.withPanics, Rust.isPanicSymbol] using Poll.cliExterns_blackBox W

set_option maxHeartbeats 800000 in
/-- Instantiation of `StageP2MatchedFramedCliStmt` on `cliExterns W` via
`Matched.stageP2_matched_ok_framed`. -/
theorem stageP2Matched_framed_cli_ok : StageP2MatchedFramedCliStmt := by
  intro W img B S Scope y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_frame Q Qpan
    himg hh hbase hcoins hMatch hinv htr hsp1 hsp0 hsp_root hpc1 hrun1 halign1 hregs
    hpan hmismatch hmatch
  rcases hregs with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, hx28, hx29, hvregs1⟩
  have hunpack := matched_entry_unpack (Scope := Scope) img y sess s0 sp rngPtr v_a8 v_b8 v_d0
  refine sepWPp_conseq_pre (sepConj_mono_left hunpack) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w => ?_
  let F_in := matchedInnerFrame img y rngPtr sp
  have hpre_assoc :
      (stageP2MatchedPre E2E.HooksE.A0 img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ F_in) ∗ F_frame =
      stageP2MatchedPre E2E.HooksE.A0 img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ (F_in ∗ F_frame) := by
    dsimp only [stageP2MatchedPre]
    ac_rfl
  rw [hpre_assoc]
  refine sepWPp_entails_post ?_
  exact stageP2_matched_ok_framed
    (cliAllocContracts hh)
    hh.memcpyRO
    (cliExterns_blackBox_raw W)
    (cliDropSessionStructure3_ok hh)
    himg hbase s0 s1
    sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
    y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
    (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img)
    y.g.peerA (y.g.msgA + 0xc8#64)
    w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
    w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
    w.u_2a8 (v_b8.extractLsb' 0 32)
    y.g.msg.messageVersion y.g.msg.message.messageVersion
    w.b_4f1 0#8 0#8 0#8 w.b_3ac
    y.g.msg.baseKey y.g.msg.identityKey
    g ⟨some sess⟩ sess (F_in ∗ F_frame)
    rfl hMatch.1 hMatch.2
    hinv htr hsp1 hsp_root hpc1 hrun1 halign1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
    (x29_eq_sp_add_c70 hsp0 hx29)
    (fun sf Pf hp => by
      rw [← sepConj_assoc Pf F_in F_frame]
      exact hpan sf (Pf ∗ F_in) (poll_panicOomProp_of_matched F_in hp))
    (fun hne sf Pf hpcf hrunf hsteps hspf htrf hcsf hvregsf hinvf hent => by
      have hfold := matched_mismatch_fold img y s0 sp rngPtr (v_b8.extractLsb' 0 32) w
      have hpost_assoc :
          stageP2MatchedMismatchPost E2E.HooksE.A0 img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
            (y.g.stores + 0x78#64) (kyberVt img)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey (F_in ∗ F_frame) =
          stageP2MatchedMismatchPost E2E.HooksE.A0 img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
            (y.g.stores + 0x78#64) (kyberVt img)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey F_in ∗ F_frame := by
        dsimp only [stageP2MatchedMismatchPost]
        ac_rfl
      rw [hpost_assoc] at hent
      exact ⟨_, Entails.trans hent (sepConj_mono_left hfold),
        hmismatch hne sf _ hpcf hrunf hsteps (hspf.trans hsp0) htrf hcsf
          (hvregsf.trans hvregs1) hinvf (Entails.refl _)⟩)
    (fun heq s2 recG opkHi kyberPreKeyId signedPreKeyId _hgcur hextra hsteps
        hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2 hvregs2 hinv2 => by
      have hx29_2' := x29_eq_sp0_sub_60 hsp0 hx29_2
      refine sepWPp_lift_entails_post ?_
      refine sepWPp_conseq_pre
        (matched_match_fold img y sess s0 s2 sp rngPtr v_d0 g recG
          opkHi kyberPreKeyId signedPreKeyId F_frame hcoins
          hsp2 hx19_2 hx27_2) ?_
      exact hmatch heq s2 g recG y.g.msgA y.g.msgG.msg
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
        opkHi kyberPreKeyId signedPreKeyId
        hextra
        (Entails.of_eq (by rw [preKeyMsgAt_eq_base_idKey_sep]; ac_rfl))
        hsteps hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2'
        (hvregs2.trans hvregs1) hinv2)

set_option maxHeartbeats 800000 in
/-- Proves `StageP2MatchedFramedExtAt img A ext` from `AllocContractsX`, stacked `memcpyRO`
(`CliExt.memHookStack`), `CliExt.blackBoxSpec`, and `drop_session_structure3` via
`Matched.stageP2_matched_ok_framed_ext32`. -/
theorem stageP2Matched_framed_ext32_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {dssStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack
        CryptoVerification.SignalSession.CliExt.memHookStack))
    (hbb : HookSat ext "subtle::black_box::<u8>" CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (hdrop_ss : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      ((dropSessionStructureLocal2SpecWithStack dssStack A).inImage img))
    (hdss : dssStack ≤ rootStack := by decide) :
    StageP2MatchedFramedExtAt img A ext := by
  intro B S Scope y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_frame Q Qpan
    hbase hcoins hMatch hinv htr hsp1 hsp0 hsp_root hpc1 hrun1 halign1 hregs
    hpan hmismatch hmatch
  rcases hregs with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, hx28, hx29, hvregs1⟩
  have hunpack := matched_entry_unpack_ext (Scope := Scope) img y sess s0 sp rngPtr v_a8 v_b8 v_d0
  refine sepWPp_conseq_pre (sepConj_mono_left hunpack) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w => ?_
  let F_in := matchedInnerFrameExt img y rngPtr sp
  have hpre_assoc :
      (stageP2MatchedPre A img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ F_in) ∗ F_frame =
      stageP2MatchedPre A img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
        y.g.peerA (y.g.msgA + 0xc8#64)
        w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
        w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
        w.u_2a8 (v_b8.extractLsb' 0 32)
        y.g.msg.messageVersion y.g.msg.message.messageVersion
        w.b_4f1 0#8 0#8 0#8 w.b_3ac
        y.g.msg.baseKey y.g.msg.identityKey g ⟨some sess⟩ (F_in ∗ F_frame) := by
    dsimp only [stageP2MatchedPre]
    ac_rfl
  rw [hpre_assoc]
  refine sepWPp_entails_post ?_
  exact stageP2_matched_ok_framed_ext32
    hA hRO hbb hdrop_ss hdss
    himg hbase s0 s1
    sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
    y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
    (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img)
    y.g.peerA (y.g.msgA + 0xc8#64)
    w.u_80 w.u_88 w.u_90 v_a8 (y.fut + 0x390#64) v_d0
    w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
    w.u_2a8 (v_b8.extractLsb' 0 32)
    y.g.msg.messageVersion y.g.msg.message.messageVersion
    w.b_4f1 0#8 0#8 0#8 w.b_3ac
    y.g.msg.baseKey y.g.msg.identityKey
    g ⟨some sess⟩ sess (F_in ∗ F_frame)
    rfl hMatch.1 hMatch.2
    hinv htr hsp1 hsp_root hpc1 hrun1 halign1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
    (x29_eq_sp_add_c70 hsp0 hx29)
    (fun sf Pf hp => by
      rw [← sepConj_assoc Pf F_in F_frame]
      exact hpan sf (Pf ∗ F_in) (poll_panicOomProp_of_matched F_in hp))
    (fun hne sf Pf hpcf hrunf hsteps hspf htrf hcsf hvregsf hinvf hent => by
      have hfold := matched_mismatch_fold_ext img y s0 sp rngPtr (v_b8.extractLsb' 0 32) w
      have hpost_assoc :
          stageP2MatchedMismatchPost A img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
            (y.g.stores + 0x78#64) (kyberVt img)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey (F_in ∗ F_frame) =
          stageP2MatchedMismatchPost A img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
            y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
            (y.g.stores + 0x78#64) (kyberVt img)
            y.g.peerA (y.g.msgA + 0xc8#64)
            w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
            w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
            w.u_2a8 (v_b8.extractLsb' 0 32)
            y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
            y.g.msg.baseKey y.g.msg.identityKey F_in ∗ F_frame := by
        dsimp only [stageP2MatchedMismatchPost]
        ac_rfl
      rw [hpost_assoc] at hent
      exact ⟨_, Entails.trans hent (sepConj_mono_left hfold),
        hmismatch hne sf _ hpcf hrunf hsteps (hspf.trans hsp0) htrf hcsf
          (hvregsf.trans hvregs1) hinvf (Entails.refl _)⟩)
    (fun heq s2 recG opkHi kyberPreKeyId signedPreKeyId _hgcur hextra hsteps
        hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2 hvregs2 hinv2 => by
      have hx29_2' := x29_eq_sp0_sub_60 hsp0 hx29_2
      refine sepWPp_lift_entails_post ?_
      refine sepWPp_conseq_pre
        (matched_match_fold_ext img y sess s0 s2 sp rngPtr v_d0 g recG
          opkHi kyberPreKeyId signedPreKeyId F_frame hcoins
          hsp2 hx19_2 hx27_2) ?_
      exact hmatch heq s2 g recG y.g.msgA y.g.msgG.msg
        (((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt A y.g.msgG y.g.msgA y.g.msg)
        opkHi kyberPreKeyId signedPreKeyId
        hextra
        (Entails.of_eq (by rw [preKeyMsgAt_eq_base_idKey_sep]; ac_rfl))
        hsteps hpc2 hrun2 hsp2 halign2 htr2 hx19_2 hx27_2 hx29_2'
        (hvregs2.trans hvregs1) hinv2)

/-- Instantiation of `StageP2MatchedFramedExtStmt` on `cliExternsWith ext` under `CliExternsOk P A ext`
and `RunHooksExt img A (cliExternsWith ext)`. -/
theorem stageP2Matched_framed_ext_ok : StageP2MatchedFramedExtStmt := by
  intro P A ext hOk img himg hh
  exact stageP2Matched_framed_ext32_ok
    (dssStack := CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Stack)
    himg hh.alloc hh.memcpyRO (Slots.ext_blackBox hOk)
    (CryptoVerification.InImageLift.subroutine_ok_inImage_of_subroutine_ok img
      (GenP3.drop_session_structure3_of_allocHooks_ext (Slots.ext_allocHooks hOk)))
    (by decide)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
