/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage4OverInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.WrapperOverPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable CLI Poll Over-Path (`D2(c)`) Stage Instantiation Bundle

Assembles the `[LibsignalPlacement]` and `[LibsignalFullPlacement]` CLI Poll `D2(c)` stage
witnesses (`closureBaseStagesCli_placed_inst`, `d2cStages_placed_inst`, and
`decPkD2cSlotOk_placed_of_seams`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel
open ProofLib.ProgramReflection SepProp CryptoVerification.E2E.Bin CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 1200000 in
theorem stageP3PrevEmptyVRegs_cli_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hLog519 : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcc : ChainClone3OkPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hscc : SenderChainClone3OkPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hroot : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C E2E.HooksE.A0 0#64
          uuidTryParse (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))))
    (hDropSS3 : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)))
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (rest : List (BitVec 8))
    (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpPollEntryPlaced + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
        (s' : State) (P_s' : SepProp),
      st.version = msgVer →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
      pt.length ≤ ptCap.toNat →
      ptCap.toNat < 2 ^ 63 →
      ptPtr ≠ 0#64 →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s s' →
      s'.pc = dpPollEntryPlaced + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      calleeSavedVRegs s' = calleeSavedVRegs s0 →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x27 = ctxPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
      (P_s' ⊢
        stageP3DispatchOkMidPrevEmpty_placed E2E.HooksE.A0 s0 s coroPtr outPtr initErrsPtr
          ptCap ptPtr g pt b_2c0 G' (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
        genP3S5PostFrame_placed E2E.HooksE.A0 s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (coinsAfterPlaced cur rest
            (decryptDraws W.C st msg.senderRatchetKey rest))) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
        (genP3S5PanicProp W.C W.Q.K rem loc st msg msgVer rest s0))
    (hErr : ∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
      st.version = msgVer →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt false G' →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmpty_placed E2E.HooksE.A0 s0 s coroPtr outPtr e ∗
        genP3S5PostFrame_placed E2E.HooksE.A0 s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (coinsAfterPlaced cur rest
            (decryptDraws W.C st msg.senderRatchetKey rest))) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame))
    (hVerNe : ∀ (sf : State) (P_f : SepProp),
      st.version ≠ msgVer →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmpty_placed E2E.HooksE.A0 s0 s coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFrame_placed E2E.HooksE.A0 s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAtPlaced cur rest)) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame)) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
      (LsTokenInit ∗
        genP3Pre_placed E2E.HooksE.A0 s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        Matched.stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
        F_frame)
      Q
      (genP3S5PanicProp W.C W.Q.K rem loc st msg msgVer rest s0) := by
  let A := E2E.HooksE.A0
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let C := W.C
  let ctl : BitVec 64 := 0#64
  let K := W.Q.K
  have hC := StageP3CalleesM3Placed.of_cliExternsPlaced mmpl gh W hh hLog519
  refine stageP3_clone_vregs_prefix_placed_steps C K ext hC hcc hscc
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0) F_frame Q
    hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre (P' := (genP3PostPlaced A s.sp
      (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st
      rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr
      g b_2c0)) ∗ F_frame) (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      Matched.stageP3Sub5ExtraPrePrevEmpty A s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗
        (F_dec ∗ F_frame)) (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot s0 s s1 coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
      (sepConj_mono_left (postTryDecrypt_entails_s5DispatchPrevEmpty_placed s0 s coroPtr ctxPtr outPtr
        initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG (genP3S5Model C K rem loc msg rest st).2
        st rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_prevEmpty_placed_ok ext hC.shim hC.alloc hC.dealloc hC.memcpy
        hC.grow hDropSS3 hC.logClosure hC.panic s0 s2 coroPtr outPtr initErrsPtr hinit_ne e he_npan
        b_2c0 g G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed at herr
      have herr_post : stageP3ErrPostPrevEmptyM3Placed A s0 s2 coroPtr outPtr e =
          stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmptyM3Placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_ hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      change _ ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr e ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))
      exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState s0 s2 coroPtr outPtr pt
        G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres hpt_le hpt_lt hpt_ne
        (hsteps02.trans hsteps2') hpc' hrun' hsp' htr' (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      change _ ⊢ stageP3DispatchOkMidPrevEmptyPlaced A s0 s coroPtr outPtr initErrsPtr
          ptCap ptPtr g pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
        genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))
      unfold stageP3DispatchOkMidPrevEmptyPlaced; rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced Matched.stageP3Sub5ExtraPrePrevEmpty; rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ =>
          P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
            (P3P4.SepWPp.weaken_frame (Entails.of_eq (GenP3.stackAt_root_split_grow s.sp)) (by sep_focus)
              (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_)))
    have hver_ne := stageP3_ver_ne_prevEmpty_placed_ok ext hC.shim hC.alloc hC.dealloc hC.grow
      hDropSS3 hC.logClosure hC.panic s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hinit_ne msgVer
      b_2c0 g G₁ recG st hcro1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    change _ ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
      stageP3ErrPostPrevEmptyM3Placed A s0 s coroPtr outPtr (.invalidMessage .preKey .decryptionFailed) ∗
      genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
        rem loc msgG msg (coinsAtPlaced cur rest)
    unfold genP3S5PostFramePlaced; exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP3GenStepsVRegs_cli_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hLog519 : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcc : ChainClone3OkPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hscc : SenderChainClone3OkPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hroot : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 508)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (pollTryDecryptPlacedSpecTPTight W.C E2E.HooksE.A0 0#64
          uuidTryParse (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))))
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpPollEntryPlaced + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
        (s' : State) (P_s' : SepProp),
      st.version = msgVer →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt true G' →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .ok pt →
      pt.length ≤ ptCap.toNat →
      ptCap.toNat < 2 ^ 63 →
      ptPtr ≠ 0#64 →
      Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s s' →
      s'.pc = dpPollEntryPlaced + 0x34dc#64 →
      s'.status = .Running →
      s'.sp = s.sp →
      s'.trace = s0.trace →
      calleeSavedVRegs s' = calleeSavedVRegs s0 →
      s'.readReg64 .x19 = coroPtr →
      s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 →
      s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x27 = ctxPtr →
      s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s'.mem →
      (P_s' ⊢
        stageP3DispatchOkMid_placed E2E.HooksE.A0 s0 s coroPtr outPtr initErrsPtr prevStatesPtr
          ptCap ptPtr pt b_2c0 G' (genP3S5Model W.C W.Q.K rem loc msg rest st).2 ∗
        genP3S5PostFrame_placed E2E.HooksE.A0 s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (coinsAfterPlaced cur rest
            (decryptDraws W.C st msg.senderRatchetKey rest))) →
      SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
        (genP3S5PanicProp W.C W.Q.K rem loc st msg msgVer rest s0))
    (hErr : ∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
      st.version = msgVer →
      CloneRel recG G₁ →
      G₁.AfterTryDecrypt false G' →
      (genP3S5Model W.C W.Q.K rem loc msg rest st).1 = .error e →
      e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost_placed E2E.HooksE.A0 s0 s coroPtr outPtr prevStatesPtr e ∗
        genP3S5PostFrame_placed E2E.HooksE.A0 s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (coinsAfterPlaced cur rest
            (decryptDraws W.C st msg.senderRatchetKey rest))) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame))
    (hVerNe : ∀ (sf : State) (P_f : SepProp),
      st.version ≠ msgVer →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
        memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPost_placed E2E.HooksE.A0 s0 s coroPtr outPtr prevStatesPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFrame_placed E2E.HooksE.A0 s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (coinsAtPlaced cur rest)) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s0.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      Q sf (P_f ∗ F_frame)) :
    SepWPp (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (s0.readReg64 .x30) s
      (LsTokenInit ∗
        genP3Pre_placed E2E.HooksE.A0 s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ∗
        F_frame)
      Q
      (genP3S5PanicProp W.C W.Q.K rem loc st msg msgVer rest s0) := by
  let A := E2E.HooksE.A0
  let ext := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let C := W.C
  let ctl : BitVec 64 := 0#64
  let K := W.Q.K
  have hC := StageP3CalleesM3Placed.of_cliExternsPlaced mmpl gh W hh hLog519
  refine stageP3_clone_vregs_prefix_placed_steps C K ext hC hcc hscc
    s0 s coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    (stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) F_frame Q
    hrc_lt hcro hpc hrun hsp_align hsp_root htr hvregs fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 (SepWPp.weaken_pre (P' := (genP3PostPlaced A s.sp
      (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st
      rem loc msgG msg s1 ∗ (LsTokenInitM3 ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr
      prevStatesPtr b_2c0)) ∗ F_frame) (Entails.of_eq (by ac_rfl)) ?_)
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEqPlaced genP3PostSpatialPlaced; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun hclone_rel => ?_)
    let F_dec : SepProp := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
    refine SepWPp.weaken_pre (P' := (LsTokenInitM3 ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool) ∗
        (F_dec ∗ F_frame)) (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_placed_steps ext C ctl K hroot s0 s s1 coroPtr ctxPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2 hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
      (sepConj_mono_left (postTryDecrypt_entails_s5Dispatch_zero_placed s0 s coroPtr ctxPtr outPtr
        initErrsPtr prevStatesPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG (genP3S5Model C K rem loc msg rest st).2
        st rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPreZeroPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_zero_placed_ok ext hC s0 s2 coroPtr outPtr initErrsPtr
        prevStatesPtr hinit_ne e he_npan b_2c0 G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPreZeroPlaced at herr
      have herr_post : stageP3ErrPost_placed A s0 s2 coroPtr outPtr prevStatesPtr e =
          stageP3ErrPost_placed A s0 s coroPtr outPtr prevStatesPtr e := by
        unfold stageP3ErrPost_placed; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ =>
          hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan
            (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))) hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
    · have hdec_true : G₁.AfterTryDecrypt true G' := by simpa [hres, Except.toBool] using hdec_rel
      have hstack_set : stackAt s.sp growOneSpeStack = memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_placed_ok ext hC.memcpy hC.setState s0 s2 coroPtr outPtr pt
        G' recG (genP3S5Model C K rem loc msg rest st).2 st hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1_placed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres hpt_le hpt_lt hpt_ne
        (hsteps02.trans hsteps2') hpc' hrun' hsp' htr' (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMid_placed; rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced, hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_panicOom; apply sepWPp_frame_closOom_prev1_placed
    unfold genP3PostNePlaced genP3PostSpatialPlaced stageP3Sub5ExtraPre; rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ =>
      P3P4.SepWPp.weaken_frame (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
        (Entails.refl _) (by sep_focus) (SepWPp.pure_elim fun _ =>
          P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus)
            (P3P4.SepWPp.weaken_frame (Entails.of_eq (GenP3.stackAt_root_split_grow s.sp)) (by sep_focus)
              (P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp)) (by sep_focus) ?_)))
    have hver_ne := stageP3_ver_ne_zero_placed_ok ext hC s0 s s1 coroPtr ctxPtr outPtr initErrsPtr
      prevStatesPtr hinit_ne msgVer b_2c0 G₁ recG st hcro1 hpc1 hrun1 hs1_sp hsp_align htr1
      hx9_1 hx19_1 hx24_1 hx27_1
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus) fun sf _ _ ⟨hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFrame_placed LsTokenInit LsTokenInitM3; exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1000000 in
theorem closure_pathA_cli_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hP2A : StageP2PathAQpanCliPlacedStmt mmpl gh W)
    (hLog519 : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hP4 : StageP4PathAPlacedStmt)
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    OverClosurePathAPlacedStmt mmpl gh W := by
  intro X B S Scope hh hReadFile hDeser hinjK hsub hS stk' hneed hstk63
    y s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
    loadRec_of_cliPollSessPlaced_loadRel (σ := σ) hinjK hsub hfPeer hload_rel
  have hcur : (none : Option (SessionRecord (List (BitVec 8)))).bind (·.currentSession) = none := rfl
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 :=
    .inr ⟨trivial, hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518, hs1_files⟩
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed B S stk' y ?_)
  refine hP2A X B S Scope y StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hReadFile hDeser hcoins hdecOk hsub hfPeer hloadS htrusted rfl hfiles1 hro1
    (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_ ?_
  · intro sf Pf hoom _ hm_pan
    rw [← sepConj_assoc] at hm_pan
    exact dpPollOnPanic_of_p3p4Oom_placed stk' y hoom hm_pan
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f) hm_f
    have hm2 : sf.mem ⊨
        (decResAt E2E.HooksE.A0 y.out (.error err) ∗
          storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := exit_entails_dpPollPost_placed B S stk' hneed hstk63 y s0 sf
      StoresGhost.opened (.error err) anyHeap hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 m i k kp reg dk recG whisperMsgPtr whisperG preKeyMsgRem
      hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ _ hvregs2 hro2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    obtain ⟨_hIn0, _hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathA_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    refine sepWPp_genP3_to_tailQpan_placed B S stk' y hpan_model ?_
    refine stageP3GenStepsVRegs_cli_placed_ok mmpl gh W hLog519
      hh (cliChainClone3_placed_ok mmpl gh W hh) (cliSenderChainClone3_placed_ok mmpl gh W hh)
      (hTryDec 0#64)
      s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hro2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' pt ptCap ptPtr s' P_s' hver hcl hdec_rel hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced σ y.g.stores
        hsub hfPeer hdecOk (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathA_p4_cont_placed hP4 B S hh hReadFile hDeser hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          hpm_eq hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s')
    · intro _G₁ _G' e sf P_f hver _hcl _hdec_rel herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y s0 s2 sf
        rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_f hsf_sp htr_f hcs_f hvregs_f
    · intro sf P_f hver_ne hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y s0 s2 sf
        rngPtr whisperMsgPtr whisperG preKeyMsgRem (coinsAtPlaced y.g.coinsP y.g.coins)
        P_f R m.opkId m.kpkId m.spkId (.invalidMessage .preKey .decryptionFailed)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

set_option maxHeartbeats 800000 in
theorem closure_pathB_cli_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hP2 : StageP2MatchedFramedCliPlacedStmt)
    (hLog519 : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hP4 : StageP4MatchedPlacedStmt)
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    OverClosurePathBPlacedStmt mmpl gh W := by
  intro X B S Scope hh hReadFile hDeser hinjK hsub hS stk' hneed hstk63
    y r sess s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hcur hsteps01 htr1 hro1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, hr_eq, hIn, hMatch, _, _, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match hinjK hsub hfPeer hdecOk hload_rel hcur
  subst hr_eq
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  let F_p2 : SepProp :=
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let Fr_tail : SepProp :=
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      ((stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAtPlaced F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed B S stk' y ?_)
  refine hP2 mmpl gh W B S Slots.scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
    hh hReadFile hDeser hcoins hMatch hro1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hroot hpc1 hrun1 hsp_align1 hregs1 ?_ ?_ ?_
  · intro sf Pf hoom _ hm_pan
    have hm_pan' : sf.mem ⊨ (Pf ∗ (F_p2 ∗ Fr_tail)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm_pan
    exact dpPollOnPanic_of_p3p4Oom_placed stk' y hoom hm_pan'
  · intro hrem_ne sf Pf _ _ _ hsf_sp htr_f hcs_f hvregs_f _ hent_f
    let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f)) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt E2E.HooksE.A0 y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAtPlaced_entails_storesAt (A := E2E.HooksE.A0)
      (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt E2E.HooksE.A0 y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAtPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores StoresGhost.opened ∗
        (protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
            stackAt sp rootStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [cliPollStoresKitsAtPlaced, F_p2, Fr_tail]; sep_frame) hm1
    have hm3 := Arm64.Satisfies.mono (sepConj_mono hdec_at (sepConj_mono_left hstores_out)) hm2
    rw [← hstk_split] at hm3
    have hm4 : sf.mem ⊨
        (decResAt E2E.HooksE.A0 y.out (.error err) ∗
          storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm3
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS (err := err) nofun nofun
        (decPkDef_pathB_remId_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_ne)
    have hpost_goal := exit_entails_dpPollPost_placed B S stk' hneed hstk63 y s0 sf
      StoresGhost.opened (.error err)
      (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins)
      hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4
  · intro hrem_eq s2 g recG whisperMsgPtr whisperG preKeyMsgRem
      opkHi kyberPreKeyId signedPreKeyId hex hmsg_fold hsteps12 hpc2 hrun2
      hs2_sp hsp_align2 htr2 _ _ _ hvregs2 hro2
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error .panic →
        (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathB_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS htrusted hMatch hrem_eq hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
         ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
         memRegion (y.fut + 0x2a8#64) 4) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        (LsTokenInit ∗
          genP3Pre_placed E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
             ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
             memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem) ∗ F_p2 ⊢
        LsTokenInit ∗
          genP3Pre_placed E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
          F_p3 := by
      dsimp only [F_p2, F_p3]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3 (sepWPp_genP3_to_tailQpan_placed B S stk' y hpan_model ?_)
    refine stageP3PrevEmptyVRegs_cli_placed_ok mmpl gh W hLog519
      hh (cliChainClone3_placed_ok mmpl gh W hh) (cliSenderChainClone3_placed_ok mmpl gh W hh)
      (hTryDec 0#64) (cliDropSessionStructure4_placed_ok_at mmpl gh W hh (i := 518))
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hro2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' pt ptCap ptPtr s' P_s' hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hro' hent_s'
      exact closure_pathB_p4_cont_placed hP4 mmpl gh W X B S Scope hh hReadFile hDeser hS stk' hneed hstk63
        y sess s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R
        opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
        hfPeer hdecOk hIn hloadS htrusted hMatch hrem_eq hex hmsg_fold
        hs2_files htr20 hs2_sp hsp_sub hsp_align2 hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hro' hent_s'
    · intro G₁ G' e sf P_f hver _ _ herr hne_p hent_f hsf_sp htr_f hcs_f hvregs_f _
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem _ P_f R
        opkHi kyberPreKeyId signedPreKeyId e hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS htrusted hMatch hrem_eq hver herr hne_p)
        hent_f hsf_sp htr_f hcs_f hvregs_f
    · intro sf P_f hver_ne hent_f hsf_sp htr_f hcs_f hvregs_f _
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem _ P_f R
        opkHi kyberPreKeyId signedPreKeyId (.invalidMessage .preKey .decryptionFailed)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_eq hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

/-! ## 3. Grand Assembly: `closureBaseStagesCli_placed_inst`, `d2cStages_placed_inst`, & `decPkD2cSlotOk_placed_of_seams` -/

theorem cliKpkGetPoll_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile)) :
    subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 576)
      (kpkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).kpkGetPoll) := by
  have hDec := SessKit.cliDecimal_placed_ok hh
  have hGet := SessKit.cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hh
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
  exact Store.KpkGetPoll.kpkGetPoll_placed_caller_ok_of_deps
    (callerProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (callerBlk := 518)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (decodeProg := RecordCodecs.Placed.lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decodeBlk := 595)
    (stk := (cliKitStk B).kpkGetPoll)
    hh.alloc hDec hGet (cliDecodeKyberPreKey_placed_ok_of_hooks mmpl gh W hh)
    (hh.fs (lsProg_576 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 576)
    (Nat.le_refl _) (by decide)

theorem closureBaseStagesCli_placed_inst [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hLog519 : subroutine_ok (lsProg_518 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    ClosureBaseStagesCliPlacedStmt mmpl gh W where
  untrustedD2c := closure_untrusted_d2c_trap_placed_ok (stageP1_untrusted_trap_placed_inst hDropNz)
  stageP1Ok := overStageP1OkCli_of_trap (stageP1_ok_trap_placed_inst hDropNz)
  cliTryDecryptPqV1 := hTryDec
  pathA := closure_pathA_cli_placed_ok mmpl gh W
    (stageP2PathA_qpan_cli_placed_of_seams mmpl gh W hDropNz hSpqr h_accept h_accept_err
      (fun B F0 peer hh hread =>
        cliPollSelf_kitPlacedOk mmpl gh W B F0 peer hDropNz hh (jRead := 518) hread)
      (cliKpkGetPoll_placed_ok mmpl gh W))
    hLog519 (stageP4PathA_placed_inst hDropNz) hTryDec
  pathB := closure_pathB_cli_placed_ok mmpl gh W
    stageP2Matched_framed_cli_placed_ok hLog519 (stageP4Matched_placed_inst hDropNz) hTryDec

theorem stageP2Over_qpan_cli_placed_of_pathC [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hP2 : StageP2PathCOverQpanCliPlacedStmt mmpl gh W) :
    StageP2OverQpanCliPlacedStmt mmpl gh W := by
  intro X B S Scope y r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hread hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hro1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 hpan herr hok
  have hr_scope : Slots.scopeIn r := hsub r (scope_of_loadRec_some hfPeer hload)
  exact hP2 X B S Scope y g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    (cliPromoteMatchingMissGen_placed_ok mmpl gh W)
    (cliPromoteOverGen_placed_ok mmpl gh W hh)
    hh hread hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hro1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    hpan
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hrof
        ⟨err, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hrof
        ⟨err, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact decPkDefD2c_pathC_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact decPkDefD2c_pathC_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact decPkDefD2c_pathC_accept_none X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

theorem d2cStages_placed_inst [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 519)
        (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec)) :
    D2cStagesPlacedStmt mmpl gh W where
  stageP2Over := stageP2Over_qpan_cli_placed_of_pathC mmpl gh W
    (stageP2PathCOver_qpan_cli_placed_of_seams mmpl gh W hDropNz hSpqr h_accept h_accept_err
      (fun B F0 peer hh hread =>
        cliPollSelf_kitPlacedOk mmpl gh W B F0 peer hDropNz hh (jRead := 518) hread)
      (fun B F0 spkId hh hread =>
        cliPollSpk_kitPlacedOk mmpl gh W B F0 spkId hDropNz hh hread)
      (fun B F0 kpkId spkId kbk hh hread =>
        cliPollKpk_kitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread
          (cliKpkGetPoll_placed_ok mmpl gh W B hh hread))
      (fun B F0 opkWord hh hread =>
        cliPollPk_kitPlacedOk mmpl gh W B F0 opkWord hDropNz hh hread))
  stageP3Prev1 := stageP3_prev1_placed_ok hLog519
  stageP4Prev1 := stageP4Prev1_placed_inst hDropNz

theorem cliDpPollOk_d2c_placed_of_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 519)
        (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    CliDpPollOkD2cStatePlacedStmt mmpl gh W :=
  cliDpPollOk_d2c_placed_of_cliStages mmpl gh W
    (closureBaseStagesCli_placed_inst mmpl gh W hDropNz hSpqr h_accept h_accept_err
      (hLog519 mmpl gh W) hTryDec)
    (d2cStages_placed_inst mmpl gh W hDropNz hSpqr h_accept h_accept_err hLog519)

theorem decPkD2cSlotOk_placed_of_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hLog519 : ∀ (mmpl' : Obj.MultiPlacement) (gh' : CliGhostHooks) (W' : CliHooks),
      subroutine_ok (lsProg_518 (cliGhostExterns gh' (cliExternsPlaced mmpl' W'))) (lsmpl.base 519)
        (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    RunProofs.DecPkD2cSlotOkPlaced mmpl gh W :=
  RunProofs.decPkD2cSlotOk_of_cliStages_placed mmpl gh W hh hRead hStage2
    (closureBaseStagesCli_placed_inst mmpl gh W hDropNz hSpqr h_accept h_accept_err
      (hLog519 mmpl gh W) hTryDec)
    (d2cStages_placed_inst mmpl gh W hDropNz hSpqr h_accept h_accept_err hLog519)

/-! ## 4. `LibsignalFrozen`-Guarded Full-Placement Instantiations -/

set_option maxHeartbeats 1000000 in
theorem closure_pathA_cli_full_placed_ok [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hP2A : StageP2PathAQpanCliFrozenPlacedStmt mmpl gh W)
    (hP4 : StageP4PathAPlacedStmt)
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    OverClosurePathAFrozenPlacedStmt mmpl gh W := by
  intro X B S Scope hh hReadFile hDeser hinjK hsub hS stk' hneed hstk63
    y s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
    loadRec_of_cliPollSessPlaced_loadRel (σ := σ) hinjK hsub hfPeer hload_rel
  have hcur : (none : Option (SessionRecord (List (BitVec 8)))).bind (·.currentSession) = none := rfl
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 :=
    .inr ⟨trivial, hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518, hs1_files⟩
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hpre_split :
      stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      (stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut none ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed B S stk' y ?_)
  refine hP2A X B S Scope y StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    hh hReadFile hDeser hcoins hdecOk hsub hfPeer hloadS htrusted rfl hfiles1 hfr1
    (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_ ?_
  · intro sf Pf hoom _ hm_pan
    rw [← sepConj_assoc] at hm_pan
    exact dpPollOnPanic_of_p3p4Oom_placed stk' y hoom hm_pan
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f) hm_f
    have hm2 : sf.mem ⊨
        (decResAt E2E.HooksE.A0 y.out (.error err) ∗
          storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          anyHeap ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := exit_entails_dpPollPost_placed B S stk' hneed hstk63 y s0 sf
      StoresGhost.opened (.error err) anyHeap hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 m i k kp reg dk recG whisperMsgPtr whisperG preKeyMsgRem
      hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ _ hvregs2 hfr2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState ⟨W.C, W.Q⟩ meE k m dk
    obtain ⟨_hIn0, _hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn ⟨W.C, W.Q⟩ meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathA_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    refine sepWPp_genP3_to_tailQpan_placed B S stk' y hpan_model ?_
    refine stageP3GenStepsVRegs_of_base_full_placed_ok
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      (StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hh)
      (cliChainClone3_placed_ok mmpl gh W hh) (cliSenderChainClone3_placed_ok mmpl gh W hh)
      (hTryDec 0#64)
      s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' pt ptCap ptPtr s' P_s' hver hcl hdec_rel hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s'
      have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced σ y.g.stores
        hsub hfPeer hdecOk (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
              (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
              (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAtPlaced]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathA_p4_cont_placed hP4 B S hh hReadFile hDeser hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          hpm_eq hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hro' hent_s')
    · intro _G₁ _G' e sf P_f hver _hcl _hdec_rel herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hro_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y s0 s2 sf
        rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (coinsAfterPlaced y.g.coinsP y.g.coins
          (decryptDraws W.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_f hsf_sp htr_f hcs_f hvregs_f
    · intro sf P_f hver_ne hent_f hsf_sp htr_f hcs_f hvregs_f _hro_f
      exact stageP3_exit_pathA_to_pollPost_placed B S hh hS stk' hneed hstk63 y s0 s2 sf
        rngPtr whisperMsgPtr whisperG preKeyMsgRem (coinsAtPlaced y.g.coinsP y.g.coins)
        P_f R m.opkId m.kpkId m.spkId (.invalidMessage .preKey .decryptionFailed)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

set_option maxHeartbeats 800000 in
theorem closure_pathB_cli_full_placed_ok [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hP2 : StageP2MatchedFramedCliPlacedStmt)
    (hP4 : StageP4MatchedPlacedStmt)
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    OverClosurePathBFrozenPlacedStmt mmpl gh W := by
  intro X B S Scope hh hReadFile hDeser hinjK hsub hS stk' hneed hstk63
    y r sess s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hcur hsteps01 htr1 hfr1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
  dsimp only
  have hro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
    ⟨LibsignalCodeLoaded.of_codeLoaded hfr1.2, hfr1.1⟩
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let sid := y.g.msg.signedPreKeyId
  let kid := pmKyberId y.g.msg
  let kbk := y.g.msg.baseKey
  let kit := cliPollSessKitPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKitPlaced E2E.HooksE.A0 y.g.F y.g.peer σ
  let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 y.g.F pid σ
  let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 y.g.F sid σ
  let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 y.g.F kid sid kbk σ
  dsimp only [cliPollSessKitPlaced] at hload_rel
  obtain ⟨hloadS, hr_eq, hIn, hMatch, _, _, hSeeds, hRC, hPqLt⟩ :=
    pathB_scopeIn_and_match hinjK hsub hfPeer hdecOk hload_rel hcur
  subst hr_eq
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  let F_p2 : SepProp :=
    ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
    kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
    memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
  let Fr_tail : SepProp :=
    pkKit.storeAt (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
    spkKit.storeAt (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
    kpkKit.storeAt (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
    dirAt E2E.HooksE.A0 (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32
  have hstores_in := storesAt_opened_entails_cliPollStoresKitsAtPlaced σ y.g.stores
    hsub hfPeer hdecOk (pid := pid) (sid := sid) (kid := kid) (kbk := kbk)
  have hstk_split := stackAt_subStack_sub_eq sp B (rootStack_le_subStack B) hsp_sub
  have hpre_split :
      stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
         (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
         (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some ⟨some sess⟩) ∗
       preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
       protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
       coinsInstalledPlaced y.g.coinsP y.g.coins ∗
       storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
       LsTokenInit ∗
       FromRecordCallees.lsLogOff ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ⊢
      ((stageP2PostP1At E2E.HooksE.A0 y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
          (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
          (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
          (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
        p1LoadedRecordAt Slots.scopeKit E2E.HooksE.A0 y.fut (some ⟨some sess⟩) ∗
        preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
        protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
        protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
        coinsInstalledPlaced y.g.coinsP y.g.coins ∗
        LsTokenInit ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack) ∗ F_p2) ∗ Fr_tail := by
    rw [hstk_split]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstores_in))))))) ?_
    unfold cliPollStoresKitsAtPlaced F_p2 Fr_tail
    sep_frame
  refine sepWPp_conseq_pre hpre_split (sepWPp_pollGoal_frame_placed B S stk' y ?_)
  refine hP2 mmpl gh W B S Slots.scopeKit y sess s0 s1 sp rngPtr v_a8 v_b8 v_d0 F_p2 _ _
    hh hReadFile hDeser hcoins hMatch hro1 (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hroot hpc1 hrun1 hsp_align1 hregs1 ?_ ?_ ?_
  · intro sf Pf hoom _ hm_pan
    have hm_pan' : sf.mem ⊨ (Pf ∗ (F_p2 ∗ Fr_tail)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm_pan
    exact dpPollOnPanic_of_p3p4Oom_placed stk' y hoom hm_pan'
  · intro hrem_ne sf Pf _ _ _ hsf_sp htr_f hcs_f hvregs_f _ hent_f
    let err : ApiError AddrVal Unit := .protocol (.invalidMessage .preKey .badCiphertext)
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent_f)) hm_f
    have hdec_at := apiDecResultAt_proto_entails_decResAt E2E.HooksE.A0 y.out
      (.invalidMessage .preKey .badCiphertext) err
    have hstores_out := cliPollStoresKitsAtPlaced_entails_storesAt (A := E2E.HooksE.A0)
      (F0 := y.g.F) (Scope := Slots.scopeKit) (peer := y.g.peer)
      (pid := pid) (sid := sid) (kid := kid) (kbk := kbk) σ y.g.stores StoresGhost.opened
    have hm2 : sf.mem ⊨
        apiDecResultAt E2E.HooksE.A0 y.out (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        cliPollStoresKitsAtPlaced E2E.HooksE.A0 y.g.F Slots.scopeKit y.g.peer pid sid kid kbk σ
          y.g.stores StoresGhost.opened ∗
        (protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          (memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack) ∗
            stackAt sp rootStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [cliPollStoresKitsAtPlaced, F_p2, Fr_tail]; sep_frame) hm1
    have hm3 := Arm64.Satisfies.mono (sepConj_mono hdec_at (sepConj_mono_left hstores_out)) hm2
    rw [← hstk_split] at hm3
    have hm4 : sf.mem ⊨
        (decResAt E2E.HooksE.A0 y.out (.error err) ∗
          storesAt E2E.HooksE.A0 y.g.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          FromRecordCallees.lsLogOff ∗
          E2E.HooksE.A0.pool ∗
          (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by sep_frame) hm3
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS (err := err) nofun nofun
        (decPkDef_pathB_remId_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_ne)
    have hpost_goal := exit_entails_dpPollPost_placed B S stk' hneed hstk63 y s0 sf
      StoresGhost.opened (.error err)
      (LsTokenInit ∗ coinsInstalledPlaced y.g.coinsP y.g.coins)
      hh hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm4
  · intro hrem_eq s2 g recG whisperMsgPtr whisperG preKeyMsgRem
      opkHi kyberPreKeyId signedPreKeyId hex hmsg_fold hsteps12 hpc2 hrun2
      hs2_sp hsp_align2 htr2 _ _ _ hvregs2 _hro2
    have hfr2 : LibsignalFrozen lsmpl s2.mem :=
      libsignalFrozen_of_keepsFrozen hfr1 hsteps12.keepsFrozen
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (cliFiles_eq_of_trace_eq_placed (i := 518) hh hsteps02 htr20).trans hf0
    have hpan_model : sess.state.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model W.C W.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins sess.state).1 = .error .panic →
        (dpSlotPollKStatePlaced E2E.HooksE.A0 B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathB_panic X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS htrusted hMatch hrem_eq hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
        (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
        (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
        (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
        (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
         ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
         memRegion (y.fut + 0x2a8#64) 4) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
      kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    have hpre_p3 :
        (LsTokenInit ∗
          genP3Pre_placed E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
          stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
            (y.g.stores + 0xf0#64) (lsρ cliSessionVtSym) y.g.stores (lsρ cliIdentityVtSym)
            (y.g.stores + 0xc8#64) (lsρ cliPreKeyVtSym) (y.g.stores + 0x50#64) (lsρ cliSignedPreKeyVtSym)
            (y.g.stores + 0x78#64) (lsρ cliKyberPreKeyVtSym) rngPtr
            (((y.fut + 0x298#64) ↦₃₂ 2#32) ∗ ((y.fut + 0x29c#64) ↦₃₂ opkHi))
            (((y.fut + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
             ((y.fut + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
             memRegion (y.fut + 0x2a8#64) 4) ∗
          stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRem) ∗ F_p2 ⊢
        LsTokenInit ∗
          genP3Pre_placed E2E.HooksE.A0 s2.sp (s2.readReg64 .x29) y.fut y.cx y.g.peerA y.g.meA
            whisperMsgPtr y.g.coinsP (y.g.msg.message.messageVersion.zeroExtend 32) y.g.coins
            recG sess.state y.g.peer y.g.me whisperG y.g.msg.message s2 ∗
          stageP3Sub5ExtraPrePrevEmpty E2E.HooksE.A0 s0 s2 y.fut y.out 8#64 g 0#8 ∗
          F_p3 := by
      dsimp only [F_p2, F_p3]
      sep_frame
    refine sepWPp_conseq_pre hpre_p3 (sepWPp_genP3_to_tailQpan_placed B S stk' y hpan_model ?_)
    refine stageP3PrevEmptyVRegs_of_base_full_placed_ok
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) W.C 0#64 W.Q.K
      (StageP3CalleesM3BasePlaced.of_cliExternsPlaced mmpl gh W hh)
      (cliChainClone3_placed_ok mmpl gh W hh) (cliSenderChainClone3_placed_ok mmpl gh W hh)
      (hTryDec 0#64) (cliDropSessionStructure4_placed_ok_at mmpl gh W hh (i := 518))
      s0 s2 y.fut y.cx y.out 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      g recG sess.state y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hfr2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' pt ptCap ptPtr s' P_s' hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hro' hent_s'
      exact closure_pathB_p4_cont_placed hP4 mmpl gh W X B S Scope hh hReadFile hDeser hS stk' hneed hstk63
        y sess s0 s2 s' rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R
        opkHi kyberPreKeyId signedPreKeyId g recG G₁ G' pt
        hfPeer hdecOk hIn hloadS htrusted hMatch hrem_eq hex hmsg_fold
        hs2_files htr20 hs2_sp hsp_sub hsp_align2 hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne
        hsteps2' hpc' hrun' hs'_sp htr' hvregs' hx19' hx24' hx25' hx26' hx27' hx28'
        hro' hent_s'
    · intro G₁ G' e sf P_f hver _ _ herr hne_p hent_f hsf_sp htr_f hcs_f hvregs_f _
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem _ P_f R
        opkHi kyberPreKeyId signedPreKeyId e hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS htrusted hMatch hrem_eq hver herr hne_p)
        hent_f hsf_sp htr_f hcs_f hvregs_f
    · intro sf P_f hver_ne hent_f hsf_sp htr_f hcs_f hvregs_f _
      exact stageP3_exit_prevEmpty_to_pollPost_placed B S hh hS stk' hneed hstk63
        y s0 s2 sf rngPtr whisperMsgPtr whisperG preKeyMsgRem _ P_f R
        opkHi kyberPreKeyId signedPreKeyId (.invalidMessage .preKey .decryptionFailed)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathB_ver_ne X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS htrusted hMatch hrem_eq hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

theorem closureBaseStagesCli_full_placed_inst [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    ClosureBaseStagesCliFrozenPlacedStmt mmpl gh W :=
  { untrustedD2c := closure_untrusted_d2c_trap_placed_ok (stageP1_untrusted_trap_placed_inst hDropNz)
    stageP1Ok := overStageP1OkCli_of_trap (stageP1_ok_trap_placed_inst hDropNz)
    cliTryDecryptPqV1 := hTryDec
    pathA := closure_pathA_cli_full_placed_ok mmpl gh W
      (stageP2PathA_qpan_cli_full_placed_of_seams mmpl gh W hG hDropNz hSpqr
        (fun B F0 peer hh hread =>
          cliPollSelf_kitPlacedOk mmpl gh W B F0 peer hDropNz hh (jRead := 518) hread)
        (cliKpkGetPoll_placed_ok mmpl gh W))
      (stageP4PathA_placed_inst hDropNz) hTryDec
    pathB := closure_pathB_cli_full_placed_ok mmpl gh W
      stageP2Matched_framed_cli_placed_ok (stageP4Matched_placed_inst hDropNz) hTryDec }

theorem stageP2Over_qpan_cli_frozen_placed_of_pathC [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hP2 : StageP2PathCOverQpanCliFrozenPlacedStmt mmpl gh W) :
    StageP2OverQpanCliFrozenPlacedStmt mmpl gh W := by
  intro X B S Scope y r s_old g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hread hcoins hdecOk hsub hfPeer hload hcur hnot htrust hg1
    hfs hfr1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1 hpan herr hok
  have hr_scope : Slots.scopeIn r := hsub r (scope_of_loadRec_some hfPeer hload)
  exact hP2 X B S Scope y g1 r s_old s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    (cliPromoteMatchingMissGen_placed_ok mmpl gh W)
    (cliPromoteOverGen_placed_ok mmpl gh W hh)
    hh hread hcoins hdecOk.toDecPkOk₀_emptyScope
    hsub hfPeer hcur hr_scope hnot htrust hg1
    hfs hfr1 htr01 hsp1 hsp0 hsp_sub hpc1 hrun1 halign1 hregs1
    hpan
    (fun sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hrof
        ⟨err, hne_p, hne_s, htrf, hrej, hpostf⟩ => by
      refine herr sf Pf hpcf hrunf hstepsf hspf hcsf hvregsf hrof
        ⟨err, hne_p, hne_s, htrf, ?_, hpostf⟩
      rcases hrej with ⟨m, i, hpm, hi, _hpm_eq, hlookup | ⟨k, kp, hk, hkp, haccAll⟩⟩
      · exact decPkDefD2c_pathC_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
          y.g.msg y.g.coins hload hcur htrust hnot hpm hlookup
      · cases hreg : StoresGhost.opened.identity.regId cliIo.rd y.g.F with
        | error u =>
          cases u
          exact decPkDefD2c_pathC_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm (Or.inr (Or.inr hreg))
        | ok reg =>
          exact decPkDefD2c_pathC_accept_none X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
            y.g.msg y.g.coins hload hcur htrust hnot hpm hi hk hkp hreg (haccAll reg))
    hok

theorem d2cStages_full_placed_inst [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    D2cStagesFrozenPlacedStmt mmpl gh W where
  stageP2Over := stageP2Over_qpan_cli_frozen_placed_of_pathC mmpl gh W
    (stageP2PathCOver_qpan_cli_full_placed_of_seams mmpl gh W hDropNz hG hSpqr
      (fun B F0 peer hh hread =>
        cliPollSelf_kitPlacedOk mmpl gh W B F0 peer hDropNz hh (jRead := 518) hread)
      (fun B F0 spkId hh hread =>
        cliPollSpk_kitPlacedOk mmpl gh W B F0 spkId hDropNz hh hread)
      (fun B F0 kpkId spkId kbk hh hread =>
        cliPollKpk_kitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread
          (cliKpkGetPoll_placed_ok mmpl gh W B hh hread))
      (fun B F0 opkWord hh hread =>
        cliPollPk_kitPlacedOk mmpl gh W B F0 opkWord hDropNz hh hread))
  stageP3Prev1 := stageP3_prev1_full_placed_ok
  stageP4Prev1 := stageP4Prev1_placed_inst hDropNz

theorem cliDpPollOk_d2c_full_placed_of_seams [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    CliDpPollOkD2cStateFrozenPlacedStmt mmpl gh W :=
  cliDpPollOk_d2c_frozen_placed_of_cliStages mmpl gh W
    (closureBaseStagesCli_full_placed_inst mmpl gh W hDropNz hG hSpqr hTryDec)
    (d2cStages_full_placed_inst mmpl gh W hDropNz hG hSpqr)

theorem decPkD2cSlotOk_full_placed_of_seams [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hStage2 : Proofs.libsignal.Hooks2.Stage2ContractsMinPlaced
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hTryDec : CliTryDecryptPqV1PlacedStmt mmpl gh W) :
    RunProofs.DecPkD2cSlotOkFrozenPlaced mmpl gh W :=
  RunProofs.decPkD2cSlotOk_of_cliStages_full_placed mmpl gh W hh hRead hStage2
    (closureBaseStagesCli_full_placed_inst mmpl gh W hDropNz hG hSpqr hTryDec)
    (d2cStages_full_placed_inst mmpl gh W hDropNz hG hSpqr)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
