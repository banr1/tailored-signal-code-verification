/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed Segment 5: Pack & Version Dispatch

Proves `clonePack_vregs_placed_ok` (`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4Placed → genP3PostPlaced`)
on `lsProg_518 ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subsPState32_placed (x y : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 x y) = (x == y) := by
  unfold subsPState32
  exact conditionHolds_eq_subs32 x y

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subsPState32_placed (x y : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 x y) = (x != y) := by
  unfold subsPState32
  exact conditionHolds_ne_subs32 x y

set_option maxHeartbeats 800000 in
theorem pack_eq_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (dv : PackDstVals)
    (hver : st.version = msgVer)
    (hpc : s.pc = (blkPl_518).base + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = w.newPqPtr)
    (hx22 : s.readReg64 .x22 = w.pendCap')
    (hx23 : s.readReg64 .x23 = w.newAlicePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = w.newRcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1cd4#64) s
      (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsAt s.sp dv)
      (fun s1 P_f =>
        (P_f ⊢
          packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
            packDstSlotsWrittenAt s.sp recG st w ((s.readReg64 .x20).truncate 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x270#64 ∧
        s1.readReg64 .x1 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x2 = remAddrPtr ∧
        s1.readReg64 .x3 = locAddrPtr ∧
        s1.readReg64 .x4 = whisperMsgPtr ∧
        s1.readReg64 .x5 = 3#64 ∧
        s1.readReg64 .x6 = 0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = fp ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold packSrcSlotsAt genP3SenderInlineWords packDstSlotsAt packDstSlotsWrittenAt
  dsimp only []
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w.newPqPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w.pendCap' := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w.newAlicePtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 recG.alice.bytes.length := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = w.newRcPtr := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 st.pqRatchetState.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 32#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  by_cases hsv0 : st.sessionVersion = 0
  · have hm : msgVer = 2#32 := by
      rw [← hver]; simp only [SessionState.version, hsv0, ↓reduceIte]; rfl
    have hsv0' : st.sessionVersion = 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = true := beq_iff_eq.mpr hsv0'
    have hne1 : (2#32 != msgVer) = false := bne_eq_false_iff_eq.mpr hm.symm
    have hne2 : (msgVer != 2#32) = false := bne_eq_false_iff_eq.mpr hm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hsv0']; ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  · have hm : st.sessionVersion = msgVer := by
      have hv : st.version = st.sessionVersion := by
        simp only [SessionState.version, hsv0, ↓reduceIte]
      exact hv.symm.trans hver
    have hsv0' : st.sessionVersion ≠ 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hsv0'
    have hne1 : (st.sessionVersion != msgVer) = false := bne_eq_false_iff_eq.mpr hm
    have hne2 : (msgVer != st.sessionVersion) = false := bne_eq_false_iff_eq.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hm]; ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem pack_ne_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (w : GenP3J4Witness) (dv : PackDstVals)
    (hver : st.version ≠ msgVer)
    (hpc : s.pc = (blkPl_518).base + 0x1bac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = w.newPqPtr)
    (hx22 : s.readReg64 .x22 = w.pendCap')
    (hx23 : s.readReg64 .x23 = w.newAlicePtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 recG.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = w.newRcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 st.pqRatchetState.length)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 32#64)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1e04#64) s
      (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
        packDstSlotsAt s.sp dv)
      (fun s1 P_f =>
        (P_f ⊢
          packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
            packDstSlotsWrittenAt s.sp recG st w ((s.readReg64 .x20).truncate 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x9 = msgVer.setWidth 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x29 = fp ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  unfold packSrcSlotsAt genP3SenderInlineWords packDstSlotsAt packDstSlotsWrittenAt
  dsimp only []
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w.newPqPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w.pendCap' := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w.newAlicePtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 recG.alice.bytes.length := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = w.newRcPtr := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 st.pqRatchetState.length := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 32#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  by_cases hsv0 : st.sessionVersion = 0
  · have hm : 2#32 ≠ msgVer := by
      intro h; apply hver
      simp only [SessionState.version, hsv0, ↓reduceIte]; exact h
    have hsv0' : st.sessionVersion = 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = true := beq_iff_eq.mpr hsv0'
    have hne1 : (2#32 != msgVer) = true := bne_iff_ne.mpr hm
    have hne2 : (msgVer != 2#32) = true := bne_iff_ne.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by simp only [hsv0']; ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  · have hm : st.sessionVersion ≠ msgVer := by
      intro h; apply hver
      simp only [SessionState.version, hsv0, ↓reduceIte]; exact h
    have hsv0' : st.sessionVersion ≠ 0#32 := hsv0
    have heq0 : (st.sessionVersion == 0#32) = false := beq_eq_false_iff_ne.mpr hsv0'
    have hne1 : (st.sessionVersion != msgVer) = true := bne_iff_ne.mpr hm
    have hne2 : (msgVer != st.sessionVersion) = true := bne_iff_ne.mpr hm.symm
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

private theorem sepWPp_done_pack_placed {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hQ : Q s P) :
    SepWPp prog ret s P Q Qp :=
  fun _ hm _ => ⟨s, Steps.refl s, Or.inl ⟨hpc, hrun, P, hm, hQ⟩⟩

set_option maxHeartbeats 800000 in
/-- Placed Segment 5 with `calleeSavedVRegs` (`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4Placed → genP3PostPlaced`). -/
theorem clonePack_vregs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (_hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1bac#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) (cloneExitPCPlaced st msgVer) s
      (genP3J4Placed A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3PostPlaced A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
          rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  dsimp only [genP3J4Placed]
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_elim
    fun ⟨hsp, hx19, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29,
         hreg_eq, hchains_len, _hsc_rel, hsc_inl⟩ => ?_
  cases hsp
  refine SepWPp.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_pure_sep A (coroPtr + 0xf8#64) recG st)) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim
    fun ⟨h_loc_deser, h_rem_deser, _, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  dsimp only [genP3CallFramePlaced]
  refine SepWPp.weaken_pre
    (P' := memRegion (s.sp + 0xa90#64) 344 ∗
            (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
              packRestFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur rest
                recG st w rem loc msgG msg))
    (Entails.of_eq (by dsimp only [packSrcSlotsAt, packRestFramePlaced]; ac_rfl)) ?_
  refine SepWPp.weaken_pre (sepConj_mono_left (memRegion_344_entails_packDstSlotsAt s.sp)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dv => ?_
  refine SepWPp.weaken_pre
    (P' := (packSrcSlotsAt s.sp recG st w remAddrPtr locAddrPtr whisperMsgPtr msgVer ∗
              packDstSlotsAt s.sp dv) ∗
            packRestFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur rest
              recG st w rem loc msgG msg)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, hver, ↓reduceIte]
    have hstep := pack_eq_placed_wp ext s coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr
      msgVer recG st w dv hver hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    refine bind_sepWP_lscro_frame_placed hcro hstep rfl
      fun s1 hpc1 hrun1 hcro1 hregs => ?_
    rcases hregs with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1,
      hx19_1, hx24_1, hx27_1, hx29_1, hvregs1⟩
    refine sepWPp_done_pack_placed hpc1 hrun1 ⟨?_, htr1.trans htr, hcro1, hvregs1⟩
    simp only [genP3PostPlaced, hver, ↓reduceIte, genP3PostEqPlaced]
    apply Entails.pure_right
      ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx19_1, hx24_1, hx27_1, hx29_1⟩
    exact packed_entails_genP3PostSpatialPlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st w ((s.readReg64 .x20).truncate 32) rem loc msgG msg
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl
  · simp only [cloneExitPCPlaced, hver, ↓reduceIte]
    have hstep := pack_ne_placed_wp ext s coroPtr ctxPtr fp remAddrPtr locAddrPtr whisperMsgPtr
      msgVer recG st w dv hver hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29
    refine bind_sepWP_lscro_frame_placed hcro hstep rfl
      fun s1 hpc1 hrun1 hcro1 hregs => ?_
    rcases hregs with ⟨hsp1, htr1, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1, hvregs1⟩
    refine sepWPp_done_pack_placed hpc1 hrun1 ⟨?_, htr1.trans htr, hcro1, hvregs1⟩
    simp only [genP3PostPlaced, hver, ↓reduceIte, genP3PostNePlaced]
    apply Entails.pure_right ⟨hsp1, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩
    exact packed_entails_genP3PostSpatialPlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st w ((s.readReg64 .x20).truncate 32) rem loc msgG msg
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len hreg_eq hchains_len hsc_inl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
