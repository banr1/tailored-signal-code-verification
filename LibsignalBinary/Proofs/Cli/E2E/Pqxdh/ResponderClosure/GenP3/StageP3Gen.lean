/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneGen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# General Stage P3 Composition

Proves `stageP3Gen_ok_of_clone : CloneGenStmt → StageP3GenStmt` and `stageP3Gen_ok : StageP3GenStmt`,
chaining `CloneGenStmt` (`+0x1778 → cloneExitPC img ext st msgVer`) with:
- `st.version = msgVer` (`+0x1cd4`): `p3_bl_tryDecrypt_ext_wp`, `tryDecryptSpecTPTight` with
  tight panic lifting into `genP3S5PanicProp`, and `stageP3_sub5_dispatch_ext_ok` to `+0x34dc`
  (`Ok`) or `s0.readReg64 .x30` (`Err`);
- `st.version ≠ msgVer` (`+0x1e04`): `stageP3_ver_ne_ext_ok` to `s0.readReg64 .x30`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SignalSession

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

/-! ## 1. Spatial Framing Helpers for `genP3SpillAll` and `genP3PostSpatial` -/

theorem genP3SpillAll_entails_s5 (sp : BitVec 64) :
    genP3SpillAll sp ⊢ memRegion (sp + 0x930#64) 48 ∗ genP3S5SpillRem sp := by
  unfold genP3SpillAll genP3S5SpillRem
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro w
  have h930 := words6_entails_memRegion48 (sp + 0x930#64)
    w.u930 w.u938 w.u940 w.u948 w.u950 w.u958
  have h960 := words6_entails_memRegion48 (sp + 0x960#64)
    w.u960 w.u968 w.u970 w.u978 w.u980 w.u988
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h930 h960
  have hrem :
      ((sp + 0x48#64) ↦₆₄ w.u_48) ∗
      ((sp + 0x50#64) ↦₆₄ w.u_50) ∗
      ((sp + 0x5c#64) ↦₃₂ w.u_5c) ∗
      ((sp + 0x7c#64) ↦₃₂ w.u_7c) ∗
      ((sp + 0x98#64) ↦₆₄ w.u_98) ∗
      ((sp + 0xd0#64) ↦₆₄ w.u_d0) ⊢
      ∃∗ w' : GenP3S5FrontRem,
        ((sp + 0x48#64) ↦₆₄ w'.u48) ∗
        ((sp + 0x50#64) ↦₆₄ w'.u50) ∗
        ((sp + 0x5c#64) ↦₃₂ w'.u5c) ∗
        ((sp + 0x7c#64) ↦₃₂ w'.u7c) ∗
        ((sp + 0x98#64) ↦₆₄ w'.u98) ∗
        ((sp + 0xd0#64) ↦₆₄ w'.ud0) :=
    Entails.sepExists_right ⟨w.u_48, w.u_50, w.u_98, w.u_d0, w.u_5c, w.u_7c⟩ (Entails.refl _)
  refine Entails.trans (entails_replace_sub h930 (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub h960 (by sep_focus) rfl) ?_
  exact entails_replace_sub hrem (by sep_focus) (by ac_rfl)

/-! ## 2. `CloneGenStmt` Prefix Step with `TokenInit` & `stageP3Sub5ExtraPre` Frame -/

theorem stageP3_clone_prefix_4k (hClone : CloneGenStmt4K)
    {A : RustAlloc} (img : Obj.Image) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4K img.base A ext)
    (hcc : ChainClone3OkExt img.base A ext)
    (hscc : SenderChainClone3OkExt img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (Q : State → SepProp → Prop)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = closureEntry img ext + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = cloneExitPC img ext st msgVer →
      s1.status = .Running →
      s1.trace = s0.trace →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      (P1 ⊢
        genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (TokenInit img ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)
      Q
      (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := hClone img ext hA hcc hscc himg s0 s s.sp (s.readReg64 .x29)
    coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc_lt hsp_align hsp_root hF hsym hpc hrun htr
  let F : SepProp :=
    TokenInit img ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
  have hP :
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) =
      genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    dsimp only [F]
    ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps,
      ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hF1, hsym1⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hCont s1 (P1 ∗ F) hpc1 hrun1 htr1 hF1 hsym1 (sepConj_mono_left hent1)
        R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨s1, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem stageP3_clone_prefix (hClone : CloneGenStmt)
    {A : RustAlloc} (img : Obj.Image) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hcc : ChainClone3OkExt img.base A ext)
    (hscc : SenderChainClone3OkExt img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (Q : State → SepProp → Prop)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = closureEntry img ext + 0x1778#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = cloneExitPC img ext st msgVer →
      s1.status = .Running →
      s1.trace = s0.trace →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      (P1 ⊢
        genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (TokenInit img ∗
          stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0)
      Q
      (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := hClone img ext hA hcc hscc himg s0 s s.sp (s.readReg64 .x29)
    coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc_lt hsp_align hsp_root hF hsym hpc hrun htr
  let F : SepProp :=
    TokenInit img ∗ stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
  have hP :
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) =
      genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    dsimp only [F]
    ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps,
      ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hF1, hsym1⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hCont s1 (P1 ∗ F) hpc1 hrun1 htr1 hF1 hsym1 (sepConj_mono_left hent1)
        R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨s1, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_lift_panicOom {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q : State → SepProp → Prop}
    {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)} {s0 : State}
    (h : SepWPp prog ret s P Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨hpan, Pm, hmm, hoom⟩ | hexit⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, Pm, hmm, Or.inl hoom⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hexit)⟩
theorem stackAt_root_split_grow (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack :=
  stackAt_split_bottom sp growOneSpeStack (rootStack - growOneSpeStack) (by decide)

theorem memRegion344_104_240_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 104 ∗ memRegion (sp + 0x448#64) 240 =
      memRegion (sp + 0x3e0#64) 344 :=
  (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 104) (k := 240)
    (b' := sp + 0x448#64) rfl (by bv_omega) (by decide)).symm

/-! ## 3. `+0x1cd4 → +0x1cd8` `try_decrypt_with_state` Step with Tight Panic Lifting -/

theorem bind_sepWPp_genPanic {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {P P_stage F : SepProp} {Q_mid : State → SepProp → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm (P_m ∗ F) Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp prog ret s P Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨hpan, P_m, hmm, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm P_m hpcm hrunm hqm R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hoom (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
theorem stageP3_call_tryDecrypt_ext {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (hroot : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img))
    (s0 s s1 : State)
    (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F : SepProp) (Q : State → SepProp → Prop)
    (hver : st.version = msgVer)
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st)
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (hF1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hpc1 : s1.pc = closureEntry img ext + 0x1cd4#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (htr1 : s1.trace = s0.trace)
    (hx0_1 : s1.readReg64 .x0 = s.sp + 0x270#64)
    (hx1_1 : s1.readReg64 .x1 = s.sp + 0xa90#64)
    (hx2_1 : s1.readReg64 .x2 = remAddrPtr)
    (hx3_1 : s1.readReg64 .x3 = locAddrPtr)
    (hx4_1 : s1.readReg64 .x4 = whisperMsgPtr)
    (hx5_1 : s1.readReg64 .x5 = 3#64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hCont : ∀ (s2 : State) (G' : SessionGhost),
      (genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic →
      G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G' →
      s2.pc = closureEntry img ext + 0x1cd8#64 →
      s2.status = .Running →
      s2.sp = s.sp →
      s2.trace = s0.trace →
      img.FrozenLoaded s2 →
      s2.symtab = img.symtab →
      s2.readReg64 .x19 = coroPtr →
      s2.readReg64 .x24 = s.sp + 0x370#64 →
      s2.readReg64 .x27 = ctxPtr →
      calleeSavedVRegs s2 = calleeSavedVRegs s1 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
        ((TokenInit img ∗
          sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗
          Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          logOff img ∗
          stackAt s.sp rootStack ∗
          A.pool) ∗ F)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      ((TokenInit img ∗
        sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        Coins.coinsAt img.base cur rest ∗
        logOff img ∗
        stackAt s.sp rootStack ∗
        A.pool) ∗ F)
      Q
      (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  have hbl := p3_bl_tryDecrypt_ext_wp img.base ext s1 hpc1 hrun1
  refine P3P4.SepWPp.bind_sepWP_frame hF1 hsym1 hbl
    (emp_sepConj _).symm
    fun sc hpcc hrunc hFc hsymc hregsc => ?_
  rw [emp_sepConj]
  rcases hregsc with ⟨hspc_1, htrc_1, hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c, _,
    hx19_c, hx24_c, hx27_c, _, hx30_c, hvregs_c⟩
  have hspc : sc.sp = s.sp := hspc_1.trans hs1_sp
  have hspc_al : sc.spAligned = true := by simpa only [State.spAligned, hspc] using hsp_align
  have hsp_root_c : rootStack ≤ sc.sp.toNat := by rw [hspc]; exact hsp_root
  have htrc_0 : sc.trace = s0.trace := htrc_1.trans htr1
  let x : TryDecryptGhost := {
    G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
    msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
    msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest
  }
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hroot hFc hsymc hpcc hrunc hspc_al hx30_c
    (fun R hm => ?_)
    (fun _ _ _ _ hexit => not_satisfies_false_sepConj hexit)
    (fun s2 _ ⟨_, hm_pan⟩ => ?_)
    (fun s2 hpc2 hrun2 hsp2_c hcs2 hF2 hsym2 => ?_)
    (fun _ _ _ hoom => (not_satisfies_false_sepConj hoom).elim)
  · dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP,
      Spec.inImage, x]
    rw [hspc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_lt, ?_⟩
    rw [← sepConj_assoc] at hm
    have hx5_byte : (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey := by
      rw [hx5_c, hx5_1]; rfl
    have hphi : sc.readReg64 .x0 = s.sp + 0x270#64 ∧
        sc.readReg64 .x1 = s.sp + 0xa90#64 ∧
        sc.readReg64 .x2 = remAddrPtr ∧
        sc.readReg64 .x3 = locAddrPtr ∧
        sc.readReg64 .x4 = whisperMsgPtr ∧
        (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey ∧
        (st.remoteIdentity ≠ some st.localIdentity ∨
          DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) ∧
        SeedsLen32 st ∧
        st.receiverChains.length < 2 ^ 32 ∧
        rootStack ≤ s.sp.toNat :=
      ⟨hx0_c.trans hx0_1, hx1_c.trans hx1_1, hx2_c.trans hx2_1, hx3_c.trans hx3_1,
       hx4_c.trans hx4_1, hx5_byte, hnot_self, hseeds, hrc_lt, hsp_root⟩
    have hpre_eq :
        (TokenInit img ∗
          (⌜img.FrozenLoaded sc ∧ sc.symtab = img.symtab⌝ ∗
            (⌜sc.readReg64 .x0 = s.sp + 0x270#64 ∧
              sc.readReg64 .x1 = s.sp + 0xa90#64 ∧
              sc.readReg64 .x2 = remAddrPtr ∧
              sc.readReg64 .x3 = locAddrPtr ∧
              sc.readReg64 .x4 = whisperMsgPtr ∧
              (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey ∧
              (st.remoteIdentity ≠ some st.localIdentity ∨
                DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) ∧
              SeedsLen32 st ∧
              st.receiverChains.length < 2 ^ 32 ∧
              rootStack ≤ s.sp.toNat⌝ ∗
              sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
              protocolAddressAt A rem remAddrPtr ∗
              protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗
              memRegion (s.sp + 0x270#64) 48 ∗
              Coins.coinsAt img.base cur rest ∗
              logOff img ∗
              stackAt s.sp rootStack ∗
              A.pool))) ∗ (F ∗ R) =
        (TokenInit img ∗
          sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
          protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗
          memRegion (s.sp + 0x270#64) 48 ∗
          Coins.coinsAt img.base cur rest ∗
          logOff img ∗
          stackAt s.sp rootStack ∗
          A.pool) ∗ F ∗ R := by
      have hp1 : (img.FrozenLoaded sc ∧ sc.symtab = img.symtab) = True :=
        propext ⟨fun _ => trivial, fun _ => ⟨hFc, hsymc⟩⟩
      have hp2 : (sc.readReg64 .x0 = s.sp + 0x270#64 ∧
          sc.readReg64 .x1 = s.sp + 0xa90#64 ∧
          sc.readReg64 .x2 = remAddrPtr ∧
          sc.readReg64 .x3 = locAddrPtr ∧
          sc.readReg64 .x4 = whisperMsgPtr ∧
          (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey ∧
          (st.remoteIdentity ≠ some st.localIdentity ∨
            DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) ∧
          SeedsLen32 st ∧
          st.receiverChains.length < 2 ^ 32 ∧
          rootStack ≤ s.sp.toNat) = True :=
        propext ⟨fun _ => trivial, fun _ => hphi⟩
      rw [hp1, hp2, pure_true, emp_sepConj, emp_sepConj]
    rw [hpre_eq]
    simpa only [sepConj_assoc] using hm
  · dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
      CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight,
      TryDecryptGhost.model, x] at hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pan
    rcases hm_pan with ⟨⟨hpan_or, hpref_c⟩, -⟩
    have hpref_0 : s0.trace <+: s2.trace := htrc_0 ▸ hpref_c
    rcases hpan_or with hmod_pan | hoom_pan
    · refine Or.inr fun R' hmR' => ?_
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hver, hmod_pan, hpref_0⟩,
        Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmR'⟩
    · have hoom_0 : allocFailedIn s0 s2 := by
        unfold allocFailedIn at hoom_pan ⊢
        rwa [← htrc_0]
      refine Or.inl fun R' hmR' => ?_
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hoom_0, hpref_0⟩,
        Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmR'⟩
  · dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec,
      Spec.inImage, TryDecryptGhost.model, x]
    rw [hspc]
    have heq :
        (TokenInit img ∗
          (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
            (∃∗ G' : SessionGhost,
              ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
              sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
            vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗
            protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            logOff img ∗
            stackAt s.sp rootStack ∗
            A.pool)) ∗ F =
        ⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧
          s2.trace = sc.trace⌝ ∗
        ((∃∗ G' : SessionGhost,
            ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
            sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
          TokenInit img ∗
          vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗
          Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          logOff img ∗
          stackAt s.sp rootStack ∗
          A.pool ∗ F) := by ac_rfl
    rw [heq]
    refine SepWPp.pure_elim fun ⟨hnpan, htr2_c⟩ => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun G' => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hdec_rel => ?_
    have heq2 :
        sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
        (TokenInit img ∗
          vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗
          Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          logOff img ∗
          stackAt s.sp rootStack ∗
          A.pool ∗ F) =
        ((TokenInit img ∗
          sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A rem remAddrPtr ∗
          protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗
          Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          logOff img ∗
          stackAt s.sp rootStack ∗
          A.pool) ∗ F) := by ac_rfl
    rw [heq2]
    rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, _, _, hx27_cs2, _, _, hvregs_cs2⟩
    exact hCont s2 G' hnpan hdec_rel hpc2 hrun2 (hsp2_c.trans hspc)
      (htr2_c.trans htrc_0) hF2 hsym2
      (hx19_cs2.trans (hx19_c.trans hx19_1))
      (hx24_cs2.trans (hx24_c.trans hx24_1))
      (hx27_cs2.trans (hx27_c.trans hx27_1))
      (hvregs_cs2.trans hvregs_c)

/-! ## 4. Full General Stage P3 (`stageP3Gen_ok_of_clone : CloneGenStmt → StageP3GenStmt`) -/

theorem postTryDecrypt_entails_s5Dispatch {A : RustAlloc} (img : Obj.Image)
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
      remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (G' recG : SessionGhost) (st₂ st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) :
    (TokenInit img ∗
      sessionStateAt A (s.sp + 0xa90#64) G' st₂ ∗
      vecResultAt A (s.sp + 0x270#64) res ∗
      protocolAddressAt A rem remAddrPtr ∗
      protocolAddressAt A loc locAddrPtr ∗
      signalMessageAt A msgG whisperMsgPtr msg ∗
      coinsPost ∗
      logOff img ∗
      stackAt s.sp rootStack ∗
      A.pool) ∗
    (sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0) ⊢
    stageP3DispatchPre A img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
      res b_2c0 G' recG st₂ st ∗
    genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
      rem loc msgG msg coinsPost := by
  unfold stageP3Sub5ExtraPre stageP3DispatchPre genP3S5PostFrame
  have hlog :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  rw [hlog, stackAt_root_split_grow s.sp, ← memRegion344_104_240_eq s.sp]
  exact entails_replace_sub (genP3SpillAll_entails_s5 s.sp)
    (by sep_focus) (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- 4K-Stack General Stage P3 (`+0x1778 → +0x34dc` / `s0.readReg64 .x30`) given `CloneGenStmt4K`. -/
theorem stageP3Gen_4k_ok_of_clone (hClone : CloneGenStmt4K) : StageP3GenStmt4K := by
  intro A img ext C ctl K hA hcc hscc hroot himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    recG st rem loc msgG msg Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt
    hF hsym hpc hrun hsp_align hsp_root htr
    hOk hErr hVerNe
  refine stageP3_clone_prefix_4k hClone img C K ext hA hcc hscc himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    recG st rem loc msgG msg Q hrc_lt hF hsym hpc hrun hsp_align hsp_root htr
    fun s1 P1 hpc1 hrun1 htr1 hF1 hsym1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPC, genP3Post, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEq genP3PostSpatial
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    let F_dec : SepProp :=
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
    refine SepWPp.weaken_pre
      (P' := (TokenInit img ∗
        sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        Coins.coinsAt img.base cur rest ∗
        logOff img ∗
        stackAt s.sp rootStack ∗
        A.pool) ∗ F_dec)
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_ext img ext C ctl K hroot
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg F_dec Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hF1 hsym1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hF2 hsym2 hx19_2 hx24_2 hx27_2 _ => ?_
    refine SepWPp.weaken_pre
      (postTryDecrypt_entails_s5Dispatch img s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG
        (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
        (Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPre
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_ext_4k_ok img img.base ext himg rfl hA
        s0 s2 coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne e he_npan b_2c0
        G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hF2 hsym2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPre at herr
      have herr_post :
          stageP3ErrPost A img.base s0 s2 coroPtr outPtr prevStatesPtr e =
            stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr e := by
        unfold stageP3ErrPost; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hFf, hsymf, _⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_ hspf htrf hcc_f hFf hsymf
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
    · have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
      have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_ext_4k_ok img img.base ext hA
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hb_align hF2 hsym2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic hok (by sep_focus)
        fun s' P_m hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hF', hsym', hx19', hx24', hx25', hx26', hx27', hx28', _, _⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres
        hpt_le hpt_lt hpt_ne hpc' hrun' hsp' htr'
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hF' hsym' ?_
      unfold stageP3DispatchOkMid
      rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPC, genP3Post, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostNe genP3PostSpatial stageP3Sub5ExtraPre
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun _ => ?_
    refine P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp))
      (by sep_focus) ?_
    have hver_ne := stageP3_ver_ne_ext_4k_ok img ext himg hA
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr hinit_ne
      msgVer b_2c0 G₁ recG st
      hF1 hsym1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    apply sepWPp_lift_panicOom
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus)
      fun sf _ _ ⟨hspf, htrf, hcc_f, hFf, hsymf, _⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f hFf hsymf
    unfold genP3S5PostFrame
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Unconditional 4K-Stack General Stage P3 (`+0x1778 → +0x34dc` / `s0.readReg64 .x30`),
obtained by instantiating `stageP3Gen_4k_ok_of_clone` with `cloneGen_4k_ok`. -/
theorem stageP3Gen_4k_ok : StageP3GenStmt4K :=
  stageP3Gen_4k_ok_of_clone cloneGen_4k_ok

set_option maxHeartbeats 1200000 in
/-- General Stage P3 (`+0x1778 → +0x34dc` / `s0.readReg64 .x30`) given `CloneGenStmt`. -/
theorem stageP3Gen_ok_of_clone (hClone : CloneGenStmt) : StageP3GenStmt := by
  intro A img ext C ctl K hA hcc hscc hroot himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    recG st rem loc msgG msg Q
    hinit_ne hnot_self hseeds hrc_lt hpq_lt
    hF hsym hpc hrun hsp_align hsp_root htr
    hOk hErr hVerNe
  refine stageP3_clone_prefix hClone img C K ext hA hcc hscc himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    recG st rem loc msgG msg Q hrc_lt hF hsym hpc hrun hsp_align hsp_root htr
    fun s1 P1 hpc1 hrun1 htr1 hF1 hsym1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPC, genP3Post, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEq genP3PostSpatial
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    let F_dec : SepProp :=
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0
    refine SepWPp.weaken_pre
      (P' := (TokenInit img ∗
        sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗
        protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        Coins.coinsAt img.base cur rest ∗
        logOff img ∗
        stackAt s.sp rootStack ∗
        A.pool) ∗ F_dec)
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_ext img ext C ctl K hroot
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg F_dec Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hF1 hsym1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hF2 hsym2 hx19_2 hx24_2 hx27_2 _ => ?_
    refine SepWPp.weaken_pre
      (postTryDecrypt_entails_s5Dispatch img s0 s coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr
        remAddrPtr locAddrPtr whisperMsgPtr msgVer b_2c0
        (genP3S5Model C K rem loc msg rest st).1 G' recG
        (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
        (Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPre
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_ext_ok img img.base ext himg rfl hA
        s0 s2 coroPtr outPtr initErrsPtr prevStatesPtr hinit_ne e he_npan b_2c0
        G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hF2 hsym2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPre at herr
      have herr_post :
          stageP3ErrPost A img.base s0 s2 coroPtr outPtr prevStatesPtr e =
            stageP3ErrPost A img.base s0 s coroPtr outPtr prevStatesPtr e := by
        unfold stageP3ErrPost; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hFf, hsymf, _⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_ hspf htrf hcc_f hFf hsymf
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
    · have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
      have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_ext_ok img img.base ext hA
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hb_align hF2 hsym2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic hok (by sep_focus)
        fun s' P_m hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hF', hsym', hx19', hx24', hx25', hx26', hx27', hx28', _, _⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres
        hpt_le hpt_lt hpt_ne hpc' hrun' hsp' htr'
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hF' hsym' ?_
      unfold stageP3DispatchOkMid
      rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs') (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPC, genP3Post, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostNe genP3PostSpatial stageP3Sub5ExtraPre
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun _ => ?_
    refine P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp))
      (by sep_focus) ?_
    have hver_ne := stageP3_ver_ne_ext_ok img ext himg hA
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevStatesPtr hinit_ne
      msgVer b_2c0 G₁ recG st
      hF1 hsym1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    apply sepWPp_lift_panicOom
    refine P3P4.SepWPp.ret_sepWPp_frame hver_ne (by sep_focus)
      fun sf _ _ ⟨hspf, htrf, hcc_f, hFf, hsymf, _⟩ => ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f hFf hsymf
    unfold genP3S5PostFrame
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Unconditional General Stage P3 (`+0x1778 → +0x34dc` / `s0.readReg64 .x30`),
obtained by instantiating `stageP3Gen_ok_of_clone` with `cloneGen_ok`. -/
theorem stageP3Gen_ok : StageP3GenStmt :=
  stageP3Gen_ok_of_clone cloneGen_ok

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
