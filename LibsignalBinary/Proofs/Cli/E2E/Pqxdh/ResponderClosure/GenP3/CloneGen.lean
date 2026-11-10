/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChains
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFront
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTail
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePack
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePending
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — End-to-End Composition

Assembles all five segments (`CloneKeysFrontStmt`, `CloneChainsStmt`, `ClonePendingStmt`,
`CloneKeysTailStmt`, `ClonePackStmt`) into `CloneGenStmt` (`+0x1778 → +0x1cd4 / +0x1e04`,
`genP3Pre → genP3Post`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxHeartbeats 400000 in
theorem cloneGen_4k_ok_of_chains (h2 : CloneChainsStmt4K) : CloneGenStmt4K := by
  intro A img ext hA hcc hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc hsp_align hsp_root hF hsym hpc hrun htr
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysFront_4k_ok img ext hA hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF hsym hpc
      hrun htr)
    (by simp) fun s1 P1 hpc1 hrun1 ⟨hent1, htr1, hF1, hsym1⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent1) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (h2 img ext hA hcc himg s0 s1 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF1 hsym1 hpc1 hrun1 htr1)
    (by simp) fun s2 P2 hpc2 hrun2 ⟨hent2, htr2, hF2, hsym2⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent2) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (clonePending_4k_ok img ext hA himg s0 s2 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF2 hsym2
      hpc2 hrun2 htr2)
    (by simp) fun s3 P3 hpc3 hrun3 ⟨hent3, htr3, hF3, hsym3⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent3) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysTail_4k_ok img ext hA himg s0 s3 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF3 hsym3
      hpc3 hrun3 htr3)
    (by simp) fun s4 P4 hpc4 hrun4 ⟨hent4, htr4, hF4, hsym4⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent4) ?_
  exact clonePack_4k_ok img ext hA himg s0 s4 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF4 hsym4
    hpc4 hrun4 htr4

theorem cloneGen_4k_ok : CloneGenStmt4K :=
  cloneGen_4k_ok_of_chains cloneChains_4k_ok

set_option maxHeartbeats 400000 in
theorem cloneGen_ok_of_chains (h2 : CloneChainsStmt) : CloneGenStmt := by
  intro A img ext hA hcc hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc hsp_align hsp_root hF hsym hpc hrun htr
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysFront_ok img ext hA hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF hsym hpc
      hrun htr)
    (by simp) fun s1 P1 hpc1 hrun1 ⟨hent1, htr1, hF1, hsym1⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent1) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (h2 img ext hA hcc himg s0 s1 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF1 hsym1 hpc1 hrun1 htr1)
    (by simp) fun s2 P2 hpc2 hrun2 ⟨hent2, htr2, hF2, hsym2⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent2) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (clonePending_ok img ext hA himg s0 s2 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF2 hsym2
      hpc2 hrun2 htr2)
    (by simp) fun s3 P3 hpc3 hrun3 ⟨hent3, htr3, hF3, hsym3⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent3) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysTail_ok img ext hA himg s0 s3 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF3 hsym3
      hpc3 hrun3 htr3)
    (by simp) fun s4 P4 hpc4 hrun4 ⟨hent4, htr4, hF4, hsym4⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent4) ?_
  exact clonePack_ok img ext hA himg s0 s4 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF4 hsym4
    hpc4 hrun4 htr4

theorem cloneGen_ok : CloneGenStmt :=
  cloneGen_4k_ok.toCloneGenStmt

private theorem sepWPp_weaken_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp)
    (himp : ∀ s1 P_f, Q s1 P_f → Q' s1 P_f) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hne
  obtain ⟨sf, hsteps, hpost⟩ := h R hm hne
  refine ⟨sf, hsteps, ?_⟩
  rcases hpost with ⟨hpc, hrun, P_f, hm', hQ⟩ | hp
  · exact Or.inl ⟨hpc, hrun, P_f, hm', himp sf P_f hQ⟩
  · exact Or.inr hp

/-- `calleeSavedVRegs`-preserving strengthening of `CloneGenStmt4K`. -/
def CloneGenVRegsStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
    (hcc : ChainClone3OkExt img.base A ext) →
    (hscc : SenderChainClone3OkExt img.base A ext) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (cloneExitPC img ext st msgVer) s
        (genP3Pre A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3Post A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0)

/-- `calleeSavedVRegs`-preserving strengthening of `CloneGenStmt`. -/
def CloneGenVRegsStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
    (hcc : ChainClone3OkExt img.base A ext) →
    (hscc : SenderChainClone3OkExt img.base A ext) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (cloneExitPC img ext st msgVer) s
        (genP3Pre A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3Post A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (P3P4.PanicOomProp s0)

theorem CloneGenVRegsStmt4K.toCloneGenVRegsStmt (h : CloneGenVRegsStmt4K) : CloneGenVRegsStmt :=
  fun img ext hA => h img ext (AllocContractsMem4K.of_AllocContracts hA)

set_option maxHeartbeats 400000 in
theorem cloneGen_vregs_4k_ok_of_chains (h2 : CloneChainsVRegsStmt4K) : CloneGenVRegsStmt4K := by
  intro A img ext hA hcc hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc hsp_align hsp_root hF hsym hpc hrun htr
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysFront_vregs_4k_ok img ext hA hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr
      locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF
      hsym hpc hrun htr)
    (by simp) fun s1 P1 hpc1 hrun1 ⟨hent1, htr1, hF1, hsym1, hvregs1⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent1) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (h2 img ext hA hcc himg s0 s1 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF1 hsym1 hpc1 hrun1 htr1)
    (by simp) fun s2 P2 hpc2 hrun2 ⟨hent2, htr2, hF2, hsym2, hvregs2⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent2) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (clonePending_vregs_4k_ok img ext hA himg s0 s2 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF2 hsym2
      hpc2 hrun2 htr2)
    (by simp) fun s3 P3 hpc3 hrun3 ⟨hent3, htr3, hF3, hsym3, hvregs3⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent3) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysTail_vregs_4k_ok img ext hA himg s0 s3 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF3 hsym3
      hpc3 hrun3 htr3)
    (by simp) fun s4 P4 hpc4 hrun4 ⟨hent4, htr4, hF4, hsym4, hvregs4⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent4) ?_
  refine sepWPp_weaken_post
    (clonePack_vregs_4k_ok img ext hA himg s0 s4 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF4 hsym4
      hpc4 hrun4 htr4)
    fun _ _ ⟨hent5, htr5, hF5, hsym5, hvregs5⟩ =>
      ⟨hent5, htr5, hF5, hsym5,
       hvregs5.trans (hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1)))⟩

theorem cloneGen_vregs_4k_ok : CloneGenVRegsStmt4K :=
  cloneGen_vregs_4k_ok_of_chains cloneChains_vregs_4k_ok

set_option maxHeartbeats 400000 in
theorem cloneGen_vregs_ok_of_chains (h2 : CloneChainsVRegsStmt) : CloneGenVRegsStmt := by
  intro A img ext hA hcc hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc hsp_align hsp_root hF hsym hpc hrun htr
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysFront_vregs_ok img ext hA hscc himg s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF hsym hpc
      hrun htr)
    (by simp) fun s1 P1 hpc1 hrun1 ⟨hent1, htr1, hF1, hsym1, hvregs1⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent1) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (h2 img ext hA hcc himg s0 s1 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF1 hsym1 hpc1 hrun1 htr1)
    (by simp) fun s2 P2 hpc2 hrun2 ⟨hent2, htr2, hF2, hsym2, hvregs2⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent2) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (clonePending_vregs_ok img ext hA himg s0 s2 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF2 hsym2
      hpc2 hrun2 htr2)
    (by simp) fun s3 P3 hpc3 hrun3 ⟨hent3, htr3, hF3, hsym3, hvregs3⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent3) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysTail_vregs_ok img ext hA himg s0 s3 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF3 hsym3
      hpc3 hrun3 htr3)
    (by simp) fun s4 P4 hpc4 hrun4 ⟨hent4, htr4, hF4, hsym4, hvregs4⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent4) ?_
  refine sepWPp_weaken_post
    (clonePack_vregs_ok img ext hA himg s0 s4 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg hrc hsp_align hsp_root hF4 hsym4
      hpc4 hrun4 htr4)
    fun _ _ ⟨hent5, htr5, hF5, hsym5, hvregs5⟩ =>
      ⟨hent5, htr5, hF5, hsym5,
       hvregs5.trans (hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1)))⟩

theorem cloneGen_vregs_ok : CloneGenVRegsStmt :=
  cloneGen_vregs_4k_ok.toCloneGenVRegsStmt

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
