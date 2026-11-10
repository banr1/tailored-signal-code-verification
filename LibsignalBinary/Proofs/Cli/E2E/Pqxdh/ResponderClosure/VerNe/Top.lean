/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneGen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePack
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvOk
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Top
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChain
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Callees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Loop
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Post
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Top-Level Version-Mismatch Closure Composition

Composes the `SessionState` clone prefix (`+0x1778 → +0x1bac → +0x1e04`) with the 1-element
`previous_sessions` loop (`VerNe.Loop`), `+0x1e04` wrapper (`VerNe.Post`), and inlined
`SessionStructure::decode` proof (`PrevDec.overPrevDecode_cli_of_chain3_ext`) to establish closed
version-mismatch theorems at `+0x1e04`, `+0x1bac`, and `+0x1778`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (stageP3ErrPostPrevEmpty)
open CryptoVerification.SignalSession

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `+0x1e04 → s0.readReg64 .x30` from `OverPrevDecodeCliStmtGenExt` -/

/-- Composes `OverVerNe1e04CliStmtGenExt A trackVRegs` (`+0x1e04 → s0.readReg64 .x30`) from
`OverPrevDecodeCliStmtGenExt A trackVRegs` (`+0x1ee8 → +0x2620`). -/
theorem overVerNe_1e04_cli_of_prevDecode_gen_ext {A : RustAlloc} {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGenExt A trackVRegs) :
    OverVerNe1e04CliStmtGenExt A trackVRegs :=
  overVerNe_1e04_cli_of_loop_ext (overPrevLoop_cli_of_dec_ext hDec)

theorem overVerNe_1e04_cli_of_prevDecode_ext {A : RustAlloc}
    (hDec : OverPrevDecodeCliStmtExt A) :
    OverVerNe1e04CliStmtExt A :=
  overVerNe_1e04_cli_of_prevDecode_gen_ext hDec

theorem overVerNe_1e04_cli_of_prevDecode_gpr_ext {A : RustAlloc}
    (hDec : OverPrevDecodeCliGPRStmtExt A) :
    OverVerNe1e04CliGPRStmtExt A :=
  overVerNe_1e04_cli_of_prevDecode_gen_ext hDec

theorem overVerNe_1e04_cli_of_prevDecode_gen {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGen trackVRegs) :
    OverVerNe1e04CliA0StmtGen trackVRegs :=
  overVerNe_1e04_cli_of_loop (overPrevLoop_cli_of_dec hDec)

theorem overVerNe_1e04_cli_of_prevDecode
    (hDec : OverPrevDecodeCliStmt) :
    OverVerNe1e04CliA0Stmt :=
  overVerNe_1e04_cli_of_prevDecode_gen hDec

theorem overVerNe_1e04_cli_of_prevDecode_gpr
    (hDec : OverPrevDecodeCliGPRStmt) :
    OverVerNe1e04CliA0GPRStmt :=
  overVerNe_1e04_cli_of_prevDecode_gen hDec

/-! ## Extra closure-frame precondition and `+0x1bac` / `+0x1778` statements -/

/-- Extra closure-frame precondition at `+0x1778` / `+0x1bac` over a 1-element
`prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]`. -/
def stageP3Sub5ExtraPrePrev1 (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (b_2c0 : BitVec 8) : SepProp :=
  ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x448#64) 240 ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0

/-- Generalized `+0x1bac → s0.readReg64 .x30` CLI version-mismatch statement at arbitrary
`(A : RustAlloc)` under 4K-stack `AllocContractsMem4K img.base A ext` starting from `GenP3`'s
post-tail junction `genP3J4`. -/
def OverVerNe1bacCliStmtGenExt (A : RustAlloc) (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContractsMem4K img.base A ext →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      msgVer ≠ 4#32 →
      OverPrevEncOK enc →
      st.version = 4#32 →
      st.receiverChains.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1bac#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3J4 A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp)
        (fun sf P_f =>
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
              rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
            overScratch s.sp ∗
            anyHeap) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧
          ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          optVRegsEq trackVRegs sf s)
        (P3P4.PanicOomProp s0)

abbrev OverVerNe1bacCliStmtExt (A : RustAlloc) : Prop := OverVerNe1bacCliStmtGenExt A true
abbrev OverVerNe1bacCliGPRStmtExt (A : RustAlloc) : Prop := OverVerNe1bacCliStmtGenExt A false

/-- Generalized `+0x1778 → s0.readReg64 .x30` CLI version-mismatch statement at arbitrary
`(A : RustAlloc)` under 4K-stack `AllocContractsMem4K img.base A ext` starting from `GenP3`'s
Stage P3 entry predicate `genP3Pre`. -/
def OverVerNe1778CliStmtGenExt (A : RustAlloc) (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContractsMem4K img.base A ext →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      msgVer ≠ 4#32 →
      OverPrevEncOK enc →
      st.version = 4#32 →
      st.receiverChains.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp)
        (fun sf P_f =>
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
              rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
            overScratch s.sp ∗
            anyHeap) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧
          ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          optVRegsEq trackVRegs sf s)
        (P3P4.PanicOomProp s0)

abbrev OverVerNe1778CliStmtExt (A : RustAlloc) : Prop := OverVerNe1778CliStmtGenExt A true
abbrev OverVerNe1778CliGPRStmtExt (A : RustAlloc) : Prop := OverVerNe1778CliStmtGenExt A false

def OverVerNe1bacCliA0StmtGen (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContracts img.base A0 ext →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      msgVer ≠ 4#32 →
      OverPrevEncOK enc →
      st.version = 4#32 →
      st.receiverChains.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1bac#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3J4 A0 img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A0 s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp)
        (fun sf P_f =>
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty A0 img.base s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame A0 img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
              rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
            overScratch s.sp ∗
            anyHeap) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧
          ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          optVRegsEq trackVRegs sf s)
        (P3P4.PanicOomProp s0)

abbrev OverVerNe1bacCliA0Stmt : Prop := OverVerNe1bacCliA0StmtGen true
abbrev OverVerNe1bacCliA0GPRStmt : Prop := OverVerNe1bacCliA0StmtGen false

def OverVerNe1778CliA0StmtGen (trackVRegs : Bool) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContracts img.base A0 ext →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      msgVer ≠ 4#32 →
      OverPrevEncOK enc →
      st.version = 4#32 →
      st.receiverChains.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A0 img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A0 s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp)
        (fun sf P_f =>
          (P_f ⊢
            ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗
            stageP3ErrPostPrevEmpty A0 img.base s0 s coroPtr outPtr
              (.invalidMessage .preKey .decryptionFailed) ∗
            genP3S5PostFrame A0 img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
              rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
            overScratch s.sp ∗
            anyHeap) ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          sf.trace = s0.trace ∧
          ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧
          sf.symtab = img.symtab ∧
          optVRegsEq trackVRegs sf s)
        (P3P4.PanicOomProp s0)

abbrev OverVerNe1778CliA0Stmt : Prop := OverVerNe1778CliA0StmtGen true
abbrev OverVerNe1778CliA0GPRStmt : Prop := OverVerNe1778CliA0StmtGen false

/-! ## Shared post-pack continuation and `+0x1bac` / `+0x1778` proofs -/

private theorem bind_clone_oom_frame {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_clone F : SepProp} {Q_mid Q : State → SepProp → Prop}
    (hclone : SepWPp prog mid s P_clone Q_mid (P3P4.PanicOomProp s0))
    (hP : P = P_clone ∗ F)
    (hnext : ∀ s1 P1, s1.pc = mid → s1.status = .Running → Q_mid s1 P1 →
      SepWPp prog ret s1 (P1 ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  rw [hP]
  exact SepWPp.bind_oom_frame hclone rfl hnext

set_option maxHeartbeats 800000 in
private theorem overVerNe_postClone_cli_ext_ok {A : RustAlloc} {trackVRegs : Bool}
    (h1e04 : OverVerNe1e04CliStmtGenExt A trackVRegs)
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s1 : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (enc rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (P1 : SepProp)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (hcap : prevCap ≠ 0#64)
    (hver_ne : msgVer ≠ 4#32)
    (hEnc : OverPrevEncOK enc)
    (hst_ver4 : st.version = 4#32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ s.sp.toNat)
    (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64)
    (hpc1 : s1.pc = cloneExitPC img ext st msgVer)
    (hrun1 : s1.status = .Running)
    (htr1 : s1.trace = s0.trace)
    (hvregs1_s : calleeSavedVRegs s1 = calleeSavedVRegs s)
    (hF1 : img.FrozenLoaded s1)
    (hsym1 : s1.symtab = img.symtab)
    (hent1 : P1 ⊢
      genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      (P1 ∗ (TokenInit img ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp))
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
          overScratch s.sp ∗
          anyHeap) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        optVRegsEq trackVRegs sf s)
      (P3P4.PanicOomProp s0) := by
  have hver : st.version ≠ msgVer := fun h => hver_ne (h.symm.trans hst_ver4)
  refine SepWPp.weaken_pre (sepConj_mono_left hent1) ?_
  simp only [cloneExitPC, genP3Post, hver, ↓reduceIte] at hpc1 ⊢
  unfold genP3PostNe genP3PostSpatial stageP3Sub5ExtraPrePrev1
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩ => ?_
  have hx29_1' : s1.readReg64 .x29 = s.sp + 0xc70#64 := hx29_1.trans hx29
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun G₁ => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine P3P4.SepWPp.weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
  unfold genP3S5SpillRem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun wFront => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp))
    (by sep_focus) ?_
  have hver_step := h1e04 img ext himg hA
    s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr wFront.ud0
    hinit_ne hcap msgVer hver_ne b_2c0 enc hEnc G₁ recG st
    hst_ver4 hsp_root hF1 hsym1 hpc1 hrun1 hs1_sp hsp_align htr1
    hx9_1 hx19_1 hx24_1 hx27_1 hx29_1'
  refine SepWPp.bind_sepWPp_frame_raw hver_step (by sep_focus)
    fun sf P_f hpcf hrunf ⟨⟨wd0, hent_f⟩, hspf, htrf, hcc_f, hFf, hsymf, hopt_f_1⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hent_f) ?_
  have hopt_f_s : optVRegsEq trackVRegs sf s :=
    optVRegsEq_trans (optVRegsEq_of_vregs_eq trackVRegs hvregs1_s) hopt_f_1
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨?_, hspf, htrf, hcc_f, hFf, hsymf, hopt_f_s⟩
  unfold genP3S5PostFrame genP3S5SpillRem
  have hwFront_repack :
      ((s.sp + 0x48#64) ↦₆₄ wFront.u48) ∗
      ((s.sp + 0x50#64) ↦₆₄ wFront.u50) ∗
      ((s.sp + 0x5c#64) ↦₃₂ wFront.u5c) ∗
      ((s.sp + 0x7c#64) ↦₃₂ wFront.u7c) ∗
      ((s.sp + 0x98#64) ↦₆₄ wFront.u98) ∗
      ((s.sp + 0xd0#64) ↦₆₄ wd0) ⊢
      ∃∗ w : GenP3S5FrontRem,
        ((s.sp + 0x48#64) ↦₆₄ w.u48) ∗
        ((s.sp + 0x50#64) ↦₆₄ w.u50) ∗
        ((s.sp + 0x5c#64) ↦₃₂ w.u5c) ∗
        ((s.sp + 0x7c#64) ↦₃₂ w.u7c) ∗
        ((s.sp + 0x98#64) ↦₆₄ w.u98) ∗
        ((s.sp + 0xd0#64) ↦₆₄ w.ud0) :=
    Entails.sepExists_right ⟨wFront.u48, wFront.u50, wFront.u98, wd0, wFront.u5c, wFront.u7c⟩
      (Entails.refl _)
  exact entails_replace_sub hwFront_repack (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 600000 in
/-- Composes `OverVerNe1bacCliStmtGenExt A trackVRegs` (`+0x1bac → s0.readReg64 .x30`) from
`OverPrevDecodeCliStmtGenExt A trackVRegs`. -/
theorem overVerNe_1bac_cli_of_prevDecode_gen_ext {A : RustAlloc} {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGenExt A trackVRegs) :
    OverVerNe1bacCliStmtGenExt A trackVRegs := by
  intro img ext himg hA s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg
    hinit_ne hcap hver_ne hEnc hst_ver4 hrc_lt
    hF hsym hpc hrun hsp_align hsp_root hx29 htr
  have hpack := clonePack_vregs_4k_ok (A := A) img ext hA himg
    s0 s s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc_lt hsp_align hsp_root hF hsym hpc hrun htr
  refine bind_clone_oom_frame hpack
    (F := TokenInit img ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp)
    (by ac_rfl)
    fun s1 P1 hpc1 hrun1 ⟨hent1, htr1, hF1, hsym1, hvregs1_s⟩ => ?_
  exact overVerNe_postClone_cli_ext_ok (overVerNe_1e04_cli_of_prevDecode_gen_ext hDec)
    img ext himg hA s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg P1
    hinit_ne hcap hver_ne hEnc hst_ver4 hsp_align hsp_root hx29
    hpc1 hrun1 htr1 hvregs1_s hF1 hsym1 hent1

theorem overVerNe_1bac_cli_of_prevDecode_ext {A : RustAlloc}
    (hDec : OverPrevDecodeCliStmtExt A) :
    OverVerNe1bacCliStmtExt A :=
  overVerNe_1bac_cli_of_prevDecode_gen_ext hDec

theorem overVerNe_1bac_cli_of_prevDecode_gpr_ext {A : RustAlloc}
    (hDec : OverPrevDecodeCliGPRStmtExt A) :
    OverVerNe1bacCliGPRStmtExt A :=
  overVerNe_1bac_cli_of_prevDecode_gen_ext hDec

theorem overVerNe_1bac_cli_of_prevDecode_gen {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGen trackVRegs) :
    OverVerNe1bacCliA0StmtGen trackVRegs :=
  fun img ext himg hA =>
    overVerNe_1bac_cli_of_prevDecode_gen_ext hDec img ext himg (.of_AllocContracts hA)

theorem overVerNe_1bac_cli_of_prevDecode
    (hDec : OverPrevDecodeCliStmt) :
    OverVerNe1bacCliA0Stmt :=
  overVerNe_1bac_cli_of_prevDecode_gen hDec

theorem overVerNe_1bac_cli_of_prevDecode_gpr
    (hDec : OverPrevDecodeCliGPRStmt) :
    OverVerNe1bacCliA0GPRStmt :=
  overVerNe_1bac_cli_of_prevDecode_gen hDec

set_option maxHeartbeats 600000 in
/-- Composes `OverVerNe1778CliStmtGenExt A trackVRegs` (`+0x1778 → s0.readReg64 .x30`) from
`OverPrevDecodeCliStmtGenExt A trackVRegs`. -/
theorem overVerNe_1778_cli_of_prevDecode_gen_ext {A : RustAlloc} {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGenExt A trackVRegs) :
    OverVerNe1778CliStmtGenExt A trackVRegs := by
  intro img ext himg hA s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg
    hinit_ne hcap hver_ne hEnc hst_ver4 hrc_lt
    hF hsym hpc hrun hsp_align hsp_root hx29 htr
  have hcc : ChainClone3OkExt img.base A ext := chainClone3_ok_ext_4k hA
  have hscc : SenderChainClone3OkExt img.base A ext := senderChainClone3_ok_ext_4k hA
  have hclone := cloneGen_vregs_4k_ok (A := A) img ext hA hcc hscc himg
    s0 s s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
    whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hrc_lt hsp_align hsp_root hF hsym hpc hrun htr
  refine bind_clone_oom_frame hclone
    (F := TokenInit img ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp)
    (by ac_rfl)
    fun s1 P1 hpc1 hrun1 ⟨hent1, htr1, hF1, hsym1, hvregs1_s⟩ => ?_
  exact overVerNe_postClone_cli_ext_ok (overVerNe_1e04_cli_of_prevDecode_gen_ext hDec)
    img ext himg hA s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg P1
    hinit_ne hcap hver_ne hEnc hst_ver4 hsp_align hsp_root hx29
    hpc1 hrun1 htr1 hvregs1_s hF1 hsym1 hent1

theorem overVerNe_1778_cli_of_prevDecode_ext {A : RustAlloc}
    (hDec : OverPrevDecodeCliStmtExt A) :
    OverVerNe1778CliStmtExt A :=
  overVerNe_1778_cli_of_prevDecode_gen_ext hDec

theorem overVerNe_1778_cli_of_prevDecode_gpr_ext {A : RustAlloc}
    (hDec : OverPrevDecodeCliGPRStmtExt A) :
    OverVerNe1778CliGPRStmtExt A :=
  overVerNe_1778_cli_of_prevDecode_gen_ext hDec

theorem overVerNe_1778_cli_of_prevDecode_gen {trackVRegs : Bool}
    (hDec : OverPrevDecodeCliStmtGen trackVRegs) :
    OverVerNe1778CliA0StmtGen trackVRegs :=
  fun img ext himg hA =>
    overVerNe_1778_cli_of_prevDecode_gen_ext hDec img ext himg (.of_AllocContracts hA)

theorem overVerNe_1778_cli_of_prevDecode
    (hDec : OverPrevDecodeCliStmt) :
    OverVerNe1778CliA0Stmt :=
  overVerNe_1778_cli_of_prevDecode_gen hDec

theorem overVerNe_1778_cli_of_prevDecode_gpr
    (hDec : OverPrevDecodeCliGPRStmt) :
    OverVerNe1778CliA0GPRStmt :=
  overVerNe_1778_cli_of_prevDecode_gen hDec

/-! ## Unconditional `overPrevDecode_cli_ext` and closed `VerNe` theorems -/

private theorem overDecScratchPre_eq_prevDec (sp : BitVec 64) :
    overDecScratchPre sp = PrevDec.overDecScratchPre sp := by
  have h920 :
      memRegion (sp + 0x920#64) 112 =
        memRegion (sp + 0x920#64) 16 ∗ memRegion (sp + 0x930#64) 96 :=
    ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 16) (k := 96) (b' := sp + 0x930#64)
      rfl (by bv_omega) (by decide)
  have h930 :
      memRegion (sp + 0x930#64) 344 =
        memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 248 :=
    ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 96) (k := 248) (b' := sp + 0x990#64)
      rfl (by bv_omega) (by decide)
  have h990 :
      memRegion (sp + 0x990#64) 256 =
        memRegion (sp + 0x990#64) 248 ∗ memRegion (sp + 0xa88#64) 8 :=
    ProofLib.memRegion_split' (b := sp + 0x990#64) (n := 248) (k := 8) (b' := sp + 0xa88#64)
      rfl (by bv_omega) (by decide)
  unfold overDecScratchPre PrevDec.overDecScratchPre
  rw [h920, h930, h990]
  ac_rfl

private theorem prevDec_scratchPost_eq_ext {A : RustAlloc} (sp : BitVec 64)
    (v : Symbolic.Swarm.TRREF.B3DeserQ.SSGQ) :
    PrevDec.overDecScratchPostExt A sp v =
      Symbolic.Swarm.TRREF.B3DeserQ.prostSSGQAt A (sp + 0x930#64) v ∗
        overDecScratchPost sp := by
  unfold PrevDec.overDecScratchPostExt overDecScratchPost
  ac_rfl

private theorem overPrevElemAt_eq_exists_prevDec_ext {A : RustAlloc} (prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) :
    overPrevElemAt A prevCap prevPtr enc =
      ∃∗ encCap : BitVec 64, ∃∗ encPtr : BitVec 64,
        PrevDec.overPrevElemAtExt A prevCap prevPtr encCap encPtr enc := by
  unfold overPrevElemAt PrevDec.overPrevElemAtExt vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem prevDec_elemAt_entails_overPrevElemAt_ext {A : RustAlloc}
    (prevCap prevPtr encCap encPtr : BitVec 64) (enc : List (BitVec 8)) :
    PrevDec.overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ⊢
      overPrevElemAt A prevCap prevPtr enc := by
  rw [overPrevElemAt_eq_exists_prevDec_ext]
  exact Entails.sepExists_right encCap (Entails.sepExists_right encPtr (Entails.refl _))

private theorem prevDec_overPrevDecode_cli_ext {A : RustAlloc} :
    PrevDec.OverPrevDecodeStmtExt A :=
  PrevDec.overPrevDecode_cli_of_chain3_ext
    (Chain3.overDecArmSender_cli_of_kit_ext PrevDec.chain3CalleeKit_cli_ext)
    (Chain3.chainMerge5_ok_ext PrevDec.chain3CalleeKit_cli_ext)

set_option maxHeartbeats 400000 in
/-- Unconditional `OverPrevDecodeCliStmtExt A` (`+0x1ee8 → +0x2620`), discharged via
`PrevDec.overPrevDecode_cli_of_chain3_ext`. -/
theorem overPrevDecode_cli_ext {A : RustAlloc} : OverPrevDecodeCliStmtExt A := by
  intro img ext himg hAX s0 s prevCap prevPtr enc sess
    henc hQ hver4 hpp hkpk hF hsym hpc hrun hsp_align _hsp_le htr hx21 hx24 hx25 hx27 hx29
  conv =>
    arg 4
    rw [overPrevElemAt_eq_exists_prevDec_ext, overDecScratchPre_eq_prevDec]
    simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun encCap => SepWPp.exists_elim fun encPtr => ?_
  have hpre_eq :
      PrevDec.overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ∗
        PrevDec.overDecScratchPre s.sp ∗ A.pool ∗ stackAt s.sp overDecStackX =
      PrevDec.overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ∗
        PrevDec.overDecScratchPre s.sp ∗ stackAt s.sp PrevDec.overDecStackX ∗ A.pool := by
    dsimp only [overDecStackX, PrevDec.overDecStackX]
    ac_rfl
  rw [hpre_eq]
  have hwp := prevDec_overPrevDecode_cli_ext img ext himg hAX s0 s prevCap prevPtr encCap encPtr
    enc sess ⟨henc, hQ, hver4, hpp, hkpk⟩ hF hsym hpc hrun hsp_align htr hx21 hx24 hx25 hx27 hx29
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', P_f, hmf, hent_f, hsp', htr', hFf, hsymf,
    hx19', hx20', hx21', hx24', hx25', _hx26', hx27', hx29_c70, hvregs'⟩ | hpan⟩ := hwp R hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', P_f, hmf, ?_,
      hsp', htr', hx19', hx20', hx21', hx24', hx25', hx27',
      hx29_c70.trans hx29.symm, hvregs', hFf, hsymf⟩⟩
    refine Entails.trans hent_f ?_
    rw [prevDec_scratchPost_eq_ext]
    refine Entails.trans (sepConj_mono_left (prevDec_elemAt_entails_overPrevElemAt_ext
      prevCap prevPtr encCap encPtr enc)) ?_
    dsimp only [overDecStackX, PrevDec.overDecStackX]
    exact Entails.of_eq (by ac_rfl)
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem overPrevDecode_cli : OverPrevDecodeCliStmt :=
  overPrevDecode_cli_ext (A := A0)

/-- Unconditional Stage P3/P4 `VerNe` at `+0x1e04` (`OverVerNe1e04CliStmtExt A`) under `AllocContractsMem4K`. -/
theorem overVerNe_1e04_cli_ext {A : RustAlloc} : OverVerNe1e04CliStmtExt A :=
  overVerNe_1e04_cli_of_prevDecode_ext overPrevDecode_cli_ext

/-- Unconditional Stage P3/P4 `VerNe` at `+0x1bac` (`OverVerNe1bacCliStmtExt A`) under `AllocContractsMem4K`. -/
theorem overVerNe_1bac_cli_ext {A : RustAlloc} : OverVerNe1bacCliStmtExt A :=
  overVerNe_1bac_cli_of_prevDecode_ext overPrevDecode_cli_ext

/-- Unconditional Stage P3/P4 `VerNe` at `+0x1778` (`OverVerNe1778CliStmtExt A`) under `AllocContractsMem4K`. -/
theorem overVerNe_1778_cli_ext {A : RustAlloc} : OverVerNe1778CliStmtExt A :=
  overVerNe_1778_cli_of_prevDecode_ext overPrevDecode_cli_ext

theorem overVerNe_1e04_cli_a0 : OverVerNe1e04CliA0Stmt :=
  overVerNe_1e04_cli_of_prevDecode overPrevDecode_cli

theorem overVerNe_1bac_cli_a0 : OverVerNe1bacCliA0Stmt :=
  overVerNe_1bac_cli_of_prevDecode overPrevDecode_cli

theorem overVerNe_1778_cli_a0 : OverVerNe1778CliA0Stmt :=
  overVerNe_1778_cli_of_prevDecode overPrevDecode_cli

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
