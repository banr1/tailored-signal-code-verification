/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneGen
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1Err
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P3 Over-Path Specification (`previous_sessions = [enc]`)

Proves `stageP3Gen_prev1_vregs_ok` and its 4K-stack variants (`+0x1778 → +0x34dc` on `Ok(pt)` or
`s0.readReg64 .x30` on decrypt/version-mismatch error) over a 1-element `previous_sessions` vector
`prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.Cli.LibsignalTripleRatchet.ChainClone3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.SignalSession

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Scratch Regions, Stage P3 Predicates, and Seam Statements -/

/-- Closure-frame scratch slots `[+0x538..+0x930)`, `[+0x990..+0xa90)`, and `[+0xbe8..+0xc70)` used
by the inlined `SessionStructure::decode` on the `VerNe` previous-session loop (`+0x1e78`). -/
def overScratch (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x538#64) 1016 ∗
  memRegion (sp + 0x990#64) 256 ∗
  memRegion (sp + 0xbe8#64) 136

/-- Extra Substage P3.5 resources holding a 1-element `prevVecAt [enc]` and `overScratch`. -/
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

/-- Stage P3 dispatch precondition at `+0x1cd8` over a 1-element `prevVecAt [enc]`. -/
def stageP3DispatchPrePrev1 (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64) (enc : List (BitVec 8))
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  vecResultAt A (s.sp + 0x270#64) res ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Stage P3 `Ok(pt)` postcondition at `+0x34dc`, preserving `prevVecAt [enc]` into Stage P4. -/
def stageP3DispatchOkMidPrev1 (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (enc pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  sessionStateAt A (coroPtr + 0xf8#64) G₂ st₂ ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

/-- Version-mismatch exit specification (`+0x1e04 → s0.readReg64 .x30` when `msgVer ≠ 4#32`) at
allocator `A`, parameterized by `PrevEncOK`. -/
def OverVerNe1e04CliAtStmt (A : RustAlloc) (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    AllocContracts img.base A ext →
    ∀ (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
      ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)), PrevEncOK enc →
      ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
        st.version = 4#32 →
        rootStack ≤ s.sp.toNat →
        img.FrozenLoaded s1 →
        s1.symtab = img.symtab →
        s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        s1.readReg64 .x29 = s.sp + 0xc70#64 →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
          (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
           ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
           ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
           ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
           ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
           ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
           ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
           ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
           ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
           ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
           memRegion (s.sp + 0x3e0#64) 344 ∗
           memRegion (s.sp + 0x930#64) 48 ∗
           memRegion (s.sp + 0x960#64) 48 ∗
           overScratch s.sp ∗
           sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
           sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
           prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
           ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
           logOff img ∗
           memRegion outPtr 48 ∗
           memRegion (s.sp + 0x250#64) 20 ∗
           memRegion (s.sp + 0x270#64) 48 ∗
           memRegion (s.sp + 0x370#64) 36 ∗
           decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
           A.pool ∗
           stackAt s.sp rootStack)
          (fun sf P_f =>
            (∃ wd0 : BitVec 64,
              P_f ⊢
                ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
                ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
                ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
                ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
                memRegion (s.sp + 0x3e0#64) 344 ∗
                memRegion (s.sp + 0x960#64) 48 ∗
                overScratch s.sp ∗
                memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
                stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
                  (.invalidMessage .preKey .decryptionFailed) ∗
                anyHeap) ∧
            sf.sp = s.sp + 0xcd0#64 ∧
            sf.trace = s0.trace ∧
            ClosureCalleeSaved s0 sf ∧
            img.FrozenLoaded sf ∧
            sf.symtab = img.symtab ∧
            calleeSavedVRegs sf = calleeSavedVRegs s1)
          (P3P4.PanicOomProp s0)

def OverVerNe1e04CliStmt (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ {A : RustAlloc}, OverVerNe1e04CliAtStmt A PrevEncOK

/-- Stage P3 specification (`+0x1778 → +0x34dc` or `s0.readReg64 .x30`) over a 1-element
`prevVecAt [enc]` at allocator `A`. -/
def StageP3Prev1VRegsAtStmt (A : RustAlloc) (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContracts img.base A ext →
    ChainClone3OkExt img.base A ext →
    SenderChainClone3OkExt img.base A ext →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8)
      (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 →
      prevCap ≠ 0#64 →
      PrevEncOK enc →
      st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st →
      st.receiverChains.length < 2 ^ 32 →
      st.pqRatchetState.length < 2 ^ 32 →
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat →
        ptCap.toNat < 2 ^ 63 →
        ptPtr ≠ 0#64 →
        Steps (tripleRatchetProgAtExt img.base ext) s s' →
        s'.pc = closureEntry img ext + 0x34dc#64 →
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
        img.FrozenLoaded s' →
        s'.symtab = img.symtab →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1 A img.base s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            ptCap ptPtr enc pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer →
        CloneRel recG G₁ →
        G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e →
        e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr e ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
          overScratch s.sp ∗
          anyHeap) →
        sf.sp = s.sp + 0xcd0#64 →
        sf.trace = s0.trace →
        ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        img.FrozenLoaded sf →
        sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp ∗
          F_frame)
        Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

def StageP3Prev1VRegsStmt (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ {A : RustAlloc}, StageP3Prev1VRegsAtStmt A PrevEncOK

abbrev OverVerNe1e04CliAtBody (A : RustAlloc) (PrevEncOK : List (BitVec 8) → Prop)
    (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  ∀ (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr ud0 : BitVec 64),
    initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 →
    ∀ (msgVer : BitVec 32), msgVer ≠ 4#32 →
    ∀ (b_2c0 : BitVec 8) (enc : List (BitVec 8)), PrevEncOK enc →
    ∀ (G₁ recG : SessionGhost) (st : SessionState (List (BitVec 8))),
      st.version = 4#32 → rootStack ≤ s.sp.toNat → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64 →
      s1.status = .Running → s1.sp = s.sp → (s.sp &&& 15#64 == 0#64) = true → s1.trace = s0.trace →
      s1.readReg64 .x9 = msgVer.setWidth 64 → s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 → s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
        (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ ud0) ∗
         ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0x930#64) 48 ∗
         memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
         sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
         prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
         logOff img ∗ memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗
         memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
         decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp rootStack)
        (fun sf P_f =>
          (∃ wd0 : BitVec 64, P_f ⊢
              ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
              ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
              memRegion (s.sp + 0x960#64) 48 ∗ overScratch s.sp ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
              stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
                (.invalidMessage .preKey .decryptionFailed) ∗ anyHeap) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
        (P3P4.PanicOomProp s0)

def OverVerNe1e04CliAt4KStmt (A : RustAlloc) (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img → AllocContractsMem4K img.base A ext →
    OverVerNe1e04CliAtBody A PrevEncOK img ext

def OverVerNe1e04Cli4KStmt (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ {A : RustAlloc}, OverVerNe1e04CliAt4KStmt A PrevEncOK

theorem OverVerNe1e04CliAt4KStmt.toAtStmt {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (h : OverVerNe1e04CliAt4KStmt A PrevEncOK) : OverVerNe1e04CliAtStmt A PrevEncOK :=
  fun img ext himg hA => h img ext himg (AllocContractsMem4K.of_AllocContracts hA)

/-- 4K-stack Stage P3 specification (`+0x1778 → +0x34dc` or `s0.readReg64 .x30`) over a 1-element
`prevVecAt [enc]` at allocator `A`. -/
def StageP3Prev1VRegsAt4KStmt (A : RustAlloc) (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem),
    AllocContractsMem4K img.base A ext →
    ChainClone3OkExt img.base A ext →
    SenderChainClone3OkExt img.base A ext →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A) →
    Obj.Loads libsignalSessionImage img →
    ∀ (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
        remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      initErrsPtr ≠ 0#64 → prevCap ≠ 0#64 → PrevEncOK enc → st.version = 4#32 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      img.FrozenLoaded s → s.symtab = img.symtab → s.pc = closureEntry img ext + 0x1778#64 →
      s.status = .Running → (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.readReg64 .x29 = s.sp + 0xc70#64 → s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (tripleRatchetProgAtExt img.base ext) s s' →
        s'.pc = closureEntry img ext + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp →
        s'.trace = s0.trace → calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        img.FrozenLoaded s' → s'.symtab = img.symtab →
        (P_s' ⊢
          stageP3DispatchOkMidPrev1 A img.base s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
            ptCap ptPtr enc pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr e ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg
            (Coins.coinsAfter img.base cur rest
              (decryptDraws C st msg.senderRatchetKey rest)) ∗
          overScratch s.sp) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → img.FrozenLoaded sf → sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      (∀ (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
          overScratch s.sp ∗ anyHeap) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → img.FrozenLoaded sf → sf.symtab = img.symtab →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (TokenInit img ∗
          genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp ∗ F_frame)
        Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)

def StageP3Prev1VRegs4KStmt (PrevEncOK : List (BitVec 8) → Prop) : Prop :=
  ∀ {A : RustAlloc}, StageP3Prev1VRegsAt4KStmt A PrevEncOK

theorem StageP3Prev1VRegsAt4KStmt.toAtStmt {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (h : StageP3Prev1VRegsAt4KStmt A PrevEncOK) : StageP3Prev1VRegsAtStmt A PrevEncOK :=
  fun img ext C ctl K hA => h img ext C ctl K (AllocContractsMem4K.of_AllocContracts hA)

/-! ## Stage P3 Composition (`stageP3Gen_prev1_vregs_ok`) -/

private theorem bind_sepWP_frame_steps_prev1 {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hstep : SepWP prog mid s P_step (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpc hrun (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem sepWPp_frame_closOom_prev1 {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P F_frame : SepProp} {Q : State → SepProp → Prop}
    (hwp : SepWPp prog ret s P (fun sf P_f => Q sf (P_f ∗ F_frame)) (PanicOomProp s0)) :
    SepWPp prog ret s (P ∗ F_frame) Q (PanicOomProp s0) := by
  intro R hm hL; rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | ⟨hpan, P_f, hmf, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hwp (F_frame ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf; exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f ∗ F_frame, hmf, hQ⟩⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F_frame, hmf, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hoom (F_frame ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem bind_sepWPp_genPanic_steps_framed_prev1 {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {C : Crypto} {K : LibsignalSpqrV1.MlKem}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {P P_stage F F_frame : SepProp} {Q_mid Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (PanicOomProp s0)) (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, Steps prog s sm → sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm ((P_m ∗ F) ∗ F_frame) Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp prog ret s (P ∗ F_frame) Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hm0 : s.mem ⊨ P_stage ∗ ((F ∗ F_frame) ∗ R) := by
    rw [hP] at hm; simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨hpan, P_m, hmm, hoom⟩ | ⟨_, hoom⟩⟩ :=
    hstage ((F ∗ F_frame) ∗ R) hm0 hL
  · have hmm' : sm.mem ⊨ ((P_m ∗ F) ∗ F_frame) ∗ R := by simpa only [sepConj_assoc] using hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm P_m hsteps hpcm hrunm hqm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ (F ∗ F_frame), hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hoom ((F ∗ F_frame) ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem postTryDecrypt_entails_s5DispatchPrev1 {A : RustAlloc} (img : Obj.Image)
    (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (enc : List (BitVec 8)) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
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
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp) ⊢
    stageP3DispatchPrePrev1 A img.base s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc
      res b_2c0 G' recG st₂ st ∗
    genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
      rem loc msgG msg coinsPost ∗
    overScratch s.sp := by
  unfold stageP3Sub5ExtraPrePrev1 stageP3DispatchPrePrev1 genP3S5PostFrame
  have hlog :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  rw [hlog, stackAt_root_split_grow s.sp, ← memRegion344_104_240_eq s.sp]
  exact entails_replace_sub (genP3SpillAll_entails_s5 s.sp)
    (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

private theorem stageP3_clone_prev1_vregs_prefix_steps
    {A : RustAlloc} (img : Obj.Image) (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State))
    (s0 s : State) (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (enc : List (BitVec 8)) (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hstep : SepWPp (tripleRatchetProgAtExt img.base ext)
      (cloneExitPC img ext st msgVer) s
      (genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0))
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s s1 →
      s1.pc = cloneExitPC img ext st msgVer → s1.status = .Running → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      (P1 ⊢
        genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (TokenInit img ∗
          stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
          overScratch s.sp ∗
          F_frame)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp ∗
        F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  let F : SepProp :=
    TokenInit img ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp ∗ F_frame
  have hP :
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp ∗
        F_frame) =
      genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    dsimp only [F]; ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps,
      ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hF1, hsym1, hvregs1_s⟩ |
      ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1 (hvregs1_s.trans hvregs) hF1 hsym1
        (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨s1, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, Or.inl (fun R' hmR' => by
      rw [sepConj_assoc] at hmR'; have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1; exact allowPanic_frame id h1)⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
private theorem stageP3_call_tryDecrypt_prev1_steps {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State)) (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (hroot : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img))
    (s0 s s1 : State) (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F : SepProp) (Q : State → SepProp → Prop)
    (hver : st.version = msgVer)
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st) (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hF1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hpc1 : s1.pc = closureEntry img ext + 0x1cd4#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (htr1 : s1.trace = s0.trace)
    (hx0_1 : s1.readReg64 .x0 = s.sp + 0x270#64) (hx1_1 : s1.readReg64 .x1 = s.sp + 0xa90#64)
    (hx2_1 : s1.readReg64 .x2 = remAddrPtr) (hx3_1 : s1.readReg64 .x3 = locAddrPtr)
    (hx4_1 : s1.readReg64 .x4 = whisperMsgPtr) (hx5_1 : s1.readReg64 .x5 = 3#64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hCont : ∀ (s2 : State) (G' : SessionGhost),
      Steps (tripleRatchetProgAtExt img.base ext) s1 s2 →
      (genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic →
      G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G' →
      s2.pc = closureEntry img ext + 0x1cd8#64 → s2.status = .Running →
      s2.sp = s.sp → s2.trace = s0.trace → img.FrozenLoaded s2 → s2.symtab = img.symtab →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x24 = s.sp + 0x370#64 →
      s2.readReg64 .x27 = ctxPtr → calleeSavedVRegs s2 = calleeSavedVRegs s1 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2
        ((TokenInit img ∗
          sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
          signalMessageAt A msgG whisperMsgPtr msg ∗
          Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          logOff img ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F)
        Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1
      ((TokenInit img ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        Coins.coinsAt img.base cur rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  have hbl := p3_bl_tryDecrypt_ext_wp img.base ext s1 hpc1 hrun1
  refine bind_sepWP_frame_steps_prev1 hF1 hsym1 hbl (emp_sepConj _).symm
    fun sc hsteps_bl hpcc hrunc hFc hsymc hregsc => ?_
  rw [emp_sepConj]
  rcases hregsc with ⟨hspc_1, htrc_1, hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c, _,
    hx19_c, hx24_c, hx27_c, _, hx30_c, hvregs_c⟩
  have hspc : sc.sp = s.sp := hspc_1.trans hs1_sp
  have hspc_al : sc.spAligned = true := by simpa only [State.spAligned, hspc] using hsp_align
  have htrc_0 : sc.trace = s0.trace := htrc_1.trans htr1
  let x : TryDecryptGhost := {
    G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
    msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
    msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest
  }
  intro R hm hL
  have hpre_c :
      sc.mem ⊨
        (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
          (LibsignalSpqrV1.spqrV1 C.F K) img).pre x sc ∗ (F ∗ R) := by
    dsimp only [_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
      _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP, Spec.inImage, x]
    rw [hspc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_lt, ?_⟩
    rw [← sepConj_assoc] at hm
    have hx5_byte : (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey := by
      rw [hx5_c, hx5_1]; rfl
    have hp1 : (img.FrozenLoaded sc ∧ sc.symtab = img.symtab) = True :=
      propext ⟨fun _ => trivial, fun _ => ⟨hFc, hsymc⟩⟩
    have hp2 : (sc.readReg64 .x0 = s.sp + 0x270#64 ∧ sc.readReg64 .x1 = s.sp + 0xa90#64 ∧
        sc.readReg64 .x2 = remAddrPtr ∧ sc.readReg64 .x3 = locAddrPtr ∧
        sc.readReg64 .x4 = whisperMsgPtr ∧ (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey ∧
        (st.remoteIdentity ≠ some st.localIdentity ∨
          DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) ∧
        SeedsLen32 st ∧ st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat) = True :=
      propext ⟨fun _ => trivial, fun _ =>
        ⟨hx0_c.trans hx0_1, hx1_c.trans hx1_1, hx2_c.trans hx2_1, hx3_c.trans hx3_1,
         hx4_c.trans hx4_1, hx5_byte, hnot_self, hseeds, hrc_lt, hsp_root⟩⟩
    rw [hp1, hp2, pure_true, emp_sepConj, emp_sepConj]
    simpa only [sepConj_assoc] using hm
  obtain ⟨s2, hsteps2,
      ⟨⟨hpc2_lr, hsp2_c, hrun2⟩, ⟨_, hcs2⟩, hm2⟩ | ⟨hpan, hm_pan⟩ | ⟨_, _, hexit⟩ | ⟨_, hoom⟩, -⟩ :=
    hroot.no_fault_before_outcome x (F ∗ R) sc hpcc hrunc hpre_c hspc_al hL
  · dsimp only [_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
      _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP,
      _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec,
      Spec.inImage, TryDecryptGhost.model, x] at hm2
    rw [hspc] at hm2
    have hF2 : img.FrozenLoaded s2 := hsteps2.frozenLoaded hFc
    have hsym2 : s2.symtab = img.symtab := hsteps2.symtab_eq.trans hsymc
    have hm2_pull :
        s2.mem ⊨
          ⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
          ((∃∗ G' : SessionGhost,
              ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
              sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
            TokenInit img ∗ vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ F ∗ R) := by
      have heq :
          (TokenInit img ∗
            (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
              (∃∗ G' : SessionGhost,
                ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
              vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
              protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
              signalMessageAt A msgG whisperMsgPtr msg ∗
              Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
              logOff img ∗ stackAt s.sp rootStack ∗ A.pool)) ∗ (F ∗ R) =
          ⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
          ((∃∗ G' : SessionGhost,
              ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
              sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2) ∗
            TokenInit img ∗ vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ F ∗ R) := by ac_rfl
      rwa [heq] at hm2
    rw [satisfies_pure_sepConj] at hm2_pull
    rcases hm2_pull with ⟨⟨hnpan, htr2_c⟩, hm2_ex⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_ex
    obtain ⟨G', hm2_G⟩ := hm2_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2_G
    obtain ⟨hdec_rel, hm2_rest⟩ := hm2_G
    have hm2_cont :
        s2.mem ⊨
          ((TokenInit img ∗
            sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            logOff img ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F) ∗ R := by
      have heq2 :
          sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          (TokenInit img ∗ vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            logOff img ∗ stackAt s.sp rootStack ∗ A.pool ∗ F ∗ R) =
          ((TokenInit img ∗
            sessionStateAt A (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
            signalMessageAt A msgG whisperMsgPtr msg ∗
            Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            logOff img ∗ stackAt s.sp rootStack ∗ A.pool) ∗ F) ∗ R := by ac_rfl
      rwa [heq2] at hm2_rest
    rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, _, _, hx27_cs2, _, _, hvregs_cs2⟩
    obtain ⟨sf, hsteps3, hout3⟩ :=
      hCont s2 G' (hsteps_bl.trans hsteps2) hnpan hdec_rel (hpc2_lr.trans hx30_c) hrun2
        (hsp2_c.trans hspc) (htr2_c.trans htrc_0) hF2 hsym2
        (hx19_cs2.trans (hx19_c.trans hx19_1)) (hx24_cs2.trans (hx24_c.trans hx24_1))
        (hx27_cs2.trans (hx27_c.trans hx27_1)) (hvregs_cs2.trans hvregs_c)
        R hm2_cont (hsteps2.codeLoaded hL)
    exact ⟨sf, hsteps2.trans hsteps3, hout3⟩
  · dsimp only [_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
      _root_.CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight,
      TryDecryptGhost.model, x] at hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pan
    rcases hm_pan with ⟨⟨hpan_or, hpref_c⟩, hm_any⟩
    have hpref_0 : s0.trace <+: s2.trace := htrc_0 ▸ hpref_c
    have hm_any_R : s2.mem ⊨ anyHeap ∗ R := by
      rw [← sepConj_assoc] at hm_any
      exact Arm64.Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_any
    rcases hpan_or with hmod_pan | hoom_pan
    · refine ⟨s2, hsteps2, Or.inr (Or.inl ⟨hpan,
        ⌜st.version = msgVer ∧ (genP3S5Model C K rem loc msg rest st).1 = .error .panic ∧
            s0.trace <+: s2.trace⌝ ∗ anyHeap, ?_, Or.inr (fun _ h => h)⟩)⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hver, hmod_pan, hpref_0⟩, hm_any_R⟩
    · have hoom_0 : allocFailedIn s0 s2 := by unfold allocFailedIn at hoom_pan ⊢; rwa [← htrc_0]
      refine ⟨s2, hsteps2, Or.inr (Or.inl ⟨hpan,
        ⌜allocFailedIn s0 s2 ∧ s0.trace <+: s2.trace⌝ ∗ anyHeap, ?_, Or.inl (fun _ h => h)⟩)⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hoom_0, hpref_0⟩, hm_any_R⟩
  · exact (not_satisfies_false_sepConj hexit).elim
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
private theorem stageP3Gen_prev1_vregs_at_core {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (img : Obj.Image) (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (hA4k : AllocContractsMem4K img.base A ext)
    (hroot : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (_root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img))
    (himg : Obj.Loads libsignalSessionImage img) (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (b_2c0 : BitVec 8) (enc rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hinit_ne : initErrsPtr ≠ 0#64) (hcap_nz : prevCap ≠ 0#64)
    (hEnc : PrevEncOK enc) (hst_ver4 : st.version = 4#32)
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st) (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hx29_s : s.readReg64 .x29 = s.sp + 0xc70#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCloneStep : SepWPp (tripleRatchetProgAtExt img.base ext)
      (cloneExitPC img ext st msgVer) s
      (genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧ img.FrozenLoaded s1 ∧ s1.symtab = img.symtab ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0))
    (hVerNeAt : OverVerNe1e04CliAtBody A PrevEncOK img ext)
    (hOk : ∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
        (s' : State) (P_s' : SepProp),
      st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
      (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
      pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
      Steps (tripleRatchetProgAtExt img.base ext) s s' →
      s'.pc = closureEntry img ext + 0x34dc#64 → s'.status = .Running → s'.sp = s.sp →
      s'.trace = s0.trace → calleeSavedVRegs s' = calleeSavedVRegs s0 →
      s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
      s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
      s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
      img.FrozenLoaded s' → s'.symtab = img.symtab →
      (P_s' ⊢
        stageP3DispatchOkMidPrev1 A img.base s0 s coroPtr outPtr initErrsPtr prevCap prevPtr
          ptCap ptPtr enc pt b_2c0 G' (genP3S5Model C K rem loc msg rest st).2 ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
        overScratch s.sp) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
        (genP3S5PanicProp C K rem loc st msg msgVer rest s0))
    (hErr : ∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (sf : State) (P_f : SepProp),
      st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
      (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr e ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg
          (Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest)) ∗
        overScratch s.sp) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → img.FrozenLoaded sf → sf.symtab = img.symtab →
      Q sf (P_f ∗ F_frame))
    (hVerNe : ∀ (sf : State) (P_f : SepProp),
      st.version ≠ msgVer →
      (P_f ⊢
        ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
        stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr
          (.invalidMessage .preKey .decryptionFailed) ∗
        genP3S5PostFrame A img s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
          rem loc msgG msg (Coins.coinsAt img.base cur rest) ∗
        overScratch s.sp ∗ anyHeap) →
      sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → img.FrozenLoaded sf → sf.symtab = img.symtab →
      Q sf (P_f ∗ F_frame)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (TokenInit img ∗
        genP3Pre A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp ∗ F_frame)
      Q (genP3S5PanicProp C K rem loc st msg msgVer rest s0) := by
  refine stageP3_clone_prev1_vregs_prefix_steps img C K ext
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur enc msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hvregs hCloneStep
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hF1 hsym1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 ?_
  refine SepWPp.weaken_pre
    (P' := (genP3Post A img s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (TokenInit img ∗
        stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
        overScratch s.sp)) ∗ F_frame)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPC, genP3Post, hver, ↓reduceIte] at hpc1 ⊢
    unfold genP3PostEq genP3PostSpatial
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine P3P4.SepWPp.weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    let F_dec : SepProp :=
      sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrev1 A s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc b_2c0 ∗
      overScratch s.sp
    refine SepWPp.weaken_pre
      (P' := (TokenInit img ∗ sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A rem remAddrPtr ∗ protocolAddressAt A loc locAddrPtr ∗
        signalMessageAt A msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        Coins.coinsAt img.base cur rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
        A.pool) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (P3P4.eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_prev1_steps img ext C ctl K hroot
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hF1 hsym1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' hsteps12 hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hF2 hsym2 hx19_2 hx24_2 hx27_2
          hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (tripleRatchetProgAtExt img.base ext) s s2 := hsteps01.trans hsteps12
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrev1 img s0 s coroPtr ctxPtr outPtr initErrsPtr
            prevCap prevPtr remAddrPtr locAddrPtr whisperMsgPtr enc msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (Coins.coinsAfter img.base cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrev1
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have herr := stageP3_sub5_err_prev1_ext_4k_ok img img.base ext himg rfl hA4k
        s0 s2 coroPtr outPtr initErrsPtr prevCap prevPtr hinit_ne e he_npan b_2c0 enc
        G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hF2 hsym2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrev1 at herr
      have herr_post :
          stageP3ErrPostPrevEmpty A img.base s0 s2 coroPtr outPtr e =
            stageP3ErrPostPrevEmpty A img.base s0 s coroPtr outPtr e := by
        unfold stageP3ErrPostPrevEmpty; rw [hs2_sp]
      rw [herr_post, hs2_sp] at herr
      apply sepWPp_lift_panicOom
      apply sepWPp_frame_closOom_prev1
      refine P3P4.SepWPp.ret_sepWPp_frame herr (by sep_focus)
        fun sf _ _ ⟨hspf, htrf, hcc_f, hFf, hsymf, hvregsf_2⟩ => ?_
      refine hErr G₁ G' e sf _ hver hclone_rel hdec_false hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hFf hsymf
      exact Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus))
    · have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
      have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hok := stageP3_sub5_decResult_ext_4k_ok img img.base ext hA4k
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hb_align hF2 hsym2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_genPanic_steps_framed_prev1 hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨ptCap, ptPtr, hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hF', hsym', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      refine hOk G₁ G' pt ptCap ptPtr s' _ hver hclone_rel hdec_true hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hF' hsym' ?_
      unfold stageP3DispatchOkMidPrev1
      rw [hstack_set]
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPC, genP3Post, hver, ↓reduceIte] at hpc1 ⊢
    have hmsgVer_ne4 : msgVer ≠ 4#32 := fun h => hver (hst_ver4.trans h.symm)
    apply sepWPp_lift_panicOom
    apply sepWPp_frame_closOom_prev1
    unfold genP3PostNe genP3PostSpatial stageP3Sub5ExtraPrePrev1
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, hx29_1⟩ => ?_
    have hx29_1' : s1.readReg64 .x29 = s.sp + 0xc70#64 := hx29_1.trans hx29_s
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
    have hver_ne := hVerNeAt
      s0 s s1 coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr wFront.ud0
      hinit_ne hcap_nz msgVer hmsgVer_ne4 b_2c0 enc hEnc G₁ recG st
      hst_ver4 hsp_root hF1 hsym1 hpc1 hrun1 hs1_sp hsp_align htr1
      hx9_1 hx19_1 hx24_1 hx27_1 hx29_1'
    refine SepWPp.bind_sepWPp_frame_raw hver_ne (by sep_focus)
      fun sf P_f hpcf hrunf ⟨⟨wd0, hent_f⟩, hspf, htrf, hcc_f, hFf, hsymf, hvregsf_1⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hent_f) ?_
    refine SepWPp.done hpcf hrunf ?_
    refine hVerNe sf _ hver ?_ hspf htrf hcc_f (hvregsf_1.trans hvregs1) hFf hsymf
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

/-- 4K-stack Stage P3 over a 1-element `prevVecAt [enc]` given `CloneGenVRegsStmt4K` and
`OverVerNe1e04CliAt4KStmt`. -/
theorem stageP3Gen_prev1_vregs_at_4k_ok_of_clone {A : RustAlloc}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hClone : CloneGenVRegsStmt4K) (hVerNeStmt : OverVerNe1e04CliAt4KStmt A PrevEncOK) :
    StageP3Prev1VRegsAt4KStmt A PrevEncOK := by
  intro img ext C ctl K hA hcc hscc hroot _hdropSs3 himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hF hsym hpc hrun hsp_align hsp_root hx29_s htr hvregs
    hOk hErr hVerNe
  exact stageP3Gen_prev1_vregs_at_core img ext C ctl K hA hroot himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hsp_align hsp_root hx29_s hvregs
    (hClone img ext hA hcc hscc himg s0 s s.sp (s.readReg64 .x29)
      coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
      hrc_lt hsp_align hsp_root hF hsym hpc hrun htr)
    (hVerNeStmt img ext himg hA)
    hOk hErr hVerNe

theorem stageP3Gen_prev1_vregs_at_4k_ok {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (hVerNe : OverVerNe1e04CliAt4KStmt A PrevEncOK) :
    StageP3Prev1VRegsAt4KStmt A PrevEncOK :=
  stageP3Gen_prev1_vregs_at_4k_ok_of_clone cloneGen_vregs_4k_ok hVerNe

theorem stageP3Gen_prev1_vregs_4k_ok_of_clone {PrevEncOK : List (BitVec 8) → Prop}
    (hClone : CloneGenVRegsStmt4K) (hVerNeStmt : OverVerNe1e04Cli4KStmt PrevEncOK) :
    StageP3Prev1VRegs4KStmt PrevEncOK :=
  fun {A} => stageP3Gen_prev1_vregs_at_4k_ok_of_clone hClone (hVerNeStmt (A := A))

theorem stageP3Gen_prev1_vregs_4k_ok {PrevEncOK : List (BitVec 8) → Prop}
    (hVerNe : OverVerNe1e04Cli4KStmt PrevEncOK) :
    StageP3Prev1VRegs4KStmt PrevEncOK :=
  fun {A} => stageP3Gen_prev1_vregs_at_4k_ok (hVerNe (A := A))

theorem stageP3Gen_prev1_vregs_at_ok_of_clone {A : RustAlloc}
    {PrevEncOK : List (BitVec 8) → Prop}
    (hClone : CloneGenVRegsStmt) (hVerNeStmt : OverVerNe1e04CliAtStmt A PrevEncOK) :
    StageP3Prev1VRegsAtStmt A PrevEncOK := by
  intro img ext C ctl K hA hcc hscc hroot _hdropSs3 himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hF hsym hpc hrun hsp_align hsp_root hx29_s htr hvregs
    hOk hErr hVerNe
  exact stageP3Gen_prev1_vregs_at_core img ext C ctl K (AllocContractsMem4K.of_AllocContracts hA) hroot himg
    s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 enc rest
    recG st rem loc msgG msg F_frame Q
    hinit_ne hcap_nz hEnc hst_ver4 hnot_self hseeds hrc_lt hpq_lt
    hsp_align hsp_root hx29_s hvregs
    (hClone img ext hA hcc hscc himg s0 s s.sp (s.readReg64 .x29)
      coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
      hrc_lt hsp_align hsp_root hF hsym hpc hrun htr)
    (hVerNeStmt img ext himg hA)
    hOk hErr hVerNe

theorem stageP3Gen_prev1_vregs_at_ok {A : RustAlloc} {PrevEncOK : List (BitVec 8) → Prop}
    (hVerNe : OverVerNe1e04CliAtStmt A PrevEncOK) :
    StageP3Prev1VRegsAtStmt A PrevEncOK :=
  stageP3Gen_prev1_vregs_at_ok_of_clone cloneGen_vregs_ok hVerNe

theorem stageP3Gen_prev1_vregs_ok_of_clone {PrevEncOK : List (BitVec 8) → Prop}
    (hClone : CloneGenVRegsStmt) (hVerNeStmt : OverVerNe1e04CliStmt PrevEncOK) :
    StageP3Prev1VRegsStmt PrevEncOK :=
  fun {A} => stageP3Gen_prev1_vregs_at_ok_of_clone hClone (hVerNeStmt (A := A))

/-- Stage P3 (`+0x1778 → +0x34dc` or `s0.readReg64 .x30`) over a 1-element `prevVecAt [enc]`,
parameterized by `OverVerNe1e04CliStmt PrevEncOK`. -/
theorem stageP3Gen_prev1_vregs_ok {PrevEncOK : List (BitVec 8) → Prop}
    (hVerNe : OverVerNe1e04CliStmt PrevEncOK) :
    StageP3Prev1VRegsStmt PrevEncOK :=
  fun {A} => stageP3Gen_prev1_vregs_at_ok (hVerNe (A := A))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
