/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone Segment Statements

Defines the segment statement predicates (`CloneKeysFrontStmt`, `CloneRecvChainsStmt`,
`ClonePendingsStmt`, `CloneKeysBackStmt`, `PackAndVerCmpStmt`, `CloneGenStmt`, and `*Stmt4K`
variants) for the general `SessionState` clone and version-dispatch pipeline (`+0x1778 →
+0x1cd4 / +0x1e04`) on `tripleRatchetProgAtExt img.base ext`.
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

/-- Closure entry address in `tripleRatchetProgAtExt img.base ext`. -/
noncomputable abbrev closureEntry (img : Obj.Image)
    (ext : String → Option (State → State)) : BitVec 64 :=
  (tripleRatchetProgAtExt img.base ext).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

/-- Post-pack exit PC (`+0x1cd4` when `st.version = msgVer`, `+0x1e04` when `st.version ≠ msgVer`). -/
noncomputable abbrev cloneExitPC (img : Obj.Image)
    (ext : String → Option (State → State))
    (st : SessionState (List (BitVec 8))) (msgVer : BitVec 32) : BitVec 64 :=
  if st.version = msgVer then
    closureEntry img ext + 0x1cd4#64
  else
    closureEntry img ext + 0x1e04#64

/-- Segment 1 (`+0x1778 → +0x19b0`, `genP3Pre → genP3J1`):
Clones `local_identity_public`, `remote_identity_public`, `root_key`, and `sender_chain`
(calling `Chain::clone [local#5]` at `+0x1978` via `hscc`, with OOM exits at `+0x3774`, `+0x3768`,
`+0x375c`, and inside `Chain::clone`). -/
def CloneKeysFrontStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
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
        (closureEntry img ext + 0x19b0#64) s
        (genP3Pre A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J1 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

/-- Segment 2 (`+0x19b0 → +0x1a5c`, `genP3J1 → genP3J2`):
Spills `[sp + 0x60..0x78)` and clones `receiver_chains` (empty fast-path `mov w25, #8` or
`__rust_alloc(len * 104, 8)` + counted `Chain::clone [local#5]` loop at `+0x1a14` via `hcc`,
OOM tail `+0x3780`). -/
def CloneChainsStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
    (hcc : ChainClone3OkExt img.base A ext) →
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
      s.pc = closureEntry img ext + 0x19b0#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x1a5c#64) s
        (genP3J1 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J2 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

/-- Segment 3 (`+0x1a5c → +0x1b20`, `genP3J2 → genP3J3`):
Reloads `x27 = ctxPtr` from `[sp + 0xc0]` and clones `pending_pre_key` (`optTailVecAt A 48`) and
`pending_kyber_pre_key` (`optTailVecAt A 32`), covering `None`, `Some` empty `Vec`, and `Some`
allocated `Vec` (OOM tails `+0x378c`, `+0x375c`). -/
def ClonePendingStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
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
      s.pc = closureEntry img ext + 0x1a5c#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x1b20#64) s
        (genP3J2 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J3 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

/-- Segment 4 (`+0x1b20 → +0x1bac`, `genP3J3 → genP3J4`):
Spills `regIds` (`[sp + 0x30..0x38)`), `kybCap'` (`[sp + 0x38]`), and `receiverChains.length`
(`[sp + 0x40]`), and clones `alice_base_key` and `pq_ratchet_state`
(OOM tails `+0x3768`, `+0x375c`). -/
def CloneKeysTailStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
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
      s.pc = closureEntry img ext + 0x1b20#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x1bac#64) s
        (genP3J3 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J4 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

/-- Segment 5 (`+0x1bac → +0x1cd4 / +0x1e04`, `genP3J4 → genP3Post`):
Packs all cloned fields into `sessionStateAt A (sp + 0xa90#64) G₁ st` (`CloneRel recG G₁`), folds
`stackAt sp rootStack`, evaluates the effective session-version comparison `st.version = msgVer`,
and either sets up `x0..x6` at `+0x1cd4` (`st.version = msgVer`) or jumps to `+0x1e04`
(`st.version ≠ msgVer`). -/
def ClonePackStmt : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContracts img.base A ext) →
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
      s.pc = closureEntry img ext + 0x1bac#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (cloneExitPC img ext st msgVer) s
        (genP3J4 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3Post A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

/-- Composite General Clone (`+0x1778 → +0x1cd4 / +0x1e04`, `genP3Pre → genP3Post`):
End-to-end general `SessionState` clone and version dispatch inside `{closure#0}`. -/
def CloneGenStmt : Prop :=
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
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

/-! ## `*Stmt4K` Variants (Parameterized over `AllocContractsMem4K`) -/

def CloneKeysFrontStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
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
        (closureEntry img ext + 0x19b0#64) s
        (genP3Pre A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J1 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

def CloneChainsStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
    (hcc : ChainClone3OkExt img.base A ext) →
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
      s.pc = closureEntry img ext + 0x19b0#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x1a5c#64) s
        (genP3J1 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J2 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

def ClonePendingStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
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
      s.pc = closureEntry img ext + 0x1a5c#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x1b20#64) s
        (genP3J2 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J3 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

def CloneKeysTailStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
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
      s.pc = closureEntry img ext + 0x1b20#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (closureEntry img ext + 0x1bac#64) s
        (genP3J3 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3J4 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

def ClonePackStmt4K : Prop :=
  ∀ {A : RustAlloc} (img : Obj.Image) (ext : String → Option (State → State)),
    (hA : AllocContractsMem4K img.base A ext) →
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
      s.pc = closureEntry img ext + 0x1bac#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (tripleRatchetProgAtExt img.base ext)
        (cloneExitPC img ext st msgVer) s
        (genP3J4 A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3Post A img sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          img.FrozenLoaded s1 ∧
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

def CloneGenStmt4K : Prop :=
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
          s1.symtab = img.symtab)
        (P3P4.PanicOomProp s0)

theorem CloneGenStmt4K.toCloneGenStmt (h : CloneGenStmt4K) : CloneGenStmt :=
  fun img ext hA => h img ext (AllocContractsMem4K.of_AllocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
