/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterface
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs -- shake: keep

/-!
# Tag 7 (`receiver_chains`) Decode-Arm Segment B Interface

Defines the field predicate `OverDecRecvField`, post-merge heap assertion
`overDecRecvPostMergeHeapExt`, and Segment B contract `OverDecRecvSegBStmtExt` (`+0x2310 → +0x2160`)
shared between `PrevDec/ArmChainRecv.lean` and `PrevDec/ArmChainRecvPush.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ)

/-- Predicate selecting tag 7 (`receiver_chains`) protobuf fields. -/
def OverDecRecvField : GenFieldQ → Prop
  | .base (.recv _) => True
  | _ => False

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG prostChainGAt GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  chainMerge3SpecAtWExt
  Chain3OkAtWExt
)

/-- Heap assertion at `+0x2310` immediately after `merge<Chain> [local#5]` returns in the tag-7 arm,
splitting `memRegion (g.q + 0xbf0) 128` into `prostChainGAt A (g.q + 0xbf0) c` (104 B) and
`memRegion (g.q + 0xc58) 24`. -/
def overDecRecvPostMergeHeapExt (A : RustAlloc) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) (c : ChainG) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr
      g.enc rest ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    prostChainGAt A (g.q + 0xbf0#64) c ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    stackAt g.q overDecStackX ∗ A.pool

abbrev overDecRecvPostMergeHeap (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ) (c : ChainG) :
    SepProp :=
  overDecRecvPostMergeHeapExt CryptoVerification.E2E.Record.A0 g rest v c

/-- Segment B of the tag-7 (`receiver_chains`) arm (`+0x2310 → +0x2160`): copies the 104-byte
`Chain` from `q + 0xbf0` to `q + 0xa90`, grows `receiver_chains` if `len = cap`, pushes the element
at `ptr' + len * 104`, and increments `len` at `q + 0x988`. -/
def OverDecRecvSegBStmtExt (A : RustAlloc) : Prop :=
  ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    Proofs.libsignal.Stage1X.AllocContractsX img A ext →
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8)),
    (GenFieldQ.base (.recv c)).Ok →
    (GenFieldQ.base (.recv c)).Fresh v →
    ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc →
    g.enc.length < 2 ^ 62 →
    OverDecRegs img ext s0 g 0x2310#64 s →
    s.readReg64 .x0 = 0#64 →
    SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr decryptPrekeyClosureName + 0x2160#64) s
      (overDecRecvPostMergeHeapExt A g rest v c)
      (fun sf P_f => OverDecRegs img ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply (.base (.recv c)))))
      (PanicOomProp s0)

abbrev OverDecRecvSegBStmt : Prop :=
  OverDecRecvSegBStmtExt CryptoVerification.E2E.Record.A0

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
