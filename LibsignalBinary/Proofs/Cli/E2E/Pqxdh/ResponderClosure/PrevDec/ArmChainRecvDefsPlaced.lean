/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Tag 7 (`receiver_chains`) Decode-Arm Segment B Interface

Defines `overDecRecvPostMergeHeapPlaced` and the `[LibsignalPlacement]` Segment B contract
`OverDecRecvSegBPlacedStmt` (`+0x2310 → +0x2160`) on `lsProg_518 ext`.
-/

@[expose] public section

set_option autoImplicit false

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
open CryptoVerification.CliHandshake.RespClosurePlaced

/-- Placed post-`merge<Chain>` heap assertion at `+0x2310` in the tag-7 arm. -/
def overDecRecvPostMergeHeapPlaced (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ) (c : ChainG) :
    SepProp :=
  overPrevElemRest g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    CryptoVerification.LibsignalTripleRatchet.Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr
      g.enc rest ∗
    prostSSGQAt CryptoVerification.E2E.Record.A0 (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    prostChainGAt CryptoVerification.E2E.Record.A0 (g.q + 0xbf0#64) c ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    stackAt g.q overDecStackX ∗ CryptoVerification.E2E.Record.A0.pool

/-- Placed Segment B contract (`(blkPl_518).base + 0x2310 → +0x2160`) for the tag-7
(`receiver_chains`) decode arm on `lsProg_518 ext`. -/
def OverDecRecvSegBPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8)),
    (GenFieldQ.base (.recv c)).Ok →
    (GenFieldQ.base (.recv c)).Fresh v →
    ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc →
    g.enc.length < 2 ^ 62 →
    OverDecRegsPlaced ext s0 g 0x2310#64 s →
    s.readReg64 .x0 = 0#64 →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeapPlaced g rest v c)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply (.base (.recv c)))))
      (PanicOomProp s0)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
