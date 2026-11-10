/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.EquationalTheory.Literal
public import Symbolic.Specifications.Model.EquationalTheory.Representable
import DY.Meta.CombineMacro

/-!
# SPQR V1 Post-Quantum Ratchet Equational Theory

DyLean term algebra, send/receive operations, and attacker deduction rules for the SPQR V1 ratchet.
On fresh initial states (`InitState`), keys come from the epoch-0 chain (`ChainKey`) so honest
first-message send and receive agree definitionally; subsequent transitions use opaque constructors
(`SendState`, `SendKey`, `SendMsg`, `RecvState`, `RecvKey`).
-/

namespace DY.Spqr

@[expose] public section Directions

/-- Session direction (`A_2_B = 0` for initiator Alice, `B_2_A = 1` for responder Bob). -/
inductive Direction where
  | a2b
  | b2a

def Direction.toByte: Direction → UInt8
  | .a2b => 0
  | .b2a => 1

def Direction.flip: Direction → Direction
  | .a2b => .b2a
  | .b2a => .a2b

end Directions

@[expose] public section Literals

variable [BytesFunctor] [BytesFunctor.Has Literal.SubF]

open Literal

/-- Single-byte literal encoding the SPQR direction parameter. -/
def encodeSpqrDirectionParams (dir: Direction): Bytes := literalToBytes ⟨#[dir.toByte]⟩

/-- Decodes a direction from an `encodeSpqrDirectionParams` literal, returning `none` otherwise. -/
def spqrParamsDir? (params: Bytes): Option Direction :=
  match bytesToLiteral params with
  | some b =>
    if b.data = #[0] then some .a2b
    else if b.data = #[1] then some .b2a
    else none
  | none => none

/-- 4-byte little-endian literal encoding the `u32` message index `i`. -/
def encodeSpqrIndexTerm (i: UInt32): Bytes :=
  literalToBytes ⟨#[i.toUInt8, (i >>> 8).toUInt8, (i >>> 16).toUInt8, (i >>> 24).toUInt8]⟩

/-- 32-byte all-zero default HKDF salt returned at message index `0` on a fresh state. -/
def zeroKey: Bytes := literalToBytes ⟨Array.replicate 32 0⟩

/-- Whether `msg` is the empty literal (SPQR version 0, rejected by `spqrRecv`). -/
def spqrEmptyMsg (msg: Bytes): Bool :=
  match bytesToLiteral msg with
  | some b => b.size == 0
  | none => false

end Literals

namespace InitState
public structure SubF (Bytes: Type) where
  authKey: Bytes
  params: Bytes
public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.authKey SubF.params
public instance: SubBytesFunctor SubF := .binary SubF.authKey SubF.params SubF.mk
public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun ⟨a, b⟩ rec => rec a + rec b
end InitState

namespace ChainKey
public structure SubF (Bytes: Type) where
  authKey: Bytes
  params: Bytes
  idx: Bytes
public instance: ALaCarte.FunctorSizeOf SubF := .ternary SubF.authKey SubF.params SubF.idx
public instance: SubBytesFunctor SubF := .ternary SubF.authKey SubF.params SubF.idx SubF.mk
public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun _ _ => 32
end ChainKey

namespace SendState
public structure SubF (Bytes: Type) where
  st: Bytes
  coins: Bytes
public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.st SubF.coins
public instance: SubBytesFunctor SubF := .binary SubF.st SubF.coins SubF.mk
public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun ⟨a, b⟩ rec => rec a + rec b
end SendState

namespace SendKey
public structure SubF (Bytes: Type) where
  st: Bytes
  coins: Bytes
public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.st SubF.coins
public instance: SubBytesFunctor SubF := .binary SubF.st SubF.coins SubF.mk
public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun _ _ => 32
end SendKey

namespace SendMsg
public structure SubF (Bytes: Type) where
  st: Bytes
  coins: Bytes
public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.st SubF.coins
public instance: SubBytesFunctor SubF := .binary SubF.st SubF.coins SubF.mk
public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun ⟨a, b⟩ rec => rec a + rec b
end SendMsg

namespace RecvState
public structure SubF (Bytes: Type) where
  st: Bytes
  msg: Bytes
public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.st SubF.msg
public instance: SubBytesFunctor SubF := .binary SubF.st SubF.msg SubF.mk
public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun ⟨a, b⟩ rec => rec a + rec b
end RecvState

namespace RecvKey
public structure SubF (Bytes: Type) where
  st: Bytes
  msg: Bytes
public instance: ALaCarte.FunctorSizeOf SubF := .binary SubF.st SubF.msg
public instance: SubBytesFunctor SubF := .binary SubF.st SubF.msg SubF.mk
public def SubF.length [BytesFunctor]: Bytes.PartialLength SubF := fun _ _ => 32
end RecvKey

#combine into BytesFunctor, BytesLength from
  InitState,
  SendState,
  SendKey,
  SendMsg,
  RecvState,
  RecvKey,
  ChainKey,

@[expose] public section Constructors

variable [BytesFunctor] [BytesFunctor.Has SubF]

abbrev InitState.SubF.pack (x: InitState.SubF Bytes) := BytesView.pack x
abbrev ChainKey.SubF.pack (x: ChainKey.SubF Bytes) := BytesView.pack x
abbrev SendState.SubF.pack (x: SendState.SubF Bytes) := BytesView.pack x
abbrev SendKey.SubF.pack (x: SendKey.SubF Bytes) := BytesView.pack x
abbrev SendMsg.SubF.pack (x: SendMsg.SubF Bytes) := BytesView.pack x
abbrev RecvState.SubF.pack (x: RecvState.SubF Bytes) := BytesView.pack x
abbrev RecvKey.SubF.pack (x: RecvKey.SubF Bytes) := BytesView.pack x

/-- Initial SPQR state `InitState{authKey, params}`. -/
def spqrInit (authKey params: Bytes): Bytes :=
  ({authKey, params}: InitState.SubF Bytes).pack

/-- Epoch-0 chain key at `idx` under `authKey` and `params`. -/
def spqrChainKey (authKey params idx: Bytes): Bytes :=
  ({authKey, params, idx}: ChainKey.SubF Bytes).pack

end Constructors

@[expose] public section Functions

variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesFunctor.Has Literal.SubF]

/-- SPQR send step returning `(state', key, msg)`. On `InitState{authKey, params}` the key is
`spqrChainKey authKey params (encodeSpqrIndexTerm 1)`; otherwise it is `SendKey{st, coins}`. -/
def spqrSend (st coins: Bytes): Bytes × Bytes × Bytes :=
  let key := match st.view? InitState.SubF with
    | some ⟨authKey, params⟩ => spqrChainKey authKey params (encodeSpqrIndexTerm 1)
    | none => ({st, coins}: SendKey.SubF Bytes).pack
  (({st, coins}: SendState.SubF Bytes).pack, key, ({st, coins}: SendMsg.SubF Bytes).pack)

/-- SPQR receive step at message index `idx` returning `some (state', key)`, or `none` on an empty
message or malformed `InitState` parameters. -/
def spqrRecv (st msg: Bytes) (idx: UInt32): Option (Bytes × Bytes) :=
  if spqrEmptyMsg msg then none
  else
    let st' := ({st, msg}: RecvState.SubF Bytes).pack
    match st.view? InitState.SubF with
    | some ⟨authKey, params⟩ =>
      match spqrParamsDir? params with
      | some dir =>
        some (st', if idx = 0 then zeroKey
          else spqrChainKey authKey (encodeSpqrDirectionParams dir.flip) (encodeSpqrIndexTerm idx))
      | none => none
    | none => some (st', ({st, msg}: RecvKey.SubF Bytes).pack)

end Functions

section AttackerKnowledgeBuild

variable [BytesFunctor] [BytesFunctor.Has SubF]

@[expose] public
def spqrInit.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ authKey params, out = spqrInit authKey params ∧ p authKey ∧ p params

@[expose] public
def spqrChainKey.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ authKey params idx, out = spqrChainKey authKey params idx ∧ p authKey ∧ p params ∧ p idx

/-- Projects arguments from a known SPQR state (`InitState`, `SendState`, or `RecvState`), modeling
unencrypted `pq_ratchet_state` storage. -/
@[expose] public
def spqrStateArg.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out :=
    (∃ x: InitState.SubF Bytes, p x.pack ∧ (out = x.authKey ∨ out = x.params)) ∨
    (∃ x: SendState.SubF Bytes, p x.pack ∧ (out = x.st ∨ out = x.coins)) ∨
    (∃ x: RecvState.SubF Bytes, p x.pack ∧ (out = x.st ∨ out = x.msg))

end AttackerKnowledgeBuild

section AttackerKnowledgeRun

variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesFunctor.Has Literal.SubF]

@[expose] public
def spqrSendState.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ st coins, out = (spqrSend st coins).1 ∧ p st ∧ p coins

@[expose] public
def spqrSendKey.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ st coins, out = (spqrSend st coins).2.1 ∧ p st ∧ p coins

@[expose] public
def spqrSendMsg.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ st coins, out = (spqrSend st coins).2.2 ∧ p st ∧ p coins

@[expose] public
def spqrRecvState.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ st msg idx r, spqrRecv st msg idx = some r ∧ out = r.1 ∧ p st ∧ p msg

@[expose] public
def spqrRecvKey.attackerKnowledge: SubAttackerKnowledge SubF where
  pred p out := ∃ st msg idx r, spqrRecv st msg idx = some r ∧ out = r.2 ∧ p st ∧ p msg

end AttackerKnowledgeRun

#combine [BytesFunctor.Has SubF] [BytesFunctor.Has Literal.SubF] into attackerKnowledge' from
  spqrInit,
  spqrChainKey,
  spqrSendState,
  spqrSendKey,
  spqrSendMsg,
  spqrRecvState,
  spqrRecvKey,
  spqrStateArg,

end DY.Spqr
