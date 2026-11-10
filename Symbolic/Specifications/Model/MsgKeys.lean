/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.KdfExtract
public import DY.Actions.ProtocolEvent
public import DY.Actions.PersistentLocalState

/-!
# Hybrid Message-Key Derivation and Trace Helpers

Hybrid HKDF message-key derivation (`trMsgKeys`), protocol constants, and trace-inspection helpers
shared by `PQXDH` and `TripleRatchet`.
-/

namespace DY.Libsignal.TripleRatchet

@[expose] public section MsgKeys

variable [BytesFunctor] [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesFunctor.Has Concat.SubF]
  [BytesFunctor.Has KdfExtract.SubF]

open Literal Concat KdfExtract

def lit (s: String): Bytes := literalToBytes s.toUTF8

def litByte (b: UInt8): Bytes := literalToBytes ⟨#[b]⟩

/-- HMAC-SHA256 (`HKDF-Extract` with `salt = key`, RFC 5869 §2.2). -/
def hmac (key msg: Bytes): Bytes := kdfExtract key msg

/-- First three 32-byte RFC 5869 HKDF-Expand output blocks `T(1)`, `T(2)`, `T(3)` for SHA-256. -/
def hkdfBlock1 (prk info: Bytes): Bytes := hmac prk (concat info (litByte 1))
def hkdfBlock2 (prk info: Bytes): Bytes := hmac prk (concat (hkdfBlock1 prk info) (concat info (litByte 2)))
def hkdfBlock3 (prk info: Bytes): Bytes := hmac prk (concat (hkdfBlock2 prk info) (concat info (litByte 3)))

/-- Default 32-byte all-zero HKDF salt (`optional_salt = None`, RFC 5869 §2.2). -/
def zeroSalt: Bytes := literalToBytes ⟨Array.replicate 32 0⟩

/-- Output of `MessageKeys::derive_keys`. -/
structure MessageKeys where
  cipherKey: Bytes
  macKey: Bytes
  /-- Full 32-byte third HKDF block; concretization uses its first 16 bytes as the AES-CBC IV. -/
  iv: Bytes

/-- Hybrid message-key derivation `MessageKeys::derive_keys(seed, Some(pqSalt), counter)`:
expands `"WhisperMessageKeys"` from `hmac pqSalt seed`. When `pqSalt = zeroSalt`, this matches the
unsalted `optional_salt = None` path. -/
def trMsgKeys (pqSalt seed: Bytes): MessageKeys :=
  let prk := hmac pqSalt seed
  { cipherKey := hkdfBlock1 prk (lit "WhisperMessageKeys")
    macKey := hkdfBlock2 prk (lit "WhisperMessageKeys")
    iv := hkdfBlock3 prk (lit "WhisperMessageKeys") }

/-- `CIPHERTEXT_MESSAGE_CURRENT_VERSION` (version 4). -/
def messageVersion: UInt8 := 4

/-- Decoded `SignalMessage` fields together with the MAC-authenticated `wire` term and `mac`. -/
structure SignalMsg where
  wire: Bytes
  mac: Bytes
  version: UInt8
  ratchetKey: Bytes
  counter: UInt32
  ciphertext: Bytes

/-- `consts::MAX_FORWARD_JUMPS`. -/
def maxForwardJumps: Nat := 25000

/-- `u32::MAX` (`index + 1` overflows and aborts in libsignal). -/
def u32Max: UInt32 := 0xFFFFFFFF

end MsgKeys

@[expose] public section TraceHelpers

/-- Whether some `EventT` entry on `tr` satisfies `p`. -/
def anyEventOnTrace (EventT: Type) [ExecTraceTypes]
    [ExecTraceTypes.Has (ProtocolEvent.ExecEntryT EventT)]
    (tr: ExecTrace) (p: EventT → Bool) : Bool :=
  (List.range tr.length).any fun i =>
    match tr.getEventAt EventT i with
    | some ev => p ev
    | none => false

/-- Trace guard that succeeds iff `p tr` holds, without appending to `tr`. -/
def guardTrace [ExecTraceTypes] (p: ExecTrace → Bool) : Traceful Unit :=
  Traceful.mk fun tr => (if p tr then some () else none, ⟨tr, by grind⟩)

/-- Stored `LocalState StateT` at trace index `idx`, if any. -/
abbrev getStoredLocalStateAt? (StateT: Type) [ExecTraceTypes]
    [ExecTraceTypes.Has (PersistentLocalState.State.ExecEntryT StateT)]
    (tr: ExecTrace) (idx: Nat) : Option (PersistentLocalState.LocalState StateT) :=
  ((tr.at? idx : Option (PersistentGlobalState.State.ExecEntryT
      (PersistentLocalState.LocalState StateT)))).map (·.st)

end TraceHelpers

end DY.Libsignal.TripleRatchet
