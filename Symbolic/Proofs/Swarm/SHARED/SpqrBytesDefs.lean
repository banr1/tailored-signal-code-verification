/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.SHARED.HookAuthPure

/-!
# Byte-Level SPQR V1 Operations for Composed Semantics

Defines byte-level SPQR V1 initialization, send, receive, and epoch-0 chain-key operations
(`spqrInitB`, `spqrSendB`, `spqrRecvB`, `spqrChainKeyB`), together with their projections and
specializations to an `ExternInterpretation`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.SHARED.SpqrBytes

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (sha256CompressFunction)
open Symbolic.Swarm.SHARED.HookAuth

/-- Run the SPQR V1 byte-model `send`, returning `some (st', keyBytes, msg)` (with `keyBytes = []`
when `salt = none` and `v.toList` when `salt = some v`) or `none` on error. -/
def spqrSendB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Option (Bytes × Bytes × Bytes) :=
  match (spqrV1WithMac F K mac).send st coins with
  | some (st', salt?, msg) =>
      let keyBytes := match salt? with
        | some v => v.toList
        | none => []
      some (st', keyBytes, msg)
  | none => none

def spqrSendStateB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Bytes :=
  match spqrSendB F K mac st coins with
  | some (st', _, _) => st'
  | none => []

def spqrSendKeyB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Bytes :=
  match spqrSendB F K mac st coins with
  | some (_, key, _) => key
  | none => []

def spqrSendMsgB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Bytes :=
  match spqrSendB F K mac st coins with
  | some (_, _, msg) => msg
  | none => []

/-- Run the SPQR V1 byte-model `recv`, returning `some (st', key?)` on `.ok (st', key?)` or `none`
on error. -/
def spqrRecvB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st msg : Bytes) : Option (Bytes × Option Bytes) :=
  match (spqrV1RecvWithMac F K mac).recv st msg with
  | .ok (st', key?) => some (st', key?)
  | .error _ => none

def spqrRecvStateB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st msg : Bytes) : Bytes :=
  match spqrRecvB F K mac st msg with
  | some (st', _) => st'
  | none => []

def spqrRecvKeyB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st msg : Bytes) : Bytes :=
  match spqrRecvB F K mac st msg with
  | some (_, some k) => k
  | _ => []

/-- Decode the 1-byte direction parameter (`[0#8]` for `.a2b`, `[1#8]` for `.b2a`). -/
def spqrDirOfParams? (p : Bytes) : Option Direction :=
  if p = [0#8] then some .a2b
  else if p = [1#8] then some .b2a
  else none

/-- Serialized initial SPQR V1 state (`initialState` with `version = .v1`, `minVersion = .v1`, and
`DEFAULT_CHAIN_PARAMS`) for authentication key `k` and 1-byte direction parameter `p`. -/
def spqrInitB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (k p : Bytes) : Bytes :=
  match spqrDirOfParams? p with
  | some dir =>
      match initialState (spqrDepsWithMac F K mac)
        { direction := dir
          version := .v1
          minVersion := .v1
          authKey := k
          chainParams := DEFAULT_CHAIN_PARAMS } with
      | .ok st => st
      | .error _ => []
  | none => []

/-- Encode `idx : BitVec 32` as 4 little-endian bytes. -/
def spqrLeBytes4 (idx : BitVec 32) : Bytes :=
  [BitVec.ofNat 8 idx.toNat,
   BitVec.ofNat 8 (idx.toNat >>> 8),
   BitVec.ofNat 8 (idx.toNat >>> 16),
   BitVec.ofNat 8 (idx.toNat >>> 24)]

/-- Decode 4 little-endian bytes to `BitVec 32`. -/
def spqrIdxOfBytes? (idxBytes : Bytes) : Option (BitVec 32) :=
  match idxBytes with
  | [b0, b1, b2, b3] =>
      some (BitVec.ofNat 32
        (b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)))
  | _ => none

/-- Epoch-0 chain key at 4-byte little-endian index `idxBytes` on `dir.switch` for authentication
key `k` and 1-byte direction parameter `p`. -/
def spqrChainKeyB (F : ShaCompress) (k p idxBytes : Bytes) : Bytes :=
  match spqrDirOfParams? p, spqrIdxOfBytes? idxBytes with
  | some dir, some idx =>
      match Chain.new (spqrHkdfWith F) k dir.switch DEFAULT_CHAIN_PARAMS.intoPb with
      | .ok chain0 =>
          match chain0.recvKey (spqrHkdfWith F) 0#64 idx with
          | .ok (_, key) => key
          | .error _ => []
      | .error _ => []
  | _, _ => []

def spqrInitOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrInitB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrSendStateOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrSendStateB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrSendKeyOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrSendKeyB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrSendMsgOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrSendMsgB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrRecvStateOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrRecvStateB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrRecvKeyOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrRecvKeyB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrChainKeyOf (i : ExternInterpretation) : Bytes → Bytes → Bytes → Bytes :=
  spqrChainKeyB (sha256CompressFunction i)

end Symbolic.Swarm.SHARED.SpqrBytes
