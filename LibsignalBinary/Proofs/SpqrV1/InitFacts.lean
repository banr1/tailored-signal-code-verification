/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec

/-!
# Nonemptiness of the Initial SPQR V1 Session State

`spqrV1InitialStateFor` returns `[]` only when `initialState` fails. For the concrete bundle
`spqrDeps F K`, `initialState` always succeeds and encodes `versionNegotiation = some _` under
protobuf wire key `[0x0a]`, so `spqrV1Init F K dir k` is always a nonempty V1 state.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.LibsignalSession (SpqrDirection ShaCompress)

private theorem encodeKey_one_lengthDelimited :
    Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := rfl

private theorem encodeState_versionNegotiation_some_ne_nil
    (F : ShaCompress) (K : MlKem)
    (inner : Option V1State) (vn : VersionNegotiationPB) (chain : Option ChainPB) :
    (spqrDeps F K).encodeState
      { inner := inner, chain := chain, versionNegotiation := some vn } ≠ [] := by
  intro h
  unfold spqrDeps Proto.encodeState PqRatchetState.encode PqRatchetState.encodeRaw
    pbToPqRatchetState Proto.encodeOptMessage Proto.encodeMessage at h
  dsimp only at h
  rw [encodeKey_one_lengthDelimited] at h
  simp only [List.cons_append] at h
  cases h

/-- The V1 initial state of a libsignal session exists and is nonempty. -/
theorem initialState_libsignal_ok (F : ShaCompress) (K : MlKem) (dir : SpqrDirection)
    (k : BitVec 256) :
    ∃ st, initialState (spqrDeps F K) (libsignalSpqrParams false dir k) = .ok st ∧ st ≠ [] := by
  cases dir with
  | a2b =>
    let authKey := CryptoGames.HMAC.keyToBytes32 k
    have hinit : ∃ v1pb, (spqrDeps F K).initV1Inner .a2b authKey = .ok v1pb := by
      unfold spqrDeps States.init_a Chunked.SendEk.KeysUnsampled.new
        Unchunked.SendEk.KeysUnsampled.new spqrAuthApi
      exact ⟨_, rfl⟩
    rcases hinit with ⟨v1pb, hinit⟩
    unfold initialState libsignalSpqrParams Direction.ofSpqrDirection initInner SpqrApiResult.ofPanic
    dsimp only
    rw [hinit]
    exact ⟨_, rfl, encodeState_versionNegotiation_some_ne_nil F K (some v1pb) _ none⟩
  | b2a =>
    let authKey := CryptoGames.HMAC.keyToBytes32 k
    have hinit : ∃ v1pb, (spqrDeps F K).initV1Inner .b2a authKey = .ok v1pb := by
      unfold spqrDeps States.init_b Chunked.SendCt.NoHeaderReceived.new
        Unchunked.SendCt.NoHeaderReceived.new spqrAuthApi spqrPolyApi
        PolyDecoder.new PolyDecoder.newWithPolyCount
      exact ⟨_, rfl⟩
    rcases hinit with ⟨v1pb, hinit⟩
    unfold initialState libsignalSpqrParams Direction.ofSpqrDirection initInner SpqrApiResult.ofPanic
    dsimp only
    rw [hinit]
    exact ⟨_, rfl, encodeState_versionNegotiation_some_ne_nil F K (some v1pb) _ none⟩

/-- `spqrV1Init F K dir k` equals the nonempty state returned by `initialState`. -/
theorem spqrV1Init_eq (F : ShaCompress) (K : MlKem) (dir : SpqrDirection) (k : BitVec 256) :
    ∃ st, initialState (spqrDeps F K) (libsignalSpqrParams false dir k) = .ok st ∧
      spqrV1Init F K dir k = st ∧ st ≠ [] := by
  rcases initialState_libsignal_ok F K dir k with ⟨st, hok, hne⟩
  refine ⟨st, hok, ?_, hne⟩
  unfold spqrV1Init spqrV1InitialStateFor
  rw [hok]

end CryptoVerification.LibsignalSpqrV1
