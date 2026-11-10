/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs
public import Symbolic.Specifications.Concrete.MachineEvents
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.Prims
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.State
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.Roundtrip -- shake: keep

/-!
# Pure SPQR V1 Initial-State Decode

Proves the protobuf merge-loop roundtrip (`decodeState_spqrInitB_b2a_eq`) for Bob's initial
`spqrInitB` state in direction `b2a`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots

cref_open
open CryptoGames
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
open DY.Libsignal (HwBytes)
open Symbolic.Swarm.CREF
open Symbolic.Swarm.SHARED.SpqrBytes (spqrInitB)
open Symbolic.Swarm.SHARED.HookAuth (HmacFn)

/-! ## Varint and Protobuf Field Length Bounds -/

private theorem encodeVarintAux_length_le_rpns28a (k : Nat) (w : BitVec 64) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux k w).length ≤ k + 1 := by
  induction k generalizing w with
  | zero =>
    unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux
    exact Nat.le_refl 1
  | succ k ih =>
    unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux
    split
    · exact Nat.succ_le_succ (Nat.zero_le (k + 1))
    · exact Nat.succ_le_succ (ih (w >>> 7))

private theorem encodeVarint_length_le_rpns28a (w : BitVec 64) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint w).length ≤ 11 :=
  encodeVarintAux_length_le_rpns28a 10 w

private theorem encodeBytesField_length_le (tag : BitVec 32) (v : HwBytes) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField tag v).length ≤ 22 + v.length := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond
    CryptoVerification.LibsignalSpqrV1.Proto.encodeKey
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeVarint_length_le_rpns28a
      (((tag <<< 3) ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited.toU32).zeroExtend 64)
    have h2 := encodeVarint_length_le_rpns28a (BitVec.ofNat 64 v.length)
    omega

private theorem encodeOptMessage_length_le {S : Type} (encodeRaw : S → HwBytes)
    (tag : BitVec 32) (s : S) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage encodeRaw tag (some s)).length ≤
      22 + (encodeRaw s).length := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
    CryptoVerification.LibsignalSpqrV1.Proto.encodeKey
  simp only [List.length_append]
  have h1 := encodeVarint_length_le_rpns28a
    (((tag <<< 3) ||| CryptoVerification.LibsignalSpqrV1.Proto.WireType.lengthDelimited.toU32).zeroExtend 64)
  have h2 := encodeVarint_length_le_rpns28a (BitVec.ofNat 64 (encodeRaw s).length)
  omega

/-! ## Protobuf Roundtrip for `spqrInitB` -/

private theorem protoAuthenticator_mergeFieldsLoop_encodeRaw
    (a : CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator) (d : Nat)
    (hrk : a.rootKey.length < 2 ^ 64) (hmk : a.macKey.length < 2 ^ 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.mergeField
      (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a).length
      default (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a) d = .ok a := by
  unfold CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw
  rw [← List.append_nil (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 2#32 a.macKey)]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeBytesField
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_protoAuthenticator_mergeField
        (fun m v => { m with rootKey := v }) default 1#32 a.rootKey _ d
        (by decide) (by decide) hrk (by intro _; rfl) (by intro _; rfl)]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeBytesField
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_protoAuthenticator_mergeField
        (fun m v => { m with macKey := v }) _ 2#32 a.macKey [] d
        (by decide) (by decide) hmk (by intro _; rfl) (by intro _; rfl)]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_nil]

private theorem unchunked_noHeaderReceived_mergeFieldsLoop_encodeRaw
    (a : CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator) (d : Nat)
    (hrk : a.rootKey.length < 2 ^ 64) (hmk : a.macKey.length < 2 ^ 64)
    (ha_len : (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a).length < 2 ^ 64) :
    let u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived :=
      { epoch := 1#64, auth := some a }
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField
      (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw u).length
      default (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw u) (d + 1) = .ok u := by
  intro u
  unfold CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
  rw [← List.append_nil (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 u.auth)]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeUint64Field
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_unchunked_noHeaderReceived_mergeField
        (fun m v => { m with epoch := v }) default 1#32 u.epoch _ (d + 1)
        (by decide) (by decide) (by intro _; rfl) (by intro _; rfl)]
  dsimp only [u]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeOptMessage
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_unchunked_noHeaderReceived_mergeField
        CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.mergeField
        CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw
        (fun m => m.auth) (fun m v => { m with auth := v })
        _ (some a) 2#32 [] d
        (by decide) (by decide) (by intro sub hsub; injection hsub with hsub; subst hsub; exact ha_len)
        (by intro bs
            simp only [CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField,
              CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage]
            cases CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
              CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.mergeField .lengthDelimited
              ((default : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived).auth.getD default)
              bs (d + 1) <;> rfl)]
  dsimp only
  have hdef : ((default : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived).auth.getD default) =
      (default : CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator) := rfl
  rw [hdef, protoAuthenticator_mergeFieldsLoop_encodeRaw a d hrk hmk]
  dsimp only [Bind.bind, Except.bind]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_nil]

def b0HdrDecoderPb : CryptoVerification.LibsignalSpqrV1.PolynomialDecoder :=
  { ptsNeeded := 48#32, polys := 16#32, pts := List.replicate 16 [], isComplete := false }

private theorem b0HdrDecoderPb_mergeFieldsLoop (d : Nat) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.mergeField
      (CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.encodeRaw b0HdrDecoderPb).length
      default (CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.encodeRaw b0HdrDecoderPb) (d + 1) =
      .ok b0HdrDecoderPb := rfl

private theorem chunked_noHeaderReceived_mergeFieldsLoop_encodeRaw
    (a : CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator) (d : Nat)
    (hrk : a.rootKey.length < 2 ^ 64) (hmk : a.macKey.length < 2 ^ 64)
    (ha_len : (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a).length < 2 ^ 64)
    (hu_len : (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
      { epoch := 1#64, auth := some a }).length < 2 ^ 64) :
    let c : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived :=
      { uc := some { epoch := 1#64, auth := some a }, receivingHdr := some b0HdrDecoderPb }
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField
      (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw c).length
      default (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw c) (d + 2) = .ok c := by
  intro c
  unfold CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw
  rw [← List.append_nil (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.encodeRaw 2#32 c.receivingHdr)]
  dsimp only [c]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeOptMessage
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_chunked_noHeaderReceived_mergeField
        CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField
        CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
        (fun m => m.uc) (fun m v => { m with uc := v })
        default (some { epoch := 1#64, auth := some a }) 1#32 _ (d + 1)
        (by decide) (by decide) (by intro sub hsub; injection hsub with hsub; subst hsub; exact hu_len)
        (by intro bs
            simp only [CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField,
              CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage]
            cases CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
              CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.mergeField .lengthDelimited
              ((default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived).uc.getD default)
              bs (d + 2) <;> rfl)]
  dsimp only
  have hdef_uc : ((default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived).uc.getD default) =
      (default : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived) := rfl
  rw [hdef_uc, unchunked_noHeaderReceived_mergeFieldsLoop_encodeRaw a d hrk hmk ha_len]
  dsimp only [Bind.bind, Except.bind]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeOptMessage
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_chunked_noHeaderReceived_mergeField
        CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.mergeField
        CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.encodeRaw
        (fun m => m.receivingHdr) (fun m v => { m with receivingHdr := v })
        _ (some b0HdrDecoderPb) 2#32 [] (d + 1)
        (by decide) (by decide) (by intro sub hsub; injection hsub with hsub; subst hsub; decide)
        (by intro bs
            simp only [CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField,
              CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage]
            cases CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
              CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.mergeField .lengthDelimited
              ((default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived).receivingHdr.getD default)
              bs (d + 2) <;> rfl)]
  dsimp only
  have hdef_hdr : ((default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived).receivingHdr.getD default) =
      (default : CryptoVerification.LibsignalSpqrV1.PolynomialDecoder) := rfl
  rw [hdef_hdr, b0HdrDecoderPb_mergeFieldsLoop d]
  dsimp only [Bind.bind, Except.bind]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_nil]

private theorem v1State_noHeaderReceived_mergeFieldsLoop_encodeRaw
    (a : CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator) (d : Nat)
    (hrk : a.rootKey.length < 2 ^ 64) (hmk : a.macKey.length < 2 ^ 64)
    (ha_len : (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a).length < 2 ^ 64)
    (hu_len : (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
      { epoch := 1#64, auth := some a }).length < 2 ^ 64)
    (hc_len : (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw
      { uc := some { epoch := 1#64, auth := some a }, receivingHdr := some b0HdrDecoderPb }).length < 2 ^ 64) :
    let c : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived :=
      { uc := some { epoch := 1#64, auth := some a }, receivingHdr := some b0HdrDecoderPb }
    let v : CryptoVerification.LibsignalSpqrV1.V1State :=
      { innerState := some (.noHeaderReceived c) }
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop
      CryptoVerification.LibsignalSpqrV1.V1State.mergeField
      (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw v).length
      default (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw v) (d + 3) = .ok v := by
  intro c v
  unfold CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw
  dsimp only [v, CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode]
  rw [← List.append_nil (CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
        CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw 6#32 c)]
  have hd3 : d + 3 = (d + 2) + 1 := rfl
  rw [hd3, Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeMessage
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_v1State_mergeField
        CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField
        CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw
        (fun m x => { m with innerState := some (.noHeaderReceived x) })
        default
        (match (default : CryptoVerification.LibsignalSpqrV1.V1State).innerState with
         | some (.noHeaderReceived v0) => v0
         | _ => default)
        c 6#32 [] (d + 2)
        (by decide) (by decide) hc_len
        (by intro bs
            dsimp only [CryptoVerification.LibsignalSpqrV1.V1State.mergeField,
              CryptoVerification.LibsignalSpqrV1.V1State.InnerState.merge]
            change (do
              let __x ← CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
                CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField
                .lengthDelimited
                (match (default : CryptoVerification.LibsignalSpqrV1.V1State).innerState with
                 | some (.noHeaderReceived v0) => v0
                 | _ => default)
                bs (d + 2 + 1)
              Except.ok (some (CryptoVerification.LibsignalSpqrV1.V1State.InnerState.noHeaderReceived __x.1), __x.2)) >>=
              (fun __x => Except.ok (({ innerState := __x.1 } : CryptoVerification.LibsignalSpqrV1.V1State), __x.2)) = _
            cases CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
              CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.mergeField
              .lengthDelimited
              (match (default : CryptoVerification.LibsignalSpqrV1.V1State).innerState with
               | some (.noHeaderReceived v0) => v0
               | _ => default)
              bs (d + 2 + 1) <;> rfl)]
  have hdef : (match (default : CryptoVerification.LibsignalSpqrV1.V1State).innerState with
      | some (.noHeaderReceived v0) => v0
      | _ => default) = (default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived) := rfl
  rw [hdef, chunked_noHeaderReceived_mergeFieldsLoop_encodeRaw a d hrk hmk ha_len hu_len]
  dsimp only [Bind.bind, Except.bind]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_nil]

def b0VnPb (k : HwBytes) : CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB :=
  { authKey := k
    direction := CryptoVerification.LibsignalSpqrV1.Direction.b2a.toI32
    minVersion := CryptoVerification.LibsignalSpqrV1.Version.v1.toI32
    chainParams := some CryptoVerification.LibsignalSpqrV1.DEFAULT_CHAIN_PARAMS.intoPb }

def b0V1StatePb (F : ShaCompress) (k : HwBytes) : CryptoVerification.LibsignalSpqrV1.V1State :=
  let a := (CryptoVerification.LibsignalSpqrV1.Authenticator.new F k 1#64).intoPb
  { innerState := some (.noHeaderReceived
      { uc := some { epoch := 1#64, auth := some a }, receivingHdr := some b0HdrDecoderPb }) }

theorem decodeState_spqrInitB_b2a_eq
    (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem) (mac : HmacFn)
    {k : HwBytes} (hk : k.length = 32) :
    CryptoVerification.LibsignalSpqrV1.decodeState
      (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac)
      (spqrInitB F K mac k [1#8]) =
    .ok { inner := some (b0V1StatePb F k)
          versionNegotiation := some (b0VnPb k)
          chain := none } := by
  set a := (CryptoVerification.LibsignalSpqrV1.Authenticator.new F k 1#64).intoPb
  set c : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived :=
    { uc := some { epoch := 1#64, auth := some a }, receivingHdr := some b0HdrDecoderPb }
  set v : CryptoVerification.LibsignalSpqrV1.V1State := { innerState := some (.noHeaderReceived c) }
  set m : CryptoVerification.LibsignalSpqrV1.PqRatchetState :=
    { versionNegotiation := some (b0VnPb k), chain := none, inner := some (.v1 v) }
  have hinit : spqrInitB F K mac k [1#8] = CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw m := rfl
  rw [hinit]
  have hrk32 : a.rootKey.length ≤ 32 := List.length_take_le 32 _
  have hmk64 : a.macKey.length ≤ 64 := by
    dsimp only [a, CryptoVerification.LibsignalSpqrV1.Authenticator.intoPb,
      CryptoVerification.LibsignalSpqrV1.Authenticator.new,
      CryptoVerification.LibsignalSpqrV1.Authenticator.update,
      CryptoVerification.LibsignalSpqrV1.hkdfToSliceUnchecked,
      CryptoVerification.LibsignalSpqrV1.hkdfToVecUnchecked,
      CryptoGames.HKDF.hkdfExpand]
    rw [List.length_drop]
    exact Nat.le_trans (Nat.sub_le _ _) (List.length_take_le 64 _)
  have hrk : a.rootKey.length < 2 ^ 64 := Nat.lt_of_le_of_lt hrk32 (by decide)
  have hmk : a.macKey.length < 2 ^ 64 := Nat.lt_of_le_of_lt hmk64 (by decide)
  have ha_le : (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a).length ≤ 140 := by
    unfold CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw
    rw [List.length_append]
    have h1 := encodeBytesField_length_le 1#32 a.rootKey
    have h2 := encodeBytesField_length_le 2#32 a.macKey
    omega
  have ha_len : (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt ha_le (by decide)
  have hu_le : (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
      { epoch := 1#64, auth := some a }).length ≤ 164 := by
    unfold CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
    dsimp only
    rw [List.length_append]
    have h1 : (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 1#64).length = 2 := rfl
    have h2 := encodeOptMessage_length_le CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 a
    omega
  have hu_len : (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw
      { epoch := 1#64, auth := some a }).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hu_le (by decide)
  have hc_le : (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw c).length ≤ 224 := by
    unfold CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw
    dsimp only [c]
    rw [List.length_append]
    have h1 := encodeOptMessage_length_le
      CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32
      { epoch := 1#64, auth := some a }
    have h2 : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.PolynomialDecoder.encodeRaw 2#32 (some b0HdrDecoderPb)).length = 38 := rfl
    omega
  have hc_len : (CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw c).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hc_le (by decide)
  have hv_le : (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw v).length ≤ 246 := by
    unfold CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw
    dsimp only [v, CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode]
    have h1 := encodeOptMessage_length_le
      CryptoVerification.LibsignalSpqrV1.V1State.Chunked.NoHeaderReceived.encodeRaw 6#32 c
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage] at h1
    omega
  have hv_len : (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw v).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hv_le (by decide)
  have hvn_le : (CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw (b0VnPb k)).length ≤ 84 := by
    unfold CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw b0VnPb
    dsimp only
    simp only [List.length_append]
    have h1 := encodeBytesField_length_le 1#32 k
    have h2 : (CryptoVerification.LibsignalSpqrV1.Proto.encodeInt32Field 2#32
      CryptoVerification.LibsignalSpqrV1.Direction.b2a.toI32).length = 2 := rfl
    have h3 : (CryptoVerification.LibsignalSpqrV1.Proto.encodeInt32Field 3#32
      CryptoVerification.LibsignalSpqrV1.Version.v1.toI32).length = 2 := rfl
    have h4 : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.ChainParamsPB.encodeRaw 4#32
      (some CryptoVerification.LibsignalSpqrV1.DEFAULT_CHAIN_PARAMS.intoPb)).length ≤ 12 := by decide
    omega
  have hm_enc :
      CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw m =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw 1#32 (some (b0VnPb k)) ++
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
          CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw 3#32 v := by
    unfold CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw
    dsimp only [m, CryptoVerification.LibsignalSpqrV1.PqRatchetState.Inner.encode]
    have hnone : CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        CryptoVerification.LibsignalSpqrV1.ChainPB.encodeRaw 2#32 none = [] := rfl
    rw [hnone, List.append_nil]
  have hm_le : (CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw m).length ≤ 400 := by
    rw [hm_enc, List.length_append]
    have h1 := encodeOptMessage_length_le CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw 1#32 (b0VnPb k)
    have h2 := encodeOptMessage_length_le CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw 3#32 v
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage] at h2
    omega
  have hm_len : (CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw m).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hm_le (by decide)
  have hemp : (CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw m).isEmpty = false := by
    unfold CryptoVerification.LibsignalSpqrV1.PqRatchetState.encodeRaw
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
    rfl
  unfold CryptoVerification.LibsignalSpqrV1.decodeState
  rw [hemp]
  dsimp only [Bool.false_eq_true, ↓reduceIte, Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac,
    CryptoVerification.LibsignalSpqrV1.Proto.decodeState,
    CryptoVerification.LibsignalSpqrV1.PqRatchetState.decode,
    CryptoVerification.LibsignalSpqrV1.Proto.decodeTopLevelMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.mergeTopLevelMessage]
  have hrec_lim : CryptoVerification.LibsignalSpqrV1.Proto.RECURSION_LIMIT = 99 + 1 := rfl
  rw [hrec_lim, hm_enc]
  have hm_len' : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      CryptoVerification.LibsignalSpqrV1.VersionNegotiationPB.encodeRaw 1#32 (some (b0VnPb k)) ++
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
        CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw 3#32 v).length < 2 ^ 64 := by
    rwa [← hm_enc]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.pqRatchetState_step_tag1 default (some (b0VnPb k))
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
          CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw 3#32 v)
        99 rfl hm_len' (by decide)]
  rw [← List.append_nil (CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage
        CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw 3#32 v)]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_encodeMessage
        CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3.protoPrefixStep_pqRatchetState_mergeField
        CryptoVerification.LibsignalSpqrV1.V1State.mergeField
        CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw
        (fun st x => { st with inner := some (.v1 x) })
        _
        (match ({ (default : CryptoVerification.LibsignalSpqrV1.PqRatchetState) with versionNegotiation := some (b0VnPb k) }).inner with
         | some (.v1 v0) => v0
         | none => default)
        v 3#32 [] 99
        (by decide) (by decide) hv_len
        (by intro bs
            dsimp only [CryptoVerification.LibsignalSpqrV1.PqRatchetState.mergeField,
              CryptoVerification.LibsignalSpqrV1.PqRatchetState.Inner.merge]
            change (do
              let __x ← CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
                CryptoVerification.LibsignalSpqrV1.V1State.mergeField .lengthDelimited
                (match ({ (default : CryptoVerification.LibsignalSpqrV1.PqRatchetState) with versionNegotiation := some (b0VnPb k) }).inner with
                 | some (.v1 v0) => v0
                 | none => default)
                bs (99 + 1)
              Except.ok (some (CryptoVerification.LibsignalSpqrV1.PqRatchetState.Inner.v1 __x.1), __x.2)) >>=
              (fun __x => Except.ok ({ { (default : CryptoVerification.LibsignalSpqrV1.PqRatchetState) with versionNegotiation := some (b0VnPb k) } with inner := __x.1 }, __x.2)) = _
            cases CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
              CryptoVerification.LibsignalSpqrV1.V1State.mergeField .lengthDelimited
              (match ({ (default : CryptoVerification.LibsignalSpqrV1.PqRatchetState) with versionNegotiation := some (b0VnPb k) }).inner with
               | some (.v1 v0) => v0
               | none => default)
              bs (99 + 1) <;> rfl)]
  have hdef : (match ({ (default : CryptoVerification.LibsignalSpqrV1.PqRatchetState) with versionNegotiation := some (b0VnPb k) }).inner with
      | some (.v1 v0) => v0
      | none => default) = (default : CryptoVerification.LibsignalSpqrV1.V1State) := rfl
  have h99 : (99 : Nat) = 96 + 3 := rfl
  rw [hdef, h99, v1State_noHeaderReceived_mergeFieldsLoop_encodeRaw a 96 hrk hmk ha_len hu_len hc_len]
  dsimp only [Bind.bind, Except.bind]
  rw [Symbolic.Swarm.TRREF.GrowthOoo.mergeFieldsLoop_nil]
  rfl

end Symbolic.Swarm.CREF.Cli.Slots
