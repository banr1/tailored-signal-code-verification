/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChain
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Prost Round-Trip for `V1State.Unchunked.*`

`LoopsTo` (recursion depth 1) and `decode (encodeRaw m) = .ok m` round-trip theorems for all ten
`V1State.Unchunked.*` protobuf message types when the encoded byte length fits in 64 bits.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)

theorem loopsTo_uc_keysUnsampled (m : V1State.Unchunked.KeysUnsampled) (h : (V1State.Unchunked.KeysUnsampled.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.KeysUnsampled.mergeField 1 default (V1State.Unchunked.KeysUnsampled.encodeRaw m) m := by
  simp only [V1State.Unchunked.KeysUnsampled.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.KeysUnsampled.mergeField 1 (default : V1State.Unchunked.KeysUnsampled) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.KeysUnsampled) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.KeysUnsampled.mergeField 1 { (default : V1State.Unchunked.KeysUnsampled) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.KeysUnsampled) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  exact (h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_keysUnsampled_mergeField h1).congr_res (by cases m; rfl)

theorem decode_uc_keysUnsampled (m : V1State.Unchunked.KeysUnsampled) (h : (V1State.Unchunked.KeysUnsampled.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.KeysUnsampled.decode (V1State.Unchunked.KeysUnsampled.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_keysUnsampled m h)

theorem loopsTo_uc_headerSent (m : V1State.Unchunked.HeaderSent) (h : (V1State.Unchunked.HeaderSent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.HeaderSent.mergeField 1 default (V1State.Unchunked.HeaderSent.encodeRaw m) m := by
  simp only [V1State.Unchunked.HeaderSent.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.HeaderSent.mergeField 1 (default : V1State.Unchunked.HeaderSent) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.HeaderSent) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.HeaderSent.mergeField 1 { (default : V1State.Unchunked.HeaderSent) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.HeaderSent) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  have h2 := loopsTo_bytes V1State.Unchunked.HeaderSent.mergeField 1 { (default : V1State.Unchunked.HeaderSent) with epoch := m.epoch, auth := m.auth } 3#32 m.ek (fun x => { (default : V1State.Unchunked.HeaderSent) with epoch := m.epoch, auth := m.auth, ek := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 3#32 m.ek; omega) (fun _ _ _ => rfl)
  have h3 := loopsTo_bytes V1State.Unchunked.HeaderSent.mergeField 1 { (default : V1State.Unchunked.HeaderSent) with epoch := m.epoch, auth := m.auth, ek := m.ek } 4#32 m.dk (fun x => { (default : V1State.Unchunked.HeaderSent) with epoch := m.epoch, auth := m.auth, ek := m.ek, dk := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 4#32 m.dk; omega) (fun _ _ _ => rfl)
  exact (((h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_headerSent_mergeField h1).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_headerSent_mergeField h2).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_headerSent_mergeField h3).congr_res (by cases m; rfl)

theorem decode_uc_headerSent (m : V1State.Unchunked.HeaderSent) (h : (V1State.Unchunked.HeaderSent.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.HeaderSent.decode (V1State.Unchunked.HeaderSent.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_headerSent m h)

theorem loopsTo_uc_ekSent (m : V1State.Unchunked.EkSent) (h : (V1State.Unchunked.EkSent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.EkSent.mergeField 1 default (V1State.Unchunked.EkSent.encodeRaw m) m := by
  simp only [V1State.Unchunked.EkSent.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.EkSent.mergeField 1 (default : V1State.Unchunked.EkSent) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.EkSent) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.EkSent.mergeField 1 { (default : V1State.Unchunked.EkSent) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.EkSent) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  have h2 := loopsTo_bytes V1State.Unchunked.EkSent.mergeField 1 { (default : V1State.Unchunked.EkSent) with epoch := m.epoch, auth := m.auth } 3#32 m.dk (fun x => { (default : V1State.Unchunked.EkSent) with epoch := m.epoch, auth := m.auth, dk := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 3#32 m.dk; omega) (fun _ _ _ => rfl)
  exact ((h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekSent_mergeField h1).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekSent_mergeField h2).congr_res (by cases m; rfl)

theorem decode_uc_ekSent (m : V1State.Unchunked.EkSent) (h : (V1State.Unchunked.EkSent.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.EkSent.decode (V1State.Unchunked.EkSent.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_ekSent m h)

theorem loopsTo_uc_ekSentCt1Received (m : V1State.Unchunked.EkSentCt1Received) (h : (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.EkSentCt1Received.mergeField 1 default (V1State.Unchunked.EkSentCt1Received.encodeRaw m) m := by
  simp only [V1State.Unchunked.EkSentCt1Received.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.EkSentCt1Received.mergeField 1 (default : V1State.Unchunked.EkSentCt1Received) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.EkSentCt1Received) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.EkSentCt1Received.mergeField 1 { (default : V1State.Unchunked.EkSentCt1Received) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.EkSentCt1Received) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  have h2 := loopsTo_bytes V1State.Unchunked.EkSentCt1Received.mergeField 1 { (default : V1State.Unchunked.EkSentCt1Received) with epoch := m.epoch, auth := m.auth } 3#32 m.dk (fun x => { (default : V1State.Unchunked.EkSentCt1Received) with epoch := m.epoch, auth := m.auth, dk := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 3#32 m.dk; omega) (fun _ _ _ => rfl)
  have h3 := loopsTo_bytes V1State.Unchunked.EkSentCt1Received.mergeField 1 { (default : V1State.Unchunked.EkSentCt1Received) with epoch := m.epoch, auth := m.auth, dk := m.dk } 4#32 m.ct1 (fun x => { (default : V1State.Unchunked.EkSentCt1Received) with epoch := m.epoch, auth := m.auth, dk := m.dk, ct1 := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 4#32 m.ct1; omega) (fun _ _ _ => rfl)
  exact (((h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekSentCt1Received_mergeField h1).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekSentCt1Received_mergeField h2).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekSentCt1Received_mergeField h3).congr_res (by cases m; rfl)

theorem decode_uc_ekSentCt1Received (m : V1State.Unchunked.EkSentCt1Received) (h : (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.EkSentCt1Received.decode (V1State.Unchunked.EkSentCt1Received.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_ekSentCt1Received m h)

theorem loopsTo_uc_noHeaderReceived (m : V1State.Unchunked.NoHeaderReceived) (h : (V1State.Unchunked.NoHeaderReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.NoHeaderReceived.mergeField 1 default (V1State.Unchunked.NoHeaderReceived.encodeRaw m) m := by
  simp only [V1State.Unchunked.NoHeaderReceived.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.NoHeaderReceived.mergeField 1 (default : V1State.Unchunked.NoHeaderReceived) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.NoHeaderReceived) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.NoHeaderReceived.mergeField 1 { (default : V1State.Unchunked.NoHeaderReceived) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.NoHeaderReceived) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  exact (h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_noHeaderReceived_mergeField h1).congr_res (by cases m; rfl)

theorem decode_uc_noHeaderReceived (m : V1State.Unchunked.NoHeaderReceived) (h : (V1State.Unchunked.NoHeaderReceived.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.NoHeaderReceived.decode (V1State.Unchunked.NoHeaderReceived.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_noHeaderReceived m h)

theorem loopsTo_uc_headerReceived (m : V1State.Unchunked.HeaderReceived) (h : (V1State.Unchunked.HeaderReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.HeaderReceived.mergeField 1 default (V1State.Unchunked.HeaderReceived.encodeRaw m) m := by
  simp only [V1State.Unchunked.HeaderReceived.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.HeaderReceived.mergeField 1 (default : V1State.Unchunked.HeaderReceived) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.HeaderReceived) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.HeaderReceived.mergeField 1 { (default : V1State.Unchunked.HeaderReceived) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.HeaderReceived) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  have h2 := loopsTo_bytes V1State.Unchunked.HeaderReceived.mergeField 1 { (default : V1State.Unchunked.HeaderReceived) with epoch := m.epoch, auth := m.auth } 3#32 m.hdr (fun x => { (default : V1State.Unchunked.HeaderReceived) with epoch := m.epoch, auth := m.auth, hdr := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 3#32 m.hdr; omega) (fun _ _ _ => rfl)
  exact ((h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_headerReceived_mergeField h1).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_headerReceived_mergeField h2).congr_res (by cases m; rfl)

theorem decode_uc_headerReceived (m : V1State.Unchunked.HeaderReceived) (h : (V1State.Unchunked.HeaderReceived.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.HeaderReceived.decode (V1State.Unchunked.HeaderReceived.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_headerReceived m h)

theorem loopsTo_uc_ekReceived (m : V1State.Unchunked.EkReceived) (h : (V1State.Unchunked.EkReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.EkReceived.mergeField 1 default (V1State.Unchunked.EkReceived.encodeRaw m) m := by
  simp only [V1State.Unchunked.EkReceived.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.EkReceived.mergeField 1 (default : V1State.Unchunked.EkReceived) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.EkReceived) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.EkReceived.mergeField 1 { (default : V1State.Unchunked.EkReceived) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.EkReceived) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  have h2 := loopsTo_bytes V1State.Unchunked.EkReceived.mergeField 1 { (default : V1State.Unchunked.EkReceived) with epoch := m.epoch, auth := m.auth } 3#32 m.hdr (fun x => { (default : V1State.Unchunked.EkReceived) with epoch := m.epoch, auth := m.auth, hdr := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 3#32 m.hdr; omega) (fun _ _ _ => rfl)
  have h3 := loopsTo_bytes V1State.Unchunked.EkReceived.mergeField 1 { (default : V1State.Unchunked.EkReceived) with epoch := m.epoch, auth := m.auth, hdr := m.hdr } 4#32 m.ek (fun x => { (default : V1State.Unchunked.EkReceived) with epoch := m.epoch, auth := m.auth, hdr := m.hdr, ek := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 4#32 m.ek; omega) (fun _ _ _ => rfl)
  exact (((h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekReceived_mergeField h1).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekReceived_mergeField h2).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ekReceived_mergeField h3).congr_res (by cases m; rfl)

theorem decode_uc_ekReceived (m : V1State.Unchunked.EkReceived) (h : (V1State.Unchunked.EkReceived.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.EkReceived.decode (V1State.Unchunked.EkReceived.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_ekReceived m h)

theorem loopsTo_uc_ct1Sent (m : V1State.Unchunked.Ct1Sent) (h : (V1State.Unchunked.Ct1Sent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.Ct1Sent.mergeField 1 default (V1State.Unchunked.Ct1Sent.encodeRaw m) m := by
  simp only [V1State.Unchunked.Ct1Sent.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.Ct1Sent.mergeField 1 (default : V1State.Unchunked.Ct1Sent) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.Ct1Sent) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.Ct1Sent.mergeField 1 { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  have h2 := loopsTo_bytes V1State.Unchunked.Ct1Sent.mergeField 1 { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch, auth := m.auth } 3#32 m.hdr (fun x => { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch, auth := m.auth, hdr := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 3#32 m.hdr; omega) (fun _ _ _ => rfl)
  have h3 := loopsTo_bytes V1State.Unchunked.Ct1Sent.mergeField 1 { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch, auth := m.auth, hdr := m.hdr } 4#32 m.es (fun x => { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch, auth := m.auth, hdr := m.hdr, es := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 4#32 m.es; omega) (fun _ _ _ => rfl)
  have h4 := loopsTo_bytes V1State.Unchunked.Ct1Sent.mergeField 1 { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch, auth := m.auth, hdr := m.hdr, es := m.es } 5#32 m.ct1 (fun x => { (default : V1State.Unchunked.Ct1Sent) with epoch := m.epoch, auth := m.auth, hdr := m.hdr, es := m.es, ct1 := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 5#32 m.ct1; omega) (fun _ _ _ => rfl)
  exact ((((h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1Sent_mergeField h1).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1Sent_mergeField h2).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1Sent_mergeField h3).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1Sent_mergeField h4).congr_res (by cases m; rfl)

theorem decode_uc_ct1Sent (m : V1State.Unchunked.Ct1Sent) (h : (V1State.Unchunked.Ct1Sent.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.Ct1Sent.decode (V1State.Unchunked.Ct1Sent.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_ct1Sent m h)

theorem loopsTo_uc_ct1SentEkReceived (m : V1State.Unchunked.Ct1SentEkReceived) (h : (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.Ct1SentEkReceived.mergeField 1 default (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m) m := by
  simp only [V1State.Unchunked.Ct1SentEkReceived.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.Ct1SentEkReceived.mergeField 1 (default : V1State.Unchunked.Ct1SentEkReceived) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.Ct1SentEkReceived.mergeField 1 { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  have h2 := loopsTo_bytes V1State.Unchunked.Ct1SentEkReceived.mergeField 1 { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch, auth := m.auth } 3#32 m.es (fun x => { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch, auth := m.auth, es := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 3#32 m.es; omega) (fun _ _ _ => rfl)
  have h3 := loopsTo_bytes V1State.Unchunked.Ct1SentEkReceived.mergeField 1 { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch, auth := m.auth, es := m.es } 4#32 m.ek (fun x => { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch, auth := m.auth, es := m.es, ek := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 4#32 m.ek; omega) (fun _ _ _ => rfl)
  have h4 := loopsTo_bytes V1State.Unchunked.Ct1SentEkReceived.mergeField 1 { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch, auth := m.auth, es := m.es, ek := m.ek } 5#32 m.ct1 (fun x => { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := m.epoch, auth := m.auth, es := m.es, ek := m.ek, ct1 := x })
    (by decide) (by decide) rfl
    (by have := length_le_encodeBytesField 5#32 m.ct1; omega) (fun _ _ _ => rfl)
  exact ((((h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1SentEkReceived_mergeField h1).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1SentEkReceived_mergeField h2).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1SentEkReceived_mergeField h3).append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct1SentEkReceived_mergeField h4).congr_res (by cases m; rfl)

theorem decode_uc_ct1SentEkReceived (m : V1State.Unchunked.Ct1SentEkReceived) (h : (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.Ct1SentEkReceived.decode (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_ct1SentEkReceived m h)

theorem loopsTo_uc_ct2Sent (m : V1State.Unchunked.Ct2Sent) (h : (V1State.Unchunked.Ct2Sent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.Ct2Sent.mergeField 1 default (V1State.Unchunked.Ct2Sent.encodeRaw m) m := by
  simp only [V1State.Unchunked.Ct2Sent.encodeRaw, List.length_append] at h
  have h0 := loopsTo_uint64 V1State.Unchunked.Ct2Sent.mergeField 1 (default : V1State.Unchunked.Ct2Sent) 1#32 m.epoch (fun x => { (default : V1State.Unchunked.Ct2Sent) with epoch := x })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have h1 := loopsTo_optMessage V1State.Unchunked.Ct2Sent.mergeField 1 { (default : V1State.Unchunked.Ct2Sent) with epoch := m.epoch } 2#32
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth (fun x => { (default : V1State.Unchunked.Ct2Sent) with epoch := m.epoch, auth := x })
    (by decide) (by decide) (by decide) rfl
    (optMessage_sub _ _ _ 2#32 _ _ (Nat.le_refl _) (by omega) loopsTo_authenticator)
    (fun _ _ _ => rfl)
  exact (h0.append CryptoVerification.SpqrV1.Prost.MessageMerge.protoPrefixStep_unchunked_ct2Sent_mergeField h1).congr_res (by cases m; rfl)

theorem decode_uc_ct2Sent (m : V1State.Unchunked.Ct2Sent) (h : (V1State.Unchunked.Ct2Sent.encodeRaw m).length < 2 ^ 64) :
    V1State.Unchunked.Ct2Sent.decode (V1State.Unchunked.Ct2Sent.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo _ 1 _ _ (by decide) (loopsTo_uc_ct2Sent m h)

/-! ## Sanity checks -/

#guard V1State.Unchunked.Ct1Sent.decode (V1State.Unchunked.Ct1Sent.encodeRaw
    { epoch := 8#64, auth := some { rootKey := [1#8], macKey := [2#8] }, hdr := [15#8], es := [16#8],
      ct1 := List.replicate 960 17#8 }) =
  .ok { epoch := 8#64, auth := some { rootKey := [1#8], macKey := [2#8] }, hdr := [15#8], es := [16#8],
        ct1 := List.replicate 960 17#8 }
#guard V1State.Unchunked.KeysUnsampled.decode (V1State.Unchunked.KeysUnsampled.encodeRaw
    { epoch := 0xffffffffffffffff#64, auth := some { rootKey := [], macKey := [] } }) =
  .ok { epoch := 0xffffffffffffffff#64, auth := some { rootKey := [], macKey := [] } }

end CryptoVerification.SpqrV1Sync.Codec
