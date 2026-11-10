/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire

/-!
# Prost Round-Trip for Leaf Messages

`LoopsTo` (recursion depth 0) and `decode (encodeRaw m) = .ok m` round-trip theorems for the leaf
messages of `pq_ratchet.proto` (`ChainParamsPB`, `EpochDirectionPB`, `ProtoAuthenticator`,
`PolynomialEncoder`, and `PolynomialDecoder`), together with sub-slice length bounds used by
enclosing messages.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)
theorem length_le_encodeBytesField (tag : BitVec 32) (v : Bytes) :
    v.length ≤ (Proto.encodeBytesField tag v).length := by
  unfold Proto.encodeBytesField
  cases v with
  | nil => simp
  | cons b tl =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Proto.encodeBytesUncond,
      List.length_append, List.length_cons]
    omega

theorem length_le_encodeMessage {N : Type} (encodeRaw : N → Bytes) (tag : BitVec 32) (n : N) :
    (encodeRaw n).length ≤ (Proto.encodeMessage encodeRaw tag n).length := by
  unfold Proto.encodeMessage
  simp only [List.length_append]
  omega

theorem length_le_encodeOptMessage {N : Type} (encodeRaw : N → Bytes) (tag : BitVec 32) (n : N) :
    (encodeRaw n).length ≤ (Proto.encodeOptMessage encodeRaw tag (some n)).length := by
  simpa only [Proto.encodeOptMessage] using length_le_encodeMessage encodeRaw tag n


/-! ## Repeated-field length bounds and leaf round-trips -/

section MoveCompat
open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)
open CryptoVerification.SpqrV1.Prost.MessageMerge (protoPrefixStep_chainParamsPB_mergeField
  protoPrefixStep_epochDirectionPB_mergeField protoPrefixStep_protoAuthenticator_mergeField
  protoPrefixStep_polynomialEncoder_mergeField protoPrefixStep_polynomialDecoder_mergeField)

theorem length_le_encodeRepeatedBytes (tag : BitVec 32) (vs : List Bytes) (v : Bytes) (hv : v ∈ vs) :
    v.length ≤ (Proto.encodeRepeatedBytes tag vs).length := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    simp only [Proto.encodeRepeatedBytes, List.foldr_cons, List.length_append] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | hv
    · simp [Proto.encodeBytesUncond]; omega
    · have := ih hv; omega

theorem length_le_encodeRepeatedMessage {N : Type} (encodeRaw : N → Bytes) (tag : BitVec 32)
    (ns : List N) (n : N) (hn : n ∈ ns) :
    (encodeRaw n).length ≤ (Proto.encodeRepeatedMessage encodeRaw tag ns).length := by
  induction ns with
  | nil => simp at hn
  | cons w ns ih =>
    simp only [Proto.encodeRepeatedMessage, List.foldr_cons, List.length_append] at ih ⊢
    rcases List.mem_cons.mp hn with rfl | hn
    · have := length_le_encodeMessage encodeRaw tag n; omega
    · have := ih hn; omega

theorem loopsTo_chainParams (p : ChainParamsPB) :
    LoopsTo ChainParamsPB.mergeField 0 default (ChainParamsPB.encodeRaw p) p := by
  have hA := loopsTo_uint32 ChainParamsPB.mergeField 0 (default : ChainParamsPB) 1#32 p.maxJump
    (fun x => { (default : ChainParamsPB) with maxJump := x }) (by decide) (by decide) rfl
    (fun _ _ _ => by simp [ChainParamsPB.mergeField])
  have hB := loopsTo_uint32 ChainParamsPB.mergeField 0
    { (default : ChainParamsPB) with maxJump := p.maxJump } 2#32 p.maxOooKeys
    (fun x => { (default : ChainParamsPB) with maxJump := p.maxJump, maxOooKeys := x })
    (by decide) (by decide) rfl (fun _ _ _ => by simp [ChainParamsPB.mergeField])
  exact (LoopsTo.append protoPrefixStep_chainParamsPB_mergeField hA hB).congr_res (by cases p; rfl)

theorem loopsTo_epochDirection (e : EpochDirectionPB)
    (h : (EpochDirectionPB.encodeRaw e).length < 2 ^ 64) :
    LoopsTo EpochDirectionPB.mergeField 0 default (EpochDirectionPB.encodeRaw e) e := by
  simp only [EpochDirectionPB.encodeRaw, List.length_append] at h
  have hn := length_le_encodeBytesField 2#32 e.next
  have hp := length_le_encodeBytesField 3#32 e.prev
  have hA := loopsTo_uint32 EpochDirectionPB.mergeField 0 (default : EpochDirectionPB) 1#32 e.ctr
    (fun x => { (default : EpochDirectionPB) with ctr := x }) (by decide) (by decide) rfl
    (fun _ _ _ => by simp [EpochDirectionPB.mergeField])
  have hB := loopsTo_bytes EpochDirectionPB.mergeField 0
    { (default : EpochDirectionPB) with ctr := e.ctr } 2#32 e.next
    (fun x => { (default : EpochDirectionPB) with ctr := e.ctr, next := x })
    (by decide) (by decide) rfl (by omega) (fun _ _ _ => by simp [EpochDirectionPB.mergeField])
  have hC := loopsTo_bytes EpochDirectionPB.mergeField 0
    { (default : EpochDirectionPB) with ctr := e.ctr, next := e.next } 3#32 e.prev
    (fun x => { (default : EpochDirectionPB) with ctr := e.ctr, next := e.next, prev := x })
    (by decide) (by decide) rfl (by omega) (fun _ _ _ => by simp [EpochDirectionPB.mergeField])
  exact ((LoopsTo.append protoPrefixStep_epochDirectionPB_mergeField hA hB).append
    protoPrefixStep_epochDirectionPB_mergeField hC).congr_res (by cases e; rfl)

theorem loopsTo_authenticator (a : ProtoAuthenticator)
    (h : (ProtoAuthenticator.encodeRaw a).length < 2 ^ 64) :
    LoopsTo ProtoAuthenticator.mergeField 0 default (ProtoAuthenticator.encodeRaw a) a := by
  simp only [ProtoAuthenticator.encodeRaw, List.length_append] at h
  have hr := length_le_encodeBytesField 1#32 a.rootKey
  have hm := length_le_encodeBytesField 2#32 a.macKey
  have hA := loopsTo_bytes ProtoAuthenticator.mergeField 0 (default : ProtoAuthenticator) 1#32
    a.rootKey (fun x => { (default : ProtoAuthenticator) with rootKey := x })
    (by decide) (by decide) rfl (by omega) (fun _ _ _ => by simp [ProtoAuthenticator.mergeField])
  have hB := loopsTo_bytes ProtoAuthenticator.mergeField 0
    { (default : ProtoAuthenticator) with rootKey := a.rootKey } 2#32 a.macKey
    (fun x => { (default : ProtoAuthenticator) with rootKey := a.rootKey, macKey := x })
    (by decide) (by decide) rfl (by omega) (fun _ _ _ => by simp [ProtoAuthenticator.mergeField])
  exact (LoopsTo.append protoPrefixStep_protoAuthenticator_mergeField hA hB).congr_res
    (by cases a; rfl)

theorem loopsTo_polyEncoder (e : PolynomialEncoder)
    (h : (PolynomialEncoder.encodeRaw e).length < 2 ^ 64) :
    LoopsTo PolynomialEncoder.mergeField 0 default (PolynomialEncoder.encodeRaw e) e := by
  simp only [PolynomialEncoder.encodeRaw, List.length_append] at h
  have hA := loopsTo_uint32 PolynomialEncoder.mergeField 0 (default : PolynomialEncoder) 1#32 e.idx
    (fun x => { (default : PolynomialEncoder) with idx := x }) (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hB := loopsTo_repeatedBytes PolynomialEncoder.mergeField protoPrefixStep_polynomialEncoder_mergeField 0
    { (default : PolynomialEncoder) with idx := e.idx } 2#32 e.pts (·.pts) (fun m l => { m with pts := l })
    (by decide) (by decide)
    (fun v hv => by have := length_le_encodeRepeatedBytes 2#32 e.pts v hv; omega)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ => rfl)
  have hC := loopsTo_repeatedBytes PolynomialEncoder.mergeField protoPrefixStep_polynomialEncoder_mergeField 0
    { (default : PolynomialEncoder) with idx := e.idx, pts := e.pts } 3#32 e.polys (·.polys)
    (fun m l => { m with polys := l })
    (by decide) (by decide)
    (fun v hv => by have := length_le_encodeRepeatedBytes 3#32 e.polys v hv; omega)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ => rfl)
  exact ((LoopsTo.append protoPrefixStep_polynomialEncoder_mergeField hA hB).append
    protoPrefixStep_polynomialEncoder_mergeField hC).congr_res (by cases e; rfl)

theorem loopsTo_polyDecoder (d : PolynomialDecoder)
    (h : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64) :
    LoopsTo PolynomialDecoder.mergeField 0 default (PolynomialDecoder.encodeRaw d) d := by
  simp only [PolynomialDecoder.encodeRaw, List.length_append] at h
  have hA := loopsTo_uint32 PolynomialDecoder.mergeField 0 (default : PolynomialDecoder) 1#32 d.ptsNeeded
    (fun x => { (default : PolynomialDecoder) with ptsNeeded := x }) (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hB := loopsTo_uint32 PolynomialDecoder.mergeField 0 { (default : PolynomialDecoder) with ptsNeeded := d.ptsNeeded }
    2#32 d.polys (fun x => { (default : PolynomialDecoder) with ptsNeeded := d.ptsNeeded, polys := x })
    (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  have hC := loopsTo_repeatedBytes PolynomialDecoder.mergeField protoPrefixStep_polynomialDecoder_mergeField 0
    { (default : PolynomialDecoder) with ptsNeeded := d.ptsNeeded, polys := d.polys } 3#32 d.pts (·.pts)
    (fun m l => { m with pts := l })
    (by decide) (by decide)
    (fun v hv => by have := length_le_encodeRepeatedBytes 3#32 d.pts v hv; omega)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ => rfl)
  have hD := loopsTo_bool PolynomialDecoder.mergeField 0
    { (default : PolynomialDecoder) with ptsNeeded := d.ptsNeeded, polys := d.polys, pts := d.pts } 4#32 d.isComplete
    (fun x => { (default : PolynomialDecoder) with
      ptsNeeded := d.ptsNeeded, polys := d.polys, pts := d.pts, isComplete := x })
    (by decide) (by decide) rfl
    (fun _ _ _ => rfl)
  exact (((LoopsTo.append protoPrefixStep_polynomialDecoder_mergeField hA hB).append
    protoPrefixStep_polynomialDecoder_mergeField hC).append
    protoPrefixStep_polynomialDecoder_mergeField hD).congr_res (by cases d; rfl)

end MoveCompat

end CryptoVerification.SpqrV1Sync.Codec
