/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState

@[expose] public section

set_option autoImplicit false

/-!
# SPQR V1 `PolyEncoder` Point-Slice and Byte-Cap Helpers

`AllocCostModel`-free byte-cap constants (`sessionCapBytes`, `spqrStateTightCapBytes`, `msgCapBytes`)
and SPQR V1 `PolyEncoder` point-slice invariants (`ValidEncPbPts`, `ValidV1Pts`, `ValidPqPts`,
`ValidEncoderPts`, `EncPtsBounded`, `StatesPtsBounded`) preserved across `States.from_pb`,
`States.into_pb`, `States.send`, and `States.recv`.
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chunk GF16 Message MlKem NUM_POLYS Point PolyEncoder PolynomialEncoder PqRatchetState
   States StatesPanic StatesResult ToStatesPanic V1Recv V1Send V1State encoderFromPbStateDecode
   expectEncodeBytes liftSpqrPanic pbToProtoPolyEncoder protoPolyEncoderToPb spqrAuthApi
   spqrPolyApi u16ToBeBytes)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (distributeMsgChunksTotal_value_length_le encodeBytesResult encodeBytes_eq_ok)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (bytesToGF16ListTotal bytesToGF16List_eq_ok decodePbPointsTotal decodePbPolysTotal fromPbResult
   fromPb_eq_ok)
open CryptoVerification.SpqrV1.Top.StateSize (except_bind_eq_ok)

/-! ## 1. Canonical R3 & SPQR Byte-Cap Constants -/

/-- Canonical R3 2 MiB (`2,097,152` B) cap on serialized `SessionRecord` files
(`Computational.Proofs.LibsignalCli.Entry.sessionCapBytes`). -/
def sessionCapBytes : Nat := 2 ^ 21

/-- Tight serialized SPQR V1 ratchet state ceiling (`286,196` B, matching
`reachPq_pqLength_le_286196`). -/
def spqrStateTightCapBytes : Nat := 286196

/-- Canonical 1 MiB (`1,048,576` B) cap on SPQR `PolyEncoder` point slices and bounded CLI payloads. -/
def msgCapBytes : Nat := 2 ^ 20

theorem spqrStateTightCapBytes_le_sessionCapBytes :
    spqrStateTightCapBytes ≤ sessionCapBytes := by
  decide

theorem sessionCapBytes_lt_2_31 :
    sessionCapBytes < 2 ^ 31 := by
  decide

/-! ## 2. SPQR V1 `PolyEncoder` Point-Slice Caps (`ValidEncoderPts`) -/

/-- Point-slice byte cap on a protobuf `PolynomialEncoder` (`2 * 524288 = 1048576`, matching the
maximum input byte length `(1 <<< 16) * NUM_POLYS` accepted by `PolyEncoder::encode_bytes`). -/
def ValidEncPbPts (pb : PolynomialEncoder) : Prop :=
  ∀ bs ∈ pb.pts, bs.length ≤ 1048576

/-- Point-slice byte cap lifted to `Option PolynomialEncoder`. -/
def ValidOptEncPbPts : Option PolynomialEncoder → Prop
  | none => True
  | some pb => ValidEncPbPts pb

/-- Point-slice byte cap across the encoder-carrying variants of `V1State`. -/
def ValidV1Pts (v1 : V1State) : Prop :=
  match v1.innerState with
  | none => True
  | some (.keysUnsampled _) => True
  | some (.keysSampled s) => ValidOptEncPbPts s.sendingHdr
  | some (.headerSent s) => ValidOptEncPbPts s.sendingEk
  | some (.ct1Received s) => ValidOptEncPbPts s.sendingEk
  | some (.ekSentCt1Received _) => True
  | some (.noHeaderReceived _) => True
  | some (.headerReceived _) => True
  | some (.ct1Sampled s) => ValidOptEncPbPts s.sendingCt1
  | some (.ekReceivedCt1Sampled s) => ValidOptEncPbPts s.sendingCt1
  | some (.ct1Acknowledged _) => True
  | some (.ct2Sampled s) => ValidOptEncPbPts s.sendingCt2

/-- Point-slice byte cap on a decoded `PqRatchetState`. -/
def ValidPqPts (pq : PqRatchetState) : Prop :=
  match pq.inner with
  | none => True
  | some (.v1 v1) => ValidV1Pts v1

/-- Point-slice byte cap on serialized SPQR state bytes `stBytes`. -/
def ValidEncoderPts (stBytes : Bytes) : Prop :=
  match spqrDecodeState stBytes with
  | .error _ => True
  | .ok pq => ValidPqPts pq

/-- Decoded `PolyEncoder` point-count cap (`≤ 524288` GF16 elements per polynomial). -/
def EncPtsBounded (enc : PolyEncoder) : Prop :=
  ∀ pts, enc.s = .points pts → ∀ pt ∈ pts, pt.value.length ≤ 524288

/-- Decoded `States` point-count cap across the encoder-carrying variants. -/
def StatesPtsBounded {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysUnsampled _ => True
  | .keysSampled s => EncPtsBounded s.sending_hdr
  | .headerSent s => EncPtsBounded s.sending_ek
  | .ct1Received s => EncPtsBounded s.sending_ek
  | .ekSentCt1Received _ => True
  | .noHeaderReceived _ => True
  | .headerReceived _ => True
  | .ct1Sampled s => EncPtsBounded s.sending_ct1
  | .ekReceivedCt1Sampled s => EncPtsBounded s.sending_ct1
  | .ct1Acknowledged _ => True
  | .ct2Sampled s => EncPtsBounded s.sending_ct2

private theorem decodePbPointsTotal_len_and_bound {K : Nat} :
    ∀ (bss : List (List (BitVec 8))) (out : List Point),
      decodePbPointsTotal bss = .ok out →
      (∀ bs ∈ bss, bs.length ≤ 2 * K) →
      out.length = bss.length ∧ ∀ pt ∈ out, pt.value.length ≤ K
  | [], out, hdec, _ => by
    simp only [decodePbPointsTotal, Except.ok.injEq] at hdec
    subst hdec
    exact ⟨rfl, fun _ h => nomatch h⟩
  | bs :: rest, out, hdec, hbound => by
    dsimp only [decodePbPointsTotal] at hdec
    split_ifs at hdec with hodd
    cases hrest : decodePbPointsTotal rest with
    | error _ => simp [hrest] at hdec
    | ok tail =>
      simp only [hrest, Except.ok.injEq] at hdec
      subst hdec
      have heven : bs.length % 2 = 0 := by
        simpa [Bool.not_eq_true, bne_eq_false_iff_eq] using hodd
      obtain ⟨hlen_tail, hpt_tail⟩ := decodePbPointsTotal_len_and_bound rest tail hrest
        (fun b hb => hbound b (List.mem_cons_of_mem bs hb))
      refine ⟨by simp [hlen_tail], ?_⟩
      intro pt hpt
      rcases List.mem_cons.mp hpt with rfl | hmem
      · have hlen := (bytesToGF16List_eq_ok bs heven).2
        have hbs := hbound bs (List.mem_cons_self ..)
        change (bytesToGF16ListTotal bs).length ≤ K
        omega
      · exact hpt_tail pt hmem

private theorem flatMap_u16_len :
    ∀ cs : List GF16, (cs.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * cs.length
  | [] => rfl
  | _ :: cs => by
    simp only [List.flatMap_cons, List.length_append, flatMap_u16_len cs, List.length_cons]
    have h2 : ∀ v, (u16ToBeBytes v).length = 2 := fun _ => rfl
    rw [h2]; omega

theorem validEncPbPts_of_encPtsBounded {enc : PolyEncoder} (h : EncPtsBounded enc) :
    ValidEncPbPts (protoPolyEncoderToPb enc.intoPb) := by
  unfold ValidEncPbPts PolyEncoder.intoPb protoPolyEncoderToPb
  cases hs : enc.s with
  | points pts =>
    dsimp only
    intro bs hbs
    rcases List.mem_map.mp hbs with ⟨pt, hpt, rfl⟩
    rw [flatMap_u16_len]
    have hle := h pts hs pt hpt
    omega
  | polys _ =>
    dsimp only
    intro _ hbs; nomatch hbs

theorem encPtsBounded_of_encoderFromPb {opt : Option PolynomialEncoder} {enc : PolyEncoder}
    (hv : ValidOptEncPbPts opt)
    (h : encoderFromPbStateDecode spqrPolyApi opt = .ok enc) :
    EncPtsBounded enc := by
  cases opt with
  | none => contradiction
  | some pb =>
    dsimp only [ValidOptEncPbPts, ValidEncPbPts] at hv
    unfold encoderFromPbStateDecode spqrPolyApi at h
    dsimp only [StatesResult.ofPanic] at h
    rw [fromPb_eq_ok (pbToProtoPolyEncoder pb)] at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hres : fromPbResult (pbToProtoPolyEncoder pb) with
    | error _ => rw [hres] at h; contradiction
    | ok enc' =>
      rw [hres] at h
      have heq := Except.ok.inj h; subst heq
      unfold fromPbResult at hres
      have hpts_eq : (pbToProtoPolyEncoder pb).pts = pb.pts := rfl
      have hpolys_eq : (pbToProtoPolyEncoder pb).polys = pb.polys := rfl
      rw [hpts_eq, hpolys_eq] at hres
      by_cases hne : (!pb.pts.isEmpty) = true
      · simp only [hne, ↓reduceIte] at hres
        by_cases hpne : (!pb.polys.isEmpty) = true
        · simp [hpne] at hres
        · simp only [hpne, Bool.false_eq_true, ↓reduceIte] at hres
          by_cases hlen : (pb.pts.length != NUM_POLYS) = true
          · simp [hlen] at hres
          · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hres
            cases hd : decodePbPointsTotal pb.pts with
            | error _ => rw [hd] at hres; contradiction
            | ok out =>
              rw [hd] at hres
              have henc' := Except.ok.inj hres; subst henc'
              obtain ⟨_, hK⟩ := decodePbPointsTotal_len_and_bound (K := 524288) pb.pts out hd hv
              intro pts hpts
              cases hpts
              exact hK
      · simp only [hne, Bool.false_eq_true, ↓reduceIte] at hres
        by_cases hlen : (pb.polys.length == NUM_POLYS) = true
        · simp only [hlen, ↓reduceIte] at hres
          cases hd : decodePbPolysTotal pb.polys with
          | error _ => rw [hd] at hres; contradiction
          | ok out =>
            rw [hd] at hres
            have henc' := Except.ok.inj hres; subst henc'
            intro pts hpts; nomatch hpts
        · simp [hlen] at hres

theorem encPtsBounded_of_expectEncodeBytes {site : String} {msg : Bytes}
    {enc : PolyEncoder} (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    EncPtsBounded enc := by
  unfold expectEncodeBytes spqrPolyApi at h
  dsimp only [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] at h
  rw [encodeBytes_eq_ok msg] at h
  dsimp only [Except.mapError, Bind.bind, Except.bind] at h
  cases hres : encodeBytesResult msg with
  | error _ => rw [hres] at h; contradiction
  | ok enc' =>
    rw [hres] at h
    have heq := Except.ok.inj h; subst heq
    unfold encodeBytesResult at hres
    split_ifs at hres with hodd hlong
    cases hres
    have heven : msg.length % 2 = 0 := by
      simpa [Bool.not_eq_true, bne_eq_false_iff_eq] using hodd
    have hmax : msg.length ≤ 1048576 := by
      have hnp : (1 <<< 16) * NUM_POLYS = 1048576 := rfl
      omega
    have hinit_len : (List.replicate NUM_POLYS ({ value := [] } : Point)).length = 16 := rfl
    intro pts hpts
    cases hpts
    intro pt hpt
    have hle := distributeMsgChunksTotal_value_length_le msg 0
      (List.replicate NUM_POLYS { value := [] }) heven hinit_len
      (fun p hp => by rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; decide) pt hpt
    omega

private theorem encPtsBounded_pointAt {self self' : PolyEncoder} {poly idx : Nat} {val : GF16}
    (hv : EncPtsBounded self) (h : self.pointAt poly idx = .ok (self', val)) :
    EncPtsBounded self' := by
  unfold PolyEncoder.pointAt at h
  cases hs : self.s with
  | points pts =>
    rw [hs] at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hget : pts[poly]? with
    | none => rw [hget] at h; contradiction
    | some pt =>
      rw [hget] at h; dsimp only at h
      cases hval : pt.value[idx]? with
      | some v =>
        rw [hval] at h
        have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
        exact hv
      | none =>
        rw [hval] at h; dsimp only at h
        cases hloop : PolyEncoder.pointsToPolysLoop pts 0 NUM_POLYS [] with
        | error _ => rw [hloop] at h; contradiction
        | ok polys =>
          rw [hloop] at h; dsimp only [Pure.pure, Except.pure] at h
          cases hp : polys[poly]? with
          | none => rw [hp] at h; contradiction
          | some p =>
            rw [hp] at h; dsimp only at h
            cases hc : p.computeAt (GF16.new (BitVec.ofNat 16 idx)) with
            | error _ => rw [hc] at h; contradiction
            | ok y =>
              rw [hc] at h
              have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
              intro _ hpts; nomatch hpts
  | polys polys =>
    rw [hs] at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    rw [hs] at h
    dsimp only at h
    cases hp : polys[poly]? with
    | none => rw [hp] at h; contradiction
    | some p =>
      rw [hp] at h; dsimp only at h
      cases hc : p.computeAt (GF16.new (BitVec.ofNat 16 idx)) with
      | error _ => rw [hc] at h; contradiction
      | ok y =>
        rw [hc] at h
        have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
        exact hv

private theorem encPtsBounded_chunkAtLoop (idx : BitVec 16) :
    ∀ (i rem : Nat) (self self' : PolyEncoder) (out : List.Vector (BitVec 8) (2 * rem)),
      EncPtsBounded self →
      PolyEncoder.chunkAtLoop idx i rem self = .ok (self', out) →
      EncPtsBounded self'
  | _, 0, self, self', _, hv, h => by
    simp only [PolyEncoder.chunkAtLoop, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ hv
  | i, rem + 1, self, self', out, hv, h => by
    simp only [PolyEncoder.chunkAtLoop] at h
    rcases except_bind_eq_ok h with ⟨⟨s1, p⟩, hp, h1⟩
    rcases except_bind_eq_ok h1 with ⟨⟨s2, tail⟩, htail, h2⟩
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    exact encPtsBounded_chunkAtLoop idx (i + 1) rem s1 s2 tail (encPtsBounded_pointAt hv hp) htail

theorem encPtsBounded_of_nextChunk {enc enc' : PolyEncoder} {chunk : Chunk}
    (hv : EncPtsBounded enc)
    (h : (liftM (spqrPolyApi.next_chunk enc) :
      Except StatesPanic (spqrPolyApi.PolyEncoder × spqrPolyApi.Chunk)) = .ok (enc', chunk)) :
    EncPtsBounded enc' := by
  unfold spqrPolyApi at h
  dsimp only [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] at h
  cases hnc : enc.nextChunk with
  | error _ => rw [hnc] at h; contradiction
  | ok pair =>
    rw [hnc] at h
    have hinj := Except.ok.inj h; subst hinj
    unfold PolyEncoder.nextChunk PolyEncoder.chunkAt at hnc
    rcases except_bind_eq_ok hnc with ⟨⟨s1, out⟩, h1, h2⟩
    rcases except_bind_eq_ok h1 with ⟨⟨s2, data⟩, hloop, h1b⟩
    have hs1 := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hs1
    have hs2 := (Prod.mk.inj (Except.ok.inj h2)).1; subst hs2
    have hb := encPtsBounded_chunkAtLoop (enc.idx.setWidth 16) 0 16 enc s2 data hv hloop
    intro pts hpts
    exact hb pts hpts

theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]

theorem validV1Pts_states_into_pb {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} (h : StatesPtsBounded st) :
    ValidV1Pts st.into_pb := by
  cases st with
  | keysUnsampled _ => trivial
  | keysSampled s => exact validEncPbPts_of_encPtsBounded h
  | headerSent s => exact validEncPbPts_of_encPtsBounded h
  | ct1Received s => exact validEncPbPts_of_encPtsBounded h
  | ekSentCt1Received _ => trivial
  | noHeaderReceived _ => trivial
  | headerReceived _ => trivial
  | ct1Sampled s => exact validEncPbPts_of_encPtsBounded h
  | ekReceivedCt1Sampled s => exact validEncPbPts_of_encPtsBounded h
  | ct1Acknowledged _ => trivial
  | ct2Sampled s => exact validEncPbPts_of_encPtsBounded h

theorem statesPtsBounded_of_from_pb {F : ShaCompress} {pb : V1State}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (hv : ValidV1Pts pb) (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st) :
    StatesPtsBounded st := by
  unfold States.from_pb at h
  unfold ValidV1Pts at hv
  cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some iv =>
    rw [hinner] at h hv
    cases iv with
    | keysUnsampled _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      have hinj := Except.ok.inj h; subst hinj; trivial
    | keysSampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hfp
      have hinj := Except.ok.inj h; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.from_pb at hfp
      cases huc : s.uc with
      | none => rw [huc] at hfp; contradiction
      | some u =>
        rw [huc] at hfp; dsimp only [Bind.bind, Except.bind] at hfp
        rcases except_bind_eq_ok hfp with ⟨_, _, hfp2⟩
        rcases except_bind_eq_ok hfp2 with ⟨enc, henc, hfp3⟩
        have hinj2 := Except.ok.inj hfp3; subst hinj2
        exact encPtsBounded_of_encoderFromPb hv henc
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hfp
      have hinj := Except.ok.inj h; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.from_pb at hfp
      cases hrec : s.receivingCt1 with
      | none =>
        rw [hrec] at hfp; dsimp only [Bind.bind, Except.bind] at hfp
        cases huc : s.uc with
        | none => rw [huc] at hfp; contradiction
        | some u =>
          rw [huc] at hfp; dsimp only [Bind.bind, Except.bind] at hfp
          rcases except_bind_eq_ok hfp with ⟨_, _, hfp2⟩
          rcases except_bind_eq_ok hfp2 with ⟨_, _, hfp3⟩; contradiction
      | some d0 =>
        rw [hrec] at hfp; dsimp only at hfp
        split at hfp
        · contradiction
        · cases huc : s.uc with
          | none => rw [huc] at hfp; contradiction
          | some u =>
            rw [huc] at hfp; dsimp only [Bind.bind, Except.bind] at hfp
            rcases except_bind_eq_ok hfp with ⟨_, _, hfp2⟩
            rcases except_bind_eq_ok hfp2 with ⟨enc, henc, hfp3⟩
            rcases except_bind_eq_ok hfp3 with ⟨_, _, hfp4⟩
            have hinj2 := Except.ok.inj hfp4; subst hinj2
            exact encPtsBounded_of_encoderFromPb hv henc
    | ct1Received s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hfp
      have hinj := Except.ok.inj h; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.from_pb at hfp
      cases huc : s.uc with
      | none => rw [huc] at hfp; contradiction
      | some u =>
        rw [huc] at hfp; dsimp only [Bind.bind, Except.bind] at hfp
        rcases except_bind_eq_ok hfp with ⟨_, _, hfp2⟩
        rcases except_bind_eq_ok hfp2 with ⟨enc, henc, hfp3⟩
        have hinj2 := Except.ok.inj hfp3; subst hinj2
        exact encPtsBounded_of_encoderFromPb hv henc
    | ekSentCt1Received _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      have hinj := Except.ok.inj h; subst hinj; trivial
    | noHeaderReceived _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      have hinj := Except.ok.inj h; subst hinj; trivial
    | headerReceived _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      have hinj := Except.ok.inj h; subst hinj; trivial
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hfp
      have hinj := Except.ok.inj h; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.from_pb at hfp
      dsimp only [Bind.bind, Except.bind] at hfp
      cases huc : s.uc with
      | none => rw [huc] at hfp; split at hfp <;> [split at hfp <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hfp
        have hbody : (do
            let uc ← CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb
              (spqrAuthApi F) u
            let sendingCt1 ← encoderFromPbStateDecode spqrPolyApi s.sendingCt1
            let receivingEk ← CryptoVerification.LibsignalSpqrV1.decoderFromPbStateDecode
              spqrPolyApi s.receivingEk
            Except.ok { uc := uc, sending_ct1 := sendingCt1, receiving_ek := receivingEk }) =
              Except.ok v := by
          split at hfp <;> [split at hfp <;> [contradiction; exact hfp]; exact hfp]
        rcases except_bind_eq_ok hbody with ⟨_, _, hfp2⟩
        rcases except_bind_eq_ok hfp2 with ⟨enc, henc, hfp3⟩
        rcases except_bind_eq_ok hfp3 with ⟨_, _, hfp4⟩
        have hinj2 := Except.ok.inj hfp4; subst hinj2
        exact encPtsBounded_of_encoderFromPb hv henc
    | ekReceivedCt1Sampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hfp
      have hinj := Except.ok.inj h; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.from_pb at hfp
      cases huc : s.uc with
      | none => rw [huc] at hfp; contradiction
      | some u =>
        rw [huc] at hfp; dsimp only [Bind.bind, Except.bind] at hfp
        rcases except_bind_eq_ok hfp with ⟨_, _, hfp2⟩
        rcases except_bind_eq_ok hfp2 with ⟨enc, henc, hfp3⟩
        have hinj2 := Except.ok.inj hfp3; subst hinj2
        exact encPtsBounded_of_encoderFromPb hv henc
    | ct1Acknowledged _ =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      have hinj := Except.ok.inj h; subst hinj; trivial
    | ct2Sampled s =>
      dsimp only [Functor.map, Except.map] at h
      split at h <;> try contradiction
      rename_i v hfp
      have hinj := Except.ok.inj h; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.from_pb at hfp
      cases huc : s.uc with
      | none => rw [huc] at hfp; contradiction
      | some u =>
        rw [huc] at hfp; dsimp only [Bind.bind, Except.bind] at hfp
        rcases except_bind_eq_ok hfp with ⟨_, _, hfp2⟩
        rcases except_bind_eq_ok hfp2 with ⟨enc, henc, hfp3⟩
        have hinj2 := Except.ok.inj hfp3; subst hinj2
        exact encPtsBounded_of_encoderFromPb hv henc

theorem statesPtsBounded_of_send {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {tape tape' : Bytes}
    {sendOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hv : StatesPtsBounded self) (h : self.send K tape = .ok (sendOut, tape')) :
    StatesPtsBounded sendOut.state := by
  unfold States.send at h
  cases self with
  | keysUnsampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _, _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.send_hdr_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩
    rcases except_bind_eq_ok h1c with ⟨⟨enc1, _⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk (encPtsBounded_of_expectEncodeBytes henc0) hnext
  | keysSampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.send_hdr_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk hv hnext
  | headerSent state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.send_ek_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk hv hnext
  | ct1Received state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.send_ek_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk hv hnext
  | ekSentCt1Received _ =>
    dsimp only at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; trivial
  | noHeaderReceived _ =>
    dsimp only at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; trivial
  | headerReceived state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _, _, _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.send_ct1_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩
    rcases except_bind_eq_ok h1c with ⟨⟨enc1, _⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk (encPtsBounded_of_expectEncodeBytes henc0) hnext
  | ct1Sampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.send_ct1_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk hv hnext
  | ekReceivedCt1Sampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk hv hnext
  | ct1Acknowledged _ =>
    dsimp only at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; trivial
  | ct2Sampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.send_ct2_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBounded_of_nextChunk hv hnext

theorem statesPtsBounded_of_recv {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hv : StatesPtsBounded self) (h : self.recv K msg = .ok recvOut) :
    StatesPtsBounded recvOut.state := by
  unfold States.recv at h
  cases self with
  | keysUnsampled _ =>
    dsimp only at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; trivial
  | keysSampled state =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact hv)
    split at h
    · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
      rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.recv_ct1_chunk at h1
      dsimp only at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨_, _, h1c⟩
      rcases except_bind_eq_ok h1c with ⟨enc0, henc0, h1d⟩
      have hs' := Except.ok.inj h1d; subst hs'
      exact encPtsBounded_of_expectEncodeBytes henc0
    · have hinj := Except.ok.inj h; subst hinj; exact hv
  | headerSent state =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact hv)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      rw [statesResult_ofPanic_eq_ok] at h1
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.recv_ct1_chunk at h1
      split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres
        have hinj := Except.ok.inj h2; subst hinj; exact hv
      | some _ =>
        rcases except_bind_eq_ok h1c with ⟨_, _, h1d⟩
        have hres := Except.ok.inj h1d; subst hres
        have hinj := Except.ok.inj h2; subst hinj; exact hv
    · have hinj := Except.ok.inj h; subst hinj; exact hv
  | ct1Received state =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact hv)
    split at h
    · rcases except_bind_eq_ok h with ⟨_, _, h2⟩
      have hinj := Except.ok.inj h2; subst hinj; trivial
    · have hinj := Except.ok.inj h; subst hinj; exact hv
  | ekSentCt1Received _ =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; trivial)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at h1
      dsimp only at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres
        have hinj := Except.ok.inj h2; subst hinj; trivial
      | some _ =>
        dsimp only at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨_, _, h1d⟩
        rcases except_bind_eq_ok h1d with ⟨_, _, h1e⟩
        have hres := Except.ok.inj h1e; subst hres
        have hinj := Except.ok.inj h2; subst hinj; trivial
    · have hinj := Except.ok.inj h; subst hinj; trivial
  | noHeaderReceived _ =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; trivial)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at h1
      dsimp only at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres
        have hinj := Except.ok.inj h2; subst hinj; trivial
      | some _ =>
        dsimp only at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨receivingEkRes, _, h1d⟩
        rcases except_bind_eq_ok h1d with ⟨_, _, h1e⟩
        cases receivingEkRes with
        | error _ => contradiction
        | ok _ =>
          have hres := Except.ok.inj h1e; subst hres
          have hinj := Except.ok.inj h2; subst hinj; trivial
    · have hinj := Except.ok.inj h; subst hinj; trivial
  | headerReceived _ =>
    dsimp only at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; trivial
  | ct1Sampled state =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact hv)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact hv)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.recv_ek_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
    rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    cases decoded? with
    | none =>
      dsimp only at h1c
      split at h1c <;>
        (have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj)
      · trivial
      · exact hv
    | some _ =>
      dsimp only at h1c
      rcases except_bind_eq_ok h1c with ⟨_, _, h1d⟩
      split at h1d
      · rcases except_bind_eq_ok h1d with ⟨_, _, h1e⟩
        rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩
        rw [statesResult_ofPanic_eq_ok] at henc2
        unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder at henc2
        have hres := Except.ok.inj h1f; subst hres
        have hinj := Except.ok.inj h2; subst hinj
        exact encPtsBounded_of_expectEncodeBytes henc2
      · have hres := Except.ok.inj h1d; subst hres
        have hinj := Except.ok.inj h2; subst hinj; exact hv
  | ekReceivedCt1Sampled state =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact hv)
    have hack_ok : ∀ s', StatesResult.ofPanic (state.recv_ct1_ack K msg.epoch) = .ok s' →
        EncPtsBounded s'.sending_ct2 := by
      intro s' h1
      rw [statesResult_ofPanic_eq_ok] at h1
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h1
      dsimp only at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨sendingCt2, henc2, h1c⟩
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder at henc2
      have hs' := Except.ok.inj h1c; subst hs'
      exact encPtsBounded_of_expectEncodeBytes henc2
    cases hpay : msg.payload with
    | none | hdr _ | ek _ | ct1 _ | ct2 _ =>
      rw [hpay] at h; dsimp only at h
      have hinj := Except.ok.inj h; subst hinj; exact hv
    | ekCt1Ack _ =>
      rw [hpay] at h; dsimp only at h
      rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
      have hinj := Except.ok.inj h2; subst hinj
      exact hack_ok s' h1
    | ct1Ack b =>
      cases b with
      | false =>
        rw [hpay] at h; dsimp only at h
        have hinj := Except.ok.inj h; subst hinj; exact hv
      | true =>
        rw [hpay] at h; dsimp only at h
        rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
        have hinj := Except.ok.inj h2; subst hinj
        exact hack_ok s' h1
  | ct1Acknowledged _ =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; trivial)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; trivial)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
    rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres
      have hinj := Except.ok.inj h2; subst hinj; trivial
    | some _ =>
      dsimp only at h1c
      rcases except_bind_eq_ok h1c with ⟨_, _, h1d⟩
      rcases except_bind_eq_ok h1d with ⟨_, _, h1e⟩
      rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩
      rw [statesResult_ofPanic_eq_ok] at henc2
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder at henc2
      have hres := Except.ok.inj h1f; subst hres
      have hinj := Except.ok.inj h2; subst hinj
      exact encPtsBounded_of_expectEncodeBytes henc2
  | ct2Sampled state =>
    dsimp only at h; split at h
    · split at h <;> [skip; contradiction]
      rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
      rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.recv_next_epoch at h1
      rcases except_bind_eq_ok h1 with ⟨_, _, h1b⟩
      have hs' := Except.ok.inj h1b; subst hs'; trivial
    · have hinj := Except.ok.inj h; subst hinj; exact hv

end LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
