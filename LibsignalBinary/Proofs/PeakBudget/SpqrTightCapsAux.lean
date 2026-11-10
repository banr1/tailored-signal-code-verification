/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs

@[expose] public section

set_option autoImplicit false

/-!
# Parametric SPQR V1 Point-Slice (`K ≤ 640`) and `ChainParamsPB` Predicates

Defines cost-model-free SPQR V1 domain predicates and `States` / `Chain` preservation lemmas:
- `ValidEncoderPtsAt K` (`ValidEncoderPts640` at `K = 640`): bounds every `PolyEncoder` `.points`
  slice to at most `K` `GF16` elements (`≤ 2 * K` bytes, covering the protocol maximum of `576`
  points on `1,152`-byte ML-KEM encapsulation keys).
- `ValidChainParams`: bounds `maxJump ≤ 25,000` and `maxOooKeys ≤ 2,000` across `Chain` and
  `VersionNegotiationPB` transitions.
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chain ChainPB ChainParams ChainParamsPB ChainResult Chunk Direction
   ENCAPSULATION_KEY_SIZE ENCAPSULATION_STATE_SIZE Epoch EpochSecret GF16 HkdfFn Message MlKem
   NUM_POLYS Point PolyEncoder PolynomialEncoder PqRatchetState SpqrPanic States StatesPanic
   StatesResult V1Recv V1Send V1State VersionNegotiationPB bytesToVector? chainFrom
   chainFromVersionNegotiation encaps1 encaps2 encoderFromPbStateDecode expectEncodeBytes generate
   liftSpqrPanic pbToProtoPolyEncoder protoPolyEncoderToPb spqrAuthApi spqrPolyApi u16ToBeBytes)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (distributeMsgChunksTotal_value_length_le encodeBytesResult encodeBytes_eq_ok)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (bytesToGF16ListTotal bytesToGF16List_eq_ok decodePbPointsTotal decodePbPolysTotal fromPbResult
   fromPb_eq_ok)
open CryptoVerification.SpqrV1.Top.StateSize (encaps1_lengths except_bind_eq_ok generate_lengths)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
  (ValidEncPbPts ValidEncoderPts ValidOptEncPbPts ValidPqPts ValidV1Pts statesResult_ofPanic_eq_ok)

/-! ## Parametric `PolyEncoder` Point-Slice Caps (`ValidEncoderPtsAt K`) -/

/-- Tight `GF16` point-count ceiling per SPQR polynomial (`640` points = `1,280` bytes). -/
def spqrEncTightPtsCap : Nat := 640

/-- Point-slice byte bound (`bs.length ≤ 2 * K`) on a protobuf `PolynomialEncoder`. -/
def ValidEncPbPtsAt (K : Nat) (pb : PolynomialEncoder) : Prop :=
  ∀ bs ∈ pb.pts, bs.length ≤ 2 * K

def ValidOptEncPbPtsAt (K : Nat) : Option PolynomialEncoder → Prop
  | none => True
  | some pb => ValidEncPbPtsAt K pb

/-- Point-slice byte bound across all encoder-carrying variants of `V1State`. -/
def ValidV1PtsAt (K : Nat) (v1 : V1State) : Prop :=
  match v1.innerState with
  | none => True
  | some (.keysUnsampled _) => True
  | some (.keysSampled s) => ValidOptEncPbPtsAt K s.sendingHdr
  | some (.headerSent s) => ValidOptEncPbPtsAt K s.sendingEk
  | some (.ct1Received s) => ValidOptEncPbPtsAt K s.sendingEk
  | some (.ekSentCt1Received _) => True
  | some (.noHeaderReceived _) => True
  | some (.headerReceived _) => True
  | some (.ct1Sampled s) => ValidOptEncPbPtsAt K s.sendingCt1
  | some (.ekReceivedCt1Sampled s) => ValidOptEncPbPtsAt K s.sendingCt1
  | some (.ct1Acknowledged _) => True
  | some (.ct2Sampled s) => ValidOptEncPbPtsAt K s.sendingCt2

/-- Point-slice byte bound on a decoded `PqRatchetState`. -/
def ValidPqPtsAt (K : Nat) (pq : PqRatchetState) : Prop :=
  match pq.inner with
  | none => True
  | some (.v1 v1) => ValidV1PtsAt K v1

/-- Point-slice byte bound on serialized SPQR state bytes. -/
def ValidEncoderPtsAt (K : Nat) (stBytes : Bytes) : Prop :=
  match spqrDecodeState stBytes with
  | .error _ => True
  | .ok pq => ValidPqPtsAt K pq

/-- `K = 640` specialization of `ValidEncoderPtsAt`. -/
abbrev ValidEncoderPts640 (stBytes : Bytes) : Prop :=
  ValidEncoderPtsAt 640 stBytes

theorem validEncPbPtsAt_mono {K₁ K₂ : Nat} (hK : K₁ ≤ K₂) {pb : PolynomialEncoder}
    (h : ValidEncPbPtsAt K₁ pb) : ValidEncPbPtsAt K₂ pb :=
  fun bs hbs => Nat.le_trans (h bs hbs) (Nat.mul_le_mul_left 2 hK)

theorem validOptEncPbPtsAt_mono {K₁ K₂ : Nat} (hK : K₁ ≤ K₂) {opt : Option PolynomialEncoder}
    (h : ValidOptEncPbPtsAt K₁ opt) : ValidOptEncPbPtsAt K₂ opt := by
  cases opt with
  | none => trivial
  | some pb => exact validEncPbPtsAt_mono hK h

theorem validV1PtsAt_mono {K₁ K₂ : Nat} (hK : K₁ ≤ K₂) {v1 : V1State}
    (h : ValidV1PtsAt K₁ v1) : ValidV1PtsAt K₂ v1 := by
  revert h
  unfold ValidV1PtsAt
  cases v1.innerState with
  | none => intro _; trivial
  | some iv =>
    cases iv <;> intro h <;>
      first
      | trivial
      | exact validOptEncPbPtsAt_mono hK h

theorem validPqPtsAt_mono {K₁ K₂ : Nat} (hK : K₁ ≤ K₂) {pq : PqRatchetState}
    (h : ValidPqPtsAt K₁ pq) : ValidPqPtsAt K₂ pq := by
  revert h
  unfold ValidPqPtsAt
  cases pq.inner with
  | none => intro _; trivial
  | some i => cases i; intro h; exact validV1PtsAt_mono hK h

theorem validEncoderPtsAt_mono {K₁ K₂ : Nat} (hK : K₁ ≤ K₂) {s : Bytes}
    (h : ValidEncoderPtsAt K₁ s) : ValidEncoderPtsAt K₂ s := by
  revert h
  unfold ValidEncoderPtsAt
  cases spqrDecodeState s with
  | error _ => intro _; trivial
  | ok pq => intro h; exact validPqPtsAt_mono hK h

theorem validEncoderPts_of_validEncoderPtsAt {K : Nat} (hK : K ≤ 524288) {s : Bytes}
    (h : ValidEncoderPtsAt K s) : ValidEncoderPts s := by
  have h524 : ValidEncoderPtsAt 524288 s := validEncoderPtsAt_mono hK h
  revert h524
  unfold ValidEncoderPtsAt ValidEncoderPts
  cases spqrDecodeState s with
  | error _ => intro _; trivial
  | ok pq =>
    unfold ValidPqPtsAt ValidPqPts
    cases pq.inner with
    | none => intro _; trivial
    | some i =>
      cases i with
      | v1 v1 =>
        unfold ValidV1PtsAt ValidV1Pts
        cases v1.innerState with
        | none => intro _; trivial
        | some iv => cases iv <;> intro h524 <;> trivial

theorem validEncoderPts_of_validEncoderPts640 {s : Bytes}
    (h : ValidEncoderPts640 s) : ValidEncoderPts s :=
  validEncoderPts_of_validEncoderPtsAt (by decide) h

/-! ## `EncPtsBoundedAt K` and `StatesPtsBoundedAt K` Preservation (`576 ≤ K`) -/

/-- Point-count bound (`≤ K` `GF16` elements per polynomial) on a runtime `PolyEncoder`. -/
def EncPtsBoundedAt (K : Nat) (enc : PolyEncoder) : Prop :=
  ∀ pts, enc.s = .points pts → ∀ pt ∈ pts, pt.value.length ≤ K

/-- Point-count bound across runtime `States` variants, paired with `ek.length = 1152` on `.keysSampled`.
-/
def StatesPtsBoundedAt {F : ShaCompress} (K : Nat) : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysUnsampled _ => True
  | .keysSampled s => EncPtsBoundedAt K s.sending_hdr ∧ s.uc.ek.length = 1152
  | .headerSent s => EncPtsBoundedAt K s.sending_ek
  | .ct1Received s => EncPtsBoundedAt K s.sending_ek
  | .ekSentCt1Received _ => True
  | .noHeaderReceived _ => True
  | .headerReceived _ => True
  | .ct1Sampled s => EncPtsBoundedAt K s.sending_ct1
  | .ekReceivedCt1Sampled s => EncPtsBoundedAt K s.sending_ct1
  | .ct1Acknowledged _ => True
  | .ct2Sampled s => EncPtsBoundedAt K s.sending_ct2

private theorem decodePbPointsTotal_len_and_bound_at {K : Nat} :
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
      obtain ⟨hlen_tail, hpt_tail⟩ := decodePbPointsTotal_len_and_bound_at rest tail hrest
        (fun b hb => hbound b (List.mem_cons_of_mem bs hb))
      refine ⟨by simp [hlen_tail], ?_⟩
      intro pt hpt
      rcases List.mem_cons.mp hpt with rfl | hmem
      · have hlen := (bytesToGF16List_eq_ok bs heven).2
        have hbs := hbound bs (List.mem_cons_self ..)
        change (bytesToGF16ListTotal bs).length ≤ K
        omega
      · exact hpt_tail pt hmem

private theorem flatMap_u16_len_at :
    ∀ cs : List GF16, (cs.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * cs.length
  | [] => rfl
  | _ :: cs => by
    simp only [List.flatMap_cons, List.length_append, flatMap_u16_len_at cs, List.length_cons]
    have h2 : ∀ v, (u16ToBeBytes v).length = 2 := fun _ => rfl
    rw [h2]; omega

theorem validEncPbPtsAt_of_encPtsBoundedAt {K : Nat} {enc : PolyEncoder}
    (h : EncPtsBoundedAt K enc) :
    ValidEncPbPtsAt K (protoPolyEncoderToPb enc.intoPb) := by
  unfold ValidEncPbPtsAt PolyEncoder.intoPb protoPolyEncoderToPb
  cases hs : enc.s with
  | points pts =>
    dsimp only
    intro bs hbs
    rcases List.mem_map.mp hbs with ⟨pt, hpt, rfl⟩
    rw [flatMap_u16_len_at]
    have hle := h pts hs pt hpt
    omega
  | polys _ =>
    dsimp only
    intro _ hbs; nomatch hbs

theorem encPtsBoundedAt_of_encoderFromPb {K : Nat} {opt : Option PolynomialEncoder}
    {enc : PolyEncoder} (hv : ValidOptEncPbPtsAt K opt)
    (h : encoderFromPbStateDecode spqrPolyApi opt = .ok enc) :
    EncPtsBoundedAt K enc := by
  cases opt with
  | none => contradiction
  | some pb =>
    dsimp only [ValidOptEncPbPtsAt, ValidEncPbPtsAt] at hv
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
              obtain ⟨_, hK⟩ := decodePbPointsTotal_len_and_bound_at (K := K) pb.pts out hd hv
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

theorem encPtsBoundedAt_of_expectEncodeBytes_le {K : Nat} {site : String} {msg : Bytes}
    {enc : PolyEncoder} (hmsg : msg.length ≤ 2 * K)
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    EncPtsBoundedAt K enc := by
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
    have hinit_len : (List.replicate NUM_POLYS ({ value := [] } : Point)).length = 16 := rfl
    intro pts hpts
    cases hpts
    intro pt hpt
    have hle := distributeMsgChunksTotal_value_length_le msg 0
      (List.replicate NUM_POLYS { value := [] }) heven hinit_len
      (fun p hp => by rcases List.mem_replicate.mp hp with ⟨_, rfl⟩; decide) pt hpt
    omega

private theorem encPtsBoundedAt_pointAt {K : Nat} {self self' : PolyEncoder} {poly idx : Nat}
    {val : GF16} (hv : EncPtsBoundedAt K self) (h : self.pointAt poly idx = .ok (self', val)) :
    EncPtsBoundedAt K self' := by
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

private theorem encPtsBoundedAt_chunkAtLoop {K : Nat} (idx : BitVec 16) :
    ∀ (i rem : Nat) (self self' : PolyEncoder) (out : List.Vector (BitVec 8) (2 * rem)),
      EncPtsBoundedAt K self →
      PolyEncoder.chunkAtLoop idx i rem self = .ok (self', out) →
      EncPtsBoundedAt K self'
  | _, 0, self, self', _, hv, h => by
    simp only [PolyEncoder.chunkAtLoop, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ hv
  | i, rem + 1, self, self', out, hv, h => by
    simp only [PolyEncoder.chunkAtLoop] at h
    rcases except_bind_eq_ok h with ⟨⟨s1, p⟩, hp, h1⟩
    rcases except_bind_eq_ok h1 with ⟨⟨s2, tail⟩, htail, h2⟩
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    exact encPtsBoundedAt_chunkAtLoop idx (i + 1) rem s1 s2 tail
      (encPtsBoundedAt_pointAt hv hp) htail

theorem encPtsBoundedAt_of_nextChunk {K : Nat} {enc enc' : PolyEncoder} {chunk : Chunk}
    (hv : EncPtsBoundedAt K enc)
    (h : (liftM (spqrPolyApi.next_chunk enc) :
      Except StatesPanic (spqrPolyApi.PolyEncoder × spqrPolyApi.Chunk)) = .ok (enc', chunk)) :
    EncPtsBoundedAt K enc' := by
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
    have hb := encPtsBoundedAt_chunkAtLoop (enc.idx.setWidth 16) 0 16 enc s2 data hv hloop
    intro pts hpts
    exact hb pts hpts

theorem validV1PtsAt_states_into_pb {F : ShaCompress} {K : Nat}
    {st : States spqrPolyApi (spqrAuthApi F)} (h : StatesPtsBoundedAt K st) :
    ValidV1PtsAt K st.into_pb := by
  cases st with
  | keysUnsampled _ => trivial
  | keysSampled s => exact validEncPbPtsAt_of_encPtsBoundedAt h.1
  | headerSent s => exact validEncPbPtsAt_of_encPtsBoundedAt h
  | ct1Received s => exact validEncPbPtsAt_of_encPtsBoundedAt h
  | ekSentCt1Received _ => trivial
  | noHeaderReceived _ => trivial
  | headerReceived _ => trivial
  | ct1Sampled s => exact validEncPbPtsAt_of_encPtsBoundedAt h
  | ekReceivedCt1Sampled s => exact validEncPbPtsAt_of_encPtsBoundedAt h
  | ct1Acknowledged _ => trivial
  | ct2Sampled s => exact validEncPbPtsAt_of_encPtsBoundedAt h

private theorem ucHeaderSent_from_pb_ek_len {F : ShaCompress}
    {pb : V1State.Unchunked.HeaderSent}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent (spqrAuthApi F)}
    (h : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.from_pb
      (spqrAuthApi F) pb = .ok uc) :
    uc.ek.length = 1152 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.from_pb at h
  split_ifs at h with hlen
  cases hpb : pb.auth with
  | none => rw [hpb] at h; contradiction
  | some a =>
    rw [hpb] at h
    have hinj := Except.ok.inj h; subst hinj
    have hek : (pb.ek.length == ENCAPSULATION_KEY_SIZE) = true :=
      (Bool.and_eq_true _ _).mp hlen |>.2
    simpa [ENCAPSULATION_KEY_SIZE] using beq_iff_eq.mp hek

theorem statesPtsBoundedAt_of_from_pb {F : ShaCompress} {K : Nat} {pb : V1State}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (hv : ValidV1PtsAt K pb) (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st) :
    StatesPtsBoundedAt K st := by
  unfold States.from_pb at h
  unfold ValidV1PtsAt at hv
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
        rcases except_bind_eq_ok hfp with ⟨uc0, huc0, hfp2⟩
        rcases except_bind_eq_ok hfp2 with ⟨enc, henc, hfp3⟩
        have hinj2 := Except.ok.inj hfp3; subst hinj2
        exact ⟨encPtsBoundedAt_of_encoderFromPb hv henc, ucHeaderSent_from_pb_ek_len huc0⟩
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
            exact encPtsBoundedAt_of_encoderFromPb hv henc
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
        exact encPtsBoundedAt_of_encoderFromPb hv henc
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
        exact encPtsBoundedAt_of_encoderFromPb hv henc
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
        exact encPtsBoundedAt_of_encoderFromPb hv henc
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
        exact encPtsBoundedAt_of_encoderFromPb hv henc

private theorem liftSpqrPanic_eq_ok_l {α : Type} {r : Except SpqrPanic α} {v : α}
    (h : liftSpqrPanic r = .ok v) : r = .ok v := by
  cases r <;> simp [liftSpqrPanic] at h; subst h; rfl

private theorem auth_macHdr_len {F : ShaCompress} {auth : Authenticator} {ep : Epoch}
    {hdr mac : Bytes}
    (h : (liftM ((spqrAuthApi F).mac_hdr auth ep hdr) : Except StatesPanic Bytes) = .ok mac) :
    mac.length = 32 := by
  change liftSpqrPanic (auth.macHdr F ep hdr) = .ok mac at h
  have hm := liftSpqrPanic_eq_ok_l h
  unfold Authenticator.macHdr at hm
  dsimp only at hm
  split_ifs at hm
  have hinj := Except.ok.inj hm; subst hinj
  exact Authenticator.length_macHdrUnchecked F auth ep hdr

private theorem auth_macCt_len {F : ShaCompress} {auth : Authenticator} {ep : Epoch}
    {ct mac : Bytes}
    (h : (liftM ((spqrAuthApi F).mac_ct auth ep ct) : Except StatesPanic Bytes) = .ok mac) :
    mac.length = 32 := by
  change liftSpqrPanic (auth.macCt F ep ct) = .ok mac at h
  have hm := liftSpqrPanic_eq_ok_l h
  unfold Authenticator.macCt at hm
  dsimp only at hm
  split_ifs at hm
  have hinj := Except.ok.inj hm; subst hinj
  exact Authenticator.length_macCtUnchecked F auth ep ct

private theorem ucSendHeader_lengths {F : ShaCompress} {mlk : MlKem}
    {self : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled (spqrAuthApi F)}
    {tape tape' : Bytes}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent (spqrAuthApi F)}
    {hdr mac : Bytes}
    (h : self.send_header mlk tape = .ok (uc, hdr, mac, tape')) :
    uc.ek.length = 1152 ∧ (hdr ++ mac).length = 96 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.send_header at h
  rcases except_bind_eq_ok h with ⟨⟨keys, tape1⟩, hgen, h1⟩
  rcases except_bind_eq_ok h1 with ⟨mac', hmac, h2⟩
  have hinj := Except.ok.inj h2
  have huc := (Prod.mk.inj hinj).1
  have hrest := (Prod.mk.inj hinj).2
  have hhdr := (Prod.mk.inj hrest).1
  have hmac_eq := (Prod.mk.inj (Prod.mk.inj hrest).2).1
  subst huc; subst hhdr; subst hmac_eq
  obtain ⟨hek, _, hhdr_len⟩ := generate_lengths hgen
  have hmac_len := auth_macHdr_len hmac
  refine ⟨hek, ?_⟩
  rw [List.length_append, hhdr_len, hmac_len]

private theorem ucSendCt1_length {F : ShaCompress} {mlk : MlKem}
    {self : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived (spqrAuthApi F)}
    {tape tape' : Bytes}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {ct1 : Bytes} {es : EpochSecret}
    (h : self.send_ct1 mlk tape = .ok (uc, ct1, es, tape')) :
    ct1.length = 960 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.send_ct1 at h
  rcases except_bind_eq_ok h with ⟨⟨⟨ct1', es1, ss⟩, tape1⟩, henc1, h1⟩
  have hinj := Except.ok.inj h1
  have hct1 := (Prod.mk.inj (Prod.mk.inj hinj).2).1
  subst hct1
  exact (encaps1_lengths henc1).1

private theorem encaps2_length {mlk : MlKem} {ek es ct2 : Bytes}
    (h : encaps2 mlk ek es = .ok ct2) : ct2.length = 128 := by
  unfold encaps2 at h
  rcases except_bind_eq_ok h with ⟨maybeFix, _, h1⟩
  dsimp only at h1
  cases hb1 : bytesToVector? ENCAPSULATION_STATE_SIZE (maybeFix.getD es) with
  | none => rw [hb1] at h1; contradiction
  | some esVec =>
    rw [hb1] at h1
    cases hb2 : bytesToVector? ENCAPSULATION_KEY_SIZE ek with
    | none => rw [hb2] at h1; contradiction
    | some ekVec =>
      rw [hb2] at h1; dsimp only at h1
      have hinj := Except.ok.inj h1; subst hinj
      exact List.Vector.toList_length _

private theorem ucSendCt2_lengths {F : ShaCompress} {mlk : MlKem}
    {self : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent (spqrAuthApi F)}
    {ct2 mac : Bytes}
    (h : self.send_ct2 mlk = .ok (uc, ct2, mac)) :
    (ct2 ++ mac).length = 160 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at h
  rcases except_bind_eq_ok h with ⟨ct2', hct2, h1⟩
  rcases except_bind_eq_ok h1 with ⟨mac', hmac, h2⟩
  have hinj := Except.ok.inj h2
  have hct2_eq := (Prod.mk.inj (Prod.mk.inj hinj).2).1
  have hmac_eq := (Prod.mk.inj (Prod.mk.inj hinj).2).2
  subst hct2_eq; subst hmac_eq
  have hlen1 := encaps2_length hct2
  have hlen2 := auth_macCt_len hmac
  rw [List.length_append, hlen1, hlen2]

theorem statesPtsBoundedAt_of_send {F : ShaCompress} {mlk : MlKem} {K : Nat} (hK : 576 ≤ K)
    {self : States spqrPolyApi (spqrAuthApi F)} {tape tape' : Bytes}
    {sendOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hv : StatesPtsBoundedAt K self) (h : self.send mlk tape = .ok (sendOut, tape')) :
    StatesPtsBoundedAt K sendOut.state := by
  unfold States.send at h
  cases self with
  | keysUnsampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _, _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.send_hdr_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨uc, toSend, mac, _⟩, hsh, h1b⟩
    dsimp only at h1b
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩
    rcases except_bind_eq_ok h1c with ⟨⟨enc1, _⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq
    obtain ⟨hek, h96⟩ := ucSendHeader_lengths hsh
    exact ⟨encPtsBoundedAt_of_nextChunk
      (encPtsBoundedAt_of_expectEncodeBytes_le (by omega) henc0) hnext, hek⟩
  | keysSampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.send_hdr_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact ⟨encPtsBoundedAt_of_nextChunk hv.1 hnext, hv.2⟩
  | headerSent state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.send_ek_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBoundedAt_of_nextChunk hv hnext
  | ct1Received state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.send_ek_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBoundedAt_of_nextChunk hv hnext
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
    rcases except_bind_eq_ok h1 with ⟨⟨_, ct1, _, _⟩, hsc1, h1b⟩
    dsimp only at h1b
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩
    rcases except_bind_eq_ok h1c with ⟨⟨enc1, _⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq
    have h960 := ucSendCt1_length hsc1
    exact encPtsBoundedAt_of_nextChunk
      (encPtsBoundedAt_of_expectEncodeBytes_le (by omega) henc0) hnext
  | ct1Sampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.send_ct1_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBoundedAt_of_nextChunk hv hnext
  | ekReceivedCt1Sampled state =>
    dsimp only at h
    rcases except_bind_eq_ok h with ⟨⟨state', _⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at h1
    dsimp only at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, _⟩, hnext, h1b⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    exact encPtsBoundedAt_of_nextChunk hv hnext
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
    exact encPtsBoundedAt_of_nextChunk hv hnext

theorem statesPtsBoundedAt_of_recv {F : ShaCompress} {mlk : MlKem} {K : Nat} (hK : 576 ≤ K)
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hv : StatesPtsBoundedAt K self) (h : self.recv mlk msg = .ok recvOut) :
    StatesPtsBoundedAt K recvOut.state := by
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
      have hek_len : state.uc.send_ek.2.length = 1152 := hv.2
      exact encPtsBoundedAt_of_expectEncodeBytes_le (by omega) henc0
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
      · rcases except_bind_eq_ok h1d with ⟨⟨_, ct2, mac⟩, hsct2, h1e⟩
        dsimp only at h1e
        rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩
        rw [statesResult_ofPanic_eq_ok] at hsct2 henc2
        unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder at henc2
        have hres := Except.ok.inj h1f; subst hres
        have hinj := Except.ok.inj h2; subst hinj
        have h160 := ucSendCt2_lengths hsct2
        exact encPtsBoundedAt_of_expectEncodeBytes_le (by omega) henc2
      · have hres := Except.ok.inj h1d; subst hres
        have hinj := Except.ok.inj h2; subst hinj; exact hv
  | ekReceivedCt1Sampled state =>
    dsimp only at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact hv)
    have hack_ok : ∀ s', StatesResult.ofPanic (state.recv_ct1_ack mlk msg.epoch) = .ok s' →
        EncPtsBoundedAt K s'.sending_ct2 := by
      intro s' h1
      rw [statesResult_ofPanic_eq_ok] at h1
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h1
      dsimp only at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨⟨_, ct2, mac⟩, hsct2, h1b⟩
      dsimp only at h1b
      rcases except_bind_eq_ok h1b with ⟨sendingCt2, henc2, h1c⟩
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder at henc2
      have hs' := Except.ok.inj h1c; subst hs'
      have h160 := ucSendCt2_lengths hsct2
      exact encPtsBoundedAt_of_expectEncodeBytes_le (by omega) henc2
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
      rcases except_bind_eq_ok h1d with ⟨⟨_, ct2, mac⟩, hsct2, h1e⟩
      dsimp only at h1e
      rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩
      rw [statesResult_ofPanic_eq_ok] at hsct2 henc2
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder at henc2
      have hres := Except.ok.inj h1f; subst hres
      have hinj := Except.ok.inj h2; subst hinj
      have h160 := ucSendCt2_lengths hsct2
      exact encPtsBoundedAt_of_expectEncodeBytes_le (by omega) henc2
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

/-! ## `ChainParamsPB` Domain Bounds (`ValidChainParamsPB`, `ValidChainParams`) -/

/-- SPQR `ChainParamsPB` domain bound (`maxJump ≤ 25,000` and `maxOooKeys ≤ 2,000`). -/
def ValidChainParamsPB (p : ChainParamsPB) : Prop :=
  p.maxJumpOrDefault.toNat ≤ 25000 ∧ p.maxOooKeysOrDefault.toNat ≤ 2000

theorem validChainParamsPB_trimSize_le {p : ChainParamsPB} (h : ValidChainParamsPB p) :
    p.trimSize ≤ 2201 := by
  unfold ChainParamsPB.trimSize
  dsimp only
  have h2 := h.2
  omega

theorem validChainParamsPB_default : ValidChainParamsPB ChainParams.default.intoPb := by
  unfold ValidChainParamsPB
  decide

def ValidChainPBParams (pb : ChainPB) : Prop :=
  ∀ p, pb.params = some p → ValidChainParamsPB p

def ValidVNParams (vn : VersionNegotiationPB) : Prop :=
  ∀ p, vn.chainParams = some p → ValidChainParamsPB p

/-- `ValidChainParamsPB` lifted across both `pq.chain` and `pq.versionNegotiation`. -/
def ValidPqChainParams (pq : PqRatchetState) : Prop :=
  (∀ c, pq.chain = some c → ValidChainPBParams c) ∧
    (∀ vn, pq.versionNegotiation = some vn → ValidVNParams vn)

/-- `ChainParamsPB` bound on serialized SPQR state bytes. -/
def ValidChainParams (stBytes : Bytes) : Prop :=
  match spqrDecodeState stBytes with
  | .error _ => True
  | .ok pq => ValidPqChainParams pq

theorem chainNew_params_eq {hkdf : HkdfFn} {k : Bytes} {dir : Direction} {params : ChainParamsPB}
    {c : Chain} (h : Chain.new hkdf k dir params = .ok c) :
    c.params = params := by
  unfold Chain.new at h
  have hinj := Except.ok.inj h
  subst hinj; rfl

theorem validChainParamsPB_of_chainFromPb {pb : ChainPB} {c : Chain}
    (hv : ValidChainPBParams pb) (h : Chain.fromPb pb = .ok c) :
    ValidChainParamsPB c.params := by
  unfold Chain.fromPb at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hd : Direction.fromI32? pb.direction with
  | none => rw [hd] at h; contradiction
  | some d =>
    rw [hd] at h; dsimp only at h
    cases hl : Chain.linksFromPb pb.links with
    | error _ => rw [hl] at h; contradiction
    | ok links =>
      rw [hl] at h; dsimp only at h
      cases hpb : pb.params with
      | none => rw [hpb] at h; contradiction
      | some p =>
        rw [hpb] at h; dsimp only at h
        have hc_eq := Except.ok.inj h; subst hc_eq
        exact hv p hpb

theorem validChainParamsPB_of_chainFromVN {hkdf : HkdfFn} {vn : VersionNegotiationPB} {c : Chain}
    (hv : ValidVNParams vn) (h : chainFromVersionNegotiation hkdf vn = .ok c) :
    ValidChainParamsPB c.params := by
  unfold chainFromVersionNegotiation at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hd : Direction.fromI32? vn.direction with
  | none => rw [hd] at h; contradiction
  | some d =>
    rw [hd] at h; dsimp only at h
    cases hvn : vn.chainParams with
    | none => rw [hvn] at h; contradiction
    | some p =>
      rw [hvn] at h; dsimp only at h
      rw [chainNew_params_eq h]
      exact hv p hvn

theorem validChainParamsPB_of_chainFrom {hkdf : HkdfFn} {pb? : Option ChainPB}
    {vn? : Option VersionNegotiationPB} {c : Chain}
    (hpb : ∀ pb, pb? = some pb → ValidChainPBParams pb)
    (hvn : ∀ vn, vn? = some vn → ValidVNParams vn)
    (h : chainFrom hkdf pb? vn? = .ok c) :
    ValidChainParamsPB c.params := by
  unfold chainFrom at h
  cases pb? with
  | some pb => exact validChainParamsPB_of_chainFromPb (hpb pb rfl) h
  | none =>
    cases vn? with
    | none => contradiction
    | some vn => exact validChainParamsPB_of_chainFromVN (hvn vn rfl) h

theorem validChainParamsPB_of_chainFrom_pq {hkdf : HkdfFn} {pq : PqRatchetState} {c : Chain}
    (hv : ValidPqChainParams pq)
    (h : chainFrom hkdf pq.chain pq.versionNegotiation = .ok c) :
    ValidChainParamsPB c.params :=
  validChainParamsPB_of_chainFrom hv.1 hv.2 h

theorem chainAddEpoch_params_eq {hkdf : HkdfFn} {self c' : Chain} {es : EpochSecret}
    (h : self.addEpoch hkdf es = .ok c') :
    c'.params = self.params := by
  unfold Chain.addEpoch at h
  split_ifs at h
  have hinj := Except.ok.inj h
  subst hinj; rfl

theorem chainSendKey_params_eq {hkdf : HkdfFn} {self c' : Chain} {ep : Epoch}
    {out : BitVec 32 × Bytes}
    (h : self.sendKey hkdf ep = .ok (c', out)) :
    c'.params = self.params := by
  unfold Chain.sendKey at h
  split_ifs at h <;>
  · rcases except_bind_eq_ok h with ⟨epochIndex0, _, h1⟩
    dsimp only at h1
    split at h1
    · contradiction
    · rcases except_bind_eq_ok h1 with ⟨⟨send', out'⟩, _, h2⟩
      dsimp only at h2
      have hinj := (Prod.mk.inj (Except.ok.inj h2)).1
      subst hinj
      rfl

theorem chainRecvKey_params_eq {hkdf : HkdfFn} {self c' : Chain} {ep : Epoch}
    {idx : BitVec 32} {out : Bytes}
    (h : self.recvKey hkdf ep idx = .ok (c', out)) :
    c'.params = self.params := by
  unfold Chain.recvKey at h
  by_cases h0 : (ep == 0#64 && idx == 0#32) = true
  · simp only [h0, ↓reduceIte] at h
    have hinj := (Prod.mk.inj (Except.ok.inj h)).1
    subst hinj; rfl
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    rcases except_bind_eq_ok h with ⟨epochIndex, _, h1⟩
    cases hlink : self.links[epochIndex]? with
    | none => rw [hlink] at h1; contradiction
    | some link =>
      rw [hlink] at h1; dsimp only at h1
      rcases except_bind_eq_ok h1 with ⟨⟨recv', out'⟩, _, h2⟩
      have hinj := (Prod.mk.inj (Except.ok.inj h2)).1
      subst hinj; rfl

theorem validChainPBParams_intoPb {c : Chain} (h : ValidChainParamsPB c.params) :
    ValidChainPBParams c.intoPb := by
  intro p hp
  unfold Chain.intoPb at hp
  dsimp only at hp
  have hinj := Option.some.inj hp
  subst hinj
  exact h

end LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
