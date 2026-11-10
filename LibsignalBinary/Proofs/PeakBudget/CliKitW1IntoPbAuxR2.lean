/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
import LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.StatesPb
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.BraidCodec
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopRecv
import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TopSend
import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync

/-!
# Guarded-Tight `<States>::into_pb` Leaf Inclusions

**Checked by Lean.**

Proves the 11-arm tight envelope inclusion `StatesIntoPbExactEnv g evs → StatesIntoPbTightEnv evs`
(`SpqrTightEvs 42 376193 2400`) under `ckx2_StatesIntoPbTightDom g.st`, and lifts `TopStateTight`
and `SpqrStateTight640` across `spqrDecodeState` + `States.from_pb`, `States.recv`, and `States.send`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1IntoPbAuxR2

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Message MlKem PolyDecoder PolyEncoder PqRatchetState States V1Recv V1Send V1State
   pbToPqRatchetState spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt
  (Ct1Acknowledged Ct1Sampled Ct2Sampled EkReceivedCt1Sampled HeaderReceived NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk
  (Ct1Received EkSentCt1Received HeaderSent KeysSampled)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState spqrDecodeState)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1Sync.Codec (spqrDecodeState_encodeState)
open CryptoVerification.SpqrV1Sync.Erasure (msgPoints)
open CryptoVerification.SpqrV1Sync.SendTotal
  (BOkTight DecWFTight EncWF isEkSide st_bCodec st_bRecvCt_tight st_bRecvEk_tight
   st_bSendClosed_tight)
open CryptoVerification.SpqrV1Sync.TopSync (topPb)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrTightEvs StatesIntoPbTightEnv decoderIntoPbEnv_tight encoderIntoPbEnv_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendRodataCaps (needed_isRodata_and_le_36)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (EncPtsBoundedAt StatesPtsBoundedAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (SpqrStateTight640 TopStateTight topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (encoderIntoPbVecs)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget (KeysUnsampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part2PlacedBudget (Ct2SampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3PlacedBudget (KeysSampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part3bPlacedBudget (Ct1ReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget (NoHeaderReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bPlacedBudget (HeaderReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4cPlacedBudget (EkSentCt1ReceivedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlacedBudget (HeaderSentEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aPlacedBudget (EkReceivedCt1SampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (ct1CloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5cBudget (Ct1AcknowledgedEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (Ct1CloneAndDropEnv Ct1SampledEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
  (StatesIntoPbExactEnv StatesIntoPbVariantExactEnv)

/-! ## Structural Leaf Guard (`ckx2_StatesIntoPbTightDom`) -/

/-- Structural encoder slot-count and per-slot length cap for `<PolyEncoder>::into_pb` tight credit. -/
def ckx2_EncIntoPbTightDom (enc : PolyEncoder) : Prop :=
  (encoderIntoPbVecs enc).length ≤ 16 ∧ ∀ cs ∈ encoderIntoPbVecs enc, cs.length ≤ 640

/-- Structural decoder slot-count and per-slot length cap for `<PolyDecoder>::into_pb` tight credit. -/
def ckx2_DecIntoPbTightDom (dec : PolyDecoder) : Prop :=
  dec.pts.length ≤ 16 ∧ ∀ s ∈ dec.pts, s.vec.length ≤ 576

/-- Per-constructor structural leaf domain on `States` under which `<States>::into_pb`
satisfies `StatesIntoPbTightEnv` (`SpqrTightEvs 42 376193 2400`). -/
def ckx2_StatesIntoPbTightDom {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .keysUnsampled _ => True
  | .keysSampled s => ckx2_EncIntoPbTightDom s.sending_hdr
  | .headerSent s => ckx2_EncIntoPbTightDom s.sending_ek ∧ ckx2_DecIntoPbTightDom s.receiving_ct1
  | .ct1Received s => ckx2_EncIntoPbTightDom s.sending_ek
  | .ekSentCt1Received s => ckx2_DecIntoPbTightDom s.receiving_ct2
  | .noHeaderReceived s => ckx2_DecIntoPbTightDom s.receiving_hdr
  | .headerReceived s => ckx2_DecIntoPbTightDom s.receiving_ek
  | .ct1Sampled s =>
      s.uc.ct1.length ≤ 2400 ∧ ckx2_EncIntoPbTightDom s.sending_ct1 ∧
        ckx2_DecIntoPbTightDom s.receiving_ek
  | .ekReceivedCt1Sampled s =>
      s.uc.ct1.length ≤ 2400 ∧ ckx2_EncIntoPbTightDom s.sending_ct1
  | .ct1Acknowledged s =>
      s.uc.ct1.length ≤ 2400 ∧ ckx2_DecIntoPbTightDom s.receiving_ek
  | .ct2Sampled s => ckx2_EncIntoPbTightDom s.sending_ct2

/-! ## 11-Arm Tight Inclusion -/

private theorem ckx2_ct1CloneEvents_tight {ct1 : List (BitVec 8)} (h : ct1.length ≤ 2400) :
    SpqrTightEvs 1 9789 2400 (ct1CloneEvents ct1) := by
  unfold ct1CloneEvents
  split
  · exact SpqrTightEvs.nil 1 9789 2400
  · exact SpqrTightEvs.rustAlloc h (by decide)

private theorem ckx2_ct1CloneAndDropEnv_tight {ct1 : List (BitVec 8)} {evs : List AllocEvent}
    (h : ct1.length ≤ 2400) (hEnv : Ct1CloneAndDropEnv ct1 evs) :
    SpqrTightEvs 1 9789 2400 evs := by
  rcases hEnv with h1 | ⟨evs1, evs2, rfl, h1, h2⟩
  · rw [h1]
    exact ckx2_ct1CloneEvents_tight h
  · rw [h1]
    exact ((ckx2_ct1CloneEvents_tight h).append (SpqrTightEvs.of_freeOnly h2)).mono
      (by omega) (by omega) (by decide)

private theorem ckx2_arm11_ct2Sampled_tight {F : ShaCompress}
    {s : Ct2Sampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_EncIntoPbTightDom s.sending_ct2) (hEnv : Ct2SampledEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (encoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm10_ct1Acknowledged_tight {F : ShaCompress}
    {s : Ct1Acknowledged spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : s.uc.ct1.length ≤ 2400 ∧ ckx2_DecIntoPbTightDom s.receiving_ek)
    (hEnv : Ct1AcknowledgedEnv s evs) :
    StatesIntoPbTightEnv evs := by
  obtain ⟨evs_d1, evs_dec, rfl, hd1, hdec⟩ := hEnv
  exact (((ckx2_ct1CloneEvents_tight hDom.1).append (SpqrTightEvs.of_freeOnly hd1)).append
    (decoderIntoPbEnv_tight hDom.2.1 hDom.2.2 hdec)).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm9_ekReceivedCt1Sampled_tight {F : ShaCompress}
    {s : EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : s.uc.ct1.length ≤ 2400 ∧ ckx2_EncIntoPbTightDom s.sending_ct1)
    (hEnv : EkReceivedCt1SampledEnv s evs) :
    StatesIntoPbTightEnv evs := by
  rcases hEnv with hcd | ⟨evs_cd, evs_enc, rfl, hcd, henc⟩
  · exact (ckx2_ct1CloneAndDropEnv_tight hDom.1 hcd).mono (by decide) (by decide) (by decide)
  · exact ((ckx2_ct1CloneAndDropEnv_tight hDom.1 hcd).append
      (encoderIntoPbEnv_tight hDom.2.1 hDom.2.2 henc)).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm8_ct1Sampled_tight {F : ShaCompress}
    {s : Ct1Sampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : s.uc.ct1.length ≤ 2400 ∧ ckx2_EncIntoPbTightDom s.sending_ct1 ∧
      ckx2_DecIntoPbTightDom s.receiving_ek)
    (hEnv : Ct1SampledEnv s evs) :
    StatesIntoPbTightEnv evs := by
  rcases hEnv with hcd | ⟨evs_cd, evs_rest, rfl, hcd, hrest⟩
  · exact (ckx2_ct1CloneAndDropEnv_tight hDom.1 hcd).mono (by decide) (by decide) (by decide)
  · rcases hrest with henc | ⟨evs_enc, evs_dec, rfl, henc, hdec⟩
    · exact ((ckx2_ct1CloneAndDropEnv_tight hDom.1 hcd).append
        (encoderIntoPbEnv_tight hDom.2.1.1 hDom.2.1.2 henc)).mono
        (by decide) (by decide) (by decide)
    · exact ((ckx2_ct1CloneAndDropEnv_tight hDom.1 hcd).append
        ((encoderIntoPbEnv_tight hDom.2.1.1 hDom.2.1.2 henc).append
          (decoderIntoPbEnv_tight hDom.2.2.1 hDom.2.2.2 hdec))).mono
        (by decide) (by decide) (by decide)

private theorem ckx2_arm7_headerReceived_tight {F : ShaCompress}
    {s : HeaderReceived spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_DecIntoPbTightDom s.receiving_ek) (hEnv : HeaderReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (decoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm6_noHeaderReceived_tight {F : ShaCompress}
    {s : NoHeaderReceived spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_DecIntoPbTightDom s.receiving_hdr) (hEnv : NoHeaderReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (decoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm5_ekSentCt1Received_tight {F : ShaCompress}
    {s : EkSentCt1Received spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_DecIntoPbTightDom s.receiving_ct2) (hEnv : EkSentCt1ReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (decoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm4_ct1Received_tight {F : ShaCompress}
    {s : Ct1Received spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_EncIntoPbTightDom s.sending_ek) (hEnv : Ct1ReceivedEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (encoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm3_headerSent_tight {F : ShaCompress}
    {s : HeaderSent spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_EncIntoPbTightDom s.sending_ek ∧ ckx2_DecIntoPbTightDom s.receiving_ct1)
    (hEnv : HeaderSentEnv s evs) :
    StatesIntoPbTightEnv evs := by
  rcases hEnv with henc | ⟨evs_enc, evs_dec, rfl, henc, hdec⟩
  · exact (encoderIntoPbEnv_tight hDom.1.1 hDom.1.2 henc).mono (by decide) (by decide) (by decide)
  · exact ((encoderIntoPbEnv_tight hDom.1.1 hDom.1.2 henc).append
      (decoderIntoPbEnv_tight hDom.2.1 hDom.2.2 hdec)).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm2_keysSampled_tight {F : ShaCompress}
    {s : KeysSampled spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_EncIntoPbTightDom s.sending_hdr) (hEnv : KeysSampledEnv s evs) :
    StatesIntoPbTightEnv evs :=
  (encoderIntoPbEnv_tight hDom.1 hDom.2 hEnv).mono (by decide) (by decide) (by decide)

private theorem ckx2_arm1_keysUnsampled_tight {evs : List AllocEvent}
    (hEnv : KeysUnsampledEnv evs) :
    StatesIntoPbTightEnv evs := by
  rw [hEnv]
  exact SpqrTightEvs.nil 42 376193 2400

/-- Exact 11-arm tight inclusion on `TopClPlacedBudget.StatesIntoPbVariantExactEnv`. -/
theorem ckx2_statesIntoPbVariantExactEnv_tight {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)} {evs : List AllocEvent}
    (hDom : ckx2_StatesIntoPbTightDom st)
    (hEnv : StatesIntoPbVariantExactEnv st evs) :
    StatesIntoPbTightEnv evs := by
  cases st with
  | keysUnsampled _ => exact ckx2_arm1_keysUnsampled_tight hEnv
  | keysSampled _ => exact ckx2_arm2_keysSampled_tight hDom hEnv
  | headerSent _ => exact ckx2_arm3_headerSent_tight hDom hEnv
  | ct1Received _ => exact ckx2_arm4_ct1Received_tight hDom hEnv
  | ekSentCt1Received _ => exact ckx2_arm5_ekSentCt1Received_tight hDom hEnv
  | noHeaderReceived _ => exact ckx2_arm6_noHeaderReceived_tight hDom hEnv
  | headerReceived _ => exact ckx2_arm7_headerReceived_tight hDom hEnv
  | ct1Sampled _ => exact ckx2_arm8_ct1Sampled_tight hDom hEnv
  | ekReceivedCt1Sampled _ => exact ckx2_arm9_ekReceivedCt1Sampled_tight hDom hEnv
  | ct1Acknowledged _ => exact ckx2_arm10_ct1Acknowledged_tight hDom hEnv
  | ct2Sampled _ => exact ckx2_arm11_ct2Sampled_tight hDom hEnv

/-- Exact ghost-indexed tight inclusion on `TopClPlacedBudget.StatesIntoPbExactEnv`. -/
theorem ckx2_statesIntoPbExactEnv_tight {F : ShaCompress}
    {g : StatesIntoPbGhost F} {evs : List AllocEvent}
    (hDom : ckx2_StatesIntoPbTightDom g.st)
    (hEnv : StatesIntoPbExactEnv g evs) :
    StatesIntoPbTightEnv evs :=
  ckx2_statesIntoPbVariantExactEnv_tight hDom hEnv

/-! ## Domain Bridges from `BOkTight`, `TopStateTight`, and `SpqrStateTight640` -/

private theorem ckx2_encPtsBoundedAt_640_of_encWF {len : Nat} {enc : PolyEncoder}
    (hlen : len = 96 ∨ len = 160 ∨ len = 960 ∨ len = 1152) (hwf : EncWF len enc) :
    EncPtsBoundedAt 640 enc := by
  obtain ⟨msg, hinv, hmlen⟩ := hwf
  intro pts hpts pt hpt
  rcases hinv with hs | ⟨polys, hs, _, _⟩
  · rw [hs] at hpts
    cases hpts
    unfold msgPoints at hpt
    rcases List.mem_map.mp hpt with ⟨j, _, rfl⟩
    simp only [List.length_map, List.length_range, hmlen]
    exact Nat.le_trans (needed_isRodata_and_le_36 hlen j).2 (by decide)
  · rw [hs] at hpts
    cases hpts

private theorem ckx2_encIntoPbTightDom_of_encWF {len : Nat} {enc : PolyEncoder}
    (hlen : len = 96 ∨ len = 160 ∨ len = 960 ∨ len = 1152) (hwf : EncWF len enc) :
    ckx2_EncIntoPbTightDom enc := by
  obtain ⟨msg, hinv, hmlen⟩ := hwf
  rcases hinv with hs | ⟨polys, hs, hplen, hp⟩
  · unfold ckx2_EncIntoPbTightDom encoderIntoPbVecs
    rw [hs]
    dsimp only
    refine ⟨by simp [msgPoints], fun cs hcs => ?_⟩
    unfold msgPoints at hcs
    rw [List.mem_map] at hcs
    rcases hcs with ⟨pt, hpt, rfl⟩
    rcases List.mem_map.mp hpt with ⟨j, _, rfl⟩
    simp only [List.length_map, List.length_range, hmlen]
    exact Nat.le_trans (needed_isRodata_and_le_36 hlen j).2 (by decide)
  · unfold ckx2_EncIntoPbTightDom encoderIntoPbVecs
    rw [hs]
    dsimp only
    refine ⟨by simp [hplen], fun cs hcs => ?_⟩
    rcases List.mem_map.mp hcs with ⟨p, hp_mem, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp_mem
    rw [(hp j hj).1, hmlen]
    exact Nat.le_trans (needed_isRodata_and_le_36 hlen j).2 (by decide)

private theorem ckx2_decIntoPbTightDom_of_decWFTight {n : Nat} {d : PolyDecoder}
    (hd : DecWFTight n d) (_hn : n ≤ 576) :
    ckx2_DecIntoPbTightDom d := by
  refine ⟨Nat.le_of_eq hd.1.2.1, fun s hs => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
  let S := (d.pts[j].vec.map fun pt => pt.x.value.toNat).toFinset
  have hnec : d.necessaryPoints j ≤ 36 := by
    unfold PolyDecoder.necessaryPoints
    rw [hd.1.1]
    dsimp only
    split_ifs <;> omega
  have hsub_union :
      S ⊆ S.filter (· < d.necessaryPoints j) ∪ S.filter (d.necessaryPoints j ≤ ·) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hlt : x < d.necessaryPoints j
    · exact Or.inl ⟨hx, hlt⟩
    · exact Or.inr ⟨hx, by omega⟩
  have hsub_range : S.filter (· < d.necessaryPoints j) ⊆ Finset.range (d.necessaryPoints j) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact hx.2
  have hlt_card : (S.filter (· < d.necessaryPoints j)).card ≤ d.necessaryPoints j := by
    have hc := Finset.card_le_card hsub_range
    rwa [Finset.card_range] at hc
  have hge_card : (S.filter (d.necessaryPoints j ≤ ·)).card ≤ d.necessaryPoints j := hd.2 j hj
  have htot_card : S.card ≤
      (S.filter (· < d.necessaryPoints j)).card + (S.filter (d.necessaryPoints j ≤ ·)).card :=
    (Finset.card_le_card hsub_union).trans (Finset.card_union_le _ _)
  have hnd : (d.pts[j].vec.map fun pt => pt.x.value.toNat).Nodup := (hd.1.2.2 j hj).imp ne_of_lt
  have hlen : d.pts[j].vec.length = S.card := by
    dsimp [S]
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  omega

/-- Any `BOkTight` SPQR V1 braid state satisfies `StatesPtsBoundedAt 640`. -/
theorem ckx2_statesPtsBoundedAt_640_of_bokTight {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (hbok : BOkTight st) :
    StatesPtsBoundedAt 640 st := by
  rcases hbok with ⟨hb, _⟩
  cases st with
  | keysUnsampled _ | ekSentCt1Received _ | noHeaderReceived _
  | headerReceived _ | ct1Acknowledged _ =>
    trivial
  | keysSampled _ =>
    exact ⟨ckx2_encPtsBoundedAt_640_of_encWF (Or.inl rfl) hb.2.2, hb.2.1.2⟩
  | headerSent _ =>
    exact ckx2_encPtsBoundedAt_640_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2.1
  | ct1Received _ =>
    exact ckx2_encPtsBoundedAt_640_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2
  | ct1Sampled _ =>
    exact ckx2_encPtsBoundedAt_640_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2.1
  | ekReceivedCt1Sampled _ =>
    exact ckx2_encPtsBoundedAt_640_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2
  | ct2Sampled _ =>
    exact ckx2_encPtsBoundedAt_640_of_encWF (Or.inr (Or.inl rfl)) hb.2

/-- Any `BOkTight` SPQR V1 braid state satisfies `ckx2_StatesIntoPbTightDom`. -/
theorem ckx2_statesIntoPbTightDom_of_bokTight {F : ShaCompress}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (hbok : BOkTight st) :
    ckx2_StatesIntoPbTightDom st := by
  rcases hbok with ⟨hb, hdt⟩
  cases st with
  | keysUnsampled _ =>
    trivial
  | keysSampled _ =>
    exact ckx2_encIntoPbTightDom_of_encWF (Or.inl rfl) hb.2.2
  | headerSent _ =>
    exact ⟨ckx2_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2.1,
      ckx2_decIntoPbTightDom_of_decWFTight hdt (by decide)⟩
  | ct1Received _ =>
    exact ckx2_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inr rfl))) hb.2.2
  | ekSentCt1Received _ =>
    exact ckx2_decIntoPbTightDom_of_decWFTight hdt (by decide)
  | noHeaderReceived _ =>
    exact ckx2_decIntoPbTightDom_of_decWFTight hdt (by decide)
  | headerReceived _ =>
    exact ckx2_decIntoPbTightDom_of_decWFTight hdt (by decide)
  | ct1Sampled _ =>
    exact ⟨by rw [hb.2.1.2.2]; decide,
      ckx2_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2.1,
      ckx2_decIntoPbTightDom_of_decWFTight hdt (by decide)⟩
  | ekReceivedCt1Sampled _ =>
    exact ⟨by rw [hb.2.1.2.1]; decide,
      ckx2_encIntoPbTightDom_of_encWF (Or.inr (Or.inr (Or.inl rfl))) hb.2.2⟩
  | ct1Acknowledged _ =>
    exact ⟨by rw [hb.2.1.2.2]; decide,
      ckx2_decIntoPbTightDom_of_decWFTight hdt (by decide)⟩
  | ct2Sampled _ =>
    exact ckx2_encIntoPbTightDom_of_encWF (Or.inr (Or.inl rfl)) hb.2

/-- Decoding a `TopStateTight` serialized state into `st0` via `spqrDecodeState` + `States.from_pb`
yields `BOkTight st0` and `ckx2_StatesIntoPbTightDom st0`. -/
theorem ckx2_topStateTight_from_pb_statesIntoPbTightDom {F : ShaCompress} {K : MlKem}
    {stBytes : List (BitVec 8)} {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hTight : TopStateTight F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pre_pb)
    (hV1 : pre_pb.inner = some (.v1 pb))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0) :
    BOkTight st0 ∧ ckx2_StatesIntoPbTightDom st0 := by
  obtain ⟨_, _, hlt31⟩ := topStateTight_to_tightValid640 hTight
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨_, _, _, st, _, _, _, vn?, ch?, _, hw⟩ := hTight
  have hdec_eq : spqrDecodeState stBytes = .ok (pbToPqRatchetState (topPb st vn? ch?)) := by
    have hbeq : stBytes = encodeState (pbToPqRatchetState (topPb st vn? ch?)) := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact spqrDecodeState_encodeState (pbToPqRatchetState (topPb st vn? ch?)) hsize
  rw [hdec_eq] at hDec
  have hpre := Except.ok.inj hDec
  subst hpre
  simp only [pbToPqRatchetState, topPb, Option.map, Option.some.injEq] at hV1
  cases hV1
  have hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st :=
    st_bCodec F st hw.hbok.1
  rw [hcodec] at hFromPb
  have hst0 := Except.ok.inj hFromPb
  subst hst0
  exact ⟨hw.hbok, ckx2_statesIntoPbTightDom_of_bokTight hw.hbok⟩

theorem ckx2_spqrStateTight640_from_pb_statesIntoPbTightDom {F : ShaCompress} {K : MlKem}
    {stBytes : List (BitVec 8)} {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    (hTight : SpqrStateTight640 F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pre_pb)
    (hV1 : pre_pb.inner = some (.v1 pb))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0) :
    BOkTight st0 ∧ ckx2_StatesIntoPbTightDom st0 := by
  rcases hTight with rfl | hTop
  · have hdec0 : spqrDecodeState ([] : List (BitVec 8)) = .ok default :=
      spqrDecodeState_encodeState (default : PqRatchetState) (by decide)
    rw [hdec0] at hDec
    have hpre := Except.ok.inj hDec
    subst hpre
    cases hV1
  · exact ckx2_topStateTight_from_pb_statesIntoPbTightDom hTop hDec hV1 hFromPb

/-- Post-`States.recv` domain preservation from `TopStateTight`. -/
theorem ckx2_topStateTight_recv_statesIntoPbTightDom {F : ShaCompress} {K : MlKem}
    {stBytes : List (BitVec 8)} {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    {msg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hTight : TopStateTight F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pre_pb)
    (hV1 : pre_pb.inner = some (.v1 pb))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hRecv : States.recv K st0 msg = .ok v) :
    ckx2_StatesIntoPbTightDom v.state := by
  obtain ⟨hbok0, _⟩ := ckx2_topStateTight_from_pb_statesIntoPbTightDom hTight hDec hV1 hFromPb
  rcases v with ⟨_key, st1⟩
  have hbok1 : BOkTight st1 := by
    cases hek : isEkSide st0
    · exact st_bRecvCt_tight F K hek hbok0 hRecv
    · exact st_bRecvEk_tight F K hek hbok0 hRecv
  exact ckx2_statesIntoPbTightDom_of_bokTight hbok1

theorem ckx2_spqrStateTight640_recv_statesIntoPbTightDom {F : ShaCompress} {K : MlKem}
    {stBytes : List (BitVec 8)} {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    {msg : Message spqrPolyApi} {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hTight : SpqrStateTight640 F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pre_pb)
    (hV1 : pre_pb.inner = some (.v1 pb))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hRecv : States.recv K st0 msg = .ok v) :
    ckx2_StatesIntoPbTightDom v.state := by
  obtain ⟨hbok0, _⟩ := ckx2_spqrStateTight640_from_pb_statesIntoPbTightDom hTight hDec hV1 hFromPb
  rcases v with ⟨_key, st1⟩
  have hbok1 : BOkTight st1 := by
    cases hek : isEkSide st0
    · exact st_bRecvCt_tight F K hek hbok0 hRecv
    · exact st_bRecvEk_tight F K hek hbok0 hRecv
  exact ckx2_statesIntoPbTightDom_of_bokTight hbok1

/-- Post-`States.send` domain preservation from `TopStateTight`. -/
theorem ckx2_topStateTight_send_statesIntoPbTightDom {F : ShaCompress} {K : MlKem}
    {stBytes : List (BitVec 8)} {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    {tape tape' : List (BitVec 8)} {v : V1Send spqrPolyApi (spqrAuthApi F)}
    (hTight : TopStateTight F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pre_pb)
    (hV1 : pre_pb.inner = some (.v1 pb))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hSend : st0.send K tape = .ok (v, tape')) :
    ckx2_StatesIntoPbTightDom v.state := by
  obtain ⟨hbok0, _⟩ := ckx2_topStateTight_from_pb_statesIntoPbTightDom hTight hDec hV1 hFromPb
  rcases v with ⟨_m, _key, _st1⟩
  exact ckx2_statesIntoPbTightDom_of_bokTight (st_bSendClosed_tight F K hbok0 hSend)

theorem ckx2_spqrStateTight640_send_statesIntoPbTightDom {F : ShaCompress} {K : MlKem}
    {stBytes : List (BitVec 8)} {pre_pb : PqRatchetState} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)}
    {tape tape' : List (BitVec 8)} {v : V1Send spqrPolyApi (spqrAuthApi F)}
    (hTight : SpqrStateTight640 F K stBytes)
    (hDec : spqrDecodeState stBytes = .ok pre_pb)
    (hV1 : pre_pb.inner = some (.v1 pb))
    (hFromPb : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hSend : st0.send K tape = .ok (v, tape')) :
    ckx2_StatesIntoPbTightDom v.state := by
  obtain ⟨hbok0, _⟩ := ckx2_spqrStateTight640_from_pb_statesIntoPbTightDom hTight hDec hV1 hFromPb
  rcases v with ⟨_m, _key, _st1⟩
  exact ckx2_statesIntoPbTightDom_of_bokTight (st_bSendClosed_tight F K hbok0 hSend)

end LibsignalBinary.Proofs.PeakBudget.CliKitW1IntoPbAuxR2
