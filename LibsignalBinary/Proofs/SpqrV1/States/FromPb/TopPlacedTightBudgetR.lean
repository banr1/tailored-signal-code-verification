/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4ePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudget
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.EncoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureCode

/-!
# Guarded-Tight Relocatable Allocation Envelopes and Producers for `<States>::from_pb` (Block `333`)

Defines the structural per-field tight domain `e2b_StatesFromPbTightDom` (`ValidV1PtsAt 640`,
`auth ≤ 32` B, `enc.polys ≤ 2,560` B, `dec.pts ≤ 2,560` B), the exact 12-arm and guarded-tight
allocation envelopes (`SpqrTightEvs 56 359623 2560`), and relocatable Block `333`
`StatesFromPbPlacedOkXOfEnv` producers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedTightBudgetR

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement extract_withLsCodeLoaded libsignalSessionLib lsProg_333 lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Bytes MlKem PolynomialDecoder PolynomialEncoder PqRatchetState ProtoAuthenticator States V1State
   spqrAuthApi spqrDecodeState spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded sessionMemmoveSpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Alloc (spqrMemmoveSym)
open CryptoVerification.SpqrV1Sync.InSync (St)
open CryptoVerification.SpqrV1Sync.SendTotal (BOkTight)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (StatesFromPbTightEnv authFromPbEnv_tight ct1SentFromPbPostEnv_tight decoderFromPbEnv_tight
   ekSentCt1ReceivedFromPbPostEnv_tight encoderFromPbEnv_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (ValidOptEncPbPtsAt ValidV1PtsAt)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (StatesFromPbEnv statesFromPbPlacedRoFreeSpecXOfEnv statesFromPbPlacedSpecXOfEnv
   statesFromPbVariantPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget (StatesFromPbPlacedOkXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (KeysUnsampledFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudgetAux (KeysSampledFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsPlacedBudget (HeaderSentFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3PlacedBudgetAux (Ct1ReceivedFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4ePlacedBudget (EkSentCt1ReceivedFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5PlacedBudget (NoHeaderReceivedFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudgetAux (HeaderReceivedFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudgetAux (Ct1SampledFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux
  (EkReceivedCt1SampledFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9PlacedBudgetAux (Ct1AcknowledgedFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudgetAux (Ct2SampledFromPbEnv)

/-! ## 1. Structural Per-Field Tight Domain (`e2b_StatesFromPbTightDom`) -/

/-- `32`-byte cap on optional `ProtoAuthenticator` key slices (`rootKey`, `macKey`). -/
def e2b_ValidOptAuth32 : Option ProtoAuthenticator → Prop
  | none => True
  | some a => a.rootKey.length ≤ 32 ∧ a.macKey.length ≤ 32

/-- `2,560`-byte cap on optional `PolynomialEncoder.polys` coefficient slices. -/
def e2b_ValidOptEncPolys2560 : Option PolynomialEncoder → Prop
  | none => True
  | some enc => ∀ bs ∈ enc.polys, bs.length ≤ 2560

/-- `2,560`-byte cap on optional `PolynomialDecoder.pts` point slices. -/
def e2b_ValidOptDecPts2560 : Option PolynomialDecoder → Prop
  | none => True
  | some dec => ∀ bs ∈ dec.pts, bs.length ≤ 2560

/-- `32`-byte authenticator key cap across all 11 variants of `V1State`. -/
def e2b_ValidV1Auth32 (v1 : V1State) : Prop :=
  match v1.innerState with
  | none => True
  | some (.keysUnsampled s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.keysSampled s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.headerSent s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.ct1Received s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.ekSentCt1Received s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.noHeaderReceived s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.headerReceived s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.ct1Sampled s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.ekReceivedCt1Sampled s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.ct1Acknowledged s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth
  | some (.ct2Sampled s) =>
    match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth

/-- `2,560`-byte `.polys` slice cap across the encoder-carrying variants of `V1State`. -/
def e2b_ValidV1Polys2560 (v1 : V1State) : Prop :=
  match v1.innerState with
  | none => True
  | some (.keysUnsampled _) => True
  | some (.keysSampled s) => e2b_ValidOptEncPolys2560 s.sendingHdr
  | some (.headerSent s) => e2b_ValidOptEncPolys2560 s.sendingEk
  | some (.ct1Received s) => e2b_ValidOptEncPolys2560 s.sendingEk
  | some (.ekSentCt1Received _) => True
  | some (.noHeaderReceived _) => True
  | some (.headerReceived _) => True
  | some (.ct1Sampled s) => e2b_ValidOptEncPolys2560 s.sendingCt1
  | some (.ekReceivedCt1Sampled s) => e2b_ValidOptEncPolys2560 s.sendingCt1
  | some (.ct1Acknowledged _) => True
  | some (.ct2Sampled s) => e2b_ValidOptEncPolys2560 s.sendingCt2

/-- `2,560`-byte decoder `.pts` slice cap across the decoder-carrying variants of `V1State`. -/
def e2b_ValidV1DecPts2560 (v1 : V1State) : Prop :=
  match v1.innerState with
  | none => True
  | some (.keysUnsampled _) => True
  | some (.keysSampled _) => True
  | some (.headerSent s) => e2b_ValidOptDecPts2560 s.receivingCt1
  | some (.ct1Received _) => True
  | some (.ekSentCt1Received s) => e2b_ValidOptDecPts2560 s.receivingCt2
  | some (.noHeaderReceived s) => e2b_ValidOptDecPts2560 s.receivingHdr
  | some (.headerReceived s) => e2b_ValidOptDecPts2560 s.receivingEk
  | some (.ct1Sampled s) => e2b_ValidOptDecPts2560 s.receivingEk
  | some (.ekReceivedCt1Sampled _) => True
  | some (.ct1Acknowledged s) => e2b_ValidOptDecPts2560 s.receivingEk
  | some (.ct2Sampled _) => True

/-- Structural zero-existential tight domain on `pb : V1State` for `<States>::from_pb` (`Block 333`):
    combines `ValidV1PtsAt 640 pb` (`enc.pts ≤ 1,280` B) with `auth ≤ 32` B,
    `enc.polys ≤ 2,560` B, and `dec.pts ≤ 2,560` B. -/
def e2b_StatesFromPbTightDom (pb : V1State) : Prop :=
  ValidV1PtsAt 640 pb ∧ e2b_ValidV1Auth32 pb ∧ e2b_ValidV1Polys2560 pb ∧ e2b_ValidV1DecPts2560 pb


/-! ## 2. Exact, Guarded-Tight, & Implication-Tight Envelopes + Domain Lifts -/

/-- Exact 12-arm (`none` + 11 `V1State.InnerState` variants) allocation envelope of
    `<spqr::v1::chunked::states::States>::from_pb` (`Block 333`). -/
def e2b_StatesFromPbExactEnv (F : ShaCompress) (pb : V1State) (evs : List AllocEvent) : Prop :=
  match pb.innerState with
  | none => evs = []
  | some (.keysUnsampled s) => KeysUnsampledFromPbEnv s evs
  | some (.keysSampled s) => KeysSampledFromPbEnv s evs
  | some (.headerSent s) => HeaderSentFromPbEnv s evs
  | some (.ct1Received s) => Ct1ReceivedFromPbEnv F s evs
  | some (.ekSentCt1Received s) => EkSentCt1ReceivedFromPbEnv F s evs
  | some (.noHeaderReceived s) => NoHeaderReceivedFromPbEnv s evs
  | some (.headerReceived s) => HeaderReceivedFromPbEnv s evs
  | some (.ct1Sampled s) => Ct1SampledFromPbEnv F s evs
  | some (.ekReceivedCt1Sampled s) => EkReceivedCt1SampledFromPbEnv s evs
  | some (.ct1Acknowledged s) => Ct1AcknowledgedFromPbEnv F s evs
  | some (.ct2Sampled s) => Ct2SampledFromPbEnv s evs

/-- Domain-split guarded-tight envelope for `<States>::from_pb` (`Block 333`):
    yields `StatesFromPbTightEnv` (`SpqrTightEvs 56 359623 2560`, zero existential binders) on
    `e2b_StatesFromPbTightDom pb`, and falls back to `DefsBudget.StatesFromPbEnv pb` off-domain
    so `FitsEnv` remains satisfiable on all `pb`. -/
def e2b_StatesFromPbGuardedTightEnv (pb : V1State) (evs : List AllocEvent) : Prop :=
  (e2b_StatesFromPbTightDom pb ∧ StatesFromPbTightEnv evs) ∨
    (¬ e2b_StatesFromPbTightDom pb ∧ StatesFromPbEnv pb evs)

/-- Implication-guarded tight envelope for `<States>::from_pb` (`Block 333`). -/
def e2b_StatesFromPbImpTightEnv (pb : V1State) (evs : List AllocEvent) : Prop :=
  e2b_StatesFromPbTightDom pb → StatesFromPbTightEnv evs

private theorem e2b_validOptAuth32_of_authOk (F : ShaCompress)
    {a : CryptoVerification.LibsignalSpqrV1.Authenticator}
    (ha : CryptoVerification.SpqrV1Sync.SendTotal.AuthOk a) :
    e2b_ValidOptAuth32 (some ((spqrAuthApi F).into_pb a)) := by
  simp [e2b_ValidOptAuth32, spqrAuthApi,
    CryptoVerification.LibsignalSpqrV1.Authenticator.intoPb, ha.1, ha.2]

private theorem e2b_needed_le {len : Nat} (hlen : len ≤ 1152) (j : Nat) :
    CryptoVerification.SpqrV1Sync.Erasure.needed len j ≤ 1200 := by
  unfold CryptoVerification.SpqrV1Sync.Erasure.needed
  split <;> omega

private theorem e2b_validOptEncPolys2560_of_encWF {len : Nat}
    {enc : CryptoVerification.LibsignalSpqrV1.PolyEncoder}
    (henc : CryptoVerification.SpqrV1Sync.SendTotal.EncWF len enc) (hlen : len ≤ 1152) :
    e2b_ValidOptEncPolys2560 (some (spqrPolyApi.encoder_into_pb enc)) := by
  rcases henc with ⟨msg, henc, rfl⟩
  rcases enc with ⟨idx, s⟩
  rcases henc with hpts | ⟨polys, hpolys, _, hcoeff⟩
  · simp only at hpts
    subst hpts
    simp [e2b_ValidOptEncPolys2560, spqrPolyApi,
      CryptoVerification.LibsignalSpqrV1.protoPolyEncoderToPb,
      CryptoVerification.LibsignalSpqrV1.PolyEncoder.intoPb]
  · simp only at hpolys
    subst hpolys
    simp only [e2b_ValidOptEncPolys2560, spqrPolyApi,
      CryptoVerification.LibsignalSpqrV1.protoPolyEncoderToPb,
      CryptoVerification.LibsignalSpqrV1.PolyEncoder.intoPb]
    intro bs hbs
    rcases List.mem_map.1 hbs with ⟨p, hp, rfl⟩
    rcases List.getElem_of_mem hp with ⟨j, hj, rfl⟩
    have hcj := (hcoeff j hj).1
    have hser : (CryptoVerification.LibsignalSpqrV1.Poly.serialize polys[j]).length =
        2 * polys[j].coefficients.length :=
      CryptoVerification.SpqrV1Sync.Erasure.EncoderCodec.flatMap_u16ToBeBytes_length
        polys[j].coefficients
    have hneed := e2b_needed_le hlen j
    omega

private theorem e2b_sortedSetPt_tight_length_le {n : Nat}
    {d : CryptoVerification.LibsignalSpqrV1.PolyDecoder}
    (hd : CryptoVerification.SpqrV1Sync.SendTotal.DecWFTight n d) (hn : n ≤ 576)
    (j : Nat) (hj : j < d.pts.length) :
    d.pts[j].vec.length ≤ 72 := by
  let S := (d.pts[j].vec.map fun pt => pt.x.value.toNat).toFinset
  have hnec : d.necessaryPoints j ≤ 36 := by
    unfold CryptoVerification.LibsignalSpqrV1.PolyDecoder.necessaryPoints
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

private theorem e2b_validOptDecPts2560_of_decWFTight {n : Nat}
    {dec : CryptoVerification.LibsignalSpqrV1.PolyDecoder}
    (hdec : CryptoVerification.SpqrV1Sync.SendTotal.DecWFTight n dec) (hn : n ≤ 576) :
    e2b_ValidOptDecPts2560 (some (spqrPolyApi.decoder_into_pb dec)) := by
  simp only [e2b_ValidOptDecPts2560, spqrPolyApi,
    CryptoVerification.LibsignalSpqrV1.protoPolyDecoderToPb,
    CryptoVerification.LibsignalSpqrV1.PolyDecoder.intoPb]
  intro bs hbs
  rcases List.mem_map.1 hbs with ⟨s, hs, rfl⟩
  rcases List.getElem_of_mem hs with ⟨j, hj, rfl⟩
  have hlen := e2b_sortedSetPt_tight_length_le hdec hn j hj
  have hser :=
    CryptoVerification.SpqrV1Sync.Erasure.DecoderCodec.length_flatMap_serialize dec.pts[j].vec
  omega

/-- Any `st : St F` satisfying `BOkTight st` and `ValidV1PtsAt 640 st.into_pb` serializes to a
    `V1State` in `e2b_StatesFromPbTightDom`. -/
theorem e2b_statesFromPbTightDom_of_bokTight {F : ShaCompress} {st : St F}
    (hbok : BOkTight st) (hpts : ValidV1PtsAt 640 st.into_pb) :
    e2b_StatesFromPbTightDom st.into_pb := by
  rcases hbok with ⟨hbok, htight⟩
  refine ⟨hpts, ?_⟩
  cases st with
  | keysUnsampled s =>
    refine ⟨?_, trivial, trivial⟩
    simpa [e2b_ValidV1Auth32, States.into_pb,
      CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.into_pb,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.into_pb] using
      e2b_validOptAuth32_of_authOk F hbok
  | keysSampled s =>
    rcases hbok with ⟨ha, _, henc⟩
    refine ⟨?_, ?_, trivial⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1Polys2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.into_pb] using
        e2b_validOptEncPolys2560_of_encWF henc (by decide)
  | headerSent s =>
    rcases hbok with ⟨ha, _, henc, _⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSent.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1Polys2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.into_pb] using
        e2b_validOptEncPolys2560_of_encWF henc (by decide)
    · simpa [e2b_ValidV1DecPts2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.into_pb] using
        e2b_validOptDecPts2560_of_decWFTight htight (by decide)
  | ct1Received s =>
    rcases hbok with ⟨ha, _, henc⟩
    refine ⟨?_, ?_, trivial⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1Polys2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.into_pb] using
        e2b_validOptEncPolys2560_of_encWF henc (by decide)
  | ekSentCt1Received s =>
    rcases hbok with ⟨ha, _, _⟩
    refine ⟨?_, trivial, ?_⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1DecPts2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.into_pb] using
        e2b_validOptDecPts2560_of_decWFTight htight (by decide)
  | noHeaderReceived s =>
    rcases hbok with ⟨ha, _⟩
    refine ⟨?_, trivial, ?_⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.NoHeaderReceived.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1DecPts2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.into_pb] using
        e2b_validOptDecPts2560_of_decWFTight htight (by decide)
  | headerReceived s =>
    rcases hbok with ⟨ha, _, _⟩
    refine ⟨?_, trivial, ?_⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1DecPts2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.into_pb] using
        e2b_validOptDecPts2560_of_decWFTight htight (by decide)
  | ct1Sampled s =>
    rcases hbok with ⟨ha, _, henc, _⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1Polys2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.into_pb] using
        e2b_validOptEncPolys2560_of_encWF henc (by decide)
    · simpa [e2b_ValidV1DecPts2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.into_pb] using
        e2b_validOptDecPts2560_of_decWFTight htight (by decide)
  | ekReceivedCt1Sampled s =>
    rcases hbok with ⟨ha, _, henc⟩
    refine ⟨?_, ?_, trivial⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1Polys2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.into_pb] using
        e2b_validOptEncPolys2560_of_encWF henc (by decide)
  | ct1Acknowledged s =>
    rcases hbok with ⟨ha, _, _⟩
    refine ⟨?_, trivial, ?_⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1DecPts2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.into_pb] using
        e2b_validOptDecPts2560_of_decWFTight htight (by decide)
  | ct2Sampled s =>
    rcases hbok with ⟨ha, henc⟩
    refine ⟨?_, ?_, trivial⟩
    · simpa [e2b_ValidV1Auth32, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.into_pb,
        CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent.into_pb] using
        e2b_validOptAuth32_of_authOk F ha
    · simpa [e2b_ValidV1Polys2560, States.into_pb,
        CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.into_pb] using
        e2b_validOptEncPolys2560_of_encWF henc (by decide)

/-- Domain lift from `LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight`
    to `e2b_StatesFromPbTightDom pb` for any decoded `V1` state `pb`. -/
theorem e2b_statesFromPbTightDom_of_topStateTight {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {pre_pb : PqRatchetState} {pb : V1State}
    (hTop : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight F K stBytes)
    (hdec : spqrDecodeState stBytes = .ok pre_pb)
    (hpb : pre_pb.inner = some (.v1 pb)) :
    e2b_StatesFromPbTightDom pb := by
  have hv1_pts : ValidV1PtsAt 640 pb :=
    ((LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.topStateTight_decode_props
      hTop hdec).2.2.1 pb hpb).2
  obtain ⟨_, _, hlt31⟩ :=
    LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.topStateTight_to_tightValid640 hTop
  have hsize : stBytes.length < 2 ^ 64 := Nat.lt_trans hlt31 (by decide)
  obtain ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, hw⟩ := hTop
  have hdec_eq :
      spqrDecodeState stBytes =
        .ok (CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState
          (CryptoVerification.SpqrV1Sync.TopSync.topPb st vn? ch?)) := by
    have hbeq := hw.htop.hbytes
    rw [hbeq] at hsize ⊢
    exact CryptoVerification.SpqrV1Sync.Codec.spqrDecodeState_encodeState
      (CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState
        (CryptoVerification.SpqrV1Sync.TopSync.topPb st vn? ch?)) hsize
  rw [hdec_eq] at hdec
  have hpre := Except.ok.inj hdec
  subst hpre
  simp only [CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState,
    CryptoVerification.SpqrV1Sync.TopSync.topPb, Option.map, Option.some.injEq] at hpb
  cases hpb
  exact e2b_statesFromPbTightDom_of_bokTight hw.hbok hv1_pts

/-- Domain lift from `LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.SpqrStateTight640`
    (`stBytes = [] ∨ TopStateTight F K stBytes`) to `e2b_StatesFromPbTightDom pb` for any decoded
    `V1` state `pb` (the `stBytes = []` disjunct decodes to `inner = none` and is vacuous). -/
theorem e2b_statesFromPbTightDom_of_spqrStateTight640 {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {pre_pb : PqRatchetState} {pb : V1State}
    (hGuard : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.SpqrStateTight640 F K stBytes)
    (hdec : spqrDecodeState stBytes = .ok pre_pb)
    (hpb : pre_pb.inner = some (.v1 pb)) :
    e2b_StatesFromPbTightDom pb := by
  rcases hGuard with rfl | hTop
  · simp [CryptoVerification.LibsignalSpqrV1.spqrDecodeState,
      CryptoVerification.LibsignalSpqrV1.Proto.spqrDecodeState] at hdec
    subst hdec
    cases hpb
  · exact e2b_statesFromPbTightDom_of_topStateTight hTop hdec hpb

private theorem e2b_freeOnly_tight50 {evs : List AllocEvent} (hf : FreeOnlyEvs evs) :
    SpqrTightEvs 50 317732 2560 evs :=
  (SpqrTightEvs.of_freeOnly hf).mono (by decide) (by decide) (by decide)

private theorem e2b_authFree_tight {auth : ProtoAuthenticator} {evs_free : List AllocEvent}
    (hAuth : e2b_ValidOptAuth32 (some auth)) (hf : FreeOnlyEvs evs_free) :
    SpqrTightEvs 2 1476 32 (authFromPbEvents auth ++ evs_free) :=
  ((authFromPbEnv_tight hAuth.1 hAuth.2 rfl).append (SpqrTightEvs.of_freeOnly hf)).mono
    (by decide) (by decide) (by decide)

private theorem e2b_enc_tight {pbEnc : PolynomialEncoder} {evs : List AllocEvent}
    (hPts : ValidOptEncPbPtsAt 640 (some pbEnc))
    (hPolys : e2b_ValidOptEncPolys2560 (some pbEnc))
    (hEnv : LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget.EncoderFromPbEnv
      (CryptoVerification.LibsignalSpqrV1.pbToProtoPolyEncoder pbEnc) evs) :
    SpqrTightEvs 32 159632 2560 evs :=
  encoderFromPbEnv_tight
    (fun bs hbs => by
      simpa [CryptoVerification.LibsignalSpqrV1.pbToProtoPolyEncoder] using hPts bs hbs)
    (fun bs hbs => by
      simpa [CryptoVerification.LibsignalSpqrV1.pbToProtoPolyEncoder] using hPolys bs hbs)
    hEnv

private theorem e2b_dec_tight {pbDec : PolynomialDecoder} {evs : List AllocEvent}
    (hPts : e2b_ValidOptDecPts2560 (some pbDec))
    (hEnv : LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget.FromPbDecEnv
      (CryptoVerification.LibsignalSpqrV1.pbToProtoPolyDecoder pbDec) evs) :
    SpqrTightEvs 16 156624 2560 evs :=
  decoderFromPbEnv_tight
    (fun bs hbs => by
      simpa [CryptoVerification.LibsignalSpqrV1.pbToProtoPolyEncoder,
        CryptoVerification.LibsignalSpqrV1.pbToProtoPolyDecoder] using hPts bs hbs)
    hEnv

private theorem e2b_headerSent3348_tight50 {s : V1State.Chunked.HeaderSent} {evs : List AllocEvent}
    (hPts : ValidOptEncPbPtsAt 640 s.sendingEk)
    (hAuth : match s.uc with | none => True | some u => e2b_ValidOptAuth32 u.auth)
    (hPolys : e2b_ValidOptEncPolys2560 s.sendingEk)
    (hDec : e2b_ValidOptDecPts2560 s.receivingCt1)
    (hEnv : Variant2hsPlacedBudget.HeaderSent3348Env s evs) :
    SpqrTightEvs 50 317732 2560 evs := by
  unfold Variant2hsPlacedBudget.HeaderSent3348Env at hEnv
  cases huc : s.uc with
  | none =>
    rw [huc] at hEnv; dsimp only at hEnv
    exact e2b_freeOnly_tight50 hEnv
  | some u =>
    rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
    split at hEnv
    · cases ha : u.auth with
      | none =>
        rw [ha] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      | some auth =>
        rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
        unfold Variant2hsPlacedBudget.HeaderSent3436Env at hEnv
        cases henc : s.sendingEk with
        | none =>
          rw [henc] at hEnv; dsimp only at hEnv
          rcases hEnv with ⟨ef, hf, rfl⟩
          exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
        | some pbEnc =>
          rw [henc] at hEnv hPts hPolys; dsimp only at hEnv hPts hPolys
          rcases hEnv with ⟨ef, hf, rfl⟩ | ⟨e1, e2, rfl, ⟨ef, hf, rfl⟩, h9036⟩
          · exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
          · have h1 := e2b_authFree_tight hAuth hf
            unfold Variant2hsgPlacedBudget.HeaderSentSomeEnc9036Env at h9036
            cases hres : CryptoVerification.SpqrV1.Poly.EncoderFromPb.fromPbResult
                (CryptoVerification.LibsignalSpqrV1.pbToProtoPolyEncoder pbEnc) with
            | error _ =>
              rw [hres] at h9036; dsimp only at h9036
              exact (h1.append (e2b_enc_tight hPts hPolys h9036)).mono
                (by decide) (by decide) (by decide)
            | ok _ =>
              rw [hres] at h9036; dsimp only at h9036
              cases hrc : s.receivingCt1 with
              | none =>
                rw [hrc] at h9036; dsimp only at h9036
                exact (h1.append (e2b_enc_tight hPts hPolys h9036)).mono
                  (by decide) (by decide) (by decide)
              | some pbDec =>
                rw [hrc] at h9036 hDec; dsimp only at h9036 hDec
                rcases h9036 with he | ⟨ea, ed, rfl, hea, hed⟩
                · exact (h1.append (e2b_enc_tight hPts hPolys he)).mono
                    (by decide) (by decide) (by decide)
                · exact (h1.append ((e2b_enc_tight hPts hPolys hea).append
                    (e2b_dec_tight hDec hed))).mono (by decide) (by decide) (by decide)
    · exact e2b_freeOnly_tight50 hEnv

private theorem e2b_statesFromPbExactEnv_sub_tight50 {F : ShaCompress} {pb : V1State}
    {evs : List AllocEvent}
    (hDom : e2b_StatesFromPbTightDom pb)
    (hEnv : e2b_StatesFromPbExactEnv F pb evs) :
    SpqrTightEvs 50 317732 2560 evs := by
  rcases hDom with ⟨hPts, hAuth, hPolys, hDec⟩
  rcases pb with ⟨inner⟩
  cases inner with
  | none =>
    dsimp only [e2b_StatesFromPbExactEnv] at hEnv
    subst hEnv
    exact SpqrTightEvs.nil 50 317732 2560
  | some st =>
    cases st with
    | keysUnsampled s =>
      dsimp only [e2b_StatesFromPbExactEnv, KeysUnsampledFromPbEnv] at hEnv
      dsimp only [e2b_ValidV1Auth32] at hAuth
      cases huc : s.uc with
      | none =>
        rw [huc] at hEnv; dsimp only at hEnv
        subst hEnv
        exact SpqrTightEvs.nil 50 317732 2560
      | some u =>
        rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
        cases ha : u.auth with
        | none =>
          rw [ha] at hEnv; dsimp only at hEnv
          subst hEnv
          exact SpqrTightEvs.nil 50 317732 2560
        | some auth =>
          rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
          rcases hEnv with ⟨ef, hf, rfl⟩
          exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
    | keysSampled s =>
      dsimp only [e2b_StatesFromPbExactEnv, KeysSampledFromPbEnv] at hEnv
      dsimp only [ValidV1PtsAt] at hPts
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1Polys2560] at hPolys
      cases huc : s.uc with
      | none =>
        rw [huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      | some uc =>
        rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
        cases hva : Variant2PlacedBudgetAux.keysSampledValidAuth? uc with
        | none =>
          rw [hva] at hEnv; dsimp only at hEnv
          exact e2b_freeOnly_tight50 hEnv
        | some auth =>
          have huca : uc.auth = some auth := by
            unfold Variant2PlacedBudgetAux.keysSampledValidAuth? at hva
            split at hva
            · exact hva
            · cases hva
          rw [hva] at hEnv; dsimp only at hEnv
          rw [huca] at hAuth
          cases henc : s.sendingHdr with
          | none =>
            rw [henc] at hEnv; dsimp only at hEnv
            rcases hEnv with ⟨ef, hf, rfl⟩
            exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
          | some pbEnc =>
            rw [henc] at hEnv hPts hPolys; dsimp only at hEnv hPts hPolys
            rcases hEnv with ⟨ef, ee, hf, he, rfl⟩
            exact ((e2b_authFree_tight hAuth hf).append (e2b_enc_tight hPts hPolys he)).mono
              (by decide) (by decide) (by decide)
    | headerSent s =>
      dsimp only [e2b_StatesFromPbExactEnv, HeaderSentFromPbEnv] at hEnv
      dsimp only [ValidV1PtsAt] at hPts
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1Polys2560] at hPolys
      dsimp only [e2b_ValidV1DecPts2560] at hDec
      cases hrc : s.receivingCt1 with
      | none =>
        rw [hrc] at hEnv; dsimp only at hEnv
        exact e2b_headerSent3348_tight50 hPts hAuth hPolys hDec hEnv
      | some d =>
        rw [hrc] at hEnv; dsimp only at hEnv
        split at hEnv
        · exact e2b_headerSent3348_tight50 hPts hAuth hPolys hDec hEnv
        · exact e2b_freeOnly_tight50 hEnv
    | ct1Received s =>
      dsimp only [e2b_StatesFromPbExactEnv, Ct1ReceivedFromPbEnv] at hEnv
      dsimp only [ValidV1PtsAt] at hPts
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1Polys2560] at hPolys
      cases huc : s.uc with
      | none =>
        rw [huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      | some u =>
        rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
        have huAuth : ∀ a, u.auth = some a → a.rootKey.length ≤ 32 ∧ a.macKey.length ≤ 32 := by
          intro a ha; rw [ha] at hAuth; exact hAuth
        cases hek : LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPb
            (spqrAuthApi F) u with
        | error _ =>
          rw [hek] at hEnv; dsimp only at hEnv
          exact e2b_freeOnly_tight50 hEnv
        | ok _ =>
          rw [hek] at hEnv; dsimp only at hEnv
          cases henc : s.sendingEk with
          | none =>
            rw [henc] at hEnv; dsimp only at hEnv
            rcases hEnv with ⟨ef, hf, rfl⟩
            exact (ekSentCt1ReceivedFromPbPostEnv_tight huAuth ⟨ef, hf, rfl⟩).mono
              (by decide) (by decide) (by decide)
          | some pbEnc =>
            rw [henc] at hEnv hPts hPolys; dsimp only at hEnv hPts hPolys
            rcases hEnv with ⟨ef, ee, hf, he, rfl⟩
            exact ((ekSentCt1ReceivedFromPbPostEnv_tight huAuth ⟨ef, hf, rfl⟩).append
              (e2b_enc_tight hPts hPolys he)).mono (by decide) (by decide) (by decide)
    | ekSentCt1Received s =>
      dsimp only [e2b_StatesFromPbExactEnv, EkSentCt1ReceivedFromPbEnv] at hEnv
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1DecPts2560] at hDec
      cases hrc : s.receivingCt2 with
      | none =>
        rw [hrc] at hEnv; dsimp only at hEnv
        cases huc : s.uc with
        | none =>
          rw [huc] at hEnv; dsimp only at hEnv
          exact e2b_freeOnly_tight50 hEnv
        | some u =>
          rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
          have huAuth : ∀ a, u.auth = some a → a.rootKey.length ≤ 32 ∧ a.macKey.length ≤ 32 := by
            intro a ha; rw [ha] at hAuth; exact hAuth
          unfold Variant4ePlacedBudget.EkSent2228SomeEnv at hEnv
          cases hr : LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPb
              (spqrAuthApi F) u with
          | error _ =>
            rw [hr] at hEnv; dsimp only at hEnv
            exact (ekSentCt1ReceivedFromPbPostEnv_tight huAuth hEnv).mono
              (by decide) (by decide) (by decide)
          | ok _ =>
            rw [hr] at hEnv; dsimp only at hEnv
            exact (ekSentCt1ReceivedFromPbPostEnv_tight huAuth hEnv).mono
              (by decide) (by decide) (by decide)
      | some d =>
        rw [hrc] at hEnv hDec; dsimp only at hEnv hDec
        split at hEnv
        · cases huc : s.uc with
          | none =>
            rw [huc] at hEnv; dsimp only at hEnv
            exact e2b_freeOnly_tight50 hEnv
          | some u =>
            rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
            have huAuth : ∀ a, u.auth = some a → a.rootKey.length ≤ 32 ∧ a.macKey.length ≤ 32 := by
              intro a ha; rw [ha] at hAuth; exact hAuth
            unfold Variant4ePlacedBudget.EkSent2228SomeEnv at hEnv
            cases hr : LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ekSentCt1ReceivedFromPb
                (spqrAuthApi F) u with
            | error _ =>
              rw [hr] at hEnv; dsimp only at hEnv
              exact (ekSentCt1ReceivedFromPbPostEnv_tight huAuth hEnv).mono
                (by decide) (by decide) (by decide)
            | ok _ =>
              rw [hr] at hEnv; dsimp only at hEnv
              rcases hEnv with ⟨e1, e2, rfl, h1, h2⟩
              exact ((ekSentCt1ReceivedFromPbPostEnv_tight huAuth h1).append
                (e2b_dec_tight hDec h2)).mono (by decide) (by decide) (by decide)
        · exact e2b_freeOnly_tight50 hEnv
    | noHeaderReceived s =>
      dsimp only [e2b_StatesFromPbExactEnv, NoHeaderReceivedFromPbEnv] at hEnv
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1DecPts2560] at hDec
      cases hrc : s.receivingHdr with
      | none =>
        rw [hrc] at hEnv; dsimp only at hEnv
        cases huc : s.uc with
        | none =>
          rw [huc] at hEnv; dsimp only at hEnv
          exact e2b_freeOnly_tight50 hEnv
        | some uc =>
          rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
          cases ha : uc.auth with
          | none =>
            rw [ha] at hEnv; dsimp only at hEnv
            exact e2b_freeOnly_tight50 hEnv
          | some authPb =>
            rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
            rcases hEnv with ⟨ef, hf, rfl⟩
            exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
      | some decPb =>
        rw [hrc] at hEnv hDec; dsimp only at hEnv hDec
        split at hEnv
        · cases huc : s.uc with
          | none =>
            rw [huc] at hEnv; dsimp only at hEnv
            exact e2b_freeOnly_tight50 hEnv
          | some uc =>
            rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
            cases ha : uc.auth with
            | none =>
              rw [ha] at hEnv; dsimp only at hEnv
              exact e2b_freeOnly_tight50 hEnv
            | some authPb =>
              rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
              rcases hEnv with ⟨ef0, ed, hf0, hd, rfl⟩
              exact ((e2b_authFree_tight hAuth hf0).append (e2b_dec_tight hDec hd)).mono
                (by decide) (by decide) (by decide)
        · exact e2b_freeOnly_tight50 hEnv
    | headerReceived s =>
      dsimp only [e2b_StatesFromPbExactEnv, HeaderReceivedFromPbEnv] at hEnv
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1DecPts2560] at hDec
      cases hrc : s.receivingEk <;> cases huc : s.uc
      · rw [hrc, huc] at hEnv; dsimp only at hEnv
        subst hEnv
        exact SpqrTightEvs.nil 50 317732 2560
      · rename_i uc
        rw [hrc, huc] at hEnv; dsimp only at hEnv
        rw [huc] at hAuth; dsimp only at hAuth
        cases ha : uc.auth with
        | none =>
          rw [ha] at hEnv; dsimp only at hEnv
          exact e2b_freeOnly_tight50 hEnv
        | some authPb =>
          rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
          split at hEnv
          · rcases hEnv with ⟨ef, hf, rfl⟩
            change SpqrTightEvs 50 317732 2560 (authFromPbEvents authPb ++ ef)
            exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
          · exact e2b_freeOnly_tight50 hEnv
      · rw [hrc, huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      · rename_i decPb uc
        rw [hrc, huc] at hEnv; dsimp only at hEnv
        rw [hrc] at hDec
        rw [huc] at hAuth; dsimp only at hAuth
        cases ha : uc.auth with
        | none =>
          rw [ha] at hEnv; dsimp only at hEnv
          exact e2b_freeOnly_tight50 hEnv
        | some authPb =>
          rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
          split at hEnv
          · rcases hEnv with ⟨e1, e2, rfl, ⟨ef, hf, rfl⟩, hd⟩
            have h1 : SpqrTightEvs 2 1476 32
                (authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey ++ ef) :=
              e2b_authFree_tight hAuth hf
            exact (h1.append (e2b_dec_tight hDec hd)).mono (by decide) (by decide) (by decide)
          · exact e2b_freeOnly_tight50 hEnv
    | ct1Sampled s =>
      dsimp only [e2b_StatesFromPbExactEnv, Ct1SampledFromPbEnv] at hEnv
      dsimp only [ValidV1PtsAt] at hPts
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1Polys2560] at hPolys
      dsimp only [e2b_ValidV1DecPts2560] at hDec
      have hsub : ∀ optDec,
          (match optDec with | none => True | some d => e2b_ValidOptDecPts2560 (some d)) →
          ∀ u, s.uc = some u →
          Variant7PlacedBudgetAux.Ct1SampledUcSomeEnv F u s.sendingCt1 optDec evs →
          SpqrTightEvs 50 317732 2560 evs := by
        intro optDec hOptDec u huc hU
        rw [huc] at hAuth; dsimp only at hAuth
        have huAuth : ∀ a, u.auth = some a → a.rootKey.length ≤ 32 ∧ a.macKey.length ≤ 32 := by
          intro a ha; rw [ha] at hAuth; exact hAuth
        unfold Variant7PlacedBudgetAux.Ct1SampledUcSomeEnv at hU
        cases hc : LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ct1SentFromPb
            (spqrAuthApi F) u with
        | error _ =>
          rw [hc] at hU; dsimp only at hU
          rcases hU with ⟨e1, e2, h1, h2, rfl⟩
          exact ((ct1SentFromPbPostEnv_tight huAuth h1).append (SpqrTightEvs.of_freeOnly h2)).mono
            (by decide) (by decide) (by decide)
        | ok _ =>
          rw [hc] at hU
          cases henc : s.sendingCt1 with
          | none =>
            rw [henc] at hU; dsimp only at hU
            rcases hU with ⟨e1, e2, h1, h2, rfl⟩
            exact ((ct1SentFromPbPostEnv_tight huAuth h1).append (SpqrTightEvs.of_freeOnly h2)).mono
              (by decide) (by decide) (by decide)
          | some encPb =>
            rw [henc] at hU hPts hPolys; dsimp only at hU hPts hPolys
            cases hres : CryptoVerification.SpqrV1.Poly.EncoderFromPb.fromPbResult
                (CryptoVerification.LibsignalSpqrV1.pbToProtoPolyEncoder encPb) with
            | error _ =>
              rw [hres] at hU; dsimp only at hU
              rcases hU with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
              exact (((ct1SentFromPbPostEnv_tight huAuth h1).append
                (e2b_enc_tight hPts hPolys h2)).append (SpqrTightEvs.of_freeOnly h3)).mono
                (by decide) (by decide) (by decide)
            | ok _ =>
              rw [hres] at hU
              cases optDec with
              | none =>
                dsimp only at hU
                rcases hU with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
                exact (((ct1SentFromPbPostEnv_tight huAuth h1).append
                  (e2b_enc_tight hPts hPolys h2)).append (SpqrTightEvs.of_freeOnly h3)).mono
                  (by decide) (by decide) (by decide)
              | some decPb =>
                dsimp only at hU hOptDec
                rcases hU with ⟨e1, e2, e3, e4, h1, h2, h3, h4, rfl⟩
                exact ((((ct1SentFromPbPostEnv_tight huAuth h1).append
                  (e2b_enc_tight hPts hPolys h2)).append (e2b_dec_tight hOptDec h3)).append
                  (SpqrTightEvs.of_freeOnly h4)).mono (by decide) (by decide) (by decide)
      cases hrc : s.receivingEk <;> cases huc : s.uc
      · rw [hrc, huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      · rename_i u
        rw [hrc, huc] at hEnv; dsimp only at hEnv
        exact hsub none trivial u huc hEnv
      · rw [hrc, huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      · rename_i d u
        rw [hrc, huc] at hEnv; dsimp only at hEnv
        rw [hrc] at hDec
        split at hEnv
        · exact hsub (some d) hDec u huc hEnv
        · exact e2b_freeOnly_tight50 hEnv
    | ekReceivedCt1Sampled s =>
      dsimp only [e2b_StatesFromPbExactEnv, EkReceivedCt1SampledFromPbEnv] at hEnv
      dsimp only [ValidV1PtsAt] at hPts
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1Polys2560] at hPolys
      cases huc : s.uc with
      | none =>
        rw [huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      | some u =>
        rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
        split at hEnv
        · cases ha : u.auth with
          | none =>
            rw [ha] at hEnv; dsimp only at hEnv
            exact e2b_freeOnly_tight50 hEnv
          | some auth =>
            rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
            cases henc : s.sendingCt1 with
            | none =>
              rw [henc] at hEnv; dsimp only at hEnv
              rcases hEnv with ⟨ef, hf, rfl⟩
              exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
            | some pbEnc =>
              rw [henc] at hEnv hPts hPolys; dsimp only at hEnv hPts hPolys
              rcases hEnv with ⟨ef, ee, hf, he, rfl⟩
              exact ((e2b_authFree_tight hAuth hf).append (e2b_enc_tight hPts hPolys he)).mono
                (by decide) (by decide) (by decide)
        · exact e2b_freeOnly_tight50 hEnv
    | ct1Acknowledged s =>
      dsimp only [e2b_StatesFromPbExactEnv, Ct1AcknowledgedFromPbEnv] at hEnv
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1DecPts2560] at hDec
      have hsub : ∀ optDec,
          (match optDec with | none => True | some d => e2b_ValidOptDecPts2560 (some d)) →
          ∀ u, s.uc = some u →
          Variant9PlacedBudgetAux.Ct1AcknowledgedUcSomeEnv F u optDec evs →
          SpqrTightEvs 50 317732 2560 evs := by
        intro optDec hOptDec u huc hU
        rw [huc] at hAuth; dsimp only at hAuth
        have huAuth : ∀ a, u.auth = some a → a.rootKey.length ≤ 32 ∧ a.macKey.length ≤ 32 := by
          intro a ha; rw [ha] at hAuth; exact hAuth
        unfold Variant9PlacedBudgetAux.Ct1AcknowledgedUcSomeEnv at hU
        cases hc : LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget.ct1SentFromPb
            (spqrAuthApi F) u with
        | error _ =>
          rw [hc] at hU; dsimp only at hU
          rcases hU with ⟨e1, e2, h1, h2, rfl⟩
          exact ((ct1SentFromPbPostEnv_tight huAuth h1).append (SpqrTightEvs.of_freeOnly h2)).mono
            (by decide) (by decide) (by decide)
        | ok _ =>
          rw [hc] at hU
          cases optDec with
          | none =>
            dsimp only at hU
            rcases hU with ⟨e1, e2, h1, h2, rfl⟩
            exact ((ct1SentFromPbPostEnv_tight huAuth h1).append (SpqrTightEvs.of_freeOnly h2)).mono
              (by decide) (by decide) (by decide)
          | some d =>
            dsimp only at hU hOptDec
            rcases hU with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
            exact (((ct1SentFromPbPostEnv_tight huAuth h1).append
              (e2b_dec_tight hOptDec h2)).append (SpqrTightEvs.of_freeOnly h3)).mono
              (by decide) (by decide) (by decide)
      cases hrc : s.receivingEk <;> cases huc : s.uc
      · rw [hrc, huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      · rename_i u
        rw [hrc, huc] at hEnv; dsimp only at hEnv
        exact hsub none trivial u huc hEnv
      · rw [hrc, huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      · rename_i d u
        rw [hrc, huc] at hEnv; dsimp only at hEnv
        rw [hrc] at hDec
        split at hEnv
        · exact hsub (some d) hDec u huc hEnv
        · exact e2b_freeOnly_tight50 hEnv
    | ct2Sampled s =>
      dsimp only [e2b_StatesFromPbExactEnv, Ct2SampledFromPbEnv] at hEnv
      dsimp only [ValidV1PtsAt] at hPts
      dsimp only [e2b_ValidV1Auth32] at hAuth
      dsimp only [e2b_ValidV1Polys2560] at hPolys
      cases huc : s.uc with
      | none =>
        rw [huc] at hEnv; dsimp only at hEnv
        exact e2b_freeOnly_tight50 hEnv
      | some uc =>
        rw [huc] at hEnv hAuth; dsimp only at hEnv hAuth
        cases ha : uc.auth with
        | none =>
          rw [ha] at hEnv; dsimp only at hEnv
          exact e2b_freeOnly_tight50 hEnv
        | some auth =>
          rw [ha] at hEnv hAuth; dsimp only at hEnv hAuth
          cases henc : s.sendingCt2 with
          | none =>
            rw [henc] at hEnv; dsimp only at hEnv
            rcases hEnv with ⟨ef, hf, rfl⟩
            exact (e2b_authFree_tight hAuth hf).mono (by decide) (by decide) (by decide)
          | some pbEnc =>
            rw [henc] at hEnv hPts hPolys; dsimp only at hEnv hPts hPolys
            rcases hEnv with ⟨ef, ee, hf, he, rfl⟩
            exact ((e2b_authFree_tight hAuth hf).append (e2b_enc_tight hPts hPolys he)).mono
              (by decide) (by decide) (by decide)

/-- Under `e2b_StatesFromPbTightDom pb` (`maxOps ≥ 50`, `maxBytes ≥ 317,732`), every trace in
    `e2b_StatesFromPbExactEnv F pb` satisfies `SpqrTightEvs maxOps maxBytes 2560` (worst-case
    `(50, 317,732)` on `headerSent` / `ct1Sampled`: `≤ (2, 1,476)` auth + `≤ (32, 159,632)` encoder +
    `≤ (16, 156,624)` decoder). -/
theorem e2b_statesFromPbExactEnv_sub_tightAt {F : ShaCompress} {pb : V1State}
    {evs : List AllocEvent} {maxOps maxBytes : Nat}
    (hOps : 50 ≤ maxOps) (hBytes : 317732 ≤ maxBytes)
    (hDom : e2b_StatesFromPbTightDom pb)
    (hEnv : e2b_StatesFromPbExactEnv F pb evs) :
    SpqrTightEvs maxOps maxBytes 2560 evs :=
  (e2b_statesFromPbExactEnv_sub_tight50 hDom hEnv).mono hOps hBytes (Nat.le_refl 2560)

/-- Tight envelope inclusion into `StatesFromPbTightEnv` (`SpqrTightEvs 56 359623 2560`, leaving
    `6` ops and `41,891` B spare over the worst-case `(50, 317,732)` `headerSent`/`ct1Sampled`
    arms; see `e2b_statesFromPbExactEnv_sub_tightAt`). -/
theorem e2b_statesFromPbExactEnv_sub_tight {F : ShaCompress} {pb : V1State}
    {evs : List AllocEvent}
    (hDom : e2b_StatesFromPbTightDom pb)
    (hEnv : e2b_StatesFromPbExactEnv F pb evs) :
    StatesFromPbTightEnv evs :=
  e2b_statesFromPbExactEnv_sub_tightAt (by decide) (by decide) hDom hEnv

/-! ## 3. Relocatable `[LibsignalPlacement]` Block `333` Tight Producers -/

private theorem e2b_statesFromPbVariantPlacedSpecOfEnv_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {pb : V1State} {E₁ E₂ : List AllocEvent → Prop}
    (hsub : ∀ evs, E₁ evs → E₂ evs)
    (hok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb E₁))) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb E₂)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F pb E₁)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    dsimp only [statesFromPbVariantPlacedSpecOfEnv] at hpre0 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    refine ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1, fun evs h1 => hpre0.1.2.2.2 evs (hsub evs h1)⟩,
      hpre0.2⟩
  refine hok.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, statesFromPbVariantPlacedSpecOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hsub evs hpost.1.2⟩, hpost.2⟩
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Per-`pb` exact-envelope `subroutine_ok` for `<States>::from_pb` (`Block 333`). -/
theorem e2b_states_from_pb_branch_proof_placed_exact [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0)))
    (pb : V1State) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F pb (e2b_StatesFromPbExactEnv F pb))) := by
  have henc : EncoderFromPbPlacedOkExt M A lim ext :=
    TopPlacedBudget.encoder_from_pb_ok_of_alloc_placed hA
  have hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext :=
    TopPlacedBudget.decoder_from_pb_ok_of_alloc_placed hA hmemmove
  rcases pb with ⟨inner⟩
  cases inner with
  | none =>
    exact subroutine_ok_withLsCodeLoaded_of_plain (DefsBudget.states_from_pb_none_placed_ok_of_env rfl)
  | some st =>
    cases st with
    | keysUnsampled s =>
      exact subroutine_ok_withLsCodeLoaded_of_plain
        (Variant1bPlacedBudget.states_from_pb_keysUnsampled_placed_ok_tight hA.toPlacedBudget s)
    | keysSampled s =>
      exact Variant2PlacedBudget.states_from_pb_keysSampled_placed_ok_tight hA henc s
    | headerSent s =>
      exact Variant2hsPlacedBudget.states_from_pb_headerSent_ok_of_env_alloc_placed hA hdec s
    | ct1Received s =>
      exact Variant3PlacedBudget.states_from_pb_ct1Received_placed_ok_tight hA
        (Variant4cPlacedBudgetAux.v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok hA) henc s
    | ekSentCt1Received s =>
      exact Variant4ePlacedBudget.states_from_pb_ekSentCt1Received_ok_of_env_placed hA hdec s
    | noHeaderReceived s =>
      exact Variant5PlacedBudget.states_from_pb_noHeaderReceived_placed_ok_tight hA.toPlacedBudget hdec s
    | headerReceived s =>
      exact Variant6PlacedBudget.states_from_pb_headerReceived_ok_ext_placed_tight_fromPbHooks hA hdec s
    | ct1Sampled s =>
      exact Variant7PlacedBudget.states_from_pb_ct1Sampled_ok_ext_placed_tight hA henc hdec s
    | ekReceivedCt1Sampled s =>
      exact Variant8PlacedBudget.states_from_pb_ekReceivedCt1Sampled_ok_ext_tight_placed hA henc s
    | ct1Acknowledged s =>
      exact Variant9PlacedBudget.states_from_pb_ct1Acknowledged_ok_ext_placed_tight hA hdec s
    | ct2Sampled s =>
      exact Variant10dPlacedBudget.states_from_pb_ct2Sampled_placed_ok_tight hA henc s

/-- Pointwise tight `subroutine_ok` for `<States>::from_pb` (`Block 333`) at `StatesFromPbTightEnv`
    under `hDom : e2b_StatesFromPbTightDom pb`. -/
theorem e2b_states_from_pb_branch_proof_placed_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0)))
    {pb : V1State} (hDom : e2b_StatesFromPbTightDom pb) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F pb StatesFromPbTightEnv)) :=
  e2b_statesFromPbVariantPlacedSpecOfEnv_mono
    (fun _ hevs => e2b_statesFromPbExactEnv_sub_tight hDom hevs)
    (e2b_states_from_pb_branch_proof_placed_exact hA hmemmove pb)

/-- Top-level exact-envelope `StatesFromPbPlacedOkXOfEnv` producer for `<States>::from_pb` (`Block 333`). -/
theorem e2b_states_from_pb_ok_x_placed_exact [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    StatesFromPbPlacedOkXOfEnv M A lim F ext (e2b_StatesFromPbExactEnv F) :=
  ProofPlacedBudget.states_from_pb_okX_of_ok_ext_placed_of_env
    (ProofPlacedBudget.states_from_pb_ok_of_forall_pb_placed_of_env
      (e2b_states_from_pb_branch_proof_placed_exact hA hmemmove))

/-- Per-`pb` domain-split guarded-tight `subroutine_ok` for `<States>::from_pb` (`Block 333`),
    combining `e2b_states_from_pb_branch_proof_placed_tight` on-domain with
    `TopPlacedBudget.states_from_pb_branch_proof_placed` off-domain. -/
theorem e2b_states_from_pb_branch_proof_placed_guardedTight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0)))
    (pb : V1State) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F pb (e2b_StatesFromPbGuardedTightEnv pb))) := by
  by_cases hDom : e2b_StatesFromPbTightDom pb
  · exact e2b_statesFromPbVariantPlacedSpecOfEnv_mono
      (fun _ hevs => Or.inl ⟨hDom, hevs⟩)
      (e2b_states_from_pb_branch_proof_placed_tight hA hmemmove hDom)
  · exact e2b_statesFromPbVariantPlacedSpecOfEnv_mono
      (fun _ hevs => Or.inr ⟨hDom, hevs⟩)
      (TopPlacedBudget.states_from_pb_branch_proof_placed hA hmemmove pb)

/-- Top-level domain-split guarded-tight `StatesFromPbPlacedOkXOfEnv` producer for `<States>::from_pb`
    (`Block 333`). -/
theorem e2b_states_from_pb_ok_x_placed_guardedTight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    StatesFromPbPlacedOkXOfEnv M A lim F ext e2b_StatesFromPbGuardedTightEnv :=
  ProofPlacedBudget.states_from_pb_okX_of_ok_ext_placed_of_env
    (ProofPlacedBudget.states_from_pb_ok_of_forall_pb_placed_of_env
      (e2b_states_from_pb_branch_proof_placed_guardedTight hA hmemmove))

/-- Top-level implication-guarded tight `StatesFromPbPlacedOkXOfEnv` producer for `<States>::from_pb`
    (`Block 333`). -/
theorem e2b_states_from_pb_ok_x_placed_impTight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    StatesFromPbPlacedOkXOfEnv M A lim F ext e2b_StatesFromPbImpTightEnv :=
  ProofPlacedBudget.states_from_pb_okX_of_ok_ext_placed_of_env
    (ProofPlacedBudget.states_from_pb_ok_of_forall_pb_placed_of_env fun pb =>
      e2b_statesFromPbVariantPlacedSpecOfEnv_mono
        (fun _ hevs hDom => e2b_statesFromPbExactEnv_sub_tight hDom hevs)
        (e2b_states_from_pb_branch_proof_placed_exact hA hmemmove pb))

/-- `.rodata`-free extended-stack (`statesFromPbPlacedRoFreeSpecXOfEnv`) corollary of
    `e2b_states_from_pb_ok_x_placed_guardedTight`. -/
theorem e2b_states_from_pb_roFree_ok_x_placed_guardedTight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hmemmove : HookSat (Rust.withPanics ext) spqrMemmoveSym
      (withAllocVmPreserved (sessionMemmoveSpec 0))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (statesFromPbPlacedRoFreeSpecXOfEnv M A lim F e2b_StatesFromPbGuardedTightEnv)) :=
  ProofPlacedBudget.states_from_pb_roFree_okX_of_okX_placed_of_env
    (e2b_states_from_pb_ok_x_placed_guardedTight hA hmemmove)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopPlacedTightBudgetR
