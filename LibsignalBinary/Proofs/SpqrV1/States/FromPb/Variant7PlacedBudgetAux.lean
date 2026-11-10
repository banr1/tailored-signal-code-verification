/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7d
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget

/-!
# Budget Envelopes and Subsumption for Placed Variant 7 (`Ct1Sampled`)

Defines the exact binary allocator event envelopes `Ct1SampledUcSomeEnv` and `Ct1SampledFromPbEnv`
for Variant 7 (`InnerState.ct1Sampled`, `+1056`, Block `333`), `FitsEnv` stepping lemmas across
callee stages, and subsumption into `StatesFromPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudgetAux

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder PolyEncoder PolynomialDecoder PolynomialEncoder ProtoAuthenticator
   ProtoPolynomialDecoder ProtoPolynomialEncoder V1State
   pbToProtoPolyDecoder pbToProtoPolyEncoder spqrAuthApi)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb (v7_receivingEkPtsOk)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth
   rawUcCt1Sent rawUcCt1Sent_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecAllocEnv_imp_fromPbDecEnv
   fromPbDecLoopAllocEvents fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbAllocEnv_imp_encoderFromPbEnv
   encoderFromPbPolysInitEvents encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents
   encoderFromPbPtsLoopEvents encoderFromPbPtsSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (Ct1SentFromPbPostEnv Ct1SentFromPbPreEnv authFromPbAllocEvents
   ct1SentFromPb ct1SentFromPbAllocEvents ct1SentFromPbPostEnv_of_nil)

/-! ## 1. Exact Binary Allocation Envelopes (`Ct1SampledUcSomeEnv`, `Ct1SampledFromPbEnv`) -/

/-- Exact binary allocator event envelope for Variant 7 (`Ct1Sampled`) from `+3480` when
    `s.uc = some u` and `v7_receivingEkPtsOk s.receivingEk` holds. -/
def Ct1SampledUcSomeEnv (F : ShaCompress) (u : V1State.Unchunked.Ct1Sent)
    (optEnc : Option PolynomialEncoder) (optDec : Option PolynomialDecoder)
    (evs : List AllocEvent) : Prop :=
  match ct1SentFromPb (spqrAuthApi F) u, optEnc with
  | .ok _, some encPb =>
    match fromPbResult (pbToProtoPolyEncoder encPb), optDec with
    | .ok _, some decPb =>
      ∃ evs1 evs2 evs3 evs4,
        Ct1SentFromPbPostEnv F u evs1 ∧
        EncoderFromPbEnv (pbToProtoPolyEncoder encPb) evs2 ∧
        FromPbDecEnv (pbToProtoPolyDecoder decPb) evs3 ∧
        FreeOnlyEvs evs4 ∧
        evs = evs1 ++ evs2 ++ evs3 ++ evs4
    | _, _ =>
      ∃ evs1 evs2 evs3,
        Ct1SentFromPbPostEnv F u evs1 ∧
        EncoderFromPbEnv (pbToProtoPolyEncoder encPb) evs2 ∧
        FreeOnlyEvs evs3 ∧
        evs = evs1 ++ evs2 ++ evs3
  | _, _ =>
    ∃ evs1 evs2,
      Ct1SentFromPbPostEnv F u evs1 ∧
      FreeOnlyEvs evs2 ∧
      evs = evs1 ++ evs2

/-- Exact binary allocator event envelope for Variant 7 (`InnerState.ct1Sampled s`, `+1056`,
    Block `333`) of `<spqr::v1::chunked::states::States>::from_pb`. -/
def Ct1SampledFromPbEnv (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled) (evs : List AllocEvent) : Prop :=
  match s.receivingEk, s.uc with
  | some d, some u =>
    if d.ptsNeeded == 576#32 then
      Ct1SampledUcSomeEnv F u s.sendingCt1 (some d) evs
    else
      FreeOnlyEvs evs
  | none, some u =>
    Ct1SampledUcSomeEnv F u s.sendingCt1 none evs
  | _, none =>
    FreeOnlyEvs evs

/-! ## 2. Envelope Constructors and `FitsEnv` Stepping Lemmas -/

theorem ct1SampledFromPbEnv_of_bad_pts {F : ShaCompress}
    {s : V1State.Chunked.Ct1Sampled} {d : PolynomialDecoder}
    (hdec : s.receivingEk = some d) (hpts : (d.ptsNeeded == 576#32) = false)
    {evs : List AllocEvent} (hfree : FreeOnlyEvs evs) :
    Ct1SampledFromPbEnv F s evs := by
  unfold Ct1SampledFromPbEnv
  cases s.uc
  · simp [hfree]
  · simp [hdec, hpts, hfree]

theorem ct1SampledFromPbEnv_of_uc_none {F : ShaCompress}
    {s : V1State.Chunked.Ct1Sampled} (huc : s.uc = none)
    {evs : List AllocEvent} (hfree : FreeOnlyEvs evs) :
    Ct1SampledFromPbEnv F s evs := by
  unfold Ct1SampledFromPbEnv
  cases s.receivingEk <;> simp [huc, hfree]

theorem ct1SampledFromPbEnv_of_ucSomeEnv {F : ShaCompress}
    {s : V1State.Chunked.Ct1Sampled} {u : V1State.Unchunked.Ct1Sent}
    (hpts : v7_receivingEkPtsOk s.receivingEk) (huc : s.uc = some u)
    {evs : List AllocEvent}
    (hevs : Ct1SampledUcSomeEnv F u s.sendingCt1 s.receivingEk evs) :
    Ct1SampledFromPbEnv F s evs := by
  unfold Ct1SampledFromPbEnv v7_receivingEkPtsOk at *
  cases hdec : s.receivingEk with
  | none =>
    rw [hdec] at hevs
    simp [huc, hevs]
  | some d =>
    rw [hdec] at hpts hevs
    simp [huc, hpts, hevs]

theorem fitsEnv_ucSomeEnv_of_ct1SampledFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {s : V1State.Chunked.Ct1Sampled} {u : V1State.Unchunked.Ct1Sent}
    (hpts : v7_receivingEkPtsOk s.receivingEk) (huc : s.uc = some u)
    (hfits : FitsEnv M lim st (Ct1SampledFromPbEnv F s)) :
    FitsEnv M lim st (Ct1SampledUcSomeEnv F u s.sendingCt1 s.receivingEk) :=
  FitsEnv.mono (fun _ hevs => ct1SampledFromPbEnv_of_ucSomeEnv hpts huc hevs) hfits

theorem ct1SampledUcSomeEnv_of_uc_err {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {optEnc : Option PolynomialEncoder} {optDec : Option PolynomialDecoder} {err : _}
    (herr : ct1SentFromPb (spqrAuthApi F) u = .error err)
    {evs1 evs2 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1) (h2 : FreeOnlyEvs evs2) :
    Ct1SampledUcSomeEnv F u optEnc optDec (evs1 ++ evs2) := by
  unfold Ct1SampledUcSomeEnv
  rw [herr]
  exact ⟨evs1, evs2, h1, h2, rfl⟩

theorem ct1SampledUcSomeEnv_of_enc_none {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {optDec : Option PolynomialDecoder}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    {evs1 evs2 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1) (h2 : FreeOnlyEvs evs2) :
    Ct1SampledUcSomeEnv F u none optDec (evs1 ++ evs2) := by
  unfold Ct1SampledUcSomeEnv
  rw [hok]
  exact ⟨evs1, evs2, h1, h2, rfl⟩

theorem ct1SampledUcSomeEnv_of_enc_err {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {e : PolynomialEncoder} {optDec : Option PolynomialDecoder}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {err : _}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    (herr : fromPbResult (pbToProtoPolyEncoder e) = .error err)
    {evs1 evs2 evs3 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (h2 : EncoderFromPbEnv (pbToProtoPolyEncoder e) evs2)
    (h3 : FreeOnlyEvs evs3) :
    Ct1SampledUcSomeEnv F u (some e) optDec ((evs1 ++ evs2) ++ evs3) := by
  unfold Ct1SampledUcSomeEnv
  rw [hok]; dsimp only
  rw [herr]
  exact ⟨evs1, evs2, evs3, h1, h2, h3, by simp [List.append_assoc]⟩

theorem ct1SampledUcSomeEnv_of_dec_none {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {e : PolynomialEncoder}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {enc : PolyEncoder}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    {evs1 evs2 evs3 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (h2 : EncoderFromPbEnv (pbToProtoPolyEncoder e) evs2)
    (h3 : FreeOnlyEvs evs3) :
    Ct1SampledUcSomeEnv F u (some e) none ((evs1 ++ evs2) ++ evs3) := by
  unfold Ct1SampledUcSomeEnv
  rw [hok]; dsimp only
  rw [henc]
  exact ⟨evs1, evs2, evs3, h1, h2, h3, by simp [List.append_assoc]⟩

theorem ct1SampledUcSomeEnv_of_dec_ok {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {e : PolynomialEncoder} {d : PolynomialDecoder}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {enc : PolyEncoder}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    {evs1 evs2 evs3 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (h2 : EncoderFromPbEnv (pbToProtoPolyEncoder e) evs2)
    (h3 : FromPbDecEnv (pbToProtoPolyDecoder d) evs3) :
    Ct1SampledUcSomeEnv F u (some e) (some d) ((evs1 ++ evs2) ++ evs3) := by
  unfold Ct1SampledUcSomeEnv
  rw [hok]; dsimp only
  rw [henc]
  exact ⟨evs1, evs2, evs3, [], h1, h2, h3, FreeOnlyEvs.nil, by simp [List.append_assoc]⟩

theorem ct1SampledUcSomeEnv_of_dec_err {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {e : PolynomialEncoder} {d : PolynomialDecoder}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {enc : PolyEncoder}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    {evs1 evs2 evs3 evs4 : List AllocEvent}
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (h2 : EncoderFromPbEnv (pbToProtoPolyEncoder e) evs2)
    (h3 : FromPbDecEnv (pbToProtoPolyDecoder d) evs3)
    (h4 : FreeOnlyEvs evs4) :
    Ct1SampledUcSomeEnv F u (some e) (some d) ((evs1 ++ evs2) ++ evs3 ++ evs4) := by
  unfold Ct1SampledUcSomeEnv
  rw [hok]; dsimp only
  rw [henc]
  exact ⟨evs1, evs2, evs3, evs4, h1, h2, h3, h4, by simp [List.append_assoc]⟩

theorem fitsEnv_ct1SentPre_of_ucSomeEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {optEnc : Option PolynomialEncoder} {optDec : Option PolynomialDecoder}
    (hfits : FitsEnv M lim st (Ct1SampledUcSomeEnv F u optEnc optDec)) :
    FitsEnv M lim st (Ct1SentFromPbPreEnv F u) := by
  intro evs1 hevs1
  subst hevs1
  apply hfits
  have h1 : Ct1SentFromPbPostEnv F u (ct1SentFromPbAllocEvents F u) :=
    ct1SentFromPbPostEnv_of_nil F u
  unfold Ct1SampledUcSomeEnv
  cases hct : ct1SentFromPb (spqrAuthApi F) u with
  | error _ => exact ⟨_, [], h1, FreeOnlyEvs.nil, (List.append_nil _).symm⟩
  | ok _ =>
    cases optEnc with
    | none => exact ⟨_, [], h1, FreeOnlyEvs.nil, (List.append_nil _).symm⟩
    | some e =>
      dsimp only
      have h2 := encoderFromPbAllocEnv_imp_encoderFromPbEnv (pb := pbToProtoPolyEncoder e) (Or.inl rfl)
      cases hres : fromPbResult (pbToProtoPolyEncoder e) with
      | error _ => exact ⟨_, [], [], h1, h2, FreeOnlyEvs.nil, by simp⟩
      | ok _ =>
        cases optDec with
        | none => exact ⟨_, [], [], h1, h2, FreeOnlyEvs.nil, by simp⟩
        | some d =>
          exact ⟨_, [], [], [], h1, h2,
            fromPbDecAllocEnv_imp_fromPbDecEnv (Or.inl rfl), FreeOnlyEvs.nil, by simp⟩

theorem fitsEnv_encAlloc_step_of_ucSomeEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    (e : PolynomialEncoder) {optDec : Option PolynomialDecoder} {evs1 : List AllocEvent}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (hfits : FitsEnv M lim st (Ct1SampledUcSomeEnv F u (some e) optDec)) :
    FitsEnv M lim (M.stepEvents evs1 st) (EncoderFromPbAllocEnv (pbToProtoPolyEncoder e)) := by
  intro evs2 hevs2
  have hmem : Ct1SampledUcSomeEnv F u (some e) optDec (evs1 ++ evs2) := by
    have h2 := encoderFromPbAllocEnv_imp_encoderFromPbEnv hevs2
    unfold Ct1SampledUcSomeEnv
    rw [hok]; dsimp only
    cases hres : fromPbResult (pbToProtoPolyEncoder e) with
    | error _ => exact ⟨evs1, evs2, [], h1, h2, FreeOnlyEvs.nil, by simp⟩
    | ok _ =>
      cases optDec with
      | none => exact ⟨evs1, evs2, [], h1, h2, FreeOnlyEvs.nil, by simp⟩
      | some d =>
        exact ⟨evs1, evs2, [], [], h1, h2,
          fromPbDecAllocEnv_imp_fromPbDecEnv (Or.inl rfl), FreeOnlyEvs.nil, by simp⟩
  exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfits (evs1 ++ evs2) hmem)).2

theorem fitsEnv_decAlloc_step_of_ucSomeEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {e : PolynomialEncoder} {enc : PolyEncoder} (d : PolynomialDecoder)
    {evs1 evs2 : List AllocEvent}
    (hok : ct1SentFromPb (spqrAuthApi F) u = .ok uc)
    (henc : fromPbResult (pbToProtoPolyEncoder e) = .ok enc)
    (h1 : Ct1SentFromPbPostEnv F u evs1)
    (h2 : EncoderFromPbEnv (pbToProtoPolyEncoder e) evs2)
    (hfits : FitsEnv M lim st (Ct1SampledUcSomeEnv F u (some e) (some d))) :
    FitsEnv M lim (M.stepEvents (evs1 ++ evs2) st)
      (FromPbDecAllocEnv (pbToProtoPolyDecoder d)) := by
  intro evs3 hevs3
  have hmem : Ct1SampledUcSomeEnv F u (some e) (some d) ((evs1 ++ evs2) ++ evs3) :=
    ct1SampledUcSomeEnv_of_dec_ok hok henc h1 h2 (fromPbDecAllocEnv_imp_fromPbDecEnv hevs3)
  exact ((fitsEvents_append M lim (evs1 ++ evs2) evs3 st).mp
    (hfits ((evs1 ++ evs2) ++ evs3) hmem)).2

/-! ## 3. Wire-Length Bounds and `StatesFromPbEnv` Subsumption -/

private theorem rawAuth_le_ct1Sampled_encodeRaw
    (s : V1State.Chunked.Ct1Sampled) (u : V1State.Unchunked.Ct1Sent)
    (auth : ProtoAuthenticator) (huc : s.uc = some u) (hauth : u.auth = some auth) :
    auth.rootKey.length + auth.macKey.length ≤
      (V1State.encodeRaw { innerState := some (.ct1Sampled s) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.Ct1Sampled.encodeRaw 8#32 s
  have h1 := length_le_encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw
    rawUcCt1Sent rawUcCt1Sent_le_encodeRaw 1#32 s.uc
  rw [huc] at h1
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.Ct1Sampled.encodeRaw, optRaw, rawUcCt1Sent, rawAuth] at h0 h1 ⊢
  simp only [List.length_append, huc] at h0
  rw [hauth] at h1
  dsimp only [] at h1
  omega

private theorem sum_enc_le_polyEncoder_encodeRaw (e : PolynomialEncoder) :
    (e.pts.map List.length).sum + (e.polys.map List.length).sum ≤
      (PolynomialEncoder.encodeRaw e).length := by
  unfold PolynomialEncoder.encodeRaw
  simp only [List.length_append]
  have h1 := sum_length_le_encodeRepeatedBytes 2#32 e.pts
  have h2 := sum_length_le_encodeRepeatedBytes 3#32 e.polys
  omega

private theorem sum_enc_le_ct1Sampled_encodeRaw
    (s : V1State.Chunked.Ct1Sampled) (e : PolynomialEncoder)
    (henc : s.sendingCt1 = some e) :
    (e.pts.map List.length).sum + (e.polys.map List.length).sum ≤
      (V1State.encodeRaw { innerState := some (.ct1Sampled s) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.Ct1Sampled.encodeRaw 8#32 s
  have h1 := length_le_encodeOptMessage PolynomialEncoder.encodeRaw
    (fun m => (m.pts.map List.length).sum + (m.polys.map List.length).sum)
    sum_enc_le_polyEncoder_encodeRaw 2#32 s.sendingCt1
  rw [henc] at h1
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.Ct1Sampled.encodeRaw, optRaw] at h0 h1 ⊢
  simp only [List.length_append, henc] at h0
  omega

private theorem sum_pts_le_polyDecoder_encodeRaw (d : PolynomialDecoder) :
    (d.pts.map List.length).sum ≤ (PolynomialDecoder.encodeRaw d).length := by
  unfold PolynomialDecoder.encodeRaw
  simp only [List.length_append]
  have h1 := sum_length_le_encodeRepeatedBytes 3#32 d.pts
  omega

private theorem sum_dec_pts_le_ct1Sampled_encodeRaw
    (s : V1State.Chunked.Ct1Sampled) (d : PolynomialDecoder)
    (hdec : s.receivingEk = some d) :
    (d.pts.map List.length).sum ≤
      (V1State.encodeRaw { innerState := some (.ct1Sampled s) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.Ct1Sampled.encodeRaw 8#32 s
  have h1 := length_le_encodeOptMessage PolynomialDecoder.encodeRaw
    (fun m => (m.pts.map List.length).sum) sum_pts_le_polyDecoder_encodeRaw 3#32 s.receivingEk
  rw [hdec] at h1
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.Ct1Sampled.encodeRaw, optRaw] at h0 h1 ⊢
  simp only [List.length_append, hdec] at h0
  omega

private theorem mem_length_le_sum_map {bs : List (BitVec 8)} {pts : List (List (BitVec 8))}
    (hmem : bs ∈ pts) :
    bs.length ≤ (pts.map List.length).sum := by
  induction pts with
  | nil => nomatch hmem
  | cons x xs ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.map_cons, List.sum_cons]
    rcases hmem with rfl | hmem'
    · omega
    · have := ih hmem'; omega

private theorem takeWhile_length_le {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.takeWhile p).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.takeWhile]
    split
    · simp only [List.length_cons]; exact Nat.succ_le_succ (takeWhile_length_le p xs)
    · exact Nat.zero_le _

private theorem mem_and_pred_of_mem_takeWhile {α : Type} {p : α → Bool} {x : α} :
    ∀ {xs : List α}, x ∈ xs.takeWhile p → x ∈ xs ∧ p x = true
  | [], h => by simp [List.takeWhile] at h
  | y :: ys, h => by
    simp only [List.takeWhile] at h
    split at h
    · rename_i hy
      simp only [List.mem_cons] at h ⊢
      rcases h with rfl | h'
      · exact ⟨Or.inl rfl, hy⟩
      · rcases mem_and_pred_of_mem_takeWhile h' with ⟨hm, hp⟩
        exact ⟨Or.inr hm, hp⟩
    · simp at h

private theorem spqrBoundedEvs_sliceClone {bs : List (BitVec 8)} {B : Nat}
    (hb : bs.length ≤ B) (hmax : B ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 B (if bs = [] then [] else rustAllocEvents bs.length 1) := by
  split
  · exact SpqrBoundedEvs.nil 1 B
  · rename_i hne
    have hpos : 1 ≤ bs.length := by
      cases bs with
      | nil => contradiction
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have hre : rustAllocEvents bs.length 1 = [.alloc bs.length] := by
      simp [rustAllocEvents, hpos]
    rw [hre]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_trans hb hmax, hb, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_ct1SentPostEnv {F : ShaCompress} {u : V1State.Unchunked.Ct1Sent}
    {B : Nat} (hmax : B ≤ MallocngMaxAllocSize)
    (hauth_le : ∀ auth, u.auth = some auth → auth.rootKey.length + auth.macKey.length ≤ B)
    {evs : List AllocEvent} (hevs : Ct1SentFromPbPostEnv F u evs) :
    SpqrBoundedEvs 2 B evs := by
  rcases hevs with ⟨evsFree, hfree, rfl⟩
  have halloc : SpqrBoundedEvs 2 B (ct1SentFromPbAllocEvents F u) := by
    unfold ct1SentFromPbAllocEvents
    cases ct1SentFromPb (spqrAuthApi F) u with
    | error _ => exact SpqrBoundedEvs.nil 2 B
    | ok _ =>
      cases hauth : u.auth with
      | none => exact SpqrBoundedEvs.nil 2 B
      | some auth =>
        have hle := hauth_le auth hauth
        unfold authFromPbAllocEvents
        have h1 := spqrBoundedEvs_sliceClone (bs := auth.rootKey) (B := B) (by omega) hmax
        have h2 := spqrBoundedEvs_sliceClone (bs := auth.macKey) (B := B) (by omega) hmax
        exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append h1 h2)
  exact SpqrBoundedEvs.mono (by decide) (by omega)
    (SpqrBoundedEvs.append halloc (SpqrBoundedEvs.of_freeOnly hfree))

private theorem spqrBoundedEvs_encoderPtsSlot {bs : List (BitVec 8)} {B : Nat}
    (hb : bs.length ≤ B) (hmax : 2 * B + 2 ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 (2 * B + 2) (encoderFromPbPtsSlotEvents bs) := by
  unfold encoderFromPbPtsSlotEvents
  split
  · exact SpqrBoundedEvs.nil 1 (2 * B + 2)
  · rename_i hempty
    have hpos : 1 ≤ bs.length := by
      cases bs with
      | nil => exact False.elim (hempty rfl)
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have hge2 : 2 ≤ 2 * bs.length := by omega
    have hre : rustAllocEvents (2 * bs.length) 2 = [.alloc (2 * bs.length)] := by
      simp [rustAllocEvents, hge2]
    rw [hre]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨by dsimp [AllocEvent.withinMaxAlloc]; omega,
      by dsimp [AllocEvent.reqBytes]; omega,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_flatMap_encoderPtsSlot :
    ∀ (xs : List (List (BitVec 8))) {B : Nat},
      2 * B + 2 ≤ MallocngMaxAllocSize →
      (∀ bs ∈ xs, bs.length ≤ B) →
      SpqrBoundedEvs xs.length (2 * B + 2) (xs.flatMap encoderFromPbPtsSlotEvents)
  | [], _, _, _ => SpqrBoundedEvs.nil 0 _
  | bs :: rest, B, hmax, hall => by
    simp only [List.flatMap_cons, List.length_cons]
    have hhead := spqrBoundedEvs_encoderPtsSlot (hall bs List.mem_cons_self) hmax
    have htail := spqrBoundedEvs_flatMap_encoderPtsSlot rest hmax
      (fun x hx => hall x (List.mem_cons_of_mem bs hx))
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hhead htail)

private theorem spqrBoundedEvs_replicate_alloc2 :
    ∀ (n : Nat) {R : Nat},
      2 ≤ R → R ≤ MallocngMaxAllocSize →
      SpqrBoundedEvs n R ((List.replicate n (rustAllocEvents 2 2)).flatten)
  | 0, _, _, _ => SpqrBoundedEvs.nil 0 _
  | n + 1, R, h2, hmax => by
    simp only [List.replicate_succ, List.flatten_cons]
    have hone : SpqrBoundedEvs 1 R (rustAllocEvents 2 2) := by
      have hre : rustAllocEvents 2 2 = [.alloc 2] := by simp [rustAllocEvents]
      rw [hre]
      refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
      simp only [List.mem_singleton] at hev
      subst hev
      exact ⟨Nat.le_trans h2 hmax, h2, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    have htail := spqrBoundedEvs_replicate_alloc2 n h2 hmax
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hone htail)

private theorem spqrBoundedEvs_encoderPolysSlot {bs : List (BitVec 8)} {B : Nat}
    (hpred : (!bs.isEmpty && (bs.length % 2 == 0)) = true)
    (hb : bs.length ≤ B) (hmax : 2 * B + 2 ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 (2 * B + 2) (encoderFromPbPolysSlotEvents bs) := by
  unfold encoderFromPbPolysSlotEvents
  rcases (Bool.and_eq_true _ _).mp hpred with ⟨hne_b, hmod_b⟩
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => simp [List.isEmpty] at hne_b
    | cons _ _ => exact Nat.succ_pos _
  have hmod0 : bs.length % 2 = 0 := beq_iff_eq.mp hmod_b
  have hge2 : 2 ≤ bs.length := by omega
  have hre : rustAllocEvents bs.length 2 = [.alloc bs.length] := by
    simp [rustAllocEvents, hge2]
  rw [hre]
  have halloc : SpqrBoundedEvs 1 (2 * B + 2) [.alloc bs.length] := by
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨by dsimp [AllocEvent.withinMaxAlloc]; omega,
      by dsimp [AllocEvent.reqBytes]; omega,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  have hfree : FreeOnlyEvs (rustDeallocEvents 2 2) := by
    intro ev hev
    simp only [rustDeallocEvents, List.mem_singleton] at hev
    exact ⟨2, 2, hev⟩
  exact SpqrBoundedEvs.mono (by decide) (by omega)
    (SpqrBoundedEvs.append halloc (SpqrBoundedEvs.of_freeOnly hfree))

private theorem spqrBoundedEvs_flatMap_encoderPolysSlot :
    ∀ (xs : List (List (BitVec 8))) {B : Nat},
      2 * B + 2 ≤ MallocngMaxAllocSize →
      (∀ bs ∈ xs, (!bs.isEmpty && (bs.length % 2 == 0)) = true ∧ bs.length ≤ B) →
      SpqrBoundedEvs xs.length (2 * B + 2) (xs.flatMap encoderFromPbPolysSlotEvents)
  | [], _, _, _ => SpqrBoundedEvs.nil 0 _
  | bs :: rest, B, hmax, hall => by
    simp only [List.flatMap_cons, List.length_cons]
    have ⟨hp0, hb0⟩ := hall bs List.mem_cons_self
    have hhead := spqrBoundedEvs_encoderPolysSlot hp0 hb0 hmax
    have htail := spqrBoundedEvs_flatMap_encoderPolysSlot rest hmax
      (fun x hx => hall x (List.mem_cons_of_mem bs hx))
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hhead htail)

private theorem spqrBoundedEvs_encoderFromPbEnv {pb : ProtoPolynomialEncoder} {B : Nat}
    (hmax : 2 * B + 2 ≤ MallocngMaxAllocSize)
    (hsum : (pb.pts.map List.length).sum + (pb.polys.map List.length).sum ≤ B)
    {evs : List AllocEvent} (hevs : EncoderFromPbEnv pb evs) :
    SpqrBoundedEvs 32 (2 * B + 2) evs := by
  rcases hevs with ⟨evs_alloc, evs_free, rfl, halloc, hfree⟩
  have hb_alloc : SpqrBoundedEvs 32 (2 * B + 2) evs_alloc := by
    rcases halloc with rfl | ⟨hpts16, _, rfl⟩ | ⟨_, hpolys16, rfl⟩
    · exact SpqrBoundedEvs.nil 32 (2 * B + 2)
    · unfold encoderFromPbPtsLoopEvents
      have htw := spqrBoundedEvs_flatMap_encoderPtsSlot
        (pb.pts.takeWhile (fun bs => bs.length % 2 == 0)) hmax fun bs hbs => by
          rcases mem_and_pred_of_mem_takeWhile hbs with ⟨hmem, _⟩
          have hm := mem_length_le_sum_map hmem
          omega
      have hlen_le : (pb.pts.takeWhile (fun bs => bs.length % 2 == 0)).length ≤ 16 :=
        hpts16 ▸ takeWhile_length_le _ pb.pts
      exact SpqrBoundedEvs.mono (Nat.le_trans hlen_le (by decide)) (Nat.le_refl _) htw
    · unfold encoderFromPbPolysInitEvents encoderFromPbPolysLoopEvents
      have hinit := spqrBoundedEvs_replicate_alloc2 16 (R := 2 * B + 2) (by omega) hmax
      have htw := spqrBoundedEvs_flatMap_encoderPolysSlot
        (pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))) hmax fun bs hbs => by
          rcases mem_and_pred_of_mem_takeWhile hbs with ⟨hmem, hp⟩
          have hm := mem_length_le_sum_map hmem
          exact ⟨hp, by omega⟩
      have hlen_le :
          (pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))).length ≤ 16 :=
        hpolys16 ▸ takeWhile_length_le _ pb.polys
      have hloop := SpqrBoundedEvs.mono hlen_le (Nat.le_refl _) htw
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append hinit hloop)
  exact SpqrBoundedEvs.mono (by decide) (by omega)
    (SpqrBoundedEvs.append hb_alloc (SpqrBoundedEvs.of_freeOnly hfree))

private theorem spqrBoundedEvs_fromPbDecSlot {bs : List (BitVec 8)} {B : Nat}
    (hmod : (bs.length % 4 == 0) = true) (hb : bs.length ≤ B)
    (hmax : B ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 B (fromPbDecSlotEvents bs) := by
  unfold fromPbDecSlotEvents
  split
  · exact SpqrBoundedEvs.nil 1 B
  · rename_i hempty
    have hpos : 0 < bs.length := by
      cases bs with
      | nil => exact False.elim (hempty rfl)
      | cons _ _ => exact Nat.succ_pos _
    have hmod0 : bs.length % 4 = 0 := beq_iff_eq.mp hmod
    have hge2 : 2 ≤ bs.length := by omega
    have hre : rustAllocEvents bs.length 2 = [.alloc bs.length] := by
      simp [rustAllocEvents, hge2]
    rw [hre]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_trans hb hmax, hb, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_flatMap_decSlot :
    ∀ (xs : List (List (BitVec 8))) {B : Nat},
      B ≤ MallocngMaxAllocSize →
      (∀ bs ∈ xs, (bs.length % 4 == 0) = true ∧ bs.length ≤ B) →
      SpqrBoundedEvs xs.length B (xs.flatMap fromPbDecSlotEvents)
  | [], _, _, _ => SpqrBoundedEvs.nil 0 _
  | bs :: rest, B, hmax, hall => by
    simp only [List.flatMap_cons, List.length_cons]
    have ⟨hm0, hb0⟩ := hall bs List.mem_cons_self
    have hhead := spqrBoundedEvs_fromPbDecSlot hm0 hb0 hmax
    have htail := spqrBoundedEvs_flatMap_decSlot rest hmax
      (fun x hx => hall x (List.mem_cons_of_mem bs hx))
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hhead htail)

private theorem spqrBoundedEvs_fromPbDecEnv {d : ProtoPolynomialDecoder} {B : Nat}
    (hmax : B ≤ MallocngMaxAllocSize) (hsum : (d.pts.map List.length).sum ≤ B)
    {evs : List AllocEvent} (hevs : FromPbDecEnv d evs) :
    SpqrBoundedEvs 16 B evs := by
  rcases hevs with ⟨evs_alloc, evs_free, rfl, halloc, hfree⟩
  have hb_alloc : SpqrBoundedEvs 16 B evs_alloc := by
    rcases halloc with rfl | ⟨hlen16, rfl⟩
    · exact SpqrBoundedEvs.nil 16 B
    · unfold fromPbDecLoopAllocEvents
      have htw := spqrBoundedEvs_flatMap_decSlot
        (d.pts.takeWhile (fun bs => bs.length % 4 == 0)) hmax fun bs hbs => by
          rcases mem_and_pred_of_mem_takeWhile hbs with ⟨hmem, hmod⟩
          exact ⟨hmod, Nat.le_trans (mem_length_le_sum_map hmem) hsum⟩
      have hlen_le : (d.pts.takeWhile (fun bs => bs.length % 4 == 0)).length ≤ 16 :=
        hlen16 ▸ takeWhile_length_le _ d.pts
      exact SpqrBoundedEvs.mono hlen_le (Nat.le_refl B) htw
  exact SpqrBoundedEvs.mono (by decide) (by omega)
    (SpqrBoundedEvs.append hb_alloc (SpqrBoundedEvs.of_freeOnly hfree))

private theorem spqrBoundedEvs_ct1SampledUcSomeEnv
    {F : ShaCompress} {s : V1State.Chunked.Ct1Sampled} {u : V1State.Unchunked.Ct1Sent}
    {optDec : Option PolynomialDecoder} {B : Nat}
    (hB : B = (V1State.encodeRaw { innerState := some (.ct1Sampled s) }).length)
    (hmax2 : 2 * B + 2 ≤ MallocngMaxAllocSize)
    (huc : s.uc = some u)
    (hdec_sub : ∀ d, optDec = some d → s.receivingEk = some d)
    {evs : List AllocEvent}
    (hevs : Ct1SampledUcSomeEnv F u s.sendingCt1 optDec evs) :
    SpqrBoundedEvs 128 (4 * B + 4096) evs := by
  have hmax : B ≤ MallocngMaxAllocSize := by omega
  have hauth_le : ∀ auth, u.auth = some auth → auth.rootKey.length + auth.macKey.length ≤ B := by
    intro auth hauth
    rw [hB]
    exact rawAuth_le_ct1Sampled_encodeRaw s u auth huc hauth
  unfold Ct1SampledUcSomeEnv at hevs
  cases hct : ct1SentFromPb (spqrAuthApi F) u with
  | error _ =>
    rw [hct] at hevs; dsimp only at hevs
    rcases hevs with ⟨evs1, evs2, h1, h2, rfl⟩
    have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax hauth_le h1
    exact SpqrBoundedEvs.mono (by decide) (by omega)
      (SpqrBoundedEvs.append hb1 (SpqrBoundedEvs.of_freeOnly h2))
  | ok _ =>
    rw [hct] at hevs
    cases henc : s.sendingCt1 with
    | none =>
      rw [henc] at hevs; dsimp only at hevs
      rcases hevs with ⟨evs1, evs2, h1, h2, rfl⟩
      have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax hauth_le h1
      exact SpqrBoundedEvs.mono (by decide) (by omega)
        (SpqrBoundedEvs.append hb1 (SpqrBoundedEvs.of_freeOnly h2))
    | some e =>
      rw [henc] at hevs; dsimp only at hevs
      have henc_sum :
          ((pbToProtoPolyEncoder e).pts.map List.length).sum +
            ((pbToProtoPolyEncoder e).polys.map List.length).sum ≤ B := by
        rw [hB]
        exact sum_enc_le_ct1Sampled_encodeRaw s e henc
      cases hres : fromPbResult (pbToProtoPolyEncoder e) with
      | error _ =>
        rw [hres] at hevs; dsimp only at hevs
        rcases hevs with ⟨evs1, evs2, evs3, h1, h2, h3, rfl⟩
        have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax hauth_le h1
        have hb2 := spqrBoundedEvs_encoderFromPbEnv hmax2 henc_sum h2
        have hb12 := SpqrBoundedEvs.append hb1 hb2
        exact SpqrBoundedEvs.mono (by decide) (by omega)
          (SpqrBoundedEvs.append hb12 (SpqrBoundedEvs.of_freeOnly h3))
      | ok _ =>
        rw [hres] at hevs
        cases hoptd : optDec with
        | none =>
          rw [hoptd] at hevs; dsimp only at hevs
          rcases hevs with ⟨evs1, evs2, evs3, h1, h2, h3, rfl⟩
          have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax hauth_le h1
          have hb2 := spqrBoundedEvs_encoderFromPbEnv hmax2 henc_sum h2
          have hb12 := SpqrBoundedEvs.append hb1 hb2
          exact SpqrBoundedEvs.mono (by decide) (by omega)
            (SpqrBoundedEvs.append hb12 (SpqrBoundedEvs.of_freeOnly h3))
        | some d =>
          rw [hoptd] at hevs; dsimp only at hevs
          rcases hevs with ⟨evs1, evs2, evs3, evs4, h1, h2, h3, h4, rfl⟩
          have hb1 := spqrBoundedEvs_ct1SentPostEnv hmax hauth_le h1
          have hb2 := spqrBoundedEvs_encoderFromPbEnv hmax2 henc_sum h2
          have hdec_sum : ((pbToProtoPolyDecoder d).pts.map List.length).sum ≤ B := by
            rw [hB]
            exact sum_dec_pts_le_ct1Sampled_encodeRaw s d (hdec_sub d hoptd)
          have hb3 := spqrBoundedEvs_fromPbDecEnv hmax hdec_sum h3
          have hb12 := SpqrBoundedEvs.append hb1 hb2
          have hb123 := SpqrBoundedEvs.append hb12 hb3
          exact SpqrBoundedEvs.mono (by decide) (by omega)
            (SpqrBoundedEvs.append hb123 (SpqrBoundedEvs.of_freeOnly h4))

/-- Subsumption of `Ct1SampledFromPbEnv F s` into the canonical `StatesFromPbEnv` envelope. -/
theorem ct1SampledFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ} (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled)
    (hfits : FitsEnv M lim st0 (StatesFromPbEnv { innerState := some (.ct1Sampled s) }))
    {evs : List AllocEvent} (hevs : Ct1SampledFromPbEnv F s evs) :
    StatesFromPbEnv { innerState := some (.ct1Sampled s) } evs := by
  let pb : V1State := { innerState := some (.ct1Sampled s) }
  let B := (V1State.encodeRaw pb).length
  change SpqrBoundedEvs 128 (4 * B + 4096) evs
  let m := min (2 * B + 2) MallocngMaxAllocSize
  have hm_env : StatesFromPbEnv pb [.alloc m] := by
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.min_le_right _ _, Nat.le_trans (Nat.min_le_left _ _) (by omega),
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  have hm_fit : FitsEvents M lim st0 [.alloc m] := hfits [.alloc m] hm_env
  rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
  have hm_req : m ≤ M.stepReserve (.alloc m) st0 := M.req_le_stepReserve (.alloc m) st0
  have hmax2 : 2 * B + 2 ≤ MallocngMaxAllocSize := by
    dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
    omega
  unfold Ct1SampledFromPbEnv at hevs
  cases hdec : s.receivingEk <;> rw [hdec] at hevs <;>
    cases huc : s.uc <;> rw [huc] at hevs
  · exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
  · rename_i u
    exact spqrBoundedEvs_ct1SampledUcSomeEnv (optDec := none) rfl hmax2 huc
      (fun _ h => nomatch h) hevs
  · exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
  · dsimp only at hevs
    split at hevs
    · rename_i d u _
      exact spqrBoundedEvs_ct1SampledUcSomeEnv (optDec := some d) rfl hmax2 huc
        (fun d' hd' => by cases hd'; exact hdec) hevs
    · exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)

theorem fitsEnv_ct1SampledFromPbEnv_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ} (F : ShaCompress)
    (s : V1State.Chunked.Ct1Sampled)
    (hfits : FitsEnv M lim st0 (StatesFromPbEnv { innerState := some (.ct1Sampled s) })) :
    FitsEnv M lim st0 (Ct1SampledFromPbEnv F s) :=
  fun _ hevs => hfits _ (ct1SampledFromPbEnv_sub_statesFromPbEnv F s hfits hevs)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7PlacedBudgetAux
