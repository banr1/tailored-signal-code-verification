/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 10 (`Ct2Sampled`) Envelopes and Prefix

Allocation envelopes, `StatesFromPbEnv` subsumption, shared prefix `+1632 -> +5728`, and
`sendingCt2 = none` error path for `InnerState.ct2Sampled` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudgetAux

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_333 lsProg_333 lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder PolynomialEncoderPB ProtoAuthenticator ProtoPolynomialEncoder V1State
   pbToProtoPolyEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.ProtoRepr
  (AuthenticatorPBGhost authenticatorPBAt authenticatorPBAt_eq_exists_pinned
   authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbJumpTablePlacedAt
   statesFromPbSavedCells statesFromPbStack v10_authPBPinnedAt_64_eq_full
   v10_fsp_split_1632 v10_fsp_unsplit_1632 v10_pbA_64_to_120_entails_56
   v10_pbA_none_some_entails_224 v10_vecU8Payload_entails_vecCapPtrDealloc
   v10_vecU8Payload_extract_bounds)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth rawUcCt2Sent
   rawUcCt2Sent_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbAllocEnv_imp_encoderFromPbEnv
   encoderFromPbPolysInitEvents encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents
   encoderFromPbPtsLoopEvents encoderFromPbPtsSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10PlacedBudget
  (v10_ct2Sent_5728_to_7212_none_placed_budget v10_ct2Sent_load_1632_to_1720_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10aPlacedBudget
  (v10_states_from_pb_err_2084_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (spqrBoundedEvs_authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)

export Variant10bPlacedBudget
  (v10_ct2Sent_expose_pre_uc_none_2304_placed v10_ct2Sent_err_1632_uc_none_2304_placed
   v10_ct2Sent_expose_pre_auth_none_2304_placed v10_ct2Sent_err_1632_auth_none_2304_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Allocation Envelopes & `StatesFromPbEnv` Subsumption for Variant 10 (`Ct2Sampled`) -/

/-- Precondition allocation envelope of Variant 10 (`InnerState.ct2Sampled`, `+1632`).
    Admits `[]` on `uc = none` / `auth = none` error paths and when `auth` + `sendingCt2` perform
    zero allocations (passing `zeroBudgetLimits`), while covering both `auth` cloning and
    non-empty `<PolyEncoder>::from_pb` allocations after dropping the input `ProtoAuthenticator`
    buffers. -/
def Ct2SampledFromPbAllocEnv (s : V1State.Chunked.Ct2Sampled) (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => evs = []
  | some uc =>
    match uc.auth with
    | none => evs = []
    | some auth =>
      match s.sendingCt2 with
      | none => AuthFromPbEnv auth evs
      | some pbEnc =>
        AuthFromPbEnv auth evs ∨
        ∃ evs_af evs_enc,
          FreeOnlyEvs evs_af ∧
          EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
          evs_enc ≠ [] ∧
          evs = authFromPbEvents auth ++ evs_af ++ evs_enc

/-- Full postcondition event envelope of Variant 10 (`InnerState.ct2Sampled`, `+1632`). -/
def Ct2SampledFromPbEnv (s : V1State.Chunked.Ct2Sampled) (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => FreeOnlyEvs evs
  | some uc =>
    match uc.auth with
    | none => FreeOnlyEvs evs
    | some auth =>
      match s.sendingCt2 with
      | none =>
        ∃ evs_free, FreeOnlyEvs evs_free ∧ evs = authFromPbEvents auth ++ evs_free
      | some pbEnc =>
        ∃ evs_af evs_enc,
          FreeOnlyEvs evs_af ∧
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
          evs = authFromPbEvents auth ++ evs_af ++ evs_enc

theorem freeOnlyEvs_append {l₁ l₂ : List AllocEvent}
    (h1 : FreeOnlyEvs l₁) (h2 : FreeOnlyEvs l₂) : FreeOnlyEvs (l₁ ++ l₂) :=
  fun ev hev => (List.mem_append.mp hev).elim (h1 ev) (h2 ev)

theorem encoderFromPbEnv_append_freeOnly {pb : ProtoPolynomialEncoder}
    {evs₁ evs₂ : List AllocEvent}
    (h1 : EncoderFromPbEnv pb evs₁) (h2 : FreeOnlyEvs evs₂) :
    EncoderFromPbEnv pb (evs₁ ++ evs₂) := by
  rcases h1 with ⟨evs_a, evs_f, rfl, ha, hf⟩
  exact ⟨evs_a, evs_f ++ evs₂, List.append_assoc evs_a evs_f evs₂, ha, freeOnlyEvs_append hf h2⟩

theorem ct2SampledAllocEnv_imp_ct2SampledEnv {s : V1State.Chunked.Ct2Sampled}
    {evs : List AllocEvent} (h : Ct2SampledFromPbAllocEnv s evs) :
    Ct2SampledFromPbEnv s evs := by
  cases s with | mk optUc optEnc =>
  cases optUc with
  | none =>
    dsimp only [Ct2SampledFromPbAllocEnv, Ct2SampledFromPbEnv] at h ⊢
    subst h
    exact FreeOnlyEvs.nil
  | some uc =>
    cases uc with | mk ep optAuth =>
    cases optAuth with
    | none =>
      dsimp only [Ct2SampledFromPbAllocEnv, Ct2SampledFromPbEnv] at h ⊢
      subst h
      exact FreeOnlyEvs.nil
    | some auth =>
      dsimp only [Ct2SampledFromPbAllocEnv, Ct2SampledFromPbEnv] at h ⊢
      cases optEnc with
      | none =>
        dsimp only [AuthFromPbEnv] at h
        exact ⟨[], FreeOnlyEvs.nil, by rw [h, List.append_nil]⟩
      | some pbEnc =>
        rcases h with hauth_ev | ⟨evs_af, evs_enc, hfree_af, henc, _, rfl⟩
        · dsimp only [AuthFromPbEnv] at hauth_ev
          refine ⟨[], [], FreeOnlyEvs.nil,
            encoderFromPbAllocEnv_imp_encoderFromPbEnv (Or.inl rfl), ?_⟩
          simp [hauth_ev]
        · exact ⟨evs_af, evs_enc, hfree_af,
            encoderFromPbAllocEnv_imp_encoderFromPbEnv henc, rfl⟩

theorem fitsEnv_alloc_of_ct2SampledEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.Ct2Sampled} (h : FitsEnv M lim st (Ct2SampledFromPbEnv s)) :
    FitsEnv M lim st (Ct2SampledFromPbAllocEnv s) :=
  FitsEnv.mono (fun _ => ct2SampledAllocEnv_imp_ct2SampledEnv) h

theorem fitsEvents_auth_of_ct2SampledAllocEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {ep : BitVec 64} {auth : ProtoAuthenticator}
    {optEnc : Option PolynomialEncoder}
    (hfits : FitsEnv M lim st
      (Ct2SampledFromPbAllocEnv
        { uc := some { epoch := ep, auth := some auth }, sendingCt2 := optEnc })) :
    FitsEvents M lim st (authFromPbEvents auth) := by
  apply hfits (authFromPbEvents auth)
  dsimp only [Ct2SampledFromPbAllocEnv]
  cases optEnc with
  | none => rfl
  | some _ => exact Or.inl rfl

theorem fitsEnv_enc_of_ct2SampledAllocEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {ep : BitVec 64} {auth : ProtoAuthenticator}
    {pbEnc : PolynomialEncoder} {evs_af : List AllocEvent}
    (hfits : FitsEnv M lim st
      (Ct2SampledFromPbAllocEnv
        { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some pbEnc }))
    (hfree_af : FreeOnlyEvs evs_af) :
    FitsEnv M lim (M.stepEvents (authFromPbEvents auth ++ evs_af) st)
      (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)) := by
  intro evs_enc henc
  by_cases hne : evs_enc = []
  · subst hne; simp [FitsEvents]
  · have hev : Ct2SampledFromPbAllocEnv
        { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some pbEnc }
        (authFromPbEvents auth ++ evs_af ++ evs_enc) :=
      Or.inr ⟨evs_af, evs_enc, hfree_af, henc, hne, rfl⟩
    exact ((fitsEvents_append M lim (authFromPbEvents auth ++ evs_af) evs_enc st).mp
      (hfits _ hev)).2

private theorem spqrBoundedEvs_alloc_singleton {sz : Nat}
    (hmax : sz ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 sz [.alloc sz] := by
  refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨hmax, Nat.le_refl sz, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_ptsLoopEvents (pts : List (List (BitVec 8)))
    (hmax : 2 * (pts.map List.length).sum ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs pts.length (2 * (pts.map List.length).sum)
      (encoderFromPbPtsLoopEvents pts) := by
  unfold encoderFromPbPtsLoopEvents
  induction pts with
  | nil => exact SpqrBoundedEvs.nil 0 0
  | cons bs rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hmax ⊢
    by_cases heven : (bs.length % 2 == 0) = true
    · simp only [List.takeWhile_cons, heven, ↓reduceIte, List.flatMap_cons]
      have hih := ih (by omega)
      unfold encoderFromPbPtsSlotEvents
      by_cases hemp : bs.isEmpty = true
      · simp only [hemp, ↓reduceIte, List.nil_append]
        exact SpqrBoundedEvs.mono (by omega) (by omega) hih
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
        have hpos : 1 ≤ bs.length := by
          cases bs with
          | nil => simp at hemp
          | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
        have h2 : 2 ≤ 2 * bs.length := by omega
        have hre : rustAllocEvents (2 * bs.length) 2 = [.alloc (2 * bs.length)] := by
          simp [rustAllocEvents, h2]
        rw [hre]
        exact SpqrBoundedEvs.mono (by omega) (by omega)
          (SpqrBoundedEvs.append (spqrBoundedEvs_alloc_singleton (by omega)) hih)
    · have hfls : (bs.length % 2 == 0) = false := Bool.eq_false_iff.mpr heven
      simp only [List.takeWhile_cons, hfls, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil]
      exact SpqrBoundedEvs.nil _ _

private theorem spqrBoundedEvs_replicate_alloc2 :
    ∀ n : Nat, SpqrBoundedEvs n 2 ((List.replicate n (rustAllocEvents 2 2)).flatten)
  | 0 => SpqrBoundedEvs.nil 0 2
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons]
    have hre : rustAllocEvents 2 2 = [.alloc 2] := by simp [rustAllocEvents]
    rw [hre]
    have h2max : 2 ≤ MallocngMaxAllocSize := by
      dsimp only [MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize]; omega
    exact SpqrBoundedEvs.mono (by omega) (by omega)
      (SpqrBoundedEvs.append (spqrBoundedEvs_alloc_singleton h2max)
        (spqrBoundedEvs_replicate_alloc2 n))

private theorem spqrBoundedEvs_polysLoopEvents (polys : List (List (BitVec 8)))
    (hmax : (polys.map List.length).sum ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs polys.length (polys.map List.length).sum
      (encoderFromPbPolysLoopEvents polys) := by
  unfold encoderFromPbPolysLoopEvents
  induction polys with
  | nil => exact SpqrBoundedEvs.nil 0 0
  | cons bs rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hmax ⊢
    by_cases hok : (!bs.isEmpty && (bs.length % 2 == 0)) = true
    · simp only [List.takeWhile_cons, hok, ↓reduceIte, List.flatMap_cons]
      have hih := ih (by omega)
      rw [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hok
      have hne : 1 ≤ bs.length := by
        cases bs with
        | nil => simp at hok
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      have h2 : 2 ≤ bs.length := by omega
      unfold encoderFromPbPolysSlotEvents
      have hre : rustAllocEvents bs.length 2 = [.alloc bs.length] := by
        simp [rustAllocEvents, h2]
      rw [hre]
      have hslot : SpqrBoundedEvs 1 bs.length ([.alloc bs.length] ++ rustDeallocEvents 2 2) :=
        SpqrBoundedEvs.mono (by omega) (by omega)
          (SpqrBoundedEvs.append (spqrBoundedEvs_alloc_singleton (by omega))
            (SpqrBoundedEvs.of_freeOnly (FreeOnlyEvs.singleton 2 2)))
      exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hslot hih)
    · have hfls : (!bs.isEmpty && (bs.length % 2 == 0)) = false := Bool.eq_false_iff.mpr hok
      simp only [List.takeWhile_cons, hfls, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil]
      exact SpqrBoundedEvs.nil _ _

theorem spqrBoundedEvs_encoderFromPbAllocEnv {pb : ProtoPolynomialEncoder}
    {evs : List AllocEvent}
    (hmax : 2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum + 2 ≤
      MallocngMaxAllocSize)
    (hevs : EncoderFromPbAllocEnv pb evs) :
    SpqrBoundedEvs 32
      (2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum + 2) evs := by
  rcases hevs with rfl | ⟨hpts16, _, rfl⟩ | ⟨_, hpol16, rfl⟩
  · exact SpqrBoundedEvs.nil _ _
  · have hb := spqrBoundedEvs_ptsLoopEvents pb.pts (by omega)
    exact SpqrBoundedEvs.mono (by omega) (by omega) hb
  · have hb_init : SpqrBoundedEvs 16 2 encoderFromPbPolysInitEvents :=
      spqrBoundedEvs_replicate_alloc2 16
    have hb_loop := spqrBoundedEvs_polysLoopEvents pb.polys (by omega)
    exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.append hb_init hb_loop)

theorem spqrBoundedEvs_encoderFromPbEnv {pb : ProtoPolynomialEncoder}
    {evs : List AllocEvent}
    (hmax : 2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum + 2 ≤
      MallocngMaxAllocSize)
    (hevs : EncoderFromPbEnv pb evs) :
    SpqrBoundedEvs 32
      (2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum + 2) evs := by
  rcases hevs with ⟨evs_a, evs_f, rfl, ha, hf⟩
  exact SpqrBoundedEvs.mono (by omega) (by omega)
    (SpqrBoundedEvs.append (spqrBoundedEvs_encoderFromPbAllocEnv hmax ha)
      (SpqrBoundedEvs.of_freeOnly hf))

private theorem rawAuth_le_ct2Sampled_encodeRaw
    (ep : BitVec 64) (auth : ProtoAuthenticator)
    (optEnc : Option PolynomialEncoder) :
    auth.rootKey.length + auth.macKey.length ≤
      (V1State.encodeRaw
        { innerState := some (.ct2Sampled
            { uc := some { epoch := ep, auth := some auth }, sendingCt2 := optEnc }) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.Ct2Sampled.encodeRaw 11#32
    { uc := some { epoch := ep, auth := some auth }, sendingCt2 := optEnc }
  have h1 := length_le_encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw
    rawUcCt2Sent rawUcCt2Sent_le_encodeRaw 1#32
    (some ({ epoch := ep, auth := some auth } : V1State.Unchunked.Ct2Sent))
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.Ct2Sampled.encodeRaw, rawUcCt2Sent, optRaw, rawAuth] at h0 h1 ⊢
  rw [List.length_append] at h0
  omega

private theorem rawAuth_and_enc_le_ct2Sampled_encodeRaw
    (ep : BitVec 64) (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder) :
    auth.rootKey.length + auth.macKey.length +
      (pbEnc.pts.map List.length).sum + (pbEnc.polys.map List.length).sum ≤
      (V1State.encodeRaw
        { innerState := some (.ct2Sampled
            { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some pbEnc }) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.Ct2Sampled.encodeRaw 11#32
    { uc := some { epoch := ep, auth := some auth }, sendingCt2 := some pbEnc }
  have h1 := length_le_encodeOptMessage V1State.Unchunked.Ct2Sent.encodeRaw
    rawUcCt2Sent rawUcCt2Sent_le_encodeRaw 1#32
    (some ({ epoch := ep, auth := some auth } : V1State.Unchunked.Ct2Sent))
  have h2 := length_le_encodeMessage PolynomialEncoder.encodeRaw 2#32 pbEnc
  have hp1 := sum_length_le_encodeRepeatedBytes 2#32 pbEnc.pts
  have hp2 := sum_length_le_encodeRepeatedBytes 3#32 pbEnc.polys
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.Ct2Sampled.encodeRaw,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    PolynomialEncoder.encodeRaw, rawUcCt2Sent, optRaw, rawAuth] at h0 h1 h2 ⊢
  simp only [List.length_append] at h0 h2
  omega

theorem ct2SampledEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.Ct2Sampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ct2Sampled s) }))
    {evs : List AllocEvent} (hevs : Ct2SampledFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.ct2Sampled s) } evs := by
  let pb : V1State := { innerState := some (.ct2Sampled s) }
  change SpqrBoundedEvs 128 (4 * (V1State.encodeRaw pb).length + 4096) evs
  cases s with | mk optUc optEnc =>
  cases optUc with
  | none =>
    exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
  | some uc =>
    cases uc with | mk ep optAuth =>
    cases optAuth with
    | none =>
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
    | some auth =>
      dsimp only [Ct2SampledFromPbEnv] at hevs
      let m := min (2 * (V1State.encodeRaw pb).length + 2) MallocngMaxAllocSize
      have hm_env : StatesFromPbEnv pb [.alloc m] := by
        refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
        simp only [List.mem_singleton] at hev
        subst hev
        exact ⟨Nat.min_le_right _ _,
          Nat.le_trans (Nat.min_le_left _ _) (by omega),
          (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
      have hm_fit : FitsEvents M lim st [.alloc m] := hfits [.alloc m] hm_env
      rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
      have hm_req : m ≤ M.stepReserve (.alloc m) st := M.req_le_stepReserve (.alloc m) st
      have hm_max : 2 * (V1State.encodeRaw pb).length + 2 ≤ MallocngMaxAllocSize := by
        dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
        omega
      cases optEnc with
      | none =>
        rcases hevs with ⟨evs_free, hfree, rfl⟩
        have hlen := rawAuth_le_ct2Sampled_encodeRaw ep auth none
        have hb_r := spqrBoundedEvs_authKeyCloneEvents (bs := auth.rootKey)
          (by dsimp [pb] at hm_max; omega)
        have hb_m := spqrBoundedEvs_authKeyCloneEvents (bs := auth.macKey)
          (by dsimp [pb] at hm_max; omega)
        have hb_auth := SpqrBoundedEvs.append hb_r hb_m
        have hb_all := SpqrBoundedEvs.append hb_auth (SpqrBoundedEvs.of_freeOnly hfree)
        exact SpqrBoundedEvs.mono (by decide) (by dsimp [pb]; omega) hb_all
      | some pbEnc =>
        rcases hevs with ⟨evs_af, evs_enc, hfree_af, henc, rfl⟩
        have hlen := rawAuth_and_enc_le_ct2Sampled_encodeRaw ep auth pbEnc
        have hpb_pts : (pbToProtoPolyEncoder pbEnc).pts = pbEnc.pts := rfl
        have hpb_pol : (pbToProtoPolyEncoder pbEnc).polys = pbEnc.polys := rfl
        have hb_r := spqrBoundedEvs_authKeyCloneEvents (bs := auth.rootKey)
          (by dsimp [pb] at hm_max; omega)
        have hb_m := spqrBoundedEvs_authKeyCloneEvents (bs := auth.macKey)
          (by dsimp [pb] at hm_max; omega)
        have hb_enc := spqrBoundedEvs_encoderFromPbEnv
          (pb := pbToProtoPolyEncoder pbEnc)
          (by rw [hpb_pts, hpb_pol]; dsimp [pb] at hm_max; omega) henc
        rw [hpb_pts, hpb_pol] at hb_enc
        have hb_1 := SpqrBoundedEvs.append (SpqrBoundedEvs.append hb_r hb_m)
          (SpqrBoundedEvs.of_freeOnly hfree_af)
        have hb_all := SpqrBoundedEvs.append hb_1 hb_enc
        exact SpqrBoundedEvs.mono (by decide) (by dsimp [pb]; omega) hb_all

theorem fitsEnv_alloc_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.Ct2Sampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ct2Sampled s) })) :
    FitsEnv M lim st (Ct2SampledFromPbAllocEnv s) := by
  refine fitsEnv_alloc_of_ct2SampledEnv fun evs hevs => ?_
  exact hfits evs (ct2SampledEnv_sub_statesFromPbEnv s hfits hevs)

/-! ## Shared Prefix `+1632 -> +5728` for `s.uc = some { auth := some auth, epoch := ep }` -/

/-- Total-correctness (`SepWP`) shared prefix `+1632 -> +5728` for Variant 10 (`Ct2Sampled`),
    cloning `auth.rootKey` and `auth.macKey` and dropping the input `ProtoAuthenticator` buffers
    under `FitsEvents M lim st (authFromPbEvents auth)`. -/
theorem v10_ct2Sent_1632_to_5728_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA cap_enc ep v152 v184 v200 v232 : BitVec 64)
    (b16 : BitVec 8) (v224 : BitVec 32) (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Rest : SepProp)
    (hfits_auth : FitsEvents M lim st (authFromPbEvents auth))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
        ((pbA + 16#64) ↦₈ b16) ∗ authenticatorPBPinnedAt A.repAlloc ga (pbA + 64#64) auth ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs_af : List AllocEvent) (pa1 pa2 : BitVec 64),
          FreeOnlyEvs evs_af ∧
          (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
            ((pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 64#64) 56 ∗
            (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
            A.pool lim (M.stepEvents (authFromPbEvents auth ++ evs_af) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa1 ∧
          sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 auth.macKey.length ∧
          sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0) := by
  have ⟨hfits_rk, hfits_mk⟩ :=
    (fitsEvents_append M lim (authKeyCloneEvents auth.rootKey)
      (authKeyCloneEvents auth.macKey) st).mp hfits_auth
  rw [v10_authPBPinnedAt_64_eq_full]
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
       ((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗
       ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest) ∗
       A.pool lim st s1) by sep_ac_rfl))
    (Entails.trans
      (sepConj_mono_left
        (v10_vecU8Payload_extract_bounds A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey))
      (Entails.of_eq (show _ =
        ⌜ga.rootKey.cap.toNat < 2 ^ 63 ∧ (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63⌝ ∗
        (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
         ((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗
         ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
         ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((pbA + 112#64) ↦₆₄ ep) ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
         (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
          vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
          vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest) ∗
         A.pool lim st s1) by sep_ac_rfl)))) ?_
  refine SepWP.pure_elim fun ⟨hc1_lt, hl1_lt⟩ => ?_
  have h1632 := v10_ct2Sent_load_1632_to_1720_placed_budget A lim st (ext := ext) s0 s1 out pbA
    cap_enc ga.rootKey.cap ga.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
    ga.macKey.cap ga.macKey.ptr (BitVec.ofNat 64 auth.macKey.length) ep v152 v200 v232 b16 v224
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
     vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
     vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest)
    hsp0_align hc1_lt hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h1632) ?_
  intro s2 P2 hpc2 hrun2
    ⟨hP2, _hvm2, hsp2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
  have hpb56 := v10_pbA_64_to_120_entails_56 pbA
    ga.rootKey.cap ga.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
    ga.macKey.cap ga.macKey.ptr (BitVec.ofNat 64 auth.macKey.length) ep
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.trans (Entails.of_eq (show _ =
      (((pbA + 64#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 72#64) ↦₆₄ ga.rootKey.ptr) ∗
       ((pbA + 80#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       ((pbA + 88#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 96#64) ↦₆₄ ga.macKey.ptr) ∗
       ((pbA + 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((pbA + 112#64) ↦₆₄ ep)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
       A.pool lim st s2 ∗
       (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
        (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
        vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest)) by sep_ac_rfl))
    (Entails.trans (sepConj_mono_left hpb56) (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
        A.pool lim st s2 ∗
        (memRegion (pbA + 64#64) 56 ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest) by sep_ac_rfl))))) ?_
  have h1720 := Variant10bPlacedBudget.v10_ct2Sent_clone_rootKey_1720_to_5540_placed hA st s0 s2 out
    ga.rootKey.ptr cap_enc ga.rootKey.cap ga.macKey.cap (BitVec.ofNat 64 auth.macKey.length)
    pbA auth.rootKey
    (memRegion (pbA + 64#64) 56 ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Rest)
    hfits_rk hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2
    hx28_2 htr2
  refine SepWP.seq h1720 ?_
  intro s3 P3 hpc3 hrun3
    ⟨pa1, hP3, hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, htr3⟩
  let st1 := M.stepEvents (authKeyCloneEvents auth.rootKey) st
  refine SepWP.weaken_pre (Entails.trans hP3 (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
      vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗
      A.pool lim st1 s3 ∗
      (vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗ memRegion (pbA + 64#64) 56 ∗
       ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗ Rest) by dsimp only [st1]; sep_ac_rfl))) ?_
  have h5540 := Variant10bPlacedBudget.v10_ct2Sent_clone_macKey_5540_to_5688_placed hA st1 s0 s3 out
    ga.rootKey.ptr pa1 cap_enc ga.rootKey.cap ga.macKey.cap ga.macKey.ptr v184 pbA auth.macKey
    (vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗ memRegion (pbA + 64#64) 56 ∗
     ((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗ Rest)
    hfits_mk hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3
    hx27_3 htr3
  refine SepWP.seq h5540 ?_
  intro s4 P4 hpc4 hrun4
    ⟨pa2, hP4, hsp4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, htr4⟩
  let st2 := M.stepEvents (authFromPbEvents auth) st
  have hst2_eq : M.stepEvents (authKeyCloneEvents auth.macKey) st1 = st2 := by
    dsimp only [st1, st2, authFromPbEvents]
    rw [M.stepEvents_append]
  refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
      vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
      vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr ∗
      A.pool lim st2 s4 ∗
      (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 64#64) 56 ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ Rest)
      by rw [hst2_eq]; sep_ac_rfl))) ?_
  have h5688 := Variant10bPlacedBudget.v10_ct2Sent_dealloc_5688_to_5728_placed hA st2 s0 s4 out
    ga.rootKey.ptr pa1 cap_enc ga.rootKey.cap ga.macKey.cap ga.macKey.ptr
    (BitVec.ofNat 64 auth.macKey.length) pbA
    (((pbA + 8#64) ↦₆₄ cap_enc) ∗ ((pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 64#64) 56 ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ Rest)
    hsp0_align hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 htr4
  refine SepWP.mono h5688 ?_
  intro s5 P5 _ _ ⟨evs_af, hevs_af, hP5, hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx26_5, hx27_5, htr5⟩
  have hst_af : M.stepEvents evs_af st2 = M.stepEvents (authFromPbEvents auth ++ evs_af) st := by
    dsimp only [st2]
    rw [M.stepEvents_append]
  exact ⟨evs_af, pa1, pa2, hevs_af, hl1_lt,
    Entails.trans hP5 (Entails.of_eq (by rw [hst_af]; sep_ac_rfl)),
    hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx26_5, hx27_5, htr5⟩

theorem v10_ct2Sent_1632_to_5728_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA cap_enc ep v152 v184 v200 v232 : BitVec 64)
    (b16 : BitVec 8) (v224 : BitVec 32) (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Rest : SepProp) (onPanic : State → SepProp → Prop)
    (hfits_auth : FitsEvents M lim st (authFromPbEvents auth))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5728#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
        ((pbA + 16#64) ↦₈ b16) ∗ authenticatorPBPinnedAt A.repAlloc ga (pbA + 64#64) auth ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs_af : List AllocEvent) (pa1 pa2 : BitVec 64),
          FreeOnlyEvs evs_af ∧
          (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((pbA + 8#64) ↦₆₄ cap_enc) ∗
            ((pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 64#64) 56 ∗
            (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
            (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
            A.pool lim (M.stepEvents (authFromPbEvents auth ++ evs_af) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa1 ∧
          sm.readReg64 .x22 = cap_enc ∧ sm.readReg64 .x23 = pbA + 8#64 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 auth.macKey.length ∧
          sm.readReg64 .x27 = pbA ∧ TraceCalleeSaved sm s0)
      onPanic :=
  SepWPp.of_sepWP_ret
    (v10_ct2Sent_1632_to_5728_placed_sepWP hA st s0 s1 out pbA cap_enc ep
      v152 v184 v200 v232 b16 v224 ga auth Rest hfits_auth
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)

/-! ## `+1632 -> s0.x30` when `sendingCt2 = none` and `uc = some { auth := some auth, epoch := ep }` -/

/-- Total-correctness (`SepWP`) branch `+1632 -> s0.x30` when `sendingCt2 = none` and
    `uc = some { auth := some auth, epoch := ep }`. -/
theorem v10_ct2Sent_sending_none_some_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA ep : BitVec 64)
    (auth : ProtoAuthenticator)
    (hfits_auth : FitsEvents M lim st (authFromPbEvents auth))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
        memRegion (pbA + 16#64) 48 ∗ authenticatorPBAt A.repAlloc (pbA + 64#64) auth ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗ memRegion (pbA + 120#64) 104 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          Ct2SampledFromPbEnv
            { uc := some { epoch := ep, auth := some auth }, sendingCt2 := none } evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hm16 : memRegion (pbA + 16#64) 48 =
      (∃∗ b16 : BitVec 8, (pbA + 16#64) ↦₈ b16) ∗ memRegion (pbA + 17#64) 47 := by
    rw [ProofLib.memRegion_split' (b := pbA + 16#64) (n := 1) (k := 47)
          (b' := pbA + 17#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one (pbA + 16#64)]
  rw [hm16, authenticatorPBAt_eq_exists_pinned A.repAlloc (pbA + 64#64) auth]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v10_fsp_split_1632 (s0.sp - 2400#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun ga => SepWP.exists_elim fun b16 =>
    SepWP.exists_elim fun v232 => SepWP.exists_elim fun v228 =>
    SepWP.exists_elim fun v224 => SepWP.exists_elim fun v200 =>
    SepWP.exists_elim fun v184 => SepWP.exists_elim fun v152 => ?_
  have h5728 := v10_ct2Sent_1632_to_5728_placed_sepWP hA st s0 s1 out pbA noneCap ep
    v152 v184 v200 v232 b16 v224 ga auth
    (memRegion (s0.sp - 2400#64) 152 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     (pbA ↦₆₄ 0x800000000000000a#64) ∗ memRegion (pbA + 17#64) 47 ∗
     memRegion (pbA + 120#64) 104 ∗ statesFromPbJumpTablePlacedAt)
    hfits_auth hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h5728) ?_
  intro s2 P2 hpc2 hrun2
    ⟨evs_af, pa1, pa2, hevs_af, hl1_lt, hP2,
     hsp2, hx19_2, hx21_2, hx22_2, _, hx26_2, _, htr2⟩
  let st_af := M.stepEvents (authFromPbEvents auth ++ evs_af) st
  have hpb := v10_pbA_none_some_entails_224 pbA b16
  have hd1 := v10_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc
    (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey
  have hd2 := v10_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc
    (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗ ((pbA + 16#64) ↦₈ b16) ∗
       memRegion (pbA + 17#64) 47 ∗ memRegion (pbA + 64#64) 56 ∗ memRegion (pbA + 120#64) 104) ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗
       A.pool lim st_af s2) by dsimp only [st_af]; sep_ac_rfl))
    (Entails.trans (sepConj_mono hpb (sepConj_mono hd1 (sepConj_mono_left hd2)))
      (Entails.of_eq (show _ =
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
         vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 ∗
         memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
         memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
         (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
         memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTablePlacedAt) ∗
        A.pool lim st_af s2 by sep_ac_rfl))))) ?_
  have h7212 := v10_ct2Sent_5728_to_7212_none_placed_budget A lim st_af (ext := ext)
    s0 s2 out pa1 (BitVec.ofNat 64 auth.rootKey.length) (BitVec.ofNat 64 auth.macKey.length)
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
     vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 ∗
     memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hl1_lt hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx26_2 htr2
  refine SepWP.seq h7212 ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, _hvm3, hsp3, hx19_3, hx21_3, hx26_3, htr3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
      vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 ∗
      vecCapPtrDealloc A.repAlloc (BitVec.ofNat 64 auth.macKey.length) pa2 ∗
      A.pool lim st_af s3 ∗
      (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt) by sep_ac_rfl))) ?_
  have h2084 := Variant10aPlacedBudget.v10_states_from_pb_err_7212_placed hA st_af s0 s3 out
    (BitVec.ofNat 64 auth.rootKey.length) pa1 (BitVec.ofNat 64 auth.macKey.length) pa2
    (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 2064 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_3 hx26_3 htr3
  refine SepWP.seq h2084 ?_
  intro s4 P4 hpc4 hrun4 ⟨evs_err, hevs_err, hP4, hsp4, hx19_4, hx21_4, htr4⟩
  let st_err := M.stepEvents evs_err st_af
  have hfsp := v10_fsp_unsplit_1632 (s0.sp - 2400#64)
    ep pa2 (BitVec.ofNat 64 auth.rootKey.length) ga.macKey.ptr (b16.zeroExtend 32) v228
  refine SepWP.weaken_pre (Entails.trans hP4 (Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 152 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 24 ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 228#64) ↦₃₂ v228) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ga.macKey.ptr) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 2064) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ A.pool lim st_err s4 ∗
       (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))
      by dsimp only [st_err]; sep_ac_rfl))
    (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st_err s4 ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl))))) ?_
  have hx21_byte : (s4.readReg64 .x21).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx21_4]; rfl
  have herr := v10_states_from_pb_err_2084_placed_budget A lim st_err (F := F) (ext := ext)
    s0 s4 out .stateDecode
    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_byte htr4
  refine SepWP.mono herr ?_
  intro sf Pf _ _ ⟨hPf, _hvmf, hsp_f, hcs_f, htr_f⟩
  have hst_all :
      st_err = M.stepEvents (authFromPbEvents auth ++ (evs_af ++ evs_err)) st := by
    simp only [st_err, st_af, M.stepEvents_append]
  have henv : Ct2SampledFromPbEnv
      { uc := some { epoch := ep, auth := some auth }, sendingCt2 := none }
      (authFromPbEvents auth ++ (evs_af ++ evs_err)) :=
    ⟨evs_af ++ evs_err, freeOnlyEvs_append hevs_af hevs_err, rfl⟩
  exact ⟨authFromPbEvents auth ++ (evs_af ++ evs_err), henv,
    Entails.trans hPf (Entails.of_eq (by rw [hst_all]; sep_ac_rfl)),
    hsp_f, hcs_f, htr_f⟩

theorem v10_ct2Sent_sending_none_some_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out pbA ep : BitVec 64)
    (auth : ProtoAuthenticator) (onPanic : State → SepProp → Prop)
    (hfits_auth : FitsEvents M lim st (authFromPbEvents auth))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x800000000000000a#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
        memRegion (pbA + 16#64) 48 ∗ authenticatorPBAt A.repAlloc (pbA + 64#64) auth ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗ memRegion (pbA + 120#64) 104 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          Ct2SampledFromPbEnv
            { uc := some { epoch := ep, auth := some auth }, sendingCt2 := none } evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      onPanic :=
  SepWPp.of_sepWP_ret
    (v10_ct2Sent_sending_none_some_placed_sepWP hA st s0 s1 out pbA ep auth
      hfits_auth hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10dPlacedBudgetAux
