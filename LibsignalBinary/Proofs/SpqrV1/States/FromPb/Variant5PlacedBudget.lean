/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 5 (`NoHeaderReceived`, `+1344`)

Allocator event envelopes, `StatesFromPbEnv` subsumption, and total-correctness Block-`333`
`subroutine_ok` contracts for `InnerState.noHeaderReceived` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder ProtoAuthenticator
  ProtoPolynomialDecoder States V1State pbToProtoPolyDecoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeOptMessage)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize optProtoUnchunkedNoHeaderReceivedAt)
open CryptoVerification.SpqrV1.Poly (boolByte optProtoPolynomialDecoderAt polyDecoderAt
  polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack loByte)
open CryptoVerification.SpqrV1.States.FromPb
  (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 decoderFromPbResult
   decoderFromPbStack resultChunkedStatesAt statesFromPbJumpTablePlacedAt statesFromPbSavedCells
   statesFromPbStack v5_memRegion_160_merge_48 v5_memRegion_2068_join_err
   v5_memRegion_2068_split_dec v5_memRegion_240_merge_1648 v5_optProtoPolyDecoderHeap_none_dup
   v5_optProtoPolyDecoderHeap_some_dup v5a_optProtoInnerStateAt_noHeaderReceived
   v5a_optProtoInnerStateAt_unpack v5a_optProtoPolyDecoderHeap v5a_optProtoPolyDecoderWordsAt
   v5a_optProtoUcHeap v5a_pbAHeadersAt v5a_protoPolyDecoderAt_pack
   v5a_states_from_pb_noHeaderReceived_auth_none_dec_none
   v5a_states_from_pb_noHeaderReceived_auth_none_dec_some
   v5a_states_from_pb_noHeaderReceived_auth_some_dec_none
   v5a_states_from_pb_noHeaderReceived_auth_some_dec_some
   v5a_states_from_pb_noHeaderReceived_ptsNeeded_ne
   v5a_states_from_pb_noHeaderReceived_uc_none_dec_none
   v5a_states_from_pb_noHeaderReceived_uc_none_dec_some
   v5b_memRegion_2304_join_224_232 v5b_memRegion_2304_split_224_232 v5c_bs384_eq_decCells
   v5c_decCellsAt v5c_memRegion_40_to_polyDecoderWordsAt v9_pointsTo32_pair_eq_pointsTo64
   v9_polyDecoderAt_relocate v9_resultPolyDecoder_err_entails_tag_392 v9_wordAt)
open CryptoVerification.SpqrV1.Top.StateSize (length_le_encodeMessage length_le_encodeOptMessage
  optRaw rawUcNoHeaderReceived rawUcNoHeaderReceived_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget (FromPbDecAllocEnv FromPbDecEnv
  fromPbDecAllocEnv_imp_fromPbDecEnv fromPbDecLoopAllocEvents fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (spqrBoundedEvs_authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget (v5a_sub_ok_decoder_from_pb_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlacedBudget
  (v5b_step_1344_to_1396_err_placed_budget v5b_step_1344_to_3744_none_placed_budget
   v5b_step_1344_to_3744_some_placed_budget v5b_step_3744_auth_none_to_6420_placed_budget
   v5b_step_3744_uc_none_to_6420_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlacedBudget
  (v5c_noHeaderReceived_6132_ok_to_ret_of_placedHooks v5c_step_6064_none_to_6520_placed_budget
   v5c_step_6064_some_to_call_35448_placed_budget v5c_step_6132_err_to_6520_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5dPlacedBudget
  (v5_auth_some_3744_to_6064_of_placedHooks v5_err_1396_to_ret_of_placedHooks
   v5_err_6420_to_ret_of_placedHooks v5_err_6520_to_ret_of_placedHooks)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs nonFreeCount)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Tight Envelopes, `StatesFromPbEnv` Subsumption, and `SepWPp` Combinators -/

/-- Allocation-only event envelope for Variant 5 (`NoHeaderReceived`, `+1344`, Block `333`). -/
def NoHeaderReceivedFromPbAllocEnv (s : V1State.Chunked.NoHeaderReceived)
    (evs : List AllocEvent) : Prop :=
  match s.receivingHdr with
  | none =>
    match s.uc with
    | none => evs = []
    | some uc => match uc.auth with
      | none => evs = []
      | some authPb => evs = [] ∨ evs = authFromPbEvents authPb
  | some decPb =>
    if decPb.ptsNeeded = 48#32 then
      match s.uc with
      | none => evs = []
      | some uc => match uc.auth with
        | none => evs = []
        | some authPb => evs = [] ∨ ∃ evs_dec, FromPbDecAllocEnv (pbToProtoPolyDecoder decPb) evs_dec ∧
            evs = authFromPbEvents authPb ++ evs_dec
    else evs = []

/-- Complete allocator event envelope for Variant 5 (`NoHeaderReceived`, `+1344`, Block `333`). -/
def NoHeaderReceivedFromPbEnv (s : V1State.Chunked.NoHeaderReceived) (evs : List AllocEvent) : Prop :=
  match s.receivingHdr with
  | none =>
    match s.uc with
    | none => FreeOnlyEvs evs
    | some uc => match uc.auth with
      | none => FreeOnlyEvs evs
      | some authPb => ∃ evs_free, FreeOnlyEvs evs_free ∧ evs = authFromPbEvents authPb ++ evs_free
  | some decPb =>
    if decPb.ptsNeeded = 48#32 then
      match s.uc with
      | none => FreeOnlyEvs evs
      | some uc => match uc.auth with
        | none => FreeOnlyEvs evs
        | some authPb => ∃ evs_free0 evs_dec, FreeOnlyEvs evs_free0 ∧
            FromPbDecEnv (pbToProtoPolyDecoder decPb) evs_dec ∧
            evs = (authFromPbEvents authPb ++ evs_free0) ++ evs_dec
    else FreeOnlyEvs evs

theorem fromPbDecEnv_append_free {pb : ProtoPolynomialDecoder} {evs1 evs2 : List AllocEvent}
    (h1 : FromPbDecEnv pb evs1) (h2 : FreeOnlyEvs evs2) : FromPbDecEnv pb (evs1 ++ evs2) := by
  rcases h1 with ⟨ea, ef, rfl, ha, hf⟩
  exact ⟨ea, ef ++ evs2, List.append_assoc ea ef evs2, ha, hf.append h2⟩

theorem fitsEvents_auth_of_noHeaderReceivedEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ep : BitVec 64} {authPb : ProtoAuthenticator} {receivingHdr : Option PolynomialDecoder}
    (hd32_48 : ∀ decPb, receivingHdr = some decPb → decPb.ptsNeeded = 48#32)
    (hfits : FitsEnv M lim st (NoHeaderReceivedFromPbEnv
      { uc := some { auth := some authPb, epoch := ep }, receivingHdr := receivingHdr })) :
    FitsEvents M lim st (authFromPbEvents authPb) := by
  cases receivingHdr with
  | none => exact hfits (authFromPbEvents authPb) ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩
  | some decPb =>
    have h48 : decPb.ptsNeeded = 48#32 := hd32_48 decPb rfl
    refine hfits (authFromPbEvents authPb) ?_; unfold NoHeaderReceivedFromPbEnv
    simp only [h48, ↓reduceIte]
    exact ⟨[], [], FreeOnlyEvs.nil, fromPbDecAllocEnv_imp_fromPbDecEnv (Or.inl rfl), by simp⟩

theorem fitsEnv_decAlloc_of_noHeaderReceivedEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ep : BitVec 64} {authPb : ProtoAuthenticator} {decPb : PolynomialDecoder}
    {evs_free0 : List AllocEvent} (h48 : decPb.ptsNeeded = 48#32) (hfree0 : FreeOnlyEvs evs_free0)
    (hfits : FitsEnv M lim st (NoHeaderReceivedFromPbEnv
      { uc := some { auth := some authPb, epoch := ep }, receivingHdr := some decPb })) :
    FitsEnv M lim (M.stepEvents (authFromPbEvents authPb ++ evs_free0) st)
      (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)) := by
  intro evs_alloc halloc
  refine ((fitsEvents_append M lim (authFromPbEvents authPb ++ evs_free0) evs_alloc st).mp
    (hfits ((authFromPbEvents authPb ++ evs_free0) ++ evs_alloc) ?_)).2
  unfold NoHeaderReceivedFromPbEnv; simp only [h48, ↓reduceIte]
  exact ⟨evs_free0, evs_alloc, hfree0, fromPbDecAllocEnv_imp_fromPbDecEnv halloc, rfl⟩

private theorem spqrBoundedEvs_fromPbDecSlotEvents {bs : List (BitVec 8)}
    (hmod : bs.length % 4 = 0) (hmax : bs.length ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 bs.length (fromPbDecSlotEvents bs) := by
  unfold fromPbDecSlotEvents; split
  · exact SpqrBoundedEvs.nil 1 bs.length
  · rename_i hne
    have hpos : 1 ≤ bs.length := by
      cases bs with | nil => simp at hne | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have h2 : 2 ≤ bs.length := by omega
    have hre : rustAllocEvents bs.length 2 = [.alloc bs.length] := by simp [rustAllocEvents, h2]
    rw [hre]; refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨hmax, Nat.le_refl _, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_fromPbDecLoopAllocEvents
    (pts : List (List (BitVec 8))) (S : Nat) (hS_max : S ≤ MallocngMaxAllocSize)
    (hle : (pts.map List.length).sum ≤ S) :
    SpqrBoundedEvs pts.length S (fromPbDecLoopAllocEvents pts) := by
  unfold fromPbDecLoopAllocEvents; induction pts with
  | nil => exact SpqrBoundedEvs.nil 0 S
  | cons bs rest ih =>
    simp only [List.map_cons, List.sum_cons] at hle; simp only [List.takeWhile_cons]; split
    · rename_i hmod_b; rw [List.flatMap_cons]
      have h1 : SpqrBoundedEvs 1 S (fromPbDecSlotEvents bs) := SpqrBoundedEvs.mono (Nat.le_refl 1)
        (by omega) (spqrBoundedEvs_fromPbDecSlotEvents (beq_iff_eq.mp hmod_b) (by omega))
      exact SpqrBoundedEvs.mono (by simp [List.length_cons]; omega) (by omega)
        (SpqrBoundedEvs.append h1 (ih (by omega)))
    · exact SpqrBoundedEvs.nil _ S

private theorem spqrBoundedEvs_fromPbDecEnv (decPb : PolynomialDecoder) (S : Nat)
    (hS_max : S ≤ MallocngMaxAllocSize) (hle : (decPb.pts.map List.length).sum ≤ S)
    {evs : List AllocEvent} (hevs : FromPbDecEnv (pbToProtoPolyDecoder decPb) evs) :
    SpqrBoundedEvs 16 S evs := by
  rcases hevs with ⟨ea, ef, rfl, ha, hf⟩
  have hba : SpqrBoundedEvs 16 S ea := by
    rcases ha with rfl | ⟨hlen16, rfl⟩
    · exact SpqrBoundedEvs.nil 16 S
    · have hloop := spqrBoundedEvs_fromPbDecLoopAllocEvents
        (pbToProtoPolyDecoder decPb).pts S hS_max (by simpa [pbToProtoPolyDecoder] using hle)
      rwa [hlen16] at hloop
  exact SpqrBoundedEvs.mono (by omega) (by omega)
    (SpqrBoundedEvs.append hba (SpqrBoundedEvs.of_freeOnly hf))

private theorem rawAuth_le_noHeaderReceived_encodeRaw
    (ep : BitVec 64) (authPb : ProtoAuthenticator) (receivingHdr : Option PolynomialDecoder) :
    authPb.rootKey.length + authPb.macKey.length ≤
      (V1State.encodeRaw { innerState := some (.noHeaderReceived
        { uc := some { auth := some authPb, epoch := ep }, receivingHdr := receivingHdr }) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.NoHeaderReceived.encodeRaw 6#32
    { uc := some { auth := some authPb, epoch := ep }, receivingHdr := receivingHdr }
  have h1 := length_le_encodeOptMessage _ rawUcNoHeaderReceived rawUcNoHeaderReceived_le_encodeRaw
    1#32 (some ({ auth := some authPb, epoch := ep } : V1State.Unchunked.NoHeaderReceived))
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.NoHeaderReceived.encodeRaw, rawUcNoHeaderReceived, optRaw,
    CryptoVerification.SpqrV1.Top.StateSize.rawAuth] at h0 h1 ⊢
  rw [List.length_append] at h0; omega

private theorem rawAuth_pts_le_noHeaderReceived_encodeRaw
    (ep : BitVec 64) (authPb : ProtoAuthenticator) (decPb : PolynomialDecoder) :
    authPb.rootKey.length + authPb.macKey.length + (decPb.pts.map List.length).sum ≤
      (V1State.encodeRaw { innerState := some (.noHeaderReceived
        { uc := some { auth := some authPb, epoch := ep }, receivingHdr := some decPb }) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.NoHeaderReceived.encodeRaw 6#32
    { uc := some { auth := some authPb, epoch := ep }, receivingHdr := some decPb }
  have h1 := length_le_encodeOptMessage _ rawUcNoHeaderReceived rawUcNoHeaderReceived_le_encodeRaw
    1#32 (some ({ auth := some authPb, epoch := ep } : V1State.Unchunked.NoHeaderReceived))
  have h2 : (PolynomialDecoder.encodeRaw decPb).length ≤
      (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 (some decPb)).length :=
    length_le_encodeMessage PolynomialDecoder.encodeRaw 2#32 decPb
  have h3 := sum_length_le_encodeRepeatedBytes 3#32 decPb.pts
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.NoHeaderReceived.encodeRaw, PolynomialDecoder.encodeRaw,
    rawUcNoHeaderReceived, optRaw, CryptoVerification.SpqrV1.Top.StateSize.rawAuth] at h0 h1 h2 h3 ⊢
  simp only [List.length_append] at h0 h2; omega

private theorem encodeRaw_le_maxAlloc_of_fits_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (s : V1State.Chunked.NoHeaderReceived)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.noHeaderReceived s) })) :
    (V1State.encodeRaw { innerState := some (.noHeaderReceived s) }).length ≤
      MallocngMaxAllocSize := by
  let pb : V1State := { innerState := some (.noHeaderReceived s) }
  let S := (V1State.encodeRaw pb).length
  let m := min S MallocngMaxAllocSize
  have hm_env : StatesFromPbEnv pb [.alloc m] := by
    change SpqrBoundedEvs 128 (4 * S + 4096) [.alloc m]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨Nat.min_le_right _ _, Nat.le_trans (Nat.min_le_left _ _) (by omega),
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  rcases hfits [.alloc m] hm_env with ⟨⟨_, _, _, hva⟩, _⟩
  have hm_req : m ≤ M.stepReserve (.alloc m) st := M.req_le_stepReserve (.alloc m) st
  dsimp only [pb, m, S, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢; omega

theorem noHeaderReceivedFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (s : V1State.Chunked.NoHeaderReceived)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.noHeaderReceived s) }))
    {evs : List AllocEvent} (hevs : NoHeaderReceivedFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.noHeaderReceived s) } evs := by
  have hS_max : (V1State.encodeRaw { innerState := some (.noHeaderReceived s) }).length ≤
      MallocngMaxAllocSize := encodeRaw_le_maxAlloc_of_fits_statesFromPbEnv s hfits
  change SpqrBoundedEvs 128
    (4 * (V1State.encodeRaw { innerState := some (.noHeaderReceived s) }).length + 4096) evs
  rcases s with ⟨uc, receivingHdr⟩; cases receivingHdr with
  | none =>
    cases uc with
    | none => exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
    | some ucVal =>
      rcases ucVal with ⟨ep, optAuth⟩; cases optAuth with
      | none => exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
      | some authPb =>
        rcases hevs with ⟨evs_free, hfree, rfl⟩
        have hlen := rawAuth_le_noHeaderReceived_encodeRaw ep authPb none
        have hb_auth : SpqrBoundedEvs 2 (max authPb.rootKey.length authPb.macKey.length)
            (authFromPbEvents authPb) :=
          SpqrBoundedEvs.append (spqrBoundedEvs_authKeyCloneEvents (by omega))
            (spqrBoundedEvs_authKeyCloneEvents (by omega))
        exact SpqrBoundedEvs.mono (by decide) (by omega)
          (SpqrBoundedEvs.append hb_auth (SpqrBoundedEvs.of_freeOnly hfree))
  | some decPb =>
    unfold NoHeaderReceivedFromPbEnv at hevs
    by_cases h48 : decPb.ptsNeeded = 48#32
    · simp only [h48, ↓reduceIte] at hevs; cases uc with
      | none => exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
      | some ucVal =>
        rcases ucVal with ⟨ep, optAuth⟩; cases optAuth with
        | none => exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
        | some authPb =>
          rcases hevs with ⟨evs_free0, evs_dec, hfree0, hdec, rfl⟩
          have hlen := rawAuth_pts_le_noHeaderReceived_encodeRaw ep authPb decPb
          have hb_auth0 : SpqrBoundedEvs 2 (max (max authPb.rootKey.length authPb.macKey.length) 0)
              (authFromPbEvents authPb ++ evs_free0) :=
            SpqrBoundedEvs.append
              (SpqrBoundedEvs.append (spqrBoundedEvs_authKeyCloneEvents (by omega))
                (spqrBoundedEvs_authKeyCloneEvents (by omega)))
              (SpqrBoundedEvs.of_freeOnly hfree0)
          exact SpqrBoundedEvs.mono (by decide) (by omega)
            (SpqrBoundedEvs.append hb_auth0 (spqrBoundedEvs_fromPbDecEnv decPb _ hS_max (by omega) hdec))
    · simp only [h48, ↓reduceIte] at hevs
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)

theorem fitsEnv_noHeaderReceived_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (s : V1State.Chunked.NoHeaderReceived)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.noHeaderReceived s) })) :
    FitsEnv M lim st (NoHeaderReceivedFromPbEnv s) :=
  fun evs hevs => hfits evs (noHeaderReceivedFromPbEnv_sub_statesFromPbEnv s hfits hevs)

private theorem v5_sepWPp_seq_st_lscl [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P : SepProp} {Q post Qpan : State → SepProp → Prop} (h1 : SepWP prog mid s P Q)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm Pm → SepWPp prog target_pc sm Pm post Qpan) :
    SepWPp prog target_pc s P post Qpan :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun hQ hcl' => h2 sm Pm hpc hrun hcl' hQ)

private theorem v5_sepWPp_call_noPanic_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F : SepProp} {Qp post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post Qp := by
  refine SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp_align hlr ?_ ?_ ?_ ?_ (hoom := ?_)
  · intro R' hm; rw [sepConj_assoc] at hm; dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; exact ⟨hcl, hpre (F ∗ R') hm⟩
  · intro sf code R' _ hpost; dsimp only [withLsCodeLoaded] at hpost; rw [hexit_eq] at hpost
    exact not_satisfies_false_sepConj hpost
  · rintro sf _ ⟨R', hm_f⟩; dsimp only [withLsCodeLoaded] at hm_f; rw [hpan_eq] at hm_f
    exact (not_satisfies_false_sepConj hm_f).elim
  · intro sf hpcm hrunm hspm hcsm; exact SepWPp.of_sepWP_ret (hnext sf hpcm hrunm hspm hcsm)
  · intro sf R' _ hpost; dsimp only [withLsCodeLoaded] at hpost; rw [hoom_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

private theorem v5_sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) (hm : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' Qp := by
  intro R hmem hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, Pf, hmf, hq⟩ | hpan⟩ := h R hmem hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, Pf, hmf, hm sf Pf hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

private theorem v5_sepWP_weaken_mono {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Q' : State → SepProp → Prop} {oom : State → SepProp}
    (hw : SepWP prog ret s P2 Q oom) (himp : P1 ⊢ P2)
    (hm : ∀ sf Pf, sf.pc = ret → sf.status = .Running → Q sf Pf → Q' sf Pf) :
    SepWP prog ret s P1 Q' oom :=
  SepWP.mono (SepWP.weaken_pre himp hw) hm

/-! ## Budget-Threaded `<PolyDecoder>::from_pb` Continuation (`+6064 -> s0.x30`) -/

/-- Shared return postcondition for Variant 5 (`NoHeaderReceived`) continuations. -/
abbrev v5_post_ret [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (Env : List AllocEvent → Prop)
    (st : M.σ) (s0 : State) (out pbA : BitVec 64) (s : V1State.Chunked.NoHeaderReceived) :
    State → SepProp → Prop := fun sf Pf =>
  (∃ evs : List AllocEvent, Env evs ∧
    (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
        (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.noHeaderReceived s) }) ∗
      memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

/-- Precondition of `+6064` when `receivingHdr = some decPb` and `decPb.ptsNeeded = 48#32`. -/
abbrev v5_pre_6064_some [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s1 : State)
    (out pbA p1_new p2_new ep w8 w16 w24 w40 w80 : BitVec 64) (d36 : BitVec 32)
    (authPb : ProtoAuthenticator) (decPb : PolynomialDecoder) : SepProp :=
  v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
    w8 w16 w24 48#32 d36 w40 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
  memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
  memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
  memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
  (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
  (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
  (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
  memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
  vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
  vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
  statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
  memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1

/-- At `+6064`, stages `ProtoPolynomialDecoder`, calls `<PolyDecoder>::from_pb`, and finishes. -/
theorem v5_noHeaderReceived_6064_some_to_ret_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (st : M.σ) (s0 s1 : State)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA p1_new p2_new ep w8 w16 w24 w40 w80 : BitVec 64) (d36 : BitVec 32)
    (authPb : ProtoAuthenticator) (decPb : PolynomialDecoder)
    (hfits_dec : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)))
    (heq48 : (decPb.ptsNeeded == 48#32) = true) (_hr_lt63 : authPb.rootKey.length < 2 ^ 63)
    (_hm_lt63 : authPb.macKey.length < 2 ^ 63)
    (hl1_lt : (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6064#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx22_1 : s1.readReg64 .x22 = w16) (hx23_1 : s1.readReg64 .x23 = w8)
    (hx25_1 : s1.readReg64 .x25 = (48#32).zeroExtend 64) (hx27_1 : s1.readReg64 .x27 = p1_new)
    (hx28_1 : s1.readReg64 .x28 = w24) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5_pre_6064_some A lim st s0 s1 out pbA p1_new p2_new ep w8 w16 w24 w40 w80 d36 authPb decPb)
      (v5_post_ret A lim F (FromPbDecEnv (pbToProtoPolyDecoder decPb)) st s0 out pbA
        { uc := some { auth := some authPb, epoch := ep }, receivingHdr := some decPb }) Qp := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hpack := v5a_protoPolyDecoderAt_pack A.repAlloc
    ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyDecoder decPb) w8 w16 w24 48#32 d36 w40
  dsimp only [v5_pre_6064_some]
  refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_left
    (v5_optProtoPolyDecoderHeap_some_dup A.repAlloc (pbToProtoPolyDecoder decPb) w8 w16 w24 48#32 d36 w40))
    (Entails.of_eq (by sep_ac_rfl))) ?_
  refine SepWPp.pure_left fun ⟨_, hw8_lt⟩ => ?_
  have h2068_split : memRegion ((s0.sp - 2400#64) + 236#64) 2068 ⊢
      (∃∗ z236 : BitVec 32, ((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗
      memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
      (∃∗ z0 : BitVec 64, ∃∗ z8 : BitVec 64, ∃∗ z16 : BitVec 64, ∃∗ zd24 : BitVec 32,
       ∃∗ zd28 : BitVec 32, ∃∗ z32 : BitVec 64,
         v5a_optProtoPolyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64) z0 z8 z16 zd24 zd28 z32) ∗
      memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 :=
    Entails.trans (v5_memRegion_2068_split_dec (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v5c_memRegion_40_to_polyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64)))))
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
    (v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
       w8 w16 w24 48#32 d36 w40 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
     memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
     (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
     (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by
      sep_ac_rfl)) (sepConj_mono_left h2068_split)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun z0 => SepWPp.exists_elim fun z8 => SepWPp.exists_elim fun z16 =>
    SepWPp.exists_elim fun zd24 => SepWPp.exists_elim fun zd28 => SepWPp.exists_elim fun z32 =>
    SepWPp.exists_elim fun z236 => ?_
  let R_post_call : SepProp :=
    (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
    (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗
    memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
    memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
    memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
    memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
    (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
    (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
  let Rest_copy : SepProp :=
    v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
      w8 w16 w24 48#32 d36 w40 ∗ (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗
    memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1432#64) 456 ∗
    memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 136 ∗
    (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
    (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
    (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
    (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
    v5a_optProtoPolyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64) z0 z8 z16 zd24 zd28 z32 ∗
    Rest_copy ∗ A.pool lim st s1 by dsimp only [Rest_copy]; try sep_ac_rfl)) ?_
  have hcopy := v5c_step_6064_some_to_call_35448_placed_budget A lim st (ext := ext) s0 s1
    (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.rootKey.length) p1_new w8 w16 w24 w40 d36
    z0 z8 z16 zd24 zd28 z32 Rest_copy
    hfsp_align hl1_lt hw8_lt hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 htr1
  refine v5_sepWPp_seq_st_lscl hcl1 hcopy ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, hx0_2, hx1_2, hx19_2, hx20_2, hx21_2, hx27_2, hx30_2, htr2, _⟩
  refine SepWPp.weaken_pre (Entails.trans hP2 (Entails.trans (Entails.of_eq (show _ =
      (v5a_optProtoPolyDecoderWordsAt ((s0.sp - 2400#64) + 1392#64) w8 w16 w24 48#32 d36 w40 ∗
       v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
         w8 w16 w24 48#32 d36 w40) ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ A.pool lim st s2 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ R_post_call) by
        dsimp only [Rest_copy, R_post_call]; try sep_ac_rfl))
    (Entails.trans (sepConj_mono_left hpack) (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) (pbToProtoPolyDecoder decPb) ∗
       A.pool lim st s2 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗
      R_post_call by sep_ac_rfl))))) ?_
  have hsub := v5a_sub_ok_decoder_from_pb_placed hDec
  have hsp2_align : s2.spAligned = true := by unfold State.spAligned; rw [hsp2]; exact hfsp_align
  refine v5_sepWPp_call_noPanic_lscl hsub
    (x := ({ out := (s0.sp - 2400#64) + 1888#64, pbA := (s0.sp - 2400#64) + 1392#64,
             pb := pbToProtoPolyDecoder decPb }, st)) hcl2 hpc2 hrun2 hsp2_align hx30_2
    (fun R' hm => Satisfies.mono (sepConj_mono_left (Entails.pure_right ⟨hx0_2, hx1_2, hfits_dec,
      by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s2.readReg64 .x30); rw [show s2.readReg64 .x30 = _ from hx30_2]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩
      (by dsimp only [polyDecoderSize, decoderFromPbStack]; rw [hsp2]; exact Entails.refl _))) hm) ?_
  intro s3 hpc3 hrun3 hsp3_2 hcs23
  simp only [DefsBudget.decoderFromPbSpec, protoPolynomialDecoderSize, decoderFromPbStack,
    R_post_call, sepExists_sepConj_left, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun evs_dec0 => ?_
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr3_2, _, hdec_env0⟩; let st_dec := M.stepEvents evs_dec0 st
  have hsp3 : s3.sp = s0.sp - 2400#64 := hsp3_2.trans hsp2
  have hx19_3 : s3.readReg64 .x19 = out := (hcs23.1).trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = (s0.sp - 2400#64) + 1888#64 := (hcs23.2.1).trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 authPb.rootKey.length := (hcs23.2.2.1).trans hx21_2
  have hx27_3 : s3.readReg64 .x27 = p1_new := (hcs23.2.2.2.2.2.2.2.2.1).trans hx27_2
  have htr3 : TraceCalleeSaved s3 s0 := ⟨htr3_2.trans htr2.1, hcs23.2.2.2.2.2.2.2.2.2.2.2.trans htr2.2⟩
  have hm1648 := v5_memRegion_240_merge_1648 (s0.sp - 2400#64)
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    (memRegion ((s0.sp - 2400#64) + 240#64) 1152 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
     memRegion ((s0.sp - 2400#64) + 1432#64) 456) ∗
    resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
      (decoderFromPbResult (pbToProtoPolyDecoder decPb)) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
     (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
     (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗ memRegion (s0.sp - 2400#64) 136 ∗
     (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
     (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
     (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool lim st_dec s3) by
      dsimp only [st_dec]; rw [hsp2]; sep_ac_rfl)) (sepConj_mono_left hm1648)) ?_
  unfold v5_post_ret; rw [v5a_states_from_pb_noHeaderReceived_auth_some_dec_some F authPb ep decPb heq48]
  cases hres : decoderFromPbResult (pbToProtoPolyDecoder decPb) with
  | error err =>
    let Rest_6132 : SepProp :=
      memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 136 ∗
      (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
      (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
    refine SepWP.weaken_pre (Entails.trans
      (sepConj_mono_right (sepConj_mono_left
        (v9_resultPolyDecoder_err_entails_tag_392 A.repAlloc (s0.sp - 2400#64) err)))
      (Entails.of_eq (show _ =
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗ Rest_6132 ∗ A.pool lim st_dec s3 by
          dsimp only [Rest_6132]; try sep_ac_rfl))) ?_
    have h6520 := v5c_step_6132_err_to_6520_placed_budget A lim st_dec (ext := ext) s0 s3
      (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.rootKey.length) p1_new Rest_6132
      hfsp_align hpc3 hrun3 hsp3 hx19_3 hx21_3 hx27_3 htr3
    refine SepWP.seq h6520 ?_; rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx21_4, hx27_4, htr4, _⟩
    have hj2068 := v5_memRegion_2068_join_err (s0.sp - 2400#64) z236 noneCap
    have herr := v5_err_6520_to_ret_of_placedHooks (F := F) hA st_dec s0 s4
      out p1_new p2_new (BitVec.ofNat 64 authPb.rootKey.length)
      (BitVec.ofNat 64 authPb.macKey.length) ep w80 w40 d36 authPb.rootKey authPb.macKey
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx27_4 htr4
    refine v5_sepWP_weaken_mono herr (Entails.trans hP4 (Entails.trans (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64) + 236#64) ↦₃₂ z236) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗
         (((s0.sp - 2400#64) + 1888#64) ↦₆₄ noneCap) ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 136 ∗
         (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
         vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st_dec s4 ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by
          dsimp only [Rest_6132]; try sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hj2068) (Entails.of_eq (by sep_ac_rfl)))))
      fun sf Pf _ _ ⟨evs_free1, hfree1, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
    refine ⟨⟨evs_dec0 ++ evs_free1, fromPbDecEnv_append_free hdec_env0 hfree1, ?_⟩, hsp_f, hcs_f, htr_f⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by dsimp only [st_dec]; try sep_ac_rfl))
  | ok dec =>
    dsimp only [resultPolyDecoderFromPbAt]
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left
      (v9_polyDecoderAt_relocate A.repAlloc ((s0.sp - 2400#64) + 1888#64) (out + 64#64) dec))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun bs => ProofLib.SepWP.exists_left fun w392 =>
      ProofLib.SepWP.exists_left fun P_heap => ?_
    have hm160 := v5_memRegion_160_merge_48 (s0.sp - 2400#64) w80
    have hm232 := v9_pointsTo32_pair_eq_pointsTo64 ((s0.sp - 2400#64) + 232#64) d36 z236
    have ha236 : ((s0.sp - 2400#64) + 232#64) + 4#64 = (s0.sp - 2400#64) + 236#64 := by bv_omega
    have ha2272 : ((s0.sp - 2400#64) + 1888#64) + 384#64 = (s0.sp - 2400#64) + 2272#64 := by bv_omega
    have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
    rw [ha236] at hm232
    rw [v5c_bs384_eq_decCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64), ha2272, ha2280]
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      ⌜(v9_wordAt bs.val 0).toNat < 2 ^ 63 ∧ loByte w392 = boolByte dec.isComplete ∧
        (((out + 64#64) ↦ₛ bs.val) ∗ (((out + 64#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
         (((out + 64#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A.repAlloc (out + 64#64) dec)⌝ ∗
      (memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80)) ∗
      ((((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ (((s0.sp - 2400#64) + 236#64) ↦₃₂ z236)) ∗
      (memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion out chunkedStatesSize ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
       (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ v5c_decCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
       (((s0.sp - 2400#64) + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ w392) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
       vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
       A.pool lim st_dec s3 ∗
       (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono hm160 (sepConj_mono_left (Entails.of_eq hm232))))) ?_
    apply ProofLib.SepWP.pure_elim; rintro ⟨hw0_lt, _, hreloc_out⟩
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 160#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648) ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
      (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
      (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ (z236 ++ d36)) ∗
      v5c_decCellsAt ((s0.sp - 2400#64) + 1888#64) bs.val ∗
      (((s0.sp - 2400#64) + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      (((s0.sp - 2400#64) + 2280#64) ↦₆₄ w392) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      statesFromPbSavedCells s0 ∗ P_heap ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
      vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
      A.pool lim st_dec s3 ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
    have hok := v5c_noHeaderReceived_6132_ok_to_ret_of_placedHooks (F := F) hA st_dec s0 s3
      (s0.sp - 2400#64) out ep p1_new (BitVec.ofNat 64 authPb.rootKey.length)
      p2_new (BitVec.ofNat 64 authPb.macKey.length) w40 (z236 ++ d36) w392
      bs.val bs.property hw0_lt dec P_heap hreloc_out authPb.rootKey authPb.macKey rfl rfl
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align rfl hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx27_3 htr3
    refine SepWP.mono hok fun sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, _⟩ =>
      ⟨⟨evs_dec0, hdec_env0, Entails.trans hPf (Entails.of_eq (by dsimp only [st_dec]; try sep_ac_rfl))⟩,
       hsp_f, hcs_f, htr_f⟩

theorem v5_noHeaderReceived_6064_some_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext) (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA p1_new p2_new ep w8 w16 w24 w40 w80 : BitVec 64) (d36 : BitVec 32)
    (authPb : ProtoAuthenticator) (decPb : PolynomialDecoder)
    (hfits_dec : FitsEnv M lim st (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)))
    (heq48 : (decPb.ptsNeeded == 48#32) = true)
    (hr_lt63 : authPb.rootKey.length < 2 ^ 63) (hm_lt63 : authPb.macKey.length < 2 ^ 63)
    (hl1_lt : (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6064#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length)
    (hx22_1 : s1.readReg64 .x22 = w16) (hx23_1 : s1.readReg64 .x23 = w8)
    (hx25_1 : s1.readReg64 .x25 = (48#32).zeroExtend 64) (hx27_1 : s1.readReg64 .x27 = p1_new)
    (hx28_1 : s1.readReg64 .x28 = w24) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5_pre_6064_some A lim st s0 s1 out pbA p1_new p2_new ep w8 w16 w24 w40 w80 d36 authPb decPb)
      (v5_post_ret A lim F (FromPbDecEnv (pbToProtoPolyDecoder decPb)) st s0 out pbA
        { uc := some { auth := some authPb, epoch := ep }, receivingHdr := some decPb }) Qp :=
  v5_noHeaderReceived_6064_some_to_ret_of_placedHooks hA.toPlacedBudget hDec st s0 s1 hcl1
    out pbA p1_new p2_new ep w8 w16 w24 w40 w80 d36 authPb decPb hfits_dec heq48
    hr_lt63 hm_lt63 hl1_lt hsp0_align hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 htr1

/-! ## Unified `+3744 -> s0.x30` & Variant 5 `+1344 -> s0.x30` Theorems -/

/-- Precondition of `+3744` before `uc` / `auth` / `receivingHdr` dispatch. -/
abbrev v5_pre_3744 [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s1 : State)
    (out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived) (receivingHdr : Option PolynomialDecoder) :
    SepProp :=
  v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
  v5a_optProtoPolyDecoderHeap A.repAlloc (receivingHdr.map pbToProtoPolyDecoder)
    w8 w16 w24 d32 d36 w40 ∗
  stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
  (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
  memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
  memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
  statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1

/-- Unified budget-threaded continuation from `+3744` to `s0.x30`. -/
theorem v5_noHeaderReceived_3744_to_ret_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived) (receivingHdr : Option PolynomialDecoder)
    (hfits : FitsEnv M lim st (NoHeaderReceivedFromPbEnv { uc := uc, receivingHdr := receivingHdr }))
    (hd32_48 : ∀ decPb, receivingHdr = some decPb → d32 = 48#32 ∧ (decPb.ptsNeeded == 48#32) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3744#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = w16) (hx23_1 : s1.readReg64 .x23 = w8)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32.zeroExtend 64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = w24) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5_pre_3744 A lim st s0 s1 out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36
        uc receivingHdr)
      (v5_post_ret A lim F (NoHeaderReceivedFromPbEnv { uc := uc, receivingHdr := receivingHdr })
        st s0 out pbA { uc := uc, receivingHdr := receivingHdr }) Qp := by
  dsimp only [v5_pre_3744]
  have hj2304 := v5b_memRegion_2304_join_224_232 (s0.sp - 2400#64) w40 d36
  let Frame_6420 : SepProp :=
    v5a_optProtoPolyDecoderHeap A.repAlloc (receivingHdr.map pbToProtoPolyDecoder)
      w8 w16 w24 d32 d36 w40 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
    memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
  cases uc with
  | none =>
    unfold v5_post_ret
    have hres_eq : States.from_pb spqrPolyApi (spqrAuthApi F)
        { innerState := some (.noHeaderReceived { uc := none, receivingHdr := receivingHdr }) } =
        .error (.err .stateDecode) := by
      cases receivingHdr with
      | none => exact v5a_states_from_pb_noHeaderReceived_uc_none_dec_none F
      | some decPb =>
        exact v5a_states_from_pb_noHeaderReceived_uc_none_dec_some F decPb (hd32_48 decPb rfl).2
    rw [hres_eq]; dsimp only [v5a_optProtoUcHeap]; refine SepWPp.pure_left fun hw48 => ?_
    rw [hw48] at hx24_1; apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 224 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
      (A.pool lim st s1 ∗ (v5a_optProtoPolyDecoderHeap A.repAlloc
         (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hj2304) (Entails.of_eq (show _ =
        A.pool lim st s1 ∗ Frame_6420 by dsimp only [Frame_6420]; try sep_ac_rfl)))) ?_
    have h6420 := v5b_step_3744_uc_none_to_6420_placed_budget A lim st (ext := ext) s0 s1
      (s0.sp - 2400#64) out w16 w8 w24 Frame_6420 hpc1 hrun1 hsp1
      hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
    refine SepWP.seq h6420 ?_; rintro s2 P2 hpc2 hrun2 ⟨hP2, _, hpres2, hx28_2⟩
    have herr := v5_err_6420_to_ret_of_placedHooks (F := F) hA st s0 s2 out w8 w16 w24 w40 d32 d36
      receivingHdr (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc2 hrun2 hpres2 hx28_2
    refine v5_sepWP_weaken_mono herr
      (Entails.trans hP2 (Entails.of_eq (by dsimp only [Frame_6420]; try sep_ac_rfl)))
      fun sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
    refine ⟨⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
    cases receivingHdr with
    | none => exact hfree
    | some decPb =>
      have h48 : decPb.ptsNeeded = 48#32 := beq_iff_eq.mp (hd32_48 decPb rfl).2
      unfold NoHeaderReceivedFromPbEnv; simp only [h48, ↓reduceIte]; exact hfree
  | some ucVal =>
    rcases ucVal with ⟨ep, optAuth⟩; cases optAuth with
    | none =>
      unfold v5_post_ret
      have hres_eq : States.from_pb spqrPolyApi (spqrAuthApi F)
          { innerState := some (.noHeaderReceived
              { uc := some { auth := none, epoch := ep }, receivingHdr := receivingHdr }) } =
          .error (.err .stateDecode) := by
        cases receivingHdr with
        | none => exact v5a_states_from_pb_noHeaderReceived_auth_none_dec_none F ep
        | some decPb =>
          exact v5a_states_from_pb_noHeaderReceived_auth_none_dec_some F ep decPb (hd32_48 decPb rfl).2
      rw [hres_eq]; dsimp only [v5a_optProtoUcHeap]; refine SepWPp.pure_left fun ⟨hw48, _⟩ => ?_
      rw [hw48] at hx24_1; apply SepWPp.of_sepWP_ret
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 224 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
        (A.pool lim st s1 ∗ (v5a_optProtoPolyDecoderHeap A.repAlloc
           (receivingHdr.map pbToProtoPolyDecoder) w8 w16 w24 d32 d36 w40 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt))) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hj2304) (Entails.of_eq (show _ =
          A.pool lim st s1 ∗ Frame_6420 by dsimp only [Frame_6420]; try sep_ac_rfl)))) ?_
      have h6420 := v5b_step_3744_auth_none_to_6420_placed_budget A lim st (ext := ext) s0 s1
        (s0.sp - 2400#64) out w16 w8 w24 Frame_6420 hpc1 hrun1 hsp1
        hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
      refine SepWP.seq h6420 ?_; rintro s2 P2 hpc2 hrun2 ⟨hP2, _, hpres2, hx28_2⟩
      have herr := v5_err_6420_to_ret_of_placedHooks (F := F) hA st s0 s2 out w8 w16 w24 w40 d32 d36
        receivingHdr (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc2 hrun2 hpres2 hx28_2
      refine v5_sepWP_weaken_mono herr
        (Entails.trans hP2 (Entails.of_eq (by dsimp only [Frame_6420]; try sep_ac_rfl)))
        fun sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
      refine ⟨⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
      cases receivingHdr with
      | none => exact hfree
      | some decPb =>
        have h48 : decPb.ptsNeeded = 48#32 := beq_iff_eq.mp (hd32_48 decPb rfl).2
        unfold NoHeaderReceivedFromPbEnv; simp only [h48, ↓reduceIte]; exact hfree
    | some authPb =>
      have hfits_auth : FitsEvents M lim st (authFromPbEvents authPb) :=
        fitsEvents_auth_of_noHeaderReceivedEnv (fun decPb h => beq_iff_eq.mp (hd32_48 decPb h).2) hfits
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        v5a_optProtoUcHeap A.repAlloc (some { auth := some authPb, epoch := ep })
          w48 w56 w64 w72 w80 w88 w96 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 224 ∗ A.pool lim st s1 ∗
        (v5a_optProtoPolyDecoderHeap A.repAlloc (receivingHdr.map pbToProtoPolyDecoder)
           w8 w16 w24 d32 d36 w40 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
      have h6064 := v5_auth_some_3744_to_6064_of_placedHooks hA st s0 s1
        out w16 w8 w24 (d32.zeroExtend 64) w48 w56 w64 w72 w80 w88 w96 ep authPb
        (v5a_optProtoPolyDecoderHeap A.repAlloc (receivingHdr.map pbToProtoPolyDecoder)
           w8 w16 w24 d32 d36 w40 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hfits_auth hsp0_align hpc1 hrun1 hsp1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1
        hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1
      refine v5_sepWPp_seq_st_lscl hcl1 h6064 ?_
      rintro s2 P2 hpc2 hrun2 hcl2
        ⟨evs_free0, p1_new, p2_new, hfree0, hr_lt63, hm_lt63, hl1_lt, hP2,
         hsp2, hx19_2, hx20_2, hx22_2, hx23_2, hx25_2, hx27_2, hx28_2, htr2⟩
      let st_auth := M.stepEvents (authFromPbEvents authPb ++ evs_free0) st
      cases receivingHdr with
      | none =>
        unfold v5_post_ret
        rw [v5a_states_from_pb_noHeaderReceived_auth_some_dec_none F authPb ep]
        dsimp only [Option.map, v5a_optProtoPolyDecoderHeap] at hP2
        let Rest_6520 : SepProp :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
          memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
          memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
          (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
          (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗
          memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
          vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        refine SepWPp.weaken_pre (Entails.trans hP2 (Entails.of_eq (show _ =
          ⌜w8 = noneCap⌝ ∗ (Rest_6520 ∗ A.pool lim st_auth s2) by
            dsimp only [Rest_6520, st_auth]; try sep_ac_rfl))) ?_
        refine SepWPp.pure_left fun hw8 => ?_; rw [hw8] at hx23_2; apply SepWPp.of_sepWP_ret
        have h6520 := v5c_step_6064_none_to_6520_placed_budget A lim st_auth (ext := ext) s0 s2
          (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.rootKey.length) p1_new Rest_6520
          hl1_lt hpc2 hrun2 hsp2 hx19_2 hx20_2 hx23_2 hx27_2 htr2
        refine SepWP.seq h6520 ?_; rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx21_3, hx27_3, htr3, _⟩
        have herr := v5_err_6520_to_ret_of_placedHooks (F := F) hA st_auth s0 s3
          out p1_new p2_new (BitVec.ofNat 64 authPb.rootKey.length)
          (BitVec.ofNat 64 authPb.macKey.length) ep w80 w40 d36 authPb.rootKey authPb.macKey
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_3 hx27_3 htr3
        refine v5_sepWP_weaken_mono herr
          (Entails.trans hP3 (Entails.of_eq (by dsimp only [Rest_6520]; try sep_ac_rfl)))
          fun sf Pf _ _ ⟨evs_free1, hfree1, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
        refine ⟨⟨authFromPbEvents authPb ++ (evs_free0 ++ evs_free1),
          ⟨evs_free0 ++ evs_free1, hfree0.append hfree1, rfl⟩, ?_⟩, hsp_f, hcs_f, htr_f⟩
        have hstep_eq : M.stepEvents (authFromPbEvents authPb ++ (evs_free0 ++ evs_free1)) st =
            M.stepEvents evs_free1 st_auth := by
          dsimp only [st_auth]; rw [← List.append_assoc, M.stepEvents_append]
        rw [hstep_eq]; exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
      | some decPb =>
        rcases hd32_48 decPb rfl with ⟨rfl, heq48⟩
        have h48 : decPb.ptsNeeded = 48#32 := beq_iff_eq.mp heq48
        have hfits_dec : FitsEnv M lim st_auth (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)) :=
          fitsEnv_decAlloc_of_noHeaderReceivedEnv h48 hfree0 hfits
        have h6064_some := v5_noHeaderReceived_6064_some_to_ret_of_placedHooks
          (F := F) (Qp := Qp) hA hDec st_auth s0 s2 hcl2
          out pbA p1_new p2_new ep w8 w16 w24 w40 w80 d36 authPb decPb hfits_dec
          heq48 hr_lt63 hm_lt63 hl1_lt hsp0_align hpc2 hrun2 hsp2
          hx19_2 hx20_2 hx22_2 hx23_2 hx25_2 hx27_2 hx28_2 htr2
        refine v5_sepWPp_mono_post
          (SepWPp.weaken_pre (Entails.trans hP2 (Entails.of_eq (by
            dsimp only [v5_pre_6064_some, Option.map, st_auth]; try sep_ac_rfl))) h6064_some) ?_
        rintro sf Pf ⟨⟨evs_dec, hdec_env, hPf⟩, hsp_f, hcs_f, htr_f⟩
        refine ⟨⟨(authFromPbEvents authPb ++ evs_free0) ++ evs_dec, ?_, ?_⟩, hsp_f, hcs_f, htr_f⟩
        · unfold NoHeaderReceivedFromPbEnv; simp only [h48, ↓reduceIte]
          exact ⟨evs_free0, evs_dec, hfree0, hdec_env, rfl⟩
        · rw [M.stepEvents_append]; exact hPf

theorem v5_noHeaderReceived_3744_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext) (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64) (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived) (receivingHdr : Option PolynomialDecoder)
    (hfits : FitsEnv M lim st (NoHeaderReceivedFromPbEnv { uc := uc, receivingHdr := receivingHdr }))
    (hd32_48 : ∀ decPb, receivingHdr = some decPb → d32 = 48#32 ∧ (decPb.ptsNeeded == 48#32) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3744#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = w16) (hx23_1 : s1.readReg64 .x23 = w8)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32.zeroExtend 64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = w24) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5_pre_3744 A lim st s0 s1 out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36
        uc receivingHdr)
      (v5_post_ret A lim F (NoHeaderReceivedFromPbEnv { uc := uc, receivingHdr := receivingHdr })
        st s0 out pbA { uc := uc, receivingHdr := receivingHdr }) Qp :=
  v5_noHeaderReceived_3744_to_ret_of_placedHooks hA.toPlacedBudget hDec st s0 s1 hcl1
    out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36 uc receivingHdr
    hfits hd32_48 hsp0_align hpc1 hrun1 hsp1
    hx8_1 hx9_1 hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1

/-- Complete budget-threaded Variant 5 (`NoHeaderReceived`, `+1344 -> s0.x30`) theorem. -/
theorem states_from_pb_noHeaderReceived_1344_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s : V1State.Chunked.NoHeaderReceived)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (hfits : FitsEnv M lim st (NoHeaderReceivedFromPbEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1344#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (_hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.noHeaderReceived s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (v5_post_ret A lim F (NoHeaderReceivedFromPbEnv s) st s0 out pbA s) Qp := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  rcases s with ⟨uc, receivingHdr⟩
  refine SepWPp.weaken_pre (sepConj_mono_right
    (sepConj_mono (v5b_memRegion_2304_split_224_232 (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v5a_optProtoInnerStateAt_unpack A.repAlloc pbA ⟨uc, receivingHdr⟩)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w8 => SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun d32 => SepWPp.exists_elim fun d36 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w56 => SepWPp.exists_elim fun w64 =>
    SepWPp.exists_elim fun w72 => SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w88 =>
    SepWPp.exists_elim fun w96 => SepWPp.exists_elim fun z232 => SepWPp.exists_elim fun z224 => ?_
  cases receivingHdr with
  | none =>
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v5a_optProtoPolyDecoderHeap A.repAlloc none w8 w16 w24 d32 d36 w40 ∗
      (v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
       A.pool lim st s1 ∗ (v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl))
      (sepConj_mono_left (v5_optProtoPolyDecoderHeap_none_dup A.repAlloc w8 w16 w24 d32 d36 w40))) ?_
    rw [sepConj_assoc]; refine SepWPp.pure_left fun hw8 => ?_; subst hw8
    let Rest_none : SepProp :=
      v5a_optProtoPolyDecoderHeap A.repAlloc (Option.map pbToProtoPolyDecoder none)
        noneCap w16 w24 d32 d36 w40 ∗ v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
      memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      v5a_pbAHeadersAt pbA noneCap w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
      A.pool lim st s1 ∗ Rest_none by dsimp only [Rest_none]; try sep_ac_rfl)) ?_
    have h3744 := v5b_step_1344_to_3744_none_placed_budget A lim st (ext := ext) s0 s1
      (s0.sp - 2400#64) out pbA w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
      Rest_none hfsp_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    refine v5_sepWPp_seq_st_lscl hcl1 h3744 ?_
    rintro s2 P2 hpc2 hrun2 hcl2
      ⟨hP2, _, hsp2, hx8_2, hx9_2, hx10_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
       hx24_2, hx25_2, hx26_2, _, hx28_2, htr2⟩
    exact SepWPp.weaken_pre
      (Entails.trans hP2 (Entails.of_eq (by dsimp only [v5_pre_3744, Rest_none]; try sep_ac_rfl)))
      (v5_noHeaderReceived_3744_to_ret_of_placedHooks (F := F) hA hDec st s0 s2 hcl2
        out pbA noneCap w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36 uc none hfits
        (fun _ h => nomatch h) hsp0_align hpc2 hrun2 hsp2
        hx8_2 hx9_2 hx10_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2)
  | some decPb =>
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
        w8 w16 w24 d32 d36 w40 ∗
      (v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
       A.pool lim st s1 ∗ (v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl))
      (sepConj_mono_left (v5_optProtoPolyDecoderHeap_some_dup A.repAlloc
        (pbToProtoPolyDecoder decPb) w8 w16 w24 d32 d36 w40))) ?_
    rw [sepConj_assoc]; refine SepWPp.pure_left fun ⟨hd32, hw8_lt⟩ => ?_
    change d32 = decPb.ptsNeeded at hd32
    by_cases h48 : decPb.ptsNeeded = 48#32
    · have hd32_48 : d32 = 48#32 := hd32.trans h48; subst hd32_48
      have heq48 : (decPb.ptsNeeded == 48#32) = true := beq_iff_eq.mpr h48
      let Rest_some : SepProp :=
        v5a_optProtoPolyDecoderHeap A.repAlloc (Option.map pbToProtoPolyDecoder (some decPb))
          w8 w16 w24 48#32 d36 w40 ∗ v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        v5a_pbAHeadersAt pbA w8 w16 w24 48#32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
        A.pool lim st s1 ∗ Rest_some by dsimp only [Rest_some]; try sep_ac_rfl)) ?_
      have h3744 := v5b_step_1344_to_3744_some_placed_budget A lim st (ext := ext) s0 s1
        (s0.sp - 2400#64) out pbA w8 w16 w24 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
        Rest_some hfsp_align hw8_lt hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      refine v5_sepWPp_seq_st_lscl hcl1 h3744 ?_
      rintro s2 P2 hpc2 hrun2 hcl2
        ⟨hP2, _, hsp2, hx8_2, hx9_2, hx10_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
         hx24_2, hx25_2, hx26_2, _, hx28_2, htr2⟩
      exact SepWPp.weaken_pre
        (Entails.trans hP2 (Entails.of_eq (by dsimp only [v5_pre_3744, Rest_some]; try sep_ac_rfl)))
        (v5_noHeaderReceived_3744_to_ret_of_placedHooks (F := F) hA hDec st s0 s2 hcl2
          out pbA w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 48#32 d36 uc (some decPb) hfits
          (fun _ h => by cases h; exact ⟨rfl, heq48⟩) hsp0_align hpc2 hrun2 hsp2
          hx8_2 hx9_2 hx10_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2)
    · unfold v5_post_ret
      have hd32_ne : d32 ≠ 48#32 := fun h => h48 (hd32.symm.trans h)
      have hne48 : (decPb.ptsNeeded == 48#32) = false := beq_false_of_ne h48
      rw [v5a_states_from_pb_noHeaderReceived_ptsNeeded_ne F decPb uc hne48]
      apply SepWPp.of_sepWP_ret
      let Rest_err : SepProp :=
        v5a_optProtoPolyDecoderHeap A.repAlloc (Option.map pbToProtoPolyDecoder (some decPb))
          w8 w16 w24 d32 d36 w40 ∗ v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 224 ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v5a_pbAHeadersAt pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ z224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ z232) ∗
        A.pool lim st s1 ∗ Rest_err by dsimp only [Rest_err]; try sep_ac_rfl)) ?_
      have h1396 := v5b_step_1344_to_1396_err_placed_budget A lim st (ext := ext) s0 s1
        (s0.sp - 2400#64) out pbA w8 w16 w24 d32 d36 w40 w48 w56 w64 w72 w80 w88 w96 z224 z232
        Rest_err hfsp_align hw8_lt hd32_ne hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      refine SepWP.seq h1396 ?_
      rintro s2 P2 hpc2 hrun2
        ⟨hP2, _, hsp2, hx10_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx28_2, htr2⟩
      have hj2304 := v5b_memRegion_2304_join_224_232 (s0.sp - 2400#64) w40 d36
      have herr := v5_err_1396_to_ret_of_placedHooks (F := F) hA st s0 s2
        out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36 uc decPb
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hsp0_align hpc2 hrun2 hsp2 hx10_2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx28_2 htr2
      refine v5_sepWP_weaken_mono herr (Entails.trans hP2 (Entails.trans (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 224 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ w40) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₃₂ d36) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
          (v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
           v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
             w8 w16 w24 d32 d36 w40 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s2 ∗
           (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by
            dsimp only [Rest_err, Option.map]; try sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hj2304) (Entails.of_eq (by sep_ac_rfl)))))
        fun sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
      refine ⟨⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
      unfold NoHeaderReceivedFromPbEnv; simp only [h48, ↓reduceIte]; exact hfree

theorem states_from_pb_noHeaderReceived_1344_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext) (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s : V1State.Chunked.NoHeaderReceived)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) (out pbA : BitVec 64)
    (hfits : FitsEnv M lim st (NoHeaderReceivedFromPbEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1344#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.noHeaderReceived s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (v5_post_ret A lim F (NoHeaderReceivedFromPbEnv s) st s0 out pbA s) Qp :=
  states_from_pb_noHeaderReceived_1344_of_placedHooks hA.toPlacedBudget hDec st s s0 s1 hcl1
    out pbA hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

/-! ## Complete Block-`333` `subroutine_ok` Theorems for Variant 5 (`NoHeaderReceived`) -/

/-- Envelope-parametric `subroutine_ok` for Variant 5 (`InnerState.noHeaderReceived`). -/
theorem states_from_pb_noHeaderReceived_placed_ok_of_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (s : V1State.Chunked.NoHeaderReceived)
    (hfit_sub : ∀ st : M.σ, FitsEnv M lim st Env → FitsEnv M lim st (NoHeaderReceivedFromPbEnv s))
    (henv_sub : ∀ (st : M.σ) {evs : List AllocEvent},
      FitsEnv M lim st Env → NoHeaderReceivedFromPbEnv s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
        { innerState := some (.noHeaderReceived s) } Env)) := by
  apply subroutine_ok_of_sepWPp; rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  dsimp only [DefsBudget.statesFromPbVariantPlacedSpecOfEnv] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hx0, _, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗ (memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some (.noHeaderReceived s)) ∗
      statesFromPbJumpTablePlacedAt), R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some (.noHeaderReceived s)) ∗
     statesFromPbJumpTablePlacedAt) hsp0_align hpc0 hrun0 hx8 hx0
  refine v5_sepWPp_seq_st_lscl hcl0 hpro ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hP1, hsp1, _, hx8_1, hx0_1, htr1, _⟩
  let Tail : SepProp :=
    optProtoPolynomialDecoderAt A.repAlloc (pbA + 8#64) (s.receivingHdr.map pbToProtoPolyDecoder) ∗
    optProtoUnchunkedNoHeaderReceivedAt A.repAlloc (pbA + 48#64) s.uc ∗ memRegion (pbA + 104#64) 120
  have hinner : optProtoInnerStateAt A.repAlloc pbA (some (.noHeaderReceived s)) =
      (pbA ↦₆₄ 0x8000000000000005#64) ∗ Tail := v5a_optProtoInnerStateAt_noHeaderReceived A.repAlloc pbA s
  have hdisp := states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA 0x8000000000000005#64 1344#64
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ Tail)
    TaggedVariantDispatch.noHeaderReceived hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine v5_sepWPp_seq_st_lscl hcl1
    (SepWP.weaken_pre (Entails.trans hP1 (by rw [hinner]; exact Entails.of_eq (by sep_ac_rfl))) hdisp) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2, _⟩
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by rw [hx23_2]; bv_omega
  have hpre_join : P2 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some (.noHeaderReceived s)) ∗
      statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2 := by
    refine Entails.trans hP2 ?_; rw [hinner]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ ((pbA ↦₆₄ 0x8000000000000005#64) ∗ Tail) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  have h1344 := states_from_pb_noHeaderReceived_1344_of_placedHooks (F := F)
    (Qp := fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (withLsCodeLoaded lsmpl
      (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
        { innerState := some (.noHeaderReceived s) } Env)).onPanic ((out, pbA), st) s0 sf ∗ R))
    hA hDec st s s0 s2 hcl2 out pbA (hfit_sub st hfits)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx27_2 htr2
  refine v5_sepWPp_mono_post (SepWPp.weaken_pre hpre_join h1344) ?_
  rintro sf Pf ⟨⟨evs, hevs, hPf⟩, hspf, hcs, htrf⟩; refine ⟨fun hmem_f => ?_, hspf, hcs⟩
  dsimp only [withLsCodeLoaded, DefsBudget.statesFromPbVariantPlacedSpecOfEnv]
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htrf, henv_sub st hfits hevs⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by sep_ac_rfl))) hmem_f⟩

/-- `subroutine_ok` for Variant 5 under its tight envelope `NoHeaderReceivedFromPbEnv s`. -/
theorem states_from_pb_noHeaderReceived_placed_ok_tight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (s : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
        { innerState := some (.noHeaderReceived s) } (NoHeaderReceivedFromPbEnv s))) :=
  states_from_pb_noHeaderReceived_placed_ok_of_env hA hDec s (fun _ h => h) (fun _ _ _ h => h)

/-- `subroutine_ok` for Variant 5 under uniform `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`). -/
theorem states_from_pb_noHeaderReceived_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (hDec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (s : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
        { innerState := some (.noHeaderReceived s) })) :=
  states_from_pb_noHeaderReceived_placed_ok_of_env hA hDec s
    (fun _ h => fitsEnv_noHeaderReceived_of_statesFromPbEnv s h)
    (fun _ _ hfits hevs => noHeaderReceivedFromPbEnv_sub_statesFromPbEnv s hfits hevs)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5PlacedBudget
