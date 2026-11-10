/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4ePlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4e
import ProofLib.SepLogic.WP.Apply

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 4 (`EkSentCt1Received`, `+248`)

Allocator event envelopes, `StatesFromPbEnv` subsumption, and total-correctness Block-`333`
`subroutine_ok` contracts for `InnerState.ekSentCt1Received` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4ePlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.StdStartup SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsProg_333 lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoPolynomialDecoder States StatesError V1State pbToProtoPolyDecoder
   spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize
   protoUnchunkedEkSentCt1ReceivedAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 decoderFromPbResult
   resultChunkedStatesAt statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack
   v1StatePtsBound v4b_optProtoInnerStateAt_ekSentCt1Received_eq v4b_optProtoPolyDecoderAt_unpack
   v4b_optProtoPolyDecoderHeap v4b_optProtoPolyDecoderWordsAt v4b_optProtoUcAt_unpack
   v4b_optProtoUcHeap v4b_optProtoUcWordsAt v4b_pbA_all_words_entails_memRegion v4b_protoUcAt_pack
   v4b_stackAt_ekSent_to_encoderFromPbStack v4b_stackAt_encoderFromPbStack_to_ekSent
   v4b_states_from_pb_ekSentCt1Received_none_uc_none_dec
   v4b_states_from_pb_ekSentCt1Received_none_uc_some_dec
   v4b_states_from_pb_ekSentCt1Received_some_uc_none_dec
   v4b_states_from_pb_ekSentCt1Received_some_uc_some_dec
   v4d_ekSent_from_pb_error_eq v4d_fsp_aligned v4d_memRegion_1156_104_392_entails_1652
   v4d_memRegion_2304_split_2228 v4d_optProtoUcHeap_some_u0_lt v4d_sepWPp_exists_left
   v4d_sepWPp_pure_left v4e_optProtoPolyDecoderHeap_some_info v4e_optProtoUcHeap_none_info
   v4e_sepWPp_exists v4e_ucWordsAt_pbA_eq)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth rawUcEkSentCt1Received
   rawUcEkSentCt1Received_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Unchunked
  (ekSentCt1ReceivedFromPbStack ekSentCt1ReceivedResultAt
   extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecAllocEnv_imp_fromPbDecEnv fromPbDecLoopAllocEvents
   fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb (v4d_sepWPp_call_lscl)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (StatesFromPbEnv statesFromPbVariantPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
  (sepWPp_seq_clean_lscl_st sfpProof_sepWPp_of_states_body_cl_placed_of_env)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudget
  (v4b_step_2228_some_to_18368_placed_budget v4b_step_248_none_to_2228_placed_budget
   v4b_step_248_some_eq_to_2228_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs nonFreeCount)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (EkSentCt1ReceivedFromPbPostEnv EkSentCt1ReceivedFromPbPreEnv authFromPbAllocEvents
   ekSentCt1ReceivedFromPb ekSentCt1ReceivedFromPbAllocEvents
   ekSentCt1ReceivedFromPbPostEnv_of_nil ekSentCt1ReceivedFromPbSpec
   ekSentCt1ReceivedFromPbSpecOfEnv)

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Exact Allocator Event Envelopes, `FitsEnv` Projections, & Wire-Size Subsumption -/

/-- Exact allocator event envelope from `+2228` when `s.uc = some u`:
    calls `<EkSentCt1Received>::from_pb`, followed either by `FreeOnlyEvs` cleanup (when `from_pb`
    fails or `optDecPb = none`) or by `<PolyDecoder>::from_pb` (`FromPbDecEnv`). -/
def EkSent2228SomeEnv (F : ShaCompress) (u : V1State.Unchunked.EkSentCt1Received)
    (optDecPb : Option PolynomialDecoder) (evs : List AllocEvent) : Prop :=
  match ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | .error _ => EkSentCt1ReceivedFromPbPostEnv F u evs
  | .ok _ =>
    match optDecPb with
    | none => EkSentCt1ReceivedFromPbPostEnv F u evs
    | some d =>
      ∃ evs1 evs2 : List AllocEvent,
        evs = evs1 ++ evs2 ∧
        EkSentCt1ReceivedFromPbPostEnv F u evs1 ∧
        FromPbDecEnv (pbToProtoPolyDecoder d) evs2

/-- Exact binary allocator event envelope of Variant 4 (`InnerState.ekSentCt1Received s`, `+248`). -/
def EkSentCt1ReceivedFromPbEnv (F : ShaCompress) (s : V1State.Chunked.EkSentCt1Received)
    (evs : List AllocEvent) : Prop :=
  match s.receivingCt2 with
  | none =>
    match s.uc with
    | none => FreeOnlyEvs evs
    | some u => EkSent2228SomeEnv F u none evs
  | some d =>
    if d.ptsNeeded = 80#32 then
      match s.uc with
      | none => FreeOnlyEvs evs
      | some u => EkSent2228SomeEnv F u (some d) evs
    else
      FreeOnlyEvs evs

theorem ekSentCt1ReceivedFromPbPostEnv_append_freeOnly
    {F : ShaCompress} {u : V1State.Unchunked.EkSentCt1Received} {evs1 evs2 : List AllocEvent}
    (h1 : EkSentCt1ReceivedFromPbPostEnv F u evs1) (h2 : FreeOnlyEvs evs2) :
    EkSentCt1ReceivedFromPbPostEnv F u (evs1 ++ evs2) := by
  rcases h1 with ⟨evsFree, hfree, rfl⟩
  exact ⟨evsFree ++ evs2, hfree.append h2, List.append_assoc _ _ _⟩

theorem ekSent2228SomeEnv_of_allocEvents
    (F : ShaCompress) (u : V1State.Unchunked.EkSentCt1Received)
    (optDecPb : Option PolynomialDecoder) :
    EkSent2228SomeEnv F u optDecPb (ekSentCt1ReceivedFromPbAllocEvents F u) := by
  unfold EkSent2228SomeEnv
  cases ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
  | error _ => exact ekSentCt1ReceivedFromPbPostEnv_of_nil F u
  | ok _ =>
    cases optDecPb with
    | none => exact ekSentCt1ReceivedFromPbPostEnv_of_nil F u
    | some _ =>
      exact ⟨ekSentCt1ReceivedFromPbAllocEvents F u, [], (List.append_nil _).symm,
        ekSentCt1ReceivedFromPbPostEnv_of_nil F u,
        fromPbDecAllocEnv_imp_fromPbDecEnv (Or.inl rfl)⟩

theorem fitsEnv_ekSentPre_of_2228Some
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {u : V1State.Unchunked.EkSentCt1Received}
    {optDecPb : Option PolynomialDecoder}
    (h : FitsEnv M lim st (EkSent2228SomeEnv F u optDecPb)) :
    FitsEnv M lim st (EkSentCt1ReceivedFromPbPreEnv F u) := by
  intro evs hevs
  subst hevs
  exact h _ (ekSent2228SomeEnv_of_allocEvents F u optDecPb)

theorem fitsEnv_decAlloc_of_2228Some
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {u : V1State.Unchunked.EkSentCt1Received}
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)}
    {d : PolynomialDecoder} {evs1 : List AllocEvent}
    (hres : ekSentCt1ReceivedFromPb (spqrAuthApi F) u = .ok uc)
    (hevs1 : EkSentCt1ReceivedFromPbPostEnv F u evs1)
    (h : FitsEnv M lim st (EkSent2228SomeEnv F u (some d))) :
    FitsEnv M lim (M.stepEvents evs1 st) (FromPbDecAllocEnv (pbToProtoPolyDecoder d)) := by
  intro evs2 ha2
  have h12 : EkSent2228SomeEnv F u (some d) (evs1 ++ evs2) := by
    unfold EkSent2228SomeEnv
    rw [hres]
    exact ⟨evs1, evs2, rfl, hevs1, fromPbDecAllocEnv_imp_fromPbDecEnv ha2⟩
  exact ((fitsEvents_append M lim evs1 evs2 st).mp (h (evs1 ++ evs2) h12)).2

private theorem spqrBoundedEvs_if_rustAlloc1 (bs : List (BitVec 8)) {R : Nat}
    (hlen : bs.length ≤ R) (hmax : R ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 R (if bs = [] then [] else rustAllocEvents bs.length 1) := by
  split
  · exact SpqrBoundedEvs.nil 1 R
  · rename_i hne
    have hpos : 1 ≤ bs.length := by
      cases bs with
      | nil => exact (hne rfl).elim
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    unfold rustAllocEvents
    split
    · refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
      simp only [List.mem_singleton] at hev
      subst hev
      exact ⟨Nat.le_trans hlen hmax, hlen, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    · rename_i hnot
      exact (hnot ⟨by decide, hpos⟩).elim

private theorem spqrBoundedEvs_rustAllocEvents_align2 (sz : Nat)
    (hmax : max sz 256 ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 (max sz 256) (rustAllocEvents sz 2) := by
  unfold rustAllocEvents
  split
  · refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_trans (Nat.le_max_left sz 256) hmax, Nat.le_max_left sz 256,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  · rename_i hnot
    have hlt2 : sz = 0 ∨ sz = 1 := by omega
    rcases hlt2 with rfl | rfl <;>
      refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩ <;>
      (simp only [List.mem_singleton] at hev; subst hev
       refine ⟨by decide, Nat.le_trans (by decide) (Nat.le_max_right _ 256), ?_,
         (fun _ _ _ h => nomatch h)⟩
       intro al r h; cases h; decide)

private theorem spqrBoundedEvs_flatMap {α : Type} (R : Nat) (f : α → List AllocEvent) :
    ∀ (xs : List α), (∀ x ∈ xs, SpqrBoundedEvs 1 R (f x)) →
      SpqrBoundedEvs xs.length R (xs.flatMap f)
  | [], _ => SpqrBoundedEvs.nil 0 R
  | x :: xs, hall => by
    simp only [List.flatMap_cons, List.length_cons]
    have hx := hall x List.mem_cons_self
    have hxs := spqrBoundedEvs_flatMap R f xs (fun y hy => hall y (List.mem_cons_of_mem _ hy))
    have happ := SpqrBoundedEvs.append hx hxs
    rw [Nat.add_comm 1 xs.length, Nat.max_self] at happ
    exact happ

private theorem takeWhile_len_and_mem {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.takeWhile p).length ≤ xs.length ∧ ∀ x ∈ xs.takeWhile p, x ∈ xs
  | [] => ⟨Nat.le_refl 0, fun _ h => nomatch h⟩
  | x :: xs => by
    simp only [List.takeWhile_cons]
    split
    · obtain ⟨hlen, hmem⟩ := takeWhile_len_and_mem p xs
      refine ⟨Nat.succ_le_succ hlen, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem y hy')
    · exact ⟨Nat.zero_le _, fun _ h => nomatch h⟩

private theorem length_le_sum_map_length {bs : List (BitVec 8)} :
    ∀ {xs : List (List (BitVec 8))}, bs ∈ xs → bs.length ≤ (xs.map List.length).sum
  | _ :: _, h => by
    rcases List.mem_cons.mp h with rfl | htl
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons, List.sum_cons]
      have ih := length_le_sum_map_length htl; omega

private theorem spqrBoundedEvs_fromPbDecEnv {pb : ProtoPolynomialDecoder} {L : Nat}
    (hsum : (pb.pts.map List.length).sum ≤ L) (hmax : L + 256 ≤ MallocngMaxAllocSize)
    {evs : List AllocEvent} (hevs : FromPbDecEnv pb evs) :
    SpqrBoundedEvs 16 (L + 256) evs := by
  rcases hevs with ⟨evs_alloc, evs_free, rfl, halloc, hfree⟩
  have hbody : SpqrBoundedEvs 16 (L + 256) evs_alloc := by
    rcases halloc with rfl | ⟨hpts16, rfl⟩
    · exact SpqrBoundedEvs.nil 16 (L + 256)
    · unfold fromPbDecLoopAllocEvents
      obtain ⟨hlen_tw, hmem_tw⟩ := takeWhile_len_and_mem
        (fun bs : List (BitVec 8) => bs.length % 4 == 0) pb.pts
      have hfm := spqrBoundedEvs_flatMap (L + 256) fromPbDecSlotEvents
        (pb.pts.takeWhile (fun bs => bs.length % 4 == 0)) fun bs hbs => by
          have hbs_len := length_le_sum_map_length (hmem_tw bs hbs)
          unfold fromPbDecSlotEvents
          split
          · exact SpqrBoundedEvs.nil 1 (L + 256)
          · exact SpqrBoundedEvs.mono (Nat.le_refl 1) (by omega)
              (spqrBoundedEvs_rustAllocEvents_align2 bs.length (by omega))
      exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) hfm
  exact SpqrBoundedEvs.mono (Nat.le_refl 16) (by omega)
    (SpqrBoundedEvs.append hbody (SpqrBoundedEvs.of_freeOnly hfree))

private theorem spqrBoundedEvs_ekSentPostEnv {F : ShaCompress}
    {u : V1State.Unchunked.EkSentCt1Received} {L : Nat}
    (huc : rawUcEkSentCt1Received u ≤ L) (hmax : L ≤ MallocngMaxAllocSize)
    {evs : List AllocEvent} (hevs : EkSentCt1ReceivedFromPbPostEnv F u evs) :
    SpqrBoundedEvs 2 L evs := by
  rcases hevs with ⟨evsFree, hfree, rfl⟩
  have halloc : SpqrBoundedEvs 2 L (ekSentCt1ReceivedFromPbAllocEvents F u) := by
    unfold ekSentCt1ReceivedFromPbAllocEvents
    cases ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
    | error _ => exact SpqrBoundedEvs.nil 2 L
    | ok _ =>
      cases hauth : u.auth with
      | none => exact SpqrBoundedEvs.nil 2 L
      | some auth =>
        have hlen : auth.rootKey.length + auth.macKey.length ≤ L := by
          dsimp only [rawUcEkSentCt1Received] at huc
          rw [hauth] at huc; dsimp only [optRaw, rawAuth] at huc; omega
        unfold authFromPbAllocEvents
        have h1 := spqrBoundedEvs_if_rustAlloc1 auth.rootKey (R := L) (by omega) hmax
        have h2 := spqrBoundedEvs_if_rustAlloc1 auth.macKey (R := L) (by omega) hmax
        have happ := SpqrBoundedEvs.append h1 h2
        rw [Nat.max_self] at happ; exact happ
  exact SpqrBoundedEvs.mono (Nat.le_refl 2) (by omega)
    (SpqrBoundedEvs.append halloc (SpqrBoundedEvs.of_freeOnly hfree))

private theorem polyDec_pts_sum_le_encodeRaw (m : PolynomialDecoder) :
    (m.pts.map List.length).sum ≤ (PolynomialDecoder.encodeRaw m).length := by
  unfold PolynomialDecoder.encodeRaw
  simp only [List.length_append]
  have h1 := sum_length_le_encodeRepeatedBytes 3#32 m.pts
  omega

private theorem ekSentCt1Received_components_le_encodeRaw (s : V1State.Chunked.EkSentCt1Received) :
    optRaw rawUcEkSentCt1Received s.uc +
      optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) s.receivingCt2 ≤
      (V1State.encodeRaw { innerState := some (.ekSentCt1Received s) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.EkSentCt1Received.encodeRaw 5#32 s
  have h1 := length_le_encodeOptMessage V1State.Unchunked.EkSentCt1Received.encodeRaw
    rawUcEkSentCt1Received rawUcEkSentCt1Received_le_encodeRaw 1#32 s.uc
  have h2 := length_le_encodeOptMessage PolynomialDecoder.encodeRaw
    (fun m => (m.pts.map List.length).sum) polyDec_pts_sum_le_encodeRaw 3#32 s.receivingCt2
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.EkSentCt1Received.encodeRaw] at h0 ⊢
  simp only [List.length_append] at h0; omega

/-- Every event sequence in `EkSentCt1ReceivedFromPbEnv F s` satisfies the linear default envelope
    `StatesFromPbEnv { innerState := some (.ekSentCt1Received s) }` whenever `FitsEnv` holds. -/
theorem ekSentCt1ReceivedFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    (s : V1State.Chunked.EkSentCt1Received)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ekSentCt1Received s) }))
    {evs : List AllocEvent} (hevs : EkSentCt1ReceivedFromPbEnv F s evs) :
    StatesFromPbEnv { innerState := some (.ekSentCt1Received s) } evs := by
  let pb : V1State := { innerState := some (.ekSentCt1Received s) }
  let L : Nat := (V1State.encodeRaw pb).length
  change SpqrBoundedEvs 128 (4 * L + 4096) evs
  let m := min (4 * L + 4096) MallocngMaxAllocSize
  have hm_env : StatesFromPbEnv pb [.alloc m] := by
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev; subst hev
    exact ⟨Nat.min_le_right _ _, Nat.min_le_left _ _,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  have hm_fit : FitsEvents M lim st [.alloc m] := hfits [.alloc m] hm_env
  rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
  have hm_req : m ≤ M.stepReserve (.alloc m) st := M.req_le_stepReserve (.alloc m) st
  have hmax : 4 * L + 4096 ≤ MallocngMaxAllocSize := by
    dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢; omega
  have hcomp : optRaw rawUcEkSentCt1Received s.uc +
      optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) s.receivingCt2 ≤ L :=
    ekSentCt1Received_components_le_encodeRaw s
  have h2228_sub : ∀ {u : V1State.Unchunked.EkSentCt1Received}
      {optDecPb : Option PolynomialDecoder} {evs' : List AllocEvent},
      rawUcEkSentCt1Received u ≤ L →
      optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) optDecPb ≤ L →
      EkSent2228SomeEnv F u optDecPb evs' →
      SpqrBoundedEvs 128 (4 * L + 4096) evs' := by
    intro u optDecPb evs' huc_le hdec_le h2228
    unfold EkSent2228SomeEnv at h2228; revert h2228
    cases ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
    | error _ =>
      intro hpost
      exact SpqrBoundedEvs.mono (by decide) (by omega)
        (spqrBoundedEvs_ekSentPostEnv huc_le (by omega) hpost)
    | ok _ =>
      cases optDecPb with
      | none =>
        intro hpost
        exact SpqrBoundedEvs.mono (by decide) (by omega)
          (spqrBoundedEvs_ekSentPostEnv huc_le (by omega) hpost)
      | some d =>
        rintro ⟨evs1, evs2, rfl, h1, h2⟩
        have hpbd : ((pbToProtoPolyDecoder d).pts.map List.length).sum ≤ L := by
          simpa [pbToProtoPolyDecoder, optRaw] using hdec_le
        have hb1 := spqrBoundedEvs_ekSentPostEnv huc_le (by omega) h1
        have hb2 := spqrBoundedEvs_fromPbDecEnv hpbd (by omega) h2
        exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append hb1 hb2)
  unfold EkSentCt1ReceivedFromPbEnv at hevs; revert hevs
  cases hrec : s.receivingCt2 with
  | none =>
    cases huc : s.uc with
    | none =>
      intro hfree
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hfree)
    | some u =>
      intro h2228
      have huc_le : rawUcEkSentCt1Received u ≤ L := by
        rw [huc] at hcomp; dsimp only [optRaw] at hcomp; omega
      exact h2228_sub huc_le (Nat.zero_le _) h2228
  | some d =>
    dsimp only; split
    · cases huc : s.uc with
      | none =>
        intro hfree
        exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hfree)
      | some u =>
        intro h2228
        have huc_le : rawUcEkSentCt1Received u ≤ L := by
          rw [huc] at hcomp; dsimp only [optRaw] at hcomp; omega
        have hdec_le : optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) (some d) ≤ L := by
          rw [hrec] at hcomp; omega
        exact h2228_sub huc_le hdec_le h2228
    · intro hfree
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hfree)

theorem fitsEnv_ekSentCt1ReceivedFromPbEnv_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {F : ShaCompress}
    (s : V1State.Chunked.EkSentCt1Received)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ekSentCt1Received s) })) :
    FitsEnv M lim st (EkSentCt1ReceivedFromPbEnv F s) :=
  fun evs hevs => hfits evs (ekSentCt1ReceivedFromPbEnv_sub_statesFromPbEnv s hfits hevs)

/-! ## `+2228 -> lsmpl.base 348 -> +2308 -> ret` & Variant 4 Body at `+248` -/

private theorem v4e_seq_clean_p_weaken_lscl_st [LibsignalPlacement]
    {ext : String → Option (State → State)} {mid_pc target_pc : BitVec 64} {s : State}
    {P1 P1' : SepProp} {P2 : State → SepProp} {Q : State → Prop}
    {post Qp : State → SepProp → Prop} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (lsProg_333 (Rust.withPanics ext)) mid_pc s P1' (fun s' P' => (P' ⊢ P2 s') ∧ Q s'))
    (hpre : P1 ⊢ P1')
    (h2 : ∀ s2, s2.pc = mid_pc → s2.status = .Running →
      LibsignalCodeLoaded lsmpl s2.mem → Q s2 →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s2 (P2 s2) post Qp) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P1 post Qp :=
  SepWPp.weaken_pre hpre (sepWPp_seq_clean_lscl_st hcl h1 h2)

private theorem sepWPp_mono_post {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {Q1 Q2 Qp : State → SepProp → Prop}
    (h : SepWPp prog target_pc s P Q1 Qp) (hQ : ∀ sf Pf, Q1 sf Pf → Q2 sf Pf) :
    SepWPp prog target_pc s P Q2 Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hQ1⟩ | hpan⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hQ1⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

private theorem sepWPp_of_false_panic {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ R : SepProp, SepWPp prog target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))) :
    SepWPp prog target_pc s P Q Qp := by
  intro R hm hL
  rcases h R R hm hL with ⟨sf, hsteps, hok | ⟨_, _, hmf, himp⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact (not_satisfies_false_sepConj (himp hmf)).elim
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- From `+2228`, when `s.uc = some u`:
    steps `+2228 -> lsmpl.base 348`, calls `<EkSentCt1Received>::from_pb`, and dispatches at
    `+2308` to return under `EkSent2228SomeEnv F u optDecPb` (polymorphic in panic postcondition `Qp`). -/
theorem v4e_ekSent_uc_some_2228_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (s0 s2 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received) (optDecPb : Option PolynomialDecoder)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem)
    (hfits : FitsEnv M lim st (EkSent2228SomeEnv F u optDecPb))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 2228#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx0_2 : s2.readReg64 .x0 = u56) (hx1_2 : s2.readReg64 .x1 = u48)
    (hx8_2 : s2.readReg64 .x8 = u16) (hx9_2 : s2.readReg64 .x9 = u40)
    (hx10_2 : s2.readReg64 .x10 = u64) (hx11_2 : s2.readReg64 .x11 = u8)
    (hx12_2 : s2.readReg64 .x12 = u32) (hx13_2 : s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64)
    (hx14_2 : s2.readReg64 .x14 = d28.zeroExtend 64) (hx15_2 : s2.readReg64 .x15 = d32)
    (hx19_2 : s2.readReg64 .x19 = out) (hx20_2 : s2.readReg64 .x20 = d16)
    (hx21_2 : s2.readReg64 .x21 = u24) (hx22_2 : s2.readReg64 .x22 = u0)
    (hx23_2 : s2.readReg64 .x23 = d24.zeroExtend 64) (hx24_2 : s2.readReg64 .x24 = d8)
    (hx25_2 : s2.readReg64 .x25 = u80) (hx26_2 : s2.readReg64 .x26 = u72)
    (hx27_2 : s2.readReg64 .x27 = pbA) (hx28_2 : s2.readReg64 .x28 = d0)
    (htr2 : TraceCalleeSaved s2 s0) (hd0_none : optDecPb = none → d0 = noneCap) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (v4b_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        (pbA ↦₆₄ 0x8000000000000004#64) ∗
        v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        memRegion (pbA + 152#64) 72 ∗
        v4b_optProtoPolyDecoderHeap A.repAlloc (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s2 ∗ statesFromPbJumpTablePlacedAt)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          EkSent2228SomeEnv F u optDecPb evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (match ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
               | .error e => .error e
               | .ok uc =>
                 match optDecPb with
                 | none => .error (.err .stateDecode)
                 | some d =>
                   match decoderFromPbResult (pbToProtoPolyDecoder d) with
                   | .error _ => .error (.err .stateDecode)
                   | .ok dec => .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      Qp := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans
      (sepConj_mono_left (v4d_optProtoUcHeap_some_u0_lt A.repAlloc u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96))
      (Entails.of_eq (sepConj_assoc _ _ _))) ?_
  apply v4d_sepWPp_pure_left; intro hu0_lt
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (sepConj_left_comm _ _ _))
      (sepConj_mono_left (v4d_memRegion_2304_split_2228 fsp))) ?_
  apply v4d_sepWPp_exists_left; intro v224; apply v4d_sepWPp_exists_left; intro v232
  apply v4d_sepWPp_exists_left; intro s0_u; apply v4d_sepWPp_exists_left; intro s8_u
  apply v4d_sepWPp_exists_left; intro s16_u; apply v4d_sepWPp_exists_left; intro s24_u
  apply v4d_sepWPp_exists_left; intro s32_u; apply v4d_sepWPp_exists_left; intro s40_u
  apply v4d_sepWPp_exists_left; intro s48_u; apply v4d_sepWPp_exists_left; intro s56_u
  apply v4d_sepWPp_exists_left; intro s64_u; apply v4d_sepWPp_exists_left; intro s72_u
  apply v4d_sepWPp_exists_left; intro s80_u; apply v4d_sepWPp_exists_left; intro s88_u
  apply v4d_sepWPp_exists_left; intro s96_u
  have h18368 := v4b_step_2228_some_to_18368_placed_budget A lim st (ext := ext)
    s2 fsp pbA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
    s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u
    v224 v232 d0 d8 d16 d24 d28 d32
    ((((pbA + 8#64) ↦₆₄ u0) ∗ ((pbA + 16#64) ↦₆₄ u8) ∗ ((pbA + 24#64) ↦₆₄ u16) ∗
      ((pbA + 32#64) ↦₆₄ u24) ∗ ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
      ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗ ((pbA + 72#64) ↦₆₄ u64) ∗
      ((pbA + 80#64) ↦₆₄ u72) ∗ ((pbA + 88#64) ↦₆₄ u80)) ∗
     (pbA ↦₆₄ 0x8000000000000004#64) ∗
     v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
     memRegion (pbA + 152#64) 72 ∗ memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1156 ∗
     memRegion (fsp + 1496#64) 392 ∗ memRegion (fsp + 1888#64) 104 ∗
     memRegion (fsp + 1992#64) 312 ∗
     v4b_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
     v4b_optProtoPolyDecoderHeap A.repAlloc (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt)
    hfsp_align hu0_lt hpc2 hrun2 hsp2
    hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hx15_2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
  refine v4e_seq_clean_p_weaken_lscl_st hcl2 h18368 ?_ ?_
  · dsimp only [fsp]
    rw [v4e_ucWordsAt_pbA_eq pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96]
    exact Entails.of_eq (by sep_ac_rfl)
  intro sm hpcm hrunm hclm ⟨_hvm2m, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, _, _, hx23_m, hx24_m, _, _, _, hx28_m, hx30_m, htr_m⟩
  have htr_m := htr_m.trans htr2
  have hsp_align_m : sm.spAligned = true := by simp only [State.spAligned, hsp_m]; exact hfsp_align
  have hfits_ek := fitsEnv_ekSentPre_of_2228Some hfits
  have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d0 d8 d16 d24 d28 d32
  have hpack_uc := v4b_protoUcAt_pack A.repAlloc (fsp + 1392#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
  have hst_ek := v4b_stackAt_encoderFromPbStack_to_ekSent fsp
  let CallFrame : SepProp :=
    ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
    memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1156 ∗
    memRegion (fsp + 1496#64) 392 ∗ memRegion (fsp + 1992#64) 312 ∗
    memRegion (fsp - 5152#64) 848 ∗
    v4b_optProtoPolyDecoderHeap A.repAlloc (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt
  refine sepWPp_of_false_panic fun R => ?_
  refine SepWPp.weaken_pre ?_
    (v4d_sepWPp_call_lscl
      (Variant4cPlacedBudget.v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok (F := F) hA)
      (x := (⟨fsp + 1888#64, fsp + 1392#64, u⟩, st))
      (P_step := memRegion (fsp + 1888#64) 104 ∗
        protoUnchunkedEkSentCt1ReceivedAt A.repAlloc (fsp + 1392#64) u ∗
        A.pool lim st sm ∗ stackAt fsp ekSentCt1ReceivedFromPbStack)
      (F := CallFrame) (R := R) (Qpan := fun _ => ⌜False⌝)
      hclm hpcm hrunm hsp_align_m hx30_m ?_
      (fun _ => Entails.pure_left False.elim) (fun _ _ => rfl) ?_)
  · rw [v4e_ucWordsAt_pbA_eq pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96] at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x8000000000000004#64) ∗
         (((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
          (((pbA + 8#64) ↦₆₄ u0) ∗ ((pbA + 16#64) ↦₆₄ u8) ∗ ((pbA + 24#64) ↦₆₄ u16) ∗
           ((pbA + 32#64) ↦₆₄ u24) ∗ ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
           ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗ ((pbA + 72#64) ↦₆₄ u64) ∗
           ((pbA + 80#64) ↦₆₄ u72) ∗ ((pbA + 88#64) ↦₆₄ u80))) ∗
         v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
         memRegion (pbA + 152#64) 72) ∗
        (v4b_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         v4b_optProtoUcHeap A.repAlloc (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96) ∗
        stackAt fsp encoderFromPbStack ∗
        (memRegion (fsp + 1888#64) 104 ∗ A.pool lim st sm ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1156 ∗
         memRegion (fsp + 1496#64) 392 ∗ memRegion (fsp + 1992#64) 312 ∗
         v4b_optProtoPolyDecoderHeap A.repAlloc (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
      (Entails.trans (sepConj_mono hpb (sepConj_mono hpack_uc (sepConj_mono_left hst_ek)))
        (by dsimp only [CallFrame]; exact Entails.of_eq (by sep_ac_rfl)))
  · intro R' hm'
    dsimp only [ekSentCt1ReceivedFromPbSpec, ekSentCt1ReceivedFromPbSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_m, hx1_m, hfits_ek,
      by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (sm.readReg64 .x30); rw [show sm.readReg64 .x30 = _ from hx30_m]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩, Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'⟩
  · intro s3 hpc3 hrun3 hcl3 hsp3 hcs3
    have hx19_3 := hcs3.1; have hx20_3 := hcs3.2.1; have hx23_3 := hcs3.2.2.2.2.1
    have hx24_3 := hcs3.2.2.2.2.2.1; have hx28_3 := hcs3.2.2.2.2.2.2.2.2.2.1
    have hvregs_3 := hcs3.2.2.2.2.2.2.2.2.2.2.2
    rw [hx19_m] at hx19_3; rw [hx20_m] at hx20_3; rw [hx23_m] at hx23_3
    rw [hx24_m] at hx24_3; rw [hx28_m] at hx28_3; rw [hsp_m] at hsp3
    dsimp only [ekSentCt1ReceivedFromPbSpec, ekSentCt1ReceivedFromPbSpecOfEnv]
    rw [sepConj_assoc]
    apply v4d_sepWPp_pure_left; intro htr3_m
    have htr3 : TraceCalleeSaved s3 s0 := ⟨htr3_m.trans htr_m.1, hvregs_3.trans htr_m.2⟩
    have hpull_evs :
        (ekSentCt1ReceivedResultAt A.repAlloc (F := F) (fsp + 1888#64)
            (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
          memRegion (fsp + 1392#64) 104 ∗
          (∃∗ evs1 : List AllocEvent, ⌜EkSentCt1ReceivedFromPbPostEnv F u evs1⌝ ∗
            A.pool lim (M.stepEvents evs1 st) s3) ∗
          stackAt sm.sp ekSentCt1ReceivedFromPbStack) ∗ CallFrame ⊢
        (∃∗ evs1 : List AllocEvent, ⌜EkSentCt1ReceivedFromPbPostEnv F u evs1⌝ ∗
          (ekSentCt1ReceivedResultAt A.repAlloc (F := F) (fsp + 1888#64)
              (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
            memRegion (fsp + 1392#64) 104 ∗ A.pool lim (M.stepEvents evs1 st) s3 ∗
            stackAt sm.sp ekSentCt1ReceivedFromPbStack)) ∗ CallFrame := by
      refine sepConj_mono_left ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro evs1
      exact Entails.sepExists_right evs1 (Entails.of_eq (by sep_ac_rfl))
    refine SepWPp.weaken_pre hpull_evs ?_
    apply v4d_sepWPp_exists_left; intro evs1
    rw [sepConj_assoc]
    apply v4d_sepWPp_pure_left; intro hevs1
    have h1652 := v4d_memRegion_1156_104_392_entails_1652 fsp
    have hst_back := v4b_stackAt_ekSent_to_encoderFromPbStack fsp
    have hpost_merge :
        (ekSentCt1ReceivedResultAt A.repAlloc (F := F) (fsp + 1888#64)
            (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
          memRegion (fsp + 1392#64) 104 ∗ A.pool lim (M.stepEvents evs1 st) s3 ∗
          stackAt sm.sp ekSentCt1ReceivedFromPbStack) ∗ CallFrame ⊢
        ekSentCt1ReceivedResultAt A.repAlloc (F := F) (fsp + 1888#64)
            (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
          memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1652 ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
          memRegion (fsp + 1992#64) 312 ∗
          v4b_optProtoPolyDecoderHeap A.repAlloc (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
          stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗ A.pool lim (M.stepEvents evs1 st) s3 ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt := by
      dsimp only [CallFrame]; rw [hsp_m]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (fsp + 236#64) 1156 ∗ memRegion (fsp + 1392#64) 104 ∗
           memRegion (fsp + 1496#64) 392) ∗
          (stackAt fsp ekSentCt1ReceivedFromPbStack ∗ memRegion (fsp - 5152#64) 848) ∗
          (ekSentCt1ReceivedResultAt A.repAlloc (F := F) (fsp + 1888#64)
             (ekSentCt1ReceivedFromPb (spqrAuthApi F) u) ∗
           memRegion fsp 224 ∗ ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
           memRegion (fsp + 1992#64) 312 ∗
           v4b_optProtoPolyDecoderHeap A.repAlloc (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           A.pool lim (M.stepEvents evs1 st) s3 ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
        (Entails.trans (sepConj_mono h1652 (sepConj_mono_left hst_back)) (Entails.of_eq (by sep_ac_rfl)))
    refine SepWPp.weaken_pre hpost_merge ?_
    cases hres : ekSentCt1ReceivedFromPb (spqrAuthApi F) u with
    | error e =>
      have he := v4d_ekSent_from_pb_error_eq F u e hres
      subst he
      apply SepWPp.of_sepWP_ret
      have herr := Variant4dPlacedBudget.v4d_ekSent_2308_err_to_ret_placed (F := F) hA (M.stepEvents evs1 st)
        s0 s3 out pbA d0 d8 d16 d32 d24 d28 (optDecPb.map pbToProtoPolyDecoder) (.err .stateDecode)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx24_3 hx28_3 htr3
      refine SepWP.weaken_pre (by dsimp only [fsp]; exact Entails.of_eq (by sep_ac_rfl))
        (SepWP.mono herr fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
      have henv : EkSent2228SomeEnv F u optDecPb (evs1 ++ evs2) := by
        unfold EkSent2228SomeEnv; rw [hres]
        exact ekSentCt1ReceivedFromPbPostEnv_append_freeOnly hevs1 hevs2
      refine ⟨⟨evs1 ++ evs2, henv, ?_⟩, hsp_f, hcs_f, htr_f⟩
      rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]; exact hPf
    | ok uc =>
      cases optDecPb with
      | none =>
        rw [hd0_none rfl] at hx28_3
        apply SepWPp.of_sepWP_ret
        dsimp only [Option.map, v4b_optProtoPolyDecoderHeap]
        have hnone := Variant4dPlacedBudget.v4d_ekSent_2308_ok_none_to_ret_placed (F := F) hA (M.stepEvents evs1 st)
          s0 s3 out pbA d32 d28 uc hsp0_align hpc3 hrun3 hsp3 hx19_3 hx28_3 htr3
        refine SepWP.weaken_pre
          (by dsimp only [fsp]
              refine Entails.trans
                (Entails.of_eq (show _ = ⌜d0 = noneCap⌝ ∗
                  (ekSentCt1ReceivedResultAt A.repAlloc (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
                   memRegion (s0.sp - 2400#64) 224 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
                   (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗ memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
                   memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
                   statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
                   A.pool lim (M.stepEvents evs1 st) s3 ∗ memRegion pbA optProtoInnerStateSize ∗
                   statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
                (Entails.pure_left fun _ => Entails.refl _))
          (SepWP.mono hnone fun sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
        have henv : EkSent2228SomeEnv F u none (evs1 ++ evs2) := by
          unfold EkSent2228SomeEnv; rw [hres]
          exact ekSentCt1ReceivedFromPbPostEnv_append_freeOnly hevs1 hevs2
        refine ⟨⟨evs1 ++ evs2, henv, ?_⟩, hsp_f, hcs_f, htr_f⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]; exact hPf
      | some d =>
        dsimp only [Option.map]
        have hfits_dec := fitsEnv_decAlloc_of_2228Some hres hevs1 hfits
        apply SepWPp.of_sepWP_ret
        have hsome := Variant4dPlacedBudget.v4d_ekSent_2308_ok_some_to_ret_placed (F := F) hA hdec
          (M.stepEvents evs1 st) s0 s3 out pbA d0 d8 d16 d32 d24 d28 uc d hcl3 hfits_dec
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx23_3 hx24_3 hx28_3 htr3
        refine SepWP.mono hsome fun sf Pf _ _ ⟨evs2, henv2, hPf, hsp_f, hcs_f, htr_f⟩ => ?_
        have henv : EkSent2228SomeEnv F u (some d) (evs1 ++ evs2) := by
          unfold EkSent2228SomeEnv; rw [hres]; exact ⟨evs1, evs2, rfl, hevs1, henv2⟩
        refine ⟨⟨evs1 ++ evs2, henv, ?_⟩, hsp_f, hcs_f, htr_f⟩
        rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]; exact hPf

/-- Full Variant 4 (`EkSentCt1Received`) execution from `lsmpl.base 333 + 248` to `s0.x30`
    under `EkSentCt1ReceivedFromPbEnv F s` (polymorphic in panic postcondition `Qp`). -/
theorem states_from_pb_ekSentCt1Received_248_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.EkSentCt1Received) (st : M.σ)
    (hfits : FitsEnv M lim st (EkSentCt1ReceivedFromPbEnv F s))
    (s0 s1 : State) (out pbA : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 248#64) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx13_1 : s1.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (optProtoInnerStateAt A.repAlloc pbA (some (.ekSentCt1Received s)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent,
          EkSentCt1ReceivedFromPbEnv F s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekSentCt1Received s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      Qp := by
  rcases s with ⟨optUc, optDec⟩
  rw [v4b_optProtoInnerStateAt_ekSentCt1Received_eq A.repAlloc pbA ⟨optUc, optDec⟩]
  dsimp only
  refine SepWPp.weaken_pre
    (sepConj_mono_left
      (sepConj_mono_right
        (sepConj_mono
          (v4b_optProtoUcAt_unpack A.repAlloc (pbA + 8#64) optUc)
          (sepConj_mono_left
            (v4b_optProtoPolyDecoderAt_unpack A.repAlloc (pbA + 112#64) (optDec.map pbToProtoPolyDecoder)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply v4e_sepWPp_exists; intro d0; apply v4e_sepWPp_exists; intro d8
  apply v4e_sepWPp_exists; intro d16; apply v4e_sepWPp_exists; intro d24
  apply v4e_sepWPp_exists; intro d28; apply v4e_sepWPp_exists; intro d32
  apply v4e_sepWPp_exists; intro u0; apply v4e_sepWPp_exists; intro u8
  apply v4e_sepWPp_exists; intro u16; apply v4e_sepWPp_exists; intro u24
  apply v4e_sepWPp_exists; intro u32; apply v4e_sepWPp_exists; intro u40
  apply v4e_sepWPp_exists; intro u48; apply v4e_sepWPp_exists; intro u56
  apply v4e_sepWPp_exists; intro u64; apply v4e_sepWPp_exists; intro u72
  apply v4e_sepWPp_exists; intro u80; apply v4e_sepWPp_exists; intro u88
  apply v4e_sepWPp_exists; intro u96
  cases optDec with
  | none =>
    dsimp only [Option.map, v4b_optProtoPolyDecoderHeap]
    refine SepWPp.weaken_pre
      (Entails.of_eq (show _ =
        ⌜d0 = noneCap⌝ ∗
        ((pbA ↦₆₄ 0x8000000000000004#64) ∗
         v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
         memRegion (pbA + 152#64) 72 ∗
         v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl)) ?_
    apply v4d_sepWPp_pure_left; rintro rfl
    have h248 := v4b_step_248_none_to_2228_placed_budget A lim st (ext := ext) s1 pbA
      u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d8 d16 d24 d28 d32
      ((pbA ↦₆₄ 0x8000000000000004#64) ∗ memRegion (pbA + 152#64) 72 ∗
       v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt)
      hpc1 hrun1 hx27_1
    refine v4e_seq_clean_p_weaken_lscl_st hcl1 h248 (Entails.of_eq (by sep_ac_rfl)) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨_hvm12, hsp2, hx0_2, hx1_2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2,
      hx13_2, hx14_2, hx15_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2,
      hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
    rw [hsp1] at hsp2; rw [hx13_1] at hx13_2; rw [hx19_1] at hx19_2; have htr2 := htr2.trans htr1
    cases optUc with
    | none =>
      have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 noneCap d8 d16 d24 d28 d32
      rw [v4b_states_from_pb_ekSentCt1Received_none_uc_none_dec F]
      refine SepWPp.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            v4b_optProtoUcHeap A.repAlloc none u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
            ((pbA ↦₆₄ 0x8000000000000004#64) ∗
             v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
             v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
             memRegion (pbA + 152#64) 72) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s2 ∗
             statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
          (Entails.trans
            (sepConj_mono
              (v4e_optProtoUcHeap_none_info A.repAlloc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96)
              (sepConj_mono_left hpb))
            (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; sep_ac_rfl)))) ?_
      apply v4d_sepWPp_pure_left; intro hu0_eq
      rw [hu0_eq] at hx22_2
      apply SepWPp.of_sepWP_ret
      have hnone := Variant4dPlacedBudget.v4d_ekSent_uc_none_2228_to_ret_placed (F := F) hA st s0 s2 out pbA
        noneCap d8 d16 d32 d24 d28 none hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 hx24_2 hx28_2 htr2
      refine SepWP.weaken_pre
        (by dsimp only [v4b_optProtoPolyDecoderHeap]
            exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl)))
        (SepWP.mono hnone fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩ =>
          ⟨⟨evs, hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩)
    | some u =>
      rw [v4b_states_from_pb_ekSentCt1Received_some_uc_none_dec F u]
      have hsome := v4e_ekSent_uc_some_2228_to_ret_placed (F := F) (Qp := Qp) hA hdec st
        s0 s2 out pbA noneCap d8 d16 d32 d24 d28
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u none
        hcl2 hfits hsp0_align hpc2 hrun2 hsp2
        hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hx15_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2
        (fun _ => rfl)
      refine SepWPp.weaken_pre ?_ hsome
      dsimp only [Option.map, v4b_optProtoPolyDecoderHeap]
      exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))
  | some d =>
    dsimp only [Option.map]
    by_cases hpts : d.ptsNeeded = 80#32
    · refine SepWPp.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
            ((pbA ↦₆₄ 0x8000000000000004#64) ∗
             v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
             v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
             memRegion (pbA + 152#64) 72 ∗
             v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1) by sep_ac_rfl))
          (Entails.trans
            (sepConj_mono_left (v4e_optProtoPolyDecoderHeap_some_info A.repAlloc (pbToProtoPolyDecoder d) d0 d8 d16 d24 d28 d32))
            (Entails.of_eq (sepConj_assoc _ _ _)))) ?_
      apply v4d_sepWPp_pure_left; rintro ⟨hd0_lt, hd24_eq⟩
      change d24 = d.ptsNeeded at hd24_eq
      have hd24_80 : d24 = 80#32 := hd24_eq.trans hpts
      have h248 := v4b_step_248_some_eq_to_2228_placed_budget A lim st (ext := ext) s1 pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d0 d8 d16 d28 d32
        ((pbA ↦₆₄ 0x8000000000000004#64) ∗ memRegion (pbA + 152#64) 72 ∗
         v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
         v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt)
        hd0_lt hpc1 hrun1 hx27_1
      refine v4e_seq_clean_p_weaken_lscl_st hcl1 h248 ?_ ?_
      · rw [hd24_80]; exact Entails.of_eq (by sep_ac_rfl)
      intro s2 hpc2 hrun2 hcl2 ⟨_hvm12, hsp2, hx0_2, hx1_2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2,
        hx13_2, hx14_2, hx15_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2,
        hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
      rw [hsp1] at hsp2; rw [hx13_1] at hx13_2; rw [hx19_1] at hx19_2; have htr2 := htr2.trans htr1
      have hx23_2' : s2.readReg64 .x23 = d24.zeroExtend 64 := by rw [hx23_2, hd24_80]; rfl
      cases optUc with
      | none =>
        have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d0 d8 d16 80#32 d28 d32
        rw [v4b_states_from_pb_ekSentCt1Received_none_uc_some_dec F d hpts]
        refine SepWPp.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ =
              v4b_optProtoUcHeap A.repAlloc none u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
              ((pbA ↦₆₄ 0x8000000000000004#64) ∗
               v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
               v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
               memRegion (pbA + 152#64) 72) ∗
              (v4b_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s2 ∗
               statesFromPbJumpTablePlacedAt) by sep_ac_rfl))
            (Entails.trans
              (sepConj_mono
                (v4e_optProtoUcHeap_none_info A.repAlloc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96)
                (sepConj_mono_left hpb))
              (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; sep_ac_rfl)))) ?_
        apply v4d_sepWPp_pure_left; intro hu0_eq
        rw [hu0_eq] at hx22_2
        apply SepWPp.of_sepWP_ret
        have hnone := Variant4dPlacedBudget.v4d_ekSent_uc_none_2228_to_ret_placed (F := F) hA st s0 s2 out pbA
          d0 d8 d16 d32 d24 d28 (some (pbToProtoPolyDecoder d))
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 hx24_2 hx28_2 htr2
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono hnone fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
        have henv : EkSentCt1ReceivedFromPbEnv F { uc := none, receivingCt2 := some d } evs := by
          simp only [EkSentCt1ReceivedFromPbEnv, hpts, ↓reduceIte]; exact hevs
        exact ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩
      | some u =>
        rw [v4b_states_from_pb_ekSentCt1Received_some_uc_some_dec F u d hpts]
        have hfits_2228 : FitsEnv M lim st (EkSent2228SomeEnv F u (some d)) := by
          intro evs hevs; apply hfits evs
          simp only [EkSentCt1ReceivedFromPbEnv, hpts, ↓reduceIte]; exact hevs
        have hsome := v4e_ekSent_uc_some_2228_to_ret_placed (F := F) (Qp := Qp) hA hdec st
          s0 s2 out pbA d0 d8 d16 d32 d24 d28
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u (some d)
          hcl2 hfits_2228 hsp0_align hpc2 hrun2 hsp2
          hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hx15_2
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2' hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2
          (by intro h; nomatch h)
        refine SepWPp.weaken_pre
          (by dsimp only [Option.map]; rw [← hd24_80]; exact Entails.of_eq (by sep_ac_rfl))
          (sepWPp_mono_post hsome fun _sf _Pf ⟨⟨evs, hevs, hPf⟩, hrest⟩ => ?_)
        have henv : EkSentCt1ReceivedFromPbEnv F { uc := some u, receivingCt2 := some d } evs := by
          simp only [EkSentCt1ReceivedFromPbEnv, hpts, ↓reduceIte]; exact hevs
        exact ⟨⟨evs, henv, hPf⟩, hrest⟩
    · apply SepWPp.of_sepWP_ret
      have herr := Variant4dPlacedBudget.v4d_ekSent_err_ptsNeeded_ne_248_placed (F := F) hA st s0 s1 out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
        d0 d8 d16 d24 d28 d32 optUc d hpts hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (SepWP.mono herr fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
      have henv : EkSentCt1ReceivedFromPbEnv F { uc := optUc, receivingCt2 := some d } evs := by
        simp only [EkSentCt1ReceivedFromPbEnv, hpts, ↓reduceIte]; exact hevs
      exact ⟨⟨evs, henv, hPf⟩, hsp_f, hcs_f, htr_f⟩

/-! ## Top-Level `subroutine_ok` Contracts at `lsmpl.base 333` -/

private theorem ekSentCt1Received_ok_of_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : V1State.Chunked.EkSentCt1Received} {Env : List AllocEvent → Prop}
    (hbody : ∀ (st : M.σ) (s0 s2 : State) (out pbA : BitVec 64) (R : SepProp),
      v1StatePtsBound { innerState := some (.ekSentCt1Received s) } →
      FitsEnv M lim st Env → LibsignalCodeLoaded lsmpl s2.mem →
      (s0.sp &&& 15#64 == 0#64) = true → s2.pc = lsmpl.base 333 + 248#64 →
      s2.status = .Running → s2.sp = s0.sp - 2400#64 →
      s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64 →
      s2.readReg64 .x19 = out → s2.readReg64 .x27 = pbA →
      TraceCalleeSaved s2 s0 →
      SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
        (optProtoInnerStateAt A.repAlloc pbA (some (.ekSentCt1Received s)) ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2)
        (fun sf Pf =>
          (∃ evs : List AllocEvent, Env evs ∧
            (Pf ⊢
              resultChunkedStatesAt A.repAlloc (F := F) out
                (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekSentCt1Received s) }) ∗
              memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ekSentCt1Received s) } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [statesFromPbVariantPlacedSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.ekSentCt1Received s)) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some (.ekSentCt1Received s)) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean_lscl_st hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1, _⟩
  have ⟨Tail, htag_eq⟩ : ∃ Tail : SepProp,
      optProtoInnerStateAt A.repAlloc pbA (some (.ekSentCt1Received s)) =
      (pbA ↦₆₄ 0x8000000000000004#64) ∗ Tail :=
    ⟨_, v4b_optProtoInnerStateAt_ekSentCt1Received_eq A.repAlloc pbA s⟩
  have hP1' :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
      memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗ A.pool lim st s1 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.ekSentCt1Received s)) ∗
       statesFromPbJumpTablePlacedAt) ⊢
      (pbA ↦₆₄ 0x8000000000000004#64) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ Tail) ∗
      A.pool lim st s1 := by
    rw [htag_eq]; exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA 0x8000000000000004#64 248#64
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ Tail)
    TaggedVariantDispatch.ekSentCt1Received hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWPp_seq_clean_lscl_st hcl1 hdisp ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, _, _, hx13_2, _, htr2, _⟩
  have hx13_2' : s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64 := by rw [hx13_2]; bv_omega
  have hpre_join :
      (pbA ↦₆₄ 0x8000000000000004#64) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ Tail) ∗
      A.pool lim st s2 ⊢
      optProtoInnerStateAt A.repAlloc pbA (some (.ekSentCt1Received s)) ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2 := by
    rw [htag_eq]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (((pbA ↦₆₄ 0x8000000000000004#64) ∗ Tail) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  exact SepWPp.weaken_pre hpre_join
    (sfpProof_sepWPp_of_states_body_cl_placed_of_env st s0 s2 out pbA
      { innerState := some (.ekSentCt1Received s) } Env _ R
      (hbody st s0 s2 out pbA R hpts hfits hcl2 hsp0_align hpc2 hrun2 hsp2
        hx13_2' hx19_2 hx27_2 htr2))

/-- Exact-envelope (`EkSentCt1ReceivedFromPbEnv F s`) Variant 4 (`InnerState.ekSentCt1Received`,
    `+248`) contract for `<States>::from_pb`. -/
theorem states_from_pb_ekSentCt1Received_ok_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ekSentCt1Received s) }
          (EkSentCt1ReceivedFromPbEnv F s))) :=
  ekSentCt1Received_ok_of_body_placed fun st s0 s2 out pbA _R _hpts hfits hcl2
      hsp0_align hpc2 hrun2 hsp2 hx13_2 hx19_2 hx27_2 htr2 =>
    states_from_pb_ekSentCt1Received_248_placed hA hdec s st hfits
      s0 s2 out pbA hcl2 hsp0_align hpc2 hrun2 hsp2 hx13_2 hx19_2 hx27_2 htr2

/-- Closed `subroutine_ok` for Variant 4 (`InnerState.ekSentCt1Received s`, `+248`) under the
    default linear envelope `StatesFromPbEnv`. -/
theorem states_from_pb_ekSentCt1Received_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.ekSentCt1Received s) })) :=
  ekSentCt1Received_ok_of_body_placed fun st s0 s2 out pbA _R _hpts hfits hcl2
      hsp0_align hpc2 hrun2 hsp2 hx13_2 hx19_2 hx27_2 htr2 =>
    sepWPp_mono_post
      (states_from_pb_ekSentCt1Received_248_placed hA hdec s st
        (fitsEnv_ekSentCt1ReceivedFromPbEnv_of_statesFromPbEnv s hfits)
        s0 s2 out pbA hcl2 hsp0_align hpc2 hrun2 hsp2 hx13_2 hx19_2 hx27_2 htr2)
      fun _sf _Pf ⟨⟨evs, hevs, hPf⟩, hrest⟩ =>
        ⟨⟨evs, ekSentCt1ReceivedFromPbEnv_sub_statesFromPbEnv s hfits hevs, hPf⟩, hrest⟩

abbrev states_from_pb_variant3_placed := @states_from_pb_ekSentCt1Received_ok_ext_placed

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4ePlacedBudget
