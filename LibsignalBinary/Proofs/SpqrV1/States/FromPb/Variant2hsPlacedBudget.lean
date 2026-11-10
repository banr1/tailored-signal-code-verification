/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsgPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsjPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`, `+508`)

Allocator event envelopes, `StatesFromPbEnv` subsumption, and total-correctness Block-`333`
`subroutine_ok` contracts for `InnerState.headerSent` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped CryptoVerification.RustHeap

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.StdStartup SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsProg_333 lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder ProtoAuthenticator ProtoPolynomialDecoder
   ProtoPolynomialEncoder States V1State pbToProtoPolyDecoder pbToProtoPolyEncoder spqrAuthApi
   spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (cap_add_one_beq_zero_false chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb
  (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 optEncoderPtsBound
   resultChunkedStatesAt sp_sub_2400_align statesFromPbJumpTablePlacedAt statesFromPbOnPanic
   statesFromPbSavedCells statesFromPbStack v1StatePtsBound v1_bv_add_add_lit v1_bv_sub_sub_lit
   v1_optProtoAuthHeap v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderHeap_extract_w0
   v1_optProtoPolyEncoderWordsAt v2hs_ekSentWordsAt v2hs_from_pb_headerSent_auth_none_eq
   v2hs_from_pb_headerSent_bad_dk_eq v2hs_from_pb_headerSent_bad_pts_eq
   v2hs_from_pb_headerSent_sendingEk_none_eq v2hs_from_pb_headerSent_uc_none_eq
   v2hs_memRegion_896_split_scratch v2hs_memRegion_896_ucWords_to_976 v2hs_optProtoDecoderHeap
   v2hs_optProtoDecoderWordsAt v2hs_optProtoUcHeap v2hs_pb128At v2hs_stack896ScratchRest
   v2hs_ucWordsAt v2hstop_optProtoAuthHeap_some_extract v2hstop_optProtoDecoderHeap_none_extract
   v2hstop_optProtoDecoderHeap_some_extract v2hstop_optProtoInnerStateAt_headerSent_unpack
   v2hstop_optProtoUcHeap_some_extract v2hstop_pb128_entails_pbEncTailAt v2hstop_pbEncTailAt
   v2hstop_pbEncTailAt_entails_full_224 v4_ptsCap_add_one_ne_zero v4b_vecU8Heap)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth rawUcEkSent
   rawUcEkSent_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecLoopAllocEvents fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbPolysInitEvents
   encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents encoderFromPbPtsLoopEvents
   encoderFromPbPtsSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (StatesFromPbEnv statesFromPbVariantPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlacedBudget
  (sepWPp_seq_clean_lscl_st sfpProof_sepWPp_of_states_body_cl_placed
   sfpProof_sepWPp_of_states_body_cl_placed_of_env)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (spqrBoundedEvs_authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget encoder_from_pb_ok_of_alloc_placed
   seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsb0PlacedBudget
  (v2hs_epilogue_4392_ret_placed v2hs_err_uc_604_to_ret_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudget
  (v2hs_assemble_ekSent_8944_9032_placed_budget v2hs_auth_from_pb_step1_3436_8700_placed
   v2hs_auth_from_pb_step2_8700_8884_placed v2hs_auth_from_pb_step3_8884_8944_placed_freeOnly
   v2hs_check_ptsNeeded_592_placed_budget v2hs_copy_pb_to_stack_508_placed_budget
   v2hs_uc_none_3348_to_4392_placed_budget v2hs_validate_ok_3348_3436_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsgPlacedBudget
  (HeaderSentSomeEnc9036Env HeaderSentSomeEncOptEnv v2hstop_SomeEnc9036HypPlaced
   v2hstop_SomeEnc9036SepWPHypPlaced v2hstop_branch_auth_none_3348_placed
   v2hstop_branch_bad_dk_3348_placed v2hstop_branch_sendingEk_none_9152_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsjPlacedBudget
  (v2hstop_some_enc_9036_to_ret_sepWP_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## Binary Allocator Event Envelopes & `StatesFromPbEnv` Subsumption -/

/-- Exact allocator event envelope for `ProtoAuthenticator` clone + input deallocations
    (`+3436 -> +8944`, plus any trailing `FreeOnlyEvs` cleanup on `sendingEk = none`). -/
def HeaderSentAuthEnv (auth : ProtoAuthenticator) (evs : List AllocEvent) : Prop :=
  ∃ evs_free : List AllocEvent, FreeOnlyEvs evs_free ∧ evs = authFromPbEvents auth ++ evs_free

/-- Complete binary allocator event envelope from `+3436 -> s0.x30` (`u.dk.length = 2400`,
    `u.auth = some auth`). -/
def HeaderSent3436Env (s : V1State.Chunked.HeaderSent) (auth : ProtoAuthenticator)
    (evs : List AllocEvent) : Prop :=
  match s.sendingEk with
  | none => HeaderSentAuthEnv auth evs
  | some pbEnc =>
    HeaderSentAuthEnv auth evs ∨
      ∃ evs1 evs2 : List AllocEvent,
        evs = evs1 ++ evs2 ∧
        HeaderSentAuthEnv auth evs1 ∧
        HeaderSentSomeEnc9036Env s pbEnc evs2

/-- Complete binary allocator event envelope from `+3348 -> s0.x30` (after optional `ptsNeeded`
    validation succeeds). -/
def HeaderSent3348Env (s : V1State.Chunked.HeaderSent) (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => FreeOnlyEvs evs
  | some u =>
    if (BitVec.ofNat 64 u.dk.length == 2400#64) = true then
      match u.auth with
      | none => FreeOnlyEvs evs
      | some auth => HeaderSent3436Env s auth evs
    else
      FreeOnlyEvs evs

/-- Complete binary allocator event envelope for Variant 2 (`InnerState.headerSent s`, `+508 -> s0.x30`)
    of `<spqr::v1::chunked::states::States>::from_pb`. -/
def HeaderSentFromPbEnv (s : V1State.Chunked.HeaderSent) (evs : List AllocEvent) : Prop :=
  match s.receivingCt1 with
  | none => HeaderSent3348Env s evs
  | some d =>
    if (d.ptsNeeded == 480#32) = true then
      HeaderSent3348Env s evs
    else
      FreeOnlyEvs evs

theorem headerSentAuthEnv_imp_3436 {s : V1State.Chunked.HeaderSent} {auth : ProtoAuthenticator}
    {evs : List AllocEvent} (h : HeaderSentAuthEnv auth evs) :
    HeaderSent3436Env s auth evs := by
  unfold HeaderSent3436Env
  cases s.sendingEk with
  | none => exact h
  | some _ => exact Or.inl h

theorem fitsEvents_auth_of_headerSent3436Env {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.HeaderSent} {auth : ProtoAuthenticator}
    (h : FitsEnv M lim st (HeaderSent3436Env s auth)) :
    FitsEvents M lim st (authFromPbEvents auth) :=
  h (authFromPbEvents auth)
    (headerSentAuthEnv_imp_3436 ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩)

theorem fitsEnv_someEnc9036_of_headerSent3436Env {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {s : V1State.Chunked.HeaderSent} {auth : ProtoAuthenticator}
    {pbEnc : PolynomialEncoder} {evs1 : List AllocEvent}
    (henc : s.sendingEk = some pbEnc)
    (hfits : FitsEnv M lim st (HeaderSent3436Env s auth))
    (hevs1 : HeaderSentAuthEnv auth evs1) :
    FitsEnv M lim (M.stepEvents evs1 st) (HeaderSentSomeEnc9036Env s pbEnc) := by
  intro evs2 hevs2
  have hmem : HeaderSent3436Env s auth (evs1 ++ evs2) := by
    unfold HeaderSent3436Env
    rw [henc]
    exact Or.inr ⟨evs1, evs2, rfl, hevs1, hevs2⟩
  exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfits (evs1 ++ evs2) hmem)).2

theorem fitsEnv_3436_of_3348 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.HeaderSent} {u : V1State.Unchunked.EkSent} {auth : ProtoAuthenticator}
    (huc : s.uc = some u) (hdk_len : u.dk.length = 2400) (hauth : u.auth = some auth)
    (h : FitsEnv M lim st (HeaderSent3348Env s)) :
    FitsEnv M lim st (HeaderSent3436Env s auth) := by
  intro evs hevs
  apply h evs
  have hdk_beq : (BitVec.ofNat 64 u.dk.length == 2400#64) = true := by
    rw [hdk_len]; decide
  simp only [HeaderSent3348Env, huc, hdk_beq, ↓reduceIte, hauth]
  exact hevs

theorem fitsEnv_3348_of_fromPb_none {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.HeaderSent} (hdec : s.receivingCt1 = none)
    (h : FitsEnv M lim st (HeaderSentFromPbEnv s)) :
    FitsEnv M lim st (HeaderSent3348Env s) := by
  intro evs hevs
  apply h evs
  unfold HeaderSentFromPbEnv
  rw [hdec]
  exact hevs

theorem fitsEnv_3348_of_fromPb_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.HeaderSent} {d : PolynomialDecoder}
    (hdec : s.receivingCt1 = some d) (hpts : (d.ptsNeeded == 480#32) = true)
    (h : FitsEnv M lim st (HeaderSentFromPbEnv s)) :
    FitsEnv M lim st (HeaderSent3348Env s) := by
  intro evs hevs
  apply h evs
  simp only [HeaderSentFromPbEnv, hdec, hpts, ↓reduceIte]
  exact hevs

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
      (simp only [List.mem_singleton] at hev
       subst hev
       refine ⟨by decide, Nat.le_trans (by decide) (Nat.le_max_right _ 256), ?_,
         (fun _ _ _ h => nomatch h)⟩
       intro al r h
       cases h
       decide)

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
      have ih := length_le_sum_map_length htl
      omega

private theorem spqrBoundedEvs_replicate_alloc2 :
    ∀ n : Nat, SpqrBoundedEvs n 256 ((List.replicate n (rustAllocEvents 2 2)).flatten)
  | 0 => SpqrBoundedEvs.nil 0 256
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons]
    have h1 : SpqrBoundedEvs 1 256 (rustAllocEvents 2 2) :=
      SpqrBoundedEvs.mono (Nat.le_refl 1) (by decide)
        (spqrBoundedEvs_rustAllocEvents_align2 2 (by decide))
    have h2 := spqrBoundedEvs_replicate_alloc2 n
    have happ := SpqrBoundedEvs.append h1 h2
    rw [Nat.add_comm 1 n, Nat.max_self] at happ
    exact happ

private theorem spqrBoundedEvs_encoderFromPbEnv {pb : ProtoPolynomialEncoder} {L : Nat}
    (hsum : (pb.pts.map List.length).sum + (pb.polys.map List.length).sum ≤ L)
    (hmax : 2 * L + 256 ≤ MallocngMaxAllocSize)
    {evs : List AllocEvent} (hevs : EncoderFromPbEnv pb evs) :
    SpqrBoundedEvs 32 (2 * L + 256) evs := by
  rcases hevs with ⟨evs_alloc, evs_free, rfl, halloc, hfree⟩
  have hbody : SpqrBoundedEvs 32 (2 * L + 256) evs_alloc := by
    rcases halloc with rfl | ⟨hpts16, _, rfl⟩ | ⟨_, hpolys16, rfl⟩
    · exact SpqrBoundedEvs.nil 32 (2 * L + 256)
    · unfold encoderFromPbPtsLoopEvents
      obtain ⟨hlen_tw, hmem_tw⟩ := takeWhile_len_and_mem (fun bs : List (BitVec 8) => bs.length % 2 == 0) pb.pts
      have hfm := spqrBoundedEvs_flatMap (2 * L + 256) encoderFromPbPtsSlotEvents
        (pb.pts.takeWhile (fun bs => bs.length % 2 == 0)) fun bs hbs => by
          have hbs_len := length_le_sum_map_length (hmem_tw bs hbs)
          unfold encoderFromPbPtsSlotEvents
          split
          · exact SpqrBoundedEvs.nil 1 (2 * L + 256)
          · exact SpqrBoundedEvs.mono (Nat.le_refl 1) (by omega)
              (spqrBoundedEvs_rustAllocEvents_align2 (2 * bs.length) (by omega))
      exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) hfm
    · have hinit : SpqrBoundedEvs 16 (2 * L + 256) encoderFromPbPolysInitEvents :=
        SpqrBoundedEvs.mono (Nat.le_refl 16) (by omega) (spqrBoundedEvs_replicate_alloc2 16)
      unfold encoderFromPbPolysLoopEvents
      obtain ⟨hlen_tw, hmem_tw⟩ := takeWhile_len_and_mem
        (fun bs : List (BitVec 8) => !bs.isEmpty && (bs.length % 2 == 0)) pb.polys
      have hfm := spqrBoundedEvs_flatMap (2 * L + 256) encoderFromPbPolysSlotEvents
        (pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))) fun bs hbs => by
          have hbs_len := length_le_sum_map_length (hmem_tw bs hbs)
          unfold encoderFromPbPolysSlotEvents
          have ha : SpqrBoundedEvs 1 (2 * L + 256) (rustAllocEvents bs.length 2) :=
            SpqrBoundedEvs.mono (Nat.le_refl 1) (by omega)
              (spqrBoundedEvs_rustAllocEvents_align2 bs.length (by omega))
          have hd_free : FreeOnlyEvs (rustDeallocEvents 2 2) := by
            intro ev hev
            simp only [rustDeallocEvents, List.mem_singleton] at hev
            exact ⟨2, 2, hev⟩
          have hd := SpqrBoundedEvs.of_freeOnly hd_free
          exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append ha hd)
      have hloop : SpqrBoundedEvs 16 (2 * L + 256)
          ((pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))).flatMap
            encoderFromPbPolysSlotEvents) :=
        SpqrBoundedEvs.mono (by omega) (Nat.le_refl _) hfm
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append hinit hloop)
  exact SpqrBoundedEvs.mono (Nat.le_refl 32) (by omega)
    (SpqrBoundedEvs.append hbody (SpqrBoundedEvs.of_freeOnly hfree))

private theorem spqrBoundedEvs_fromPbDecEnv {pb : ProtoPolynomialDecoder} {L : Nat}
    (hsum : (pb.pts.map List.length).sum ≤ L)
    (hmax : L + 256 ≤ MallocngMaxAllocSize)
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

private theorem polyEnc_pts_polys_sum_le_encodeRaw (m : PolynomialEncoder) :
    (m.pts.map List.length).sum + (m.polys.map List.length).sum ≤
      (PolynomialEncoder.encodeRaw m).length := by
  unfold PolynomialEncoder.encodeRaw
  simp only [List.length_append]
  have h1 := sum_length_le_encodeRepeatedBytes 2#32 m.pts
  have h2 := sum_length_le_encodeRepeatedBytes 3#32 m.polys
  omega

private theorem polyDec_pts_sum_le_encodeRaw (m : PolynomialDecoder) :
    (m.pts.map List.length).sum ≤ (PolynomialDecoder.encodeRaw m).length := by
  unfold PolynomialDecoder.encodeRaw
  simp only [List.length_append]
  have h1 := sum_length_le_encodeRepeatedBytes 3#32 m.pts
  omega

private theorem headerSent_components_le_encodeRaw (s : V1State.Chunked.HeaderSent) :
    optRaw rawUcEkSent s.uc +
      optRaw (fun m : PolynomialEncoder => (m.pts.map List.length).sum + (m.polys.map List.length).sum) s.sendingEk +
      optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) s.receivingCt1 ≤
      (V1State.encodeRaw { innerState := some (.headerSent s) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.HeaderSent.encodeRaw 3#32 s
  have h1 := length_le_encodeOptMessage V1State.Unchunked.EkSent.encodeRaw
    rawUcEkSent rawUcEkSent_le_encodeRaw 1#32 s.uc
  have h2 := length_le_encodeOptMessage PolynomialEncoder.encodeRaw
    (fun m => (m.pts.map List.length).sum + (m.polys.map List.length).sum)
    polyEnc_pts_polys_sum_le_encodeRaw 2#32 s.sendingEk
  have h3 := length_le_encodeOptMessage PolynomialDecoder.encodeRaw
    (fun m => (m.pts.map List.length).sum)
    polyDec_pts_sum_le_encodeRaw 3#32 s.receivingCt1
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.HeaderSent.encodeRaw] at h0 ⊢
  simp only [List.length_append] at h0
  omega

private theorem spqrBoundedEvs_someEnc9036Env {s : V1State.Chunked.HeaderSent}
    {pbEnc : PolynomialEncoder} {L : Nat}
    (henc_sum : (pbEnc.pts.map List.length).sum + (pbEnc.polys.map List.length).sum ≤ L)
    (hdec_sum : optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) s.receivingCt1 ≤ L)
    (hmax : 4 * L + 4096 ≤ MallocngMaxAllocSize)
    {evs : List AllocEvent} (hevs : HeaderSentSomeEnc9036Env s pbEnc evs) :
    SpqrBoundedEvs 48 (2 * L + 256) evs := by
  have hpbe : ((pbToProtoPolyEncoder pbEnc).pts.map List.length).sum +
      ((pbToProtoPolyEncoder pbEnc).polys.map List.length).sum ≤ L := by
    simpa [pbToProtoPolyEncoder] using henc_sum
  unfold HeaderSentSomeEnc9036Env at hevs
  revert hevs
  cases fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | error _ =>
    intro hevs
    exact SpqrBoundedEvs.mono (by decide) (Nat.le_refl _)
      (spqrBoundedEvs_encoderFromPbEnv hpbe (by omega) hevs)
  | ok _ =>
    cases hrec : s.receivingCt1 with
    | none =>
      intro hevs
      exact SpqrBoundedEvs.mono (by decide) (Nat.le_refl _)
        (spqrBoundedEvs_encoderFromPbEnv hpbe (by omega) hevs)
    | some pbDec =>
      rintro (hevs | ⟨evs1, evs2, rfl, h1, h2⟩)
      · exact SpqrBoundedEvs.mono (by decide) (Nat.le_refl _)
          (spqrBoundedEvs_encoderFromPbEnv hpbe (by omega) hevs)
      · have hpbd : ((pbToProtoPolyDecoder pbDec).pts.map List.length).sum ≤ L := by
          rw [hrec] at hdec_sum
          simpa [pbToProtoPolyDecoder, optRaw] using hdec_sum
        have hb1 := spqrBoundedEvs_encoderFromPbEnv hpbe (by omega) h1
        have hb2 := spqrBoundedEvs_fromPbDecEnv hpbd (by omega) h2
        exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append hb1 hb2)

/-- Every event sequence in `HeaderSentFromPbEnv s` satisfies the linear default envelope
    `StatesFromPbEnv { innerState := some (.headerSent s) }` whenever `FitsEnv` holds. -/
theorem headerSentFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.HeaderSent)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.headerSent s) }))
    {evs : List AllocEvent} (hevs : HeaderSentFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.headerSent s) } evs := by
  let pb : V1State := { innerState := some (.headerSent s) }
  let L : Nat := (V1State.encodeRaw pb).length
  change SpqrBoundedEvs 128 (4 * L + 4096) evs
  let m := min (4 * L + 4096) MallocngMaxAllocSize
  have hm_env : StatesFromPbEnv pb [.alloc m] := by
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.min_le_right _ _, Nat.min_le_left _ _,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  have hm_fit : FitsEvents M lim st [.alloc m] := hfits [.alloc m] hm_env
  rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
  have hm_req : m ≤ M.stepReserve (.alloc m) st := M.req_le_stepReserve (.alloc m) st
  have hmax : 4 * L + 4096 ≤ MallocngMaxAllocSize := by
    dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
    omega
  have hcomp : optRaw rawUcEkSent s.uc +
      optRaw (fun m : PolynomialEncoder => (m.pts.map List.length).sum + (m.polys.map List.length).sum) s.sendingEk +
      optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) s.receivingCt1 ≤ L :=
    headerSent_components_le_encodeRaw s
  have h3348_sub : ∀ {evs' : List AllocEvent}, HeaderSent3348Env s evs' →
      SpqrBoundedEvs 128 (4 * L + 4096) evs' := by
    intro evs' h3348
    unfold HeaderSent3348Env at h3348
    revert h3348
    cases huc : s.uc with
    | none =>
      intro hfree
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hfree)
    | some u =>
      dsimp only
      split
      · cases hauth : u.auth with
        | none =>
          intro hfree
          exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hfree)
        | some auth =>
          intro h3436
          have hauth_len : auth.rootKey.length + auth.macKey.length ≤ L := by
            rw [huc] at hcomp
            dsimp only [optRaw, rawUcEkSent] at hcomp
            rw [hauth] at hcomp
            dsimp only [optRaw, rawAuth] at hcomp
            omega
          have hauth_bound : ∀ {ea : List AllocEvent}, HeaderSentAuthEnv auth ea →
              SpqrBoundedEvs 2 L ea := by
            rintro ea ⟨ef, hfree, rfl⟩
            have hbr := spqrBoundedEvs_authKeyCloneEvents (bs := auth.rootKey) (by omega)
            have hbm := spqrBoundedEvs_authKeyCloneEvents (bs := auth.macKey) (by omega)
            have hba := SpqrBoundedEvs.append hbr hbm
            exact SpqrBoundedEvs.mono (by decide) (by omega)
              (SpqrBoundedEvs.append hba (SpqrBoundedEvs.of_freeOnly hfree))
          unfold HeaderSent3436Env at h3436
          revert h3436
          cases henc : s.sendingEk with
          | none =>
            intro ha
            exact SpqrBoundedEvs.mono (by decide) (by omega) (hauth_bound ha)
          | some pbEnc =>
            rintro (ha | ⟨e1, e2, rfl, ha1, he2⟩)
            · exact SpqrBoundedEvs.mono (by decide) (by omega) (hauth_bound ha)
            · have henc_sum : (pbEnc.pts.map List.length).sum + (pbEnc.polys.map List.length).sum ≤ L := by
                rw [henc] at hcomp
                dsimp only [optRaw] at hcomp
                omega
              have hdec_sum : optRaw (fun m : PolynomialDecoder => (m.pts.map List.length).sum) s.receivingCt1 ≤ L := by
                omega
              have hb1 := hauth_bound ha1
              have hb2 := spqrBoundedEvs_someEnc9036Env henc_sum hdec_sum hmax he2
              exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append hb1 hb2)
      · intro hfree
        exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hfree)
  unfold HeaderSentFromPbEnv at hevs
  revert hevs
  cases s.receivingCt1 with
  | none =>
    intro h3348
    exact h3348_sub h3348
  | some d =>
    dsimp only
    split
    · intro h3348
      exact h3348_sub h3348
    · intro hfree
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hfree)

theorem fitsEnv_headerSentFromPbEnv_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.HeaderSent)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.headerSent s) })) :
    FitsEnv M lim st (HeaderSentFromPbEnv s) :=
  fun evs hevs => hfits evs (headerSentFromPbEnv_sub_statesFromPbEnv s hfits hevs)

/-! ## Budget-Threaded Continuations (`+3436`, `+3348`, `+508 -> s0.x30`) -/

private theorem sepWPp_seq_exists_lscl_st [LibsignalPlacement] {α : Type}
    {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : α → State → SepProp} {Q_mid : α → State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => ∃ a : α, (Pm ⊢ P_mid a sm) ∧ Q_mid a sm))
    (h2 : ∀ (a : α) (sm : State), sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid a sm → SepWPp prog target sm (P_mid a sm) Q Qp) :
    SepWPp prog target s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨a, hPm, hQ⟩ hcl' =>
      SepWPp.weaken_pre hPm (h2 a sm hpc hrun hcl' hQ))

private theorem sepWPp_mono_post {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog target s P Q Qp oom)
    (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog target s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq⟩ | hrest⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hrest⟩

/-- `Qpan`-polymorphic `+9036 -> s0.x30` continuation shape unifying `v2hstop_SomeEnc9036HypPlaced`
    (`statesFromPbOnPanic`) and `v2hstop_SomeEnc9036SepWPHypPlaced` (`⌜False⌝` panic). -/
def v2hstop_SomeEnc9036HypPlacedQpan [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State))
    (s : V1State.Chunked.HeaderSent)
    (Qpan : State → SepProp → (State → SepProp → Prop)) : Prop :=
  ∀ (st : M.σ) (s0 sm : State) (out pbA : BitVec 64) (R : SepProp)
    (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder)
    (u8 u16 u24 u40 u48 u72 u80 pa1 pa2 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64),
    LibsignalCodeLoaded lsmpl sm.mem →
    optEncoderPtsBound s.sendingEk →
    (match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true) →
    FitsEnv M lim st (HeaderSentSomeEnc9036Env s pbEnc) →
    s.uc = some u → u.dk.length = 2400 → u.auth = some auth → s.sendingEk = some pbEnc →
    u8.toNat < 2 ^ 63 → u24 = 2400#64 → u48 = BitVec.ofNat 64 auth.rootKey.length →
    u72 = BitVec.ofNat 64 auth.macKey.length → u80 = u.epoch → auth.rootKey.length < 2 ^ 63 →
    (s0.sp &&& 15#64 == 0#64) = true →
    sm.pc = lsmpl.base 333 + 9036#64 →
    sm.status = .Running → sm.sp = s0.sp - 2400#64 →
    sm.readReg64 .x0 = pa2 → sm.readReg64 .x8 = w0 → sm.readReg64 .x9 = u24 →
    sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 → sm.readReg64 .x19 = out →
    sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 →
    sm.readReg64 .x22 = d_w0 → sm.readReg64 .x23 = pa1 → sm.readReg64 .x25 = u48 →
    sm.readReg64 .x26 = u8 → sm.readReg64 .x27 = pbA → sm.readReg64 .x28 = u80 →
    TraceCalleeSaved sm s0 →
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) sm
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st sm)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSentSomeEncOptEnv s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (Qpan s0 R)

theorem v2hstop_someEnc9036HypPlacedQpan_of_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : V1State.Chunked.HeaderSent}
    {Qpan : State → SepProp → (State → SepProp → Prop)}
    (h : v2hstop_SomeEnc9036SepWPHypPlaced M A lim F ext s) :
    v2hstop_SomeEnc9036HypPlacedQpan M A lim F ext s Qpan :=
  fun st s0 sm out pbA _R u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
      hcl hpts hdec hfits huc hdk hauth henc hu8 hu24 hu48 hu72 hu80 hrk
      hsp0 hpc hrun hsp hx0 hx8 hx9 hx10 hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 htr =>
    SepWPp.of_sepWP_ret
      (h st s0 sm out pbA u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
        hcl hpts hdec hfits huc hdk hauth henc hu8 hu24 hu48 hu72 hu80 hrk
        hsp0 hpc hrun hsp hx0 hx8 hx9 hx10 hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 htr)

set_option maxHeartbeats 800000 in
theorem v2hstop_headerSent_3436_to_ret_qpan_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Qpan : State → SepProp → (State → SepProp → Prop)}
    (hA : FromPbAllocHooksBudget M A lim ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036HypPlacedQpan M A lim F ext s Qpan)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true)
    (st : M.σ) (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (hfits : FitsEnv M lim st (HeaderSent3436Env s auth))
    (huc : s.uc = some u) (hdk_len : u.dk.length = 2400) (hauth : u.auth = some auth)
    (s0 s2 : State) (out pbA : BitVec 64) (R : SepProp)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w184 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (hu8_lt : u8.toNat < 2 ^ 63) (hu24_val : u24 = 2400#64)
    (hu48_eq : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72_eq : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hu80_eq : u80 = u.epoch) (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 3436#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out) (hx20_2 : s2.readReg64 .x20 = u48)
    (hx21_2 : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_2 : s2.readReg64 .x22 = d_w0) (hx24_2 : s2.readReg64 .x24 = u56)
    (hx25_2 : s2.readReg64 .x25 = u64) (hx26_2 : s2.readReg64 .x26 = u32)
    (hx27_2 : s2.readReg64 .x27 = pbA)
    (hx28_2 : s2.readReg64 .x28 = u80) (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u32 u40 auth.rootKey ∗
        vecU8Payload A.repAlloc u56 u64 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s2)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSent3436Env s auth evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (Qpan s0 R) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hx20_2' : s2.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length := by rw [hx20_2, hu48_eq]
  have hfits_auth : FitsEvents M lim st (authFromPbEvents auth) :=
    fitsEvents_auth_of_headerSent3436Env hfits
  obtain ⟨hfits_rk, hfits_mk⟩ :=
    (fitsEvents_append M lim (authKeyCloneEvents auth.rootKey) (authKeyCloneEvents auth.macKey) st).mp hfits_auth
  let Frame3436 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
    v2hs_stack896ScratchRest fsp ∗ v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
    vecU8Payload A.repAlloc u56 u64 auth.macKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt fsp encoderFromPbStack ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    vecU8Payload A.repAlloc u32 u40 auth.rootKey ∗ A.pool lim st s2 ∗ Frame3436 by
    dsimp only [Frame3436, fsp]; sep_ac_rfl)) ?_
  refine sepWPp_seq_exists_lscl_st hcl2
    (v2hs_auth_from_pb_step1_3436_8700_placed hA.toPlacedBudget st s0 s2 fsp out d_w0
      u32 u40 u56 u64 u80 auth Frame3436 hfits_rk hfsp_align hpc2 hrun2 hsp2
      hx19_2 hx20_2' hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2) ?_
  intro pa1 s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3⟩
  let st1 := M.stepEvents (authKeyCloneEvents auth.rootKey) st
  let Frame8700 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
    vecU8Payload A.repAlloc (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗
    ((fsp + 232#64) ↦₆₄ u72) ∗ vecU8Payload A.repAlloc u56 u64 auth.macKey ∗
    A.pool lim st1 s3 ∗ Frame8700 by dsimp only [Frame3436, Frame8700]; sep_ac_rfl)) ?_
  refine sepWPp_seq_exists_lscl_st hcl3
    (v2hs_auth_from_pb_step2_8700_8884_placed hA.toPlacedBudget st1 s0 s3 fsp out d_w0 pa1 w184
      u32 u56 u64 u72 auth Frame8700 hfits_mk hfsp_align hpc3 hrun3 hsp3
      hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hu72_eq htr3) ?_
  intro pa2 s4 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, htr4⟩
  let st2 := M.stepEvents (authKeyCloneEvents auth.macKey) st1
  let Rest8884 : SepProp :=
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗ memRegion (fsp + 240#64) 736 ∗
    v2hs_stack896ScratchRest fsp ∗ v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
    vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt fsp encoderFromPbStack ∗ ((fsp + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗
    vecCapPtrDealloc A.repAlloc u32 u40 ∗ vecCapPtrDealloc A.repAlloc u56 u64 ∗
    A.pool lim st2 s4 ∗ Rest8884 by
    dsimp only [Frame8700, Rest8884]; rw [← hu48_eq, ← hu72_eq]; sep_ac_rfl)) ?_
  refine sepWPp_seq_exists_lscl_st
    (mid := lsmpl.base 333 + 8944#64)
    (P_mid := fun evs_free s5 =>
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2400#64 + 200#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
      A.pool lim (M.stepEvents evs_free st2) s5 ∗
      Rest8884)
    (Q_mid := fun evs_free s5 =>
      FreeOnlyEvs evs_free ∧
      s5.sp = s0.sp - 2400#64 ∧
      s5.readReg64 .x19 = out ∧
      s5.readReg64 .x21 = s4.readReg64 .x21 ∧
      s5.readReg64 .x22 = d_w0 ∧
      s5.readReg64 .x23 = pa1 ∧
      s5.readReg64 .x25 = BitVec.ofNat 64 auth.rootKey.length ∧
      s5.readReg64 .x26 = pa1 >>> 8 ∧
      s5.readReg64 .x27 = s4.readReg64 .x27 ∧
      s5.readReg64 .x28 = u80 ∧
      TraceCalleeSaved s5 s0)
    hcl4
    (SepWP.mono
      (v2hs_auth_from_pb_step3_8884_8944_placed_freeOnly hA.toPlacedBudget st2 s0 s4 out d_w0 pa1
        u32 u40 u56 u64 u80 auth Rest8884 hr_lt63 hsp0_align hpc4 hrun4 hsp4
        hx19_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 htr4)
      fun _ _ _ _ ⟨evs_free, hfree3, hP5, hregs5⟩ => ⟨evs_free, hP5, hfree3, hregs5⟩) ?_
  intro evs_free s5 hpc5 hrun5 hcl5 ⟨hfree3, hsp5, hx19_5, hx21_5, hx22_5, hx23_5, hx25_5, hx26_5, hx27_5, hx28_5, htr5⟩
  let st3 := M.stepEvents evs_free st2
  have hst3_eq : st3 = M.stepEvents (authFromPbEvents auth ++ evs_free) st := by
    dsimp only [st3, st2, st1, authFromPbEvents]
    rw [M.stepEvents_append, M.stepEvents_append]
  have hx25_5' : s5.readReg64 .x25 = u48 := by rw [hx25_5, hu48_eq]
  let Rest8944 : SepProp :=
    stackAt fsp encoderFromPbStack ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
    ((fsp + 224#64) ↦₆₄ u80) ∗ memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
    v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
    vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
    ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
    v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
    memRegion (fsp + 1072#64) 1232 ∗ Rest8944 ∗ A.pool lim st3 s5 by
    dsimp only [Rest8884, Rest8944, fsp]; rw [← hu48_eq]; sep_ac_rfl)) ?_
  refine sepWPp_seq_clean_lscl_st hcl5
    (v2hs_assemble_ekSent_8944_9032_placed_budget A lim st3 (ext := ext) s0 s5 out d_w0 pa1 pa2
      u8 u16 u24 u48 u72 u80 w0 w8 w16 w24 w32 w40 w48 Rest8944
      hsp0_align hpc5 hrun5 hsp5 hx19_5 hx22_5 hx23_5 hx25_5' hx26_5 hx28_5 htr5) ?_
  intro sm hpcm hrunm hclm ⟨_hvmm, hspm, hx0m, hx8m, hx9m, hx10m, hx19m, hx21m, hx22m, hx23m, hx25m, hx26m, hx27m, hx28m, htrm⟩
  have hx21m' : sm.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by
    rw [hx21m, hx21_5, hx21_4, hx21_3, hx21_2]
  have hx27m' : sm.readReg64 .x27 = pbA := by
    rw [hx27m, hx27_5, hx27_4, hx27_3, hx27_2]
  cases henc : s.sendingEk with
  | none =>
    rw [v2hs_from_pb_headerSent_sendingEk_none_eq F s u auth hdec_ok huc hdk_len hauth henc]
    dsimp only [Rest8944]
    rw [henc, show (none : Option PolynomialEncoder).map pbToProtoPolyEncoder = none from rfl]
    dsimp only [v1_optProtoPolyEncoderHeap]
    have hpb_col := v2hstop_pbEncTailAt_entails_full_224 pbA w8 w16 w24 w32 w40 w48
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
      (⌜w0 = noneCap⌝ ∗
       (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
        ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
        ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
        memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 192 ∗
        v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
        memRegion (fsp + 1344#64) 960 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st3 sm ∗
        statesFromPbJumpTablePlacedAt)) by dsimp only [fsp]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (show _ =
        ⌜w0 = noneCap⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗
         ((fsp + 176#64) ↦₆₄ u16) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗
         ((fsp + 216#64) ↦₆₄ u40) ∗ ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
         memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
         v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
         vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 192 ∗
         v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
         memRegion (fsp + 1344#64) 960 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st3 sm ∗
         (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)))) ?_
    refine SepWPp.pure_elim fun hw0 => ?_
    have hw0_beq : (w0 + 1#64 == 0#64) = true := by rw [hw0]; decide
    simp only [hw0_beq, ↓reduceIte] at hpcm
    apply SepWPp.of_sepWP_ret
    have hret := v2hstop_branch_sendingEk_none_9152_placed (F := F) hA st3 s0 sm out u.dk auth
      u8 u16 u24 u40 u48 u72 u80 pa1 pa2 w0 w8 w16 w24 w32 w40 w48
      (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hu48_eq hu72_eq hsp0_align hpcm hrunm hspm hx0m hx19m hx22m hx25m hx26m htrm
    refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; try sep_ac_rfl))
      (SepWP.mono hret fun sf Pf _ _ ⟨evs_end, hfree_end, hPf, hspf, hcsf, htrf⟩ => ?_)
    have hevs_tot : HeaderSent3436Env s auth (authFromPbEvents auth ++ (evs_free ++ evs_end)) := by
      unfold HeaderSent3436Env
      rw [henc]
      exact ⟨evs_free ++ evs_end, hfree3.append hfree_end, rfl⟩
    refine ⟨⟨authFromPbEvents auth ++ (evs_free ++ evs_end), hevs_tot, ?_⟩, hspf, hcsf, htrf⟩
    have hst_tot : M.stepEvents evs_end st3 =
        M.stepEvents (authFromPbEvents auth ++ (evs_free ++ evs_end)) st := by
      rw [hst3_eq, ← M.stepEvents_append, List.append_assoc]
    rw [← hst_tot]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
  | some pbEnc =>
    dsimp only [Rest8944]
    rw [henc, show (some pbEnc : Option PolynomialEncoder).map pbToProtoPolyEncoder = some (pbToProtoPolyEncoder pbEnc) from rfl]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
      (stackAt fsp encoderFromPbStack ∗
       ((fsp + 96#64) ↦₆₄ u24) ∗ ((fsp + 152#64) ↦₆₄ u8) ∗ ((fsp + 176#64) ↦₆₄ u16) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ u48) ∗ ((fsp + 216#64) ↦₆₄ u40) ∗
       ((fsp + 224#64) ↦₆₄ u80) ∗ ((fsp + 232#64) ↦₆₄ u72) ∗
       memRegion (fsp + 240#64) 736 ∗ v2hs_stack896ScratchRest fsp ∗
       v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u48 pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc u72 pa2 auth.macKey ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (fsp + 1072#64) 192 ∗
       v2hs_ekSentWordsAt (fsp + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
       memRegion (fsp + 1344#64) 960 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
       A.pool lim st3 sm) by dsimp only [fsp]; sep_ac_rfl))
      (sepConj_mono_left (v1_optProtoPolyEncoderHeap_extract_w0 A.repAlloc (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48))) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hw0_lt => ?_
    have hw0_beq : (w0 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw0_lt)
    simp only [hw0_beq, Bool.false_eq_true, ↓reduceIte] at hpcm
    have hevs_auth1 : HeaderSentAuthEnv auth (authFromPbEvents auth ++ evs_free) :=
      ⟨evs_free, hfree3, rfl⟩
    have hfits9036 : FitsEnv M lim st3 (HeaderSentSomeEnc9036Env s pbEnc) := by
      rw [hst3_eq]
      exact fitsEnv_someEnc9036_of_headerSent3436Env henc hfits hevs_auth1
    have h9036 := hsome_enc_9036 st3 s0 sm out pbA R u auth pbEnc u8 u16 u24 u40 u48 u72 u80 pa1 pa2
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
      hclm hpts hdec_ok hfits9036 huc hdk_len hauth henc hu8_lt hu24_val hu48_eq hu72_eq hu80_eq hr_lt63
      hsp0_align hpcm hrunm hspm hx0m hx8m hx9m hx10m hx19m hx21m' hx22m hx23m hx25m hx26m hx27m' hx28m htrm
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [fsp]; try sep_ac_rfl))
      (sepWPp_mono_post h9036 fun sf Pf ⟨⟨evs2, hevs2, hPf⟩, hspf, hcsf, htrf⟩ => ?_)
    have hevs2' : HeaderSentSomeEnc9036Env s pbEnc evs2 := by
      unfold HeaderSentSomeEncOptEnv at hevs2
      rwa [henc] at hevs2
    have hevs_tot : HeaderSent3436Env s auth ((authFromPbEvents auth ++ evs_free) ++ evs2) := by
      unfold HeaderSent3436Env
      rw [henc]
      exact Or.inr ⟨authFromPbEvents auth ++ evs_free, evs2, rfl, hevs_auth1, hevs2'⟩
    refine ⟨⟨(authFromPbEvents auth ++ evs_free) ++ evs2, hevs_tot, ?_⟩, hspf, hcsf, htrf⟩
    rw [hst3_eq, ← M.stepEvents_append] at hPf
    exact hPf

theorem v2hstop_headerSent_3436_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036HypPlaced M A lim F ext s)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true)
    (st : M.σ) (u : V1State.Unchunked.EkSent) (auth : ProtoAuthenticator)
    (hfits : FitsEnv M lim st (HeaderSent3436Env s auth))
    (huc : s.uc = some u) (hdk_len : u.dk.length = 2400) (hauth : u.auth = some auth)
    (s0 s2 : State) (out pbA : BitVec 64) (R : SepProp)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w184 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (hu8_lt : u8.toNat < 2 ^ 63) (hu24_val : u24 = 2400#64)
    (hu48_eq : u48 = BitVec.ofNat 64 auth.rootKey.length)
    (hu72_eq : u72 = BitVec.ofNat 64 auth.macKey.length)
    (hu80_eq : u80 = u.epoch) (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 3436#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out) (hx20_2 : s2.readReg64 .x20 = u48)
    (hx21_2 : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_2 : s2.readReg64 .x22 = d_w0) (hx24_2 : s2.readReg64 .x24 = u56)
    (hx25_2 : s2.readReg64 .x25 = u64) (hx26_2 : s2.readReg64 .x26 = u32)
    (hx27_2 : s2.readReg64 .x27 = pbA)
    (hx28_2 : s2.readReg64 .x28 = u80) (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ w184) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 736 ∗ v2hs_stack896ScratchRest (s0.sp - 2400#64) ∗
        v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u32 u40 auth.rootKey ∗
        vecU8Payload A.repAlloc u56 u64 auth.macKey ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s2)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSent3436Env s auth evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v2hstop_headerSent_3436_to_ret_qpan_placed
    (Qpan := fun s0 R sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))
    hA s hsome_enc_9036 hpts hdec_ok st u auth hfits huc hdk_len hauth s0 s2 out pbA R
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w184 w0 w8 w16 w24 w32 w40 w48
    d_w0 d_w8 d_w16 d_w24 d_w32 hu8_lt hu24_val hu48_eq hu72_eq hu80_eq hr_lt63
    hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2

set_option maxHeartbeats 800000 in
theorem v2hstop_headerSent_3348_to_ret_qpan_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Qpan : State → SepProp → (State → SepProp → Prop)}
    (hA : FromPbAllocHooksBudget M A lim ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036HypPlacedQpan M A lim F ext s Qpan)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true)
    (st : M.σ) (hfits : FitsEnv M lim st (HeaderSent3348Env s))
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = d_w0) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A.repAlloc s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSent3348Env s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (Qpan s0 R) := by
  let fsp := s0.sp - 2400#64
  have hpb_col := v2hstop_pbEncTailAt_entails_full_224 pbA w8 w16 w24 w32 w40 w48
  cases huc : s.uc with
  | none =>
    rw [v2hs_from_pb_headerSent_uc_none_eq F s hdec_ok huc]
    dsimp only [v2hs_optProtoUcHeap]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
      (⌜u8 = noneCap⌝ ∗
       (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        (stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1))) by
      dsimp only [fsp]; sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (show _ =
        ⌜u8 = noneCap⌝ ∗
        (v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         (stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) ∗ A.pool lim st s1)) by
        sep_ac_rfl)))) ?_
    refine SepWPp.pure_elim fun hu8 => ?_
    subst hu8
    apply SepWPp.of_sepWP_ret
    let RestUcNone : SepProp :=
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 333 + 4392#64)
      (P_mid := fun s2 => v2hs_ucWordsAt (fsp + 896#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        RestUcNone ∗ A.pool lim st s2)
      (Q := fun s2 => VmPreserved s1 s2 ∧ s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧ TraceCalleeSaved s2 s0)
      (SepWP.weaken_pre (Entails.of_eq (by dsimp only [RestUcNone, fsp]; sep_ac_rfl))
        (v2hs_uc_none_3348_to_4392_placed_budget A lim st (ext := ext) s0 s1 out d_w0
          u16 u24 u32 u40 u48 u56 u64 u72 u80 RestUcNone
          hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1)) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx19_2, hx22_2, htr2⟩
    have h976 := v2hs_memRegion_896_ucWords_to_976 fsp noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80
    have hret := v2hs_epilogue_4392_ret_placed (F := F) hA st s0 s2 out
      (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
      (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        (memRegion fsp 896 ∗ v2hs_ucWordsAt (fsp + 896#64) noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80) ∗
        (stackAt fsp encoderFromPbStack ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim st s2 ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by
        dsimp only [RestUcNone]; sep_ac_rfl))
       (Entails.trans (sepConj_mono_left h976) (Entails.of_eq (by dsimp only [fsp]; try sep_ac_rfl))))
      (SepWP.mono hret fun sf Pf _ _ ⟨evs, hfree, hPf, hspf, hcsf, htrf⟩ => ?_)
    have hevs_env : HeaderSent3348Env s evs := by
      unfold HeaderSent3348Env; rw [huc]; exact hfree
    exact ⟨⟨evs, hevs_env, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hspf, hcsf, htrf⟩
  | some u =>
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono (v2hs_memRegion_896_split_scratch fsp)
        (sepConj_mono_right (sepConj_mono_left
          (v2hstop_optProtoUcHeap_some_extract A.repAlloc u u8 u16 u24 u32 u40 u48 u56 u64 u72 u80))))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWPp.exists_elim; intro w232; apply SepWPp.exists_elim; intro w224
    apply SepWPp.exists_elim; intro w216; apply SepWPp.exists_elim; intro w200
    apply SepWPp.exists_elim; intro w184; apply SepWPp.exists_elim; intro w176
    apply SepWPp.exists_elim; intro w152; apply SepWPp.exists_elim; intro w96
    refine SepWPp.pure_elim fun ⟨hu8_lt, hu24_eq, hdk_lt63, hu80_eq⟩ => ?_
    by_cases hdk : (u24 == 2400#64) = true
    · have hu24_val : u24 = 2400#64 := beq_iff_eq.mp hdk
      have hdk_len : u.dk.length = 2400 := by
        have h1 : (BitVec.ofNat 64 u.dk.length).toNat = (2400#64 : BitVec 64).toNat := by
          rw [← hu24_eq, hu24_val]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; exact h1
      have hdk_beq : (BitVec.ofNat 64 u.dk.length == 2400#64) = true := by
        rw [hdk_len]; decide
      cases hauth : u.auth with
      | none =>
        rw [v2hs_from_pb_headerSent_auth_none_eq F s u hdec_ok huc hdk_len hauth]
        dsimp only [v1_optProtoAuthHeap]
        refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
          v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
          (⌜u32 = noneCap⌝ ∗
           (stackAt fsp encoderFromPbStack ∗
            ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
            ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
            ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
            memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
            v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
            v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
            v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
            v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
            v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
            memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
            A.pool lim st s1 ∗ statesFromPbJumpTablePlacedAt)) by dsimp only [fsp]; sep_ac_rfl))
          (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (show _ =
            ⌜u32 = noneCap⌝ ∗
            (stackAt fsp encoderFromPbStack ∗
             ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
             ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
             ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
             memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
             v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
             v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
             v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
             v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
             v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
             v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
             memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             A.pool lim st s1 ∗ (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by sep_ac_rfl)))) ?_
        refine SepWPp.pure_elim fun hu32 => ?_
        subst hu32
        apply SepWPp.of_sepWP_ret
        have hret := v2hstop_branch_auth_none_3348_placed (F := F) hA st s0 s1 out u.dk
          u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 w176 w184 w200 w216 w224 w232
          (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
          (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
          hcl1 hsp0_align hu8_lt hdk hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
        refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [fsp]; try sep_ac_rfl))
          (SepWP.mono hret fun sf Pf _ _ ⟨evs, hfree, hPf, hspf, hcsf, htrf⟩ => ?_)
        have hevs_env : HeaderSent3348Env s evs := by
          simp only [HeaderSent3348Env, huc, hdk_beq, ↓reduceIte, hauth]; exact hfree
        exact ⟨⟨evs, hevs_env, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hspf, hcsf, htrf⟩
      | some auth =>
        refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
          v1_optProtoAuthHeap A.repAlloc (some auth) u32 u40 u48 u56 u64 u72 ∗
          (stackAt fsp encoderFromPbStack ∗
           ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
           ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
           ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
           memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
           v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
           v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
           v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
           memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
           A.pool lim st s1) by dsimp only [fsp]; sep_ac_rfl))
          (sepConj_mono_left (v2hstop_optProtoAuthHeap_some_extract A.repAlloc auth u32 u40 u48 u56 u64 u72))) ?_
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hu32_lt, hu48_eq, hu72_eq, hr_lt63⟩ => ?_
        let RestOk : SepProp :=
          stackAt fsp encoderFromPbStack ∗ ((fsp + 184#64) ↦₆₄ w184) ∗ v2hs_stack896ScratchRest fsp ∗
          v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗ vecU8Payload A.repAlloc u32 u40 auth.rootKey ∗
          vecU8Payload A.repAlloc u56 u64 auth.macKey ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt
        refine SepWPp.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
          ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 656 ∗
          v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
          RestOk ∗ A.pool lim st s1 by dsimp only [RestOk, fsp]; sep_ac_rfl)) ?_
        refine sepWPp_seq_clean_lscl_st hcl1
          (v2hs_validate_ok_3348_3436_placed_budget A lim st (ext := ext) s0 s1 out d_w0
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
            w96 w152 w176 w200 w216 w224 w232 RestOk hsp0_align hu8_lt hdk hu32_lt
            hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1) ?_
        intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, _, _, _, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
        have hx21_2' : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by rw [hx21_2, hx21_1]
        have hx27_2' : s2.readReg64 .x27 = pbA := by rw [hx27_2, hx27_1]
        have hfits3436 := fitsEnv_3436_of_3348 huc hdk_len hauth hfits
        have h3436 := v2hstop_headerSent_3436_to_ret_qpan_placed hA s hsome_enc_9036 hpts hdec_ok
          st u auth hfits3436 huc hdk_len hauth
          s0 s2 out pbA R u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w184
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
          hu8_lt hu24_val hu48_eq hu72_eq hu80_eq hr_lt63
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2' hx22_2 hx24_2 hx25_2 hx26_2 hx27_2' hx28_2 htr2
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [RestOk, fsp]; sep_ac_rfl))
          (sepWPp_mono_post h3436 fun sf Pf ⟨⟨evs, hevs, hPf⟩, hspf, hcsf, htrf⟩ => ?_)
        have hevs_env : HeaderSent3348Env s evs := by
          simp only [HeaderSent3348Env, huc, hdk_beq, ↓reduceIte, hauth]; exact hevs
        exact ⟨⟨evs, hevs_env, hPf⟩, hspf, hcsf, htrf⟩
    · have hdk_f : (u24 == 2400#64) = false := Bool.eq_false_iff.mpr hdk
      have hdk_eq_f : (BitVec.ofNat 64 u.dk.length == 2400#64) = false := by
        rw [← hu24_eq]; exact hdk_f
      rw [v2hs_from_pb_headerSent_bad_dk_eq F s u hdec_ok huc hdk_eq_f]
      apply SepWPp.of_sepWP_ret
      have hret := v2hstop_branch_bad_dk_3348_placed (F := F) hA st s0 s1 out u
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 w176 w184 w200 w216 w224 w232
        (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hcl1 hsp0_align hu8_lt hdk_f hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 96#64) ↦₆₄ w96) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
         ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
         ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
         memRegion (fsp + 240#64) 656 ∗ v2hs_stack896ScratchRest fsp ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         v4b_vecU8Heap A.repAlloc u.dk u8 u16 u24 ∗
         v1_optProtoAuthHeap A.repAlloc u.auth u32 u40 u48 u56 u64 u72 ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim st s1 ∗ statesFromPbJumpTablePlacedAt) by dsimp only [fsp]; sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl))))
        (SepWP.mono hret fun sf Pf _ _ ⟨evs, hfree, hPf, hspf, hcsf, htrf⟩ => ?_)
      have hevs_env : HeaderSent3348Env s evs := by
        simp only [HeaderSent3348Env, huc, hdk_eq_f, Bool.false_eq_true, ↓reduceIte]
        exact hfree
      exact ⟨⟨evs, hevs_env, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hspf, hcsf, htrf⟩

theorem v2hstop_headerSent_3348_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036HypPlaced M A lim F ext s)
    (hpts : optEncoderPtsBound s.sendingEk)
    (hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true)
    (st : M.σ) (hfits : FitsEnv M lim st (HeaderSent3348Env s))
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22_1 : s1.readReg64 .x22 = d_w0) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A.repAlloc s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSent3348Env s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v2hstop_headerSent_3348_to_ret_qpan_placed
    (Qpan := fun s0 R sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))
    hA s hsome_enc_9036 hpts hdec_ok st hfits s0 s1 out pbA R
    u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w0 w8 w16 w24 w32 w40 w48
    d_w0 d_w8 d_w16 d_w24 d_w32
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx27_1 htr1

set_option maxHeartbeats 800000 in
theorem states_from_pb_headerSent_508_of_some_enc_qpan_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Qpan : State → SepProp → (State → SepProp → Prop)}
    (hA : FromPbAllocHooksBudget M A lim ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036HypPlacedQpan M A lim F ext s Qpan)
    (hpts : optEncoderPtsBound s.sendingEk)
    (st : M.σ) (hfits : FitsEnv M lim st (HeaderSentFromPbEnv s))
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSentFromPbEnv s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (Qpan s0 R) := by
  let fsp := s0.sp - 2400#64
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (v2hstop_optProtoInnerStateAt_headerSent_unpack A.repAlloc pbA s)))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro u8; apply SepWPp.exists_elim; intro u16
  apply SepWPp.exists_elim; intro u24; apply SepWPp.exists_elim; intro u32
  apply SepWPp.exists_elim; intro u40; apply SepWPp.exists_elim; intro u48
  apply SepWPp.exists_elim; intro u56; apply SepWPp.exists_elim; intro u64
  apply SepWPp.exists_elim; intro u72; apply SepWPp.exists_elim; intro u80
  apply SepWPp.exists_elim; intro w0; apply SepWPp.exists_elim; intro w8
  apply SepWPp.exists_elim; intro w16; apply SepWPp.exists_elim; intro w24
  apply SepWPp.exists_elim; intro w32; apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48
  apply SepWPp.exists_elim; intro d_w0; apply SepWPp.exists_elim; intro d_w8
  apply SepWPp.exists_elim; intro d_w16; apply SepWPp.exists_elim; intro d_w24
  apply SepWPp.exists_elim; intro d_w32
  let Rest508 : SepProp :=
    (pbA ↦₆₄ 0x8000000000000002#64) ∗ memRegion (pbA + 184#64) 40 ∗
    stackAt fsp encoderFromPbStack ∗
    v2hs_optProtoUcHeap A.repAlloc s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
    v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
    v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    statesFromPbJumpTablePlacedAt
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    memRegion fsp 2304 ∗
    v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
    Rest508 ∗ A.pool lim st s1 by dsimp only [Rest508, fsp]; sep_ac_rfl)) ?_
  refine sepWPp_seq_clean_lscl_st hcl1
    (v2hs_copy_pb_to_stack_508_placed_budget A lim st (ext := ext)
      s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 Rest508
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx19_2, hx21_2, hx27_2, hx22_2, htr2⟩
  have hx21_2' : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by rw [hx21_2, hx21_1]
  have hpb_tail := v2hstop_pb128_entails_pbEncTailAt pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
  have hpb_col := v2hstop_pbEncTailAt_entails_full_224 pbA w8 w16 w24 w32 w40 w48
  have hcol_pb :
      (memRegion fsp 896 ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (fsp + 1072#64) 1232 ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        Rest508 ∗ A.pool lim st s2) ⊢
      v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      (v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       (stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
        v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v2hs_optProtoUcHeap A.repAlloc s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s2)) := by
    dsimp only [Rest508]
    refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x8000000000000002#64) ∗
       v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
         w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       memRegion (pbA + 184#64) 40) ∗
      (v2hs_optProtoDecoderHeap A.repAlloc (s.receivingCt1.map pbToProtoPolyDecoder) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
       stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
       v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
       v2hs_optProtoUcHeap A.repAlloc s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
       v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb_tail) (Entails.of_eq (by sep_ac_rfl))
  refine SepWPp.weaken_pre hcol_pb ?_
  cases hdec : s.receivingCt1 with
  | none =>
    have hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true := by
      rw [hdec]; trivial
    rw [show (none : Option PolynomialDecoder).map pbToProtoPolyDecoder = none from rfl]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v2hstop_optProtoDecoderHeap_none_extract A.repAlloc d_w0 d_w8 d_w16 d_w24 d_w32)) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun hd_w0 => ?_
    have hd_w0_beq : (d_w0 + 1#64 == 0#64) = true := by rw [hd_w0]; decide
    simp only [hd_w0_beq, ↓reduceIte] at hpc2
    have hfits3348 := fitsEnv_3348_of_fromPb_none hdec hfits
    have h3348 := v2hstop_headerSent_3348_to_ret_qpan_placed hA s hsome_enc_9036 hpts hdec_ok
      st hfits3348 s0 s2 out pbA R u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
      hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2' hx22_2 hx27_2 htr2
    refine SepWPp.weaken_pre (Entails.of_eq (by
      dsimp only [fsp]; rw [hdec, show (none : Option PolynomialDecoder).map pbToProtoPolyDecoder = none from rfl]
      sep_ac_rfl))
      (sepWPp_mono_post h3348 fun sf Pf ⟨⟨evs, hevs, hPf⟩, hspf, hcsf, htrf⟩ => ?_)
    have hevs_env : HeaderSentFromPbEnv s evs := by
      unfold HeaderSentFromPbEnv; rw [hdec]; exact hevs
    exact ⟨⟨evs, hevs_env, hPf⟩, hspf, hcsf, htrf⟩
  | some d =>
    rw [show (some d : Option PolynomialDecoder).map pbToProtoPolyDecoder = some (pbToProtoPolyDecoder d) from rfl]
    refine SepWPp.weaken_pre
      (sepConj_mono_left (v2hstop_optProtoDecoderHeap_some_extract A.repAlloc d d_w0 d_w8 d_w16 d_w24 d_w32)) ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hd_cap, hd_pts⟩ => ?_
    have hd_w0_beq : (d_w0 + 1#64 == 0#64) = false :=
      Bool.eq_false_iff.mpr (v4_ptsCap_add_one_ne_zero hd_cap)
    simp only [hd_w0_beq, Bool.false_eq_true, ↓reduceIte] at hpc2
    let Rest592 : SepProp :=
      v2hs_optProtoDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
      v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      v2hs_optProtoUcHeap A.repAlloc s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
      v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTablePlacedAt
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
      Rest592 ∗ A.pool lim st s2 by dsimp only [Rest592, fsp]; sep_ac_rfl)) ?_
    refine sepWPp_seq_clean_lscl_st hcl2
      (v2hs_check_ptsNeeded_592_placed_budget A lim st (ext := ext)
        s0 s2 out d_w0 d_w8 d_w16 d_w24 d_w32 Rest592
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htr2) ?_
    intro s3 hpc3 hrun3 hcl3 ⟨_hvm3, hsp3, hx19_3, hx21_3, hx22_3, hx27_3, htr3⟩
    have hx21_3' : s3.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by rw [hx21_3, hx21_2']
    have hx27_3' : s3.readReg64 .x27 = pbA := by rw [hx27_3, hx27_2]
    by_cases hpts_dec : (d.ptsNeeded == 480#32) = true
    · have hpts_dw24 : (d_w24.extractLsb' 0 32 == 480#32) = true := by rw [hd_pts]; exact hpts_dec
      simp only [hpts_dw24, ↓reduceIte] at hpc3
      have hdec_ok : match s.receivingCt1 with | none => True | some d => (d.ptsNeeded == 480#32) = true := by
        rw [hdec]; exact hpts_dec
      have hfits3348 := fitsEnv_3348_of_fromPb_some hdec hpts_dec hfits
      have h3348 := v2hstop_headerSent_3348_to_ret_qpan_placed hA s hsome_enc_9036 hpts hdec_ok
        st hfits3348 s0 s3 out pbA R u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32
        hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx21_3' hx22_3 hx27_3' htr3
      refine SepWPp.weaken_pre (Entails.of_eq (by
        dsimp only [Rest592, fsp]
        rw [hdec, show (some d : Option PolynomialDecoder).map pbToProtoPolyDecoder = some (pbToProtoPolyDecoder d) from rfl]
        sep_ac_rfl))
        (sepWPp_mono_post h3348 fun sf Pf ⟨⟨evs, hevs, hPf⟩, hspf, hcsf, htrf⟩ => ?_)
      have hevs_env : HeaderSentFromPbEnv s evs := by
        simp only [HeaderSentFromPbEnv, hdec, hpts_dec, ↓reduceIte]; exact hevs
      exact ⟨⟨evs, hevs_env, hPf⟩, hspf, hcsf, htrf⟩
    · have hpts_f : (d.ptsNeeded == 480#32) = false := Bool.eq_false_iff.mpr hpts_dec
      have hpts_dw24 : (d_w24.extractLsb' 0 32 == 480#32) = false := by rw [hd_pts]; exact hpts_f
      simp only [hpts_dw24, Bool.false_eq_true, ↓reduceIte] at hpc3
      rw [v2hs_from_pb_headerSent_bad_pts_eq F s d hdec hpts_f]
      apply SepWPp.of_sepWP_ret
      have hret := v2hs_err_uc_604_to_ret_placed (F := F) hA st s0 s3 out s.uc
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
        (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 htr3
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v2hstop_pbEncTailAt pbA w8 w16 w24 w32 w40 w48 ∗
        (v2hs_optProtoDecoderWordsAt (fsp + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         v2hs_optProtoDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder d)) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
         stackAt fsp encoderFromPbStack ∗ memRegion fsp 896 ∗
         v2hs_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         v2hs_optProtoUcHeap A.repAlloc s.uc u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
         v1_optProtoPolyEncoderWordsAt (fsp + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc (s.sendingEk.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTablePlacedAt ∗ A.pool lim st s3) by dsimp only [Rest592, fsp]; sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl))))
        (SepWP.mono hret fun sf Pf _ _ ⟨evs, hfree, hPf, hspf, hcsf, htrf⟩ => ?_)
      have hevs_env : HeaderSentFromPbEnv s evs := by
        simp only [HeaderSentFromPbEnv, hdec, hpts_f, Bool.false_eq_true, ↓reduceIte]
        exact hfree
      exact ⟨⟨evs, hevs_env, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hspf, hcsf, htrf⟩

theorem states_from_pb_headerSent_508_of_some_enc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (s : V1State.Chunked.HeaderSent)
    (hsome_enc_9036 : v2hstop_SomeEnc9036HypPlaced M A lim F ext s)
    (hpts : optEncoderPtsBound s.sendingEk)
    (st : M.σ) (hfits : FitsEnv M lim st (HeaderSentFromPbEnv s))
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSentFromPbEnv s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  states_from_pb_headerSent_508_of_some_enc_qpan_placed
    (Qpan := fun s0 R sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))
    hA s hsome_enc_9036 hpts st hfits s0 s1 out pbA R
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx27_1 htr1

/-- `Qpan`-polymorphic unconditional post-dispatch step for `InnerState.headerSent s` at `+508#64`. -/
theorem states_from_pb_headerSent_508_qpan_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Qpan : State → SepProp → (State → SepProp → Prop)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent)
    (hpts : optEncoderPtsBound s.sendingEk)
    (st : M.σ) (hfits : FitsEnv M lim st (HeaderSentFromPbEnv s))
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSentFromPbEnv s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (Qpan s0 R) :=
  states_from_pb_headerSent_508_of_some_enc_qpan_placed hA s
    (v2hstop_someEnc9036HypPlacedQpan_of_sepWP
      (v2hstop_some_enc_9036_to_ret_sepWP_placed hA henc hdec s))
    hpts st hfits s0 s1 out pbA R hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx27_1 htr1

theorem states_from_pb_headerSent_508_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent)
    (hpts : optEncoderPtsBound s.sendingEk)
    (st : M.σ) (hfits : FitsEnv M lim st (HeaderSentFromPbEnv s))
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSentFromPbEnv s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  states_from_pb_headerSent_508_qpan_placed
    (Qpan := fun s0 R sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))
    hA henc hdec s hpts st hfits s0 s1 out pbA R
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx27_1 htr1

theorem states_from_pb_headerSent_508_noPanic_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent)
    (hpts : optEncoderPtsBound s.sendingEk)
    (st : M.σ) (hfits : FitsEnv M lim st (HeaderSentFromPbEnv s))
    (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (∃ evs : List AllocEvent, HeaderSentFromPbEnv s evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)) :=
  states_from_pb_headerSent_508_qpan_placed
    (Qpan := fun _s0 R sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))
    hA henc hdec s hpts st hfits s0 s1 out pbA R
    hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx23_1 hx27_1 htr1

/-! ## Top-Level `subroutine_ok` Contracts (`lsmpl.base 333`) -/

private theorem headerSent_ok_of_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {s : V1State.Chunked.HeaderSent} {Env : List AllocEvent → Prop}
    (hbody : ∀ (st : M.σ) (s0 s2 : State) (out pbA : BitVec 64) (R : SepProp),
      optEncoderPtsBound s.sendingEk →
      FitsEnv M lim st Env →
      LibsignalCodeLoaded lsmpl s2.mem →
      (s0.sp &&& 15#64 == 0#64) = true →
      s2.pc = lsmpl.base 333 + 508#64 →
      s2.status = .Running → s2.sp = s0.sp - 2400#64 →
      s2.readReg64 .x19 = out → s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 →
      s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 → s2.readReg64 .x27 = pbA →
      TraceCalleeSaved s2 s0 →
      SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2)
        (fun sf Pf =>
          (∃ evs : List AllocEvent, Env evs ∧
            (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
                (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.headerSent s) }) ∗
              memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt s0.sp statesFromPbStack)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R))) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.headerSent s) } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [statesFromPbVariantPlacedSpecOfEnv, v1StatePtsBound] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine sepWPp_seq_clean_lscl_st hcl0 hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1, _⟩
  have ⟨Tail, htag_eq⟩ : ∃ Tail : SepProp,
      optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) =
      (pbA ↦₆₄ 0x8000000000000002#64) ∗ Tail := ⟨_, rfl⟩
  have hP1' :
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
      memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
      statesFromPbSavedCells s0 ∗ A.pool lim st s1 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
       statesFromPbJumpTablePlacedAt) ⊢
      (pbA ↦₆₄ 0x8000000000000002#64) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail) ∗
      A.pool lim st s1 := by
    rw [htag_eq]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA 0x8000000000000002#64 508#64
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     Tail)
    TaggedVariantDispatch.headerSent hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine sepWPp_seq_clean_lscl_st hcl1 hdisp ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, _, hx21_2, _, hx23_2, htr2, _⟩
  have hx21_2' : s2.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64 := by
    rw [hx21_2]; bv_omega
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hpre_join :
      (pbA ↦₆₄ 0x8000000000000002#64) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail) ∗
      A.pool lim st s2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some (.headerSent s)) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    rw [htag_eq]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ 0x8000000000000002#64) ∗ Tail) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  exact SepWPp.weaken_pre hpre_join
    (sfpProof_sepWPp_of_states_body_cl_placed_of_env st s0 s2 out pbA
      { innerState := some (.headerSent s) } Env _ R
      (hbody st s0 s2 out pbA R hpts hfits hcl2 hsp0_align hpc2 hrun2 hsp2
        hx19_2 hx21_2' hx23_2' hx27_2 htr2))

/-- Exact-envelope (`HeaderSentFromPbEnv s`) Variant 2 (`InnerState.headerSent`, `+508`) contract
    for `<States>::from_pb`. -/
theorem states_from_pb_headerSent_ok_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.headerSent s) }
          (HeaderSentFromPbEnv s))) :=
  headerSent_ok_of_body_placed fun st s0 s2 out pbA R hpts hfits hcl2
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx23_2 hx27_2 htr2 =>
    states_from_pb_headerSent_508_noPanic_placed hA henc hdec s hpts st hfits
      s0 s2 out pbA R hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx23_2 hx27_2 htr2

/-- Budget-threaded Variant 2 (`InnerState.headerSent`, `+508`) contract for `<States>::from_pb`
    under the default linear envelope `StatesFromPbEnv`. -/
theorem states_from_pb_headerSent_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.headerSent s) })) :=
  headerSent_ok_of_body_placed fun st s0 s2 out pbA R hpts hfits hcl2
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx23_2 hx27_2 htr2 =>
    sepWPp_mono_post
      (states_from_pb_headerSent_508_noPanic_placed hA henc hdec s hpts st
        (fitsEnv_headerSentFromPbEnv_of_statesFromPbEnv s hfits)
        s0 s2 out pbA R hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx23_2 hx27_2 htr2)
      fun _sf _Pf ⟨⟨evs, hevs, hPf⟩, hrest⟩ =>
        ⟨⟨evs, headerSentFromPbEnv_sub_statesFromPbEnv s hfits hevs, hPf⟩, hrest⟩

theorem states_from_pb_headerSent_ok_of_env_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some (.headerSent s) }
          (HeaderSentFromPbEnv s))) :=
  states_from_pb_headerSent_ok_of_env_placed hA (encoder_from_pb_ok_of_alloc_placed hA) hdec s

theorem states_from_pb_headerSent_ok_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (s : V1State.Chunked.HeaderSent) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F { innerState := some (.headerSent s) })) :=
  states_from_pb_headerSent_ok_ext_placed hA (encoder_from_pb_ok_of_alloc_placed hA) hdec s

abbrev states_from_pb_variant1_placed := @states_from_pb_headerSent_ok_ext_placed
abbrev states_from_pb_variant1_of_alloc_placed := @states_from_pb_headerSent_ok_of_alloc_placed

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsPlacedBudget
