/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2ePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 1 (`KeysSampled`) Envelopes and `+4016` Continuation

Allocator event envelopes, `StatesFromPbEnv` subsumption, and post-`auth` composition
(`+4016 -> ret`) for `InnerState.keysSampled` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudgetAux

open scoped CryptoVerification.RustHeap
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_333 blkPl_333 lsProg_333 lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (PolyEncoder PolynomialEncoder ProtoAuthenticator ProtoPolynomialEncoder States V1State
   pbToProtoPolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderAt polyEncoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize
   resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved collapse_step collapse_step0 collapse_top optEncoderPtsBound
   resultChunkedStatesAt sp_sub_2400_align split_step split_top statesFromPbJumpTablePlacedAt
   statesFromPbSavedCells statesFromPbStack v1_bs384_eq_encCells v1_bv_add_add_lit
   v1_bv_sub_sub_lit v1_encCellsAt v1_from_pb_sendingHdr_none v1_from_pb_sendingHdr_some
   v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderHeap_extract_w0
   v1_optProtoPolyEncoderWordsAt v1_optProtoPolyEncoderWordsAt_entails_56
   v1_polyEncoderAt_relocate)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth rawUcHeaderSent
   rawUcHeaderSent_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload vecU8Payload_entails_dealloc)
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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (spqrBoundedEvs_authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget seq_clean_lscl_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2cPlacedBudget
  (v1_cleanup_enc_err_4116_placed v1_cleanup_sendingHdr_none_5860_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
  (v1_sendingHdr_none_4016_5860_placed_budget v1_sendingHdr_some_copy_4016_4096_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2ePlacedBudget
  (v1_encoder_call_4096_to_4100_placed_sepWP v1_encoder_err_4100_4116_placed_budget
   v1_encoder_ok_4100_6568_placed_budget v1_keysSampled_6568_ret_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v1_bv_add_add_lit v1_bv_sub_sub_lit

/-! ## Allocation Envelopes & `StatesFromPbEnv` Subsumption for `KeysSampled` -/

/-- Extract `uc.auth` iff `uc.dk.length` (`2400`) and `uc.ek.length` (`1152`) pass the `+1196`
    header-validation checks in Variant 1 (`InnerState.keysSampled`). -/
def keysSampledValidAuth? (uc : V1State.Unchunked.HeaderSent) : Option ProtoAuthenticator :=
  if (BitVec.ofNat 64 uc.dk.length == 2400#64) && (BitVec.ofNat 64 uc.ek.length == 1152#64) then
    uc.auth
  else
    none

theorem keysSampledValidAuth?_eq_none_of_err {uc : V1State.Unchunked.HeaderSent}
    (herr :
      ((BitVec.ofNat 64 uc.dk.length != 2400#64) ||
       (BitVec.ofNat 64 uc.ek.length != 1152#64)) = true ∨
      uc.auth = none) :
    keysSampledValidAuth? uc = none := by
  unfold keysSampledValidAuth?
  rcases herr with hlen | hnone
  · rw [Bool.or_eq_true, bne_iff_ne, bne_iff_ne] at hlen
    rcases hlen with hdk | hek
    · rw [beq_eq_false_iff_ne.mpr hdk]; rfl
    · rw [beq_eq_false_iff_ne.mpr hek, Bool.and_false]; rfl
  · rw [hnone]; split <;> rfl

theorem keysSampledValidAuth?_eq_some {uc : V1State.Unchunked.HeaderSent}
    {auth : ProtoAuthenticator}
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hauth : uc.auth = some auth) :
    keysSampledValidAuth? uc = some auth := by
  unfold keysSampledValidAuth?
  rw [hdk, hek, hauth]
  rfl

/-- Tail budget precondition required at `+4016` after `auth` cloning and input `auth` drop. -/
def KeysSampledTailFits (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (optEnc : Option PolynomialEncoder) : Prop :=
  match optEnc with
  | none => True
  | some pbEnc => FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc))

/-- Tail postcondition event envelope emitted from `+4016` to `s0.x30`. -/
def KeysSampledTailEnv (optEnc : Option PolynomialEncoder) (evs : List AllocEvent) : Prop :=
  match optEnc with
  | none => FreeOnlyEvs evs
  | some pbEnc => EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs

/-- Precondition allocation envelope of Variant 1 (`InnerState.keysSampled`, `+1104`).
    Admits `[]` when `s` performs zero allocations (passing `zeroBudgetLimits`), while covering
    both `auth` cloning and non-empty `<PolyEncoder>::from_pb` allocations after dropping the
    input `ProtoAuthenticator` buffers. -/
def KeysSampledFromPbAllocEnv (s : V1State.Chunked.KeysSampled) (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => evs = []
  | some uc =>
    match keysSampledValidAuth? uc with
    | none => evs = []
    | some auth =>
      match s.sendingHdr with
      | none => AuthFromPbEnv auth evs
      | some pbEnc =>
        AuthFromPbEnv auth evs ∨
        ∃ evs_af evs_enc,
          FreeOnlyEvs evs_af ∧
          EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
          evs_enc ≠ [] ∧
          evs = authFromPbEvents auth ++ evs_af ++ evs_enc

/-- Full postcondition event envelope of Variant 1 (`InnerState.keysSampled`, `+1104`). -/
def KeysSampledFromPbEnv (s : V1State.Chunked.KeysSampled) (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => FreeOnlyEvs evs
  | some uc =>
    match keysSampledValidAuth? uc with
    | none => FreeOnlyEvs evs
    | some auth =>
      match s.sendingHdr with
      | none =>
        ∃ evs_free, FreeOnlyEvs evs_free ∧ evs = authFromPbEvents auth ++ evs_free
      | some pbEnc =>
        ∃ evs_af evs_enc,
          FreeOnlyEvs evs_af ∧
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
          evs = authFromPbEvents auth ++ evs_af ++ evs_enc

private theorem freeOnlyEvs_append {l₁ l₂ : List AllocEvent}
    (h1 : FreeOnlyEvs l₁) (h2 : FreeOnlyEvs l₂) : FreeOnlyEvs (l₁ ++ l₂) :=
  fun ev hev => (List.mem_append.mp hev).elim (h1 ev) (h2 ev)

theorem encoderFromPbEnv_append_freeOnly {pb : ProtoPolynomialEncoder}
    {evs₁ evs₂ : List AllocEvent}
    (h1 : EncoderFromPbEnv pb evs₁) (h2 : FreeOnlyEvs evs₂) :
    EncoderFromPbEnv pb (evs₁ ++ evs₂) := by
  rcases h1 with ⟨evs_a, evs_f, rfl, ha, hf⟩
  exact ⟨evs_a, evs_f ++ evs₂, List.append_assoc evs_a evs_f evs₂, ha, freeOnlyEvs_append hf h2⟩

theorem keysSampledAllocEnv_imp_keysSampledEnv {s : V1State.Chunked.KeysSampled}
    {evs : List AllocEvent} (h : KeysSampledFromPbAllocEnv s evs) :
    KeysSampledFromPbEnv s evs := by
  cases s with | mk optUc optEnc =>
  cases optUc with
  | none =>
    dsimp only [KeysSampledFromPbAllocEnv, KeysSampledFromPbEnv] at h ⊢
    subst h
    exact FreeOnlyEvs.nil
  | some uc =>
    dsimp only [KeysSampledFromPbAllocEnv, KeysSampledFromPbEnv] at h ⊢
    cases hval : keysSampledValidAuth? uc with
    | none =>
      rw [hval] at h
      subst h
      exact FreeOnlyEvs.nil
    | some auth =>
      rw [hval] at h
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

theorem fitsEnv_alloc_of_keysSampledEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.KeysSampled} (h : FitsEnv M lim st (KeysSampledFromPbEnv s)) :
    FitsEnv M lim st (KeysSampledFromPbAllocEnv s) :=
  FitsEnv.mono (fun _ => keysSampledAllocEnv_imp_keysSampledEnv) h

theorem fitsEvents_auth_of_keysSampledAllocEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {uc : V1State.Unchunked.HeaderSent} {auth : ProtoAuthenticator}
    {optEnc : Option PolynomialEncoder}
    (hval : keysSampledValidAuth? uc = some auth)
    (hfits : FitsEnv M lim st (KeysSampledFromPbAllocEnv { uc := some uc, sendingHdr := optEnc })) :
    FitsEvents M lim st (authFromPbEvents auth) := by
  apply hfits (authFromPbEvents auth)
  dsimp only [KeysSampledFromPbAllocEnv]
  rw [hval]
  cases optEnc with
  | none => rfl
  | some _ => exact Or.inl rfl

theorem keysSampledTailFits_of_keysSampledAllocEnv {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {uc : V1State.Unchunked.HeaderSent} {auth : ProtoAuthenticator}
    {optEnc : Option PolynomialEncoder} {evs_af : List AllocEvent}
    (hval : keysSampledValidAuth? uc = some auth)
    (hfits : FitsEnv M lim st (KeysSampledFromPbAllocEnv { uc := some uc, sendingHdr := optEnc }))
    (hfree_af : FreeOnlyEvs evs_af) :
    KeysSampledTailFits M lim
      (M.stepEvents evs_af (M.stepEvents (authFromPbEvents auth) st)) optEnc := by
  cases optEnc with
  | none => trivial
  | some pbEnc =>
    dsimp only [KeysSampledTailFits, FitsEnv]
    intro evs_enc henc
    by_cases hne : evs_enc = []
    · subst hne; simp [FitsEvents]
    · have hev : KeysSampledFromPbAllocEnv { uc := some uc, sendingHdr := some pbEnc }
          (authFromPbEvents auth ++ evs_af ++ evs_enc) := by
        dsimp only [KeysSampledFromPbAllocEnv]
        rw [hval]
        exact Or.inr ⟨evs_af, evs_enc, hfree_af, henc, hne, rfl⟩
      have hf := (fitsEvents_append M lim (authFromPbEvents auth ++ evs_af) evs_enc st).mp
        (hfits _ hev)
      rw [M.stepEvents_append] at hf
      exact hf.2

theorem keysSampledEnv_of_tail {uc : V1State.Unchunked.HeaderSent} {auth : ProtoAuthenticator}
    {optEnc : Option PolynomialEncoder} {evs_af evs_tail : List AllocEvent}
    (hval : keysSampledValidAuth? uc = some auth)
    (hfree_af : FreeOnlyEvs evs_af)
    (htail : KeysSampledTailEnv optEnc evs_tail) :
    KeysSampledFromPbEnv { uc := some uc, sendingHdr := optEnc }
      (authFromPbEvents auth ++ evs_af ++ evs_tail) := by
  dsimp only [KeysSampledFromPbEnv]
  rw [hval]
  cases optEnc with
  | none =>
    exact ⟨evs_af ++ evs_tail, freeOnlyEvs_append hfree_af htail,
      List.append_assoc (authFromPbEvents auth) evs_af evs_tail⟩
  | some pbEnc =>
    exact ⟨evs_af, evs_tail, hfree_af, htail, rfl⟩

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

private theorem rawAuth_le_keysSampled_encodeRaw
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (optEnc : Option PolynomialEncoder) (hauth : uc.auth = some auth) :
    auth.rootKey.length + auth.macKey.length ≤
      (V1State.encodeRaw
        { innerState := some (.keysSampled { uc := some uc, sendingHdr := optEnc }) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.KeysSampled.encodeRaw 2#32
    { uc := some uc, sendingHdr := optEnc }
  have h1 := length_le_encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw
    rawUcHeaderSent rawUcHeaderSent_le_encodeRaw 1#32 (some uc)
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.KeysSampled.encodeRaw, rawUcHeaderSent, optRaw, rawAuth] at h0 h1 ⊢
  rw [hauth] at h1
  dsimp only at h1
  rw [List.length_append] at h0
  omega

private theorem rawAuth_and_enc_le_keysSampled_encodeRaw
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder) (hauth : uc.auth = some auth) :
    auth.rootKey.length + auth.macKey.length +
      (pbEnc.pts.map List.length).sum + (pbEnc.polys.map List.length).sum ≤
      (V1State.encodeRaw
        { innerState := some (.keysSampled { uc := some uc, sendingHdr := some pbEnc }) }).length := by
  have h0 := length_le_encodeMessage V1State.Chunked.KeysSampled.encodeRaw 2#32
    { uc := some uc, sendingHdr := some pbEnc }
  have h1 := length_le_encodeOptMessage V1State.Unchunked.HeaderSent.encodeRaw
    rawUcHeaderSent rawUcHeaderSent_le_encodeRaw 1#32 (some uc)
  have h2 := length_le_encodeMessage PolynomialEncoder.encodeRaw 2#32 pbEnc
  have hp1 := sum_length_le_encodeRepeatedBytes 2#32 pbEnc.pts
  have hp2 := sum_length_le_encodeRepeatedBytes 3#32 pbEnc.polys
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.KeysSampled.encodeRaw,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    PolynomialEncoder.encodeRaw, rawUcHeaderSent, optRaw, rawAuth] at h0 h1 h2 ⊢
  rw [hauth] at h1
  dsimp only at h1
  simp only [List.length_append] at h0 h2
  omega

private theorem auth_of_keysSampledValidAuth?_eq_some {uc : V1State.Unchunked.HeaderSent}
    {auth : ProtoAuthenticator} (h : keysSampledValidAuth? uc = some auth) :
    uc.auth = some auth := by
  unfold keysSampledValidAuth? at h
  split at h
  · exact h
  · contradiction

theorem keysSampledEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.KeysSampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.keysSampled s) }))
    {evs : List AllocEvent} (hevs : KeysSampledFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.keysSampled s) } evs := by
  let pb : V1State := { innerState := some (.keysSampled s) }
  change SpqrBoundedEvs 128 (4 * (V1State.encodeRaw pb).length + 4096) evs
  cases s with | mk optUc optEnc =>
  cases optUc with
  | none =>
    exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
  | some uc =>
    dsimp only [KeysSampledFromPbEnv] at hevs
    cases hval : keysSampledValidAuth? uc with
    | none =>
      rw [hval] at hevs
      exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.of_freeOnly hevs)
    | some auth =>
      rw [hval] at hevs
      have hauth : uc.auth = some auth := auth_of_keysSampledValidAuth?_eq_some hval
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
        have hlen := rawAuth_le_keysSampled_encodeRaw uc auth none hauth
        have hb_r := spqrBoundedEvs_authKeyCloneEvents (bs := auth.rootKey) (by dsimp [pb] at hm_max; omega)
        have hb_m := spqrBoundedEvs_authKeyCloneEvents (bs := auth.macKey) (by dsimp [pb] at hm_max; omega)
        have hb_auth := SpqrBoundedEvs.append hb_r hb_m
        have hb_all := SpqrBoundedEvs.append hb_auth (SpqrBoundedEvs.of_freeOnly hfree)
        exact SpqrBoundedEvs.mono (by decide) (by dsimp [pb]; omega) hb_all
      | some pbEnc =>
        rcases hevs with ⟨evs_af, evs_enc, hfree_af, henc, rfl⟩
        have hlen := rawAuth_and_enc_le_keysSampled_encodeRaw uc auth pbEnc hauth
        have hpb_pts : (pbToProtoPolyEncoder pbEnc).pts = pbEnc.pts := rfl
        have hpb_pol : (pbToProtoPolyEncoder pbEnc).polys = pbEnc.polys := rfl
        have hb_r := spqrBoundedEvs_authKeyCloneEvents (bs := auth.rootKey) (by dsimp [pb] at hm_max; omega)
        have hb_m := spqrBoundedEvs_authKeyCloneEvents (bs := auth.macKey) (by dsimp [pb] at hm_max; omega)
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
    (s : V1State.Chunked.KeysSampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.keysSampled s) })) :
    FitsEnv M lim st (KeysSampledFromPbAllocEnv s) := by
  refine fitsEnv_alloc_of_keysSampledEnv fun evs hevs => ?_
  exact hfits evs (keysSampledEnv_sub_statesFromPbEnv s hfits hevs)

/-! ## Total-Correctness (`SepWP`) Post-`auth` Composition (`+4016 -> s0.x30`) -/

/-- Branch `optEnc = none` at `+4016 -> +5860 -> s0.x30`. -/
theorem v1_keysSampled_4016_none_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63)
    (s0 s : State) (out pbA pa1 pa2 w200 : BitVec 64)
    (u8 u16 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx26 : s.readReg64 .x26 = pa1) (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc none w0 w8 w16 w24 w32 w40 w48 ∗
        vecU8Payload A.repAlloc u8 u16 uc.ek ∗
        vecU8Payload A.repAlloc u32 u40 uc.dk ∗
        vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          KeysSampledTailEnv none evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysSampled { uc := some uc, sendingHdr := none }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hm176 : memRegion (s0.sp - 2400#64) 64 ∗
      ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
      memRegion (s0.sp - 2400#64 + 72#64) 104 ⊢
      memRegion (s0.sp - 2400#64) 176 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (pointsTo64_entails_memRegion _ _) <| Entails.refl _
  rw [v1_from_pb_sendingHdr_none uc auth hauth hdk hek hdk_lt hek_lt]
  dsimp only [v1_optProtoPolyEncoderHeap]
  wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
  refine SepWP.pure_elim fun hw0 => ?_
  subst hw0
  have hnone := v1_sendingHdr_none_4016_5860_placed_budget A lim st (ext := ext)
    s0 s (s0.sp - 2400#64) out pa1 u8 u32 u72
    (((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
     ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗
     ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
     ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗
     ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
     ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48) ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
     memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
     ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
     ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
     ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
     ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
     memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA 112 ∗
     v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
     memRegion (pbA + 168#64) 56 ∗ vecU8Payload A.repAlloc u8 u16 uc.ek ∗
     vecU8Payload A.repAlloc u32 u40 uc.dk ∗ vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
     vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗ statesFromPbJumpTablePlacedAt)
    hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx26 hx28 htr
  have hw_1496 : v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) noneCap w8 w16 w24 w32 w40 w48 =
      ((s0.sp - 2400#64 + 1496#64) ↦₆₄ noneCap) ∗
      ((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
      ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗
      ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
      ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗
      ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
      ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48) := rfl
  refine SepWP.seq (SepWP.weaken_pre (by rw [hw_1496]; exact Entails.of_eq (by sep_ac_rfl)) hnone) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, _hvm1, hsp1, hx0_1, hx19_1, hx21_1, hx22_1, hx28_1, htr1⟩
  have hm24 : ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
      memRegion (s0.sp - 2400#64 + 208#64) 8 ⊢ memRegion (s0.sp - 2400#64 + 192#64) 24 :=
    collapse_top <| collapse_step (pointsTo64_entails_memRegion _ _) <|
      collapse_step (pointsTo64_entails_memRegion _ _) <| Entails.refl _
  have hm1496 := v1_optProtoPolyEncoderWordsAt_entails_56 (s0.sp - 2400#64 + 1496#64) noneCap w8 w16 w24 w32 w40 w48
  have hm2064 : memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
      v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) noneCap w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ⊢ memRegion (s0.sp - 2400#64 + 240#64) 2064 :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hm1496))
      (collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _)
  have hm112 := v1_optProtoPolyEncoderWordsAt_entails_56 (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48
  have hmpb : memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
      memRegion (pbA + 168#64) 56 ⊢ memRegion pbA optProtoInnerStateSize :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left hm112))
      (collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _)
  have hP1' : P1 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 176 ∗
      ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
      memRegion (s0.sp - 2400#64 + 192#64) 24 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      vecCapPtrDealloc A.repAlloc u72 pa1 ∗
      vecCapPtrDealloc A.repAlloc u96 pa2 ∗
      vecCapPtrDealloc A.repAlloc u8 u16 ∗
      vecCapPtrDealloc A.repAlloc u32 u40 ∗
      A.pool lim st s1 ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
    refine Entails.trans hP1 ?_
    rw [hw_1496] at hm2064
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗ memRegion (s0.sp - 2400#64 + 72#64) 104) ∗
      (((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8) ∗
      (memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
       (((s0.sp - 2400#64 + 1496#64) ↦₆₄ noneCap) ∗ ((s0.sp - 2400#64 + 1496#64 + 8#64) ↦₆₄ w8) ∗
        ((s0.sp - 2400#64 + 1496#64 + 16#64) ↦₆₄ w16) ∗ ((s0.sp - 2400#64 + 1496#64 + 24#64) ↦₆₄ w24) ∗
        ((s0.sp - 2400#64 + 1496#64 + 32#64) ↦₆₄ w32) ∗ ((s0.sp - 2400#64 + 1496#64 + 40#64) ↦₆₄ w40) ∗
        ((s0.sp - 2400#64 + 1496#64 + 48#64) ↦₆₄ w48)) ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 752) ∗
      (memRegion pbA 112 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 112#64) noneCap w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56) ∗
      vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
      vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
      vecU8Payload A.repAlloc u8 u16 uc.ek ∗
      vecU8Payload A.repAlloc u32 u40 uc.dk ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
       ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       A.pool lim st s1 ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono hm176 (sepConj_mono hm24 (sepConj_mono hm2064 (sepConj_mono hmpb
        (sepConj_mono (vecU8Payload_entails_dealloc A.repAlloc u72 pa1 auth.rootKey)
          (sepConj_mono (vecU8Payload_entails_dealloc A.repAlloc u96 pa2 auth.macKey)
            (sepConj_mono (vecU8Payload_entails_dealloc A.repAlloc u8 u16 uc.ek)
              (sepConj_mono_left (vecU8Payload_entails_dealloc A.repAlloc u32 u40 uc.dk)))))))))
      (Entails.of_eq (by sep_ac_rfl))
  have hcl_none := v1_cleanup_sendingHdr_none_5860_placed (F := F) hA st s0 s1 out pa1 pa2
    u8 u16 u32 u40 u72 u96 (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
    hsp0_align hpc1 hrun1 hsp1 hx0_1 hx19_1 hx21_1 hx22_1 hx28_1 htr1
  refine SepWP.weaken_pre hP1' (SepWP.mono hcl_none fun sf Pf _ _ ⟨evs_cl, hfree_cl, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
  exact ⟨evs_cl, hfree_cl, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-- Post-`<PolyEncoder>::from_pb` continuation at `+4100 -> s0.x30` (`error` cleanup at `+4116` vs
    `ok` assembly at `+6568`). -/
theorem v1_keysSampled_4100_ret_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder) (evs_enc : List AllocEvent)
    (henv_enc : EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs_enc)
    (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63)
    (s0 s2 : State) (out pbA pa1 pa2 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (hu24 : u24 = BitVec.ofNat 64 uc.ek.length)
    (hu48 : u48 = BitVec.ofNat 64 uc.dk.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.rootKey.length)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (hu104 : u104 = uc.epoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = lsmpl.base 333 + 4100#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx19_2 : s2.readReg64 .x19 = out) (hx21_2 : s2.readReg64 .x21 = u8)
    (hx22_2 : s2.readReg64 .x22 = u72)
    (hx23_2 : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25_2 : s2.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx28_2 : s2.readReg64 .x28 = u32) (htr2 : TraceCalleeSaved s2 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (resultPolyEncoderFromPbAt A.repAlloc (s0.sp - 2400#64 + 1888#64)
        (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
        vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_enc st) s2)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          KeysSampledTailEnv (some pbEnc) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysSampled { uc := some uc, sendingHdr := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hm176 : memRegion (s0.sp - 2400#64) 64 ∗
      ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
      memRegion (s0.sp - 2400#64 + 72#64) 104 ⊢
      memRegion (s0.sp - 2400#64) 176 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (pointsTo64_entails_memRegion _ _) <| Entails.refl _
  rw [v1_from_pb_sendingHdr_some uc auth pbEnc hauth hdk hek hdk_lt hek_lt]
  cases hres : fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | error err =>
    have herr4100 := v1_encoder_err_4100_4116_placed_budget A lim (M.stepEvents evs_enc st)
      (ext := ext) s0 s2 (s0.sp - 2400#64) out u8 u32 u72 err
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
       ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
       memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ vecU8Payload A.repAlloc u8 u16 uc.ek ∗
       vecU8Payload A.repAlloc u32 u40 uc.dk ∗ vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗ memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx25_2 hx28_2 htr2
    refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) herr4100) ?_
    intro s3 P3 hpc3 hrun3 ⟨hP3, _hvm3, hsp3, hx19_3, hx22_3, _, hx26_3, hx28_3, htr3⟩
    have hm2064 : memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
        memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ⊢
        memRegion (s0.sp - 2400#64 + 240#64) 2064 :=
      collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
    have hP3' : P3 ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 2064 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecCapPtrDealloc A.repAlloc u72 pa1 ∗ vecCapPtrDealloc A.repAlloc u96 pa2 ∗
        vecCapPtrDealloc A.repAlloc u8 u16 ∗ vecCapPtrDealloc A.repAlloc u32 u40 ∗
        A.pool lim (M.stepEvents evs_enc st) s3 ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
      refine Entails.trans hP3 ?_
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗ memRegion (s0.sp - 2400#64 + 72#64) 104) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        (memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗ memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗
         memRegion (s0.sp - 2400#64 + 2288#64) 16) ∗
        vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
        vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
         ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
         memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
         ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs_enc st) s3 ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
      exact Entails.trans
        (sepConj_mono hm176 (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono hm2064
          (sepConj_mono (vecU8Payload_entails_dealloc A.repAlloc u72 pa1 auth.rootKey)
            (sepConj_mono (vecU8Payload_entails_dealloc A.repAlloc u96 pa2 auth.macKey)
              (sepConj_mono (vecU8Payload_entails_dealloc A.repAlloc u8 u16 uc.ek)
                (sepConj_mono_left (vecU8Payload_entails_dealloc A.repAlloc u32 u40 uc.dk))))))))
        (Entails.of_eq (by sep_ac_rfl))
    have hcl_err := v1_cleanup_enc_err_4116_placed (F := F) hA (M.stepEvents evs_enc st)
      s0 s3 out pa1 pa2 u8 u16 u32 u40 u72 u96
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc3 hrun3 hsp3 hx19_3 hx22_3 hx26_3 hx28_3 htr3
    refine SepWP.weaken_pre hP3' (SepWP.mono hcl_err fun sf Pf _ _ ⟨evs_cl, hfree_cl, hPf, hsp_f, hcs_f, htr_f⟩ => ?_)
    refine ⟨evs_enc ++ evs_cl, encoderFromPbEnv_append_freeOnly henv_enc hfree_cl, ?_, hsp_f, hcs_f, htr_f⟩
    rw [M.stepEvents_append]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
  | ok enc =>
    dsimp only [resultPolyEncoderFromPbAt]
    refine SepWP.weaken_pre
      (sepConj_mono_left (v1_polyEncoderAt_relocate A.repAlloc (s0.sp - 2400#64 + 1888#64) (out + 8#64) enc)) ?_
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun tag =>
      ProofLib.SepWP.exists_left fun bs =>
      ProofLib.SepWP.exists_left fun hi32 =>
      ProofLib.SepWP.exists_left fun P_heap => ?_
    apply SepWP.pure_elim; rintro ⟨htag, hreloc⟩
    have ha2280 : (s0.sp - 2400#64 + 1888#64) + 392#64 = s0.sp - 2400#64 + 2280#64 := by bv_omega
    wp_conv_pre => rw [v1_bs384_eq_encCells bs.val bs.property (s0.sp - 2400#64 + 1888#64), ha2280]
    have hok4100 := v1_encoder_ok_4100_6568_placed_budget A lim (M.stepEvents evs_enc st)
      (ext := ext) s0 s2 (s0.sp - 2400#64) out tag u8 u32 u72
      (v1_encCellsAt (s0.sp - 2400#64 + 1888#64) bs.val ∗
       ((s0.sp - 2400#64 + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
       P_heap ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
       ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
       memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ vecU8Payload A.repAlloc u8 u16 uc.ek ∗
       vecU8Payload A.repAlloc u32 u40 uc.dk ∗ vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗ memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTablePlacedAt)
      hfsp_align htag hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx23_2 hx25_2 hx28_2 htr2
    refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hok4100) ?_
    intro s3 P3 hpc3 hrun3 ⟨hP3, _hvm3, hsp3, hx15_3, hx19_3, hx21_3, hx22_3, hx23_3, hx25_3, hx26_3, hx28_3, htr3⟩
    have hu24_1152 : u24 = 1152#64 := by rw [hu24]; exact beq_iff_eq.mp hek
    subst hu104
    have h6568 := v1_keysSampled_6568_ret_placed (F := F) hA (M.stepEvents evs_enc st)
      s0 s3 out tag pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 uc.epoch bs.val bs.property hi32 enc
      P_heap hreloc uc.ek uc.dk auth.rootKey auth.macKey hu24 hu48 hu72 hu96 hu24_1152
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
      hsp0_align hpc3 hrun3 hsp3 hx15_3 hx19_3 hx21_3 hx22_3 hx23_3 hx25_3 hx26_3 hx28_3 htr3
    refine SepWP.weaken_pre (Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl)))
      (SepWP.mono h6568 fun sf Pf _ _ ⟨hPf, _hvmf, hsp_f, hcs_f, htr_f⟩ => ?_)
    exact ⟨evs_enc, henv_enc, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-- Branch `optEnc = some pbEnc` at `+4016 -> +4096 -> +4100 -> s0.x30`. -/
theorem v1_keysSampled_4016_some_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (pbEnc : PolynomialEncoder)
    (hpts : optEncoderPtsBound (some pbEnc))
    (hfits_tail : FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)))
    (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA pa1 pa2 w200 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hu24 : u24 = BitVec.ofNat 64 uc.ek.length)
    (hu48 : u48 = BitVec.ofNat 64 uc.dk.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.rootKey.length)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (hu104 : u104 = uc.epoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = pa1) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        vecU8Payload A.repAlloc u8 u16 uc.ek ∗
        vecU8Payload A.repAlloc u32 u40 uc.dk ∗
        vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          KeysSampledTailEnv (some pbEnc) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysSampled { uc := some uc, sendingHdr := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  have hex_w0 := v1_optProtoPolyEncoderHeap_extract_w0 A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
    w0 w8 w16 w24 w32 w40 w48
  dsimp only at hex_w0
  have hsplit1256 : memRegion (s0.sp - 2400#64 + 240#64) 1256 ⊢
      memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
      memRegion (s0.sp - 2400#64 + 896#64) 56 ∗
      memRegion (s0.sp - 2400#64 + 952#64) 544 :=
    split_top <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
  have hsplit752 : memRegion (s0.sp - 2400#64 + 1552#64) 752 ⊢
      memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗
      memRegion (s0.sp - 2400#64 + 1888#64) polyEncoderSize ∗
      memRegion (s0.sp - 2400#64 + 2288#64) 16 :=
    split_top <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
       ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
       v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA 112 ∗
       v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 168#64) 56 ∗ vecU8Payload A.repAlloc u8 u16 uc.ek ∗
       vecU8Payload A.repAlloc u32 u40 uc.dk ∗ vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
       vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗ statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s) by sep_ac_rfl))
      (Entails.trans (sepConj_mono hex_w0 (sepConj_mono hsplit1256 (sepConj_mono_left hsplit752)))
        (Entails.of_eq (by sep_ac_rfl)))) ?_
  refine SepWP.pure_elim fun hw0 => ?_
  have h4016 := v1_sendingHdr_some_copy_4016_4096_placed_budget A lim st (ext := ext)
    s0 s (s0.sp - 2400#64) out pbA pa1 w200 u8 u32 u72
    (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
     memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
     ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
     memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
     ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
     memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
     memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗ memRegion (s0.sp - 2400#64 + 1888#64) polyEncoderSize ∗
     memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
     vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
     vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
     statesFromPbJumpTablePlacedAt)
    hfsp_align hw0 hpc hrun hsp hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 htr
  refine seq_clean_lscl_st hcl (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h4016) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨_hvm1, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx28_1, htr1⟩
  have hcall := v1_encoder_call_4096_to_4100_placed_sepWP henc st s0 s1 hcl1
    (s0.sp - 2400#64) out pbA u8 u32 u72 (pbToProtoPolyEncoder pbEnc)
    (((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗
     memRegion (s0.sp - 2400#64 + 1496#64) 56 ∗
     memRegion (pbA + 112#64) 56 ∗
     memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
     memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
     ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
     memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
     ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
     memRegion (s0.sp - 2400#64 + 240#64) 656 ∗ memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
     memRegion (s0.sp - 2400#64 + 1552#64) 336 ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
     vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
     vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
     statesFromPbJumpTablePlacedAt)
    hfits_tail hfsp_align hpts hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx28_1 htr1
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hcall) ?_
  intro s2 P2 hpc2 hrun2 ⟨evs_enc, henv_enc, hP2, hsp2, hx19_2, hx21_2, hx22_2, hx23_2, hx25_2, hx28_2, htr2⟩
  have hm1648 : memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
      memRegion (s0.sp - 2400#64 + 896#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
      memRegion (s0.sp - 2400#64 + 1496#64) 56 ∗
      memRegion (s0.sp - 2400#64 + 1552#64) 336 ⊢
      memRegion (s0.sp - 2400#64 + 240#64) 1648 :=
    collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  have hmpb : memRegion pbA 112 ∗ memRegion (pbA + 112#64) 56 ∗ memRegion (pbA + 168#64) 56 ⊢
      memRegion pbA optProtoInnerStateSize :=
    collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Entails.refl _) <| Entails.refl _
  have hP2' : P2 ⊢
      resultPolyEncoderFromPbAt A.repAlloc (s0.sp - 2400#64 + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
      memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
      ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
      ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 1648 ∗
      memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
      vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
      memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs_enc st) s2 := by
    refine Entails.trans hP2 ?_
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
       memRegion (s0.sp - 2400#64 + 896#64) protoPolynomialEncoderSize ∗
       memRegion (s0.sp - 2400#64 + 952#64) 544 ∗
       memRegion (s0.sp - 2400#64 + 1496#64) 56 ∗
       memRegion (s0.sp - 2400#64 + 1552#64) 336) ∗
      (memRegion pbA 112 ∗ memRegion (pbA + 112#64) 56 ∗ memRegion (pbA + 168#64) 56) ∗
      (resultPolyEncoderFromPbAt A.repAlloc (s0.sp - 2400#64 + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
       memRegion (s0.sp - 2400#64 + 72#64) 104 ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
       ((s0.sp - 2400#64 + 200#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
       ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
       ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A.repAlloc u8 u16 uc.ek ∗ vecU8Payload A.repAlloc u32 u40 uc.dk ∗
       vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗ vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs_enc st) s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hm1648 (sepConj_mono_left hmpb)) (Entails.of_eq (by sep_ac_rfl))
  exact SepWP.weaken_pre hP2'
    (v1_keysSampled_4100_ret_placed_sepWP hA st uc auth pbEnc evs_enc henv_enc
      hauth hdk hek hdk_lt hek_lt s0 s2 out pbA pa1 pa2 u8 u16 u24 u32 u40 u48 u72 u96 u104
      hu24 hu48 hu72 hu96 hu104 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx21_2 hx22_2 hx23_2 hx25_2 hx28_2 htr2)

/-- Combined post-`auth` total-correctness (`SepWP`) theorem at `+4016 -> s0.x30` for any
    `optEnc : Option PolynomialEncoder`. -/
theorem v1_keysSampled_4016_ret_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext) (st : M.σ)
    (uc : V1State.Unchunked.HeaderSent) (auth : ProtoAuthenticator)
    (optEnc : Option PolynomialEncoder)
    (hpts : optEncoderPtsBound optEnc)
    (hfits_tail : KeysSampledTailFits M lim st optEnc)
    (hauth : uc.auth = some auth)
    (hdk : (BitVec.ofNat 64 uc.dk.length == 2400#64) = true)
    (hek : (BitVec.ofNat 64 uc.ek.length == 1152#64) = true)
    (hdk_lt : uc.dk.length < 2 ^ 63) (hek_lt : uc.ek.length < 2 ^ 63)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA pa1 pa2 w200 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u72 u96 u104 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (hu24 : u24 = BitVec.ofNat 64 uc.ek.length)
    (hu48 : u48 = BitVec.ofNat 64 uc.dk.length)
    (hu72 : u72 = BitVec.ofNat 64 auth.rootKey.length)
    (hu96 : u96 = BitVec.ofNat 64 auth.macKey.length)
    (hu104 : u104 = uc.epoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8) (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = pa1) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u32) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        ((s0.sp - 2400#64 + 64#64) ↦₆₄ u104) ∗
        memRegion (s0.sp - 2400#64 + 72#64) 104 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 192#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ u32) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u96) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1256 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1552#64) 752 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (optEnc.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        vecU8Payload A.repAlloc u8 u16 uc.ek ∗
        vecU8Payload A.repAlloc u32 u40 uc.dk ∗
        vecU8Payload A.repAlloc u72 pa1 auth.rootKey ∗
        vecU8Payload A.repAlloc u96 pa2 auth.macKey ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          KeysSampledTailEnv optEnc evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.keysSampled { uc := some uc, sendingHdr := optEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  cases optEnc with
  | none =>
    exact v1_keysSampled_4016_none_placed_sepWP hA st uc auth hauth hdk hek hdk_lt hek_lt
      s0 s out pbA pa1 pa2 w200 u8 u16 u32 u40 u48 u72 u96 u104 w0 w8 w16 w24 w32 w40 w48
      hsp0_align hpc hrun hsp hx19 hx20 hx21 hx22 hx26 hx28 htr
  | some pbEnc =>
    exact v1_keysSampled_4016_some_placed_sepWP hA henc st uc auth pbEnc hpts hfits_tail
      hauth hdk hek hdk_lt hek_lt s0 s hcl out pbA pa1 pa2 w200
      u8 u16 u24 u32 u40 u48 u72 u96 u104 w0 w8 w16 w24 w32 w40 w48
      hu24 hu48 hu72 hu96 hu104 hsp0_align hpc hrun hsp hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2PlacedBudgetAux
