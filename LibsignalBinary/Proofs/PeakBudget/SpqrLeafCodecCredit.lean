/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase

/-!
# SPQR V1 Leaf Codec, Polynomial, and Chain Credit Specs

Exact-call-order `PhaseCreditSpec` bounds for SPQR V1 leaf protobuf codecs
(`<Authenticator>::from_pb`, `<Ct1Sent>::from_pb`, `<EkSentCt1Received>::from_pb`), polynomial
codecs and interpolation (`PolyEncoder`, `PolyDecoder`, `<Poly>::lagrange_interpolate_prepare`),
chain codecs (`<Chain>::into_pb`, `spqr::chain_from`), and `spqr::kdf::hkdf_to_vec`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB Direction GF16 PolyDecoder PolyEncoder ProtoAuthenticator ProtoPolynomialDecoder
   ProtoPolynomialEncoder Pt VersionNegotiationPB spqrAuthApi)
open CryptoVerification.SpqrV1.ChainProofs (ChainIntoPbCall)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (LagrangePrepareArgs)
open CryptoVerification.SpqrV1.Top.StateSize (rawAuth)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (Ct1SentFromPbPostEnv Ct1SentFromPbPreEnv EkSentCt1ReceivedFromPbPostEnv
   EkSentCt1ReceivedFromPbPreEnv PbCt1Sent PbEkSentCt1Received authFromPbAllocEvents
   ct1SentFromPb ct1SentFromPbAllocEvents ekSentCt1ReceivedFromPb
   ekSentCt1ReceivedFromPbAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbPolysInitEvents
   encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents encoderFromPbPtsLoopEvents
   encoderFromPbPtsSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbAllocEvents encoderIntoPbSlotEvents
   encoderIntoPbVecs)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecLoopAllocEvents fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbAllocEvents decoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
  (ChainIntoPbAllocEnv ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromAllocEnv ChainFromEnv ChainFromVersionNegotiationEnv chainNewEvents)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (HkdfToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.DefsBudget (LagrangePrepareEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv IterConcatEnv ModelHyps PhaseCreditSpec iterPeak)

/-! ## Exact-Order `flatMap`, `replicate`, and `takeWhile` List Combinators -/

private theorem iterConcatEnv_flatMap {α : Type} (f : α → List AllocEvent) :
    ∀ (xs : List α), IterConcatEnv (fun x evs => evs = f x) xs (xs.flatMap f)
  | [] => rfl
  | x :: xs => ⟨f x, xs.flatMap f, rfl, rfl, iterConcatEnv_flatMap f xs⟩

private theorem iterPeak_le_sum_of_le {α : Type} (l p : α → Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, p x ≤ l x) → iterPeak l p xs ≤ (xs.map l).sum
  | [], _ => by simp [iterPeak]
  | x :: xs, hle => by
    have hx := hle x List.mem_cons_self
    have hxs := iterPeak_le_sum_of_le l p xs fun y hy => hle y (List.mem_cons_of_mem x hy)
    simp only [iterPeak, List.map_cons, List.sum_cons]
    omega

private theorem foldr_max_le_sum : ∀ (ns : List Nat), ns.foldr max 0 ≤ ns.sum
  | [] => Nat.le_refl 0
  | n :: ns => by
    have ih := foldr_max_le_sum ns
    simp only [List.foldr_cons, List.sum_cons]
    omega

private theorem flatMap_phaseCreditSpec {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (f : α → List AllocEvent) (c l r : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (· = f x) (c x) (l x) (l x) (r x)) :
    PhaseCreditSpec M (· = xs.flatMap f)
      (xs.map c).sum (xs.map l).sum (xs.map l).sum (xs.map r).sum := by
  have hiter := PhaseCreditSpec.iterConcat c l l r xs hstep
  have hpeak := iterPeak_le_sum_of_le l l xs fun _ _ => Nat.le_refl _
  have hmax := foldr_max_le_sum (xs.map r)
  exact (hiter.of_imp fun _ h => h ▸ iterConcatEnv_flatMap f xs).mono
    (Nat.le_refl _) (Nat.le_refl _) hpeak hmax

private theorem replicate_flatten_eq_flatMap (n : Nat) (evs₀ : List AllocEvent) :
    (List.replicate n evs₀).flatten = (List.replicate n ()).flatMap (fun _ => evs₀) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.flatMap_cons, ih]

private theorem replicate_flatten_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (n : Nat) (evs₀ : List AllocEvent) {c l r : Nat}
    (h₀ : PhaseCreditSpec M (· = evs₀) c l l r) :
    PhaseCreditSpec M (· = (List.replicate n evs₀).flatten)
      (n * c) (n * l) (n * l) r := by
  have hmax : (((List.replicate n ()).map (fun _ => r)).foldr max 0) ≤ r := by
    induction n with
    | zero => exact Nat.zero_le r
    | succ k ih =>
      simp only [List.replicate_succ, List.map_cons, List.foldr_cons]
      exact Nat.max_le.2 ⟨Nat.le_refl r, ih⟩
  have hiter := PhaseCreditSpec.iterConcat
    (fun _ : Unit => c) (fun _ => l) (fun _ => l) (fun _ => r)
    (List.replicate n ()) (fun _ _ => h₀)
  have hsum_c : ((List.replicate n ()).map (fun _ => c)).sum = n * c := by
    simp [List.map_replicate, List.sum_replicate]
  have hsum_l : ((List.replicate n ()).map (fun _ => l)).sum = n * l := by
    simp [List.map_replicate, List.sum_replicate]
  have hpeak := iterPeak_le_sum_of_le (fun _ : Unit => l) (fun _ => l)
    (List.replicate n ()) (fun _ _ => Nat.le_refl l)
  refine (hiter.of_imp fun _ h => ?_).mono
    (Nat.le_of_eq hsum_c) (Nat.le_of_eq hsum_l) (by omega) hmax
  rw [h, replicate_flatten_eq_flatMap]
  exact iterConcatEnv_flatMap (fun _ : Unit => evs₀) (List.replicate n ())

private theorem sum_map_aff {α : Type} (g : α → Nat) (a b : Nat) :
    ∀ (xs : List α), (xs.map (fun x => a * g x + b)).sum = a * (xs.map g).sum + xs.length * b
  | [] => by simp
  | x :: xs => by
    have ih := sum_map_aff g a b xs
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.mul_add]
    omega

private theorem sum_map_add_const {α : Type} (g : α → Nat) (b : Nat) (xs : List α) :
    (xs.map (fun x => g x + b)).sum = (xs.map g).sum + xs.length * b := by
  have h := sum_map_aff g 1 b xs
  simp only [Nat.one_mul] at h
  exact h

private theorem sum_map_mul {α : Type} (g : α → Nat) (a : Nat) :
    ∀ (xs : List α), (xs.map (fun x => a * g x)).sum = a * (xs.map g).sum
  | [] => by simp
  | x :: xs => by
    have ih := sum_map_mul g a xs
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

private theorem takeWhile_length_le {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.takeWhile p).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.takeWhile]
    split
    · have ih := takeWhile_length_le p xs
      simp only [List.length_cons]
      omega
    · exact Nat.zero_le _

private theorem takeWhile_map_sum_le {α : Type} (p : α → Bool) (g : α → Nat) :
    ∀ (xs : List α), ((xs.takeWhile p).map g).sum ≤ (xs.map g).sum
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.takeWhile, List.map_cons, List.sum_cons]
    split
    · have ih := takeWhile_map_sum_le p g xs
      simp only [List.map_cons, List.sum_cons]
      omega
    · exact Nat.zero_le _

private theorem concat_freeOnly_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E_alloc Env : List AllocEvent → Prop} {c l r : Nat}
    (hsub : ∀ evs, Env evs → ConcatEnv E_alloc FreeOnlyEvs evs)
    (halloc : PhaseCreditSpec M E_alloc c l l r) :
    PhaseCreditSpec M Env c l l r := by
  have hcat := halloc.concat (PhaseCreditSpec.freeOnly_of_hyps hM)
  exact (hcat.of_imp hsub).mono (by omega) (by omega) (by omega) (by omega)

/-! ## `<Authenticator>::from_pb`, `<Ct1Sent>::from_pb`, and `<EkSentCt1Received>::from_pb` -/

private theorem optRustAlloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cond : Bool) (req al : Nat) (hal : al ≤ 16) :
    PhaseCreditSpec M (· = if cond then [] else rustAllocEvents req al)
      (2 * req + 9539) (req + 8195) (req + 8195) req := by
  cases cond
  · exact PhaseCreditSpec.rustAlloc_aff hM hal
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

theorem authFromPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pb : ProtoAuthenticator) :
    let R := pb.rootKey.length + pb.macKey.length
    PhaseCreditSpec M (AuthFromPbEnv pb)
      (2 * R + 19078) (R + 16390) (R + 16390)
      (max pb.rootKey.length pb.macKey.length) := by
  dsimp only
  have hroot : PhaseCreditSpec M (· = authKeyCloneEvents pb.rootKey)
      (2 * pb.rootKey.length + 9539) (pb.rootKey.length + 8195)
      (pb.rootKey.length + 8195) pb.rootKey.length :=
    optRustAlloc_aff hM pb.rootKey.isEmpty pb.rootKey.length 1 (by decide)
  have hmac : PhaseCreditSpec M (· = authKeyCloneEvents pb.macKey)
      (2 * pb.macKey.length + 9539) (pb.macKey.length + 8195)
      (pb.macKey.length + 8195) pb.macKey.length :=
    optRustAlloc_aff hM pb.macKey.isEmpty pb.macKey.length 1 (by decide)
  have hcat := hroot.concat hmac
  refine (hcat.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (Nat.le_refl _)
  rw [h]
  exact ⟨authKeyCloneEvents pb.rootKey, authKeyCloneEvents pb.macKey, rfl, rfl, rfl⟩

theorem authFromPb_raw_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pb : ProtoAuthenticator) :
    let R := rawAuth pb
    PhaseCreditSpec M (AuthFromPbEnv pb)
      (2 * R + 19078) (R + 16390) (R + 16390) R := by
  have hraw : pb.rootKey.length + pb.macKey.length ≤ rawAuth pb := by
    unfold rawAuth; omega
  have hmax : max pb.rootKey.length pb.macKey.length ≤ rawAuth pb := by
    unfold rawAuth; omega
  exact (authFromPb_phaseCreditSpec hM pb).mono (by omega) (by omega) (by omega) hmax

private theorem authFromPbAllocEvents_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (auth : ProtoAuthenticator) :
    let R := auth.rootKey.length + auth.macKey.length
    PhaseCreditSpec M (· = authFromPbAllocEvents auth)
      (2 * R + 19078) (R + 16390) (R + 16390) R := by
  dsimp only
  have hroot : PhaseCreditSpec M
      (· = if auth.rootKey = [] then [] else rustAllocEvents auth.rootKey.length 1)
      (2 * auth.rootKey.length + 9539) (auth.rootKey.length + 8195)
      (auth.rootKey.length + 8195) auth.rootKey.length := by
    split
    · exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have hmac : PhaseCreditSpec M
      (· = if auth.macKey = [] then [] else rustAllocEvents auth.macKey.length 1)
      (2 * auth.macKey.length + 9539) (auth.macKey.length + 8195)
      (auth.macKey.length + 8195) auth.macKey.length := by
    split
    · exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact PhaseCreditSpec.rustAlloc_aff hM (by decide)
  have hcat := hroot.concat hmac
  refine (hcat.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (by omega)
  rw [h]
  exact ⟨_, _, rfl, rfl, rfl⟩

/-- Total byte length of an optional `ProtoAuthenticator`'s root and MAC keys. -/
def optAuthKeyLen : Option ProtoAuthenticator → Nat
  | none => 0
  | some auth => auth.rootKey.length + auth.macKey.length

/-- `PhaseCreditSpec` for `<Ct1Sent>::from_pb`. -/
theorem ct1SentFromPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (pb : PbCt1Sent) :
    let R := optAuthKeyLen pb.auth
    PhaseCreditSpec M (Ct1SentFromPbPostEnv F pb)
      (2 * R + 19078) (R + 16390) (R + 16390) R := by
  dsimp only
  have halloc : PhaseCreditSpec M (Ct1SentFromPbPreEnv F pb)
      (2 * optAuthKeyLen pb.auth + 19078)
      (optAuthKeyLen pb.auth + 16390)
      (optAuthKeyLen pb.auth + 16390)
      (optAuthKeyLen pb.auth) := by
    unfold Ct1SentFromPbPreEnv ct1SentFromPbAllocEvents
    cases hres : ct1SentFromPb (spqrAuthApi F) pb with
    | error _ =>
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok _ =>
      cases hauth : pb.auth with
      | none =>
        exact (PhaseCreditSpec.nil M).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | some auth =>
        simpa [optAuthKeyLen, hauth] using authFromPbAllocEvents_phaseCreditSpec hM auth
  refine concat_freeOnly_phaseCreditSpec hM (fun _ h => ?_) halloc
  obtain ⟨evsFree, hFree, rfl⟩ := h
  exact ⟨ct1SentFromPbAllocEvents F pb, evsFree, rfl, rfl, hFree⟩

/-- `PhaseCreditSpec` for `<EkSentCt1Received>::from_pb`. -/
theorem ekSentCt1ReceivedFromPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (pb : PbEkSentCt1Received) :
    let R := optAuthKeyLen pb.auth
    PhaseCreditSpec M (EkSentCt1ReceivedFromPbPostEnv F pb)
      (2 * R + 19078) (R + 16390) (R + 16390) R := by
  dsimp only
  have halloc : PhaseCreditSpec M (EkSentCt1ReceivedFromPbPreEnv F pb)
      (2 * optAuthKeyLen pb.auth + 19078)
      (optAuthKeyLen pb.auth + 16390)
      (optAuthKeyLen pb.auth + 16390)
      (optAuthKeyLen pb.auth) := by
    unfold EkSentCt1ReceivedFromPbPreEnv ekSentCt1ReceivedFromPbAllocEvents
    cases hres : ekSentCt1ReceivedFromPb (spqrAuthApi F) pb with
    | error _ =>
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok _ =>
      cases hauth : pb.auth with
      | none =>
        exact (PhaseCreditSpec.nil M).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | some auth =>
        simpa [optAuthKeyLen, hauth] using authFromPbAllocEvents_phaseCreditSpec hM auth
  refine concat_freeOnly_phaseCreditSpec hM (fun _ h => ?_) halloc
  obtain ⟨evsFree, hFree, rfl⟩ := h
  exact ⟨ekSentCt1ReceivedFromPbAllocEvents F pb, evsFree, rfl, rfl, hFree⟩

/-! ## `<PolyEncoder>::from_pb` and `<PolyEncoder>::into_pb` -/

private theorem encoderFromPbPtsLoop_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {pts : List (List (BitVec 8))} (hlen : pts.length = 16) :
    let P := (pts.map List.length).sum
    PhaseCreditSpec M (· = encoderFromPbPtsLoopEvents pts)
      (4 * P + 152624) (2 * P + 131120) (2 * P + 131120) (2 * P) := by
  dsimp only
  let pfx := pts.takeWhile (fun bs => bs.length % 2 == 0)
  have hslot : ∀ bs ∈ pfx, PhaseCreditSpec M (· = encoderFromPbPtsSlotEvents bs)
      (4 * bs.length + 9539) (2 * bs.length + 8195) (2 * bs.length + 8195) (2 * bs.length) := by
    intro bs _
    have h := optRustAlloc_aff hM bs.isEmpty (2 * bs.length) 2 (by decide)
    exact h.mono (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hfm := flatMap_phaseCreditSpec encoderFromPbPtsSlotEvents
    (fun bs => 4 * bs.length + 9539) (fun bs => 2 * bs.length + 8195)
    (fun bs => 2 * bs.length) pfx hslot
  have hc_eq := sum_map_aff List.length 4 9539 pfx
  have hl_eq := sum_map_aff List.length 2 8195 pfx
  have hr_eq := sum_map_mul List.length 2 pfx
  have htw_len : pfx.length ≤ 16 := hlen ▸ takeWhile_length_le _ pts
  have htw_sum : (pfx.map List.length).sum ≤ (pts.map List.length).sum :=
    takeWhile_map_sum_le _ List.length pts
  exact hfm.mono (by omega) (by omega) (by omega) (by omega)

private theorem encoderFromPbPolysBranch_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {polys : List (List (BitVec 8))} (hlen : polys.length = 16) :
    let Q := (polys.map List.length).sum
    PhaseCreditSpec M (· = encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents polys)
      (2 * Q + 305312) (Q + 262272) (Q + 262272) (Q + 2) := by
  dsimp only
  have hinit : PhaseCreditSpec M (· = encoderFromPbPolysInitEvents)
      152688 131152 131152 2 := by
    have h2 := PhaseCreditSpec.rustAlloc_aff hM (req := 2) (al := 2) (by decide)
    have hrep := replicate_flatten_phaseCreditSpec 16 (rustAllocEvents 2 2) h2
    exact hrep.mono (by omega) (by omega) (by omega) (Nat.le_refl 2)
  let pfx := polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))
  have hslot : ∀ bs ∈ pfx, PhaseCreditSpec M (· = encoderFromPbPolysSlotEvents bs)
      (2 * bs.length + 9539) (bs.length + 8195) (bs.length + 8195) bs.length := by
    intro bs _
    have ha := PhaseCreditSpec.rustAlloc_aff hM (req := bs.length) (al := 2) (by decide)
    have hd := PhaseCreditSpec.rustDealloc_align16 M (req := 2) (al := 2) (by decide)
    have hcat := ha.concat hd
    refine (hcat.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (by omega)
    rw [h]
    exact ⟨rustAllocEvents bs.length 2, rustDeallocEvents 2 2, rfl, rfl, rfl⟩
  have hloop := flatMap_phaseCreditSpec encoderFromPbPolysSlotEvents
    (fun bs => 2 * bs.length + 9539) (fun bs => bs.length + 8195) List.length pfx hslot
  have hc_eq := sum_map_aff List.length 2 9539 pfx
  have hl_eq := sum_map_add_const List.length 8195 pfx
  have htw_len : pfx.length ≤ 16 := hlen ▸ takeWhile_length_le _ polys
  have htw_sum : (pfx.map List.length).sum ≤ (polys.map List.length).sum :=
    takeWhile_map_sum_le _ List.length polys
  have hcat := hinit.concat hloop
  refine (hcat.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (by omega)
  rw [h]
  exact ⟨encoderFromPbPolysInitEvents, encoderFromPbPolysLoopEvents polys, rfl, rfl, rfl⟩

/-- Allocation-phase `PhaseCreditSpec` for `<PolyEncoder>::from_pb`. -/
theorem encoderFromPbAlloc_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pb : ProtoPolynomialEncoder) :
    let R := 2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum
    PhaseCreditSpec M (EncoderFromPbAllocEnv pb)
      (2 * R + 305312) (R + 262272) (R + 262272) (R + 2) := by
  dsimp only
  have h1 : PhaseCreditSpec M
      (fun evs => pb.pts.length = 16 ∧ pb.polys.length = 0 ∧
        evs = encoderFromPbPtsLoopEvents pb.pts)
      (4 * (pb.pts.map List.length).sum + 152624)
      (2 * (pb.pts.map List.length).sum + 131120)
      (2 * (pb.pts.map List.length).sum + 131120)
      (2 * (pb.pts.map List.length).sum) := by
    by_cases hpts16 : pb.pts.length = 16
    · exact (encoderFromPbPtsLoop_phaseCreditSpec hM hpts16).of_imp fun _ ⟨_, _, heq⟩ => heq
    · exact ((PhaseCreditSpec.empty M).of_imp fun _ ⟨h, _⟩ => hpts16 h).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have h2 : PhaseCreditSpec M
      (fun evs => pb.pts.length = 0 ∧ pb.polys.length = 16 ∧
        evs = encoderFromPbPolysInitEvents ++ encoderFromPbPolysLoopEvents pb.polys)
      (2 * (pb.polys.map List.length).sum + 305312)
      ((pb.polys.map List.length).sum + 262272)
      ((pb.polys.map List.length).sum + 262272)
      ((pb.polys.map List.length).sum + 2) := by
    by_cases hpolys16 : pb.polys.length = 16
    · exact (encoderFromPbPolysBranch_phaseCreditSpec hM hpolys16).of_imp fun _ ⟨_, _, heq⟩ => heq
    · exact ((PhaseCreditSpec.empty M).of_imp fun _ ⟨_, h, _⟩ => hpolys16 h).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  exact ((PhaseCreditSpec.nil M).or (h1.or h2)).congr_mono (fun _ h => h)
    (by omega) (by omega) (by omega) (by omega)

theorem encoderFromPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pb : ProtoPolynomialEncoder) :
    let R := 2 * (pb.pts.map List.length).sum + (pb.polys.map List.length).sum
    PhaseCreditSpec M (EncoderFromPbEnv pb)
      (2 * R + 305312) (R + 262272) (R + 262272) (R + 2) :=
  concat_freeOnly_phaseCreditSpec hM
    (fun _ ⟨ea, ef, heq, ha, hf⟩ => ⟨ea, ef, heq, ha, hf⟩)
    (encoderFromPbAlloc_phaseCreditSpec hM pb)

/-- Allocation-phase `PhaseCreditSpec` for `<PolyEncoder>::into_pb`. -/
theorem encoderIntoPbAlloc_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (enc : PolyEncoder) :
    let V := ((encoderIntoPbVecs enc).map List.length).sum
    let N := (encoderIntoPbVecs enc).length
    PhaseCreditSpec M (EncoderIntoPbAllocEnv enc)
      (4 * V + N * 9539 + 20614)
      (2 * V + N * 8195 + 17158)
      (2 * V + N * 8195 + 17158)
      (max 384 (2 * V)) := by
  dsimp only
  have h384 := PhaseCreditSpec.rustAlloc_aff hM (req := 384) (al := 8) (by decide)
  have hhdr := h384.concat h384
  have hslot : ∀ cs ∈ encoderIntoPbVecs enc, PhaseCreditSpec M (· = encoderIntoPbSlotEvents cs)
      (4 * cs.length + 9539) (2 * cs.length + 8195) (2 * cs.length + 8195) (2 * cs.length) := by
    intro cs _
    exact (optRustAlloc_aff hM cs.isEmpty (2 * cs.length) 1 (by decide)).mono
      (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hslots := flatMap_phaseCreditSpec encoderIntoPbSlotEvents
    (fun cs => 4 * cs.length + 9539) (fun cs => 2 * cs.length + 8195)
    (fun cs => 2 * cs.length) (encoderIntoPbVecs enc) hslot
  have hc_eq := sum_map_aff List.length 4 9539 (encoderIntoPbVecs enc)
  have hl_eq := sum_map_aff List.length 2 8195 (encoderIntoPbVecs enc)
  have hr_eq := sum_map_mul List.length 2 (encoderIntoPbVecs enc)
  have hcat := hhdr.concat hslots
  refine (hcat.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (by omega)
  rw [h]
  exact ⟨rustAllocEvents 384 8 ++ rustAllocEvents 384 8,
    (encoderIntoPbVecs enc).flatMap encoderIntoPbSlotEvents, rfl,
    ⟨rustAllocEvents 384 8, rustAllocEvents 384 8, rfl, rfl, rfl⟩, rfl⟩

theorem encoderIntoPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (enc : PolyEncoder) :
    let V := ((encoderIntoPbVecs enc).map List.length).sum
    let N := (encoderIntoPbVecs enc).length
    PhaseCreditSpec M (EncoderIntoPbEnv enc)
      (4 * V + N * 9539 + 20614)
      (2 * V + N * 8195 + 17158)
      (2 * V + N * 8195 + 17158)
      (max 384 (2 * V)) :=
  concat_freeOnly_phaseCreditSpec hM
    (fun _ ⟨ea, ef, heq, ha, hf⟩ => ⟨ea, ef, heq, ha, hf⟩)
    (encoderIntoPbAlloc_phaseCreditSpec hM enc)

/-! ## `<PolyDecoder>::from_pb` and `<PolyDecoder>::into_pb` -/

private theorem fromPbDecLoop_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {pts : List (List (BitVec 8))} (hlen : pts.length = 16) :
    let P := (pts.map List.length).sum
    PhaseCreditSpec M (· = fromPbDecLoopAllocEvents pts)
      (2 * P + 152624) (P + 131120) (P + 131120) P := by
  dsimp only
  let pfx := pts.takeWhile (fun bs => bs.length % 4 == 0)
  have hslot : ∀ bs ∈ pfx, PhaseCreditSpec M (· = fromPbDecSlotEvents bs)
      (2 * bs.length + 9539) (bs.length + 8195) (bs.length + 8195) bs.length := by
    intro bs _
    exact optRustAlloc_aff hM bs.isEmpty bs.length 2 (by decide)
  have hfm := flatMap_phaseCreditSpec fromPbDecSlotEvents
    (fun bs => 2 * bs.length + 9539) (fun bs => bs.length + 8195) List.length pfx hslot
  have hc_eq := sum_map_aff List.length 2 9539 pfx
  have hl_eq := sum_map_add_const List.length 8195 pfx
  have htw_len : pfx.length ≤ 16 := hlen ▸ takeWhile_length_le _ pts
  have htw_sum : (pfx.map List.length).sum ≤ (pts.map List.length).sum :=
    takeWhile_map_sum_le _ List.length pts
  exact hfm.mono (by omega) (by omega) (by omega) htw_sum

/-- Allocation-phase `PhaseCreditSpec` for `<PolyDecoder>::from_pb`. -/
theorem decoderFromPbAlloc_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pb : ProtoPolynomialDecoder) :
    let P := (pb.pts.map List.length).sum
    PhaseCreditSpec M (FromPbDecAllocEnv pb)
      (2 * P + 152624) (P + 131120) (P + 131120) P := by
  dsimp only
  have h1 : PhaseCreditSpec M
      (fun evs => pb.pts.length = 16 ∧ evs = fromPbDecLoopAllocEvents pb.pts)
      (2 * (pb.pts.map List.length).sum + 152624)
      ((pb.pts.map List.length).sum + 131120)
      ((pb.pts.map List.length).sum + 131120)
      (pb.pts.map List.length).sum := by
    by_cases h16 : pb.pts.length = 16
    · exact (fromPbDecLoop_phaseCreditSpec hM h16).of_imp fun _ ⟨_, heq⟩ => heq
    · exact ((PhaseCreditSpec.empty M).of_imp fun _ ⟨h, _⟩ => h16 h).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  exact ((PhaseCreditSpec.nil M).or h1).congr_mono (fun _ h => h)
    (by omega) (by omega) (by omega) (by omega)

theorem decoderFromPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pb : ProtoPolynomialDecoder) :
    let P := (pb.pts.map List.length).sum
    PhaseCreditSpec M (FromPbDecEnv pb)
      (2 * P + 152624) (P + 131120) (P + 131120) P :=
  concat_freeOnly_phaseCreditSpec hM
    (fun _ ⟨ea, ef, heq, ha, hf⟩ => ⟨ea, ef, heq, ha, hf⟩)
    (decoderFromPbAlloc_phaseCreditSpec hM pb)

/-- Allocation-phase `PhaseCreditSpec` for `<PolyDecoder>::into_pb`. -/
theorem decoderIntoPbAlloc_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (dec : PolyDecoder) :
    let P := (dec.pts.map (fun s => s.vec.length)).sum
    let N := dec.pts.length
    PhaseCreditSpec M (DecoderIntoPbAllocEnv dec)
      (8 * P + N * 9539 + 10307)
      (4 * P + N * 8195 + 8579)
      (4 * P + N * 8195 + 8579)
      (max 384 (4 * P)) := by
  dsimp only
  have h384 := PhaseCreditSpec.rustAlloc_aff hM (req := 384) (al := 8) (by decide)
  have hslot : ∀ s ∈ dec.pts,
      PhaseCreditSpec M (· = decoderIntoPbSlotEvents s.vec)
        (8 * s.vec.length + 9539) (4 * s.vec.length + 8195)
        (4 * s.vec.length + 8195) (4 * s.vec.length) := by
    intro s _
    exact (optRustAlloc_aff hM s.vec.isEmpty (4 * s.vec.length) 1 (by decide)).mono
      (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have hslots := flatMap_phaseCreditSpec (fun s => decoderIntoPbSlotEvents s.vec)
    (fun s => 8 * s.vec.length + 9539) (fun s => 4 * s.vec.length + 8195)
    (fun s => 4 * s.vec.length) dec.pts hslot
  have hc_eq := sum_map_aff (fun s => s.vec.length) 8 9539 dec.pts
  have hl_eq := sum_map_aff (fun s => s.vec.length) 4 8195 dec.pts
  have hr_eq := sum_map_mul (fun s => s.vec.length) 4 dec.pts
  have hcat := h384.concat hslots
  refine (hcat.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (by omega)
  rw [h]
  exact ⟨rustAllocEvents 384 8, dec.pts.flatMap (fun s => decoderIntoPbSlotEvents s.vec),
    rfl, rfl, rfl⟩

theorem decoderIntoPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (dec : PolyDecoder) :
    let P := (dec.pts.map (fun s => s.vec.length)).sum
    let N := dec.pts.length
    PhaseCreditSpec M (DecoderIntoPbEnv dec)
      (8 * P + N * 9539 + 10307)
      (4 * P + N * 8195 + 8579)
      (4 * P + N * 8195 + 8579)
      (max 384 (4 * P)) :=
  concat_freeOnly_phaseCreditSpec hM
    (fun _ ⟨ea, ef, heq, ha, hf⟩ => ⟨ea, ef, heq, ha, hf⟩)
    (decoderIntoPbAlloc_phaseCreditSpec hM dec)

/-! ## `<Chain>::into_pb`, `spqr::chain_from_version_negotiation`, and `spqr::chain_from` -/

/-- `PhaseCreditSpec` for `<Chain>::into_pb`. -/
theorem chainIntoPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : ChainIntoPbCall) :
    let B := x.chain.links.length * 112
    PhaseCreditSpec M (ChainIntoPbEnv x)
      (2 * B + 9539) (B + 8195) (B + 8195) B := by
  dsimp only
  unfold ChainIntoPbEnv
  split
  · exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · have halloc := PhaseCreditSpec.rustAlloc_aff hM
      (req := x.chain.links.length * 112) (al := 8) (by decide)
    refine concat_freeOnly_phaseCreditSpec hM (fun _ ⟨ef, hf, heq⟩ => ?_) halloc
    exact ⟨rustAllocEvents (x.chain.links.length * 112) 8, ef, heq, rfl, hf⟩

private theorem chainNewEvents_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (· = chainNewEvents) 58610 49858 49858 448 := by
  have h72 := PhaseCreditSpec.rustAlloc_aff hM (req := 72) (al := 1) (by decide)
  have h32 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
  have h448 := PhaseCreditSpec.rustAlloc_aff hM (req := 448) (al := 8) (by decide)
  have hcat := ((((h72.concat h32).concat h72).concat h32).concat h448).concat h32
  refine (hcat.of_imp fun _ h => ?_).mono (by omega) (by omega) (by omega) (by omega)
  rw [h]
  unfold chainNewEvents
  refine ⟨_, rustAllocEvents 32 1, rfl, ?_, rfl⟩
  refine ⟨_, rustAllocEvents 448 8, rfl, ?_, rfl⟩
  refine ⟨_, rustAllocEvents 32 1, rfl, ?_, rfl⟩
  refine ⟨_, rustAllocEvents 72 1, rfl, ?_, rfl⟩
  exact ⟨rustAllocEvents 72 1, rustAllocEvents 32 1, rfl, rfl, rfl⟩

/-- `PhaseCreditSpec` for `spqr::chain_from_version_negotiation`. -/
theorem chainFromVN_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (v : VersionNegotiationPB) :
    PhaseCreditSpec M (ChainFromVersionNegotiationEnv v) 58610 49858 49858 448 := by
  unfold ChainFromVersionNegotiationEnv
  split
  · exact chainNewEvents_phaseCreditSpec hM
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-- `PhaseCreditSpec` for `spqr::chain_from`. -/
theorem chainFrom_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pb : Option ChainPB) (vn : Option VersionNegotiationPB) :
    PhaseCreditSpec M (ChainFromEnv pb vn) 58610 49858 49858 448 := by
  cases pb with
  | some _ =>
    exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | none =>
    cases vn with
    | some v => exact chainFromVN_phaseCreditSpec hM v
    | none =>
      exact (PhaseCreditSpec.nil M).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-! ## `<PolyEncoder>::encode_bytes`, `hkdf_to_vec`, and `<Poly>::lagrange_interpolate_prepare` -/

/-- `PhaseCreditSpec` for `<PolyEncoder>::encode_bytes`. -/
theorem encodeBytes_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (msgLen : Nat) :
    PhaseCreditSpec M (EncodeBytesEnv msgLen)
      (16 * (2 * msgLen + 9539))
      (16 * (msgLen + 8195))
      (16 * (msgLen + 8195))
      msgLen := by
  unfold EncodeBytesEnv encodeBytesAllocEvents
  split
  · have hmsg := PhaseCreditSpec.rustAlloc_aff hM (req := msgLen) (al := 2) (by decide)
    exact replicate_flatten_phaseCreditSpec 16 (rustAllocEvents msgLen 2) hmsg
  · exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

/-- `PhaseCreditSpec` for `spqr::kdf::hkdf_to_vec`. -/
theorem hkdfToVec_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (okmLen : Nat) :
    PhaseCreditSpec M (HkdfToVecEnv okmLen)
      (2 * okmLen + 9539) (okmLen + 8195) (okmLen + 8195) okmLen :=
  PhaseCreditSpec.rustAlloc_aff hM (req := okmLen) (al := 1) (by decide)

/-- `PhaseCreditSpec` for `<Poly>::lagrange_interpolate_prepare`. -/
theorem lagrangePrepare_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (a : LagrangePrepareArgs) :
    let B := 2 * (a.pts.length + 1)
    PhaseCreditSpec M (LagrangePrepareEnv a)
      (2 * B + 9539) (B + 8195) (B + 8195) B :=
  PhaseCreditSpec.rustAlloc_aff hM (req := 2 * (a.pts.length + 1)) (al := 2) (by decide)

end LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit
