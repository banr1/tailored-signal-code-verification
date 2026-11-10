/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6e
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6f
import ProofLib.SepLogic.WPp

/-!
# Budget Envelopes and Low-Stack Helpers for Placed Variant 6 (`HeaderReceived`)

Defines the Variant 6 (`InnerState.headerReceived`, `+1464`, Block `333`) allocator event envelopes
(`HeaderReceivedFromPbAllocEnv`, `HeaderReceivedFromPbEnv`), proves `StatesFromPbEnv` subsumption,
and lifts the `v6hr_lowStack_*` header-load and early-error helpers to `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsProg_333 lsmpl sepWP_seq_lscl)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator ProtoPolynomialDecoder V1State pbToProtoPolyDecoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v6hr_Regs1508 v6hr_Saved10324Preserved
   v6hr_headersAt v6hr_lowStackAt v6hr_lowStackGaps)
open CryptoVerification.SpqrV1.Top.StateSize
  (length_le_encodeMessage length_le_encodeOptMessage optRaw
   rawAuth rawUcHeaderReceived rawUcHeaderReceived_le_encodeRaw
   sum_length_le_encodeRepeatedBytes)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget (authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv fromPbDecAllocEnv_imp_fromPbDecEnv
   fromPbDecLoopAllocEvents fromPbDecSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (spqrBoundedEvs_authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlacedBudget
  (v6hr_load_headers_1464_none_to_3760_placed_budget
   v6hr_load_headers_1464_some_eq_to_3760_placed_budget
   v6hr_load_headers_1464_some_ne_to_1520_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6bPlacedBudget
  (v6hr_err_1520_auth_none_to_10324_of_placedHooks
   v6hr_err_1520_auth_none_to_10324_placed
   v6hr_err_1520_auth_some_to_10324_of_placedHooks
   v6hr_err_1520_auth_some_to_10324_placed
   v6hr_err_1520_uc_none_to_10324_placed_budget
   v6hr_err_3760_auth_none_to_10316_of_placedHooks
   v6hr_err_3760_auth_none_to_10316_placed
   v6hr_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks
   v6hr_err_3760_hdr_ne64_auth_some_to_10316_placed
   v6hr_err_3760_uc_none_to_10316_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6fPlacedBudget (V6hrAuthCloneEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-! ## 1. Allocation & Full Event Envelopes and `StatesFromPbEnv` Subsumption -/

/-- Precondition allocation envelope of Variant 6 (`HeaderReceived`, `+1464`, Block `333`) of
    `<spqr::v1::chunked::states::States>::from_pb`:
    - `[]` on early error branches (`uc = none`, `auth = none`, `hdr.length ≠ 64`, or
      `receivingEk = some decPb` with `decPb.ptsNeeded ≠ 576#32`);
    - `authKeyCloneEvents rootKey ++ authKeyCloneEvents macKey` when `receivingEk = none`,
      `uc = some { auth := some authPb, hdr := hdr, .. }`, and `hdr.length = 64`;
    - `V6hrAuthCloneEnv rootKey macKey` followed by `FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)`
      when `receivingEk = some decPb`, `uc = some { auth := some authPb, hdr := hdr, .. }`,
      `decPb.ptsNeeded = 576#32`, and `hdr.length = 64`. -/
def HeaderReceivedFromPbAllocEnv (s : V1State.Chunked.HeaderReceived)
    (evs : List AllocEvent) : Prop :=
  match s.receivingEk, s.uc with
  | none, some uc =>
    match uc.auth with
    | some authPb =>
      if uc.hdr.length = 64 then
        evs = authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey
      else evs = []
    | none => evs = []
  | some decPb, some uc =>
    match uc.auth with
    | some authPb =>
      if decPb.ptsNeeded = 576#32 ∧ uc.hdr.length = 64 then
        ∃ evs1 evs2, evs = evs1 ++ evs2 ∧
          V6hrAuthCloneEnv authPb.rootKey authPb.macKey evs1 ∧
          FromPbDecAllocEnv (pbToProtoPolyDecoder decPb) evs2
      else evs = []
    | none => evs = []
  | _, none => evs = []

/-- Complete postcondition event envelope of Variant 6 (`HeaderReceived`, `+1464`, Block `333`) of
    `<spqr::v1::chunked::states::States>::from_pb`, including trailing `FreeOnlyEvs` drops of the
    input `V1State` buffers and any cloned buffers freed on error. -/
def HeaderReceivedFromPbEnv (s : V1State.Chunked.HeaderReceived)
    (evs : List AllocEvent) : Prop :=
  match s.receivingEk, s.uc with
  | none, none => evs = []
  | none, some uc =>
    match uc.auth with
    | none => FreeOnlyEvs evs
    | some authPb =>
      if uc.hdr.length = 64 then
        V6hrAuthCloneEnv authPb.rootKey authPb.macKey evs
      else FreeOnlyEvs evs
  | some decPb, some uc =>
    match uc.auth with
    | some authPb =>
      if decPb.ptsNeeded = 576#32 ∧ uc.hdr.length = 64 then
        ∃ evs1 evs2, evs = evs1 ++ evs2 ∧
          V6hrAuthCloneEnv authPb.rootKey authPb.macKey evs1 ∧
          FromPbDecEnv (pbToProtoPolyDecoder decPb) evs2
      else FreeOnlyEvs evs
    | none => FreeOnlyEvs evs
  | some _, none => FreeOnlyEvs evs

theorem v6hrAuthCloneEnv_append_freeOnly {rootKey macKey : List (BitVec 8)}
    {evs1 evs2 : List AllocEvent}
    (h1 : V6hrAuthCloneEnv rootKey macKey evs1) (h2 : FreeOnlyEvs evs2) :
    V6hrAuthCloneEnv rootKey macKey (evs1 ++ evs2) := by
  rcases h1 with ⟨ef, hf, rfl⟩
  exact ⟨ef ++ evs2, hf.append h2, by simp [List.append_assoc]⟩

theorem fitsEnv_alloc_of_headerReceivedEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : V1State.Chunked.HeaderReceived}
    (h : FitsEnv M lim st (HeaderReceivedFromPbEnv s)) :
    FitsEnv M lim st (HeaderReceivedFromPbAllocEnv s) := by
  intro evs hevs
  rcases s with ⟨uc, receivingEk⟩
  cases receivingEk with
  | none =>
    cases uc with
    | none => exact h evs hevs
    | some ucVal =>
      rcases ucVal with ⟨ep, authOpt, hdr⟩
      cases authOpt with
      | none =>
        subst hevs
        exact h [] FreeOnlyEvs.nil
      | some authPb =>
        dsimp only [HeaderReceivedFromPbAllocEnv] at hevs
        by_cases hlen : hdr.length = 64
        · simp only [hlen, ↓reduceIte] at hevs
          subst hevs
          apply h
          simp only [HeaderReceivedFromPbEnv, hlen, ↓reduceIte]
          exact ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩
        · simp only [hlen, ↓reduceIte] at hevs
          subst hevs
          apply h
          simp only [HeaderReceivedFromPbEnv, hlen, ↓reduceIte]
          exact FreeOnlyEvs.nil
  | some decPb =>
    cases uc with
    | none =>
      subst hevs
      exact h [] FreeOnlyEvs.nil
    | some ucVal =>
      rcases ucVal with ⟨ep, authOpt, hdr⟩
      cases authOpt with
      | none =>
        subst hevs
        exact h [] FreeOnlyEvs.nil
      | some authPb =>
        dsimp only [HeaderReceivedFromPbAllocEnv] at hevs
        by_cases hcond : decPb.ptsNeeded = 576#32 ∧ hdr.length = 64
        · simp only [hcond, ↓reduceIte] at hevs
          rcases hevs with ⟨evs1, evs2, rfl, hevs1, hevs2⟩
          apply h
          simp only [HeaderReceivedFromPbEnv, hcond, ↓reduceIte]
          exact ⟨evs1, evs2, rfl, hevs1, fromPbDecAllocEnv_imp_fromPbDecEnv hevs2⟩
        · simp only [hcond, ↓reduceIte] at hevs
          subst hevs
          apply h
          simp only [HeaderReceivedFromPbEnv, hcond, ↓reduceIte]
          exact FreeOnlyEvs.nil

theorem fitsEvents_authClone_of_allocEnv_dec_none
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ep : BitVec 64} {authPb : ProtoAuthenticator} {hdr : List (BitVec 8)}
    (hfits : FitsEnv M lim st
      (HeaderReceivedFromPbAllocEnv
        { uc := some { epoch := ep, auth := some authPb, hdr := hdr }, receivingEk := none }))
    (hlen : hdr.length = 64) :
    FitsEvents M lim st (authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey) := by
  apply hfits
  simp [HeaderReceivedFromPbAllocEnv, hlen]

theorem fitsEvents_authClone_of_allocEnv_dec_some
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ep : BitVec 64} {authPb : ProtoAuthenticator} {hdr : List (BitVec 8)}
    {decPb : PolynomialDecoder}
    (hfits : FitsEnv M lim st
      (HeaderReceivedFromPbAllocEnv
        { uc := some { epoch := ep, auth := some authPb, hdr := hdr },
          receivingEk := some decPb }))
    (heq_pts : decPb.ptsNeeded = 576#32) (hlen : hdr.length = 64) :
    FitsEvents M lim st (authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey) := by
  apply hfits
  simp only [HeaderReceivedFromPbAllocEnv, heq_pts, hlen, and_self, ↓reduceIte]
  exact ⟨authKeyCloneEvents authPb.rootKey ++ authKeyCloneEvents authPb.macKey, [],
    (List.append_nil _).symm,
    ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩,
    Or.inl rfl⟩

theorem fitsEnv_decAlloc_of_allocEnv_dec_some
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ep : BitVec 64} {authPb : ProtoAuthenticator} {hdr : List (BitVec 8)}
    {decPb : PolynomialDecoder} {evs1 : List AllocEvent}
    (hfits : FitsEnv M lim st
      (HeaderReceivedFromPbAllocEnv
        { uc := some { epoch := ep, auth := some authPb, hdr := hdr },
          receivingEk := some decPb }))
    (heq_pts : decPb.ptsNeeded = 576#32) (hlen : hdr.length = 64)
    (hevs1 : V6hrAuthCloneEnv authPb.rootKey authPb.macKey evs1) :
    FitsEnv M lim (M.stepEvents evs1 st) (FromPbDecAllocEnv (pbToProtoPolyDecoder decPb)) := by
  intro evs2 hevs2
  have h12 : FitsEvents M lim st (evs1 ++ evs2) := by
    apply hfits
    simp only [HeaderReceivedFromPbAllocEnv, heq_pts, hlen, and_self, ↓reduceIte]
    exact ⟨evs1, evs2, rfl, hevs1, hevs2⟩
  exact ((fitsEvents_append M lim evs1 evs2 st).mp h12).2

private theorem rawAuth_le_headerReceived_encodeRaw
    (ep : BitVec 64) (auth : ProtoAuthenticator) (hdr : List (BitVec 8))
    (decOpt : Option PolynomialDecoder) :
    auth.rootKey.length + auth.macKey.length ≤
      (V1State.encodeRaw
        { innerState := some (.headerReceived
            { uc := some { epoch := ep, auth := some auth, hdr := hdr },
              receivingEk := decOpt }) }).length := by
  let s : V1State.Chunked.HeaderReceived :=
    { uc := some { epoch := ep, auth := some auth, hdr := hdr }, receivingEk := decOpt }
  have h0 := length_le_encodeMessage V1State.Chunked.HeaderReceived.encodeRaw 7#32 s
  have h1 := length_le_encodeOptMessage _ rawUcHeaderReceived rawUcHeaderReceived_le_encodeRaw 1#32 s.uc
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.HeaderReceived.encodeRaw, rawUcHeaderReceived, optRaw, rawAuth, s] at h0 h1 ⊢
  rw [List.length_append] at h0
  omega

private theorem sum_pts_le_headerReceived_encodeRaw
    (ucOpt : Option V1State.Unchunked.HeaderReceived) (decPb : PolynomialDecoder) :
    (decPb.pts.map List.length).sum ≤
      (V1State.encodeRaw
        { innerState := some (.headerReceived { uc := ucOpt, receivingEk := some decPb }) }).length := by
  let s : V1State.Chunked.HeaderReceived := { uc := ucOpt, receivingEk := some decPb }
  have h0 := length_le_encodeMessage V1State.Chunked.HeaderReceived.encodeRaw 7#32 s
  have hmsg := length_le_encodeMessage PolynomialDecoder.encodeRaw 2#32 decPb
  have hpts := sum_length_le_encodeRepeatedBytes 3#32 decPb.pts
  have hdec : (decPb.pts.map List.length).sum ≤ (PolynomialDecoder.encodeRaw decPb).length := by
    unfold PolynomialDecoder.encodeRaw
    simp only [List.length_append]
    omega
  dsimp only [V1State.encodeRaw, V1State.InnerState.encode,
    V1State.Chunked.HeaderReceived.encodeRaw,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, s] at h0 ⊢
  rw [List.length_append] at h0
  omega

private theorem spqrBoundedEvs_v6hrAuthCloneEnv
    {rootKey macKey : List (BitVec 8)} {M_sz : Nat}
    (hrk : rootKey.length ≤ M_sz) (hmk : macKey.length ≤ M_sz)
    (hmax : M_sz ≤ MallocngMaxAllocSize)
    {evs : List AllocEvent} (hevs : V6hrAuthCloneEnv rootKey macKey evs) :
    SpqrBoundedEvs 2 M_sz evs := by
  rcases hevs with ⟨ef, hf, rfl⟩
  have h1 : SpqrBoundedEvs 1 rootKey.length (authKeyCloneEvents rootKey) :=
    spqrBoundedEvs_authKeyCloneEvents (Nat.le_trans hrk hmax)
  have h2 : SpqrBoundedEvs 1 macKey.length (authKeyCloneEvents macKey) :=
    spqrBoundedEvs_authKeyCloneEvents (Nat.le_trans hmk hmax)
  have h12 := SpqrBoundedEvs.append h1 h2
  have h12f := SpqrBoundedEvs.append h12 (SpqrBoundedEvs.of_freeOnly hf)
  exact SpqrBoundedEvs.mono (by decide) (by omega) h12f

private theorem spqrBoundedEvs_fromPbDecSlotEvents {bs : List (BitVec 8)} {M_sz : Nat}
    (hmod : (bs.length % 4 == 0) = true)
    (hle : bs.length ≤ M_sz) (hmax : M_sz ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 M_sz (fromPbDecSlotEvents bs) := by
  unfold fromPbDecSlotEvents
  split
  · exact SpqrBoundedEvs.nil 1 M_sz
  · rename_i hne
    have hmod' : bs.length % 4 = 0 := beq_iff_eq.mp hmod
    have hpos : 1 ≤ bs.length := by
      cases bs with
      | nil => simp at hne
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have hge2 : 2 ≤ bs.length := by omega
    have hre : rustAllocEvents bs.length 2 = [.alloc bs.length] := by
      simp [rustAllocEvents, hge2]
    rw [hre]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_trans hle hmax, hle, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem spqrBoundedEvs_fromPbDecLoopAllocEvents
    (pts : List (List (BitVec 8))) (M_sz : Nat)
    (hle : (pts.map List.length).sum ≤ M_sz) (hmax : M_sz ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs pts.length M_sz (fromPbDecLoopAllocEvents pts) := by
  unfold fromPbDecLoopAllocEvents
  induction pts with
  | nil =>
    simpa [List.takeWhile] using SpqrBoundedEvs.nil 0 M_sz
  | cons bs tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hle ⊢
    simp only [List.takeWhile]
    split
    · rename_i hmod
      simp only [List.flatMap_cons]
      have hbs : SpqrBoundedEvs 1 M_sz (fromPbDecSlotEvents bs) :=
        spqrBoundedEvs_fromPbDecSlotEvents hmod (by omega) hmax
      have htl : SpqrBoundedEvs tl.length M_sz
          ((List.takeWhile (fun x => x.length % 4 == 0) tl).flatMap fromPbDecSlotEvents) :=
        ih (by omega)
      have happ := SpqrBoundedEvs.append hbs htl
      exact SpqrBoundedEvs.mono (by omega) (by omega) happ
    · simpa using SpqrBoundedEvs.nil (tl.length + 1) M_sz

private theorem spqrBoundedEvs_fromPbDecEnv {pb : ProtoPolynomialDecoder} {M_sz : Nat}
    (hle : (pb.pts.map List.length).sum ≤ M_sz) (hmax : M_sz ≤ MallocngMaxAllocSize)
    {evs : List AllocEvent} (hevs : FromPbDecEnv pb evs) :
    SpqrBoundedEvs 16 M_sz evs := by
  rcases hevs with ⟨ea, ef, rfl, ha, hf⟩
  have hba : SpqrBoundedEvs 16 M_sz ea := by
    rcases ha with rfl | ⟨hlen16, rfl⟩
    · exact SpqrBoundedEvs.nil 16 M_sz
    · have hloop := spqrBoundedEvs_fromPbDecLoopAllocEvents pb.pts M_sz hle hmax
      rwa [hlen16] at hloop
  have hall := SpqrBoundedEvs.append hba (SpqrBoundedEvs.of_freeOnly hf)
  exact SpqrBoundedEvs.mono (by decide) (by omega) hall

private theorem encodeRaw_le_maxAlloc_of_fitsStatesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.HeaderReceived)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.headerReceived s) })) :
    (V1State.encodeRaw { innerState := some (.headerReceived s) }).length ≤ MallocngMaxAllocSize := by
  let pb : V1State := { innerState := some (.headerReceived s) }
  let m := min (V1State.encodeRaw pb).length MallocngMaxAllocSize
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
  dsimp only [m, pb, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
  omega

theorem headerReceivedFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.HeaderReceived)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.headerReceived s) }))
    {evs : List AllocEvent} (hevs : HeaderReceivedFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.headerReceived s) } evs := by
  change SpqrBoundedEvs 128
    (4 * (V1State.encodeRaw { innerState := some (.headerReceived s) }).length + 4096) evs
  have hmax : (V1State.encodeRaw { innerState := some (.headerReceived s) }).length ≤
      MallocngMaxAllocSize :=
    encodeRaw_le_maxAlloc_of_fitsStatesFromPbEnv s hfits
  rcases s with ⟨uc, receivingEk⟩
  cases receivingEk with
  | none =>
    cases uc with
    | none =>
      subst hevs
      exact SpqrBoundedEvs.nil _ _
    | some ucVal =>
      rcases ucVal with ⟨ep, authOpt, hdr⟩
      cases authOpt with
      | none =>
        exact SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (SpqrBoundedEvs.of_freeOnly hevs)
      | some authPb =>
        dsimp only [HeaderReceivedFromPbEnv] at hevs
        by_cases hlen : hdr.length = 64
        · simp only [hlen, ↓reduceIte] at hevs
          have hauth := rawAuth_le_headerReceived_encodeRaw ep authPb hdr none
          have hb := spqrBoundedEvs_v6hrAuthCloneEnv
            (M_sz := (V1State.encodeRaw
              { innerState := some (.headerReceived
                  { uc := some { epoch := ep, auth := some authPb, hdr := hdr },
                    receivingEk := none }) }).length)
            (by omega) (by omega) hmax hevs
          exact SpqrBoundedEvs.mono (by decide) (by omega) hb
        · simp only [hlen, ↓reduceIte] at hevs
          exact SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (SpqrBoundedEvs.of_freeOnly hevs)
  | some decPb =>
    cases uc with
    | none =>
      exact SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (SpqrBoundedEvs.of_freeOnly hevs)
    | some ucVal =>
      rcases ucVal with ⟨ep, authOpt, hdr⟩
      cases authOpt with
      | none =>
        exact SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (SpqrBoundedEvs.of_freeOnly hevs)
      | some authPb =>
        dsimp only [HeaderReceivedFromPbEnv] at hevs
        by_cases hcond : decPb.ptsNeeded = 576#32 ∧ hdr.length = 64
        · simp only [hcond, ↓reduceIte] at hevs
          rcases hevs with ⟨evs1, evs2, rfl, hevs1, hevs2⟩
          have hauth := rawAuth_le_headerReceived_encodeRaw ep authPb hdr (some decPb)
          have hpts := sum_pts_le_headerReceived_encodeRaw
            (some { epoch := ep, auth := some authPb, hdr := hdr }) decPb
          have hb1 := spqrBoundedEvs_v6hrAuthCloneEnv
            (M_sz := (V1State.encodeRaw
              { innerState := some (.headerReceived
                  { uc := some { epoch := ep, auth := some authPb, hdr := hdr },
                    receivingEk := some decPb }) }).length)
            (by omega) (by omega) hmax hevs1
          have hb2 := spqrBoundedEvs_fromPbDecEnv (pb := pbToProtoPolyDecoder decPb)
            (M_sz := (V1State.encodeRaw
              { innerState := some (.headerReceived
                  { uc := some { epoch := ep, auth := some authPb, hdr := hdr },
                    receivingEk := some decPb }) }).length)
            hpts hmax hevs2
          have hb12 := SpqrBoundedEvs.append hb1 hb2
          exact SpqrBoundedEvs.mono (by decide) (by omega) hb12
        · simp only [hcond, ↓reduceIte] at hevs
          exact SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (SpqrBoundedEvs.of_freeOnly hevs)

theorem fitsEnv_alloc_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : V1State.Chunked.HeaderReceived)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.headerReceived s) })) :
    FitsEnv M lim st (HeaderReceivedFromPbAllocEnv s) := by
  refine fitsEnv_alloc_of_headerReceivedEnv fun evs hevs => ?_
  exact hfits evs (headerReceivedFromPbEnv_sub_statesFromPbEnv s hfits hevs)

/-! ## 2. `SepWP` Code-Loaded Bind Helper & Budget-Threaded `v6hr_lowStack_*` Theorems -/

/-- `SepWP` bind helper threading `LibsignalCodeLoaded lsmpl ·.mem` across an intermediate `mid`
    PC with spatial predicate `Pm`. -/
theorem v6hr_sepWP_bind_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q_mid : State → SepProp → Prop}
    {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P Q_mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_mid sm Pm →
      SepWP prog ret sm Pm Q) :
    SepWP prog ret s P Q :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpcm hrunm hQm hcl_m =>
    h2 sm Pm hpcm hrunm hcl_m hQm)

theorem v6hr_lowStack_load_headers_1464_none_to_3760_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w104 d112 d116 w120) := by
  unfold v6hr_lowStackAt
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_load_headers_1464_none_to_3760_placed_budget A lim st s0 s1 out pbA
        w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 d112 d116 w120 v232
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
      fun _ _ _ _ ⟨hPm, hvm, hregs⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hregs⟩)

theorem v6hr_lowStack_load_headers_1464_some_eq_to_3760_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 576#32 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 576#32 d116 w120) := by
  unfold v6hr_lowStackAt
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_load_headers_1464_some_eq_to_3760_placed_budget A lim st s0 s1 out pbA
        w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d116 w120 v232
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hw88 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
      fun _ _ _ _ ⟨hPm, hvm, hregs⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hregs⟩)

theorem v6hr_lowStack_load_headers_1464_some_ne_to_1520_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hd112 : (d112 == 576#32) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1520#64) s1
      (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) := by
  unfold v6hr_lowStackAt
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_load_headers_1464_some_ne_to_1520_placed_budget A lim st s0 s1 out pbA
        w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v232
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hw88 hd112 hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
      fun _ _ _ _ ⟨hPm, hvm, hregs⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hregs⟩)

theorem v6hr_lowStack_err_3760_uc_none_to_10316_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 w120 w96 ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 0#64 ∧
        sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_err_3760_uc_none_to_10316_placed_budget A lim st s0 s1 out
        w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 v224
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hpc1 hrun1 hregs1)
      fun _ _ _ _ ⟨hPm, hvm, hpres, hx23⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hpres, hx23⟩)

theorem v6hr_lowStack_err_3760_auth_none_to_10316_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp w24 v128 v136 (if (c0 == 0#64) = true then v144 else p0)
              d184 v192 d200 v208 v216 w120 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_err_3760_auth_none_to_10316_of_placedHooks hA st s0 s1 out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104
        d112 d116 w120 v80 v144 v224
        (((s0.sp - 2272#64) ↦₆₄ v128) ∗ ((s0.sp - 2264#64) ↦₆₄ v136) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨evs, hevs, hP, hx25, hpres, hx23⟩
  exact ⟨evs, hevs, Entails.trans hP (Entails.of_eq (by sep_ac_rfl)), hx25, hpres, hx23⟩

theorem v6hr_lowStack_err_3760_auth_none_to_10316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp w24 v128 v136 (if (c0 == 0#64) = true then v144 else p0)
              d184 v192 d200 v208 v216 w120 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_lowStack_err_3760_auth_none_to_10316_of_placedHooks hA.toPlacedBudget st
    s0 s1 out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 Rest
    hsp0_align hc0 hpc1 hrun1 hregs1

theorem v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hw24 : (w24 == 64#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp w24 v128 v136 (if (c0 == 0#64) = true then v144 else p0)
              d184 v192 d200 v208 v216 w120 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks hA st s0 s1
        out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104
        d112 d116 w120 v80 v144 v224
        (((s0.sp - 2272#64) ↦₆₄ v128) ∗ ((s0.sp - 2264#64) ↦₆₄ v136) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hc1 hw24 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨evs, hevs, hP, hx25, hpres, hx23⟩
  exact ⟨evs, hevs, Entails.trans hP (Entails.of_eq (by sep_ac_rfl)), hx25, hpres, hx23⟩

theorem v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hw24 : (w24 == 64#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3760#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10316#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp w24 v128 v136 (if (c0 == 0#64) = true then v144 else p0)
              d184 v192 d200 v208 v216 w120 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          (sm.readReg64 .x25).extractLsb' 0 8 = 0#8 ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 (sm.readReg64 .x25) ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_lowStack_err_3760_hdr_ne64_auth_some_to_10316_of_placedHooks hA.toPlacedBudget st
    s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 d112 d116 w120
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 Rest
    hsp0_align hc0 hc1 hw24 hpc1 hrun1 hregs1

theorem v6hr_lowStack_err_1520_uc_none_to_10324_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out noneCap w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10324#64) s1
      (v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
        sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_err_1520_uc_none_to_10324_placed_budget A lim st s0 s1 out
        w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hpc1 hrun1 hregs1)
      fun _ _ _ _ ⟨hPm, hvm, hpres, hx23⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hpres, hx23⟩)

theorem v6hr_lowStack_err_1520_auth_none_to_10324_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
          sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_err_1520_auth_none_to_10324_of_placedHooks hA st s0 s1
        out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨evs, hevs, hP, hpres, hx23⟩
  exact ⟨evs, hevs, Entails.trans hP (Entails.of_eq (by sep_ac_rfl)), hpres, hx23⟩

theorem v6hr_lowStack_err_1520_auth_none_to_10324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 noneCap w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_lowStack_err_1520_auth_none_to_10324_of_placedHooks hA.toPlacedBudget st
    s0 s1 out c0 p0 w24 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 Rest
    hsp0_align hc0 hpc1 hrun1 hregs1

theorem v6hr_lowStack_err_1520_auth_some_to_10324_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
          sm.readReg64 .x23 = w104) := by
  unfold v6hr_lowStackAt
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWP.mono
      (v6hr_err_1520_auth_some_to_10324_of_placedHooks hA st s0 s1
        out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 d112 d116 w120
        (((s0.sp - 2320#64) ↦₆₄ v80) ∗ ((s0.sp - 2272#64) ↦₆₄ v128) ∗
         ((s0.sp - 2264#64) ↦₆₄ v136) ∗ ((s0.sp - 2256#64) ↦₆₄ v144) ∗
         ((s0.sp - 2216#64) ↦₃₂ d184) ∗ ((s0.sp - 2208#64) ↦₆₄ v192) ∗
         ((s0.sp - 2200#64) ↦₃₂ d200) ∗ ((s0.sp - 2192#64) ↦₆₄ v208) ∗
         ((s0.sp - 2184#64) ↦₆₄ v216) ∗ ((s0.sp - 2176#64) ↦₆₄ v224) ∗
         v6hr_lowStackGaps s0.sp ∗ Rest)
        hsp0_align hc0 hc1 hpc1 hrun1 hregs1) ?_)
  intro sm Pm _ _ ⟨evs, hevs, hP, hpres, hx23⟩
  exact ⟨evs, hevs, Entails.trans hP (Entails.of_eq (by sep_ac_rfl)), hpres, hx23⟩

theorem v6hr_lowStack_err_1520_auth_some_to_10324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s1 : State) (out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc0 : c0.toNat < 2 ^ 63) (hc1 : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1520#64)
    (hrun1 : s1.status = .Running)
    (hregs1 : v6hr_Regs1508 s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w104 d112 d116 w120) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10324#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
        vecCapPtrDealloc A.repAlloc c0 p0 ∗ vecCapPtrDealloc A.repAlloc c1 p1 ∗
        vecCapPtrDealloc A.repAlloc c2 p2 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 w96 ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          v6hr_Saved10324Preserved s0 sm (s0.sp - 2400#64) out w96 w88 2#64 ∧
          sm.readReg64 .x23 = w104) :=
  v6hr_lowStack_err_1520_auth_some_to_10324_of_placedHooks hA.toPlacedBudget st
    s0 s1 out c0 p0 w24 c1 p1 w48 c2 p2 w72 w80 w88 w96 w104 d112 d116 w120
    v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 Rest
    hsp0_align hc0 hc1 hpc1 hrun1 hregs1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6PlacedBudgetAux
