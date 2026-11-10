/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget Envelopes and Tail Steps for `Variant8PlacedBudget`

Defines exact allocator event envelopes (`EkReceivedCt1SampledFromPbAllocEnv`,
`EkReceivedCt1SampledFromPbEnv`) with `StatesFromPbEnv` subsumption, and proves the budget-threaded
`Ok(enc)` staging (`+11264 -> +8180 -> s0.x30`) and `<PolyEncoder>::from_pb` call (`+10900 -> +10904`)
for Variant 8 (`InnerState.ekReceivedCt1Sampled`, Block `333`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap

open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (CIPHERTEXT1_SIZE ENCAPSULATION_KEY_SIZE ENCAPSULATION_STATE_SIZE PolyEncoder PolynomialEncoder ProtoAuthenticator ProtoPolynomialEncoder V1State pbToProtoPolyEncoder)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt polyEncoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack fromPbResult loByte unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved epilogueOutFull epilogueStackGaps epilogueStackSlots overlapWord7 resultChunkedStatesAt sp_sub_2400_align statesFromPbSavedCells statesFromPbStack v1_optProtoPolyEncoderAt_pack_some v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt v8_encCellsAt v8_epilogueOutFull_entails_ekReceivedCt1Sampled v8_fsp_176_184_cells_entails_16 v8_fsp_1888_entails_epilogue v8_fsp_64_72_entails_92 v8_fsp_96_100_entails_8 v8_fsp_split_11264_all v8_midQ128 v8_quadAt v8_stagingSlotsPost v8_stagingSlotsPre v8_wordAt)
open CryptoVerification.SpqrV1.Top.StateSize (length_le_encodeMessage length_le_encodeOptMessage optRaw rawAuth rawUcCt1SentEkReceived rawUcCt1SentEkReceived_le_encodeRaw sum_length_le_encodeRepeatedBytes)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget)

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbAllocEnv_imp_encoderFromPbEnv
   encoderFromPbPolysInitEvents encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents
   encoderFromPbPtsLoopEvents encoderFromPbPtsSlotEvents encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_epilogue_8180_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
  (spqrBoundedEvs_authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (blk333_noSvc0 v1_encoder_from_pb_ok_at_statesFromPb_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlacedBudget
  (v8_stage_11264_to_8180_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs nonFreeCount)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem lsmpl_base_333_eq [LibsignalPlacement] : lsmpl.base 333 = (blkPl_333).base := rfl

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  try rw [lsmpl_base_333_eq]
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

theorem seq_clean_lscl_st [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target_pc sm (P_mid sm) post) :
    SepWP prog target_pc s P post :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
      SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

/-! ## 1. Envelopes & `StatesFromPbEnv` Subsumption for Variant 8 (`EkReceivedCt1Sampled`) -/

/-- Exact binary length check on `V1State.Unchunked.Ct1SentEkReceived` (`es = 2080`,
    `ct1 = 960`, `ek = 1152`). -/
def ekReceivedCt1SampledUcLenOk (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived) : Bool :=
  u.es.length == ENCAPSULATION_STATE_SIZE &&
    u.ct1.length == CIPHERTEXT1_SIZE &&
    u.ek.length == ENCAPSULATION_KEY_SIZE

/-- Tail budget precondition at `+10836` after cloning `auth` and freeing the input `auth` buffers. -/
def EkReceivedCt1SampledTailFits (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (optEnc : Option PolynomialEncoder) : Prop :=
  match optEnc with
  | none => True
  | some pbEnc => FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc))

/-- Tail allocator event envelope emitted from `+10836` to return. -/
def EkReceivedCt1SampledTailEnv (optEnc : Option PolynomialEncoder)
    (evs : List AllocEvent) : Prop :=
  match optEnc with
  | none => FreeOnlyEvs evs
  | some pbEnc => EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs

/-- Precondition body event envelope for Variant 8 (`InnerState.ekReceivedCt1Sampled`) of
    `<States>::from_pb`: `[]` on early error paths (`uc = none`, length mismatch, `auth = none`),
    `authFromPbEvents auth` when `sendingCt1 = none`, and `authFromPbEvents auth` optionally
    followed by `FreeOnlyEvs` old-`auth` cleanup + `EncoderFromPbAllocEnv` when
    `sendingCt1 = some pbEnc`. -/
def EkReceivedCt1SampledFromPbAllocEnv (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => evs = []
  | some u =>
    if ekReceivedCt1SampledUcLenOk u then
      match u.auth with
      | none => evs = []
      | some auth =>
        match s.sendingCt1 with
        | none => evs = authFromPbEvents auth
        | some pbEnc =>
          evs = authFromPbEvents auth ∨
            ∃ evs_af evs_enc,
              FreeOnlyEvs evs_af ∧
              EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
              evs = (authFromPbEvents auth ++ evs_af) ++ evs_enc
    else evs = []

/-- Complete allocator event envelope for Variant 8 (`InnerState.ekReceivedCt1Sampled`) of
    `<States>::from_pb`, including `FreeOnlyEvs` drops of input/temporary buffers on all paths. -/
def EkReceivedCt1SampledFromPbEnv (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (evs : List AllocEvent) : Prop :=
  match s.uc with
  | none => FreeOnlyEvs evs
  | some u =>
    if ekReceivedCt1SampledUcLenOk u then
      match u.auth with
      | none => FreeOnlyEvs evs
      | some auth =>
        match s.sendingCt1 with
        | none => ∃ evs_free, FreeOnlyEvs evs_free ∧ evs = authFromPbEvents auth ++ evs_free
        | some pbEnc =>
          ∃ evs_af evs_enc,
            FreeOnlyEvs evs_af ∧
            EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs_enc ∧
            evs = authFromPbEvents auth ++ evs_af ++ evs_enc
    else FreeOnlyEvs evs

theorem freeOnlyEvs_append {xs ys : List AllocEvent}
    (hx : FreeOnlyEvs xs) (hy : FreeOnlyEvs ys) : FreeOnlyEvs (xs ++ ys) := by
  intro ev hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact hx ev h1
  · exact hy ev h2

theorem encoderFromPbEnv_append_freeOnly {pb : ProtoPolynomialEncoder}
    {evs₁ evs₂ : List AllocEvent}
    (h1 : EncoderFromPbEnv pb evs₁) (h2 : FreeOnlyEvs evs₂) :
    EncoderFromPbEnv pb (evs₁ ++ evs₂) := by
  rcases h1 with ⟨evs_alloc, evs_free, rfl, halloc, hfree⟩
  exact ⟨evs_alloc, evs_free ++ evs₂, List.append_assoc _ _ _, halloc, freeOnlyEvs_append hfree h2⟩

theorem ekReceivedCt1SampledAllocEnv_imp_env
    {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled} {evs : List AllocEvent}
    (h : EkReceivedCt1SampledFromPbAllocEnv s evs) :
    EkReceivedCt1SampledFromPbEnv s evs := by
  cases s with | mk uc sendingCt1 =>
  cases uc with
  | none => subst h; exact LibsignalBinary.Heap.FreeOnlyEvs.nil
  | some u =>
    unfold EkReceivedCt1SampledFromPbAllocEnv at h
    unfold EkReceivedCt1SampledFromPbEnv
    dsimp only [] at h ⊢
    cases hlen : ekReceivedCt1SampledUcLenOk u
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h ⊢
      subst h; exact LibsignalBinary.Heap.FreeOnlyEvs.nil
    · simp only [hlen, ↓reduceIte] at h ⊢
      cases hauth : u.auth with
      | none => simp only [hauth] at h ⊢; subst h; exact LibsignalBinary.Heap.FreeOnlyEvs.nil
      | some auth =>
        simp only [hauth] at h ⊢
        cases sendingCt1 with
        | none =>
          subst h; exact ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, (List.append_nil _).symm⟩
        | some pbEnc =>
          rcases h with rfl | ⟨evs_af, evs_enc, hfree_af, halloc_enc, rfl⟩
          · refine ⟨[], [], LibsignalBinary.Heap.FreeOnlyEvs.nil, ?_, by simp⟩
            exact encoderFromPbAllocEnv_imp_encoderFromPbEnv (Or.inl rfl)
          · exact ⟨evs_af, evs_enc, hfree_af,
              encoderFromPbAllocEnv_imp_encoderFromPbEnv halloc_enc, rfl⟩

theorem fitsEnv_alloc_of_ekReceivedCt1SampledEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled}
    (h : FitsEnv M lim st (EkReceivedCt1SampledFromPbEnv s)) :
    FitsEnv M lim st (EkReceivedCt1SampledFromPbAllocEnv s) :=
  fun _ hevs => h _ (ekReceivedCt1SampledAllocEnv_imp_env hevs)

theorem fitsEvents_auth_of_ekReceivedCt1SampledAllocEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived} {auth : ProtoAuthenticator}
    {sendingCt1 : Option PolynomialEncoder}
    (hlen : ekReceivedCt1SampledUcLenOk u = true)
    (hauth : u.auth = some auth)
    (hfits : FitsEnv M lim st
      (EkReceivedCt1SampledFromPbAllocEnv { uc := some u, sendingCt1 := sendingCt1 })) :
    FitsEvents M lim st (authFromPbEvents auth) := by
  apply hfits (authFromPbEvents auth)
  unfold EkReceivedCt1SampledFromPbAllocEnv
  simp only [hlen, ↓reduceIte, hauth]
  cases sendingCt1 with
  | none => trivial
  | some _ => exact Or.inl trivial

theorem tailFits_of_ekReceivedCt1SampledAllocEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived} {auth : ProtoAuthenticator}
    {sendingCt1 : Option PolynomialEncoder} {evs_af : List AllocEvent}
    (hlen : ekReceivedCt1SampledUcLenOk u = true)
    (hauth : u.auth = some auth)
    (hfree : FreeOnlyEvs evs_af)
    (hfits : FitsEnv M lim st
      (EkReceivedCt1SampledFromPbAllocEnv { uc := some u, sendingCt1 := sendingCt1 })) :
    EkReceivedCt1SampledTailFits M lim
      (M.stepEvents (authFromPbEvents auth ++ evs_af) st) sendingCt1 := by
  cases sendingCt1 with
  | none => trivial
  | some pbEnc =>
    intro evs_enc henc
    have hall : FitsEvents M lim st ((authFromPbEvents auth ++ evs_af) ++ evs_enc) := by
      apply hfits
      unfold EkReceivedCt1SampledFromPbAllocEnv
      simp only [hlen, ↓reduceIte, hauth]
      exact Or.inr ⟨evs_af, evs_enc, hfree, henc, rfl⟩
    rw [fitsEvents_append] at hall
    exact hall.2

theorem ekReceivedCt1SampledFromPbEnv_of_tailEnv
    {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived} {auth : ProtoAuthenticator}
    {sendingCt1 : Option PolynomialEncoder} {evs_af evs_tail : List AllocEvent}
    (hlen : ekReceivedCt1SampledUcLenOk u = true)
    (hauth : u.auth = some auth)
    (hfree : FreeOnlyEvs evs_af)
    (htail : EkReceivedCt1SampledTailEnv sendingCt1 evs_tail) :
    EkReceivedCt1SampledFromPbEnv { uc := some u, sendingCt1 := sendingCt1 }
      ((authFromPbEvents auth ++ evs_af) ++ evs_tail) := by
  unfold EkReceivedCt1SampledFromPbEnv
  simp only [hlen, ↓reduceIte, hauth]
  cases sendingCt1 with
  | none =>
    exact ⟨evs_af ++ evs_tail, freeOnlyEvs_append hfree htail, List.append_assoc _ _ _⟩
  | some pbEnc =>
    exact ⟨evs_af, evs_tail, hfree, htail, rfl⟩

private theorem mem_length_le_sum_map_length {bs : List (BitVec 8)}
    {vs : List (List (BitVec 8))} (h : bs ∈ vs) :
    bs.length ≤ (vs.map List.length).sum := by
  induction vs with
  | nil => nomatch h
  | cons v rest ih =>
    simp only [List.mem_cons, List.map_cons, List.sum_cons] at h ⊢
    rcases h with rfl | hrest
    · omega
    · have hle := ih hrest; omega

private theorem polyEncoder_pts_polys_sum_le_encodeRaw (pbEnc : PolynomialEncoder) :
    (pbEnc.pts.map List.length).sum + (pbEnc.polys.map List.length).sum ≤
      (CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw pbEnc).length := by
  unfold CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw
  simp only [List.length_append]
  have h1 := sum_length_le_encodeRepeatedBytes 2#32 pbEnc.pts
  have h2 := sum_length_le_encodeRepeatedBytes 3#32 pbEnc.polys
  omega

private theorem rawAuth_and_enc_le_ekReceivedCt1Sampled_encodeRaw
    (u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator)
    (sendingCt1 : Option PolynomialEncoder) (hauth : u.auth = some auth) :
    auth.rootKey.length + auth.macKey.length +
        (match sendingCt1 with
         | none => 0
         | some pbEnc => (pbEnc.pts.map List.length).sum + (pbEnc.polys.map List.length).sum) ≤
      (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw
        { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }).length := by
  have h0 := length_le_encodeMessage CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled.encodeRaw 9#32
    { uc := some u, sendingCt1 := sendingCt1 }
  have h1 := length_le_encodeOptMessage _ rawUcCt1SentEkReceived rawUcCt1SentEkReceived_le_encodeRaw
    1#32 (some u)
  have hu_auth : auth.rootKey.length + auth.macKey.length ≤ rawUcCt1SentEkReceived u := by
    unfold rawUcCt1SentEkReceived optRaw rawAuth
    simp only [hauth]
    omega
  cases sendingCt1 with
  | none =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw, CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode,
      CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled.encodeRaw, optRaw] at h0 h1 ⊢
    rw [List.length_append] at h0
    omega
  | some pbEnc =>
    have he1 := polyEncoder_pts_polys_sum_le_encodeRaw pbEnc
    have he2 := length_le_encodeMessage CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw 2#32 pbEnc
    dsimp only [CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw, CryptoVerification.LibsignalSpqrV1.V1State.InnerState.encode,
      CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled.encodeRaw, CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, optRaw] at h0 h1 ⊢
    rw [List.length_append] at h0
    omega

private theorem spqrBoundedEvs_rustAlloc2 {sz maxReq : Nat}
    (hge2 : 2 ≤ sz) (hmax : sz ≤ MallocngMaxAllocSize) (hreq : sz ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (rustAllocEvents sz 2) := by
  have hcond : (2 ≤ 16 ∧ 2 ≤ sz) := ⟨by decide, hge2⟩
  simp only [rustAllocEvents, hcond, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem freeOnlyEvs_rustDeallocEvents (sz al : Nat) :
    FreeOnlyEvs (rustDeallocEvents sz al) := by
  intro ev hev
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  exact ⟨al, sz, hev⟩

private theorem spqrBoundedEvs_flatMap_ptsSlots {maxReq : Nat} :
    ∀ (xss : List (List (BitVec 8))),
      (∀ bs ∈ xss, 2 * bs.length ≤ MallocngMaxAllocSize ∧ 2 * bs.length ≤ maxReq) →
      SpqrBoundedEvs xss.length maxReq (xss.flatMap encoderFromPbPtsSlotEvents)
  | [], _ => LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 0 maxReq
  | bs :: rest, h => by
    simp only [List.flatMap_cons, List.length_cons]
    have hbs := h bs List.mem_cons_self
    have hslot : SpqrBoundedEvs 1 maxReq (encoderFromPbPtsSlotEvents bs) := by
      unfold encoderFromPbPtsSlotEvents
      cases bs with
      | nil => exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 1 maxReq
      | cons _ tl =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        exact spqrBoundedEvs_rustAlloc2 (by simp only [List.length_cons]; omega) hbs.1 hbs.2
    have hrest := spqrBoundedEvs_flatMap_ptsSlots rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have happ := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hslot hrest
    simpa [Nat.add_comm 1 rest.length, Nat.max_self] using happ

private theorem spqrBoundedEvs_polysInitEvents {maxReq : Nat} (hreq : 2 ≤ maxReq) :
    SpqrBoundedEvs 16 maxReq encoderFromPbPolysInitEvents := by
  unfold encoderFromPbPolysInitEvents
  have h2 : rustAllocEvents 2 2 = [.alloc 2] := by simp [rustAllocEvents]
  rw [h2]
  have hrep : ∀ n : Nat, SpqrBoundedEvs n maxReq ((List.replicate n [LibsignalBinary.Heap.AllocEvent.alloc 2]).flatten) := by
    intro n
    induction n with
    | zero => exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 0 maxReq
    | succ k ih =>
      simp only [List.replicate_succ, List.flatten_cons]
      have h1 : SpqrBoundedEvs 1 maxReq [.alloc 2] :=
        ⟨by simp [nonFreeCount], fun ev hev => by
          simp only [List.mem_singleton] at hev; subst hev
          exact ⟨by decide, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩⟩
      simpa [Nat.add_comm 1 k, Nat.max_self] using LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append h1 ih
  exact hrep 16

private theorem spqrBoundedEvs_flatMap_polysSlots {maxReq : Nat} :
    ∀ (xss : List (List (BitVec 8))),
      (∀ bs ∈ xss, 2 ≤ bs.length ∧ bs.length ≤ MallocngMaxAllocSize ∧ bs.length ≤ maxReq) →
      SpqrBoundedEvs xss.length maxReq (xss.flatMap encoderFromPbPolysSlotEvents)
  | [], _ => LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.nil 0 maxReq
  | bs :: rest, h => by
    simp only [List.flatMap_cons, List.length_cons]
    obtain ⟨hge2, hmax, hreq⟩ := h bs List.mem_cons_self
    have hslot : SpqrBoundedEvs 1 maxReq (encoderFromPbPolysSlotEvents bs) := by
      unfold encoderFromPbPolysSlotEvents
      have ha := spqrBoundedEvs_rustAlloc2 hge2 hmax hreq
      have hd := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly (freeOnlyEvs_rustDeallocEvents 2 2)
      simpa using LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append ha hd
    have hrest := spqrBoundedEvs_flatMap_polysSlots rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simpa [Nat.add_comm 1 rest.length, Nat.max_self] using LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hslot hrest

private theorem takeWhile_length_le {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.takeWhile p).length ≤ l.length
  | [] => Nat.le_refl 0
  | _ :: xs => by
    unfold List.takeWhile
    split
    · simp only [List.length_cons]; exact Nat.succ_le_succ (takeWhile_length_le p xs)
    · exact Nat.zero_le _

private theorem mem_of_mem_takeWhile {α : Type} {p : α → Bool} {a : α} :
    ∀ {l : List α}, a ∈ l.takeWhile p → a ∈ l ∧ p a = true
  | [], h => nomatch h
  | x :: xs, h => by
    unfold List.takeWhile at h
    split at h
    · rename_i hpx
      simp only [List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact ⟨Or.inl rfl, hpx⟩
      · obtain ⟨hm, hp⟩ := mem_of_mem_takeWhile htl
        exact ⟨Or.inr hm, hp⟩
    · nomatch h

theorem spqrBoundedEvs_encoderFromPbEnv
    {pb : ProtoPolynomialEncoder} {maxReq : Nat} {evs : List AllocEvent}
    (hreq2 : 2 ≤ maxReq)
    (hpts : ∀ bs ∈ pb.pts, 2 * bs.length ≤ MallocngMaxAllocSize ∧ 2 * bs.length ≤ maxReq)
    (hpolys : ∀ bs ∈ pb.polys, bs.length ≤ MallocngMaxAllocSize ∧ bs.length ≤ maxReq)
    (henv : EncoderFromPbEnv pb evs) :
    SpqrBoundedEvs 32 maxReq evs := by
  rcases henv with ⟨evs_alloc, evs_free, rfl, halloc, hfree⟩
  have hbfree := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hfree
  rcases halloc with rfl | ⟨hpts_len, _, rfl⟩ | ⟨_, hpolys_len, rfl⟩
  · exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) hbfree
  · unfold encoderFromPbPtsLoopEvents
    have htw_len : (pb.pts.takeWhile (fun bs => bs.length % 2 == 0)).length ≤ 16 := by
      have hle := takeWhile_length_le (fun bs : List (BitVec 8) => bs.length % 2 == 0) pb.pts
      omega
    have hb_loop := spqrBoundedEvs_flatMap_ptsSlots
      (pb.pts.takeWhile (fun bs => bs.length % 2 == 0))
      (fun bs hbs => hpts bs (mem_of_mem_takeWhile hbs).1)
    have hb_all := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_loop hbfree
    exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega) hb_all
  · unfold encoderFromPbPolysLoopEvents
    have htw_len :
        (pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0))).length ≤ 16 := by
      have hle := takeWhile_length_le
        (fun bs : List (BitVec 8) => !bs.isEmpty && (bs.length % 2 == 0)) pb.polys
      omega
    have hb_init := spqrBoundedEvs_polysInitEvents hreq2
    have hb_loop := spqrBoundedEvs_flatMap_polysSlots
      (pb.polys.takeWhile (fun bs => !bs.isEmpty && (bs.length % 2 == 0)))
      (fun bs hbs => by
        obtain ⟨hmem, hpred⟩ := mem_of_mem_takeWhile hbs
        have hge2 : 2 ≤ bs.length := by
          cases bs with
          | nil => simp at hpred
          | cons _ tl =>
            cases tl with
            | nil => simp at hpred
            | cons _ _ => simp only [List.length_cons]; omega
        exact ⟨hge2, (hpolys bs hmem).1, (hpolys bs hmem).2⟩)
    have hb_body := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_init hb_loop
    have hb_all := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_body hbfree
    exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by omega) (by omega) hb_all

private theorem maxAlloc_of_fitsStatesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {inner : CryptoVerification.LibsignalSpqrV1.V1State.InnerState} {n : Nat}
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some inner }))
    (hle : n ≤ 4 * (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw { innerState := some inner }).length + 4096) :
    n ≤ MallocngMaxAllocSize := by
  let m := min n MallocngMaxAllocSize
  have hm_env : StatesFromPbEnv { innerState := some inner } [.alloc m] := by
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.min_le_right _ _, Nat.le_trans (Nat.min_le_left _ _) hle,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  have hm_fit : FitsEvents M lim st [.alloc m] := hfits [.alloc m] hm_env
  rcases hm_fit with ⟨⟨_, _, _, hva⟩, _⟩
  have hm_req : m ≤ M.stepReserve (.alloc m) st := M.req_le_stepReserve (.alloc m) st
  dsimp only [m, MMAP_MIN_ADDR, PAGE_SIZE, MallocngMaxAllocSize] at hva hm_req ⊢
  omega

theorem ekReceivedCt1SampledFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ekReceivedCt1Sampled s) }))
    {evs : List AllocEvent} (hevs : EkReceivedCt1SampledFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.ekReceivedCt1Sampled s) } evs := by
  let pb : V1State := { innerState := some (.ekReceivedCt1Sampled s) }
  let maxReq := 4 * (CryptoVerification.LibsignalSpqrV1.V1State.encodeRaw pb).length + 4096
  change SpqrBoundedEvs 128 maxReq evs
  cases s with | mk uc sendingCt1 =>
  cases uc with
  | none =>
    exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hevs)
  | some u =>
    unfold EkReceivedCt1SampledFromPbEnv at hevs
    dsimp only [] at hevs
    cases hlen : ekReceivedCt1SampledUcLenOk u
    · rw [hlen] at hevs; simp only [Bool.false_eq_true, ↓reduceIte] at hevs
      exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hevs)
    · rw [hlen] at hevs; simp only [↓reduceIte] at hevs
      cases hauth : u.auth with
      | none =>
        rw [hauth] at hevs
        exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (Nat.zero_le _) (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hevs)
      | some auth =>
        rw [hauth] at hevs
        have hwire := rawAuth_and_enc_le_ekReceivedCt1Sampled_encodeRaw u auth sendingCt1 hauth
        have hauth_max : auth.rootKey.length + auth.macKey.length ≤ MallocngMaxAllocSize :=
          maxAlloc_of_fitsStatesFromPbEnv hfits (by omega)
        have hb_r : SpqrBoundedEvs 1 auth.rootKey.length (authKeyCloneEvents auth.rootKey) :=
          spqrBoundedEvs_authKeyCloneEvents (by omega)
        have hb_m : SpqrBoundedEvs 1 auth.macKey.length (authKeyCloneEvents auth.macKey) :=
          spqrBoundedEvs_authKeyCloneEvents (by omega)
        have hb_auth : SpqrBoundedEvs 2 (max auth.rootKey.length auth.macKey.length)
            (authFromPbEvents auth) :=
          LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_r hb_m
        cases sendingCt1 with
        | none =>
          rcases hevs with ⟨evs_free, hfree, rfl⟩
          have hb_all := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_auth (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hfree)
          exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by try dsimp only [maxReq, pb]; omega) hb_all
        | some pbEnc =>
          dsimp only [] at hwire
          rcases hevs with ⟨evs_af, evs_enc, hfree_af, henc, rfl⟩
          have hb_enc : SpqrBoundedEvs 32 maxReq evs_enc := by
            refine spqrBoundedEvs_encoderFromPbEnv (by try dsimp only [maxReq]; omega) ?_ ?_ henc
            · intro bs hbs
              have hbs_sum : bs.length ≤ (pbEnc.pts.map List.length).sum :=
                mem_length_le_sum_map_length hbs
              have hreq : 2 * bs.length ≤ maxReq := by
                try dsimp only [maxReq, pb]
                omega
              exact ⟨maxAlloc_of_fitsStatesFromPbEnv hfits hreq, hreq⟩
            · intro bs hbs
              have hbs_sum : bs.length ≤ (pbEnc.polys.map List.length).sum :=
                mem_length_le_sum_map_length hbs
              have hreq : bs.length ≤ maxReq := by
                try dsimp only [maxReq, pb]
                omega
              exact ⟨maxAlloc_of_fitsStatesFromPbEnv hfits hreq, hreq⟩
          have hb_1 := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_auth (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.of_freeOnly hfree_af)
          have hb_2 := LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.append hb_1 hb_enc
          exact LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.SpqrBoundedEvs.mono (by decide) (by try dsimp only [maxReq, pb]; omega) hb_2

theorem fitsEnv_ekReceivedCt1SampledAlloc_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ekReceivedCt1Sampled s) })) :
    FitsEnv M lim st (EkReceivedCt1SampledFromPbAllocEnv s) :=
  fun evs hevs =>
    hfits evs (ekReceivedCt1SampledFromPbEnv_sub_statesFromPbEnv s hfits
      (ekReceivedCt1SampledAllocEnv_imp_env hevs))

/-! ## 2. Budget-Threaded `Ok(enc)` Staging + Epilogue (`+11264 -> +8180 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem v8_stage_11264_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State)
    (fsp out tag ep pa1 l1 pa2 l2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp)
    (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
        (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A.repAlloc (out + 8#64) enc)
    (rootKey macKey es ek ct1 : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length)
    (hl2 : l2 = BitVec.ofNat 64 macKey.length)
    (hes : es.length = 2080) (hek : ek.length = 1152) (hct1 : ct1.length = 960)
    (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 11264#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = pa5) (hx22 : s.readReg64 .x22 = l1)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((memRegion (fsp + 72#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
          memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648) ∗
        stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 120#64) ↦₆₄ ep) ∗
        memRegion (fsp + 128#64) 32 ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗
        ((fsp + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt (fsp + 1888#64) bs ∗
        ((fsp + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (fsp + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ P_heap ∗
        vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
        vecU8Payload A.repAlloc ca3 pa3 es ∗ vecU8Payload A.repAlloc ca4 pa4 ek ∗
        vecU8Payload A.repAlloc ca5 pa5 ct1 ∗ Frame ∗ A.pool lim st s)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (.ok (.ekReceivedCt1Sampled
              { uc := { auth := { rootKey := rootKey, macKey := macKey },
                        es := es, ek := ek, ct1 := ct1, epoch := ep },
                sending_ct1 := enc })) ∗
          stackAt s0.sp statesFromPbStack ∗ Frame ∗ A.pool lim st sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  refine SepWP.weaken_pre (sepConj_mono_left (v8_fsp_split_11264_all fsp)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun u887 => ProofLib.SepWP.exists_left fun u880 =>
    ProofLib.SepWP.exists_left fun u864 => ProofLib.SepWP.exists_left fun uq848 =>
    ProofLib.SepWP.exists_left fun u832 => ProofLib.SepWP.exists_left fun uq816 =>
    ProofLib.SepWP.exists_left fun uq800 => ProofLib.SepWP.exists_left fun uq784 =>
    ProofLib.SepWP.exists_left fun uq768 => ProofLib.SepWP.exists_left fun uq752 =>
    ProofLib.SepWP.exists_left fun uq736 => ProofLib.SepWP.exists_left fun uq720 =>
    ProofLib.SepWP.exists_left fun uq704 => ProofLib.SepWP.exists_left fun uq688 =>
    ProofLib.SepWP.exists_left fun uq672 => ProofLib.SepWP.exists_left fun uq656 =>
    ProofLib.SepWP.exists_left fun uq640 => ProofLib.SepWP.exists_left fun uq624 =>
    ProofLib.SepWP.exists_left fun uq608 => ProofLib.SepWP.exists_left fun w592 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun u232 => ProofLib.SepWP.exists_left fun u208 =>
    ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun u160 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d96 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have hstep := v8_stage_11264_to_8180_placed_budget A lim st (ext := ext)
    s0 s fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 (hi32 ++ enc.idx) bs
    d96 w104 w112 u160 d172 w192 u208 u232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816
    u832 uq848 u864 u880 u887
    (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      memRegion fsp 64 ∗ memRegion (fsp + 72#64) 20 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗
      memRegion (fsp + 100#64) 4 ∗ ((fsp + 120#64) ↦₆₄ ep) ∗ memRegion (fsp + 128#64) 32 ∗
      memRegion (fsp + 168#64) 4 ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 240#64) ↦ₛ bs240.val) ∗
      memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
      ((fsp + 592#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗
      memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993 ∗
      ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
      P_heap ∗ vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
      vecU8Payload A.repAlloc ca3 pa3 es ∗ vecU8Payload A.repAlloc ca4 pa4 ek ∗
      vecU8Payload A.repAlloc ca5 pa5 ct1 ∗ Frame)
    hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx26 hx28 htr
  refine SepWP.weaken_pre ?_ (SepWP.seq hstep ?_)
  · unfold v8_stagingSlotsPre; exact Entails.of_eq (by sep_ac_rfl)
  intro s2 P2 hpc2 hrun2 ⟨hP2, _hvm2, hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2,
    hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2,
    hx28_2, hx16_2, hx19_2, hx23_2, htr2⟩
  subst hfsp
  have h92 := v8_fsp_64_72_entails_92 (s0.sp - 2400#64) ca5
  have h96 := v8_fsp_96_100_entails_8 (s0.sp - 2400#64) ((loByte (v8_wordAt bs 104)).zeroExtend 32)
  have h176 := v8_fsp_176_184_cells_entails_16 (s0.sp - 2400#64) pa3 pa2
  have h200 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 200#64) pa1
  have h216 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 216#64) pa4
  have h1888 := v8_fsp_1888_entails_epilogue (s0.sp - 2400#64) tag (hi32 ++ enc.idx) bs hbs
  have hP2_ep : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        epilogueStackSlots (s0.sp - 2400#64) d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32)
          pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0) ca4 l2 bs240.val q576 w592
          (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
          (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
          (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328)
          (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376)
          (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144))
          (v8_wordAt bs 144 >>> 8)
          (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)
          (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗
        epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
        (P_heap ∗ vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
          vecU8Payload A.repAlloc ca3 pa3 es ∗ vecU8Payload A.repAlloc ca4 pa4 ek ∗
          vecU8Payload A.repAlloc ca5 pa5 ct1 ∗ Frame) ∗ A.pool lim st s2 := by
    refine Entails.trans hP2 ?_
    unfold v8_stagingSlotsPost epilogueStackSlots epilogueStackGaps
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 20) ∗
      ((((s0.sp - 2400#64) + 96#64) ↦₃₂ (loByte (v8_wordAt bs 104)).zeroExtend 32) ∗
        memRegion ((s0.sp - 2400#64) + 100#64) 4) ∗
      ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2)) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
        (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗ (((s0.sp - 2400#64) + 104#64) ↦₆₄ pa5) ∗
        (((s0.sp - 2400#64) + 112#64) ↦₆₄ 960#64) ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ ep) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ l2) ∗
        memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗
        (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte (v8_wordAt bs 128)).zeroExtend 32) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ 1152#64) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v8_wordAt bs 0) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ l2) ∗
        (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
        (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
        (((s0.sp - 2400#64) + 592#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 w592) ∗
        memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗
        (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v8_quadAt bs 152) ∗
        (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v8_quadAt bs 168) ∗
        (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v8_quadAt bs 184) ∗
        (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v8_quadAt bs 200) ∗
        (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v8_quadAt bs 216) ∗
        (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v8_quadAt bs 232) ∗
        (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v8_quadAt bs 248) ∗
        (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v8_quadAt bs 264) ∗
        (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v8_quadAt bs 280) ∗
        (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v8_quadAt bs 296) ∗
        (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v8_quadAt bs 312) ∗
        (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v8_quadAt bs 328) ∗
        (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v8_quadAt bs 344) ∗
        (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v8_quadAt bs 360) ∗
        (((s0.sp - 2400#64) + 832#64) ↦₆₄ v8_wordAt bs 376) ∗
        memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
        (((s0.sp - 2400#64) + 848#64) ↦₁₂₈
          v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) ∗
        (((s0.sp - 2400#64) + 864#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (v8_wordAt bs 144 >>> 8)) ∗
        memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗
        (((s0.sp - 2400#64) + 880#64) ↦₆₄
          unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
        (((s0.sp - 2400#64) + 888#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (v8_wordAt bs 112 >>> 8)) ∗
        memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
        vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
        vecU8Payload A.repAlloc ca3 pa3 es ∗ vecU8Payload A.repAlloc ca4 pa4 ek ∗
        vecU8Payload A.repAlloc ca5 pa5 ct1 ∗ Frame ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono h92 (sepConj_mono h96 (sepConj_mono h176
        (sepConj_mono h200 (sepConj_mono h216 (sepConj_mono_left h1888)))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hep := Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed A lim st hA.toPlacedBudget.memcpy_ok s0 s2 out
    d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32) pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0)
    ca4 l2 bs240.val bs240.property q576 w592
    (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
    (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
    (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328)
    (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376)
    (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144))
    (v8_wordAt bs 144 >>> 8)
    (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)
    (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
    (P_heap ∗ vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
      vecU8Payload A.repAlloc ca3 pa3 es ∗ vecU8Payload A.repAlloc ca4 pa4 ek ∗
      vecU8Payload A.repAlloc ca5 pa5 ct1 ∗ Frame)
    halign hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2,
      hx27_lo_2, hx27_mid_2, hx27_hi_2, hx4_2, hx5_2, hx21_2, hx7_2,
      hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2] at hep
  refine SepWP.weaken_pre hP2_ep (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, _hvm_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  have hout := v8_epilogueOutFull_entails_ekReceivedCt1Sampled A.repAlloc (F := F) out tag
    l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep bs hbs hi32 enc P_heap hreloc
    rootKey macKey es ek ct1 hl1 hl2 hes hek hct1
    (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property
    (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueOutFull out 10#64 tag (v8_wordAt bs 0) (v8_wordAt bs 8) (v8_wordAt bs 16)
      (v8_wordAt bs 24) (v8_wordAt bs 32) (v8_wordAt bs 40) (v8_wordAt bs 48) (v8_wordAt bs 56)
      (v8_wordAt bs 64) (v8_wordAt bs 72) ((v8_wordAt bs 80).extractLsb' 0 8)
      ((v8_wordAt bs 80).extractLsb' 8 32) ((v8_wordAt bs 80).extractLsb' 40 16)
      ((v8_wordAt bs 80).extractLsb' 56 8) (v8_wordAt bs 88) (v8_wordAt bs 96)
      (loByte (v8_wordAt bs 104)) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112)))
        (v8_wordAt bs 112 >>> 8))
      (v8_wordAt bs 120) (((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144))
      (overlapWord7
        ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64)
        (v8_wordAt bs 144 >>> 8))
      (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
      (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
      (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328)
      (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376) (hi32 ++ enc.idx)
      l1 pa1 l1 l2 pa2 l2 ca3 pa3 2080#64 ca4 pa4 1152#64 ca5 pa5 960#64 ep
      (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val
      (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗
     P_heap ∗ vecU8Payload A.repAlloc l1 pa1 rootKey ∗ vecU8Payload A.repAlloc l2 pa2 macKey ∗
     vecU8Payload A.repAlloc ca3 pa3 es ∗ vecU8Payload A.repAlloc ca4 pa4 ek ∗
     vecU8Payload A.repAlloc ca5 pa5 ct1) ∗
    stackAt s0.sp statesFromPbStack ∗ Frame ∗ A.pool lim st sf by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. Budget-Threaded `<PolyEncoder>::from_pb` Call (`+10900 -> +10904`) -/

private theorem v8_step_10900_to_374_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pa5 l1 u8 pbA l2 : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 10900#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5)
    (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 374) s (P ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 10904#64 ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa5 ∧
        sm.readReg64 .x22 = l1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = l2 ∧
        TraceCalleeSaved sm s0) := by
  rw [lsmpl_base_333_eq] at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 374) s (P ∗ A.pool lim st s) _
  wp_steps_sync_333 (lsmpl.base 374)
  try rw [lsmpl_base_333_eq]
  wp_done

/-- Total-correctness (`SepWP`) call `<PolyEncoder>::from_pb` at `+10900 -> +10904`
    (`bl lsmpl.base 374`, Block `333` calling Block `374`) under `RustCliAllocBudget M`. -/
theorem v8_call_encoder_from_pb_10900_to_10904_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hE : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp out pa5 l1 u8 pbA l2 : BitVec 64)
    (pbEnc : PolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (Frame : SepProp)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)))
    (hpts : ∀ bs ∈ (pbToProtoPolyEncoder pbEnc).pts, bs.length ≤ 2 * 0x0555555555555555)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 10900#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5)
    (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 10904#64) s
      (memRegion (fsp + 1888#64) 400 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt fsp encoderFromPbStack ∗ A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs ∧
          (Pf ⊢
            resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64)
              (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
            memRegion (fsp + 240#64) 56 ∗ stackAt fsp encoderFromPbStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame) ∧
          sf.sp = fsp ∧ sf.readReg64 .x19 = out ∧ sf.readReg64 .x21 = pa5 ∧
          sf.readReg64 .x22 = l1 ∧ sf.readReg64 .x23 = fsp + 848#64 ∧
          sf.readReg64 .x26 = u8 ∧ sf.readReg64 .x27 = pbA ∧
          sf.readReg64 .x28 = l2 ∧ TraceCalleeSaved sf s0) := by
  subst hfsp
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 halign (by decide)
  have hpre :
      memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st s ∗ Frame ⊢
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 240#64)
          (pbToProtoPolyEncoder pbEnc) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ Frame) ∗ A.pool lim st s := by
    dsimp only [polyEncoderSize]
    refine Entails.trans (Entails.of_eq (show _ =
      (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc))
          w0 w8 w16 w24 w32 w40 w48) ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ Frame ∗ A.pool lim st s) by sep_ac_rfl)) ?_
    exact Entails.trans
      (sepConj_mono_left
        (v1_optProtoPolyEncoderAt_pack_some A.repAlloc ((s0.sp - 2400#64) + 240#64)
          (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48))
      (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  have hsub := v1_encoder_from_pb_ok_at_statesFromPb_placed hE
  have hstep := v8_step_10900_to_374_placed_budget A lim st (ext := ext)
    s0 s (s0.sp - 2400#64) out pa5 l1 u8 pbA l2
    (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
      protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 240#64)
        (pbToProtoPolyEncoder pbEnc) ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ Frame)
    hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx26 hx27 hx28 htr
  refine seq_clean_lscl_st hcl
    (P_mid := fun sm =>
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 240#64)
          (pbToProtoPolyEncoder pbEnc) ∗
        A.pool lim st sm ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗ Frame)
    (SepWP.mono hstep fun sm Pm _ _ ⟨hPm, hregs⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hregs⟩)
    ?_
  intro sm hpc_m hrun_m hcl_m
    ⟨hsp_m, hlr_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m, hx26_m, hx27_m, hx28_m, htr_m⟩
  have hsp_align_m : sm.spAligned = true := by
    unfold State.spAligned; rw [hsp_m]; exact hfsp_align
  have hpre_ent :
      memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 240#64)
          (pbToProtoPolyEncoder pbEnc) ∗
        A.pool lim st sm ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ⊢
      (withLsCodeLoaded lsmpl (Poly.EncoderFromPb.DefsBudget.encoderFromPbSpec M A lim)).pre
        (CryptoVerification.SpqrV1.Poly.EncoderFromPb.EncoderFromPbGhost.mk ((s0.sp - 2400#64) + 1888#64) ((s0.sp - 2400#64) + 240#64)
          (pbToProtoPolyEncoder pbEnc), st) sm := by
    dsimp only [withLsCodeLoaded, Poly.EncoderFromPb.DefsBudget.encoderFromPbSpec]
    rw [hsp_m, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl sm.mem⌝]
    exact Entails.pure_right hcl_m
      (Entails.pure_right ⟨hx0_m, hx1_m, hpts, hfits,
        by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (sm.readReg64 .x30); rw [show sm.readReg64 .x30 = _ from hlr_m]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.call_subroutine_frame hsub
    (x := (CryptoVerification.SpqrV1.Poly.EncoderFromPb.EncoderFromPbGhost.mk ((s0.sp - 2400#64) + 1888#64) ((s0.sp - 2400#64) + 240#64)
      (pbToProtoPolyEncoder pbEnc), st))
    (F := Frame)
    hpc_m hrun_m hsp_align_m hlr_m
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
    (fun _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    ?_
    (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm))
  intro sf hpcf hrunf hspf hcsf
  dsimp only [withLsCodeLoaded, Poly.EncoderFromPb.DefsBudget.encoderFromPbSpec, protoPolynomialEncoderSize]
  rw [hsp_m] at hspf ⊢
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_elim; intro evs
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr_sf, _hacp_sf, henv⟩
  apply ProofLib.SepWP.done hpcf hrunf
  rcases hcsf with ⟨hx19_f, _hx20_f, hx21_f, hx22_f, hx23_f, _hx24_f, _hx25_f,
    hx26_f, hx27_f, hx28_f, _hx29_f, hvregs_f⟩
  refine ⟨evs, henv, Entails.of_eq (by sep_ac_rfl), hspf,
    hx19_f.trans hx19_m, hx21_f.trans hx21_m, hx22_f.trans hx22_m,
    hx23_f.trans hx23_m, hx26_f.trans hx26_m, hx27_f.trans hx27_m,
    hx28_f.trans hx28_m, ⟨htr_sf.trans htr_m.1, hvregs_f.trans htr_m.2⟩⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux
