/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
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
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudgetAux
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
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux2
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap

open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement blkPC_333 extract_withLsCodeLoaded lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (CIPHERTEXT1_SIZE ENCAPSULATION_KEY_SIZE ENCAPSULATION_STATE_SIZE PolyEncoder PolynomialEncoder ProtoAuthenticator ProtoPolynomialEncoder V1State pbToProtoPolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize optProtoUnchunkedCt1SentEkReceivedAt protoChunkedEkReceivedCt1SampledAt vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (optProtoPolynomialEncoderAt polyEncoderAt resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb (TaggedVariantDispatch TraceCalleeSaved cell0_2296_entails_memRegion_2304 optEncoderPtsBound resultChunkedStatesAt statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack v10_cap_add_one_beq_zero_false v1StatePtsBound v1_optProtoAuthHeap v1_optProtoPolyEncoderAt_unpack v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt v8_3vecs_entails_dealloc v8_encCellsAt v8_len_err_of_false v8_len_ok_of_true v8_optProtoInnerStateAt_ekReceivedCt1Sampled_eq v8_optProtoUcHeap v8_optProtoUnchunkedCt1SentEkReceivedAt_unpack v8_pb128At v8_pb_uc_enc_entails_224 v8_states_from_pb_auth_none_eq v8_states_from_pb_len_err_eq v8_states_from_pb_uc_none_eq v8_ucWordsAt v8_uc_and_enc_words_eq_pb128 vecU8Payload_extract_len_lt63)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget encoder_from_pb_ok_of_alloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudgetAux2 (v8_ekReceivedCt1Sampled_from_1984_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudgetAux (v8_check_auth_1972_none_placed_budget v8_check_auth_1972_some_placed_budget v8_step_1872_to_1972_len_ok_placed_budget)

/-!
# Budget-Threaded Placed Variant 8 (`EkReceivedCt1Sampled`, `+1764`, Block `333`)

Total-correctness (`SepWP`) relocatable body proof (`+1764 -> s0.x30`) and top-level `subroutine_ok`
contracts for Variant 8 (`InnerState.ekReceivedCt1Sampled`) of `<spqr::v1::chunked::states::States>::from_pb`
under `EkReceivedCt1SampledFromPbEnv` and `StatesFromPbEnv`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (authFromPbEvents authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_dispatch_tagged_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget encoder_from_pb_ok_of_alloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudget
  (v8_drop_uc_and_sendingCt1_2100_placed v8_drop_uc_auth_none_10544_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8aPlacedBudgetAux
  (v8_err_4240_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8bPlacedBudget
  (v8_copy_pb_to_stack_1764_placed_budget v8_ekReceivedCt1Sampled_uc_none_placed
   v8_step_1872_to_2100_len_err_x26_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8cPlacedBudget
  (v8_check_auth_1972_none_placed_budget v8_check_auth_1972_some_placed_budget
   v8_check_sendingCt1_10836_none_placed_budget v8_cleanup_5vecs_11120_placed
   v8_clone_macKey_10680_to_10740_placed v8_clone_rootKey_1984_to_10680_placed
   v8_dealloc_old_auth_10740_to_10836_placed v8_step_1872_to_1972_len_ok_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8dPlacedBudget
  (v8_check_enc_res_10904_err_placed_budget v8_check_enc_res_10904_ok_placed_budget
   v8_cleanup_5vecs_10916_placed v8_copy_enc_10836_to_10900_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

theorem seq_clean_lscl_st [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target_pc sm (P_mid sm) post) :
    SepWP prog target_pc s P post := by
  exact Variant8PlacedBudgetAux.seq_clean_lscl_st hcl h1 h2

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
  exact Variant8PlacedBudgetAux.freeOnlyEvs_append hx hy

theorem encoderFromPbEnv_append_freeOnly {pb : ProtoPolynomialEncoder}
    {evs₁ evs₂ : List AllocEvent}
    (h1 : EncoderFromPbEnv pb evs₁) (h2 : FreeOnlyEvs evs₂) :
    EncoderFromPbEnv pb (evs₁ ++ evs₂) := by
  exact Variant8PlacedBudgetAux.encoderFromPbEnv_append_freeOnly h1 h2

theorem ekReceivedCt1SampledAllocEnv_imp_env
    {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled} {evs : List AllocEvent}
    (h : EkReceivedCt1SampledFromPbAllocEnv s evs) :
    EkReceivedCt1SampledFromPbEnv s evs := by
  exact Variant8PlacedBudgetAux.ekReceivedCt1SampledAllocEnv_imp_env h

theorem fitsEnv_alloc_of_ekReceivedCt1SampledEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled}
    (h : FitsEnv M lim st (EkReceivedCt1SampledFromPbEnv s)) :
    FitsEnv M lim st (EkReceivedCt1SampledFromPbAllocEnv s) := by
  exact Variant8PlacedBudgetAux.fitsEnv_alloc_of_ekReceivedCt1SampledEnv h

theorem fitsEvents_auth_of_ekReceivedCt1SampledAllocEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived} {auth : ProtoAuthenticator}
    {sendingCt1 : Option PolynomialEncoder}
    (hlen : ekReceivedCt1SampledUcLenOk u = true)
    (hauth : u.auth = some auth)
    (hfits : FitsEnv M lim st
      (EkReceivedCt1SampledFromPbAllocEnv { uc := some u, sendingCt1 := sendingCt1 })) :
    FitsEvents M lim st (authFromPbEvents auth) := by
  exact Variant8PlacedBudgetAux.fitsEvents_auth_of_ekReceivedCt1SampledAllocEnv hlen hauth hfits

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
  exact Variant8PlacedBudgetAux.tailFits_of_ekReceivedCt1SampledAllocEnv hlen hauth hfree hfits

theorem ekReceivedCt1SampledFromPbEnv_of_tailEnv
    {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1SentEkReceived} {auth : ProtoAuthenticator}
    {sendingCt1 : Option PolynomialEncoder} {evs_af evs_tail : List AllocEvent}
    (hlen : ekReceivedCt1SampledUcLenOk u = true)
    (hauth : u.auth = some auth)
    (hfree : FreeOnlyEvs evs_af)
    (htail : EkReceivedCt1SampledTailEnv sendingCt1 evs_tail) :
    EkReceivedCt1SampledFromPbEnv { uc := some u, sendingCt1 := sendingCt1 }
      ((authFromPbEvents auth ++ evs_af) ++ evs_tail) := by
  exact Variant8PlacedBudgetAux.ekReceivedCt1SampledFromPbEnv_of_tailEnv hlen hauth hfree htail

theorem spqrBoundedEvs_encoderFromPbEnv
    {pb : ProtoPolynomialEncoder} {maxReq : Nat} {evs : List AllocEvent}
    (hreq2 : 2 ≤ maxReq)
    (hpts : ∀ bs ∈ pb.pts, 2 * bs.length ≤ MallocngMaxAllocSize ∧ 2 * bs.length ≤ maxReq)
    (hpolys : ∀ bs ∈ pb.polys, bs.length ≤ MallocngMaxAllocSize ∧ bs.length ≤ maxReq)
    (henv : EncoderFromPbEnv pb evs) :
    SpqrBoundedEvs 32 maxReq evs := by
  exact Variant8PlacedBudgetAux.spqrBoundedEvs_encoderFromPbEnv hreq2 hpts hpolys henv

theorem ekReceivedCt1SampledFromPbEnv_sub_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ekReceivedCt1Sampled s) }))
    {evs : List AllocEvent} (hevs : EkReceivedCt1SampledFromPbEnv s evs) :
    StatesFromPbEnv { innerState := some (.ekReceivedCt1Sampled s) } evs := by
  exact Variant8PlacedBudgetAux.ekReceivedCt1SampledFromPbEnv_sub_statesFromPbEnv s hfits hevs

theorem fitsEnv_ekReceivedCt1SampledAlloc_of_statesFromPbEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (hfits : FitsEnv M lim st (StatesFromPbEnv { innerState := some (.ekReceivedCt1Sampled s) })) :
    FitsEnv M lim st (EkReceivedCt1SampledFromPbAllocEnv s) := by
  exact Variant8PlacedBudgetAux.fitsEnv_ekReceivedCt1SampledAlloc_of_statesFromPbEnv s hfits

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
  exact Variant8PlacedBudgetAux.v8_stage_11264_to_ret_placed (F := F) hA st s0 s
    fsp out tag ep pa1 l1 pa2 l2 ca3 pa3 ca4 pa4 ca5 pa5 bs hbs hi32 enc P_heap hreloc
    rootKey macKey es ek ct1 hl1 hl2 hes hek hct1 Frame
    halign hfsp hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx26 hx28 htr

/-! ## 3. Budget-Threaded `<PolyEncoder>::from_pb` Call (`+10900 -> +10904`) -/

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
  exact Variant8PlacedBudgetAux.v8_call_encoder_from_pb_10900_to_10904_placed hE st s0 s hcl
    fsp out pa5 l1 u8 pbA l2 pbEnc w0 w8 w16 w24 w32 w40 w48 Frame
    hfits hpts halign hfsp hpc hrun hsp hx0 hx1 hx19 hx21 hx22 hx23 hx26 hx27 hx28 htr

example : EkReceivedCt1SampledTailEnv none [] := FreeOnlyEvs.nil
example : EkReceivedCt1SampledFromPbAllocEnv { uc := none, sendingCt1 := none } [] := rfl
example : EkReceivedCt1SampledFromPbEnv { uc := none, sendingCt1 := none } [] := FreeOnlyEvs.nil

/-! ## 4. Budget-Threaded Entry from `+1764` (`+1764 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem states_from_pb_ekReceivedCt1Sampled_1764_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hE : EncoderFromPbPlacedOkExt M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (hpts : optEncoderPtsBound s.sendingCt1)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (hfits : FitsEnv M lim st (EkReceivedCt1SampledFromPbAllocEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.ekReceivedCt1Sampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EkReceivedCt1SampledFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  rw [v8_optProtoInnerStateAt_ekReceivedCt1Sampled_eq]
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      optProtoUnchunkedCt1SentEkReceivedAt A.repAlloc (pbA + 8#64) s.uc ∗
      optProtoPolynomialEncoderAt A.repAlloc (pbA + 136#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000008#64) ∗
       memRegion (pbA + 192#64) 32 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) by sep_ac_rfl))
      (sepConj_mono (v8_optProtoUnchunkedCt1SentEkReceivedAt_unpack A.repAlloc (pbA + 8#64) s.uc)
        (sepConj_mono_left
          (v1_optProtoPolyEncoderAt_unpack A.repAlloc (pbA + 136#64)
            (s.sendingCt1.map pbToProtoPolyEncoder))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro w32
  apply ProofLib.SepWP.exists_left; intro w40
  apply ProofLib.SepWP.exists_left; intro w48
  apply ProofLib.SepWP.exists_left; intro u8
  apply ProofLib.SepWP.exists_left; intro u16
  apply ProofLib.SepWP.exists_left; intro u24
  apply ProofLib.SepWP.exists_left; intro u32
  apply ProofLib.SepWP.exists_left; intro u40
  apply ProofLib.SepWP.exists_left; intro u48
  apply ProofLib.SepWP.exists_left; intro u56
  apply ProofLib.SepWP.exists_left; intro u64
  apply ProofLib.SepWP.exists_left; intro u72
  apply ProofLib.SepWP.exists_left; intro u80
  apply ProofLib.SepWP.exists_left; intro u88
  apply ProofLib.SepWP.exists_left; intro u96
  apply ProofLib.SepWP.exists_left; intro u104
  apply ProofLib.SepWP.exists_left; intro u112
  apply ProofLib.SepWP.exists_left; intro u120
  apply ProofLib.SepWP.exists_left; intro u128
  cases s with | mk uc sendingCt1 =>
  dsimp only at hpts hfits ⊢
  cases uc with
  | none =>
    rw [v8_states_from_pb_uc_none_eq]
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72
          u80 u88 u96 u104 u112 u120 u128 ∗
        ⌜u8 = noneCap⌝ ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1 =
      ⌜u8 = noneCap⌝ ∗
      ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72
          u80 u88 u96 u104 u112 u120 u128 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000008#64) ∗
       memRegion (pbA + 192#64) 32 ∗
       v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
         w0 w8 w16 w24 w32 w40 w48 ∗
       statesFromPbJumpTablePlacedAt ∗
       A.pool lim st s1) by sep_ac_rfl]
    apply ProofLib.SepWP.pure_elim; intro hu8
    subst hu8
    rw [v8_uc_and_enc_words_eq_pb128]
    have hnone := Variant8bPlacedBudget.v8_ekReceivedCt1Sampled_uc_none_placed (F := F) hA st s0 s1 out pbA
      u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
      hcl1 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hnone ?_)
    intro sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩
  | some u =>
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72
          u80 u88 u96 u104 u112 u120 u128 ∗
        ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧
          u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧
          u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧ u128 = u.epoch⌝ ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗
        vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1 =
      ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧
        u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧
        u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧ u128 = u.epoch⌝ ∗
      (vecU8Payload A.repAlloc u8 u16 u.es ∗
       vecU8Payload A.repAlloc u32 u40 u.ek ∗
       vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
       ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72
           u80 u88 u96 u104 u112 u120 u128 ∗
         v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)) by sep_ac_rfl]
    apply ProofLib.SepWP.pure_elim; rintro ⟨hu8, hu24, hu32, hu48, hu56, hu72, hu128⟩
    rw [v8_uc_and_enc_words_eq_pb128]
    refine SepWP.weaken_pre
      (sepConj_mono (vecU8Payload_extract_len_lt63 A.repAlloc u8 u16 u.es)
        (sepConj_mono (vecU8Payload_extract_len_lt63 A.repAlloc u32 u40 u.ek)
          (sepConj_mono_left (vecU8Payload_extract_len_lt63 A.repAlloc u56 u64 u.ct1)))) ?_
    rw [show (⌜u.es.length < 2 ^ 63⌝ ∗ vecU8Payload A.repAlloc u8 u16 u.es) ∗
        (⌜u.ek.length < 2 ^ 63⌝ ∗ vecU8Payload A.repAlloc u32 u40 u.ek) ∗
        (⌜u.ct1.length < 2 ^ 63⌝ ∗ vecU8Payload A.repAlloc u56 u64 u.ct1) ∗
        (v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
         v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
           w0 w8 w16 w24 w32 w40 w48 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x8000000000000008#64) ∗
         memRegion (pbA + 192#64) 32 ∗
         statesFromPbJumpTablePlacedAt ∗
         A.pool lim st s1) =
      ⌜u.es.length < 2 ^ 63⌝ ∗ ⌜u.ek.length < 2 ^ 63⌝ ∗ ⌜u.ct1.length < 2 ^ 63⌝ ∗
      (memRegion (s0.sp - 2400#64) 2304 ∗
       v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
         w0 w8 w16 w24 w32 w40 w48 ∗
       A.pool lim st s1 ∗
       (vecU8Payload A.repAlloc u8 u16 u.es ∗
        vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt)) by sep_ac_rfl]
    apply ProofLib.SepWP.pure_elim; intro hes_lt
    apply ProofLib.SepWP.pure_elim; intro hek_lt
    apply ProofLib.SepWP.pure_elim; intro hct1_lt
    let Rest_copy : SepProp :=
      vecU8Payload A.repAlloc u8 u16 u.es ∗
      vecU8Payload A.repAlloc u32 u40 u.ek ∗
      vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
      v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
        w0 w8 w16 w24 w32 w40 w48 ∗
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      (pbA ↦₆₄ 0x8000000000000008#64) ∗
      memRegion (pbA + 192#64) 32 ∗
      statesFromPbJumpTablePlacedAt
    have hcopy := v8_copy_pb_to_stack_1764_placed_budget A lim st (ext := ext) s0 s1 out pbA
      u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
      w0 w8 w16 w24 w32 w40 w48 Rest_copy
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    have hu8_ne : (u8 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hu8
    simp only [hu8_ne, Bool.false_eq_true, ↓reduceIte] at hcopy
    refine seq_clean_lscl_st hcl1
      (mid := lsmpl.base 333 + 1872#64)
      (P_mid := fun s2 =>
        memRegion (s0.sp - 2400#64) 1392 ∗
        v8_ucWordsAt (s0.sp - 2400#64 + 1392#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
          w0 w8 w16 w24 w32 w40 w48 ∗
        A.pool lim st s2 ∗ Rest_copy)
      (Q := fun s2 =>
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x23 = s1.readReg64 .x23 ∧
        s2.readReg64 .x26 = u8 ∧
        s2.readReg64 .x27 = pbA ∧
        TraceCalleeSaved s2 s0)
      (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, _hvm2, hregs⟩ => ⟨hP2, hregs⟩) ?_
    intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx23_2, hx26_2, hx27_2, htr2⟩
    rw [hx23_1] at hx23_2
    rw [← v8_uc_and_enc_words_eq_pb128]
    dsimp only [Rest_copy]
    cases hlen : ekReceivedCt1SampledUcLenOk u with
    | false =>
      have hlen_raw :
          (u.es.length == ENCAPSULATION_STATE_SIZE &&
           u.ct1.length == CIPHERTEXT1_SIZE &&
           u.ek.length == ENCAPSULATION_KEY_SIZE) = false := hlen
      rw [v8_states_from_pb_len_err_eq u sendingCt1 hlen_raw]
      have herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64 := by
        rw [hu24, hu72, hu48]
        exact v8_len_err_of_false u hlen_raw hes_lt hct1_lt hek_lt
      let Rest_lerr : SepProp :=
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗
        vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt
      have hstep := v8_step_1872_to_2100_len_err_x26_placed_budget A lim st (ext := ext)
        s0 s2 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        Rest_lerr herr hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWP.weaken_pre (by dsimp only [Rest_lerr]; exact Entails.of_eq (by sep_ac_rfl))
        (SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl2
          (SepWP.mono hstep fun s3 P3 hpc3 hrun3 ⟨hP3, _hvm3, hsp3, hx19_3, hx26_3, htr3⟩ hcl3 => ?_))
      have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72
        u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
      have h3v := v8_3vecs_entails_dealloc A.repAlloc u8 u16 u32 u40 u56 u64 u.es u.ek u.ct1
      have hP3' : P3 ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 896 ∗
          v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A.repAlloc u8 u16 ∗
          vecCapPtrDealloc A.repAlloc u32 u40 ∗
          vecCapPtrDealloc A.repAlloc u56 u64 ∗
          v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
          A.pool lim st s3 ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) := by
        refine Entails.trans hP3 ?_
        dsimp only [Rest_lerr]
        refine Entails.trans (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 0x8000000000000008#64) ∗
           v8_ucWordsAt (pbA + 8#64)
             u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 192#64) 32) ∗
          (vecU8Payload A.repAlloc u8 u16 u.es ∗
           vecU8Payload A.repAlloc u32 u40 u.ek ∗
           vecU8Payload A.repAlloc u56 u64 u.ct1) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 896 ∗
           v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
             u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
           A.pool lim st s3 ∗
           statesFromPbJumpTablePlacedAt) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hpb_col (sepConj_mono_left h3v)) (Entails.of_eq (by sep_ac_rfl))
      have hdrop := Variant8aPlacedBudget.v8_drop_uc_and_sendingCt1_2100_placed (F := F) hA st s0 s3 out
        u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u.auth
        (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
        hcl3 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3
      refine SepWP.weaken_pre hP3' (SepWP.mono hdrop ?_)
      intro sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩
      refine ⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩
      unfold EkReceivedCt1SampledFromPbEnv
      simp only [hlen, Bool.false_eq_true, ↓reduceIte]
      exact hfree
    | true =>
      have hlen_raw :
          (u.es.length == ENCAPSULATION_STATE_SIZE &&
           u.ct1.length == CIPHERTEXT1_SIZE &&
           u.ek.length == ENCAPSULATION_KEY_SIZE) = true := hlen
      obtain ⟨hes, hct1, hek⟩ := v8_len_ok_of_true u hlen_raw
      have hu24_eq : u24 = 2080#64 := by rw [hu24, hes]
      have hu48_eq : u48 = 1152#64 := by rw [hu48, hek]
      have hu72_eq : u72 = 960#64 := by rw [hu72, hct1]
      subst hu24_eq hu48_eq hu72_eq hu128
      let Rest_lok : SepProp :=
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        vecU8Payload A.repAlloc u8 u16 u.es ∗
        vecU8Payload A.repAlloc u32 u40 u.ek ∗
        vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
        v1_optProtoAuthHeap A.repAlloc u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
          w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTablePlacedAt
      have hstep := v8_step_1872_to_1972_len_ok_placed_budget A lim st (ext := ext)
        s0 s2 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u.epoch Rest_lok
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWP.weaken_pre (by dsimp only [Rest_lok]; exact Entails.of_eq (by sep_ac_rfl))
        (seq_clean_lscl_st hcl2
          (mid := lsmpl.base 333 + 1972#64)
          (P_mid := fun s3 =>
            memRegion (s0.sp - 2400#64) 896 ∗
            v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            A.pool lim st s3 ∗ Rest_lok)
          (Q := fun s3 =>
            s3.sp = s0.sp - 2400#64 ∧
            s3.readReg64 .x19 = out ∧
            s3.readReg64 .x26 = u8 ∧
            s3.readReg64 .x27 = pbA ∧
            TraceCalleeSaved s3 s0)
          (SepWP.mono hstep fun s3 P3 _ _ ⟨hP3, _hvm3, hregs⟩ => ⟨hP3, hregs⟩) ?_)
      intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx26_3, hx27_3, htr3⟩
      dsimp only [Rest_lok]
      cases hauth : u.auth with
      | none =>
        rw [v8_states_from_pb_auth_none_eq u sendingCt1 hlen_raw hauth]
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗
            v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            A.pool lim st s3 ∗
            (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64)
               w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
             v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
             vecU8Payload A.repAlloc u8 u16 u.es ∗
             vecU8Payload A.repAlloc u32 u40 u.ek ∗
             vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
             ⌜u80 = noneCap⌝ ∗
             v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
               w0 w8 w16 w24 w32 w40 w48 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             (pbA ↦₆₄ 0x8000000000000008#64) ∗
             memRegion (pbA + 192#64) 32 ∗
             statesFromPbJumpTablePlacedAt) =
          ⌜u80 = noneCap⌝ ∗
          (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
             u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
             u80 u88 u96 u104 u112 u120 u.epoch ∗
           ((pbA ↦₆₄ 0x8000000000000008#64) ∗
            v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (pbA + 192#64) 32) ∗
           A.pool lim st s3 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 896 ∗
           memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
             w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           vecU8Payload A.repAlloc u8 u16 u.es ∗
           vecU8Payload A.repAlloc u32 u40 u.ek ∗
           vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
           statesFromPbJumpTablePlacedAt) by sep_ac_rfl]
        apply ProofLib.SepWP.pure_elim; intro hu80
        subst hu80
        have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
          noneCap u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hpb_col)) ?_
        let Rest_an : SepProp :=
          memRegion pbA optProtoInnerStateSize ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 896 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecU8Payload A.repAlloc u8 u16 u.es ∗
          vecU8Payload A.repAlloc u32 u40 u.ek ∗
          vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
          statesFromPbJumpTablePlacedAt
        have hchk := v8_check_auth_1972_none_placed_budget A lim st (ext := ext) s0 s3 out
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120 u.epoch
          Rest_an hsp0_align hpc3 hrun3 hsp3 hx19_3 htr3
        refine SepWP.weaken_pre (by dsimp only [Rest_an]; exact Entails.of_eq (by sep_ac_rfl))
          (SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl3
            (SepWP.mono hchk fun s4 P4 hpc4 hrun4 ⟨hP4, _hvm4, hsp4, hx19_4, htr4⟩ hcl4 => ?_))
        have hdrop := Variant8aPlacedBudget.v8_drop_uc_auth_none_10544_placed (F := F) hA st s0 s4 out u
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120
          (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
          hcl4 hsp0_align hu8 (by rw [hes]; rfl) hu32 (by rw [hek]; rfl) hu56 (by rw [hct1]; rfl)
          hauth hpc4 hrun4 hsp4 hx19_4 htr4
        refine SepWP.weaken_pre
          (Entails.trans hP4 (by dsimp only [Rest_an]; exact Entails.of_eq (by sep_ac_rfl)))
          (SepWP.mono hdrop ?_)
        intro sf Pf _ _ ⟨evs, hfree, hPf, hsp_f, hcs_f, htr_f⟩
        refine ⟨evs, ?_, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩
        unfold EkReceivedCt1SampledFromPbEnv
        simp only [hlen, ↓reduceIte, hauth]
        exact hfree
      | some auth =>
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗
            v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            A.pool lim st s3 ∗
            (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64)
               w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
             v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
             vecU8Payload A.repAlloc u8 u16 u.es ∗
             vecU8Payload A.repAlloc u32 u40 u.ek ∗
             vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
             (⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧
                 u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
              vecU8Payload A.repAlloc u80 u88 auth.rootKey ∗
              vecU8Payload A.repAlloc u104 u112 auth.macKey) ∗
             v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
               w0 w8 w16 w24 w32 w40 w48 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             (pbA ↦₆₄ 0x8000000000000008#64) ∗
             memRegion (pbA + 192#64) 32 ∗
             statesFromPbJumpTablePlacedAt) =
          ⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧
            u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗
          (v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
             u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
             u80 u88 u96 u104 u112 u120 u.epoch ∗
           A.pool lim st s3 ∗
           (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 896 ∗
            memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
            v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
              w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
            statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗
            vecU8Payload A.repAlloc u80 u88 auth.rootKey ∗
            vecU8Payload A.repAlloc u104 u112 auth.macKey ∗
            vecU8Payload A.repAlloc u8 u16 u.es ∗
            vecU8Payload A.repAlloc u32 u40 u.ek ∗
            vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
            (pbA ↦₆₄ 0x8000000000000008#64) ∗
            v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 u96 u104 u112 u120 u.epoch ∗
            v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (pbA + 192#64) 32 ∗
            statesFromPbJumpTablePlacedAt)) by sep_ac_rfl]
        apply ProofLib.SepWP.pure_elim; rintro ⟨hu80, hu96, hu120⟩
        subst hu96 hu120
        let Rest_as : SepProp :=
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 896 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A.repAlloc (sendingCt1.map pbToProtoPolyEncoder)
            w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          vecU8Payload A.repAlloc u80 u88 auth.rootKey ∗
          vecU8Payload A.repAlloc u104 u112 auth.macKey ∗
          vecU8Payload A.repAlloc u8 u16 u.es ∗
          vecU8Payload A.repAlloc u32 u40 u.ek ∗
          vecU8Payload A.repAlloc u56 u64 u.ct1 ∗
          (pbA ↦₆₄ 0x8000000000000008#64) ∗
          v8_ucWordsAt (pbA + 8#64)
            u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
            u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
            u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (pbA + 192#64) 32 ∗
          statesFromPbJumpTablePlacedAt
        have hchk := v8_check_auth_1972_some_placed_budget A lim st (ext := ext) s0 s3 out pbA
          u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
          u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
          u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch Rest_as
          hu80 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 hx27_3 htr3
        refine seq_clean_lscl_st hcl3
          (mid := lsmpl.base 333 + 1984#64)
          (P_mid := fun s4 =>
            v8_ucWordsAt (s0.sp - 2400#64 + 896#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64
              u80 u88 (BitVec.ofNat 64 auth.rootKey.length)
              u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
            A.pool lim st s4 ∗ Rest_as)
          (Q := fun s4 =>
            s4.sp = s0.sp - 2400#64 ∧
            s4.readReg64 .x19 = out ∧
            s4.readReg64 .x23 = u80 ∧
            s4.readReg64 .x26 = u8 ∧
            s4.readReg64 .x27 = pbA ∧
            TraceCalleeSaved s4 s0)
          (SepWP.mono hchk fun s4 P4 _ _ ⟨hP4, _hvm4, hregs⟩ => ⟨hP4, hregs⟩) ?_
        intro s4 hpc4 hrun4 hcl4 ⟨hsp4, hx19_4, hx23_4, hx26_4, hx27_4, htr4⟩
        exact SepWP.weaken_pre (by dsimp only [Rest_as]; exact Entails.of_eq (by sep_ac_rfl))
          (v8_ekReceivedCt1Sampled_from_1984_placed (F := F) hA hE st s0 s4 out pbA u auth
            sendingCt1 hpts hfits u8 u16 u32 u40 u56 u64 u80 u88 u104 u112
            w0 w8 w16 w24 w32 w40 w48
            hlen hes hek hct1 hauth hcl4 hsp0_align hpc4 hrun4 hsp4
            hx19_4 hx23_4 hx26_4 hx27_4 htr4)

theorem states_from_pb_ekReceivedCt1Sampled_1764_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (hpts : optEncoderPtsBound s.sendingCt1)
    (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out pbA : BitVec 64)
    (hfits : FitsEnv M lim st (EkReceivedCt1SampledFromPbAllocEnv s))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1764#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A.repAlloc pbA (some (.ekReceivedCt1Sampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗
        A.pool lim st s1)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EkReceivedCt1SampledFromPbEnv s evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled s) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  exact states_from_pb_ekReceivedCt1Sampled_1764_placed (F := F) hA
    (encoder_from_pb_ok_of_alloc_placed hA) s hpts st s0 s1 hcl1 out pbA hfits
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

/-! ## 5. Tagged Dispatch + Top-Level `subroutine_ok` Contracts (`[LibsignalPlacement]`) -/

/-- Lift a tagged-variant `SepWP` body at `+off` (threading `LibsignalCodeLoaded`) to `subroutine_ok`
    for `withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)`. -/
theorem sfpProof_tagged_ok_of_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {inner : CryptoVerification.LibsignalSpqrV1.V1State.InnerState} {tag off : BitVec 64} {Tail : BitVec 64 → SepProp}
    {Env : List AllocEvent → Prop}
    (htag : TaggedVariantDispatch tag off)
    (hinner : ∀ pbA, optProtoInnerStateAt A.repAlloc pbA (some inner) = (pbA ↦₆₄ tag) ∗ Tail pbA)
    (hstep : ∀ (hpts : v1StatePtsBound { innerState := some inner })
      (st : M.σ) (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
      (out pbA : BitVec 64) (R : SepProp),
      FitsEnv M lim st Env →
      (s0.sp &&& 15#64 == 0#64) = true →
      s1.pc = lsmpl.base 333 + off →
      s1.status = .Running →
      s1.sp = s0.sp - 2400#64 →
      s1.readReg64 .x19 = out →
      s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 →
      s1.readReg64 .x27 = pbA →
      TraceCalleeSaved s1 s0 →
      SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s1
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
          statesFromPbJumpTablePlacedAt ∗
          A.pool lim st s1)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              (withLsCodeLoaded lsmpl
                (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)).post
                ((out, pbA), st) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨
              (withLsCodeLoaded lsmpl
                (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)).onPanic
                ((out, pbA), st) s0 sf ∗ R))) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F { innerState := some inner } Env)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨out, pbA⟩, st⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  dsimp only [DefsBudget.statesFromPbVariantPlacedSpecOfEnv] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx8, hx0, hpts, hfits⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗ A.pool lim st s0 ∗
      (memRegion out chunkedStatesSize ∗
       optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
       statesFromPbJumpTablePlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := DefsBudget.states_from_pb_prologue_placed (ext := ext) A lim st s0 out pbA
    (memRegion out chunkedStatesSize ∗
     optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
     statesFromPbJumpTablePlacedAt)
    hsp0_align hpc0 hrun0 hx8 hx0
  refine SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl0
    (SepWP.mono hpro fun s1 P1 hpc1 hrun1 ⟨hP1, hsp1, _, hx8_1, hx0_1, htr1, _⟩ hcl1 => ?_)
  have hP1' : P1 ⊢
      (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
       memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Tail pbA) ∗
      A.pool lim st s1 := by
    refine Entails.trans hP1 ?_
    rw [hinner pbA]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := states_from_pb_dispatch_tagged_placed_budget A lim st (ext := ext)
    s0 s1 out pbA tag off
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     ((s0.sp - 2400#64) ↦₆₄ 0#64) ∗
     memRegion ((s0.sp - 2400#64) + 8#64) 2296 ∗
     statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗
     Tail pbA)
    htag hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl1
    (SepWP.mono hdisp fun s2 P2 hpc2 hrun2
      ⟨hP2, hsp2, hx19_2, hx27_2, _, _, _, _, hx23_2, htr2, _⟩ hcl2 => ?_)
  have hx23_2' : s2.readReg64 .x23 = (s0.sp - 2400#64) + 848#64 := by
    rw [hx23_2]; bv_omega
  have hpre_join : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A.repAlloc pbA (some inner) ∗
      statesFromPbJumpTablePlacedAt ∗
      A.pool lim st s2 := by
    refine Entails.trans hP2 ?_
    rw [hinner pbA]
    have h2304 := cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64
    refine Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       ((pbA ↦₆₄ tag) ∗ Tail pbA) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool lim st s2) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h2304) (Entails.of_eq (by sep_ac_rfl))
  exact SepWPp.weaken_pre hpre_join
    (hstep hpts st s0 s2 hcl2 out pbA R hfits hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2' hx27_2 htr2)

/-- Envelope-parametric `subroutine_ok` for Variant 8 (`InnerState.ekReceivedCt1Sampled`, `+1764`). -/
theorem states_from_pb_ekReceivedCt1Sampled_ok_ext_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : List AllocEvent → Prop}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled)
    (hfits_imp : ∀ st, FitsEnv M lim st Env → FitsEnv M lim st (EkReceivedCt1SampledFromPbAllocEnv s))
    (henv_sub : ∀ st, FitsEnv M lim st Env → ∀ evs, EkReceivedCt1SampledFromPbEnv s evs → Env evs) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ekReceivedCt1Sampled s) } Env)) := by
  exact sfpProof_tagged_ok_of_step_cl_placed CryptoVerification.SpqrV1.States.FromPb.TaggedVariantDispatch.ekReceivedCt1Sampled
    (Tail := fun pbA =>
      protoChunkedEkReceivedCt1SampledAt A.repAlloc (pbA + 8#64) s ∗ memRegion (pbA + 192#64) 32)
    (fun _ => rfl)
    (fun hpts st s0 s1 hcl1 out pbA R hfits hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1 =>
      DefsBudget.sepWPp_of_states_exit_cl_placed st s0 s1 out pbA
        { innerState := some (.ekReceivedCt1Sampled s) } Env _ R
        (SepWP.mono
          (states_from_pb_ekReceivedCt1Sampled_1764_placed (F := F) hA henc s hpts st s0 s1 hcl1
            out pbA (hfits_imp st hfits) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1)
          fun _ _ _ _ ⟨evs, hevs, hPf, hsp_f, hcs_f, htr_f⟩ =>
            ⟨⟨evs, henv_sub st hfits evs hevs, hPf⟩, hsp_f, hcs_f, htr_f⟩))

/-- Tight-envelope (`EkReceivedCt1SampledFromPbEnv s`) `subroutine_ok` for Variant 8. -/
theorem states_from_pb_ekReceivedCt1Sampled_ok_ext_tight_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpecOfEnv M A lim F
          { innerState := some (.ekReceivedCt1Sampled s) }
          (EkReceivedCt1SampledFromPbEnv s))) := by
  exact states_from_pb_ekReceivedCt1Sampled_ok_ext_of_env_placed hA henc s
    (fun _ => fitsEnv_alloc_of_ekReceivedCt1SampledEnv)
    (fun _ _ _ h => h)

/-- Uniform `statesFromPbVariantPlacedSpec` (`StatesFromPbEnv`) `subroutine_ok` for Variant 8
    (`InnerState.ekReceivedCt1Sampled`, `+1764`). -/
theorem states_from_pb_ekReceivedCt1Sampled_ok_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.ekReceivedCt1Sampled s) })) := by
  exact states_from_pb_ekReceivedCt1Sampled_ok_ext_of_env_placed hA henc s
    (fun _ => fitsEnv_ekReceivedCt1SampledAlloc_of_statesFromPbEnv s)
    (fun _ hfits _ hevs => ekReceivedCt1SampledFromPbEnv_sub_statesFromPbEnv s hfits hevs)

theorem states_from_pb_ekReceivedCt1Sampled_ok_ext_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333)
      (withLsCodeLoaded lsmpl
        (DefsBudget.statesFromPbVariantPlacedSpec M A lim F
          { innerState := some (.ekReceivedCt1Sampled s) })) := by
  exact states_from_pb_ekReceivedCt1Sampled_ok_ext_placed hA (encoder_from_pb_ok_of_alloc_placed hA) s

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8PlacedBudget
