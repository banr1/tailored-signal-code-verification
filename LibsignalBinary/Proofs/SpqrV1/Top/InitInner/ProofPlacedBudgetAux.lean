/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `spqr::init_inner` (`Block 324`): Callee-Parametric Relocatable Budget Proof

Composes relocatable `VmPreserved` basic-block steppers on `Block 324` with allocator/memcpy
contracts, `<Authenticator>::new` (`Block 340`), and `<States>::into_pb` (`Block 334`) to
prove callee-parametric relocatable entrypoints for `spqr::init_inner`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement extract_withLsCodeLoaded lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Direction PolynomialDecoder ProtoAuthenticator States V1State Version
   hkdfToSliceUnchecked hkdfToVecUnchecked length_hkdfExpand spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto
  (WireType encodeBytesField encodeBytesUncond encodeKey encodeMessage encodeOptMessage
   encodeUint64Field encodeVarint encodeVarintAux)
open CryptoVerification.SpqrV1.Auth
  (AuthNewGhost authNewStackX authenticatorAt authenticatorSize)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (LsCallInv withLsCallInv)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.States.IntoPb
  (authenticatorHeap bv_add_add_lit' bv_sub_sub_lit' statesIntoPbStack)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost authenticatorAt_expose_frame calleeSaved_chain_hi calleeSaved_x19 calleeSaved_x29
   initHdrDecoder initInnerResultAt initInnerSavedCells initInnerStack initInnerStackX initV1State
   memRegion_24_and_cells_17_eq_cells_20 memRegion_24_and_cells_5_eq_cells_8
   memRegion_48_and_8_eq_56 memRegion_992_rejoin_b2a memRegion_992_split_a2b
   memRegion_992_split_b2a stackAt_authNew_split_allocHook stackAt_authNew_split_statesIntoPb
   stackAt_initInner_split statesIntoPbJumpTablePlacedAt vecU8_nonempty_of_cells)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_324 blkPl_324)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv SpqrBoundedEvs initInnerPlacedSpec initInnerPlacedSpecOfEnv initInnerPlacedSpecX
   initInnerPlacedSpecXOfEnv nonFreeCount statesIntoPbPlacedSpec statesIntoPbPlacedSpecOfEnv
   statesIntoPbVariantPlacedSpec statesIntoPbVariantPlacedSpecOfEnv
   withLsCodeLoaded_initInnerPlacedSpecX_of_initInnerPlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsPlacedBudget
  (init_inner_a2b_132_to_140_placed init_inner_a2b_144_ok_to_160_placed
   init_inner_a2b_164_to_364_placed init_inner_a2b_empty_to_364_placed
   init_inner_a2b_post_auth_placed init_inner_a2b_to_128_placed init_inner_b2a_52_to_60_placed
   init_inner_b2a_empty_to_192_placed init_inner_b2a_post_auth_placed init_inner_b2a_to_48_placed
   init_inner_epilogue_placed init_inner_prologue_v1_placed init_inner_v0_placed)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

/-! ## 1. Budget Envelope & Protobuf Encoding Bounds -/

/-- Any request size `n ≤ maxReq` admitted by `FitsEnv M lim st (SpqrBoundedEvs c maxReq)` with
    `1 ≤ c` is bounded by `2 ^ 48` (and hence `≤ MallocngMaxAllocSize`). -/
theorem le_two_pow_48_of_fitsEnv_spqrBoundedEvs
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {c maxReq n : Nat}
    (hc : 1 ≤ c) (hn : n ≤ maxReq)
    (hfit : FitsEnv M lim st (SpqrBoundedEvs c maxReq)) :
    n ≤ 2 ^ 48 := by
  let r := min n MallocngMaxAllocSize
  have hmem : SpqrBoundedEvs c maxReq [.alloc r] := by
    refine ⟨by simp [nonFreeCount]; omega, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.min_le_right _ _, Nat.le_trans (Nat.min_le_left _ _) hn,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
  rcases (hfit [.alloc r] hmem).1 with ⟨_, _, _, hva⟩
  have hreq : r ≤ M.stepReserve (.alloc r) st := M.req_le_stepReserve (.alloc r) st
  have hmax : 2 ^ 48 < MallocngMaxAllocSize := by decide
  have hr48 : min n MallocngMaxAllocSize ≤ 2 ^ 48 := by omega
  omega

theorem le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {c maxReq n : Nat}
    (hc : 1 ≤ c) (hn : n ≤ maxReq)
    (hfit : FitsEnv M lim st (SpqrBoundedEvs c maxReq)) :
    n ≤ MallocngMaxAllocSize := by
  have h48 := le_two_pow_48_of_fitsEnv_spqrBoundedEvs hc hn hfit
  have hmax : 2 ^ 48 ≤ MallocngMaxAllocSize := by decide
  omega

/-- Deterministic allocation events emitted by cloning `authKey : &[u8]` into `Vec<u8>`. -/
def cloneEvs (authKey : Bytes) : List AllocEvent :=
  if authKey.length = 0 then [] else rustAllocEvents authKey.length 1

theorem cloneEvs_of_length_zero {authKey : Bytes} (h : authKey.length = 0) :
    cloneEvs authKey = [] := by
  simp [cloneEvs, h]

theorem cloneEvs_of_pos {authKey : Bytes} (h : 0 < authKey.length) :
    cloneEvs authKey = rustAllocEvents authKey.length 1 := by
  unfold cloneEvs
  simp [Nat.ne_of_gt h]

theorem rustAllocEvents_one_of_pos {n : Nat} (h : 0 < n) :
    rustAllocEvents n 1 = [.alloc n] := by
  unfold rustAllocEvents
  simp [Nat.ne_of_gt h]

theorem spqrBoundedEvs_cloneEvs {authKey : Bytes}
    (hmax : authKey.length ≤ MallocngMaxAllocSize) :
    SpqrBoundedEvs 1 authKey.length (cloneEvs authKey) := by
  by_cases h0 : authKey.length = 0
  · rw [cloneEvs_of_length_zero h0]
    exact SpqrBoundedEvs.nil 1 _
  · have hpos : 0 < authKey.length := Nat.pos_of_ne_zero h0
    rw [cloneEvs_of_pos hpos, rustAllocEvents_one_of_pos hpos]
    refine ⟨by simp [nonFreeCount], fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hmax, Nat.le_refl _, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

private theorem encodeVarintAux_length_le : ∀ (fuel : Nat) (v : BitVec 64),
    (encodeVarintAux fuel v).length ≤ fuel + 1
  | 0, _ => by simp [encodeVarintAux]
  | fuel + 1, v => by
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have ih := encodeVarintAux_length_le fuel (v >>> 7)
      omega

private theorem encodeVarint_length_le (v : BitVec 64) :
    (encodeVarint v).length ≤ 11 :=
  encodeVarintAux_length_le 10 v

private theorem encodeKey_length_le (tag : BitVec 32) (wt : WireType) :
    (encodeKey tag wt).length ≤ 11 :=
  encodeVarint_length_le _

private theorem encodeBytesUncond_length_le (tag : BitVec 32) (bs : Bytes) :
    (encodeBytesUncond tag bs).length ≤ 22 + bs.length := by
  unfold encodeBytesUncond
  simp only [List.length_append]
  have hk := encodeKey_length_le tag .lengthDelimited
  have hv := encodeVarint_length_le (BitVec.ofNat 64 bs.length)
  omega

private theorem encodeBytesField_length_le (tag : BitVec 32) (bs : Bytes) :
    (encodeBytesField tag bs).length ≤ 22 + bs.length := by
  unfold encodeBytesField
  split
  · simp
  · exact encodeBytesUncond_length_le tag bs

private theorem encodeMessage_length_le {M : Type} (enc : M → Bytes)
    (tag : BitVec 32) (m : M) :
    (encodeMessage enc tag m).length ≤ 22 + (enc m).length := by
  unfold encodeMessage
  dsimp only
  simp only [List.length_append]
  have hk := encodeKey_length_le tag .lengthDelimited
  have hv := encodeVarint_length_le (BitVec.ofNat 64 (enc m).length)
  omega

private theorem authenticatorNew_keys_length_le (F : ShaCompress) (authKey : Bytes) :
    (Authenticator.new F authKey 1#64).rootKey.length ≤ 32 ∧
      (Authenticator.new F authKey 1#64).macKey.length ≤ 32 := by
  unfold Authenticator.new Authenticator.update hkdfToVecUnchecked hkdfToSliceUnchecked
  dsimp only
  simp only [List.length_take, List.length_drop, length_hkdfExpand]
  omega

private theorem protoAuthenticator_encodeRaw_new_length_le (F : ShaCompress) (authKey : Bytes) :
    (ProtoAuthenticator.encodeRaw
      ((spqrAuthApi F).into_pb (Authenticator.new F authKey 1#64))).length ≤ 108 := by
  have ⟨hrk, hmk⟩ := authenticatorNew_keys_length_le F authKey
  change (encodeBytesField 1#32 (Authenticator.new F authKey 1#64).rootKey ++
    encodeBytesField 2#32 (Authenticator.new F authKey 1#64).macKey).length ≤ 108
  simp only [List.length_append]
  have h1 := encodeBytesField_length_le 1#32 (Authenticator.new F authKey 1#64).rootKey
  have h2 := encodeBytesField_length_le 2#32 (Authenticator.new F authKey 1#64).macKey
  omega

/-- Encoded protobuf size of `(initV1State F d authKey).into_pb` is bounded by `512` bytes
    independently of `F` and `authKey`. -/
theorem encodeRaw_initV1State_length_le (F : ShaCompress) (d : Direction) (authKey : Bytes) :
    (V1State.encodeRaw (initV1State F d authKey).into_pb).length ≤ 512 := by
  have hauth := protoAuthenticator_encodeRaw_new_length_le F authKey
  have hep : (encodeUint64Field 1#32 1#64).length ≤ 10 := by decide
  have hdec :
      (encodeOptMessage PolynomialDecoder.encodeRaw 2#32
        (some (spqrPolyApi.decoder_into_pb initHdrDecoder))).length ≤ 100 := by decide
  cases d
  · change (encodeMessage V1State.Chunked.KeysUnsampled.encodeRaw 1#32
        { uc := some { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
            (Authenticator.new F authKey 1#64)) } }).length ≤ 512
    have h1 := encodeMessage_length_le V1State.Chunked.KeysUnsampled.encodeRaw 1#32
      { uc := some { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
          (Authenticator.new F authKey 1#64)) } }
    have h2 : (V1State.Chunked.KeysUnsampled.encodeRaw
        { uc := some { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
            (Authenticator.new F authKey 1#64)) } }).length ≤
        22 + (V1State.Unchunked.KeysUnsampled.encodeRaw
          { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
              (Authenticator.new F authKey 1#64)) }).length :=
      encodeMessage_length_le V1State.Unchunked.KeysUnsampled.encodeRaw 1#32 _
    have h3 : (V1State.Unchunked.KeysUnsampled.encodeRaw
        { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
            (Authenticator.new F authKey 1#64)) }).length ≤ 140 := by
      unfold V1State.Unchunked.KeysUnsampled.encodeRaw encodeOptMessage
      dsimp only
      simp only [List.length_append]
      have ha := encodeMessage_length_le ProtoAuthenticator.encodeRaw 2#32
        ((spqrAuthApi F).into_pb (Authenticator.new F authKey 1#64))
      omega
    omega
  · change (encodeMessage V1State.Chunked.NoHeaderReceived.encodeRaw 6#32
        { uc := some { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
            (Authenticator.new F authKey 1#64)) }
          receivingHdr := some (spqrPolyApi.decoder_into_pb initHdrDecoder) }).length ≤ 512
    have h1 := encodeMessage_length_le V1State.Chunked.NoHeaderReceived.encodeRaw 6#32
      { uc := some { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
          (Authenticator.new F authKey 1#64)) }
        receivingHdr := some (spqrPolyApi.decoder_into_pb initHdrDecoder) }
    have h2 : (V1State.Chunked.NoHeaderReceived.encodeRaw
        { uc := some { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
            (Authenticator.new F authKey 1#64)) }
          receivingHdr := some (spqrPolyApi.decoder_into_pb initHdrDecoder) }).length ≤ 262 := by
      unfold V1State.Chunked.NoHeaderReceived.encodeRaw
      simp only [List.length_append]
      have huc : (encodeOptMessage V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32
          (some { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
            (Authenticator.new F authKey 1#64)) })).length ≤
          22 + (V1State.Unchunked.NoHeaderReceived.encodeRaw
            { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
              (Authenticator.new F authKey 1#64)) }).length :=
        encodeMessage_length_le V1State.Unchunked.NoHeaderReceived.encodeRaw 1#32 _
      have h3 : (V1State.Unchunked.NoHeaderReceived.encodeRaw
          { epoch := 1#64, auth := some ((spqrAuthApi F).into_pb
            (Authenticator.new F authKey 1#64)) }).length ≤ 140 := by
        unfold V1State.Unchunked.NoHeaderReceived.encodeRaw encodeOptMessage
        dsimp only
        simp only [List.length_append]
        have ha := encodeMessage_length_le ProtoAuthenticator.encodeRaw 2#32
          ((spqrAuthApi F).into_pb (Authenticator.new F authKey 1#64))
        omega
      omega
    omega

/-- Bounded allocation envelope for `<spqr::authenticator::Authenticator>::new`:
    at most `24` non-`free` events of request size `≤ 2 * x.rootKey.length + 512` and
    alignment `≤ 16`. -/
def AuthNewBudgetEnv (x : AuthNewGhost) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 24 (2 * x.rootKey.length + 512) evs

theorem authNewBudgetEnv_nil (x : AuthNewGhost) : AuthNewBudgetEnv x [] :=
  SpqrBoundedEvs.nil 24 _

/-- Envelope-parametric budget specification of `<Authenticator>::new`. -/
def authNewBudgetSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (Env : AuthNewGhost → List AllocEvent → Prop) :
    Spec (AuthNewGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (Env x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8 A.repAlloc x.rkVecA x.rootKey ∗
      A.pool lim st s ∗ stackAt s.sp authNewStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      authenticatorAt A.repAlloc x.outA (Authenticator.new F x.rootKey 1#64) ∗
      memRegion x.rkVecA 24 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authNewStackX

/-- Bounded-envelope budget specification of `<Authenticator>::new`. -/
abbrev authNewBudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (AuthNewGhost × M.σ) :=
  authNewBudgetSpecOfEnv M A lim F AuthNewBudgetEnv

theorem fitsEvents_clone_of_initInnerEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {authKey : Bytes}
    (hpos : 0 < authKey.length)
    (hfit : FitsEnv M lim st (SpqrBoundedEvs 96 (2 * authKey.length + 2048))) :
    RustLayoutOk authKey.length 1 ∧ FitsEvents M lim st (rustAllocEvents authKey.length 1) := by
  have h48 := le_two_pow_48_of_fitsEnv_spqrBoundedEvs (n := authKey.length)
    (by decide) (by omega) hfit
  have hmax := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := authKey.length)
    (by decide) (by omega) hfit
  have hlay : RustLayoutOk authKey.length 1 :=
    ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hcl := spqrBoundedEvs_cloneEvs (authKey := authKey) hmax
  rw [cloneEvs_of_pos hpos] at hcl
  exact ⟨hlay, hfit _ (SpqrBoundedEvs.mono (by decide) (by omega) hcl)⟩

theorem spqrBoundedEvs_step12 {authKey : Bytes} {evs₂ : List AllocEvent}
    (hmax : authKey.length ≤ MallocngMaxAllocSize)
    (h2 : SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂) :
    SpqrBoundedEvs 25 (2 * authKey.length + 512) (cloneEvs authKey ++ evs₂) := by
  have h1 := spqrBoundedEvs_cloneEvs hmax
  exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append h1 h2)

theorem spqrBoundedEvs_step123 {F : ShaCompress} {d : Direction} {authKey : Bytes}
    {evs₂ evs₃ : List AllocEvent}
    (hmax : authKey.length ≤ MallocngMaxAllocSize)
    (h2 : SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂)
    (h3 : SpqrBoundedEvs 64 (2 * (V1State.encodeRaw (initV1State F d authKey).into_pb).length + 1024) evs₃) :
    SpqrBoundedEvs 96 (2 * authKey.length + 2048) ((cloneEvs authKey ++ evs₂) ++ evs₃) := by
  have h12 := spqrBoundedEvs_step12 hmax h2
  have henc := encodeRaw_initV1State_length_le F d authKey
  exact SpqrBoundedEvs.mono (by decide) (by omega) (SpqrBoundedEvs.append h12 h3)

theorem fitsEnv_auth_of_initInnerEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {x : AuthNewGhost}
    (hfit : FitsEnv M lim st (SpqrBoundedEvs 96 (2 * x.rootKey.length + 2048))) :
    FitsEnv M lim (M.stepEvents (cloneEvs x.rootKey) st) (AuthNewBudgetEnv x) := by
  have hmax := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := x.rootKey.length)
    (by decide) (by omega) hfit
  intro evs₂ h2
  have h12 : SpqrBoundedEvs 96 (2 * x.rootKey.length + 2048) (cloneEvs x.rootKey ++ evs₂) :=
    SpqrBoundedEvs.mono (by decide) (by omega) (spqrBoundedEvs_step12 hmax h2)
  exact ((fitsEvents_append M lim (cloneEvs x.rootKey) evs₂ st).mp (hfit _ h12)).2

theorem fitsEnv_statesIntoPb_of_initInnerEnv
    {M : AllocCostModel} {lim : BudgetLimits} {F : ShaCompress} {st : M.σ}
    {d : Direction} {authKey : Bytes} {evs₂ : List AllocEvent}
    (hfit : FitsEnv M lim st (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (h2 : SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂) :
    FitsEnv M lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st))
      (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw (initV1State F d authKey).into_pb).length + 1024)) := by
  have hmax := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := authKey.length)
    (by decide) (by omega) hfit
  intro evs₃ h3
  have h123 := spqrBoundedEvs_step123 (F := F) (d := d) hmax h2 h3
  have hf := (fitsEvents_append M lim (cloneEvs authKey ++ evs₂) evs₃ st).mp (hfit _ h123)
  rw [M.stepEvents_append] at hf
  exact hf.2

theorem statesIntoPbVariantPlacedSpec_of_statesIntoPbPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (statesIntoPbPlacedSpec M A lim F))
    (stateVal : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok P addr (statesIntoPbVariantPlacedSpec M A lim F stateVal) := by
  refine subroutine_ok_outcome_intro fun (⟨out, stA⟩, st) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (statesIntoPbPlacedSpec M A lim F).pre (⟨out, stA, stateVal⟩, st) s0 ∗ R :=
    hpre
  refine h.mono_outcome (⟨out, stA, stateVal⟩, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨c, hex_st, hex⟩ | ⟨hoom_st, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl ⟨hpan_st, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom⟩))

theorem withLsCodeLoaded_statesIntoPbVariantPlacedSpec_of_statesIntoPbPlacedSpec [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F)))
    (stateVal : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F stateVal)) := by
  refine subroutine_ok_outcome_intro fun (⟨out, stA⟩, st) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F)).pre (⟨out, stA, stateVal⟩, st) s0 ∗ R :=
    hpre
  refine h.mono_outcome (⟨out, stA, stateVal⟩, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨c, hex_st, hex⟩ | ⟨hoom_st, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl ⟨hpan_st, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom⟩))

/-! ## 2. Remaining `VmPreserved` Basic-Block & `BL` Steppers on `Block 324` -/

private theorem align_pre_tp {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Tp : State → Prop} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => Tp sm ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => Tp sm ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

private theorem sepWP_rebase_entails_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre Q : SepProp} {R : State → Prop}
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ Q) ∧ R sm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => (Pm ⊢ Q) ∧ VmPreserved s sm ∧ R sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hQ, hR⟩ => ⟨hQ, hvm, hR⟩

private theorem sepWP_rebase_strengthen_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {Pre Q Q' : SepProp} {R : State → Prop}
    (h : Q ⊢ Q')
    (hwp : SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ Q) ∧ R sm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => (Pm ⊢ Q') ∧ VmPreserved s sm ∧ R sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hvm, hQ, hR⟩ => ⟨Entails.trans hQ h, hvm, hR⟩

/-- `.b2a` non-empty slice step 3 (`+64 -> +80`, 4 instructions) on `Block 324`. -/
theorem init_inner_b2a_64_ok_to_80_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr len ptr : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_324).base + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = len)
    (hx21 : s.readReg64 .x21 = akPtr)
    (hx0 : s.readReg64 .x0 = ptr)
    (hptr_ne : (ptr == 0#64) = false)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 80#64) s
      (cells (s0.sp - 1032#64) 2 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ ((s0.sp - 1032#64) ↦₆₄ len) ∗ ((s0.sp - 1024#64) ↦₆₄ ptr) ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = len ∧
        s2.readReg64 .x0 = ptr ∧
        s2.readReg64 .x1 = akPtr ∧
        s2.readReg64 .x2 = len ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  refine sepWP_rebase_entails_vmPreserved ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  by_vm_steps (
    cells_unfold
    wp_pull_exists
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

/-- `.b2a` non-empty slice step 4 (`+84 -> +88 -> +184 -> +192`, 4 instructions) on `Block 324`. -/
theorem init_inner_b2a_84_to_192_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (out ptr : BitVec 64) (authKey : Bytes) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpos : 0 < authKey.length)
    (hlt : authKey.length < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hpc : s.pc = (blkPl_324).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧
      s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧
      s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧
      s.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      ((blkPl_324).base + 192#64) s
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       cells (s0.sp - 1016#64) 1 ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey) ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢ vecU8 A (s0.sp - 1032#64) authKey ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = s0.sp - 1040#64 ∧
        s2.readReg64 .x29 = s0.sp - 48#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x0 = s0.sp - 104#64 ∧
        s2.readReg64 .x1 = s0.sp - 1032#64 ∧
        (s2.readReg64 .x22 = s0.readReg64 .x22 ∧
         s2.readReg64 .x23 = s0.readReg64 .x23 ∧
         s2.readReg64 .x24 = s0.readReg64 .x24 ∧
         s2.readReg64 .x25 = s0.readReg64 .x25 ∧
         s2.readReg64 .x26 = s0.readReg64 .x26 ∧
         s2.readReg64 .x27 = s0.readReg64 .x27 ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.trace = s0.trace) := by
  have hvec :
      (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
       ((s0.sp - 1016#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
       A.live ptr authKey.length 1 ∗
       (ptr ↦ₛ authKey)) ∗ Rest ⊢
      vecU8 A (s0.sp - 1032#64) authKey ∗ Rest := by
    refine sepConj_mono_left ?_
    simpa only [arm64_norm] using vecU8_nonempty_of_cells A (s0.sp - 1032#64) ptr authKey hpos hlt hptr
  refine sepWP_rebase_strengthen_vmPreserved hvec ?_
  rcases hcs_hi with ⟨hx22, hx23, hx24, hx25, hx26, hx27, hvregs⟩
  by_vm_steps (
    cells_unfold
    wp_pull_exists
    wp_steps
    refine align_pre_tp (by sep_ac_rfl) ?_
    wp_done
  )

theorem init_inner_bl_128_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 128#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 132#64 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_140_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 140#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 144#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_160_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 160#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 164#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_48_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 48#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 52#64 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_60_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 60#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 64#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_80_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 80#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 84#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_364_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 364#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 368#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_192_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 192#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 196#64 ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

theorem init_inner_bl_412_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_324).base + 412#64) (hrun : s.status = .Running) :
    SepWP ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) s P
      (fun s' P1 => (P1 ⊢ P) ∧ VmPreserved s s' ∧ s'.sp = s.sp ∧
        s'.readReg64 .x30 = (blkPl_324).base + 416#64 ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧ s'.readReg64 .x0 = s.readReg64 .x0 ∧
        CalleeSavedPreserved s s' ∧ s'.trace = s.trace) := by
  wp_steps; wp_done

/-! ## 3. `SepWPp` Invariant-Preserving Combinators & Slice-Clone CPS (`Block 324`) -/

theorem sepWPp_of_sepWP_keepLsInv [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm =>
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sm.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl sm.mem) →
      SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext
      (fun hcl => hcl.of_keepsFrozen hsteps.keepsFrozen)
      (fun hinv => hinv.of_steps hsteps)
      R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem initInner_seq_sepWP_lsInv [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl s'.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl s'.mem) → Post s' →
      SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_of_sepWP_keepLsInv (mid := mid) ?_
  refine SepWP.mono hstep fun s' P1 hpc' hrun' ⟨hent, hpost⟩ hcode' hinv' =>
    SepWPp.weaken_pre hent (hnext s' hpc' hrun' hcode' hinv' hpost)

/-- Panic-free / OOM-free `SepWPp` subroutine call combinator preserving `LibsignalCodeLoaded`
    and `LsCallInv`. -/
theorem sepWPp_call_total_keepLsInv [LibsignalPlacement] {α : Type} {prog : Program}
    {caller_ret target ret_pc : BitVec 64} {spec : Spec α} (x : α)
    {s : State} {P Frame : SepProp} {Q Qp : State → SepProp → Prop}
    (hsub : subroutine_ok prog target spec)
    (hpc : s.pc = target)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : ∀ R', (s.mem ⊨ P ∗ R') → (s.mem ⊨ (spec.pre x s ∗ Frame) ∗ R'))
    (hexit : ∀ sf c, spec.onExit x c s sf = ⌜False⌝ := by
      intros; first | rfl | simp only [withLsCallInv, withLsCodeLoaded])
    (hpanic : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by
      intros; first | rfl | simp only [withLsCallInv, withLsCodeLoaded])
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intros; first | rfl | simp only [withLsCallInv, withLsCodeLoaded])
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl sf.mem) →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog caller_ret sf (spec.post x s sf ∗ Frame) Q Qp) :
    SepWPp prog caller_ret s P Q Qp := by
  refine sepWPp_of_sepWP_keepLsInv (mid := ret_pc) ?_
  refine SepWP.call_subroutine_frame hsub (x := x) (F := Frame)
    hpc hrun hsp_align hlr
    (fun R hm => by rw [← sepConj_assoc]; exact hpre R hm)
    (fun _ sf _ hp => by rw [hpanic sf] at hp; exact not_satisfies_false_sepConj hp)
    (fun _ code sf _ he => by rw [hexit sf code] at he; exact not_satisfies_false_sepConj he)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf =>
      SepWP.done hpc_sf hrun_sf fun hcode_sf hinv_sf =>
        hnext sf hpc_sf hrun_sf hcode_sf hinv_sf hsp_sf hcs_sf)
    (fun _ sf _ ho => by rw [hoom sf] at ho; exact (not_satisfies_false_sepConj ho).elim)

/-- Postcondition predicate of relocatable `spqr::init_inner` (`Block 324`) under `RustCliAllocBudget M`. -/
def InitInnerPlacedBudgetPost [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (s0 : State) (x : InitInnerGhost) (st0 : M.σ) : State → SepProp → Prop :=
  fun sf Pf =>
    (∃ evs : List AllocEvent,
      InitInnerEnv F x evs ∧
      (Pf ⊢
        initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
        (x.akPtr ↦ₛ x.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp initInnerStack)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

/-- Panic predicate for panic-free budget specs (`onPanic = ⌜False⌝`). -/
def InitInnerBudgetPanic (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)

theorem sepWPp_of_init_inner_placed_budget_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitInnerGhost) (st0 : M.σ) (P R : SepProp)
    (hwpp : SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (s0.readReg64 .x30) s P
      (InitInnerPlacedBudgetPost M A lim F s0 x st0) (InitInnerBudgetPanic R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (initInnerPlacedSpec M A lim F).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (initInnerPlacedSpec M A lim F).onPanic (x, st0) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, hevs, hent⟩, hspf, hcsf, htrf⟩⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    have hm' := Satisfies.mono (sepConj_mono_left hent) hmR
    dsimp only [initInnerPlacedSpec, initInnerPlacedSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htrf, hevs⟩, by simpa only [sepConj_assoc] using hm'⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun hmR => hqp hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem cells_1032_3_split_2_1 (sp : BitVec 64) :
    cells (sp - 1032#64) 3 = cells (sp - 1032#64) 2 ∗ cells (sp - 1016#64) 1 := by
  rw [← ProofLib.memRegion_cells (sp - 1032#64) 3 (by decide),
      ← ProofLib.memRegion_cells (sp - 1032#64) 2 (by decide),
      ← ProofLib.memRegion_cells (sp - 1016#64) 1 (by decide)]
  exact ProofLib.memRegion_split' (b := sp - 1032#64) (n := 16) (k := 8)
    (b' := sp - 1016#64) rfl (by bv_omega) (by decide)

theorem authenticatorAt_expose_budget_frame
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (sp : BitVec 64) (authKey : Bytes) (st' : M.σ) (sf : State)
    (Frame : SepProp) :
    (authenticatorAt A.repAlloc (sp - 104#64) (Authenticator.new F authKey 1#64) ∗
      memRegion (sp - 1032#64) 24 ∗ A.pool lim st' sf ∗ stackAt (sp - 1040#64) authNewStackX) ∗ Frame ⊢
    ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
    ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      (((((sp - 104#64) ↦₆₄ a0) ∗ ((sp - 96#64) ↦₆₄ a1) ∗ ((sp - 88#64) ↦₆₄ a2) ∗
         ((sp - 80#64) ↦₆₄ a3) ∗ ((sp - 72#64) ↦₆₄ a4) ∗ ((sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (sp - 1032#64) 24 ∗ A.pool lim st' sf ∗ stackAt (sp - 1040#64) authNewStackX) ∗ Frame) :=
  authenticatorAt_expose_frame (A.atState lim st' sf) F sp authKey Frame

/-- `.a2b` slice-clone (`+36 → +364`) on `Block 324`, advancing `st0` to
    `M.stepEvents (cloneEvs authKey) st0` without OOM. -/
theorem init_inner_clone_a2b_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (st0 : M.σ)
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2 : s.readReg32 .x2 = Direction.a2b.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hnext : ∀ s2 : State,
      s2.pc = (blkPl_324).base + 364#64 →
      s2.status = .Running →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl s2.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl s2.mem) →
      s2.sp = s0.sp - 1040#64 →
      s2.readReg64 .x29 = s0.sp - 48#64 →
      s2.readReg64 .x19 = out →
      s2.readReg64 .x0 = s0.sp - 104#64 →
      s2.readReg64 .x1 = s0.sp - 1032#64 →
      (s2.readReg64 .x22 = s0.readReg64 .x22 ∧ s2.readReg64 .x23 = s0.readReg64 .x23 ∧
       s2.readReg64 .x24 = s0.readReg64 .x24 ∧ s2.readReg64 .x25 = s0.readReg64 .x25 ∧
       s2.readReg64 .x26 = s0.readReg64 .x26 ∧ s2.readReg64 .x27 = s0.readReg64 .x27 ∧
       calleeSavedVRegs s2 = calleeSavedVRegs s0) →
      s2.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s2
        (vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s2 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases h0 : authKey.length = 0
  · rcases List.eq_nil_of_length_eq_zero h0 with rfl
    dsimp only [List.length_nil] at hx20
    refine initInner_seq_sepWP_lsInv
      (init_inner_a2b_empty_to_364_placed (A := A.repAlloc) s0 s out _
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htr) ?_
    intro s2 hpc2 hrun2 hcode2 hinv2 ⟨hvm2, hsp2, hx29_2, hx19_2, hx0_2, hx1_2, hcs2, htr2⟩
    have hpool :
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗ (akPtr ↦ₛ ([] : Bytes)) ∗
        A.pool lim (M.stepEvents (cloneEvs []) st0) s2 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
      rw [cloneEvs_of_length_zero rfl, M.stepEvents_nil, A.pool_of_vmPreserved hvm2]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool
      (hnext s2 hpc2 hrun2 hcode2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2)
  · have hpos : 0 < authKey.length := Nat.pos_of_ne_zero h0
    have ⟨hlay, hfits_cl⟩ := fitsEvents_clone_of_initInnerEnv hpos hfit
    have hlt64 : authKey.length < 2 ^ 64 := by omega
    have hlen_toNat : (BitVec.ofNat 64 authKey.length).toNat = authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    have hlen_ne : (BitVec.ofNat 64 authKey.length == 0#64) = false := by
      apply beq_false_of_ne
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hlen_toNat] at this
      change authKey.length = 0 at this
      omega
    refine initInner_seq_sepWP_lsInv
      (init_inner_a2b_to_128_placed s0 s out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc hrun hsp hx29 hx19 hx20 hlen_ne hw2 hx3 hcs_hi htr) ?_
    intro s1 hpc1 hrun1 hcode1 hinv1 ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hcs1, htr1⟩
    refine initInner_seq_sepWP_lsInv (init_inner_bl_128_placed s1 _ hpc1 hrun1) ?_
    intro s2 hpc2 hrun2 hcode2 hinv2 ⟨hvm2, hsp2, hlr2, hcs2, htr2⟩
    have hcs_hi2 := calleeSaved_chain_hi hcs1 hcs2
    have hx29_2 := calleeSaved_x29 hx29_1 hcs2
    have hx19_2 := calleeSaved_x19 hx19_1 hcs2
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs2.2.1, hx20_1]
    have hx21_2 : s2.readReg64 .x21 = akPtr := by rw [hcs2.2.2.1, hx21_1]
    refine sepWPp_call_total_keepLsInv () hshim hpc2 hrun2
      (by rw [State.spAligned, hsp2, hsp1]; exact hfsp_align) hlr2
      (fun R' hm => by
        dsimp only [noAllocShimBudgetSpec]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
      (hnext := fun s3 hpc3 hrun3 hcode3 hinv3 hsp3 hcs3 => ?_)
    dsimp only [noAllocShimBudgetSpec]
    refine SepWPp.pure_left fun ⟨htr3, hvm3⟩ => ?_
    have hcs_hi3 := calleeSaved_chain_hi hcs_hi2 hcs3
    have hx29_3 := calleeSaved_x29 hx29_2 hcs3
    have hx19_3 := calleeSaved_x19 hx19_2 hcs3
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs3.2.1, hx20_2]
    have hx21_3 : s3.readReg64 .x21 = akPtr := by rw [hcs3.2.2.1, hx21_2]
    refine initInner_seq_sepWP_lsInv
      (init_inner_a2b_132_to_140_placed s0 s3 out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]) hx29_3 hx19_3 hx20_3 hx21_3 hcs_hi3
        (by rw [htr3, htr2, htr1])) ?_
    intro s4 hpc4 hrun4 hcode4 hinv4 ⟨hvm4, hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx0_4, hx1_4, hcs4, htr4⟩
    refine initInner_seq_sepWP_lsInv (init_inner_bl_140_placed s4 _ hpc4 hrun4) ?_
    intro s5 hpc5 hrun5 hcode5 hinv5 ⟨hvm5, hsp5, hlr5, hx0_5, hx1_5, hcs5, htr5⟩
    have hcs_hi5 := calleeSaved_chain_hi hcs4 hcs5
    have hx29_5 := calleeSaved_x29 hx29_4 hcs5
    have hx19_5 := calleeSaved_x19 hx19_4 hcs5
    have hx20_5 : s5.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs5.2.1, hx20_4]
    have hx21_5 : s5.readReg64 .x21 = akPtr := by rw [hcs5.2.2.1, hx21_4]
    have hvm_0_5 : VmPreserved s s5 :=
      hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans hvm5)))
    have hpre_alloc :
        cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
        A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame ⊢
        (A.pool lim st0 s5 ∗ stackAt s5.sp allocHookStack) ∗
        (cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame) := by
      rw [cells_1032_3_split_2_1 s0.sp, hsp5, hsp4, ← A.pool_of_vmPreserved hvm_0_5]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_alloc ?_
    refine sepWPp_call_total_keepLsInv (authKey.length, 1, st0)
      (Frame := cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame)
      halloc hpc5 hrun5
      (by rw [State.spAligned, hsp5, hsp4]; exact hfsp_align) hlr5
      (fun R' hm => by
        dsimp only [rustCliAllocNoOomSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        refine ⟨⟨?_, ?_, hlay, hfits_cl, ?_⟩, hm⟩
        · rw [hx0_5, hx0_4, hlen_toNat]
        · rw [hx1_5, hx1_4]; rfl
        · rw [show s5.readReg64 .lr = _ from hlr5]
          simp (config := { decide := true }) only [blkPl_324, wp_norm, arm64_norm])
      (hnext := fun s6 hpc6 hrun6 hcode6 hinv6 hsp6 hcs6 => ?_)
    dsimp only [rustCliAllocNoOomSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hpres6, hptr_ne0, _⟩ => ?_
    have hcs_hi6 := calleeSaved_chain_hi hcs_hi5 hcs6
    have hx29_6 := calleeSaved_x29 hx29_5 hcs6
    have hx19_6 := calleeSaved_x19 hx19_5 hcs6
    have hx20_6 : s6.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs6.2.1, hx20_5]
    have hx21_6 : s6.readReg64 .x21 = akPtr := by rw [hcs6.2.2.1, hx21_5]
    let ptr := s6.readReg64 .x0
    have hptr_beq : (ptr == 0#64) = false := beq_false_of_ne hptr_ne0
    have hre6 :
        (A.pool lim (M.stepEvents (rustAllocEvents authKey.length 1) st0) s6 ∗
         stackAt s5.sp allocHookStack ∗ A.live ptr authKey.length 1 ∗
         memRegion ptr authKey.length) ∗
        (cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame) ⊢
        cells (s0.sp - 1032#64) 2 ∗
        (memRegion ptr authKey.length ∗ (akPtr ↦ₛ authKey) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s6 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) := by
      rw [cloneEvs_of_pos hpos, hsp5, hsp4]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hre6 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_a2b_144_ok_to_160_placed s0 s6 out akPtr (BitVec.ofNat 64 authKey.length) ptr _
        hsp0_align hpc6 hrun6 (by rw [hsp6, hsp5, hsp4]) hx29_6 hx19_6 hx20_6 hx21_6
        rfl hptr_beq hcs_hi6 (by rw [hpres6.2.1, htr5, htr4])) ?_
    intro s7 hpc7 hrun7 hcode7 hinv7 ⟨hvm7, hsp7, hx29_7, hx19_7, hx20_7, hx0_7, hx1_7, hx2_7, hcs7, htr7⟩
    refine initInner_seq_sepWP_lsInv (init_inner_bl_160_placed s7 _ hpc7 hrun7) ?_
    intro s8 hpc8 hrun8 hcode8 hinv8 ⟨hvm8, hsp8, hlr8, hx0_8, hx1_8, hx2_8, hcs8, htr8⟩
    have hcs_hi8 := calleeSaved_chain_hi hcs7 hcs8
    have hx29_8 := calleeSaved_x29 hx29_7 hcs8
    have hx19_8 := calleeSaved_x19 hx19_7 hcs8
    have hx20_8 : s8.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs8.2.1, hx20_7]
    have hvm_6_8 : VmPreserved s6 s8 := hvm7.trans hvm8
    have hpre_mc :
        ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        (memRegion ptr authKey.length ∗ (akPtr ↦ₛ authKey) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s6 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        (memRegion ptr authKey.length ∗ (akPtr ↦ₛ authKey)) ∗
        (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
         ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) := by
      rw [← A.pool_of_vmPreserved hvm_6_8]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_mc ?_
    refine sepWPp_call_total_keepLsInv (ptr, akPtr, authKey)
      (Frame := ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
        A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      hmemcpy hpc8 hrun8
      (by rw [State.spAligned, hsp8, hsp7]; exact hfsp_align) hlr8
      (fun R' hm => by
        dsimp only [framelessMemcpyBudgetSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        exact ⟨⟨by rw [hx0_8, hx0_7], by rw [hx1_8, hx1_7], by rw [hx2_8, hx2_7, hlen_toNat]⟩, hm⟩)
      (hnext := fun s9 hpc9 hrun9 hcode9 hinv9 hsp9 hcs9 => ?_)
    dsimp only [framelessMemcpyBudgetSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr9, hvm9⟩ => ?_
    have hcs_hi9 := calleeSaved_chain_hi hcs_hi8 hcs9
    have hx29_9 := calleeSaved_x29 hx29_8 hcs9
    have hx19_9 := calleeSaved_x19 hx19_8 hcs9
    have hx20_9 : s9.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs9.2.1, hx20_8]
    have hre9 :
        ((ptr ↦ₛ authKey) ∗ (akPtr ↦ₛ authKey)) ∗
        (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
         ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        cells (s0.sp - 1016#64) 1 ∗ A.repAlloc.live ptr authKey.length 1 ∗
        (ptr ↦ₛ authKey) ∗
        ((akPtr ↦ₛ authKey) ∗ A.pool lim (M.stepEvents (cloneEvs authKey) st0) s9 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) := by
      rw [← A.pool_of_vmPreserved hvm9]
      change _ ⊢ ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗ cells (s0.sp - 1016#64) 1 ∗
        A.live ptr authKey.length 1 ∗ (ptr ↦ₛ authKey) ∗
        ((akPtr ↦ₛ authKey) ∗ A.pool lim (M.stepEvents (cloneEvs authKey) st0) s9 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hre9 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_a2b_164_to_364_placed (A := A.repAlloc) s0 s9 out ptr authKey _
        hsp0_align hpos hlt hptr_ne0 hpc9 hrun9 (by rw [hsp9, hsp8, hsp7])
        hx29_9 hx19_9 hx20_9 hcs_hi9 (by rw [htr9, htr8, htr7])) ?_
    intro s10 hpc10 hrun10 hcode10 hinv10 ⟨hvm10, hsp10, hx29_10, hx19_10, hx0_10, hx1_10, hcs10, htr10⟩
    have hpool10 :
        vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
        ((akPtr ↦ₛ authKey) ∗ A.pool lim (M.stepEvents (cloneEvs authKey) st0) s9 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
        A.pool lim (M.stepEvents (cloneEvs authKey) st0) s10 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
      rw [A.pool_of_vmPreserved hvm10]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool10
      (hnext s10 hpc10 hrun10
        (fun h => hcode10 (hcode9 (hcode8 (hcode7 (hcode6 (hcode5 (hcode4 (hcode3 (hcode2 (hcode1 h))))))))))
        (fun h => hinv10 (hinv9 (hinv8 (hinv7 (hinv6 (hinv5 (hinv4 (hinv3 (hinv2 (hinv1 h))))))))))
        hsp10 hx29_10 hx19_10 hx0_10 hx1_10 hcs10 htr10)

/-- `.b2a` slice-clone (`+36 → +192`) on `Block 324`, advancing `st0` to
    `M.stepEvents (cloneEvs authKey) st0` without OOM. -/
theorem init_inner_clone_b2a_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (st0 : M.σ)
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hpc : s.pc = (blkPl_324).base + 36#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 48#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2 : s.readReg32 .x2 = Direction.b2a.toI32)
    (hx3 : s.readReg64 .x3 = akPtr)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hnext : ∀ s2 : State,
      s2.pc = (blkPl_324).base + 192#64 →
      s2.status = .Running →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl s2.mem) →
      (LsCallInv lsmpl s.mem → LsCallInv lsmpl s2.mem) →
      s2.sp = s0.sp - 1040#64 →
      s2.readReg64 .x29 = s0.sp - 48#64 →
      s2.readReg64 .x19 = out →
      s2.readReg64 .x0 = s0.sp - 104#64 →
      s2.readReg64 .x1 = s0.sp - 1032#64 →
      (s2.readReg64 .x22 = s0.readReg64 .x22 ∧ s2.readReg64 .x23 = s0.readReg64 .x23 ∧
       s2.readReg64 .x24 = s0.readReg64 .x24 ∧ s2.readReg64 .x25 = s0.readReg64 .x25 ∧
       s2.readReg64 .x26 = s0.readReg64 .x26 ∧ s2.readReg64 .x27 = s0.readReg64 .x27 ∧
       calleeSavedVRegs s2 = calleeSavedVRegs s0) →
      s2.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s2
        (vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s2 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases h0 : authKey.length = 0
  · rcases List.eq_nil_of_length_eq_zero h0 with rfl
    dsimp only [List.length_nil] at hx20
    refine initInner_seq_sepWP_lsInv
      (init_inner_b2a_empty_to_192_placed (A := A.repAlloc) s0 s out _
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htr) ?_
    intro s2 hpc2 hrun2 hcode2 hinv2 ⟨hvm2, hsp2, hx29_2, hx19_2, hx0_2, hx1_2, hcs2, htr2⟩
    have hpool :
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗ (akPtr ↦ₛ ([] : Bytes)) ∗
        A.pool lim (M.stepEvents (cloneEvs []) st0) s2 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
      rw [cloneEvs_of_length_zero rfl, M.stepEvents_nil, A.pool_of_vmPreserved hvm2]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool
      (hnext s2 hpc2 hrun2 hcode2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2)
  · have hpos : 0 < authKey.length := Nat.pos_of_ne_zero h0
    have ⟨hlay, hfits_cl⟩ := fitsEvents_clone_of_initInnerEnv hpos hfit
    have hlt64 : authKey.length < 2 ^ 64 := by omega
    have hlen_toNat : (BitVec.ofNat 64 authKey.length).toNat = authKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
    have hlen_ne : (BitVec.ofNat 64 authKey.length == 0#64) = false := by
      apply beq_false_of_ne
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hlen_toNat] at this
      change authKey.length = 0 at this
      omega
    refine initInner_seq_sepWP_lsInv
      (init_inner_b2a_to_48_placed s0 s out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc hrun hsp hx29 hx19 hx20 hlen_ne hw2 hx3 hcs_hi htr) ?_
    intro s1 hpc1 hrun1 hcode1 hinv1 ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hcs1, htr1⟩
    refine initInner_seq_sepWP_lsInv (init_inner_bl_48_placed s1 _ hpc1 hrun1) ?_
    intro s2 hpc2 hrun2 hcode2 hinv2 ⟨hvm2, hsp2, hlr2, hcs2, htr2⟩
    have hcs_hi2 := calleeSaved_chain_hi hcs1 hcs2
    have hx29_2 := calleeSaved_x29 hx29_1 hcs2
    have hx19_2 := calleeSaved_x19 hx19_1 hcs2
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs2.2.1, hx20_1]
    have hx21_2 : s2.readReg64 .x21 = akPtr := by rw [hcs2.2.2.1, hx21_1]
    refine sepWPp_call_total_keepLsInv () hshim hpc2 hrun2
      (by rw [State.spAligned, hsp2, hsp1]; exact hfsp_align) hlr2
      (fun R' hm => by
        dsimp only [noAllocShimBudgetSpec]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
      (hnext := fun s3 hpc3 hrun3 hcode3 hinv3 hsp3 hcs3 => ?_)
    dsimp only [noAllocShimBudgetSpec]
    refine SepWPp.pure_left fun ⟨htr3, hvm3⟩ => ?_
    have hcs_hi3 := calleeSaved_chain_hi hcs_hi2 hcs3
    have hx29_3 := calleeSaved_x29 hx29_2 hcs3
    have hx19_3 := calleeSaved_x19 hx19_2 hcs3
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs3.2.1, hx20_2]
    have hx21_3 : s3.readReg64 .x21 = akPtr := by rw [hcs3.2.2.1, hx21_2]
    refine initInner_seq_sepWP_lsInv
      (init_inner_b2a_52_to_60_placed s0 s3 out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]) hx29_3 hx19_3 hx20_3 hx21_3 hcs_hi3
        (by rw [htr3, htr2, htr1])) ?_
    intro s4 hpc4 hrun4 hcode4 hinv4 ⟨hvm4, hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx0_4, hx1_4, hcs4, htr4⟩
    refine initInner_seq_sepWP_lsInv (init_inner_bl_60_placed s4 _ hpc4 hrun4) ?_
    intro s5 hpc5 hrun5 hcode5 hinv5 ⟨hvm5, hsp5, hlr5, hx0_5, hx1_5, hcs5, htr5⟩
    have hcs_hi5 := calleeSaved_chain_hi hcs4 hcs5
    have hx29_5 := calleeSaved_x29 hx29_4 hcs5
    have hx19_5 := calleeSaved_x19 hx19_4 hcs5
    have hx20_5 : s5.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs5.2.1, hx20_4]
    have hx21_5 : s5.readReg64 .x21 = akPtr := by rw [hcs5.2.2.1, hx21_4]
    have hvm_0_5 : VmPreserved s s5 :=
      hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans hvm5)))
    have hpre_alloc :
        cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
        A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame ⊢
        (A.pool lim st0 s5 ∗ stackAt s5.sp allocHookStack) ∗
        (cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame) := by
      rw [cells_1032_3_split_2_1 s0.sp, hsp5, hsp4, ← A.pool_of_vmPreserved hvm_0_5]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_alloc ?_
    refine sepWPp_call_total_keepLsInv (authKey.length, 1, st0)
      (Frame := cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame)
      halloc hpc5 hrun5
      (by rw [State.spAligned, hsp5, hsp4]; exact hfsp_align) hlr5
      (fun R' hm => by
        dsimp only [rustCliAllocNoOomSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        refine ⟨⟨?_, ?_, hlay, hfits_cl, ?_⟩, hm⟩
        · rw [hx0_5, hx0_4, hlen_toNat]
        · rw [hx1_5, hx1_4]; rfl
        · rw [show s5.readReg64 .lr = _ from hlr5]
          simp (config := { decide := true }) only [blkPl_324, wp_norm, arm64_norm])
      (hnext := fun s6 hpc6 hrun6 hcode6 hinv6 hsp6 hcs6 => ?_)
    dsimp only [rustCliAllocNoOomSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hpres6, hptr_ne0, _⟩ => ?_
    have hcs_hi6 := calleeSaved_chain_hi hcs_hi5 hcs6
    have hx29_6 := calleeSaved_x29 hx29_5 hcs6
    have hx19_6 := calleeSaved_x19 hx19_5 hcs6
    have hx20_6 : s6.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs6.2.1, hx20_5]
    have hx21_6 : s6.readReg64 .x21 = akPtr := by rw [hcs6.2.2.1, hx21_5]
    let ptr := s6.readReg64 .x0
    have hptr_beq : (ptr == 0#64) = false := beq_false_of_ne hptr_ne0
    have hre6 :
        (A.pool lim (M.stepEvents (rustAllocEvents authKey.length 1) st0) s6 ∗
         stackAt s5.sp allocHookStack ∗ A.live ptr authKey.length 1 ∗
         memRegion ptr authKey.length) ∗
        (cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame) ⊢
        cells (s0.sp - 1032#64) 2 ∗
        (memRegion ptr authKey.length ∗ (akPtr ↦ₛ authKey) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s6 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) := by
      rw [cloneEvs_of_pos hpos, hsp5, hsp4]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hre6 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_b2a_64_ok_to_80_placed s0 s6 out akPtr (BitVec.ofNat 64 authKey.length) ptr _
        hsp0_align hpc6 hrun6 (by rw [hsp6, hsp5, hsp4]) hx29_6 hx19_6 hx20_6 hx21_6
        rfl hptr_beq hcs_hi6 (by rw [hpres6.2.1, htr5, htr4])) ?_
    intro s7 hpc7 hrun7 hcode7 hinv7 ⟨hvm7, hsp7, hx29_7, hx19_7, hx20_7, hx0_7, hx1_7, hx2_7, hcs7, htr7⟩
    refine initInner_seq_sepWP_lsInv (init_inner_bl_80_placed s7 _ hpc7 hrun7) ?_
    intro s8 hpc8 hrun8 hcode8 hinv8 ⟨hvm8, hsp8, hlr8, hx0_8, hx1_8, hx2_8, hcs8, htr8⟩
    have hcs_hi8 := calleeSaved_chain_hi hcs7 hcs8
    have hx29_8 := calleeSaved_x29 hx29_7 hcs8
    have hx19_8 := calleeSaved_x19 hx19_7 hcs8
    have hx20_8 : s8.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs8.2.1, hx20_7]
    have hvm_6_8 : VmPreserved s6 s8 := hvm7.trans hvm8
    have hpre_mc :
        ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        (memRegion ptr authKey.length ∗ (akPtr ↦ₛ authKey) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s6 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        (memRegion ptr authKey.length ∗ (akPtr ↦ₛ authKey)) ∗
        (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
         ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) := by
      rw [← A.pool_of_vmPreserved hvm_6_8]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_mc ?_
    refine sepWPp_call_total_keepLsInv (ptr, akPtr, authKey)
      (Frame := ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
        A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      hmemcpy hpc8 hrun8
      (by rw [State.spAligned, hsp8, hsp7]; exact hfsp_align) hlr8
      (fun R' hm => by
        dsimp only [framelessMemcpyBudgetSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        exact ⟨⟨by rw [hx0_8, hx0_7], by rw [hx1_8, hx1_7], by rw [hx2_8, hx2_7, hlen_toNat]⟩, hm⟩)
      (hnext := fun s9 hpc9 hrun9 hcode9 hinv9 hsp9 hcs9 => ?_)
    dsimp only [framelessMemcpyBudgetSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr9, hvm9⟩ => ?_
    have hcs_hi9 := calleeSaved_chain_hi hcs_hi8 hcs9
    have hx29_9 := calleeSaved_x29 hx29_8 hcs9
    have hx19_9 := calleeSaved_x19 hx19_8 hcs9
    have hx20_9 : s9.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs9.2.1, hx20_8]
    have hre9 :
        ((ptr ↦ₛ authKey) ∗ (akPtr ↦ₛ authKey)) ∗
        (((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
         ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
         cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        cells (s0.sp - 1016#64) 1 ∗ A.repAlloc.live ptr authKey.length 1 ∗
        (ptr ↦ₛ authKey) ∗
        ((akPtr ↦ₛ authKey) ∗ A.pool lim (M.stepEvents (cloneEvs authKey) st0) s9 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) := by
      rw [← A.pool_of_vmPreserved hvm9]
      change _ ⊢ ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗ cells (s0.sp - 1016#64) 1 ∗
        A.live ptr authKey.length 1 ∗ (ptr ↦ₛ authKey) ∗
        ((akPtr ↦ₛ authKey) ∗ A.pool lim (M.stepEvents (cloneEvs authKey) st0) s9 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hre9 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_b2a_84_to_192_placed (A := A.repAlloc) s0 s9 out ptr authKey _
        hsp0_align hpos hlt hptr_ne0 hpc9 hrun9 (by rw [hsp9, hsp8, hsp7])
        hx29_9 hx19_9 hx20_9 hcs_hi9 (by rw [htr9, htr8, htr7])) ?_
    intro s10 hpc10 hrun10 hcode10 hinv10 ⟨hvm10, hsp10, hx29_10, hx19_10, hx0_10, hx1_10, hcs10, htr10⟩
    have hpool10 :
        vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
        ((akPtr ↦ₛ authKey) ∗ A.pool lim (M.stepEvents (cloneEvs authKey) st0) s9 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
        A.pool lim (M.stepEvents (cloneEvs authKey) st0) s10 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
      rw [A.pool_of_vmPreserved hvm10]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool10
      (hnext s10 hpc10 hrun10
        (fun h => hcode10 (hcode9 (hcode8 (hcode7 (hcode6 (hcode5 (hcode4 (hcode3 (hcode2 (hcode1 h))))))))))
        (fun h => hinv10 (hinv9 (hinv8 (hinv7 (hinv6 (hinv5 (hinv4 (hinv3 (hinv2 (hinv1 h))))))))))
        hsp10 hx29_10 hx19_10 hx0_10 hx1_10 hcs10 htr10)

/-! ## 4. Relocatable Callee Wrappers (`<Authenticator>::new` & `<States>::into_pb`) & Body -/

/-- Abstract budget-threaded call interface for `<Authenticator>::new` at `lsmpl.base 340` on `Block 324`. -/
def AuthBudgetCallAtPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (s0 : State) (authKey : Bytes) (st1 : M.σ)
    (Q : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (s : State) (ret_pc : BitVec 64) (P Frame : SepProp),
    (LsCallInv lsmpl s0.mem → LsCallInv lsmpl s.mem) →
    s.pc = lsmpl.base 340 →
    s.status = .Running → s.sp = s0.sp - 1040#64 →
    s.readReg64 .x30 = ret_pc → LsRetAddr624 ret_pc → s.trace = s0.trace →
    s.readReg64 .x0 = s0.sp - 104#64 → s.readReg64 .x1 = s0.sp - 1032#64 →
    FitsEnv M lim st1 (AuthNewBudgetEnv ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) →
    P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
      A.pool lim st1 s ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame →
    (∀ (sf : State) (evs₂ : List AllocEvent) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂ →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗
          A.pool lim (M.stepEvents evs₂ st1) sf ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerBudgetPanic R)) →
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q
      (InitInnerBudgetPanic R)

theorem call_authNew_budget_placed_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewBudgetSpec M A lim F))
    (authKey : Bytes) (st1 : M.σ) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp)
    (hpc : s.pc = lsmpl.base 340)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = s0.sp - 104#64) (hx1 : s.readReg64 .x1 = s0.sp - 1032#64)
    (hfit1 : FitsEnv M lim st1 (AuthNewBudgetEnv ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩))
    (hsplit : P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
      A.pool lim st1 s ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
    (hnext : ∀ (sf : State) (evs₂ : List AllocEvent) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂ →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗
          A.pool lim (M.stepEvents evs₂ st1) sf ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerBudgetPanic R))
    (hlr_ls : LsRetAddr624 ret_pc := by
      simp (config := { decide := true }) only [blkPl_324, wp_norm, arm64_norm]) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q
      (InitInnerBudgetPanic R) := by
  refine sepWPp_call_total_keepLsInv (⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩, st1)
    hauth_raw hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit] at hm
      dsimp only [authNewBudgetSpec, authNewBudgetSpecOfEnv]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      have hlr624 : LsRetAddr624 (s.readReg64 .lr) := by
        simpa only [show s.readReg64 .lr = ret_pc from hlr] using hlr_ls
      exact ⟨⟨hx0, hx1, hlt, hfit1, hlr624⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf hcode_sf _ hsp_sf hcs_sf => ?_)
  dsimp only [authNewBudgetSpec, authNewBudgetSpecOfEnv]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₂ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr_sf, hevs₂⟩ => ?_
  refine SepWPp.weaken_pre
    (authenticatorAt_expose_budget_frame A lim F s0.sp authKey _ sf Frame) ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
  exact hnext sf evs₂ a0 a1 a2 a3 a4 a5 hpc_sf hrun_sf
    (by rw [hsp_sf, hsp]) hcode_sf hcs_sf (by rw [htr_sf, htrace]) hevs₂

theorem call_authNew_budget_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewBudgetSpec M A lim F)))
    (authKey : Bytes) (st1 : M.σ) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp) (hinv : LsCallInv lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 340)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = s0.sp - 104#64) (hx1 : s.readReg64 .x1 = s0.sp - 1032#64)
    (hfit1 : FitsEnv M lim st1 (AuthNewBudgetEnv ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩))
    (hsplit : P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
      A.pool lim st1 s ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
    (hnext : ∀ (sf : State) (evs₂ : List AllocEvent) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      (LibsignalCodeLoaded lsmpl s.mem → LibsignalCodeLoaded lsmpl sf.mem) →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂ →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗
          A.pool lim (M.stepEvents evs₂ st1) sf ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerBudgetPanic R))
    (hlr_ls : LsRetAddr624 ret_pc := by
      simp (config := { decide := true }) only [blkPl_324, wp_norm, arm64_norm]) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q
      (InitInnerBudgetPanic R) := by
  refine sepWPp_call_total_keepLsInv (⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩, st1)
    hauth_raw hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit] at hm
      dsimp only [withLsCallInv, authNewBudgetSpec, authNewBudgetSpecOfEnv]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      have hlr624 : LsRetAddr624 (s.readReg64 .lr) := by
        simpa only [show s.readReg64 .lr = ret_pc from hlr] using hlr_ls
      exact ⟨hinv, ⟨hx0, hx1, hlt, hfit1, hlr624⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf hcode_sf _ hsp_sf hcs_sf => ?_)
  dsimp only [withLsCallInv, authNewBudgetSpec, authNewBudgetSpecOfEnv]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₂ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr_sf, hevs₂⟩ => ?_
  refine SepWPp.weaken_pre
    (authenticatorAt_expose_budget_frame A lim F s0.sp authKey _ sf Frame) ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
  exact hnext sf evs₂ a0 a1 a2 a3 a4 a5 hpc_sf hrun_sf
    (by rw [hsp_sf, hsp]) hcode_sf hcs_sf (by rw [htr_sf, htrace]) hevs₂

/-- Abstract budget-threaded call interface for `<States>::into_pb` at `lsmpl.base 334` on `Block 324`. -/
def IntoPbBudgetCallAtPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (s0 : State) (out : BitVec 64) (d : Direction) (authKey : Bytes)
    (Q : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (s : State) (st2 : M.σ) (ret_pc : BitVec 64) (P Frame : SepProp),
    (LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s.mem) →
    s.pc = lsmpl.base 334 →
    s.status = .Running → s.sp = s0.sp - 1040#64 →
    s.readReg64 .x30 = ret_pc → s.trace = s0.trace →
    s.readReg64 .x8 = out → s.readReg64 .x0 = s0.sp - 1032#64 →
    FitsEnv M lim st2
      (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw (initV1State F d authKey).into_pb).length + 1024)) →
    P = (memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F d authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st2 s ∗
      stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame →
    (∀ (sf : State) (evs₃ : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 64
        (2 * (V1State.encodeRaw (initV1State F d authKey).into_pb).length + 1024) evs₃ →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A.repAlloc out (initV1State F d authKey).into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₃ st2) sf ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
        Q (InitInnerBudgetPanic R)) →
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q
      (InitInnerBudgetPanic R)

theorem call_statesIntoPb_variant_placed_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    {stateVal : States spqrPolyApi (spqrAuthApi F)}
    (hinto_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F stateVal)))
    (out : BitVec 64) (st2 : M.σ)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 334)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hfit2 : FitsEnv M lim st2
      (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024)))
    (hsplit : P = (memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) stateVal ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool lim st2 s ∗
      stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs₃ : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024) evs₃ →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₃ st2) sf ∗ stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q
      (InitInnerBudgetPanic R) := by
  refine sepWPp_call_total_keepLsInv (⟨out, s0.sp - 1032#64⟩, st2) (Frame := Frame)
    hinto_raw hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit] at hm
      dsimp only [withLsCodeLoaded, statesIntoPbVariantPlacedSpec,
        statesIntoPbVariantPlacedSpecOfEnv]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      refine ⟨⟨hx8, hx0, hfit2⟩, ?_⟩
      apply Satisfies.mono (P := ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        (memRegion out optProtoInnerStateSize ∗
          chunkedStatesAt A.repAlloc (s0.sp - 1032#64) stateVal ∗
          statesIntoPbJumpTablePlacedAt ∗ A.pool lim st2 s ∗
          stackAt (s0.sp - 1040#64) statesIntoPbStack ∗ Frame ∗ R'))
        (Entails.of_eq (by sep_ac_rfl))
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ _ hsp_sf hcs_sf => ?_)
  dsimp only [withLsCodeLoaded, statesIntoPbVariantPlacedSpec, statesIntoPbVariantPlacedSpecOfEnv]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₃ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr_sf, hevs₃⟩ => ?_
  exact hnext sf evs₃ hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr_sf, htrace]) hevs₃

/-- Shared tail from `+412` on `Block 324`: `bl <States>::into_pb` + epilogue. -/
theorem init_inner_from_412_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr : BitVec 64) (d : Direction) (authKey : Bytes)
    (st0 : M.σ) (evs₂ : List AllocEvent) (R : SepProp)
    (hcall_into : IntoPbBudgetCallAtPlaced M A lim F ext s0 out d authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, d, akPtr, authKey⟩ st0) R)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcode : LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s.mem)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hevs₂ : SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂)
    (hpc : s.pc = (blkPl_324).base + 412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx8 : s.readReg64 .x8 = out)
    (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hcs_hi :
      s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
      s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
      s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F d authKey) ∗
       memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s)
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, d, akPtr, authKey⟩ st0)
      (InitInnerBudgetPanic R) := by
  have hmax := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := authKey.length)
    (by decide) (by omega) hfit
  have hfit2 := fitsEnv_statesIntoPb_of_initInnerEnv (F := F) (d := d) hfit hevs₂
  refine initInner_seq_sepWP_lsInv (init_inner_bl_412_placed s _ hpc hrun) ?_
  intro s1 hpc1 hrun1 hcode1 _ ⟨hvm1, hsp1, hlr1, hx8_1, hx0_1, hcs1, htr1⟩
  have hcs_hi1 := calleeSaved_chain_hi hcs_hi hcs1
  have hsplit_pb :
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F d authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s =
      (memRegion out optProtoInnerStateSize ∗
       chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F d authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s1 ∗
       stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 10768 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) := by
    rw [stackAt_authNew_split_statesIntoPb (s0.sp - 1040#64), ← A.pool_of_vmPreserved hvm1]
    sep_ac_rfl
  refine hcall_into s1 (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0))
    ((blkPl_324).base + 416#64) _ _
    (fun hc0 => hcode1 (hcode hc0)) hpc1 hrun1 (hsp1.trans hsp) hlr1 (htr1.trans htr)
    (hx8_1.trans hx8) (hx0_1.trans hx0) hfit2 hsplit_pb ?_
  intro s2 evs₃ hpc2 hrun2 hsp2 hcs2 htr2 hevs₃
  have hcs_hi2 := calleeSaved_chain_hi hcs_hi1 hcs2
  let evs_tot := (cloneEvs authKey ++ evs₂) ++ evs₃
  have hevs_tot : SpqrBoundedEvs 96 (2 * authKey.length + 2048) evs_tot :=
    spqrBoundedEvs_step123 (F := F) (d := d) hmax hevs₂ hevs₃
  have hstep_eq :
      M.stepEvents evs₃ (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) =
        M.stepEvents evs_tot st0 := by
    dsimp only [evs_tot]
    rw [M.stepEvents_append, M.stepEvents_append]
  have hrejoin_ep :
      (optProtoInnerStateAt A.repAlloc out (initV1State F d authKey).into_pb.innerState ∗
       memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs₃ (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0))) s2 ∗
       stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 10768 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) ⊢
      stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992 ∗
      initInnerSavedCells s0 ∗
      (initInnerResultAt A.repAlloc (F := F) out .v1 d authKey ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs_tot st0) s2) := by
    dsimp only [initInnerResultAt]
    rw [hstep_eq, ← memRegion_992_rejoin_b2a s0.sp,
      stackAt_authNew_split_statesIntoPb (s0.sp - 1040#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hrejoin_ep ?_
  refine initInner_seq_sepWP_lsInv
    (init_inner_epilogue_placed s0 s2
      (initInnerResultAt A.repAlloc (F := F) out .v1 d authKey ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs_tot st0) s2)
      hsp0_align hpc2 hrun2 hsp2 hcs_hi2 htr2) ?_
  intro sf hpcf hrunf _ _ ⟨hvmf, hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨evs_tot, hevs_tot, ?_⟩, hspf, hcsf, htrf⟩
  rw [A.pool_of_vmPreserved hvmf]
  exact Entails.of_eq (by sep_ac_rfl)

/-- `.v1, .a2b` path from `+36` to return on `Block 324`. -/
theorem init_inner_v1_a2b_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (s0 s1 : State) (out akPtr : BitVec 64) (authKey : Bytes) (st0 : M.σ) (R : SepProp)
    (hcall_auth : AuthBudgetCallAtPlaced M A lim F ext s0 authKey
      (M.stepEvents (cloneEvs authKey) st0)
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, .a2b, akPtr, authKey⟩ st0) R)
    (hcall_into : IntoPbBudgetCallAtPlaced M A lim F ext s0 out .a2b authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, .a2b, akPtr, authKey⟩ st0) R)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hcode1 : LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s1.mem)
    (hinv1 : LsCallInv lsmpl s0.mem → LsCallInv lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_324).base + 36#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.a2b.toI32) (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 :
      s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s1 ∗
        stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992))
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, .a2b, akPtr, authKey⟩ st0)
      (InitInnerBudgetPanic R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s1 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool lim st0 s1 ∗
      stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt) := by
    rw [memRegion_992_split_a2b s0.sp, stackAt_authNew_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_a2b_placed hshim halloc hmemcpy s0 s1 out akPtr authKey st0 _ R
    hsp0_align hlt hfit hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hcode2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP_lsInv (init_inner_bl_364_placed s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hcode3 hinv3 ⟨hvm3, hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
  have hcs_hi3 := calleeSaved_chain_hi hcs2 hcs3
  have hx29_3 := calleeSaved_x29 hx29_2 hcs3
  have hx19_3 := calleeSaved_x19 hx19_2 hcs3
  have hfit_auth := fitsEnv_auth_of_initInnerEnv
    (x := ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) hfit
  have hsplit_auth :
      vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
      A.pool lim (M.stepEvents (cloneEvs authKey) st0) s2 ∗
      stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTablePlacedAt) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗
       vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
       A.pool lim (M.stepEvents (cloneEvs authKey) st0) s3 ∗
       stackAt (s0.sp - 1040#64) authNewStackX) ∗
      (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt) := by
    rw [stackAt_authNew_split_allocHook (s0.sp - 1040#64), ← A.pool_of_vmPreserved hvm3]
    sep_ac_rfl
  refine hcall_auth s3 ((blkPl_324).base + 368#64) _ _
    (fun h0 => hinv3 (hinv2 (hinv1 h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3
    (by simp (config := { decide := true }) only [blkPl_324, wp_norm, arm64_norm])
    (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hfit_auth hsplit_auth ?_
  intro s4 evs₂ a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcode4 hcs4 htr4 hevs₂
  have hcs_hi4 := calleeSaved_chain_hi hcs_hi3 hcs4
  have hx29_4 := calleeSaved_x29 hx29_3 hcs4
  have hx19_4 := calleeSaved_x19 hx19_3 hcs4
  have hpre_post_auth :
      (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
         ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (s0.sp - 1032#64) 24 ∗
        A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4 ∗
        stackAt (s0.sp - 1040#64) authNewStackX) ∗
       (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗ memRegion (s0.sp - 1040#64) 8 ∗
        memRegion (s0.sp - 56#64) 8 ∗ initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
        (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 1032#64) 8 ∗ memRegion (s0.sp - 968#64) 864 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) := by
    rw [← memRegion_24_and_cells_5_eq_cells_8 s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine initInner_seq_sepWP_lsInv
    (init_inner_a2b_post_auth_placed (A := A.repAlloc) (F := F) s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 hpc5 hrun5 hcode5 _ ⟨hvm5, hsp5, hx8_5, hx0_5, hcs5, htr5⟩
  have h56 :
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 48 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) ⊢
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s5 := by
    rw [← memRegion_48_and_8_eq_56 s0.sp, A.pool_of_vmPreserved hvm5]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre h56 ?_
  exact init_inner_from_412_placed s0 s5 out akPtr .a2b authKey st0 evs₂ R hcall_into hsp0_align
    (fun hc0 => hcode5 (hcode4 (hcode3 (hcode2 (hcode1 hc0)))))
    hfit hevs₂ hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

/-- `.v1, .b2a` path from `+36` to return on `Block 324`. -/
theorem init_inner_v1_b2a_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (s0 s1 : State) (out akPtr : BitVec 64) (authKey : Bytes) (st0 : M.σ) (R : SepProp)
    (hcall_auth : AuthBudgetCallAtPlaced M A lim F ext s0 authKey
      (M.stepEvents (cloneEvs authKey) st0)
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, .b2a, akPtr, authKey⟩ st0) R)
    (hcall_into : IntoPbBudgetCallAtPlaced M A lim F ext s0 out .b2a authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, .b2a, akPtr, authKey⟩ st0) R)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hcode1 : LibsignalCodeLoaded lsmpl s0.mem → LibsignalCodeLoaded lsmpl s1.mem)
    (hinv1 : LsCallInv lsmpl s0.mem → LsCallInv lsmpl s1.mem)
    (hpc1 : s1.pc = (blkPl_324).base + 36#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.b2a.toI32) (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 :
      s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s1 ∗
        stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992))
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨out, .v1, .b2a, akPtr, authKey⟩ st0)
      (InitInnerBudgetPanic R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s1 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool lim st0 s1 ∗
      stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt) := by
    rw [memRegion_992_split_b2a s0.sp, stackAt_authNew_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_b2a_placed hshim halloc hmemcpy s0 s1 out akPtr authKey st0 _ R
    hsp0_align hlt hfit hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hcode2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP_lsInv (init_inner_bl_192_placed s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hcode3 hinv3 ⟨hvm3, hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
  have hcs_hi3 := calleeSaved_chain_hi hcs2 hcs3
  have hx29_3 := calleeSaved_x29 hx29_2 hcs3
  have hx19_3 := calleeSaved_x19 hx19_2 hcs3
  have hfit_auth := fitsEnv_auth_of_initInnerEnv
    (x := ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) hfit
  have hsplit_auth :
      vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
      A.pool lim (M.stepEvents (cloneEvs authKey) st0) s2 ∗
      stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗
       vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
       A.pool lim (M.stepEvents (cloneEvs authKey) st0) s3 ∗
       stackAt (s0.sp - 1040#64) authNewStackX) ∗
      (cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt) := by
    rw [stackAt_authNew_split_allocHook (s0.sp - 1040#64), ← A.pool_of_vmPreserved hvm3]
    sep_ac_rfl
  refine hcall_auth s3 ((blkPl_324).base + 196#64) _ _
    (fun h0 => hinv3 (hinv2 (hinv1 h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3
    (by simp (config := { decide := true }) only [blkPl_324, wp_norm, arm64_norm])
    (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hfit_auth hsplit_auth ?_
  intro s4 evs₂ a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcode4 hcs4 htr4 hevs₂
  have hcs_hi4 := calleeSaved_chain_hi hcs_hi3 hcs4
  have hx29_4 := calleeSaved_x29 hx29_3 hcs4
  have hx19_4 := calleeSaved_x19 hx19_3 hcs4
  have hpre_post_auth :
      (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
         ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (s0.sp - 1032#64) 24 ∗
        A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4 ∗
        stackAt (s0.sp - 1040#64) authNewStackX) ∗
       (cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
        cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
        memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
        memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1032#64) 20 ∗
      cells (s0.sp - 872#64) 20 ∗ cells (s0.sp - 712#64) 17 ∗
      (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
      memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
      (memRegion (s0.sp - 1040#64) 8 ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) := by
    rw [← memRegion_24_and_cells_17_eq_cells_20 s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine initInner_seq_sepWP_lsInv
    (init_inner_b2a_post_auth_placed (A := A.repAlloc) (F := F) s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 hpc5 hrun5 hcode5 _ ⟨hvm5, hsp5, hx8_5, hx0_5, hcs5, htr5⟩
  have hpool5 :
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗
      (memRegion (s0.sp - 1040#64) 8 ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) ⊢
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s5 := by
    rw [A.pool_of_vmPreserved hvm5]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpool5 ?_
  exact init_inner_from_412_placed s0 s5 out akPtr .b2a authKey st0 evs₂ R hcall_into hsp0_align
    (fun hc0 => hcode5 (hcode4 (hcode3 (hcode2 (hcode1 hc0)))))
    hfit hevs₂ hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

/-- Unified budget-threaded body of `spqr::init_inner` (`Block 324`) for all `(v, d)`. -/
theorem init_inner_body_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocNoOomSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (s0 : State) (x : InitInnerGhost) (st0 : M.σ) (R : SepProp)
    (hcall_auth : AuthBudgetCallAtPlaced M A lim F ext s0 x.authKey
      (M.stepEvents (cloneEvs x.authKey) st0)
      (InitInnerPlacedBudgetPost M A lim F s0 x st0) R)
    (hcall_into_a2b : IntoPbBudgetCallAtPlaced M A lim F ext s0 x.out .a2b x.authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨x.out, .v1, .a2b, x.akPtr, x.authKey⟩ st0) R)
    (hcall_into_b2a : IntoPbBudgetCallAtPlaced M A lim F ext s0 x.out .b2a x.authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨x.out, .v1, .b2a, x.akPtr, x.authKey⟩ st0) R)
    (hpc : s0.pc = (blkPl_324).base)
    (hrun : s0.status = .Running)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpure :
      s0.readReg64 .x0 = x.out ∧ s0.readReg32 .x1 = x.v.toI32 ∧
      s0.readReg32 .x2 = x.d.toI32 ∧ s0.readReg64 .x3 = x.akPtr ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧ 32 + x.authKey.length < 2 ^ 63 ∧
      FitsEnv M lim st0 (InitInnerEnv F x)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s0
      (memRegion x.out optProtoInnerStateSize ∗ (x.akPtr ↦ₛ x.authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initInnerStack)
      (InitInnerPlacedBudgetPost M A lim F s0 x st0)
      (InitInnerBudgetPanic R) := by
  rcases x with ⟨out, v, d, akPtr, authKey⟩
  rcases hpure with ⟨hx0, hw1, hw2, hx3, hx4, _, hlt32, hfit⟩
  cases v
  · have hpre_v0 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initInnerStack ⊢
        memRegion out optProtoInnerStateSize ∗ stackAt s0.sp initInnerStack ∗
        ((akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s0) :=
      Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_v0 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_v0_placed (A := A.repAlloc) (F := F) s0 out d authKey
        ((akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s0)
        hsp0_align hpc hrun hx0 hw1) ?_
    intro sf hpcf hrunf _ _ ⟨hvmf, hspf, hcsf, htrf⟩
    refine SepWPp.done hpcf hrunf ⟨⟨[], rfl, ?_⟩, hspf, hcsf, htrf⟩
    rw [M.stepEvents_nil, A.pool_of_vmPreserved hvmf]
    exact Entails.of_eq (by sep_ac_rfl)
  · change FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)) at hfit
    have hpre_v1 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initInnerStack ⊢
        cells (s0.sp - 48#64) 6 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s0 ∗
         stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) := by
      rw [stackAt_initInner_split s0.sp]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_v1 ?_
    refine initInner_seq_sepWP_lsInv
      (init_inner_prologue_v1_placed s0 out akPtr d authKey _
        hsp0_align hpc hrun hx0 hw1 hw2 hx3 hx4) ?_
    intro s1 hpc1 hrun1 hcode1 hinv1 ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hw2_1, hx3_1, hcs1, htr1⟩
    have hpool1 :
        initInnerSavedCells s0 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s0 ∗
         stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) ⊢
        initInnerSavedCells s0 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTablePlacedAt ∗ A.pool lim st0 s1 ∗
         stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) := by
      rw [A.pool_of_vmPreserved hvm1]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpool1 ?_
    cases d
    · exact init_inner_v1_a2b_placed hshim halloc hmemcpy s0 s1 out akPtr authKey st0 R
        hcall_auth hcall_into_a2b hsp0_align (by dsimp at hlt32; omega) hfit hcode1 hinv1
        hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1
    · exact init_inner_v1_b2a_placed hshim halloc hmemcpy s0 s1 out akPtr authKey st0 R
        hcall_auth hcall_into_b2a hsp0_align (by dsimp at hlt32; omega) hfit hcode1 hinv1
        hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1

/-! ## 5. Callee-Parametric `Block 324` Entrypoints -/

/-- Verification of `spqr::init_inner` (`Block 324`) against
    `withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)` given per-arm `<States>::into_pb`
    contracts (`keysUnsampled`, `noHeaderReceived`) and `authNewBudgetSpec M A lim F`. -/
theorem init_inner_placed_ok_ext_of_arms [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewBudgetSpec M A lim F))
    (hinto_a2b : ∀ authKey : Bytes,
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (lsmpl.base 334)
        (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F (initV1State F .a2b authKey))))
    (hinto_b2a : ∀ authKey : Bytes,
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (lsmpl.base 334)
        (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F (initV1State F .b2a authKey)))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)) := by
  apply withLsCodeLoaded_initInnerPlacedSpecX_of_initInnerPlacedSpec
  apply subroutine_ok_of_sepWPp
  intro (x, st0) R s0 hpc hrun hpre hsp0_align
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  obtain ⟨hcode0, hpre⟩ := extract_withLsCodeLoaded hpre
  dsimp only [initInnerPlacedSpec, initInnerPlacedSpecOfEnv] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2.1
  have hcall_auth : AuthBudgetCallAtPlaced M A lim F ext s0 x.authKey
      (M.stepEvents (cloneEvs x.authKey) st0)
      (InitInnerPlacedBudgetPost M A lim F s0 x st0) R :=
    fun s ret_pc P Frame _ hpcs hruns hsps hlrs hlr_ls htrs hx0s hx1s hfits hsplits hnext =>
      call_authNew_budget_placed_ext hauth x.authKey (M.stepEvents (cloneEvs x.authKey) st0)
        hlt32 s0 s ret_pc P Frame R hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hfits hsplits
        hnext (hlr_ls := hlr_ls)
  have hcall_into_a2b : IntoPbBudgetCallAtPlaced M A lim F ext s0 x.out .a2b x.authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨x.out, .v1, .a2b, x.akPtr, x.authKey⟩ st0) R :=
    fun s st2 ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hfits2 hsplits hnext =>
      call_statesIntoPb_variant_placed_x (hinto_a2b x.authKey) x.out st2
        (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hfits2 hsplits hnext
  have hcall_into_b2a : IntoPbBudgetCallAtPlaced M A lim F ext s0 x.out .b2a x.authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨x.out, .v1, .b2a, x.akPtr, x.authKey⟩ st0) R :=
    fun s st2 ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hfits2 hsplits hnext =>
      call_statesIntoPb_variant_placed_x (hinto_b2a x.authKey) x.out st2
        (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hfits2 hsplits hnext
  exact ⟨_, R, hm, sepWPp_of_init_inner_placed_budget_wpp s0 s0 x st0 _ R
    (init_inner_body_placed hshim (subroutine_ok_allocNoOom_of_budget halloc) hmemcpy
      s0 x st0 R hcall_auth hcall_into_a2b hcall_into_b2a hpc hrun hsp0_align hpure)⟩

/-- Verification of `spqr::init_inner` (`Block 324`) against
    `withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)` given per-arm `<States>::into_pb`
    contracts and `withLsCallInv lsmpl (authNewBudgetSpec M A lim F)`. -/
theorem init_inner_placed_ok_x_of_arms [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewBudgetSpec M A lim F)))
    (hinto_a2b : ∀ authKey : Bytes,
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (lsmpl.base 334)
        (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F (initV1State F .a2b authKey))))
    (hinto_b2a : ∀ authKey : Bytes,
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (lsmpl.base 334)
        (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec M A lim F (initV1State F .b2a authKey)))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) := by
  apply subroutine_ok_of_sepWPp
  intro (x, st0) R s0 hpc hrun hpre hsp0_align
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpecXOfEnv] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hcode0 : LibsignalCodeLoaded lsmpl s0.mem := hinv0.2
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2.1
  have hcall_auth : AuthBudgetCallAtPlaced M A lim F ext s0 x.authKey
      (M.stepEvents (cloneEvs x.authKey) st0)
      (InitInnerPlacedBudgetPost M A lim F s0 x st0) R :=
    fun s ret_pc P Frame hinv_s hpcs hruns hsps hlrs hlr_ls htrs hx0s hx1s hfits hsplits hnext =>
      call_authNew_budget_placed_x hauth x.authKey (M.stepEvents (cloneEvs x.authKey) st0)
        hlt32 s0 s ret_pc P Frame R (hinv_s hinv0) hpcs hruns hsps hfsp_align hlrs htrs
        hx0s hx1s hfits hsplits hnext (hlr_ls := hlr_ls)
  have hcall_into_a2b : IntoPbBudgetCallAtPlaced M A lim F ext s0 x.out .a2b x.authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨x.out, .v1, .a2b, x.akPtr, x.authKey⟩ st0) R :=
    fun s st2 ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hfits2 hsplits hnext =>
      call_statesIntoPb_variant_placed_x (hinto_a2b x.authKey) x.out st2
        (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hfits2 hsplits hnext
  have hcall_into_b2a : IntoPbBudgetCallAtPlaced M A lim F ext s0 x.out .b2a x.authKey
      (InitInnerPlacedBudgetPost M A lim F s0 ⟨x.out, .v1, .b2a, x.akPtr, x.authKey⟩ st0) R :=
    fun s st2 ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hfits2 hsplits hnext =>
      call_statesIntoPb_variant_placed_x (hinto_b2a x.authKey) x.out st2
        (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hfits2 hsplits hnext
  exact ⟨_, R, hm, sepWPp_of_init_inner_placed_budget_wpp s0 s0 x st0 _ R
    (init_inner_body_placed hshim (subroutine_ok_allocNoOom_of_budget halloc) hmemcpy
      s0 x st0 R hcall_auth hcall_into_a2b hcall_into_b2a hpc hrun hsp0_align hpure)⟩

/-- Verification of `spqr::init_inner` (`Block 324`) against
    `withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)` from full `statesIntoPbPlacedSpec`. -/
theorem init_inner_placed_ok_ext_of_intoPb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (authNewBudgetSpec M A lim F))
    (hinto : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCodeLoaded lsmpl (initInnerPlacedSpecX M A lim F)) :=
  init_inner_placed_ok_ext_of_arms hshim halloc hmemcpy hauth
    (fun _ => withLsCodeLoaded_statesIntoPbVariantPlacedSpec_of_statesIntoPbPlacedSpec hinto _)
    (fun _ => withLsCodeLoaded_statesIntoPbVariantPlacedSpec_of_statesIntoPbPlacedSpec hinto _)

/-- Verification of `spqr::init_inner` (`Block 324`) against
    `withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)` from full `statesIntoPbPlacedSpec`. -/
theorem init_inner_placed_ok_x_of_intoPb [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewBudgetSpec M A lim F)))
    (hinto : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec M A lim F))) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) :=
  init_inner_placed_ok_x_of_arms hshim halloc hmemcpy hauth
    (fun _ => withLsCodeLoaded_statesIntoPbVariantPlacedSpec_of_statesIntoPbPlacedSpec hinto _)
    (fun _ => withLsCodeLoaded_statesIntoPbVariantPlacedSpec_of_statesIntoPbPlacedSpec hinto _)

end LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudgetAux
