/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Proof
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::init_inner` (`0x532dc`): Callee-Parametric Budget-Threaded Proof

Composes the `VmPreserved` segment lemmas for `spqr::init_inner` (`0x532dc`) with
`AllocContractsBudget`, budget-threaded `<Authenticator>::new`, and `<States>::into_pb`
arm contracts (`keysUnsampled`, `noHeaderReceived`) to prove `init_inner_ok_ext_of_arms`
and `init_inner_ok_x_of_arms`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode libsignalSessionImage)
open CryptoVerification.RustHeap (LayoutOk RustAlloc allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchet (ImgCallInv tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Direction PolynomialDecoder ProtoAuthenticator States V1State Version
   hkdfToSliceUnchecked hkdfToVecUnchecked length_hkdfExpand spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto
  (WireType encodeBytesField encodeBytesUncond encodeKey encodeMessage encodeOptMessage
   encodeUint64Field encodeVarint encodeVarintAux)
open CryptoVerification.SpqrV1.Auth
  (AuthNewGhost authNewName authNewStackX authenticatorAt authenticatorSize)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.States.IntoPb
  (StatesIntoPbGhost authenticatorHeap bv_add_add_lit' bv_sub_sub_lit' statesIntoPbJumpTableAt
   statesIntoPbName statesIntoPbStack)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost authenticatorAt_expose_frame fnAddr_fwd_eq initHdrDecoder initInnerFrame
   initInnerName initInnerResultAt initInnerSavedCells initInnerStack initInnerStackExt
   initInnerStackX initV1State libsignalSessionCode_fnOff_authNew
   libsignalSessionCode_fnOff_statesIntoPb_initInner memRegion_24_and_cells_17_eq_cells_20
   memRegion_24_and_cells_5_eq_cells_8 memRegion_48_and_8_eq_56 memRegion_992_rejoin_b2a
   memRegion_992_split_a2b memRegion_992_split_b2a stackAt_authNew_split_allocHook
   stackAt_authNew_split_statesIntoPb stackAt_initInner_split)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
   FitsStep FreeOnlyEvs RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append
   fitsEvents_cons fitsEvents_nil rustAllocEvents rustCliAllocNoOomSpecBase)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (StatesIntoPbOkExt StatesIntoPbOkX statesIntoPbSpec statesIntoPbSpecOfEnv
   statesIntoPbVariantSpec statesIntoPbVariantSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsBudget
  (InitInnerBaseOkExt InitInnerBaseOkExtOfEnv InitInnerEnv InitInnerOkExt InitInnerOkExtOfEnv
   InitInnerOkX InitInnerOkXExt InitInnerOkXExtOfEnv InitInnerOkXOfEnv SpqrBoundedEvs
   StatesIntoPbEnv initInnerSpec initInnerSpecExt initInnerSpecExtOfEnv initInnerSpecOfEnv
   initInnerSpecX initInnerSpecXOfEnv initInner_fnOff nonFreeCount nonFreeCount_append
   nonFreeCount_nil)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.StepsBudget
  (calleeSaved_chain_hi calleeSaved_x19 calleeSaved_x29 initInner_seq_sepWP
   init_inner_a2b_132_to_140 init_inner_a2b_144_ok_to_160 init_inner_a2b_164_to_364
   init_inner_a2b_empty_to_364 init_inner_a2b_post_auth init_inner_a2b_to_128
   init_inner_b2a_52_to_60 init_inner_b2a_64_ok_to_80 init_inner_b2a_84_to_192
   init_inner_b2a_empty_to_192 init_inner_b2a_post_auth init_inner_b2a_to_48
   init_inner_bl_128 init_inner_bl_140 init_inner_bl_160 init_inner_bl_192 init_inner_bl_364
   init_inner_bl_412 init_inner_bl_48 init_inner_bl_60 init_inner_bl_80
   init_inner_epilogue init_inner_prologue_v1 init_inner_v0 sepWPp_of_sepWP_keepInv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (AllocContractsBudget framelessMemcpyBudgetSpec noAllocShimBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::init_inner")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

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
  have hf := (hfit [.alloc r] hmem).1
  rcases hf with ⟨_, _, _, hva⟩
  have hreq : r ≤ M.stepReserve (.alloc r) st := M.req_le_stepReserve (.alloc r) st
  have hmax : 2 ^ 48 < MallocngMaxAllocSize := by decide
  have hr48 : r ≤ 2 ^ 48 := by omega
  have : min n MallocngMaxAllocSize ≤ 2 ^ 48 := hr48
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
    independently of `F` and `authKey` (since `Authenticator.new` hashes `authKey` to two
    32-byte keys). -/
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

/-! ## 2. Budget-Threaded `<Authenticator>::new` Contract & Envelope Propagation -/

/-- Default allocation envelope for `<spqr::authenticator::Authenticator>::new`:
    at most `24` non-`free` events of request size `≤ 2 * x.rootKey.length + 512` and
    alignment `≤ 16`. -/
def AuthNewBudgetEnv (x : AuthNewGhost) (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 24 (2 * x.rootKey.length + 512) evs

/-- Envelope-parametric fixed-offset budget specification of `<Authenticator>::new`. -/
def authNewBudgetSpecOfEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (Env : AuthNewGhost → List AllocEvent → Prop) :
    Spec (AuthNewGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.rkVecA ∧
      32 + x.rootKey.length < 2 ^ 63 ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA authenticatorSize ∗
      vecU8 A.repAlloc x.rkVecA x.rootKey ∗
      A.pool lim st s ∗ stackAt s.sp authNewStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      authenticatorAt A.repAlloc x.outA (Authenticator.new F x.rootKey 1#64) ∗
      memRegion x.rkVecA 24 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp authNewStackX

abbrev authNewBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (AuthNewGhost × M.σ) :=
  authNewBudgetSpecOfEnv M A lim F AuthNewBudgetEnv

/-- `<Authenticator>::new` meets `authNewBudgetSpecOfEnv M A lim F Env` on `tripleRatchetProgAtExt b ext`. -/
def AuthNewBudgetOkExtOfEnv (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : AuthNewGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr authNewName)
    (authNewBudgetSpecOfEnv M A lim F Env)

abbrev AuthNewBudgetOkExt (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  AuthNewBudgetOkExtOfEnv b M A lim F AuthNewBudgetEnv ext

/-- `<Authenticator>::new` meets `(authNewBudgetSpecOfEnv M A lim F Env).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def AuthNewBudgetOkXOfEnv (img : Obj.Image) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : AuthNewGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authNewName)
    ((authNewBudgetSpecOfEnv M A lim F Env).inImage img)

abbrev AuthNewBudgetOkX (img : Obj.Image) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  AuthNewBudgetOkXOfEnv img M A lim F AuthNewBudgetEnv ext

theorem AuthNewBudgetOkExtOfEnv.mono_env
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {Env₁ Env₂ : AuthNewGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hsub : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (h : AuthNewBudgetOkExtOfEnv b M A lim F Env₁ ext) :
    AuthNewBudgetOkExtOfEnv b M A lim F Env₂ ext := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (authNewBudgetSpecOfEnv M A lim F Env₁).pre (x, st) s0 ∗ R := by
    dsimp only [authNewBudgetSpecOfEnv] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hlt, hfit⟩, hm⟩
    exact ⟨⟨hx0, hx1, hlt, fun evs he => hfit evs (hsub x evs he)⟩, hm⟩
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨c, hex_st, hex⟩ | ⟨hoom_st, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [authNewBudgetSpecOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hsub x evs hpost.1.2⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hpan_st, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom⟩))

theorem AuthNewBudgetOkXOfEnv.mono_env
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {Env₁ Env₂ : AuthNewGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hsub : ∀ x evs, Env₁ x evs → Env₂ x evs)
    (h : AuthNewBudgetOkXOfEnv img M A lim F Env₁ ext) :
    AuthNewBudgetOkXOfEnv img M A lim F Env₂ ext := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((authNewBudgetSpecOfEnv M A lim F Env₁).inImage img).pre (x, st) s0 ∗ R := by
    dsimp only [Spec.inImage, authNewBudgetSpecOfEnv] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hinv, hpre⟩
    refine ⟨hinv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hlt, hfit⟩, hm⟩
    exact ⟨⟨hx0, hx1, hlt, fun evs he => hfit evs (hsub x evs he)⟩, hm⟩
  refine h.mono_outcome (x, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨c, hex_st, hex⟩ | ⟨hoom_st, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, authNewBudgetSpecOfEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hsub x evs hpost.1.2⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hpan_st, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom⟩))

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

/-! ## 3. Subroutine Address Rewriting & Variant Specialization -/

private theorem sub_ok_of_addr_eq {α : Type} {prog : Program} {a₁ a₂ : BitVec 64} {spec : Spec α}
    (heq : a₁ = a₂) (h : subroutine_ok prog a₁ spec) : subroutine_ok prog a₂ spec :=
  heq ▸ h

theorem sub_ok_authNew_budget_ext
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hauth : AuthNewBudgetOkExt b M A lim F ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      (authNewBudgetSpec M A lim F) :=
  sub_ok_of_addr_eq (fnAddr_fwd_eq
    (d := num% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
    (b := b) (X := Rust.withPanics ext)
    initInner_fnOff libsignalSessionCode_fnOff_authNew (by decide)).symm hauth

theorem sub_ok_authNew_budget_x
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hauth : AuthNewBudgetOkX img M A lim F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      ((authNewBudgetSpec M A lim F).inImage img) :=
  sub_ok_of_addr_eq (fnAddr_fwd_eq
    (d := num% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
    (b := img.base) (X := Rust.withPanics ext)
    initInner_fnOff libsignalSessionCode_fnOff_authNew (by decide)).symm hauth

theorem sub_ok_statesIntoPb_variant_at
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    {stateVal : States spqrPolyApi (spqrAuthApi F)}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec M A lim F b stateVal)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb"))
      (statesIntoPbVariantSpec M A lim F b stateVal) :=
  sub_ok_of_addr_eq (fnAddr_fwd_eq
    (d := num% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb"))
    (b := b) (X := Rust.withPanics ext)
    initInner_fnOff libsignalSessionCode_fnOff_statesIntoPb_initInner (by decide)).symm h

theorem statesIntoPbVariantSpec_of_statesIntoPbSpec
    {P : Program} {addr b : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    (h : subroutine_ok P addr (statesIntoPbSpec M A lim F b))
    (stateVal : States spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok P addr (statesIntoPbVariantSpec M A lim F b stateVal) := by
  refine subroutine_ok_outcome_intro fun (⟨out, stA⟩, st) R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (statesIntoPbSpec M A lim F b).pre (⟨out, stA, stateVal⟩, st) s0 ∗ R :=
    hpre
  refine h.mono_outcome (⟨out, stA, stateVal⟩, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan_st, hpan⟩ | ⟨c, hex_st, hex⟩ | ⟨hoom_st, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl ⟨hpan_st, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex_st, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom_st, hoom⟩))

/-! ## 4. Total `SepWPp` Subroutine Call Helper & Postcondition Wrapper -/

/-- Panic-free / OOM-free `SepWPp` subroutine call combinator for budget specs whose
    `onExit`, `onPanic`, and `onOom` are `⌜False⌝`. -/
theorem sepWPp_call_total {α : Type} {prog : Program} {caller_ret target ret_pc : BitVec 64}
    {spec : Spec α} (x : α) {s : State} {P Frame : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hsub : subroutine_ok prog target spec)
    (hpc : s.pc = target)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : ∀ R', (s.mem ⊨ P ∗ R') → (s.mem ⊨ (spec.pre x s ∗ Frame) ∗ R'))
    (hexit : ∀ sf c, spec.onExit x c s sf = ⌜False⌝ := by intros; rfl)
    (hpanic : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      (∀ img, ImgCallInv img s → ImgCallInv img sf) →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog caller_ret sf (spec.post x s sf ∗ Frame) Q Qp) :
    SepWPp prog caller_ret s P Q Qp := by
  refine CryptoVerification.SpqrV1.Top.InitInner.sepWPp_of_sepWP_keepInv (mid := ret_pc) ?_
  refine SepWP.call_subroutine_frame hsub (x := x) (F := Frame)
    hpc hrun hsp_align hlr
    (fun R hm => by rw [← sepConj_assoc]; exact hpre R hm)
    (fun _ sf _ hp => by rw [hpanic sf] at hp; exact not_satisfies_false_sepConj hp)
    (fun _ code sf _ he => by rw [hexit sf code] at he; exact not_satisfies_false_sepConj he)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf =>
      SepWP.done hpc_sf hrun_sf fun hinv_sf =>
        hnext sf hpc_sf hrun_sf hinv_sf hsp_sf hcs_sf)
    (fun _ sf _ ho => by rw [hoom sf] at ho; exact (not_satisfies_false_sepConj ho).elim)

/-- Postcondition predicate of `spqr::init_inner` under `RustCliAllocBudget M`. -/
def InitInnerBudgetPost (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (s0 : State) (x : InitInnerGhost) (st0 : M.σ) : State → SepProp → Prop :=
  fun sf Pf =>
    (∃ evs : List AllocEvent,
      InitInnerEnv F x evs ∧
      (Pf ⊢
        initInnerResultAt A.repAlloc (F := F) x.out x.v x.d x.authKey ∗
        (x.akPtr ↦ₛ x.authKey) ∗ statesIntoPbJumpTableAt b ∗
        A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp initInnerStack)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

/-- Panic predicate for panic-free budget specs (`onPanic = ⌜False⌝`). -/
def InitInnerBudgetPanic (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)

theorem sepWPp_of_init_inner_budget_wpp
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitInnerGhost) (st0 : M.σ) (P R : SepProp)
    (hwpp : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (InitInnerBudgetPost M A lim F b s0 x st0) (InitInnerBudgetPanic R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initInnerSpec M A lim F b).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initInnerSpec M A lim F b).onPanic (x, st0) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps,
      ⟨hpcf, hrunf, P_f, hmf, ⟨⟨evs, hevs, hent⟩, hspf, hcsf, htrf⟩⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR
    have hm' := Satisfies.mono (sepConj_mono_left hent) hmR
    dsimp only [initInnerSpec, initInnerSpecOfEnv]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htrf, hevs⟩, by simpa only [sepConj_assoc] using hm'⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun hmR => hqp hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 5. Spatial Split Helpers & Slice-Clone CPS Lemmas (`.a2b` & `.b2a`) -/

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

/-- `.a2b` slice-clone (`+36 → +364`) under `AllocContractsBudget`, advancing `st0` to
    `M.stepEvents (cloneEvs authKey) st0` without OOM. -/
theorem init_inner_clone_a2b
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsBudget b M A lim ext)
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (st0 : M.σ)
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
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
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 364#64 →
      s2.status = .Running →
      (∀ img, ImgCallInv img s → ImgCallInv img s2) →
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
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
        (vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s2 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases h0 : authKey.length = 0
  · rcases List.eq_nil_of_length_eq_zero h0 with rfl
    dsimp only [List.length_nil] at hx20
    refine initInner_seq_sepWP
      (init_inner_a2b_empty_to_364 (A := A.repAlloc) s0 s out _
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htr) ?_
    intro s2 hpc2 hrun2 hinv2 ⟨hvm2, hsp2, hx29_2, hx19_2, hx0_2, hx1_2, hcs2, htr2⟩
    have hpool :
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗ (akPtr ↦ₛ ([] : Bytes)) ∗
        A.pool lim (M.stepEvents (cloneEvs []) st0) s2 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
      rw [cloneEvs_of_length_zero rfl, M.stepEvents_nil, A.pool_of_vmPreserved hvm2]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool
      (hnext s2 hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2)
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
    refine initInner_seq_sepWP
      (init_inner_a2b_to_128 s0 s out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc hrun hsp hx29 hx19 hx20 hlen_ne hw2 hx3 hcs_hi htr) ?_
    intro s1 hpc1 hrun1 hinv1 ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hcs1, htr1⟩
    refine initInner_seq_sepWP (init_inner_bl_128 s1 _ hpc1 hrun1) ?_
    intro s2 hpc2 hrun2 hinv2 ⟨hvm2, hsp2, hlr2, hcs2, htr2⟩
    have hcs_hi2 := calleeSaved_chain_hi hcs1 hcs2
    have hx29_2 := calleeSaved_x29 hx29_1 hcs2
    have hx19_2 := calleeSaved_x19 hx19_1 hcs2
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs2.2.1, hx20_1]
    have hx21_2 : s2.readReg64 .x21 = akPtr := by rw [hcs2.2.2.1, hx21_1]
    have hshim := hA.shim_ok_at initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    refine sepWPp_call_total () hshim hpc2 hrun2
      (by rw [State.spAligned, hsp2, hsp1]; exact hfsp_align) hlr2
      (fun R' hm => by
        dsimp only [noAllocShimBudgetSpec]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
      (hnext := fun s3 hpc3 hrun3 hinv3 hsp3 hcs3 => ?_)
    dsimp only [noAllocShimBudgetSpec]
    refine SepWPp.pure_left fun ⟨htr3, hvm3⟩ => ?_
    have hcs_hi3 := calleeSaved_chain_hi hcs_hi2 hcs3
    have hx29_3 := calleeSaved_x29 hx29_2 hcs3
    have hx19_3 := calleeSaved_x19 hx19_2 hcs3
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs3.2.1, hx20_2]
    have hx21_3 : s3.readReg64 .x21 = akPtr := by rw [hcs3.2.2.1, hx21_2]
    refine initInner_seq_sepWP
      (init_inner_a2b_132_to_140 s0 s3 out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]) hx29_3 hx19_3 hx20_3 hx21_3 hcs_hi3
        (by rw [htr3, htr2, htr1])) ?_
    intro s4 hpc4 hrun4 hinv4 ⟨hvm4, hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx0_4, hx1_4, hcs4, htr4⟩
    refine initInner_seq_sepWP (init_inner_bl_140 s4 _ hpc4 hrun4) ?_
    intro s5 hpc5 hrun5 hinv5 ⟨hvm5, hsp5, hlr5, hx0_5, hx1_5, hcs5, htr5⟩
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
    have halloc := hA.allocNoOom_ok_at initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_alloc"))
    refine sepWPp_call_total (authKey.length, 1, st0)
      (Frame := cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame)
      halloc hpc5 hrun5
      (by rw [State.spAligned, hsp5, hsp4]; exact hfsp_align) hlr5
      (fun R' hm => by
        dsimp only [rustCliAllocNoOomSpecBase]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        refine ⟨⟨?_, ?_, hlay, hfits_cl⟩, hm⟩
        · rw [hx0_5, hx0_4, hlen_toNat]
        · rw [hx1_5, hx1_4]; rfl)
      (hnext := fun s6 hpc6 hrun6 hinv6 hsp6 hcs6 => ?_)
    dsimp only [rustCliAllocNoOomSpecBase]
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
    refine initInner_seq_sepWP
      (init_inner_a2b_144_ok_to_160 s0 s6 out akPtr (BitVec.ofNat 64 authKey.length) ptr _
        hsp0_align hpc6 hrun6 (by rw [hsp6, hsp5, hsp4]) hx29_6 hx19_6 hx20_6 hx21_6
        rfl hptr_beq hcs_hi6 (by rw [hpres6.2.1, htr5, htr4])) ?_
    intro s7 hpc7 hrun7 hinv7 ⟨hvm7, hsp7, hx29_7, hx19_7, hx20_7, hx0_7, hx1_7, hx2_7, hcs7, htr7⟩
    refine initInner_seq_sepWP (init_inner_bl_160 s7 _ hpc7 hrun7) ?_
    intro s8 hpc8 hrun8 hinv8 ⟨hvm8, hsp8, hlr8, hx0_8, hx1_8, hx2_8, hcs8, htr8⟩
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
    have hmc := hA.session_memcpy_region_ok_at initInnerName
      (num% (ls_rel% "spqr::init_inner" "memcpy"))
    refine sepWPp_call_total (ptr, akPtr, authKey)
      (Frame := ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
        A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      hmc hpc8 hrun8
      (by rw [State.spAligned, hsp8, hsp7]; exact hfsp_align) hlr8
      (fun R' hm => by
        dsimp only [framelessMemcpyBudgetSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        exact ⟨⟨by rw [hx0_8, hx0_7], by rw [hx1_8, hx1_7], by rw [hx2_8, hx2_7, hlen_toNat]⟩, hm⟩)
      (hnext := fun s9 hpc9 hrun9 hinv9 hsp9 hcs9 => ?_)
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
    refine initInner_seq_sepWP
      (init_inner_a2b_164_to_364 (A := A.repAlloc) s0 s9 out ptr authKey _
        hsp0_align hpos hlt hptr_ne0 hpc9 hrun9 (by rw [hsp9, hsp8, hsp7])
        hx29_9 hx19_9 hx20_9 hcs_hi9 (by rw [htr9, htr8, htr7])) ?_
    intro s10 hpc10 hrun10 hinv10 ⟨hvm10, hsp10, hx29_10, hx19_10, hx0_10, hx1_10, hcs10, htr10⟩
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
        (fun img h =>
          hinv10 img (hinv9 img (hinv8 img (hinv7 img
            (hinv6 img (hinv5 img (hinv4 img (hinv3 img (hinv2 img (hinv1 img h))))))))))
        hsp10 hx29_10 hx19_10 hx0_10 hx1_10 hcs10 htr10)

/-- `.b2a` slice-clone (`+36 → +192`) under `AllocContractsBudget`, advancing `st0` to
    `M.stepEvents (cloneEvs authKey) st0` without OOM. -/
theorem init_inner_clone_b2a
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q : State → SepProp → Prop}
    (hA : AllocContractsBudget b M A lim ext)
    (s0 s : State) (out akPtr : BitVec 64) (authKey : Bytes) (st0 : M.σ)
    (Frame R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
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
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 192#64 →
      s2.status = .Running →
      (∀ img, ImgCallInv img s → ImgCallInv img s2) →
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
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
        (vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗ (akPtr ↦ₛ authKey) ∗
         A.pool lim (M.stepEvents (cloneEvs authKey) st0) s2 ∗
         stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗
       A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  by_cases h0 : authKey.length = 0
  · rcases List.eq_nil_of_length_eq_zero h0 with rfl
    dsimp only [List.length_nil] at hx20
    refine initInner_seq_sepWP
      (init_inner_b2a_empty_to_192 (A := A.repAlloc) s0 s out _
        hsp0_align hpc hrun hsp hx29 hx19 hx20 hw2 hcs_hi htr) ?_
    intro s2 hpc2 hrun2 hinv2 ⟨hvm2, hsp2, hx29_2, hx19_2, hx0_2, hx1_2, hcs2, htr2⟩
    have hpool :
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗
        ((akPtr ↦ₛ ([] : Bytes)) ∗ A.pool lim st0 s ∗ stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame) ⊢
        vecU8 A.repAlloc (s0.sp - 1032#64) [] ∗ (akPtr ↦ₛ ([] : Bytes)) ∗
        A.pool lim (M.stepEvents (cloneEvs []) st0) s2 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame := by
      rw [cloneEvs_of_length_zero rfl, M.stepEvents_nil, A.pool_of_vmPreserved hvm2]
      exact Entails.of_eq (by sep_ac_rfl)
    exact SepWPp.weaken_pre hpool
      (hnext s2 hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2)
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
    refine initInner_seq_sepWP
      (init_inner_b2a_to_48 s0 s out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc hrun hsp hx29 hx19 hx20 hlen_ne hw2 hx3 hcs_hi htr) ?_
    intro s1 hpc1 hrun1 hinv1 ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hcs1, htr1⟩
    refine initInner_seq_sepWP (init_inner_bl_48 s1 _ hpc1 hrun1) ?_
    intro s2 hpc2 hrun2 hinv2 ⟨hvm2, hsp2, hlr2, hcs2, htr2⟩
    have hcs_hi2 := calleeSaved_chain_hi hcs1 hcs2
    have hx29_2 := calleeSaved_x29 hx29_1 hcs2
    have hx19_2 := calleeSaved_x19 hx19_1 hcs2
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs2.2.1, hx20_1]
    have hx21_2 : s2.readReg64 .x21 = akPtr := by rw [hcs2.2.2.1, hx21_1]
    have hshim := hA.shim_ok_at initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    refine sepWPp_call_total () hshim hpc2 hrun2
      (by rw [State.spAligned, hsp2, hsp1]; exact hfsp_align) hlr2
      (fun R' hm => by
        dsimp only [noAllocShimBudgetSpec]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm)
      (hnext := fun s3 hpc3 hrun3 hinv3 hsp3 hcs3 => ?_)
    dsimp only [noAllocShimBudgetSpec]
    refine SepWPp.pure_left fun ⟨htr3, hvm3⟩ => ?_
    have hcs_hi3 := calleeSaved_chain_hi hcs_hi2 hcs3
    have hx29_3 := calleeSaved_x29 hx29_2 hcs3
    have hx19_3 := calleeSaved_x19 hx19_2 hcs3
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 authKey.length := by rw [hcs3.2.1, hx20_2]
    have hx21_3 : s3.readReg64 .x21 = akPtr := by rw [hcs3.2.2.1, hx21_2]
    refine initInner_seq_sepWP
      (init_inner_b2a_52_to_60 s0 s3 out akPtr (BitVec.ofNat 64 authKey.length) _
        hpc3 hrun3 (by rw [hsp3, hsp2, hsp1]) hx29_3 hx19_3 hx20_3 hx21_3 hcs_hi3
        (by rw [htr3, htr2, htr1])) ?_
    intro s4 hpc4 hrun4 hinv4 ⟨hvm4, hsp4, hx29_4, hx19_4, hx20_4, hx21_4, hx0_4, hx1_4, hcs4, htr4⟩
    refine initInner_seq_sepWP (init_inner_bl_60 s4 _ hpc4 hrun4) ?_
    intro s5 hpc5 hrun5 hinv5 ⟨hvm5, hsp5, hlr5, hx0_5, hx1_5, hcs5, htr5⟩
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
    have halloc := hA.allocNoOom_ok_at initInnerName
      (num% (ls_rel% "spqr::init_inner" "__rustc::__rust_alloc"))
    refine sepWPp_call_total (authKey.length, 1, st0)
      (Frame := cells (s0.sp - 1032#64) 2 ∗ cells (s0.sp - 1016#64) 1 ∗ (akPtr ↦ₛ authKey) ∗ Frame)
      halloc hpc5 hrun5
      (by rw [State.spAligned, hsp5, hsp4]; exact hfsp_align) hlr5
      (fun R' hm => by
        dsimp only [rustCliAllocNoOomSpecBase]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        refine ⟨⟨?_, ?_, hlay, hfits_cl⟩, hm⟩
        · rw [hx0_5, hx0_4, hlen_toNat]
        · rw [hx1_5, hx1_4]; rfl)
      (hnext := fun s6 hpc6 hrun6 hinv6 hsp6 hcs6 => ?_)
    dsimp only [rustCliAllocNoOomSpecBase]
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
    refine initInner_seq_sepWP
      (init_inner_b2a_64_ok_to_80 s0 s6 out akPtr (BitVec.ofNat 64 authKey.length) ptr _
        hsp0_align hpc6 hrun6 (by rw [hsp6, hsp5, hsp4]) hx29_6 hx19_6 hx20_6 hx21_6
        rfl hptr_beq hcs_hi6 (by rw [hpres6.2.1, htr5, htr4])) ?_
    intro s7 hpc7 hrun7 hinv7 ⟨hvm7, hsp7, hx29_7, hx19_7, hx20_7, hx0_7, hx1_7, hx2_7, hcs7, htr7⟩
    refine initInner_seq_sepWP (init_inner_bl_80 s7 _ hpc7 hrun7) ?_
    intro s8 hpc8 hrun8 hinv8 ⟨hvm8, hsp8, hlr8, hx0_8, hx1_8, hx2_8, hcs8, htr8⟩
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
    have hmc := hA.session_memcpy_region_ok_at initInnerName
      (num% (ls_rel% "spqr::init_inner" "memcpy"))
    refine sepWPp_call_total (ptr, akPtr, authKey)
      (Frame := ((s0.sp - 1032#64) ↦₆₄ BitVec.ofNat 64 authKey.length) ∗
        ((s0.sp - 1024#64) ↦₆₄ ptr) ∗
        cells (s0.sp - 1016#64) 1 ∗ A.live ptr authKey.length 1 ∗
        A.pool lim (M.stepEvents (cloneEvs authKey) st0) s8 ∗
        stackAt (s0.sp - 1040#64) allocHookStack ∗ Frame)
      hmc hpc8 hrun8
      (by rw [State.spAligned, hsp8, hsp7]; exact hfsp_align) hlr8
      (fun R' hm => by
        dsimp only [framelessMemcpyBudgetSpec]
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
        exact ⟨⟨by rw [hx0_8, hx0_7], by rw [hx1_8, hx1_7], by rw [hx2_8, hx2_7, hlen_toNat]⟩, hm⟩)
      (hnext := fun s9 hpc9 hrun9 hinv9 hsp9 hcs9 => ?_)
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
    refine initInner_seq_sepWP
      (init_inner_b2a_84_to_192 (A := A.repAlloc) s0 s9 out ptr authKey _
        hsp0_align hpos hlt hptr_ne0 hpc9 hrun9 (by rw [hsp9, hsp8, hsp7])
        hx29_9 hx19_9 hx20_9 hcs_hi9 (by rw [htr9, htr8, htr7])) ?_
    intro s10 hpc10 hrun10 hinv10 ⟨hvm10, hsp10, hx29_10, hx19_10, hx0_10, hx1_10, hcs10, htr10⟩
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
        (fun img h =>
          hinv10 img (hinv9 img (hinv8 img (hinv7 img
            (hinv6 img (hinv5 img (hinv4 img (hinv3 img (hinv2 img (hinv1 img h))))))))))
        hsp10 hx29_10 hx19_10 hx0_10 hx1_10 hcs10 htr10)

/-! ## 6. Subroutine Call Wrappers (`<Authenticator>::new` & `<States>::into_pb`) & Body -/

/-- Abstract budget-threaded call interface for `<Authenticator>::new`, instantiated by both
    `call_authNew_budget_ext` and `call_authNew_budget_x`. -/
def AuthBudgetCallAt (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (b : BitVec 64)
    (ext : String → Option (State → State))
    (s0 : State) (authKey : Bytes) (st1 : M.σ)
    (Q : State → SepProp → Prop) (R : SepProp) : Prop :=
  ∀ (s : State) (ret_pc : BitVec 64) (P Frame : SepProp),
    (∀ img, ImgCallInv img s0 → ImgCallInv img s) →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new") →
    s.status = .Running → s.sp = s0.sp - 1040#64 →
    s.readReg64 .x30 = ret_pc → s.trace = s0.trace →
    s.readReg64 .x0 = s0.sp - 104#64 → s.readReg64 .x1 = s0.sp - 1032#64 →
    FitsEnv M lim st1 (AuthNewBudgetEnv ⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩) →
    P = (memRegion (s0.sp - 104#64) authenticatorSize ∗
      vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
      A.pool lim st1 s ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame →
    (∀ (sf : State) (evs₂ : List AllocEvent) (a0 a1 a2 a3 a4 a5 : BitVec 64),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂ →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗
          A.pool lim (M.stepEvents evs₂ st1) sf ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerBudgetPanic R)) →
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q (InitInnerBudgetPanic R)

theorem call_authNew_budget_ext
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      (authNewBudgetSpec M A lim F))
    (authKey : Bytes) (st1 : M.σ) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
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
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂ →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗
          A.pool lim (M.stepEvents evs₂ st1) sf ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q (InitInnerBudgetPanic R) := by
  refine sepWPp_call_total (⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩, st1)
    hauth_raw hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit] at hm
      dsimp only [authNewBudgetSpec, authNewBudgetSpecOfEnv]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨⟨hx0, hx1, hlt, hfit1⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ hsp_sf hcs_sf => ?_)
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
    (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr_sf, htrace]) hevs₂

theorem call_authNew_budget_x
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hauth_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
      ((authNewBudgetSpec M A lim F).inImage img))
    (authKey : Bytes) (st1 : M.σ) (hlt : 32 + authKey.length < 2 ^ 63)
    {Q : State → SepProp → Prop}
    (s0 s : State) (ret_pc : BitVec 64) (P Frame R : SepProp) (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::authenticator::Authenticator>::new"))
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
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂ →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) sf
        (((((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
           ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
          authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
          memRegion (s0.sp - 1032#64) 24 ∗
          A.pool lim (M.stepEvents evs₂ st1) sf ∗ stackAt (s0.sp - 1040#64) authNewStackX) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P Q
      (InitInnerBudgetPanic R) := by
  refine sepWPp_call_total (⟨s0.sp - 104#64, s0.sp - 1032#64, authKey⟩, st1)
    hauth_raw hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit] at hm
      dsimp only [Spec.inImage, authNewBudgetSpec, authNewBudgetSpecOfEnv]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨hinv, ⟨hx0, hx1, hlt, hfit1⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ hsp_sf hcs_sf => ?_)
  dsimp only [Spec.inImage, authNewBudgetSpec, authNewBudgetSpecOfEnv]
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
    (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr_sf, htrace]) hevs₂

theorem call_statesIntoPb_budget
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    {stateVal : States spqrPolyApi (spqrAuthApi F)}
    (hinto_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr initInnerName +
        bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb"))
      (statesIntoPbVariantSpec M A lim F b stateVal))
    (out : BitVec 64) (st2 : M.σ)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop} (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName +
      bv% (ls_rel% "spqr::init_inner" "<spqr::v1::chunked::states::States>::into_pb"))
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hfit2 : FitsEnv M lim st2
      (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024)))
    (hsplit : P =
      (memRegion out optProtoInnerStateSize ∗
       chunkedStatesAt A.repAlloc (s0.sp - 1032#64) stateVal ∗
       statesIntoPbJumpTableAt b ∗ A.pool lim st2 s ∗
       stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs₃ : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024) evs₃ →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗
          statesIntoPbJumpTableAt b ∗ A.pool lim (M.stepEvents evs₃ st2) sf ∗
          stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P Q (InitInnerBudgetPanic R) := by
  refine sepWPp_call_total (⟨out, s0.sp - 1032#64⟩, st2)
    hinto_raw hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr
    (fun R' hm => by
      rw [hsplit] at hm
      dsimp only [statesIntoPbVariantSpec, statesIntoPbVariantSpecOfEnv]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨⟨hx8, hx0, hb, hfit2⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ hsp_sf hcs_sf => ?_)
  dsimp only [statesIntoPbVariantSpec, statesIntoPbVariantSpecOfEnv]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₃ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr_sf, hevs₃⟩ => ?_
  exact hnext sf evs₃ hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr_sf, htrace]) hevs₃

/-- Shared tail from `+412`: `bl <States>::into_pb` + epilogue, assembling `InitInnerBudgetPost`. -/
theorem init_inner_from_412
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (out akPtr : BitVec 64) (d : Direction) (authKey : Bytes)
    (st0 : M.σ) (evs₂ : List AllocEvent) (R : SepProp)
    (hinto_d : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec M A lim F b (initV1State F d authKey)))
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hevs₂ : SpqrBoundedEvs 24 (2 * authKey.length + 512) evs₂)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 412#64)
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
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F d authKey) ∗
       memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s)
      (InitInnerBudgetPost M A lim F b s0 ⟨out, .v1, d, akPtr, authKey⟩ st0)
      (InitInnerBudgetPanic R) := by
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  have hmax := le_mallocngMaxAllocSize_of_fitsEnv_spqrBoundedEvs (n := authKey.length)
    (by decide) (by omega) hfit
  have hfit2 := fitsEnv_statesIntoPb_of_initInnerEnv (F := F) (d := d) hfit hevs₂
  refine initInner_seq_sepWP (init_inner_bl_412 s _ hpc hrun) ?_
  intro s1 hpc1 hrun1 _ ⟨hvm1, hsp1, hlr1, hx8_1, hx0_1, hcs1, htr1⟩
  have hcs_hi1 := calleeSaved_chain_hi hcs_hi hcs1
  have hsplit_pb :
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F d authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s =
      (memRegion out optProtoInnerStateSize ∗
       chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F d authKey) ∗
       statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s1 ∗
       stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 10768 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) := by
    rw [stackAt_authNew_split_statesIntoPb (s0.sp - 1040#64), ← A.pool_of_vmPreserved hvm1]
    sep_ac_rfl
  refine call_statesIntoPb_budget (sub_ok_statesIntoPb_variant_at hinto_d)
    out (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0))
    (s0 := s0) (s := s1)
    (ret_pc := (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 416#64)
    (R := R) hb hpc1 hrun1 (hsp1.trans hsp) hfsp_align hlr1 (htr1.trans htr)
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
       memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs₃ (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0))) s2 ∗
       stackAt (s0.sp - 1040#64) statesIntoPbStack) ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 10768 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       memRegion (s0.sp - 104#64) 56 ∗ initInnerSavedCells s0 ∗ (akPtr ↦ₛ authKey)) ⊢
      stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992 ∗
      initInnerSavedCells s0 ∗
      (initInnerResultAt A.repAlloc (F := F) out .v1 d authKey ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs_tot st0) s2) := by
    dsimp only [initInnerResultAt]
    rw [hstep_eq, ← memRegion_992_rejoin_b2a s0.sp,
      stackAt_authNew_split_statesIntoPb (s0.sp - 1040#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hrejoin_ep ?_
  refine initInner_seq_sepWP
    (init_inner_epilogue s0 s2
      (initInnerResultAt A.repAlloc (F := F) out .v1 d authKey ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs_tot st0) s2)
      hsp0_align hpc2 hrun2 hsp2 hcs_hi2 htr2) ?_
  intro sf hpcf hrunf _ ⟨hvmf, hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨evs_tot, hevs_tot, ?_⟩, hspf, hcsf, htrf⟩
  rw [A.pool_of_vmPreserved hvmf]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Complete `.v1` `.a2b` branch from `+36` to return. -/
theorem init_inner_v1_a2b
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    {authKey : Bytes}
    (hA : AllocContractsBudget b M A lim ext)
    (hinto_a2b : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec M A lim F b (initV1State F .a2b authKey)))
    (s0 s1 : State) (out akPtr : BitVec 64) (st0 : M.σ) (R : SepProp)
    (hcall_auth : AuthBudgetCallAt M A lim F b ext s0 authKey
      (M.stepEvents (cloneEvs authKey) st0)
      (InitInnerBudgetPost M A lim F b s0 ⟨out, .v1, .a2b, akPtr, authKey⟩ st0) R)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hinv1 : ∀ img, ImgCallInv img s0 → ImgCallInv img s1)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.a2b.toI32)
    (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 :
      s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗
       (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool lim st0 s1 ∗
        stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992))
      (InitInnerBudgetPost M A lim F b s0 ⟨out, .v1, .a2b, akPtr, authKey⟩ st0)
      (InitInnerBudgetPanic R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool lim st0 s1 ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool lim st0 s1 ∗
      stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ memRegion (s0.sp - 56#64) 8 ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b) := by
    rw [memRegion_992_split_a2b s0.sp, stackAt_authNew_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_a2b hA s0 s1 out akPtr authKey st0 _ R
    hsp0_align hlt hfit hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP (init_inner_bl_364 s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hvm3, hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
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
       cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ memRegion (s0.sp - 56#64) 8 ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗
       vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
       A.pool lim (M.stepEvents (cloneEvs authKey) st0) s3 ∗
       stackAt (s0.sp - 1040#64) authNewStackX) ∗
      (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ memRegion (s0.sp - 56#64) 8 ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b) := by
    rw [stackAt_authNew_split_allocHook (s0.sp - 1040#64), ← A.pool_of_vmPreserved hvm3]
    sep_ac_rfl
  refine hcall_auth s3 ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 368#64) _ _
    (fun img h0 => hinv3 img (hinv2 img (hinv1 img h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3 (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hfit_auth hsplit_auth ?_
  intro s4 evs₂ a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcs4 htr4 hevs₂
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
       (cells (s0.sp - 1008#64) 5 ∗ memRegion (s0.sp - 968#64) 864 ∗
        memRegion (s0.sp - 1040#64) 8 ∗ memRegion (s0.sp - 56#64) 8 ∗
        initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
        (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 1032#64) 8 ∗ memRegion (s0.sp - 968#64) 864 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) := by
    rw [← memRegion_24_and_cells_5_eq_cells_8 s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine initInner_seq_sepWP
    (init_inner_a2b_post_auth (A := A.repAlloc) (F := F) s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 hpc5 hrun5 _ ⟨hvm5, hsp5, hx8_5, hx0_5, hcs5, htr5⟩
  have h56 :
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 48 ∗
      (memRegion (s0.sp - 56#64) 8 ∗ memRegion (s0.sp - 1040#64) 8 ∗
       stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) ⊢
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .a2b authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s5 := by
    rw [← memRegion_48_and_8_eq_56 s0.sp, A.pool_of_vmPreserved hvm5]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre h56 ?_
  exact init_inner_from_412 s0 s5 out akPtr .a2b authKey st0 evs₂ R hinto_a2b hb hsp0_align
    hfit hevs₂ hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

/-- Complete `.v1` `.b2a` branch from `+36` to return. -/
theorem init_inner_v1_b2a
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    {authKey : Bytes}
    (hA : AllocContractsBudget b M A lim ext)
    (hinto_b2a : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec M A lim F b (initV1State F .b2a authKey)))
    (s0 s1 : State) (out akPtr : BitVec 64) (st0 : M.σ) (R : SepProp)
    (hcall_auth : AuthBudgetCallAt M A lim F b ext s0 authKey
      (M.stepEvents (cloneEvs authKey) st0)
      (InitInnerBudgetPost M A lim F b s0 ⟨out, .v1, .b2a, akPtr, authKey⟩ st0) R)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : authKey.length < 2 ^ 63)
    (hfit : FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)))
    (hinv1 : ∀ img, ImgCallInv img s0 → ImgCallInv img s1)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1040#64)
    (hx29_1 : s1.readReg64 .x29 = s0.sp - 48#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 authKey.length)
    (hw2_1 : s1.readReg32 .x2 = Direction.b2a.toI32)
    (hx3_1 : s1.readReg64 .x3 = akPtr)
    (hcs1 :
      s1.readReg64 .x22 = s0.readReg64 .x22 ∧ s1.readReg64 .x23 = s0.readReg64 .x23 ∧
      s1.readReg64 .x24 = s0.readReg64 .x24 ∧ s1.readReg64 .x25 = s0.readReg64 .x25 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧ s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (htr1 : s1.trace = s0.trace) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (initInnerSavedCells s0 ∗
       (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool lim st0 s1 ∗
        stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992))
      (InitInnerBudgetPost M A lim F b s0 ⟨out, .v1, .b2a, akPtr, authKey⟩ st0)
      (InitInnerBudgetPanic R) := by
  have hpre_split :
      initInnerSavedCells s0 ∗ (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool lim st0 s1 ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       memRegion (s0.sp - 1040#64) 992) ⊢
      cells (s0.sp - 1032#64) 3 ∗ (akPtr ↦ₛ authKey) ∗ A.pool lim st0 s1 ∗
      stackAt (s0.sp - 1040#64) allocHookStack ∗
      (memRegion (s0.sp - 1040#64 - 16640#64) 12544 ∗ memRegion (s0.sp - 104#64) authenticatorSize ∗
       cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b) := by
    rw [memRegion_992_split_b2a s0.sp, stackAt_authNew_split_allocHook (s0.sp - 1040#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_split ?_
  refine init_inner_clone_b2a hA s0 s1 out akPtr authKey st0 _ R
    hsp0_align hlt hfit hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1 ?_
  intro s2 hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx0_2 hx1_2 hcs2 htr2
  refine initInner_seq_sepWP (init_inner_bl_192 s2 _ hpc2 hrun2) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hvm3, hsp3, hlr3, hx0_3, hx1_3, hcs3, htr3⟩
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
       memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b) =
      (memRegion (s0.sp - 104#64) authenticatorSize ∗
       vecU8 A.repAlloc (s0.sp - 1032#64) authKey ∗
       A.pool lim (M.stepEvents (cloneEvs authKey) st0) s3 ∗
       stackAt (s0.sp - 1040#64) authNewStackX) ∗
      (cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1008#64) 17 ∗ cells (s0.sp - 872#64) 20 ∗
       cells (s0.sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
       memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
       memRegion (s0.sp - 1040#64) 8 ∗ initInnerSavedCells s0 ∗
       memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b) := by
    rw [stackAt_authNew_split_allocHook (s0.sp - 1040#64), ← A.pool_of_vmPreserved hvm3]
    sep_ac_rfl
  refine hcall_auth s3 ((tripleRatchetProgAtExt b ext).fnAddr initInnerName + 196#64) _ _
    (fun img h0 => hinv3 img (hinv2 img (hinv1 img h0)))
    hpc3 hrun3 (hsp3.trans hsp2) hlr3 (htr3.trans htr2)
    (hx0_3.trans hx0_2) (hx1_3.trans hx1_2) hfit_auth hsplit_auth ?_
  intro s4 evs₂ a0 a1 a2 a3 a4 a5 hpc4 hrun4 hsp4 hcs4 htr4 hevs₂
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
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b)) ⊢
      (((s0.sp - 104#64) ↦₆₄ a0) ∗ ((s0.sp - 96#64) ↦₆₄ a1) ∗ ((s0.sp - 88#64) ↦₆₄ a2) ∗
       ((s0.sp - 80#64) ↦₆₄ a3) ∗ ((s0.sp - 72#64) ↦₆₄ a4) ∗ ((s0.sp - 64#64) ↦₆₄ a5)) ∗
      authenticatorHeap A.repAlloc a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
      cells (s0.sp - 56#64) 1 ∗ cells (s0.sp - 1032#64) 20 ∗
      cells (s0.sp - 872#64) 20 ∗ cells (s0.sp - 712#64) 17 ∗
      (∃∗ b0 : BitVec 8, (s0.sp - 576#64) ↦₈ b0) ∗
      memRegion (s0.sp - 575#64) 7 ∗ memRegion (s0.sp - 568#64) 464 ∗
      (memRegion (s0.sp - 1040#64) 8 ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) := by
    rw [← memRegion_24_and_cells_17_eq_cells_20 s0.sp]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre_post_auth ?_
  refine initInner_seq_sepWP
    (init_inner_b2a_post_auth (A := A.repAlloc) (F := F) s0 s4 out authKey a0 a1 a2 a3 a4 a5 _
      hsp0_align hpc4 hrun4 hsp4 hx29_4 hx19_4 hcs_hi4 htr4) ?_
  intro s5 hpc5 hrun5 _ ⟨hvm5, hsp5, hx8_5, hx0_5, hcs5, htr5⟩
  have hpool5 :
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗
      (memRegion (s0.sp - 1040#64) 8 ∗ stackAt (s0.sp - 1040#64) authNewStackX ∗
       initInnerSavedCells s0 ∗ memRegion out optProtoInnerStateSize ∗
       (akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗
       A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s4) ⊢
      chunkedStatesAt A.repAlloc (s0.sp - 1032#64) (initV1State F .b2a authKey) ∗
      memRegion (s0.sp - 104#64) 56 ∗ memRegion (s0.sp - 1040#64) 8 ∗
      stackAt (s0.sp - 1040#64) authNewStackX ∗ initInnerSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
      statesIntoPbJumpTableAt b ∗
      A.pool lim (M.stepEvents evs₂ (M.stepEvents (cloneEvs authKey) st0)) s5 := by
    rw [A.pool_of_vmPreserved hvm5]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpool5 ?_
  exact init_inner_from_412 s0 s5 out akPtr .b2a authKey st0 evs₂ R hinto_b2a hb hsp0_align
    hfit hevs₂ hpc5 hrun5 hsp5 hx8_5 hx0_5 hcs5 htr5

/-- Unified budget-threaded body of `spqr::init_inner` for all `(v, d)`. -/
theorem init_inner_body
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (hinto_a2b : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F b (initV1State F .a2b authKey)))
    (hinto_b2a : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F b (initV1State F .b2a authKey)))
    (s0 : State) (x : InitInnerGhost) (st0 : M.σ) (R : SepProp)
    (hcall_auth : AuthBudgetCallAt M A lim F b ext s0 x.authKey
      (M.stepEvents (cloneEvs x.authKey) st0)
      (InitInnerBudgetPost M A lim F b s0 x st0) R)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr initInnerName)
    (hrun : s0.status = .Running)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpure :
      s0.readReg64 .x0 = x.out ∧ s0.readReg32 .x1 = x.v.toI32 ∧
      s0.readReg32 .x2 = x.d.toI32 ∧ s0.readReg64 .x3 = x.akPtr ∧
      s0.readReg64 .x4 = BitVec.ofNat 64 x.authKey.length ∧
      x.akPtr ≠ 0#64 ∧ 32 + x.authKey.length < 2 ^ 63 ∧
      b &&& 0xfff#64 = 0#64 ∧ FitsEnv M lim st0 (InitInnerEnv F x)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
      (memRegion x.out optProtoInnerStateSize ∗ (x.akPtr ↦ₛ x.authKey) ∗
       statesIntoPbJumpTableAt b ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initInnerStack)
      (InitInnerBudgetPost M A lim F b s0 x st0)
      (InitInnerBudgetPanic R) := by
  rcases x with ⟨out, v, d, akPtr, authKey⟩
  rcases hpure with ⟨hx0, hw1, hw2, hx3, hx4, _, hlt32, hb, hfit⟩
  cases v
  · have hpre_v0 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initInnerStack ⊢
        memRegion out optProtoInnerStateSize ∗ stackAt s0.sp initInnerStack ∗
        ((akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗ A.pool lim st0 s0) :=
      Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_v0 ?_
    refine initInner_seq_sepWP
      (init_inner_v0 (A := A.repAlloc) (F := F) s0 out d authKey
        ((akPtr ↦ₛ authKey) ∗ statesIntoPbJumpTableAt b ∗ A.pool lim st0 s0)
        hsp0_align hpc hrun hx0 hw1) ?_
    intro sf hpcf hrunf _ ⟨hvmf, hspf, hcsf, htrf⟩
    refine SepWPp.done hpcf hrunf ⟨⟨[], rfl, ?_⟩, hspf, hcsf, htrf⟩
    rw [M.stepEvents_nil, A.pool_of_vmPreserved hvmf]
    exact Entails.of_eq (by sep_ac_rfl)
  · change FitsEnv M lim st0 (SpqrBoundedEvs 96 (2 * authKey.length + 2048)) at hfit
    have hpre_v1 :
        memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
        statesIntoPbJumpTableAt b ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initInnerStack ⊢
        cells (s0.sp - 48#64) 6 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTableAt b ∗ A.pool lim st0 s0 ∗
         stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) := by
      rw [stackAt_initInner_split s0.sp]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpre_v1 ?_
    refine initInner_seq_sepWP
      (init_inner_prologue_v1 s0 out akPtr d authKey _
        hsp0_align hpc hrun hx0 hw1 hw2 hx3 hx4) ?_
    intro s1 hpc1 hrun1 hinv1 ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hw2_1, hx3_1, hcs1, htr1⟩
    have hpool1 :
        initInnerSavedCells s0 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTableAt b ∗ A.pool lim st0 s0 ∗
         stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) ⊢
        initInnerSavedCells s0 ∗
        (memRegion out optProtoInnerStateSize ∗ (akPtr ↦ₛ authKey) ∗
         statesIntoPbJumpTableAt b ∗ A.pool lim st0 s1 ∗
         stackAt (s0.sp - 1040#64) authNewStackX ∗ memRegion (s0.sp - 1040#64) 992) := by
      rw [A.pool_of_vmPreserved hvm1]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hpool1 ?_
    cases d
    · exact init_inner_v1_a2b hA (hinto_a2b authKey) s0 s1 out akPtr st0 R hcall_auth
        hb hsp0_align (by dsimp at hlt32; omega) hfit hinv1 hpc1 hrun1 hsp1
        hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1
    · exact init_inner_v1_b2a hA (hinto_b2a authKey) s0 s1 out akPtr st0 R hcall_auth
        hb hsp0_align (by dsimp at hlt32; omega) hfit hinv1 hpc1 hrun1 hsp1
        hx29_1 hx19_1 hx20_1 hw2_1 hx3_1 hcs1 htr1

/-! ## 7. Top-Level Budget-Threaded Entrypoints (`InitInnerOkExt`, `InitInnerOkX`) -/

/-- Verification of `spqr::init_inner` (`0x532dc`) against `initInnerSpec M A lim F b` given
    the two `<States>::into_pb` arms (`keysUnsampled`, `noHeaderReceived`) and
    `AuthNewBudgetOkExt`. -/
theorem init_inner_ok_ext_of_arms
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (hauth : AuthNewBudgetOkExt b M A lim F ext)
    (hinto_a2b : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F b (initV1State F .a2b authKey)))
    (hinto_b2a : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F b (initV1State F .b2a authKey))) :
    InitInnerOkExt b M A lim F ext := by
  refine subroutine_ok_of_sepWPp fun (x, st0) R s0 hpc hrun hpre hsp0_align => ?_
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [initInnerSpec, initInnerSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2.1
  have hcall_auth : AuthBudgetCallAt M A lim F b ext s0 x.authKey
      (M.stepEvents (cloneEvs x.authKey) st0)
      (InitInnerBudgetPost M A lim F b s0 x st0) R :=
    fun s ret_pc P Frame _ hpcs hruns hsps hlrs htrs hx0s hx1s hfits hsplits hnext =>
      call_authNew_budget_ext (sub_ok_authNew_budget_ext hauth)
        x.authKey (M.stepEvents (cloneEvs x.authKey) st0) hlt32 s0 s ret_pc P Frame R
        hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hfits hsplits hnext
  exact ⟨_, R, hm, sepWPp_of_init_inner_budget_wpp s0 s0 x st0 _ R
    (init_inner_body hA hinto_a2b hinto_b2a s0 x st0 R hcall_auth hpc hrun hsp0_align hpure)⟩

/-- Envelope-parametric `<Authenticator>::new` variant of `init_inner_ok_ext_of_arms`. -/
theorem init_inner_ok_ext_of_arms_of_authEnv
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {AuthEnv : AuthNewGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (hauth : AuthNewBudgetOkExtOfEnv b M A lim F AuthEnv ext)
    (hauth_sub : ∀ x evs, AuthEnv x evs → AuthNewBudgetEnv x evs)
    (hinto_a2b : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F b (initV1State F .a2b authKey)))
    (hinto_b2a : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F b (initV1State F .b2a authKey))) :
    InitInnerOkExt b M A lim F ext :=
  init_inner_ok_ext_of_arms hA (hauth.mono_env hauth_sub) hinto_a2b hinto_b2a

/-- Verification of `spqr::init_inner` (`0x532dc`) against
    `(initInnerSpecX M A lim F img.base).inImage img` given the two `<States>::into_pb` arms and
    `AuthNewBudgetOkX`. -/
theorem init_inner_ok_x_of_arms
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsBudget img.base M A lim ext)
    (hauth : AuthNewBudgetOkX img M A lim F ext)
    (hinto_a2b : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F img.base (initV1State F .a2b authKey)))
    (hinto_b2a : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F img.base (initV1State F .b2a authKey))) :
    InitInnerOkX img M A lim F ext := by
  refine subroutine_ok_of_sepWPp fun (x, st0) R s0 hpc hrun hpre hsp0_align => ?_
  have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
  dsimp only [Spec.inImage, initInnerSpecX, initInnerSpecXOfEnv] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hm⟩
  have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2.1
  have hcall_auth : AuthBudgetCallAt M A lim F img.base ext s0 x.authKey
      (M.stepEvents (cloneEvs x.authKey) st0)
      (InitInnerBudgetPost M A lim F img.base s0 x st0) R :=
    fun s ret_pc P Frame hinv_s hpcs hruns hsps hlrs htrs hx0s hx1s hfits hsplits hnext =>
      call_authNew_budget_x (sub_ok_authNew_budget_x hauth)
        x.authKey (M.stepEvents (cloneEvs x.authKey) st0) hlt32 s0 s ret_pc P Frame R
        (hinv_s img hinv0) hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hfits hsplits hnext
  exact ⟨_, R, hm, sepWPp_of_init_inner_budget_wpp s0 s0 x st0 _ R
    (init_inner_body hA hinto_a2b hinto_b2a s0 x st0 R hcall_auth hpc hrun hsp0_align hpure)⟩

/-- Envelope-parametric `<Authenticator>::new` variant of `init_inner_ok_x_of_arms`. -/
theorem init_inner_ok_x_of_arms_of_authEnv
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {AuthEnv : AuthNewGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsBudget img.base M A lim ext)
    (hauth : AuthNewBudgetOkXOfEnv img M A lim F AuthEnv ext)
    (hauth_sub : ∀ x evs, AuthEnv x evs → AuthNewBudgetEnv x evs)
    (hinto_a2b : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F img.base (initV1State F .a2b authKey)))
    (hinto_b2a : ∀ authKey : Bytes,
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesIntoPbName)
        (statesIntoPbVariantSpec M A lim F img.base (initV1State F .b2a authKey))) :
    InitInnerOkX img M A lim F ext :=
  init_inner_ok_x_of_arms himg hA (hauth.mono_env hauth_sub) hinto_a2b hinto_b2a

/-- Verification of `spqr::init_inner` (`0x532dc`) from full `StatesIntoPbOkExt`. -/
theorem init_inner_ok_ext_of_intoPb
    {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext)
    (hauth : AuthNewBudgetOkExt b M A lim F ext)
    (hinto : StatesIntoPbOkExt b M A lim F ext) :
    InitInnerOkExt b M A lim F ext :=
  init_inner_ok_ext_of_arms hA hauth
    (fun authKey => statesIntoPbVariantSpec_of_statesIntoPbSpec hinto _)
    (fun authKey => statesIntoPbVariantSpec_of_statesIntoPbSpec hinto _)

/-- Verification of `spqr::init_inner` (`0x532dc`) in-image from full `StatesIntoPbOkExt`. -/
theorem init_inner_ok_x_of_intoPb
    {img : Obj.Image} {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsBudget img.base M A lim ext)
    (hauth : AuthNewBudgetOkX img M A lim F ext)
    (hinto : StatesIntoPbOkExt img.base M A lim F ext) :
    InitInnerOkX img M A lim F ext :=
  init_inner_ok_x_of_arms himg hA hauth
    (fun authKey => statesIntoPbVariantSpec_of_statesIntoPbSpec hinto _)
    (fun authKey => statesIntoPbVariantSpec_of_statesIntoPbSpec hinto _)

end LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofBudgetAux
