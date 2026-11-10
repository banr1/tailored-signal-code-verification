/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPb
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
meta import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Closed `[LibsignalPlacement]` Contracts for Blocks `330`, `286`, and `339`

Proves closed `[LibsignalPlacement]` contracts under `RustCliAllocBudget M` for
`<Authenticator>::from_pb` (Block `330`), `drop_glue::<unchunked::Ct1SentEkReceived>` (Block `286`),
and `<Ct1Sent>::from_pb` (Block `339`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_333 blkPC_339 blkPl_339 extract_withLsCodeLoaded libsignalSessionLib
   lsProg_286 lsProg_330 lsProg_333 lsProg_339 ls_blockPlacement_base
   ls_subroutine_ok_of_block lscall_blk_cl lsmpl lsρ sepWP_seq_lscl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withMemEq)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator CIPHERTEXT1_SIZE ENCAPSULATION_STATE_SIZE HEADER_SIZE
   ProtoAuthenticator V1State spqrAuthApi)
open CryptoVerification.SpqrV1.ProtoRepr (AuthenticatorPBGhost authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.Auth (AuthFromPbPinnedGhost authFromPbStack authenticatorAt)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (DropProtoUnchunkedCt1SentEkReceivedGhost Saved48Preserved ThreeVecGhost
   auth72HeadersAt auth72HeadersAt_entails_memRegion_48 cap_add_one_beq_zero_false
   dropStack32 optProtoAuthenticatorAt optProtoAuthenticatorAt_72_none
   optProtoAuthenticatorAt_72_none_entails_memRegion_48 optProtoAuthenticatorAt_some
   protoAuthenticatorAt_entails_dealloc protoUnchunked3VecHeadersAt
   protoUnchunked3VecHeadersAt_entails_memRegion_128 protoUnchunkedCt1SentAt
   protoUnchunkedCt1SentEkReceivedAt protoUnchunkedCt1SentEkReceivedSize
   twoVecHeadersAt_72_eq vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Unchunked
  (Ct1SentFromPbGhost authenticatorAt_unpack authenticatorPBPinnedAt_entails_dealloc
   authenticatorPBPinnedAt_eq_cap_tail ct1SentAt ct1SentAt_pack ct1SentFromPbStack
   ct1SentResultAt memRegion_128_eq_cells16 memRegion_128_err_split
   memRegion_72_auth72_8_entails_128 memRegion_ct1Sent_scratch_restore
   ofNat_beq_lit_iff optProtoAuthenticatorAt_some_unpack protoUnchunkedCt1SentAt_unpack
   stackAt_authFromPb_split_allocHook_sub176
   stackAt_ct1SentFromPb_restore_from_allocHook stackAt_ct1SentFromPb_split
   stackAt_ct1SentFromPb_split_allocHook stackAt_ct1SentFromPb_split_dropStack32
   stackAt_ct1SentFromPb_tail_allocHook stackAt_ct1SentFromPb_tail_dropStack32
   unpacked_ct1Sent_auth_none_pack unpacked_ct1Sent_entails_dealloc
   unpacked_ct1Sent_headers_entails_memRegion_72_8 vecU8Payload)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authFromPbPinnedSpec authKeyCloneEvents
   auth_from_pb_pinned_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
  (dropProtoUnchunkedCt1SentEkReceivedSpec
   drop_proto_unchunked_ct1_sent_ek_received_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (Ct1SentFromPbPostEnv Ct1SentFromPbPreEnv authFromPbAllocEvents ct1SentFromPb
   ct1SentFromPbAllocEvents ct1SentFromPbSpec ct1SentFromPbSpecOfEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.Unchunked.extractLsb'_0_64_append
  CryptoVerification.SpqrV1.Unchunked.extractLsb'_64_64_append

private theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

abbrev spqrRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

/-! ## 1. Block `330`: `<Authenticator>::from_pb` Closed Budget-Threaded Contract -/

theorem auth_from_pb_pinned_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_330 H) (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 330)]
  exact subroutine_ok_withLsCodeLoaded_of_plain (auth_from_pb_pinned_placed_ok
    (spqr_hook_ok_of_mem hshim) (spqr_hook_ok_of_mem halloc) (spqr_hook_ok_of_mem hmemcpy))

theorem auth_from_pb_pinned_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 330 H) (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim)) :=
  ls_to_blockProgram (auth_from_pb_pinned_cl_placed_ok hshim halloc hmemcpy)

theorem auth_from_pb_pinned_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H]
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim)) :=
  ls_subroutine_ok_of_block (auth_from_pb_pinned_cl_placed_ok hshim halloc hmemcpy) hidx

theorem auth_from_pb_pinned_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H] {m : Memory}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 330)
      (withMemEq m (authFromPbPinnedSpec M A lim)) :=
  lscall_blk_cl (auth_from_pb_pinned_cl_placed_ok hshim halloc hmemcpy) hcl hidx

/-! ## 2. Block `286`: `drop_glue::<unchunked::Ct1SentEkReceived>` Closed Budget-Threaded Contract -/

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_286 H) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 286)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_unchunked_ct1_sent_ek_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 H) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc)

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H]
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hidx

theorem drop_proto_unchunked_ct1_sent_ek_received_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H] {m : Memory}
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hcl hidx

/-! ## 3. Private Helpers for Block `339` (`<Ct1Sent>::from_pb`) -/

@[local simp]
private theorem spqrAuthApi_from_pb (F : ShaCompress) :
    (spqrAuthApi F).from_pb = Authenticator.fromPb := rfl

@[local arm64_norm]
private theorem sub_beq_zero_eq_beq (x y : BitVec 64) :
    (x - y == 0#64) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x - y ≠ 0#64 := by intro h0; apply h; bv_omega
    simp [h, hne]

@[local arm64_norm]
private theorem bne_eq_not_beq (x y : BitVec 64) : (x != y) = !(x == y) := rfl

private theorem authKeyCloneEvents_eq (bs : List (BitVec 8)) :
    authKeyCloneEvents bs = (if bs = [] then [] else rustAllocEvents bs.length 1) := by
  cases bs <;> rfl

private theorem authFromPbEvents_eq_allocEvents (auth : ProtoAuthenticator) :
    authFromPbEvents auth = authFromPbAllocEvents auth := by
  simp only [authFromPbEvents, authFromPbAllocEvents, authKeyCloneEvents_eq]

private theorem ct1SentFromPbAllocEvents_of_cond_false (F : ShaCompress)
    (pb : V1State.Unchunked.Ct1Sent)
    (hcond : (pb.hdr.length == HEADER_SIZE &&
      pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false) :
    ct1SentFromPbAllocEvents F pb = [] := by
  simp [ct1SentFromPbAllocEvents, ct1SentFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb, hcond]

private theorem ct1SentFromPbAllocEvents_of_auth_none (F : ShaCompress)
    (pb : V1State.Unchunked.Ct1Sent) (hauth : pb.auth = none) :
    ct1SentFromPbAllocEvents F pb = [] := by
  simp [ct1SentFromPbAllocEvents, hauth]

private theorem ct1SentFromPbAllocEvents_of_ok (F : ShaCompress)
    (pb : V1State.Unchunked.Ct1Sent) (auth : ProtoAuthenticator)
    (hcond : (pb.hdr.length == HEADER_SIZE &&
      pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth) :
    ct1SentFromPbAllocEvents F pb = authFromPbAllocEvents auth := by
  simp [ct1SentFromPbAllocEvents, ct1SentFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb, hcond, hauth]

private theorem fitsEnv_auth_of_ct1 {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {pb : V1State.Unchunked.Ct1Sent} {auth : ProtoAuthenticator}
    (hcond : (pb.hdr.length == HEADER_SIZE &&
      pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hfits : FitsEnv M lim st (Ct1SentFromPbPreEnv F pb)) :
    FitsEnv M lim st (AuthFromPbEnv auth) := by
  intro evs hevs
  apply hfits
  simp only [Ct1SentFromPbPreEnv, ct1SentFromPbAllocEvents_of_ok F pb auth hcond hauth]
  simpa only [AuthFromPbEnv, authFromPbEvents_eq_allocEvents] using hevs

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem authenticatorAt_sub168_unpack (A : RustAlloc) (sp : BitVec 64)
    (auth : Authenticator) :
    authenticatorAt A (sp - 168#64) auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64, ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        (((sp - 168#64) ↦₆₄ ca1) ∗ ((sp - 160#64) ↦₆₄ pa1) ∗
         ((sp - 152#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp - 144#64) ↦₆₄ ca2) ∗ ((sp - 136#64) ↦₆₄ pa2) ∗
         ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗ vecU8Payload A ca2 pa2 auth.macKey := by
  have h := authenticatorAt_unpack A (sp - 168#64) auth
  have h1 : (sp - 168#64) + 8#64 = sp - 160#64 := by bv_omega
  have h2 : (sp - 168#64) + 16#64 = sp - 152#64 := by bv_omega
  have h3 : (sp - 168#64) + 24#64 = sp - 144#64 := by bv_omega
  have h4 : (sp - 168#64) + 32#64 = sp - 136#64 := by bv_omega
  have h5 : (sp - 168#64) + 40#64 = sp - 128#64 := by bv_omega
  rw [h1, h2, h3, h4, h5] at h; exact h

private theorem authenticatorPBPinnedAt_72_entails_dealloc (A : RustAlloc)
    (ga : AuthenticatorPBGhost) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 72#64) auth ⊢
      auth72HeadersAt a ⟨ga.rootKey, ga.macKey⟩ ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
        vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  rw [← twoVecHeadersAt_72_eq]
  exact authenticatorPBPinnedAt_entails_dealloc A ga (a + 72#64) auth

private theorem memRegion_176_128_split_8_48_72 (sp : BitVec 64) :
    memRegion (sp - 176#64) 128 =
      memRegion (sp - 176#64) 8 ∗ memRegion (sp - 168#64) 48 ∗ memRegion (sp - 120#64) 72 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 120)
        (b' := sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 48) (k := 72)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide)]

private abbrev RetPost {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private theorem close_ct1_post {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {pbA : BitVec 64} {pb : V1State.Unchunked.Ct1Sent}
    {st0 : M.σ} {s0 sf : State} {Pf Res R : SepProp} {evsAll : List AllocEvent}
    (hp : Pf ⊢ Res ∗ memRegion pbA 128 ∗ A.pool lim (M.stepEvents evsAll st0) sf ∗
      stackAt s0.sp ct1SentFromPbStack)
    (htr : sf.trace = s0.trace)
    (hevs : Ct1SentFromPbPostEnv F pb evsAll)
    (hm : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ Res ∗ memRegion pbA 128 ∗
      (∃∗ evs : List AllocEvent, ⌜Ct1SentFromPbPostEnv F pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st0) sf) ∗
      stackAt s0.sp ct1SentFromPbStack) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hp) hm)⟩
  refine Entails.trans (Entails.of_eq (show _ =
    A.pool lim (M.stepEvents evsAll st0) sf ∗
      (Res ∗ memRegion pbA 128 ∗ stackAt s0.sp ct1SentFromPbStack ∗ R) by sep_ac_rfl)) ?_
  have hex : A.pool lim (M.stepEvents evsAll st0) sf ⊢
      ∃∗ evs : List AllocEvent, ⌜Ct1SentFromPbPostEnv F pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st0) sf :=
    Entails.sepExists_right evsAll (Entails.pure_right hevs (Entails.refl _))
  exact Entails.trans (sepConj_mono_left hex) (Entails.of_eq (by sep_ac_rfl))

private theorem sepWP_cut {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (mid : BitVec 64) (Q : State → SepProp → Prop)
    (h1 : SepWP prog mid s P Q)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q sm Pm → SepWP prog target sm Pm post) :
    SepWP prog target s P post := SepWP.seq h1 h2

private theorem sepWP_cut_lscl [LibsignalPlacement] {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (mid : BitVec 64) (Q : State → SepProp → Prop)
    (h1 : SepWP prog mid s P Q)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm Pm → SepWP prog target sm Pm post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hQ hclm => h2 sm Pm hpc hrun hclm hQ)

private theorem calleeSavedPreserved_trans {s0 sm sf : State}
    (h1 : CalleeSavedPreserved s0 sm) (h2 : CalleeSavedPreserved sm sf) :
    CalleeSavedPreserved s0 sf := by
  rcases h1 with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
  rcases h2 with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
  exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22,
    h23'.trans h23, h24'.trans h24, h25'.trans h25, h26'.trans h26,
    h27'.trans h27, h28'.trans h28, hfp'.trans hfp, hv'.trans hv⟩

private theorem sepWP_strengthen_entails {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 : State → SepProp} {R : State → Prop}
    (h : ∀ sm, Q1 sm ⊢ Q2 sm)
    (hwp : SepWP prog target s P (fun sm Pm => (Pm ⊢ Q1 sm) ∧ R sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ Q2 sm) ∧ R sm) :=
  SepWP.mono hwp fun sm _ _ _ ⟨hp, hr⟩ => ⟨Entails.trans hp (h sm), hr⟩

private theorem sepWP_evs_step {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

private theorem sepWP_close_ret {prog : Program} {s0 s : State} {P : SepProp}
    {Post : State → SepProp → Prop} (Q_out : State → SepProp)
    (h : SepWP prog (s0.readReg64 .lr) s P (fun sf Pf =>
      (Pf ⊢ Q_out sf) ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ CalleeSavedPreserved s0 sf))
    (hpost : ∀ sf Pf, (Pf ⊢ Q_out sf) → sf.sp = s0.sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → Post sf Pf) :
    SepWP prog (s0.readReg64 .lr) s P Post :=
  SepWP.mono h fun sf Pf _ _ ⟨hp, hsp_f, htr_f, hcs_f⟩ => hpost sf Pf hp hsp_f htr_f hcs_f


set_option maxHeartbeats 800000 in
private theorem ct1_sent_from_pb_err_drop_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    {out pbA : BitVec 64} {pb : V1State.Unchunked.Ct1Sent} {st0 : M.σ}
    {R : SepProp} {s0 s1 : State}
    {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : ThreeVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_339).base + 236#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 119) ∗
        (protoUnchunked3VecHeadersAt pbA g ∗ optProtoAuthenticatorAt A.repAlloc (pbA + 72#64) pb.auth ∗
          memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        A.pool lim st0 s1 ∗ memRegion (s0.sp - 4336#64) 64 ∗
        stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ct1SentFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have halloc_nil := ct1SentFromPbAllocEvents_of_cond_false F pb hcond
  unfold RetPost ct1SentFromPbSpec ct1SentFromPbSpecOfEnv; dsimp only
  simp only [ct1SentFromPb, CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb,
    hcond, Bool.false_eq_true, ↓reduceIte, ct1SentResultAt]
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
  refine seq_clean_evs (mid := (blkPl_339).base + 296#64)
    (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
      (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 8 ∗
        vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
      A.pool lim (M.stepEvents evs st0) sm ∗ memRegion (s0.sp - 4336#64) 64 ∗
      stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · cases pb.auth with
    | none =>
      rw [optProtoAuthenticatorAt_72_none]; apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      refine sepWP_strengthen_entails (fun _ => sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_left (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A.repAlloc pbA))))) ?_
      wp_steps_sync_pool ((blkPl_339).base + 296#64); simp only [State.setMem_setMem]; dsimp only [noneCap]; wp_done
    | some a =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (protoAuthenticatorAt_entails_dealloc A.repAlloc (pbA + 72#64) a))))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga; rw [twoVecHeadersAt_72_eq]
      have hpull_ga :
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 119) ∗
            (protoUnchunked3VecHeadersAt pbA g ∗ (⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗ auth72HeadersAt pbA ga ∗
              vecCapPtrDealloc A.repAlloc ga.v1.cap ga.v1.ptr ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
              memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
            A.pool lim st0 s1 ∗ memRegion (s0.sp - 4336#64) 64 ∗ stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) =
          (⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗ (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 119) ∗
            (protoUnchunked3VecHeadersAt pbA g ∗ (auth72HeadersAt pbA ga ∗ vecCapPtrDealloc A.repAlloc ga.v1.cap ga.v1.ptr ∗
              vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
            A.pool lim st0 s1 ∗ memRegion (s0.sp - 4336#64) 64 ∗ stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) := by sep_ac_rfl
      rw [hpull_ga]; apply SepWP.pure_elim; intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine seq_clean_evs (mid := (blkPl_339).base + 276#64)
        (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
          (protoUnchunked3VecHeadersAt pbA g ∗
            (auth72HeadersAt pbA ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
            memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim (M.stepEvents evs st0) sm ∗ memRegion (s0.sp - 4336#64) 64 ∗
          stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [auth72HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
          wp_steps_sync_pool ((blkPl_339).base + 276#64)
          simp only [State.setMem_setMem]; dsimp only [noneCap]; wp_done
        · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
          wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          simp only [State.setMem_setMem]
          have hsp_sub : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
            ProofLib.spAligned_sub s0.sp 176#64 hsp_align (by decide)
          wp_apply; refine align_pre_st (by rw [hsp_1]; dsimp only [noneCap]; sep_ac_rfl) ?_; wp_done
      · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1⟩
        let sta1 := M.stepEvents evsa1 st0
        dsimp only [auth72HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_step evsa1 hevsa1; wp_steps
          refine SepWP.weaken_pre
            (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (auth72HeadersAt_entails_memRegion_48 pbA ga))))) ?_
          wp_done
        · apply sepWP_evs_step (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1)
            (hevsa1.append (FreeOnlyEvs.singleton 1 ga.v2.cap.toNat))
          have heq_st : M.stepEvents (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1) st0 =
              M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1 := by
            simp only [sta1, AllocCostModel.stepEvents_append]
          rw [heq_st]
          have hsp_sub : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
            ProofLib.spAligned_sub s0.sp 176#64 hsp_align (by decide)
          wp_steps; wp_apply
          refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
            (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
              (protoUnchunked3VecHeadersAt pbA g ∗ auth72HeadersAt pbA ga ∗ memRegion (pbA + 120#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1) _ ∗
              memRegion (s0.sp - 4336#64) 64 ∗ stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) by
              rw [hsp_a1]; unfold auth72HeadersAt vecCapPtrDealloc
              dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]; sep_ac_rfl))
            (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (auth72HeadersAt_entails_memRegion_48 pbA ga)))))) ?_
          dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]; wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    let st1 := M.stepEvents evs1 st0
    refine seq_clean_evs (mid := (blkPl_339).base + 316#64)
      (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
        (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
        A.pool lim (M.stepEvents evs st1) sm ∗ memRegion (s0.sp - 4336#64) 64 ∗
        stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        have hsp_sub : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
          ProofLib.spAligned_sub s0.sp 176#64 hsp_align (by decide)
        wp_steps; wp_apply; refine align_pre_st (by rw [hsp_2]; sep_ac_rfl) ?_; wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs (mid := (blkPl_339).base + 336#64)
        (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
          (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 8 ∗
            vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr) ∗
          A.pool lim (M.stepEvents evs st2) sm ∗ memRegion (s0.sp - 4336#64) 64 ∗
          stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps; wp_done
        · apply sepWP_evs_dealloc g.v2.cap.toNat 1
          have hsp_sub : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
            ProofLib.spAligned_sub s0.sp 176#64 hsp_align (by decide)
          wp_steps; wp_apply; refine align_pre_st (by rw [hsp_3]; sep_ac_rfl) ?_; wp_done
      · intro evs3 s4 hevs3 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
        let st3 := M.stepEvents evs3 st2
        dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · refine sepWP_close_ret
            (fun sf => ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
              memRegion pbA 128 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3) st0) sf ∗
              stackAt s0.sp ct1SentFromPbStack)
            ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ct1_post hp htr_f
              ⟨evs1 ++ evs2 ++ evs3, (hevs1.append hevs2).append hevs3,
                by rw [halloc_nil, List.nil_append]⟩, hsp_f, hcs_f⟩)
          have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3) st0 = st3 := by
            simp only [st1, st2, st3, AllocCostModel.stepEvents_append]
          rw [heq_st]; wp_steps
          refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
            (protoUnchunked3VecHeadersAt_entails_memRegion_128 pbA g)
            (sepConj_mono_right (stackAt_ct1SentFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
          wp_done
        · refine sepWP_close_ret
            (fun sf => ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
              memRegion pbA 128 ∗
              A.pool lim (M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1) st0) sf ∗
              stackAt s0.sp ct1SentFromPbStack)
            ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ct1_post hp htr_f
              ⟨evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1,
                ((hevs1.append hevs2).append hevs3).append (FreeOnlyEvs.singleton 1 g.v3.cap.toNat),
                by rw [halloc_nil, List.nil_append]⟩, hsp_f, hcs_f⟩)
          have heq_st : M.stepEvents (evs1 ++ evs2 ++ evs3 ++ rustDeallocEvents g.v3.cap.toNat 1) st0 =
              M.stepEvents (rustDeallocEvents g.v3.cap.toNat 1) st3 := by
            simp only [st1, st2, st3, AllocCostModel.stepEvents_append]
          rw [heq_st]; wp_steps
          refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
            (Entails.trans
              (Entails.of_eq (show _ =
                (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 8) ∗
                (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) by
                  unfold protoUnchunked3VecHeadersAt; sep_ac_rfl))
              (sepConj_mono_left (protoUnchunked3VecHeadersAt_entails_memRegion_128 pbA g)))
            (sepConj_mono_right (stackAt_ct1SentFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
          have hlr0' : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr0
          wp_apply; rw [stackAt_ct1SentFromPb_split_allocHook s0.sp]; wp_done

private theorem ct1_sent_from_pb_err_drop_unpacked_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 c3 p3 : BitVec 64}
    {pb : V1State.Unchunked.Ct1Sent} {st0 : M.σ} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_339).base + 236#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (memRegion out 128 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A.repAlloc (pbA + 72#64) pb.auth ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
        A.pool lim st0 s1 ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ct1SentFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub176 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_128_err_split out)
    (sepConj_mono_left (unpacked_ct1Sent_entails_dealloc A.repAlloc pbA c1 p1
      (BitVec.ofNat 64 pb.hdr.length) c2 p2 (BitVec.ofNat 64 pb.es.length)
      c3 p3 (BitVec.ofNat 64 pb.ct1.length) pb.epoch pb.auth pb.hdr pb.es pb.ct1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0
  apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (ct1_sent_from_pb_err_drop_placed (v_out0 := v_out0) (v_out8 := v_out8)
      (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩⟩) hdealloc_raw hcond hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align hlr0)

set_option maxHeartbeats 1200000 in
private theorem ct1_sent_from_pb_ok_after_auth_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 c3 p3 : BitVec 64}
    {pb : V1State.Unchunked.Ct1Sent} {auth : ProtoAuthenticator} {st0 : M.σ}
    {ga : AuthenticatorPBGhost} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.hdr.length == HEADER_SIZE &&
      pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hpc1 : s1.pc = (blkPl_339).base + 92#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64))
    (hx19_1 : s1.readReg64 .x19 = pbA) (hx20_1 : s1.readReg64 .x20 = ga.rootKey.cap)
    (hx21_1 : s1.readReg64 .x21 = pb.epoch) (hx22_1 : s1.readReg64 .x22 = out)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (memRegion out 128 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         authenticatorPBPinnedAt A.repAlloc ga (pbA + 72#64) auth ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
        A.pool lim (M.stepEvents (authFromPbAllocEvents auth) st0) s1 ∗
        stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 8 ∗
        authenticatorAt A.repAlloc (s0.sp - 168#64) (Authenticator.fromPb auth) ∗
        memRegion (s0.sp - 120#64) 72 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ct1SentFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have halloc_ok := ct1SentFromPbAllocEvents_of_ok F pb auth hcond hauth
  let stA := M.stepEvents (authFromPbAllocEvents auth) st0
  unfold RetPost ct1SentFromPbSpec ct1SentFromPbSpecOfEnv; dsimp only [spqrAuthApi]
  simp only [ct1SentFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb, hcond, hauth,
    ↓reduceIte, ct1SentResultAt]
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
  refine sepWP_cut ((blkPl_339).base + 180#64)
    (fun sm Pm => (Pm ⊢ (ct1SentAt A.repAlloc (F := F) out
        { epoch := pb.epoch, auth := Authenticator.fromPb auth,
          hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
      (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8 ∗
        vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
        vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr) ∗
      A.pool lim stA sm ∗ memRegion (s0.sp - 4336#64) 64 ∗
      stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
      Saved48Preserved s0 sm (s0.sp - 176#64) ∧
      sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap) ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left
              (authenticatorPBPinnedAt_72_entails_dealloc A.repAlloc ga pbA auth)))))))))))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (authenticatorAt_sub168_unpack A.repAlloc s0.sp (Authenticator.fromPb auth)))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.SepWP.exists_left; intro ca1; apply ProofLib.SepWP.exists_left; intro pa1
    apply ProofLib.SepWP.exists_left; intro ca2; apply ProofLib.SepWP.exists_left; intro pa2
    rw [ProofLib.memRegion_cells (s0.sp - 120#64) 9 (by decide), memRegion_128_eq_cells16 out]
    cells_unfold
    simp only [ProofLib.cells_succ, ProofLib.cells_zero,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]
    wp_pull_exists; wp_steps_sync_pool ((blkPl_339).base + 180#64)
    simp only [State.setMem_setMem]; rw [stackAt_authFromPb_split_allocHook_sub176 s0.sp]
    have hpack_out := ct1SentAt_pack A.repAlloc (F := F) out
      ca1 pa1 ca2 pa2 c1 p1 c2 p2 c3 p3 pb.epoch (Authenticator.fromPb auth) pb.hdr pb.es pb.ct1
    have hpack_sp := memRegion_ct1Sent_scratch_restore s0.sp
      ca1 pa1 (BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length)
      ca2 pa2 (BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)
      c1 p1 (BitVec.ofNat 64 pb.hdr.length) c2 p2 (BitVec.ofNat 64 pb.es.length)
      c3 p3 (BitVec.ofNat 64 pb.ct1.length)
    have hpack_pb := unpacked_ct1Sent_headers_entails_memRegion_72_8 pbA
      c1 p1 (BitVec.ofNat 64 pb.hdr.length) c2 p2 (BitVec.ofNat 64 pb.es.length)
      c3 p3 (BitVec.ofNat 64 pb.ct1.length) pb.epoch
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) ∗
        ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((out + 96#64) ↦₆₄ c3) ∗ ((out + 104#64) ↦₆₄ p3) ∗ ((out + 112#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((out + 120#64) ↦₆₄ pb.epoch)) ∗
       vecU8Payload A.repAlloc ca1 pa1 (Authenticator.fromPb auth).rootKey ∗
       vecU8Payload A.repAlloc ca2 pa2 (Authenticator.fromPb auth).macKey ∗
       vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
      (((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((pbA + 120#64) ↦₆₄ pb.epoch)) ∗
       auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗
       vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr) ∗
      (memRegion (s0.sp - 176#64) 8 ∗
        (((s0.sp - 168#64) ↦₆₄ ca1) ∗ ((s0.sp - 160#64) ↦₆₄ pa1) ∗ ((s0.sp - 152#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
         ((s0.sp - 144#64) ↦₆₄ ca2) ∗ ((s0.sp - 136#64) ↦₆₄ pa2) ∗ ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)) ∗
        (((s0.sp - 120#64) ↦₆₄ c1) ∗ ((s0.sp - 112#64) ↦₆₄ p1) ∗ ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((s0.sp - 96#64) ↦₆₄ c2) ∗ ((s0.sp - 88#64) ↦₆₄ p2) ∗ ((s0.sp - 80#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((s0.sp - 72#64) ↦₆₄ c3) ∗ ((s0.sp - 64#64) ↦₆₄ p3) ∗ ((s0.sp - 56#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length))) ∗
      A.pool lim stA _ ∗ memRegion (s0.sp - 4336#64) 64 ∗ stackAt (s0.sp - 176#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) by sep_ac_rfl))
      (sepConj_mono hpack_out (sepConj_mono (sepConj_mono_left hpack_pb) (sepConj_mono_left hpack_sp)))) ?_
    refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro s2 _Pm hpc2 hrun2 ⟨hent2, ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
    refine SepWP.weaken_pre hent2 ?_
    refine seq_clean_evs (mid := (blkPl_339).base + 200#64)
      (P_evs := fun evs sm => (ct1SentAt A.repAlloc (F := F) out
          { epoch := pb.epoch, auth := Authenticator.fromPb auth,
            hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
        (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8 ∗
          vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr) ∗
        A.pool lim (M.stepEvents evs stA) sm ∗ memRegion (s0.sp - 4336#64) 64 ∗
        stackAt (s0.sp - 176#64) allocHookStack ∗ memRegion (s0.sp - 176#64) 128 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [auth72HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hca1 : (ga.rootKey.cap == 0#64) = true <;>
        simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc ga.rootKey.cap.toNat 1
        have hsp_sub : ((s0.sp - 176#64) &&& 15#64 == 0#64) = true :=
          ProofLib.spAligned_sub s0.sp 176#64 hsp_align (by decide)
        wp_steps; wp_apply; refine align_pre_st (by rw [hsp_2]; sep_ac_rfl) ?_; wp_done
    · intro evs1 s3 hevs1 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
      let st1 := M.stepEvents evs1 stA
      dsimp only [auth72HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hca2 : (ga.macKey.cap == 0#64) = true <;>
        simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_close_ret
          (fun sf => ct1SentAt A.repAlloc (F := F) out
              { epoch := pb.epoch, auth := Authenticator.fromPb auth,
                hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
            memRegion pbA 128 ∗ A.pool lim (M.stepEvents (authFromPbAllocEvents auth ++ evs1) st0) sf ∗
            stackAt s0.sp ct1SentFromPbStack)
          ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ct1_post hp htr_f
            ⟨evs1, hevs1, by rw [halloc_ok]⟩, hsp_f, hcs_f⟩)
        have heq_st : M.stepEvents (authFromPbAllocEvents auth ++ evs1) st0 = st1 := by
          simp only [stA, st1, AllocCostModel.stepEvents_append]
        rw [heq_st]; wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (memRegion_72_auth72_8_entails_128 pbA ⟨ga.rootKey, ga.macKey⟩)
          (sepConj_mono_right (stackAt_ct1SentFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_done
      · refine sepWP_close_ret
          (fun sf => ct1SentAt A.repAlloc (F := F) out
              { epoch := pb.epoch, auth := Authenticator.fromPb auth,
                hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
            memRegion pbA 128 ∗
            A.pool lim (M.stepEvents (authFromPbAllocEvents auth ++ (evs1 ++ rustDeallocEvents ga.macKey.cap.toNat 1)) st0) sf ∗
            stackAt s0.sp ct1SentFromPbStack)
          ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ct1_post hp htr_f
            ⟨evs1 ++ rustDeallocEvents ga.macKey.cap.toNat 1,
              hevs1.append (FreeOnlyEvs.singleton 1 ga.macKey.cap.toNat),
              by rw [halloc_ok]⟩, hsp_f, hcs_f⟩)
        have heq_st : M.stepEvents (authFromPbAllocEvents auth ++ (evs1 ++ rustDeallocEvents ga.macKey.cap.toNat 1)) st0 =
            M.stepEvents (rustDeallocEvents ga.macKey.cap.toNat 1) st1 := by
          simp only [stA, st1, AllocCostModel.stepEvents_append]
        rw [heq_st]; wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans
            (Entails.of_eq (show _ =
              (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8) ∗
              (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ memRegion ga.macKey.ptr ga.macKey.cap.toNat) by
                unfold auth72HeadersAt; sep_ac_rfl))
            (sepConj_mono_left (memRegion_72_auth72_8_entails_128 pbA ⟨ga.rootKey, ga.macKey⟩)))
          (sepConj_mono_right (stackAt_ct1SentFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        have hlr0' : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr0
        wp_apply; rw [stackAt_ct1SentFromPb_split_allocHook s0.sp]; wp_done

/-! ## 4. Block `339`: `<Ct1Sent>::from_pb` Closed Budget-Threaded Contract -/

set_option maxHeartbeats 1200000 in
/-- Closed `[LibsignalPlacement]` contract for `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb`
    (Block `339`) with `RustCliAllocBudget M`. -/
theorem ct1_sent_from_pb_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_339 H) (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 339)]
  change subroutine_ok ((blkPC_339).rebase (blkPl_339).base H) (blkPl_339).base _
  have hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem hdealloc
  have hauth_cl : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim)) :=
    auth_from_pb_pinned_cl_on hshim halloc hmemcpy
  have hdrop_cl : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsmpl.base 286) (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec M A lim)) :=
    drop_proto_unchunked_ct1_sent_ek_received_cl_on hdealloc
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, pbA, pb⟩, st0⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align_bv : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  have hpre' : s0.mem ⊨
      (memRegion out 128 ∗ protoUnchunkedCt1SentAt A.repAlloc pbA pb ∗
        A.pool lim st0 s0 ∗ stackAt s0.sp ct1SentFromPbStack) ∗ R ∧
      s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = pbA ∧
      FitsEnv M lim st0 (Ct1SentFromPbPreEnv F pb) ∧
      LsRetAddr624 (s0.readReg64 .lr) := by
    simp only [ct1SentFromPbSpec, ct1SentFromPbSpecOfEnv] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact ⟨hpre.2, hpre.1⟩
  rcases hpre' with ⟨hm0, hx0, hx1, hfits, hlr0⟩
  refine ⟨memRegion out 128 ∗ protoUnchunkedCt1SentAt A.repAlloc pbA pb ∗
    A.pool lim st0 s0 ∗ stackAt s0.sp ct1SentFromPbStack, R, hm0,
    SepWPp.of_sepWP_ret ?_⟩
  rw [stackAt_ct1SentFromPb_split s0.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (protoUnchunkedCt1SentAt_unpack A.repAlloc pbA pb))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro c1; apply ProofLib.SepWP.exists_left; intro p1
  apply ProofLib.SepWP.exists_left; intro c2; apply ProofLib.SepWP.exists_left; intro p2
  apply ProofLib.SepWP.exists_left; intro c3; apply ProofLib.SepWP.exists_left; intro p3
  have hfocus1 :
      memRegion out 128 ∗ (⌜pb.hdr.length < 2 ^ 63 ∧ pb.es.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
        (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        optProtoAuthenticatorAt A.repAlloc (pbA + 72#64) pb.auth ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
        vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
      A.pool lim st0 s0 ∗ (stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ cells (s0.sp - 48#64) 6) =
      ⌜pb.hdr.length < 2 ^ 63 ∧ pb.es.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
      (memRegion out 128 ∗ ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        optProtoAuthenticatorAt A.repAlloc (pbA + 72#64) pb.auth ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
        vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
      A.pool lim st0 s0 ∗ (stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ cells (s0.sp - 48#64) 6)) := by sep_ac_rfl
  rw [hfocus1]; apply SepWP.pure_elim; intro ⟨hl1, hl2, hl3, _⟩
  cells_unfold; wp_pull_exists; rename_i fp_old lr_old x22_old x21_old x20_old x19_old
  by_cases hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true
  · have hhdr_t : (BitVec.ofNat 64 pb.hdr.length == 64#64) = true := by
      rw [ofNat_beq_lit_iff hl1 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1.1
    have hes_t : (BitVec.ofNat 64 pb.es.length == 2080#64) = true := by
      rw [ofNat_beq_lit_iff hl2 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1.2
    have hct1_t : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true := by
      rw [ofNat_beq_lit_iff hl3 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.2
    cases hauth : pb.auth with
    | none =>
      have halloc_nil := ct1SentFromPbAllocEvents_of_auth_none F pb hauth
      rw [optProtoAuthenticatorAt_72_none]
      refine SepWP.weaken_pre (sepConj_mono_left (memRegion_128_err_split out)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
      refine sepWP_cut_lscl hcl (lsmpl.base 286)
        (fun sm Pm => (Pm ⊢ (protoUnchunkedCt1SentEkReceivedAt A.repAlloc pbA
              { epoch := pb.epoch, auth := none, es := pb.hdr, ek := pb.es, ct1 := pb.ct1 } ∗
            A.pool lim st0 sm ∗ stackAt s0.sp dropStack32) ∗
            (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗ memRegion (s0.sp - 4336#64) 208)) ∧
          sm.readReg64 .x0 = pbA ∧ sm.readReg64 .lr = s0.readReg64 .lr ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) ?_ ?_
      · wp_steps_sync_pool (lsmpl.base 286); simp only [State.setMem_setMem]
        have hpre_none (s_mid : State) :
            ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119 ∗
             (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
             ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
             ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
             ((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40 ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
             vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1 ∗
             A.pool lim st0 s_mid ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
            (protoUnchunkedCt1SentEkReceivedAt A.repAlloc pbA
              { epoch := pb.epoch, auth := none, es := pb.hdr, ek := pb.es, ct1 := pb.ct1 } ∗
             A.pool lim st0 s_mid ∗ stackAt s0.sp dropStack32) ∗
            (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗ memRegion (s0.sp - 4336#64) 208) := by
          refine Entails.trans (Entails.of_eq (show _ =
            (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119)) ∗
            ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
             ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
             ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
             (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40) ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
             vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
            A.pool lim st0 s_mid ∗ (stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) by sep_ac_rfl)) ?_
          refine Entails.trans (sepConj_mono_right (sepConj_mono
            (unpacked_ct1Sent_auth_none_pack A.repAlloc pbA c1 p1 c2 p2 c3 p3 pb.epoch pb.hdr pb.es pb.ct1)
            (sepConj_mono_right (stackAt_ct1SentFromPb_tail_dropStack32 s0.sp _ _ _ _ _ _)))) ?_
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by
          dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl)) (hpre_none _)) ?_
        refine align_pre_st (by sep_ac_rfl) ?_; wp_done
      · intro sm _Pm hpcm hrunm hclm ⟨hentm, hx0_m, hlr_m, hsp_m, hcs_m, htr_m⟩
        refine SepWP.weaken_pre hentm ?_
        have hsp_align_m : sm.spAligned = true := by simp only [State.spAligned, hsp_m]; exact hsp_align_bv
        refine SepWP.call_subroutine_frame hdrop_cl
          (x := (⟨pbA, { epoch := pb.epoch, auth := none, es := pb.hdr, ek := pb.es, ct1 := pb.ct1 }⟩, st0))
          (F := ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗ memRegion (s0.sp - 4336#64) 208)
          hpcm hrunm hsp_align_m hlr_m ?_
          (fun _ _ _ hm => not_satisfies_false_sepConj hm)
          (fun _ _ _ _ hm => not_satisfies_false_sepConj hm) ?_
        · intro R' hm'; dsimp only [withLsCodeLoaded, dropProtoUnchunkedCt1SentEkReceivedSpec]
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hclm, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hx0_m, hlr_m ▸ hlr0⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by rw [hsp_m]; try sep_ac_rfl)) hm'
        · intro sf hpcf hrunf hspf hcsf
          dsimp only [withLsCodeLoaded, dropProtoUnchunkedCt1SentEkReceivedSpec, protoUnchunkedCt1SentEkReceivedSize]
          rw [sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro evsDrop
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; rintro ⟨htr_sf, _, hevsDrop⟩; rw [htr_m] at htr_sf
          refine SepWP.done hpcf hrunf ⟨fun hm => ?_, hspf.trans hsp_m, calleeSavedPreserved_trans hcs_m hcsf⟩
          simp only [ct1SentFromPbSpec, ct1SentFromPbSpecOfEnv, ct1SentFromPb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb, hcond, hauth, ↓reduceIte, ct1SentResultAt]
          have hp_out :
              (memRegion pbA 128 ∗ (A.pool lim (M.stepEvents evsDrop st0) sf ∗ (stackAt sm.sp dropStack32 ∗
                (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗ memRegion (s0.sp - 4336#64) 208)))) ⊢
              ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119) ∗
                memRegion pbA 128 ∗ A.pool lim (M.stepEvents evsDrop st0) sf ∗ stackAt s0.sp ct1SentFromPbStack := by
            rw [hsp_m, stackAt_ct1SentFromPb_split_dropStack32 s0.sp]; exact Entails.of_eq (by sep_ac_rfl)
          exact close_ct1_post hp_out htr_sf ⟨evsDrop, hevsDrop, by rw [halloc_nil, List.nil_append]⟩ hm
    | some auth =>
      have hfits_auth := fitsEnv_auth_of_ct1 hcond hauth hfits
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        optProtoAuthenticatorAt A.repAlloc (pbA + 72#64) (some auth) ∗
        (memRegion out 128 ∗ (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1 ∗
         A.pool lim st0 s0 ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
         ((s0.sp - 48#64) ↦₆₄ fp_old) ∗ ((s0.sp - 40#64) ↦₆₄ lr_old) ∗ ((s0.sp - 32#64) ↦₆₄ x22_old) ∗
         ((s0.sp - 24#64) ↦₆₄ x21_old) ∗ ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old)) by sep_ac_rfl))
        (sepConj_mono_left (optProtoAuthenticatorAt_some_unpack A.repAlloc (pbA + 72#64) auth))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply ProofLib.SepWP.exists_left; intro ga
      have hfocus_ga :
          ((⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ ((pbA + 72#64) ↦₆₄ ga.rootKey.cap) ∗
            CryptoVerification.SpqrV1.Unchunked.authPBPinnedTailAt A.repAlloc ga (pbA + 72#64) auth) ∗
           (memRegion out 128 ∗ (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
            ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
            vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1 ∗
            A.pool lim st0 s0 ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
            ((s0.sp - 48#64) ↦₆₄ fp_old) ∗ ((s0.sp - 40#64) ↦₆₄ lr_old) ∗ ((s0.sp - 32#64) ↦₆₄ x22_old) ∗
            ((s0.sp - 24#64) ↦₆₄ x21_old) ∗ ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old))) =
          ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ (((pbA + 72#64) ↦₆₄ ga.rootKey.cap) ∗
            CryptoVerification.SpqrV1.Unchunked.authPBPinnedTailAt A.repAlloc ga (pbA + 72#64) auth ∗
            memRegion out 128 ∗ (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
            ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
            vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1 ∗
            A.pool lim st0 s0 ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
            ((s0.sp - 48#64) ↦₆₄ fp_old) ∗ ((s0.sp - 40#64) ↦₆₄ lr_old) ∗ ((s0.sp - 32#64) ↦₆₄ x22_old) ∗
            ((s0.sp - 24#64) ↦₆₄ x21_old) ∗ ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old)) := by sep_ac_rfl
      rw [hfocus_ga]; apply SepWP.pure_elim; intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      rw [memRegion_176_128_split_8_48_72 s0.sp]
      refine sepWP_cut_lscl hcl (lsmpl.base 330)
        (fun sm Pm => (Pm ⊢ (memRegion (s0.sp - 168#64) 48 ∗
          authenticatorPBPinnedAt A.repAlloc ga (pbA + 72#64) auth ∗
          A.pool lim st0 sm ∗ stackAt (s0.sp - 176#64) authFromPbStack) ∗
          (memRegion out 128 ∗
           ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
            ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
            ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
            vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
           memRegion (s0.sp - 176#64) 8 ∗ memRegion (s0.sp - 120#64) 72 ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
          Saved48Preserved s0 sm (s0.sp - 176#64) ∧
          sm.readReg64 .x0 = s0.sp - 168#64 ∧ sm.readReg64 .x1 = pbA + 72#64 ∧
          sm.readReg64 .lr = (blkPl_339).base + 92#64 ∧
          sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap ∧
          sm.readReg64 .x21 = pb.epoch ∧ sm.readReg64 .x22 = out) ?_ ?_
      · wp_steps_sync_pool (lsmpl.base 330)
        simp only [State.setMem_setMem]
        rw [← sepConj_assoc ((pbA + 72#64) ↦₆₄ ga.rootKey.cap),
            ← authenticatorPBPinnedAt_eq_cap_tail A.repAlloc ga (pbA + 72#64) auth]
        refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_
        wp_done
      · intro sm _Pm hpcm hrunm hclm ⟨hentm, ⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx0_m, hx1_m, hlr_m, hx19_m, hx20_m, hx21_m, hx22_m⟩
        refine SepWP.weaken_pre hentm ?_
        have hsp_align_m : sm.spAligned = true := by
          simp only [State.spAligned, hsp_m]
          exact ProofLib.spAligned_sub s0.sp 176#64 hsp_align_bv (by decide)
        refine SepWP.call_subroutine_frame hauth_cl
          (x := (⟨s0.sp - 168#64, pbA + 72#64, ga, auth⟩, st0))
          (F := memRegion out 128 ∗
           ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
            ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
            ((pbA + 120#64) ↦₆₄ pb.epoch) ∗ vecU8Payload A.repAlloc c1 p1 pb.hdr ∗
            vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
           memRegion (s0.sp - 176#64) 8 ∗ memRegion (s0.sp - 120#64) 72 ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          hpcm hrunm hsp_align_m hlr_m ?_
          (fun _ _ _ hm => not_satisfies_false_sepConj hm)
          (fun _ _ _ _ hm => not_satisfies_false_sepConj hm) ?_
        · intro R' hm'; dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hclm, ?_⟩
          rw [sepConj_assoc] at hm' ⊢
          rw [satisfies_pure_sepConj]; refine ⟨⟨hx0_m, hx1_m, hfits_auth⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by rw [hsp_m]; try sep_ac_rfl)) hm'
        · intro s1 hpc1 hrun1 hsp1 ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
          rw [hx19_m] at hx19_1; rw [hx20_m] at hx20_1; rw [hx21_m] at hx21_1; rw [hx22_m] at hx22_1
          rw [hx23_m] at hx23_1; rw [hx24_m] at hx24_1; rw [hx25_m] at hx25_1; rw [hx26_m] at hx26_1
          rw [hx27_m] at hx27_1; rw [hx28_m] at hx28_1; rw [hsp_m] at hsp1
          dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]; rw [sepExists_sepConj_left]
          apply ProofLib.SepWP.exists_left; intro evsAuth
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; rintro ⟨htrace_s1, hevsAuth⟩; rw [htrace_m] at htrace_s1
          have hevsAuth_eq : evsAuth = authFromPbAllocEvents auth := by
            simpa only [AuthFromPbEnv, authFromPbEvents_eq_allocEvents] using hevsAuth
          subst hevsAuth_eq
          exact SepWP.weaken_pre (Entails.of_eq (by rw [hsp_m]; sep_ac_rfl))
            (ct1_sent_from_pb_ok_after_auth_placed hdealloc_raw hcond hauth hpc1 hrun1
              ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp1, htrace_s1, hvregs_1.trans hvregs_m⟩
              hx19_1 hx20_1 hx21_1 hx22_1 hsp_align_bv hlr0)
  · have hcond_f : (pb.hdr.length == HEADER_SIZE &&
        pb.es.length == ENCAPSULATION_STATE_SIZE &&
        pb.ct1.length == CIPHERTEXT1_SIZE) = false := Bool.eq_false_iff.mpr hcond
    refine sepWP_cut ((blkPl_339).base + 236#64)
      (fun sm Pm => (Pm ⊢ (memRegion out 128 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A.repAlloc (pbA + 72#64) pb.auth ∗ ((pbA + 120#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.hdr ∗ vecU8Payload A.repAlloc c2 p2 pb.es ∗ vecU8Payload A.repAlloc c3 p3 pb.ct1) ∗
        A.pool lim st0 sm ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
        Saved48Preserved s0 sm (s0.sp - 176#64) ∧
        sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · by_cases h1 : (BitVec.ofNat 64 pb.hdr.length == 64#64) = true
      · by_cases h2 : (BitVec.ofNat 64 pb.es.length == 2080#64) = true
        · by_cases h3 : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true
          · exfalso; apply hcond
            rw [ofNat_beq_lit_iff hl1 (by decide)] at h1
            rw [ofNat_beq_lit_iff hl2 (by decide)] at h2
            rw [ofNat_beq_lit_iff hl3 (by decide)] at h3
            simp [h1, h2, h3, HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE]
          · have h3_f : (BitVec.ofNat 64 pb.ct1.length == 960#64) = false := Bool.eq_false_iff.mpr h3
            wp_steps_sync_pool ((blkPl_339).base + 236#64); simp only [State.setMem_setMem]
            refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_; wp_done
        · have h2_f : (BitVec.ofNat 64 pb.es.length == 2080#64) = false := Bool.eq_false_iff.mpr h2
          wp_steps_sync_pool ((blkPl_339).base + 236#64); simp only [State.setMem_setMem]
          refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_; wp_done
      · have h1_f : (BitVec.ofNat 64 pb.hdr.length == 64#64) = false := Bool.eq_false_iff.mpr h1
        wp_steps_sync_pool ((blkPl_339).base + 236#64); simp only [State.setMem_setMem]
        refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_; wp_done
    · intro s1 _Pm hpc1 hrun1 ⟨hent1, hpres1, hx0_1, hx19_1⟩
      exact SepWP.weaken_pre hent1
        (ct1_sent_from_pb_err_drop_unpacked_placed hdealloc_raw hcond_f
          hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv hlr0)

theorem ct1_sent_from_pb_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 339 H) (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec M A lim F)) :=
  ls_to_blockProgram (ct1_sent_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy)

theorem ct1_sent_from_pb_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H]
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec M A lim F)) :=
  ls_subroutine_ok_of_block (ct1_sent_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy) hidx

theorem ct1_sent_from_pb_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H] {m : Memory}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 339)
      (withMemEq m (ct1SentFromPbSpec M A lim F)) :=
  lscall_blk_cl (ct1_sent_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy) hcl hidx

theorem ct1_sent_from_pb_on_333_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H spqrMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_333 H) (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec M A lim F)) :=
  ct1_sent_from_pb_cl_on hshim halloc hdealloc hmemcpy

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlacedBudgetAux
