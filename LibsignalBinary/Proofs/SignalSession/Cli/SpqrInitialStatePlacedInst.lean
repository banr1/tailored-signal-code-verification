/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlaced
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs

/-!
# Closed Relocatable `spqr::initial_state` & Drop Instantiations

Proves closed placed contracts for `spqr::initial_state` (Block 327), `spqr::init_inner`
(Block 324), `PolyDecoder::into_pb` (Block 377), `States::into_pb` on `initV1State` (Block 334),
and protobuf/state drop blocks (Blocks 266, 267, 269, 270, 273, 279, 281, 282) under
`[CliSpqrExt W ext]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInst

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.InitialState
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (CliSpqrExt cliSpqrExt_self cliSpqrExt_dealloc_sat cliSpqrExt_sessionMemcpyRegion_sat
   cliSpqrSendAllocContractsPlacedExt
   cliNoAllocShim_at_block cliAlloc_at_block cliFramelessMemcpy_at_block
   cliSessionMemcpy_at_block cliAuthNew_placed_ok cliEncodeToVec_placed_ok)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (CliGhostA0Hooks lsLibcruxHmacSymCli cliGhostExterns_panic_handle_error)
open CryptoVerification.E2E.HooksE (A0)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst (cliDrop_264_cl)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
  (ls_to_blockProgram drop_proto_chunked_header_sent_cl_placed_ok
   drop_proto_chunked_ct1_received_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlaced
  (drop_opt_proto_inner_state_cl_placed_ok drop_opt_proto_inner_state_cl_blockProgram
   drop_proto_pq_ratchet_state_cl_placed_ok drop_proto_pq_ratchet_state_cl_blockProgram)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlaced
  (drop_opt_proto_spqr_chain_cl_blockProgram drop_spqr_chain_cl_blockProgram
   drop_chunked_states_local2_cl_blockProgram drop_unchunked_ct1_sent_local2_cl_blockProgram)

/-!
## 1. Group B CLI `withLsCodeLoaded` Drop Instantiations (`266, 267, 269, 270, 273, 279, 281, 282`)
-/

private theorem cliDealloc_withPanics_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat (Rust.withPanics ext) CryptoVerification.SpqrV1.States.Recv.spqrRustDeallocSym
      (rustDeallocSpec A0) :=
  cliSpqrExt_dealloc_sat W (ext := Rust.withPanics ext)

theorem cliDrop_266_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 266 (Rust.withPanics ext)) (lsmpl.base 266)
      (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec A0)) :=
  drop_opt_proto_spqr_chain_cl_blockProgram (cliDealloc_withPanics_sat W)

theorem cliDrop_267_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext)) (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec A0)) :=
  drop_opt_proto_inner_state_cl_blockProgram (cliDealloc_withPanics_sat W)

theorem cliDrop_269_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 269 (Rust.withPanics ext)) (lsmpl.base 269)
      (withLsCodeLoaded lsmpl (dropSpqrChainSpec A0)) :=
  drop_spqr_chain_cl_blockProgram (cliDealloc_withPanics_sat W)

theorem cliDrop_270_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext)) (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A0)) :=
  drop_proto_pq_ratchet_state_cl_blockProgram (cliDealloc_withPanics_sat W)

theorem cliDrop_270_cl_rebase [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext)) (blkPl_270).base
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A0)) := by
  have h := drop_proto_pq_ratchet_state_cl_placed_ok (ext := ext) (cliDealloc_withPanics_sat W)
  rwa [← ls_blockPlacement_base (i := 270)] at h

theorem cliDrop_273_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 273 (Rust.withPanics ext)) (lsmpl.base 273)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec A0 W.C.F)) :=
  drop_chunked_states_local2_cl_blockProgram (cliDealloc_withPanics_sat W)

theorem cliDrop_279_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 279 (Rust.withPanics ext)) (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec A0 W.C.F)) :=
  drop_unchunked_ct1_sent_local2_cl_blockProgram (cliDealloc_withPanics_sat W)

theorem cliDrop_281_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 281 (Rust.withPanics ext)) (lsmpl.base 281)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec A0)) :=
  ls_to_blockProgram (drop_proto_chunked_header_sent_cl_placed_ok (cliDealloc_withPanics_sat W))

theorem cliDrop_282_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 282 (Rust.withPanics ext)) (lsmpl.base 282)
      (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec A0)) :=
  ls_to_blockProgram (drop_proto_chunked_ct1_received_cl_placed_ok (cliDealloc_withPanics_sat W))

/-!
## 2. Block `377` (`PolyDecoder::into_pb`) & Block `334` (`States::into_pb` on `initV1State`)
-/

private theorem drop_withLsCl_post [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCl lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

theorem cliDecoderIntoPb_cl_placed_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      ((CryptoVerification.blkPC_377).rebase
        (CryptoVerification.blkPl_377).base (Rust.withPanics ext))
      (lsmpl.base 377)
      (withLsCodeLoaded lsmpl (CryptoVerification.SpqrV1.Poly.DecoderPb.decoderIntoPbSpec A0)) := by
  have hA := cliSpqrSendAllocContractsPlacedExt W (ext := ext)
  have hdrop264 :
      subroutine_ok
        ((CryptoVerification.blkPC_377).rebase
          (CryptoVerification.blkPl_377).base (Rust.withPanics ext))
        (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A0)) :=
    drop_withLsCl_post
      (ls_subroutine_ok_cl_of_block (i := 377) (j := 264)
        (CryptoVerification.SpqrV1.States.Recv.drop_glue_sorted_set_pt16_cl_placed_ok
          (cliDealloc_withPanics_sat W (ext := ext))))
  rw [← ls_blockPlacement_base (i := 377)]
  exact CryptoVerification.SpqrV1.Poly.DecoderPb.decoder_into_pb_cl_placed_ok_ext
    hA.handle_error hA.shim hA.alloc hdrop264

theorem cliStatesIntoPb_initV1State_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (d : Direction) (authKey : Bytes) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl
        (SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec A0 W.C.F (initV1State W.C.F d authKey))) := by
  cases d with
  | a2b =>
    dsimp only [initV1State]
    have harm0 :
        subroutine_ok
          ((SpqrV1.States.IntoPb.Placed.blkPC_334).rebase
            (SpqrV1.States.IntoPb.Placed.blkPl_334).base (Rust.withPanics ext))
          (lsmpl.base 334)
          (withLsCodeLoaded lsmpl
            (SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec A0 W.C.F
              (.keysUnsampled { uc := { epoch := 1#64, auth := Authenticator.new W.C.F authKey 1#64 } }))) := by
      rw [← ls_blockPlacement_base (i := 334)]
      exact subroutine_ok_withLsCodeLoaded_of_plain
        (SpqrV1.States.IntoPb.states_into_pb_keysUnsampled_placed _)
    exact drop_withLsCl_post (ls_subroutine_ok_cl_of_block (i := 324) (j := 334) harm0)
  | b2a =>
    dsimp only [initV1State]
    have hdec_334 :
        subroutine_ok
          ((SpqrV1.States.IntoPb.Placed.blkPC_334).rebase
            (SpqrV1.States.IntoPb.Placed.blkPl_334).base (Rust.withPanics ext))
          (lsmpl.base 377)
          (withLsCodeLoaded lsmpl (SpqrV1.Poly.DecoderPb.decoderIntoPbSpec A0)) :=
      drop_withLsCl_post
        (ls_subroutine_ok_cl_of_block (i := 334) (j := 377) (cliDecoderIntoPb_cl_placed_ok W (ext := ext)))
    have hmc_334 :
        subroutine_ok
          ((SpqrV1.States.IntoPb.Placed.blkPC_334).rebase
            (SpqrV1.States.IntoPb.Placed.blkPl_334).base (Rust.withPanics ext))
          (lsρ "memcpy") sessionMemcpyRegionSpec :=
      spqr_hook_ok_of_mem
        (cliSpqrExt_sessionMemcpyRegion_sat W (ext := Rust.withPanics ext))
        (by decide) (i := 334) (by decide) (by decide)
    have harm5 :
        subroutine_ok
          ((SpqrV1.States.IntoPb.Placed.blkPC_334).rebase
            (SpqrV1.States.IntoPb.Placed.blkPl_334).base (Rust.withPanics ext))
          (lsmpl.base 334)
          (withLsCodeLoaded lsmpl
            (SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec A0 W.C.F
              (.noHeaderReceived
                { uc := { epoch := 1#64, auth := Authenticator.new W.C.F authKey 1#64 }
                  receiving_hdr := initHdrDecoder }))) := by
      rw [← ls_blockPlacement_base (i := 334)]
      exact SpqrV1.States.IntoPb.states_into_pb_noHeaderReceived_cl_placed
        hdec_334 hmc_334 _
    exact drop_withLsCl_post (ls_subroutine_ok_cl_of_block (i := 324) (j := 334) harm5)

/-! ## 3. Block `324` (`spqr::init_inner`) Closed `withLsCallInv` Contract -/

private theorem call_statesIntoPb_variant_cl_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} {st : States spqrPolyApi (spqrAuthApi F)}
    (hinto_raw : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 334) (withLsCodeLoaded lsmpl (SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec A F st)))
    (out : BitVec 64) {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 334)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1040#64)
    (hsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out) (hx0 : s.readReg64 .x0 = s0.sp - 1032#64)
    (hsplit : P = (memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A (s0.sp - 1032#64) st ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 1040#64) SpqrV1.States.IntoPb.statesIntoPbStack) ∗ Frame)
    (hnext : ∀ (sf : State),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s0.sp - 1040#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) sf
        ((optProtoInnerStateAt A out st.into_pb.innerState ∗
          memRegion (s0.sp - 1032#64) chunkedStatesSize ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt (s0.sp - 1040#64) SpqrV1.States.IntoPb.statesIntoPbStack) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext)) (s0.readReg64 .x30) s P Q (InitInnerPanic s0 R) := by
  refine SepWPp.call hinto_raw (x := (out, s0.sp - 1032#64)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => ProofLib.allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec]; rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hx8, hx0⟩, hm⟩
  · change (sf.mem ⊨ ((withLsCodeLoaded lsmpl (SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec A F st)).onPanic (out, s0.sp - 1032#64) s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [withLsCodeLoaded, SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec, SpqrV1.States.IntoPb.statesIntoPbOnPanic] at hmem
    rw [← sepConj_assoc]
    have hpan := ProofLib.allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [withLsCodeLoaded, SpqrV1.States.IntoPb.statesIntoPbVariantPlacedSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

theorem cliInitInner_callInv_placed_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX A0 W.C.F)) := by
  have hA := cliSpqrSendAllocContractsPlacedExt W (ext := ext)
  have hauth_340 : subroutine_ok
      ((CryptoVerification.blkPC_340).rebase (CryptoVerification.blkPl_340).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewSpec W.C.F A0)) := by
    rw [← ls_blockPlacement_base (i := 340)]
    exact cliAuthNew_placed_ok W (H := Rust.withPanics ext)
  have hauth : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 340) (withLsCallInv lsmpl (authNewSpec W.C.F A0)) :=
    ls_subroutine_ok_callInv_of_block (i := 324) (j := 340) hauth_340
  have hspec_base :
      subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
        (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpec A0 W.C.F)) := by
    apply subroutine_ok_of_sepWPp
    intro x R s0 hpc hrun hpre hsp0_align
    have hfsp_align : ((s0.sp - 1040#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 1040#64 hsp0_align (by decide)
    dsimp only [withLsCallInv, initInnerPlacedSpec] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hinv0, hpre⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hpure, hm⟩
    have hcode0 : LibsignalCodeLoaded lsmpl s0.mem := hinv0.2
    have hlt32 : 32 + x.authKey.length < 2 ^ 63 := hpure.2.2.2.2.2.2
    have hcall_auth : AuthCallAtPlaced A0 W.C.F ext s0 x.authKey (InitInnerPlacedPost A0 W.C.F s0 x) R :=
      fun s ret_pc P Frame hinv_s hpcs hruns hsps hlrs htrs hx0s hx1s hsplits hnext =>
        call_authNew_placed_x hauth x.authKey hlt32 s0 s ret_pc P Frame R
          (hinv_s hinv0) hpcs hruns hsps hfsp_align hlrs htrs hx0s hx1s hsplits hnext
    have hcall_into_a2b : IntoPbCallAtPlaced A0 W.C.F ext s0 x.out .a2b x.authKey
        (InitInnerPlacedPost A0 W.C.F s0 ⟨x.out, .v1, .a2b, x.akPtr, x.authKey⟩) R :=
      fun s ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hsplits hnext =>
        call_statesIntoPb_variant_cl_placed (cliStatesIntoPb_initV1State_cl W .a2b x.authKey)
          x.out (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hsplits hnext
    have hcall_into_b2a : IntoPbCallAtPlaced A0 W.C.F ext s0 x.out .b2a x.authKey
        (InitInnerPlacedPost A0 W.C.F s0 ⟨x.out, .v1, .b2a, x.akPtr, x.authKey⟩) R :=
      fun s ret_pc P Frame hcs hpcs hruns hsps hlrs htrs hx8s hx0s hsplits hnext =>
        call_statesIntoPb_variant_cl_placed (cliStatesIntoPb_initV1State_cl W .b2a x.authKey)
          x.out (hcs hcode0) hpcs hruns hsps hfsp_align hlrs htrs hx8s hx0s hsplits hnext
    refine ⟨_, R, hm, sepWPp_of_init_inner_placed_wpp s0 s0 x _ R
      (init_inner_body_placed hA.handle_error
        (cliNoAllocShim_at_block W (i := 324))
        (cliAlloc_at_block W (i := 324))
        (cliFramelessMemcpy_at_block W (i := 324))
        s0 x R hcall_auth hcall_into_a2b hcall_into_b2a hpc hrun hsp0_align hpure)⟩
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  dsimp only [withLsCallInv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, hpre⟩
  have hle : initInnerStack ≤ initInnerStackX := by decide
  have hsplit : stackAt s0.sp initInnerStackX =
      memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
        (initInnerStackX - initInnerStack) ∗
        stackAt s0.sp initInnerStack := by
    have h1 := stackAt_split_bottom s0.sp initInnerStack
      (initInnerStackX - initInnerStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX)
      (initInnerStackX - initInnerStack) ∗ R
  have hpre' : s0.mem ⊨ (withLsCallInv lsmpl (initInnerPlacedSpec A0 W.C.F)).pre x s0 ∗ R' := by
    dsimp only [withLsCallInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ?_⟩
    dsimp only [initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine subroutine_ok.mono_outcome hspec_base x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpec, initInnerOnPanic, R'] at hpost ⊢
    have h1 : ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 initInnerStackX) (initInnerStackX - initInnerStack) ∗ R)) ⊢
        (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      rw [sepConj_assoc (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝) anyHeap _,
          ← sepConj_assoc anyHeap _ R,
          sepConj_assoc (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝) anyHeap R]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))
    exact Satisfies.mono h1 hpost
  · dsimp only [withLsCallInv, initInnerPlacedSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-!
## 4. Block `327` (`spqr::initial_state`) Closed Seam (`cliSpqrInitialState_placed_ok_closed`)
-/

private theorem call_initInner_callInv_placed_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX A F)))
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hak_ne : x.akPtr ≠ 0#64) (hlt : 32 + x.p.authKey.length < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 324)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 344#64)
    (hx0 : s.readReg64 .x0 = (s0.sp - 456#64) + 0x80#64)
    (hw1 : s.readReg32 .x1 = Version.v1.toI32) (hw2 : s.readReg32 .x2 = x.p.direction.toI32)
    (hx3 : s.readReg64 .x3 = x.akPtr) (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 x.p.authKey.length)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ sf : State,
      sf.pc = initialStatePlacedEntry + 344#64 →
      sf.status = .Running → LsCallInv lsmpl sf.mem → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
          (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
        Q (InitInnerPanic s0 R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
        A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
      Q (InitInnerPanic s0 R) := by
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hinit' : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 324) (withLsCallInv lsmpl (initInnerPlacedSpecX A F)) := by
    rwa [← ls_blockPlacement_base (i := 324)]
  have hcall : subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 324)
      (withLsCallInv lsmpl (initInnerPlacedSpecX A F)) :=
    ls_subroutine_ok_callInv_of_block (callerProg := initialStatePlacedProg ext) (i := 327) (j := 324) hinit'
  let gx : InitInnerGhost := ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩
  refine sepWPp_call_lsCallInv hcall (x := gx) (F := Frame) hinv
    hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
    (fun _ _ _ _ h => ProofLib.allowPanic_not_exited h) (fun sf _ => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerStackX, gx]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hinv, ⟨hx0, hw1, hw2, hx3, hx4, hak_ne, hlt⟩, hm⟩
  · change (sf.mem ⊨ ((withLsCallInv lsmpl (initInnerPlacedSpecX A F)).onPanic gx s sf ∗ Frame) ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)
    intro hmem
    dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerOnPanic] at hmem
    rw [← sepConj_assoc]
    have hpan := ProofLib.allowPanic_frame (φ := allocFailedIn s sf ∧ s.trace <+: sf.trace)
      (ψ := allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
      (fun ⟨haf, htr_sub⟩ => by
        unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩) hmem
    simpa only [sepConj_assoc] using hpan
  · dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerStackX, gx]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hnext' := hnext sf hpc_sf hrun_sf hinv_sf (by rw [hsp_sf, hsp]) hcs_sf (by rw [htr, htrace])
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hnext'

private theorem initial_state_v1_body_callInv_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ CryptoVerification.lsMemcpySym) framelessMemcpySpec)
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX A F)))
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A)))
    (s0 : State) (x : InitialStateGhost) (R : SepProp) (hinv0 : LsCallInv lsmpl s0.mem)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hv : x.p.version = .v1) (hx0 : s0.readReg64 .x0 = x.pA) (hx8 : s0.readReg64 .x8 = x.ret)
    (hak_ne : x.akPtr ≠ 0#64) (hlen : x.p.authKey.length < 2 ^ 32)
    (hlen_pb : (PqRatchetState.encodeRaw (initialStatePB F x.p)).length < 2 ^ 63)
    (hproto_eq : protoPqRatchetStateAt A (s0.sp - 456#64) (initialStatePB F x.p) =
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (hpbAt : ∀ ptr : BitVec 64,
      (vecU8At A (s0.sp - 456#64) (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
        (((s0.sp - 456#64) + 0x18#64) ↦₃₂ 1#32) ∗
        (((s0.sp - 456#64) + 0x1c#64) ↦₃₂ x.p.chainParams.intoPb.maxJump) ∗
        (((s0.sp - 456#64) + 0x20#64) ↦₃₂ x.p.chainParams.intoPb.maxOooKeys) ∗
        (((s0.sp - 456#64) + 0x24#64) ↦₃₂ x.p.direction.toI32) ∗
        (((s0.sp - 456#64) + 0x28#64) ↦₃₂ x.p.minVersion.toI32) ∗
        memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
        (((s0.sp - 456#64) + 0x30#64) ↦₆₄ noneCap) ∗
        memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
        initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey) ⊢
      pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack)
      (InitialStateV1PlacedPost A F s0 x)
      (InitInnerPanic s0 R) := by
  have hlt63 : x.p.authKey.length < 2 ^ 63 := by omega
  have hlt32_63 : 32 + x.p.authKey.length < 2 ^ 63 := by omega
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [h61s_stackAt_initialState_split s0.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_prologue_v1_placed s0 x _ hsp0_align hpc hrun hx0 hx8 hv hlen) ?_
  intro s1 hpc1 hrun1 _ hinv1 ⟨hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hx22_1, hw25_1, htr1, hvregs1⟩
  refine SepWPp.weaken_pre (P' :=
      (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool ∗ stackAt (s0.sp - 496#64) allocHookStack ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13584 ∗ paramsAt x.pA x.akPtr x.p ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_allocHook (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initial_state_to_vec_placed h_panic hshim halloc hmemcpy s0 s1 x _ R hsp0_align hlt63
    hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx22_1 hw25_1 htr1 hvregs1 ?_
  intro s2 ptr hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2
  refine SepWPp.weaken_pre (P' :=
      paramsAt x.pA x.akPtr x.p ∗
      (memRegion (s0.sp - 456#64) 352 ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_allocHook (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_init_inner_placed s0 s2 x ptr _ hsp0_align
      hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2) ?_
  intro s3 hpc3 hrun3 _ hinv3
    ⟨hsp3, hlr3, hx0_3, hw1_3, hw2_3, hx3_3, hx4_3, hx29_3, hx19_3, hw20_3, hx21_3, hx23_3,
     hw24_3, hw25_3, hw26_3, hw27_3, htr3, hvregs3⟩
  refine SepWPp.weaken_pre (P' :=
      (memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
       A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗
      (cells (s0.sp - 456#64) 3 ∗
       (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
       (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
       (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
       (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
       (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [memRegion_pqState_split (s0.sp - 456#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  have hinv_s3 : LsCallInv lsmpl s3.mem := hinv3 (hinv2 (hinv1 hinv0))
  refine call_initInner_callInv_placed_x hinit s0 s3 x _ R hinv_s3 hsp0_align hak_ne hlt32_63
    hpc3 hrun3 hsp3 hlr3 hx0_3 hw1_3 hw2_3 hx3_3 hx4_3 htr3 ?_
  intro s4 hpc4 hrun4 hinv4 hsp4 hcs4 htr4
  obtain ⟨hx19_4, hx20_4, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, hx29_4⟩ := hcs4
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 456#64) 3 ∗
      (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
      (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
      (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
      (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
      (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
      memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
      (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
      memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
      initInnerResultAt A (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
      RustHeap.vecU8Buf A (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
      (memRegion x.ret 32 ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
       optProtoInnerStateJumpTablePlacedAt))
    (Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_encode_to_vec_placed s0 s4 x ptr _ (hpbAt ptr) hsp0_align
      hpc4 hrun4 hsp4
      (hx29_4.1.trans hx29_3) (hx19_4.trans hx19_3)
      ((readReg32_of_eq hx20_4).trans hw20_3)
      (hx21_4.trans hx21_3) (hx23_4.trans hx23_3)
      ((readReg32_of_eq hx24_4).trans hw24_3)
      ((readReg32_of_eq hx25_4).trans hw25_3)
      ((readReg32_of_eq hx26_4).trans hw26_3)
      ((readReg32_of_eq hx27_4).trans hw27_3) htr4 (hx29_4.2.trans hvregs3)) ?_
  intro s5 hpc5 hrun5 _ hinv5 ⟨hsp5, hlr5, hx0_5, hx1_5, hx29_5, hx19_5, htr5, hvregs5⟩
  refine SepWPp.weaken_pre (P' :=
      ∃∗ r0 : BitVec 64,
        (memRegion (x.ret + 8#64) 24 ∗
         pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
         A.pool ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗
        ((x.ret ↦₆₄ r0) ∗
         memRegion ((s0.sp - 496#64) - 17680#64) (initInnerStack - encodeToVecStackX) ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
         memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
         optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [memRegion_ret_32_split x.ret, stackAt_initInner_split_encodeToVec (s0.sp - 496#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Arm64.Entails.sepExists_elim; intro r0
      exact Entails.sepExists_right r0 (Entails.of_eq (by ac_rfl))) ?_
  refine SepWPp.exists_elim fun r0 => ?_
  have hinv_s5 : LsCallInv lsmpl s5.mem := hinv5 hinv4
  refine call_encodeToVec_placed_x henc s0 s5 x _ R hinv_s5 hsp0_align hlen_pb
    hpc5 hrun5 hsp5 hlr5 hx0_5 hx1_5 htr5 ?_
  intro s6 hpc6 hrun6 hinv6 hsp6 hcs6 htr6
  obtain ⟨hx19_6, _, _, _, _, _, _, _, _, _, hx29_6⟩ := hcs6
  refine SepWPp.weaken_pre (P' :=
      (x.ret ↦₆₄ r0) ∗ vecU8 A (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
      (pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_encodeToVec (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_drop_placed s0 s6 x r0 _ hv hsp0_align
      hpc6 hrun6 hsp6 (hx29_6.1.trans hx29_5) (hx19_6.trans hx19_5) htr6 (hx29_6.2.trans hvregs5)) ?_
  intro s7 hpc7 hrun7 _ hinv7 ⟨hsp7, hlr7, hx0_7, hx29_7, htr7, hvregs7⟩
  refine SepWPp.weaken_pre (P' :=
      (pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool ∗ stackAt (s0.sp - 496#64) dropStack96) ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13488 ∗
       initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  have hinv_s7 : LsCallInv lsmpl s7.mem := hinv7 hinv6
  refine call_dropPqRatchetState_placed hdrop s0 s7 x _ R hinv_s7 hproto_eq hsp0_align
    hpc7 hrun7 hsp7 hlr7 hx0_7 htr7 ?_
  intro s8 hpc8 hrun8 hsp8 hcs8 htr8
  refine SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
      memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
      h61s_initialStateSavedCells s0 ∗
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       initialStateResultAt A x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool))
    (by rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64)]; exact Entails.of_eq (by ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_epilogue_placed s0 s8 _ hsp0_align hpc8 hrun8 hsp8 htr8
      (hcs8.2.2.2.2.2.2.2.2.2.2.2.trans hvregs7)) ?_
  intro sf hpcf hrunf _ _ ⟨hspf, hcsf, htrf⟩
  exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), hspf, hcsf, htrf⟩

private theorem initialState_v1_callInv_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ CryptoVerification.lsMemcpySym) framelessMemcpySpec)
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX A F)))
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A))) :
    subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX A F .v1) := by
  refine subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp => ?_
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp
  dsimp only [initialStateVPlacedSpecX, initialStatePlacedSpecX,
    LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, initialStatePlacedSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hv, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hcl0, hro0⟩, hpre⟩ := hpre
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨hro0, hcl0⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hak_ne, hlen⟩, hmem⟩ := hpre
  have hmem1 := lsro_optProtoInnerStateJumpTablePlacedAt hro0 hmem
  have hmem2 := lsro_statesIntoPbJumpTablePlacedAt hro0 hmem1
  have hmem3 : s0.mem ⊨
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp initialStateStack) ∗ R :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
  have hwpp := initial_state_v1_body_callInv_placed h_panic hshim halloc hmemcpy
    hinit henc hdrop s0 x R hinv0 hpc hrun hsp_align hv hx0 hx8 hak_ne hlen
    (initialStatePB_encodeRaw_length_lt F x.p hlen)
    (SpqrV1.Top.Recv.protoPqRatchetStateAt_eq_pqRatchetStatePBAt A (s0.sp - 456#64) (initialStatePB F x.p))
    (fun ptr => initialState_pbAt_of_cells A F x.p hv (s0.sp - 456#64)
      (BitVec.ofNat 64 x.p.authKey.length) ptr)
  exact ⟨_, R, hmem3, sepWPp_of_initialState_v1_placed_wpp s0 x _ R hwpp⟩

private theorem cliGhostExterns_isPanic' (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

/-- Closed relocatable `spqr::initial_state` (`Block 327`) seam on
    `cliGhostExterns gh (cliExternsPlaced mmpl W)` matching `SpqrV1PlacedSeams.spqrInitialState`. -/
theorem cliSpqrInitialState_placed_ok_closed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 327 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec E2E.HooksE.A0 W.C.F)) := by
  let _ := CryptoVerification.SpqrV1.Top.Placed.instIsLsBlockProg_327
    (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)))
  have : CliSpqrExt W (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  have hv1 := initialState_v1_callInv_placed_ok (A := A0) (F := W.C.F)
    (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))
    ((congrFun (withPanics_cliGhostExterns mmpl gh W) spqrHandleErrorSym).trans
      (cliGhostExterns_panic_handle_error mmpl gh W))
    (cliNoAllocShim_at_block W (i := 327))
    (cliAlloc_at_block W (i := 327))
    (cliFramelessMemcpy_at_block W (i := 327))
    (cliInitInner_callInv_placed_ok W (ext := cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (cliEncodeToVec_placed_ok W (ext := cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (cliDrop_270_cl_rebase W (ext := cliGhostExterns gh (cliExternsPlaced mmpl W)))
  have hok : InitialStatePlacedOkX A0 W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    initialState_placed_ok_of_versions initialState_v0_placed_ok hv1
  dsimp only [InitialStatePlacedOkX] at hok
  rw [IsLsBlockProg.eq_blockProgram
    (prog := initialStatePlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))),
    initialStatePlacedEntry, ls_blockPlacement_base (i := 327)] at hok
  rwa [withPanics_eq_of_isPanicSymbol (cliGhostExterns_isPanic' mmpl gh W)] at hok

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInst
