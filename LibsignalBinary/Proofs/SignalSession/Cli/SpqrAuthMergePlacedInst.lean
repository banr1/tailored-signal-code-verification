/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrVarintPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Code-Loaded Placed `Authenticator::merge` (Block `295`) CLI Instantiations

Instantiates `auth_merge_cl_placed_ok_of_contracts` for Block `295`
(`prost::encoding::message::merge::<spqr::proto::pq_ratchet::Authenticator, &mut &[u8]> [local#2]`)
with the code-loaded CLI contracts for its five cross-block callees (Blocks `257, 261, 263, 290, 291`)
under `[LibsignalPlacement]` and `[CliSpqrExt W H]`, providing own-block, `blockProgram`, and
caller-block-polymorphic (`[IsLsBlockProg callerProg i H]`) corollaries.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl libsignalSessionLib
   IsLsBlockProg withLsCodeLoaded subroutine_ok_withLsCodeLoaded_of_plain
   ls_blockPlacement_base ls_subroutine_ok_of_block
   lsRustNoAllocShimSym lsRustAllocSym lsRustReallocSym lsRustDeallocSym
   lsMemcpySym lsHandleErrorSym
   blkPC_261 blkPl_261 instIsLsBlockProg_261
   blkPC_263 blkPl_263 instIsLsBlockProg_263
   blkPC_290 blkPl_290 instIsLsBlockProg_290
   blkPC_291 blkPl_291 instIsLsBlockProg_291
   blkPC_295 blkPl_295 instIsLsBlockProg_295)
open CryptoVerification.RecordCodecs.Placed (blkPC_257 blkPl_257 instIsLsBlockProg_257)
open CryptoVerification.RecordCodecsBinary.Assembly (decode_error_push_spec_placed_ok)
open CryptoVerification.RustHeap (RustAlloc rustAllocSpec rustReallocSpec rustDeallocSpec)
open CryptoVerification.LibsignalTripleRatchet
  (withLsCodeRoLoaded decodeErrorFromSpec decodeErrorPushSpec
   sessionShimSpec framelessMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (lsHandleAllocErrorSym decode_error_from_placed_ok)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Spec skipField3Spec)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3RawSpec)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (CliSpqrExt instCliSpqrExtWithPanics)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.SpqrV1.Auth (authMergeSpec)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.SpqrV1.Top.Recv (ls_subroutine_ok_cro_of_cro)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlaced (decodeVarint2_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3ClPlaced (skipField3_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlaced (bytes_merge_3_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlaced
  (auth_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrVarintPlacedInst
  (subroutine_ok_callInv_of_cro
   cliDecodeErrorFrom_at_block_cl cliDecodeErrorPush_at_block_cl
   cliDecodeVarint2_at_block_cl cliSkipField3_at_block_cl
   cliBytesMerge3_at_block_cro)

/-! ## Allocator-polymorphic hook-only contract -/

/-- Verifies Block `295` (`Authenticator::merge`) under `[LibsignalPlacement]`, discharging
cross-block callees (Blocks `257, 261, 263, 290, 291`) for arbitrary `A : RustAlloc`. -/
theorem auth_merge_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : H lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A)) := by
  have hFrom261 : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)) := by
    rw [← ls_blockPlacement_base (i := 261)]
    exact subroutine_ok_withLsCodeLoaded_of_plain
      (decode_error_from_placed_ok hshim halloc hpanic_alloc)
  have hPush257 : subroutine_ok ((blkPC_257).rebase (blkPl_257).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)) := by
    rw [← ls_blockPlacement_base (i := 257)]
    exact decode_error_push_spec_placed_ok hpanic_raw hshim halloc hrealloc
  have hVarint291 : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A)) := by
    rw [← ls_blockPlacement_base (i := 291)]
    exact decodeVarint2_cl_placed_ok hshim halloc hpanic_alloc
  have hSkip263 : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A)) := by
    rw [← ls_blockPlacement_base (i := 263)]
    exact skipField3_cl_placed_ok hshim halloc hpanic_alloc
  have hBytes290 : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)) := by
    rw [← ls_blockPlacement_base (i := 290)]
    exact bytes_merge_3_cl_placed_ok hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw
  exact auth_merge_cl_placed_ok_of_contracts
    (ls_subroutine_ok_of_block (i := 295) (j := 261) hFrom261)
    (ls_subroutine_ok_of_block (i := 295) (j := 257) hPush257)
    (ls_subroutine_ok_of_block (i := 295) (j := 291) hVarint291)
    (ls_subroutine_ok_of_block (i := 295) (j := 263) hSkip263)
    (ls_subroutine_ok_cro_of_cro (i := 295) (j := 290) hBytes290)

/-! ## Own-block rebased contracts under `[CliSpqrExt W H]` -/

theorem cliAuthMerge_cro [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_295).rebase (blkPl_295).base H)
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A0)) := by
  rw [← ls_blockPlacement_base (i := 295)]
  exact auth_merge_cl_placed_ok_of_contracts
    (cliDecodeErrorFrom_at_block_cl W)
    (cliDecodeErrorPush_at_block_cl W)
    (cliDecodeVarint2_at_block_cl W)
    (cliSkipField3_at_block_cl W)
    (cliBytesMerge3_at_block_cro W)

theorem cliAuthMerge_callInv [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_295).rebase (blkPl_295).base H)
      (lsmpl.base 295)
      (withLsCallInv lsmpl (authMergeSpec A0)) :=
  subroutine_ok_callInv_of_cro (cliAuthMerge_cro W)

/-! ## Own-block `blockProgram` contracts under `[CliSpqrExt W ext]` -/

theorem cliAuthMerge_blockProgram_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_295).rebase (blkPl_295).base (Rust.withPanics ext))]
  exact cliAuthMerge_cro W

theorem cliAuthMerge_blockProgram_callInv [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCallInv lsmpl (authMergeSpec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_295).rebase (blkPl_295).base (Rust.withPanics ext))]
  exact cliAuthMerge_callInv W

/-! ## Caller-block-polymorphic contracts -/

/-- Transfers Block `295` (`Authenticator::merge`) with `withLsCodeRoLoaded` to any caller block `i`. -/
theorem cliAuthMerge_at_block_cro [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A0)) :=
  ls_subroutine_ok_cro_of_cro (i := i) (j := 295) (cliAuthMerge_cro W) hi

/-- Transfers Block `295` (`Authenticator::merge`) with `withLsCallInv` to any caller block `i`. -/
theorem cliAuthMerge_at_block_callInv [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 295)
      (withLsCallInv lsmpl (authMergeSpec A0)) :=
  subroutine_ok_callInv_of_cro (cliAuthMerge_at_block_cro W hi)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInst
