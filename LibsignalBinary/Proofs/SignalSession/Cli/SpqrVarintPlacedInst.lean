/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlaced
public import LibsignalBinary.Proofs.RecordCodecs.Assembly
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Code-Loaded Placed Varint, BytesMerge & DecodeError Instantiations

Code-loaded (`withLsCodeLoaded` / `withLsCodeRoLoaded` / `withLsCallInv`) placed contracts under
`[CliSpqrExt W H]` for `DecodeError::from` (Block 261), `DecodeError::push` (Block 257),
`decode_varint [local#2]` (Block 291), `skip_field [local#3]` (Block 263), and
`bytes::merge [local#3]` (Block 290), in own-block and caller-polymorphic forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrVarintPlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl libsignalSessionLib libsignalMutatedBlocks
   IsLsBlockProg withLsCodeLoaded withLsCl
   subroutine_ok_withLsCodeLoaded_of_plain ls_blockPlacement_base
   ls_subroutine_ok_of_block ls_subroutine_ok_cl_of_block
   blkPC_261 blkPl_261 instIsLsBlockProg_261
   blkPC_263 blkPl_263 instIsLsBlockProg_263
   blkPC_290 blkPl_290 instIsLsBlockProg_290
   blkPC_291 blkPl_291 instIsLsBlockProg_291)
open CryptoVerification.RecordCodecs.Placed
  (blkPC_257 blkPl_257 lsProg_257 instIsLsBlockProg_257)
open CryptoVerification.RecordCodecsBinary.Assembly
  (decode_error_push_spec_placed_ok)
open CryptoVerification.LibsignalTripleRatchet
  (withLsCodeRoLoaded decodeErrorFromSpec decodeErrorPushSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (decode_error_from_placed_ok)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli
  (CliSpqrExt instCliSpqrExtWithPanics
   cliSpqrExt_shim_sat cliSpqrExt_noAllocShim_sat
   cliSpqrExt_alloc_sat cliSpqrExt_realloc_sat cliSpqrExt_dealloc_sat
   cliSpqrExt_framelessMemcpy_sat
   cliSpqrExt_panic_handle_error cliSpqrExt_panic_handle_alloc_error)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Spec skipField3Spec)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3RawSpec bytesMerge3ProtoRawSpec)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.SpqrV1.Top.Recv
  (ls_subroutine_ok_cro_of_cro ls_subroutine_ok_cro_of_cl)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlaced
  (decodeVarint2_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3ClPlaced
  (skipField3_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlaced
  (bytes_merge_3_cl_placed_ok bytes_merge_3_proto_cl_placed_ok)

/-! ## (a) Own-Block Rebased Contracts under `[CliSpqrExt W H]` -/

/-- Block `261` (`<DecodeError as From<DecodeErrorKind>>::from`) with `withLsCodeLoaded lsmpl`. -/
theorem cliDecodeErrorFrom_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_261).rebase (blkPl_261).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)) := by
  rw [← ls_blockPlacement_base (i := 261)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (decode_error_from_placed_ok
      (cliSpqrExt_shim_sat W)
      (cliSpqrExt_alloc_sat W)
      (cliSpqrExt_panic_handle_alloc_error W))

/-- Block `257` (`<DecodeError>::push`) with `withLsCodeLoaded lsmpl`. -/
theorem cliDecodeErrorPush_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_257).rebase (blkPl_257).base H)
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)) := by
  rw [← ls_blockPlacement_base (i := 257)]
  exact decode_error_push_spec_placed_ok
    (cliSpqrExt_panic_handle_error W)
    (cliSpqrExt_noAllocShim_sat W)
    (cliSpqrExt_alloc_sat W)
    (cliSpqrExt_realloc_sat W)

/-- Block `291` (`decode_varint [local#2]`) with `withLsCodeLoaded lsmpl` (`decodeVarint2Spec A0`). -/
theorem cliDecodeVarint2_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)) := by
  rw [← ls_blockPlacement_base (i := 291)]
  exact decodeVarint2_cl_placed_ok
    (cliSpqrExt_shim_sat W)
    (cliSpqrExt_alloc_sat W)
    (cliSpqrExt_panic_handle_alloc_error W)

/-- Block `263` (`skip_field [local#3]`) with `withLsCodeLoaded lsmpl`. -/
theorem cliSkipField3_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A0)) := by
  rw [← ls_blockPlacement_base (i := 263)]
  exact skipField3_cl_placed_ok
    (cliSpqrExt_shim_sat W)
    (cliSpqrExt_alloc_sat W)
    (cliSpqrExt_panic_handle_alloc_error W)

/-- Block `290` (`bytes::merge [local#3]`) with `withLsCodeRoLoaded lsmpl` (`bytesMerge3RawSpec A0`). -/
theorem cliBytesMerge3_cro [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)) := by
  rw [← ls_blockPlacement_base (i := 290)]
  exact bytes_merge_3_cl_placed_ok
    (cliSpqrExt_noAllocShim_sat W)
    (cliSpqrExt_alloc_sat W)
    (cliSpqrExt_realloc_sat W)
    (cliSpqrExt_dealloc_sat W)
    (cliSpqrExt_framelessMemcpy_sat W)
    (cliSpqrExt_panic_handle_alloc_error W)
    (cliSpqrExt_panic_handle_error W)

theorem subroutine_ok_callInv_of_cro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (hok : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsCallInv lsmpl spec) :=
  subroutine_ok_mono hok
    (fun _ _ _ hpre => by
      dsimp only [withLsCodeRoLoaded,
        CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        withLsCallInv] at hpre ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj,
        satisfies_sepConj_pure_assoc] at hpre ⊢
      exact ⟨⟨hpre.1.2, hpre.1.1⟩, hpre.2⟩)
    (fun _ _ _ _ hpost => hpost)

/-- Block `290` (`bytes::merge [local#3]`) with `withLsCallInv lsmpl` (`bytesMerge3RawSpec A0`). -/
theorem cliBytesMerge3_callInv [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 290)
      (withLsCallInv lsmpl (bytesMerge3RawSpec A0)) :=
  subroutine_ok_callInv_of_cro (cliBytesMerge3_cro W)

/-- Block `290` (`bytes::merge [local#3]`) with `withLsCodeRoLoaded lsmpl` (`bytesMerge3ProtoRawSpec A0`). -/
theorem cliBytesMerge3Proto_cro [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A0)) := by
  rw [← ls_blockPlacement_base (i := 290)]
  exact bytes_merge_3_proto_cl_placed_ok
    (cliSpqrExt_noAllocShim_sat W)
    (cliSpqrExt_alloc_sat W)
    (cliSpqrExt_realloc_sat W)
    (cliSpqrExt_dealloc_sat W)
    (cliSpqrExt_framelessMemcpy_sat W)
    (cliSpqrExt_panic_handle_alloc_error W)
    (cliSpqrExt_panic_handle_error W)

/-! ## (b) Own-Block `blockProgram` Contracts under `[CliSpqrExt W ext]` -/

/-- Own-block `blockProgram` form of Block `261` (`DecodeError::from`) under `Rust.withPanics ext`. -/
theorem cliDecodeErrorFrom_blockProgram_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_261).rebase (blkPl_261).base (Rust.withPanics ext))]
  exact cliDecodeErrorFrom_cl W

/-- Own-block `blockProgram` form of Block `257` (`DecodeError::push`) under `Rust.withPanics ext`. -/
theorem cliDecodeErrorPush_blockProgram_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_257).rebase (blkPl_257).base (Rust.withPanics ext))]
  exact cliDecodeErrorPush_cl W

/-- Own-block `blockProgram` form of Block `291` (`decode_varint [local#2]`) under `Rust.withPanics ext`. -/
theorem cliDecodeVarint2_blockProgram_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_291).rebase (blkPl_291).base (Rust.withPanics ext))]
  exact cliDecodeVarint2_cl W

/-- Own-block `blockProgram` form of Block `263` (`skip_field [local#3]`) under `Rust.withPanics ext`. -/
theorem cliSkipField3_blockProgram_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_263).rebase (blkPl_263).base (Rust.withPanics ext))]
  exact cliSkipField3_cl W

/-- Own-block `blockProgram` form of Block `290` (`bytes::merge [local#3]`) with `withLsCodeRoLoaded`. -/
theorem cliBytesMerge3_blockProgram_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_290).rebase (blkPl_290).base (Rust.withPanics ext))]
  exact cliBytesMerge3_cro W

/-- Own-block `blockProgram` form of Block `290` (`bytes::merge [local#3]`) with `withLsCallInv`. -/
theorem cliBytesMerge3_blockProgram_callInv [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCallInv lsmpl (bytesMerge3RawSpec A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_290).rebase (blkPl_290).base (Rust.withPanics ext))]
  exact cliBytesMerge3_callInv W

/-! ## (c) Caller-Block-Polymorphic Contracts (`Block 325`, `Blocks 294..312`, etc.) -/

/-- Block `261` (`DecodeError::from`) lifted to any caller block `i` (`withLsCodeLoaded`). -/
theorem cliDecodeErrorFrom_at_block_cl [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)) :=
  ls_subroutine_ok_of_block (i := i) (j := 261) (cliDecodeErrorFrom_cl W) hi

/-- Block `257` (`DecodeError::push`) lifted to any caller block `i` (`withLsCodeLoaded`). -/
theorem cliDecodeErrorPush_at_block_cl [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)) :=
  ls_subroutine_ok_of_block (i := i) (j := 257) (cliDecodeErrorPush_cl W) hi

/-- Block `291` (`decode_varint [local#2]`) lifted to any caller block `i` (`withLsCodeLoaded`). -/
theorem cliDecodeVarint2_at_block_cl [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)) :=
  ls_subroutine_ok_of_block (i := i) (j := 291) (cliDecodeVarint2_cl W) hi

/-- Block `263` (`skip_field [local#3]`) lifted to any caller block `i` (`withLsCodeLoaded`). -/
theorem cliSkipField3_at_block_cl [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A0)) :=
  ls_subroutine_ok_of_block (i := i) (j := 263) (cliSkipField3_cl W) hi

/-- Block `290` (`bytes::merge [local#3]`) lifted to any caller block `i` (`withLsCodeRoLoaded`). -/
theorem cliBytesMerge3_at_block_cro [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)) :=
  ls_subroutine_ok_cro_of_cro (i := i) (j := 290) (cliBytesMerge3_cro W) hi

/-- Block `290` (`bytes::merge [local#3]`) lifted to any caller block `i` (`withLsCallInv`). -/
theorem cliBytesMerge3_at_block_callInv [LibsignalPlacement] (W : CliHooks)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 290)
      (withLsCallInv lsmpl (bytesMerge3RawSpec A0)) :=
  subroutine_ok_callInv_of_cro (cliBytesMerge3_at_block_cro W hi)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrVarintPlacedInst
