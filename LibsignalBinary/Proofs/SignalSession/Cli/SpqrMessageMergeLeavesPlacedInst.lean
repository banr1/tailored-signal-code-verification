/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChainParamsClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefs
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlaced
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlaced

/-!
# Placed `MessageMerge` Leaf Instantiations

Code-loaded (`withLsCodeLoaded` / `withLsCodeRoLoaded`) contracts for non-chunked protobuf
`MessageMerge` leaves: `ChainParams::merge` (Block 294), `EpochDirection::merge` (Block 299),
`PolynomialDecoder::merge` (Block 296), and `PolynomialEncoder::merge` (Block 297), plus
cross-block caller lifts for `Unchunked.{EkSentCt1Received,Ct1Sent}::merge` (Blocks 311, 312).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl libsignalSessionLib
   libsignalMutatedBlocks withLsCl withLsCodeLoaded
   ls_blockPlacement_base ls_subroutine_ok_cl_of_block
   lsProg_261 lsProg_263 lsProg_290 lsProg_291 lsProg_311 lsProg_312)
open CryptoVerification.RecordCodecs.Placed (lsProg_257)
open CryptoVerification.LibsignalTripleRatchet
  (withLsCodeRoLoaded decodeErrorFromSpec decodeErrorPushSpec)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Spec skipField3Spec)
open CryptoVerification.SpqrV1.Prost.BytesMerge (bytesMerge3RawSpec)
open CryptoVerification.LibsignalSpqrV1 (growOneVecU8Spec)
open CryptoVerification.SpqrV1.Alloc (growOneVecU8_caller_cro_ok)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (blkPC_294 blkPl_294 blkPC_296 blkPl_296 blkPC_297 blkPl_297 blkPC_299 blkPl_299
   ChainParamsMergeGhost chainParamsMergeSpec chainParamsMerge_cl_placed_ok_of_contracts
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
   EpochDirectionMergeGhost epochDirectionMergeSpec epochDirectionMerge_cro_placed_ok_of_contracts
   polyDecoderMergeSpec polyDecoderMerge_cro_placed_ok_of_contracts
   polyEncoderMergeSpec polyEncoderMerge_cro_placed_ok_of_contracts)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (unchunkedEkSentCt1ReceivedMergeSpec unchunkedCt1SentMergeSpec)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.SpqrV1.Top.Recv (ls_subroutine_ok_cro_of_cro ls_subroutine_ok_cro_of_cl)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (CliSpqrExt cliRecvCt2PlacedAllocExt)
open CryptoVerification.E2E.HooksE (A0)

/-! ### 1. Callee Abbreviations & Cross-Block Lifting Helpers -/

/-- own-block `withLsCodeLoaded` contract for Block `261` (`DecodeError::from`). -/
abbrev DecodeErrorFrom261ClOk [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
    (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0))

/-- own-block `withLsCodeLoaded` contract for Block `257` (`DecodeError::push`). -/
abbrev DecodeErrorPush257ClOk [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
    (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0))

/-- own-block `withLsCodeLoaded` contract for Block `291` (`decode_varint [local#2]`). -/
abbrev DecodeVarint291ClOk [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
    (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A0))

/-- own-block `withLsCodeLoaded` contract for Block `263` (`skip_field [local#3]`). -/
abbrev SkipField263ClOk [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
    (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A0))

/-- own-block `withLsCodeRoLoaded` contract for Block `290` (`bytes::merge [local#3]`). -/
abbrev BytesMerge290CroOk [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
    (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0))

/-- own-block `withLsCodeRoLoaded` contract for Block `311`
    (`unchunked::EkSentCt1Received::merge`). -/
abbrev UnchunkedEkSentCt1Received311CroOk [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
    (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0))

/-- own-block `withLsCodeRoLoaded` contract for Block `312`
    (`unchunked::Ct1Sent::merge`). -/
abbrev UnchunkedCt1Sent312CroOk [LibsignalPlacement]
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
    (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0))

private theorem rebase_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (libsignalSessionLib.blockPlacement lsmpl j).base spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec := by
  have h' : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H)
      (libsignalSessionLib.blockPlacement lsmpl j).base spec :=
    hcallee.eq_blockProgram ▸ h
  rwa [ls_blockPlacement_base (i := j)] at h'

private theorem withLsCodeLoaded_of_withLsCl [LibsignalPlacement] {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCl lsmpl spec)) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

theorem lift_261_cl [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromSpec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      261 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_261 (Rust.withPanics ext))
      261 (Rust.withPanics ext)).externs_eq⟩
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block h261 hi (by decide) (by decide))

theorem lift_257_cl [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h257 : DecodeErrorPush257ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushSpec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      257 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_257 (Rust.withPanics ext))
      257 (Rust.withPanics ext)).externs_eq⟩
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block h257 hi (by decide) (by decide))

theorem lift_291_cl [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h291 : DecodeVarint291ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      291 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_291 (Rust.withPanics ext))
      291 (Rust.withPanics ext)).externs_eq⟩
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block h291 hi (by decide) (by decide))

theorem lift_263_cl [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h263 : SkipField263ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      263 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_263 (Rust.withPanics ext))
      263 (Rust.withPanics ext)).externs_eq⟩
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block h263 hi (by decide) (by decide))

theorem lift_261_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      261 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_261 (Rust.withPanics ext))
      261 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl h261 hi (by decide) (by decide)

theorem lift_257_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h257 : DecodeErrorPush257ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      257 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_257 (Rust.withPanics ext))
      257 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl h257 hi (by decide) (by decide)

theorem lift_291_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h291 : DecodeVarint291ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      291 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_291 (Rust.withPanics ext))
      291 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl h291 hi (by decide) (by decide)

theorem lift_263_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h263 : SkipField263ClOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      263 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_263 (Rust.withPanics ext))
      263 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl h263 hi (by decide) (by decide)

theorem lift_290_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h290 : BytesMerge290CroOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      290 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_290 (Rust.withPanics ext))
      290 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cro h290 hi (by decide) (by decide)

/-! ### 2. Extern `RawVec::<Vec<u8>>::grow_one` Discharged from `[CliSpqrExt W ext]` -/

/-- Block `621` `grow_one` on `Vec<Vec<u8>>` discharged directly from `[CliSpqrExt W ext]`. -/
theorem cliGrowOneVecU8_at_block [LibsignalPlacement] {prog : Program} {i : Nat}
    (W : CliHooks) {ext : String → Option (State → State)} [CliSpqrExt W ext]
    [IsLsBlockProg prog i (Rust.withPanics ext)]
    (hi : i < 624 := by decide) :
    subroutine_ok prog (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8Spec A0)) :=
  let hA := cliRecvCt2PlacedAllocExt W (ext := ext)
  growOneVecU8_caller_cro_ok hA.handleError hA.shim hA.alloc hA.realloc hi

/-! ### 3. Block `294`: `ChainParams::merge` -/

/-- Block `294` (`ChainParams::merge`) on `(blkPC_294).rebase` with `withLsCodeLoaded`. -/
theorem cliChainParamsMerge_294_rebase_cl [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext) :
    subroutine_ok ((blkPC_294).rebase (blkPl_294).base (Rust.withPanics ext))
      (blkPl_294).base (withLsCodeLoaded lsmpl (chainParamsMergeSpec A0)) :=
  chainParamsMerge_cl_placed_ok_of_contracts
    (lift_261_cl (i := 294) h261)
    (lift_257_cl (i := 294) h257)
    (lift_291_cl (i := 294) h291)
    (lift_263_cl (i := 294) h263)

/-- Own-block `withLsCodeLoaded` contract for Block `294` (`ChainParams::merge`). -/
theorem cliChainParamsMerge_294_cl [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A0)) :=
  rebase_to_blockProgram (j := 294)
    (cliChainParamsMerge_294_rebase_cl h261 h257 h291 h263)

/-- Own-block `withLsCodeRoLoaded` contract for Block `294` (`ChainParams::merge`). -/
theorem cliChainParamsMerge_294_cro [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 294 (Rust.withPanics ext))
      (lsmpl.base 294) (withLsCodeRoLoaded lsmpl (chainParamsMergeSpec A0)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
    (cliChainParamsMerge_294_cl h261 h257 h291 h263)

/-- Generic caller-lifted `withLsCodeLoaded` contract for Block `294` (`ChainParams::merge`). -/
theorem cliChainParamsMerge_at_block_cl [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 294)
      (withLsCodeLoaded lsmpl (chainParamsMergeSpec A0)) := by
  have h := cliChainParamsMerge_294_rebase_cl h261 h257 h291 h263
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 294)]
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (i := i) (j := 294) h hi (by decide) (by decide))

/-- Generic caller-lifted `withLsCodeRoLoaded` contract for Block `294` (`ChainParams::merge`). -/
theorem cliChainParamsMerge_at_block_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 294)
      (withLsCodeRoLoaded lsmpl (chainParamsMergeSpec A0)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
    (cliChainParamsMerge_at_block_cl h261 h257 h291 h263 hi)

private theorem toDecodeStateChainParams_cl [LibsignalPlacement] {P : Program} {entry : BitVec 64}
    (hok : subroutine_ok P entry (withLsCodeLoaded lsmpl (chainParamsMergeSpec A0))) :
    subroutine_ok P entry
      (withLsCodeLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.chainParamsMergeSpec A0)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : ChainParamsMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => hout

/-- Generic caller-lifted `withLsCodeLoaded` contract for
    `Top.DecodeState.chainParamsMergeSpec A0` at `lsmpl.base 294`. -/
theorem cliDecodeStateChainParamsMerge_at_block_cl [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.chainParamsMergeSpec A0)) :=
  toDecodeStateChainParams_cl (cliChainParamsMerge_at_block_cl h261 h257 h291 h263 hi)

/-- Generic caller-lifted `withLsCodeRoLoaded` contract for
    `Top.DecodeState.chainParamsMergeSpec A0` at `lsmpl.base 294`. -/
theorem cliDecodeStateChainParamsMerge_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 294)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.chainParamsMergeSpec A0)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
    (cliDecodeStateChainParamsMerge_at_block_cl h261 h257 h291 h263 hi)

/-- Block `325` (`spqr::decode_state`) specialization of
    `cliDecodeStateChainParamsMerge_at_block_cl`. -/
theorem cliDecodeStateChainParamsMerge_325_cl [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 294)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.chainParamsMergeSpec A0)) :=
  cliDecodeStateChainParamsMerge_at_block_cl (i := 325) h261 h257 h291 h263

/-! ### 4. Block `299`: `EpochDirection::merge` -/

/-- Block `299` (`EpochDirection::merge`) on `(blkPC_299).rebase` with `withLsCodeRoLoaded`. -/
theorem cliEpochDirectionMerge_299_rebase_cro [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) :
    subroutine_ok ((blkPC_299).rebase (blkPl_299).base (Rust.withPanics ext))
      (blkPl_299).base (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A0)) :=
  epochDirectionMerge_cro_placed_ok_of_contracts
    (lift_261_cro (i := 299) h261)
    (lift_257_cro (i := 299) h257)
    (lift_291_cro (i := 299) h291)
    (lift_263_cro (i := 299) h263)
    (lift_290_cro (i := 299) h290)

/-- Own-block `withLsCodeRoLoaded` contract for Block `299` (`EpochDirection::merge`). -/
theorem cliEpochDirectionMerge_299_cro [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 299 (Rust.withPanics ext))
      (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A0)) :=
  rebase_to_blockProgram (j := 299)
    (cliEpochDirectionMerge_299_rebase_cro h261 h257 h291 h263 h290)

/-- Generic caller-lifted `withLsCodeRoLoaded` contract for Block `299` (`EpochDirection::merge`). -/
theorem cliEpochDirectionMerge_at_block_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A0)) := by
  have h := cliEpochDirectionMerge_299_rebase_cro h261 h257 h291 h263 h290
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 299)]
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 299) h hi (by decide) (by decide)

private theorem toDecodeStateEpochDirection_cro [LibsignalPlacement] {P : Program}
    {entry : BitVec 64}
    (hok : subroutine_ok P entry (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A0))) :
    subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.epochDirectionMergeSpec A0)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : EpochDirectionMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => hout

/-- Generic caller-lifted `withLsCodeRoLoaded` contract for
    `Top.DecodeState.epochDirectionMergeSpec A0` at `lsmpl.base 299`. -/
theorem cliDecodeStateEpochDirectionMerge_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.epochDirectionMergeSpec A0)) :=
  toDecodeStateEpochDirection_cro
    (cliEpochDirectionMerge_at_block_cro h261 h257 h291 h263 h290 hi)

/-- Exact `epochDirectionMerge` field of `DecodeStateCalleeContractsPlacedX` on Block `325`. -/
theorem cliDecodeStateEpochDirectionMerge_325_cro [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) :
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsmpl.base 299)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.epochDirectionMergeSpec A0)) :=
  cliDecodeStateEpochDirectionMerge_at_block_cro (i := 325) h261 h257 h291 h263 h290

/-!
### 5. Block `296` (`PolynomialDecoder::merge`) & Block `297` (`PolynomialEncoder::merge`)
-/

/-- Block `296` (`PolynomialDecoder::merge`) on `(blkPC_296).rebase` with `withLsCodeRoLoaded`,
    with `growOneVecU8Spec A0` discharged internally from `[CliSpqrExt W ext]`. -/
theorem cliPolyDecoderMerge_296_rebase_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (blkPl_296).base (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0)) :=
  polyDecoderMerge_cro_placed_ok_of_contracts
    (lift_261_cro (i := 296) h261)
    (lift_257_cro (i := 296) h257)
    (lift_291_cro (i := 296) h291)
    (lift_263_cro (i := 296) h263)
    (lift_290_cro (i := 296) h290)
    (cliGrowOneVecU8_at_block (i := 296) W (ext := ext))

/-- Own-block `withLsCodeRoLoaded` contract for Block `296` (`PolynomialDecoder::merge`),
    generic in `[CliSpqrExt W ext]`. -/
theorem cliPolyDecoderMerge_296_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0)) :=
  rebase_to_blockProgram (j := 296)
    (cliPolyDecoderMerge_296_rebase_cro W h261 h257 h291 h263 h290)

/-- Generic caller-lifted `withLsCodeRoLoaded` contract for Block `296`
    (`PolynomialDecoder::merge`), ready for `Chunked.*` and `V1State` callers. -/
theorem cliPolyDecoderMerge_at_block_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (W : CliHooks) {ext : String → Option (State → State)} [CliSpqrExt W ext]
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A0)) := by
  have h := cliPolyDecoderMerge_296_rebase_cro W h261 h257 h291 h263 h290
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 296)]
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 296) h hi (by decide) (by decide)

/-- Block `297` (`PolynomialEncoder::merge`) on `(blkPC_297).rebase` with `withLsCodeRoLoaded`,
    with `growOneVecU8Spec A0` discharged internally from `[CliSpqrExt W ext]`. -/
theorem cliPolyEncoderMerge_297_rebase_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (blkPl_297).base (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0)) :=
  polyEncoderMerge_cro_placed_ok_of_contracts
    (lift_261_cro (i := 297) h261)
    (lift_257_cro (i := 297) h257)
    (lift_291_cro (i := 297) h291)
    (lift_263_cro (i := 297) h263)
    (lift_290_cro (i := 297) h290)
    (cliGrowOneVecU8_at_block (i := 297) W (ext := ext))

/-- Own-block `withLsCodeRoLoaded` contract for Block `297` (`PolynomialEncoder::merge`),
    generic in `[CliSpqrExt W ext]`. -/
theorem cliPolyEncoderMerge_297_cro [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0)) :=
  rebase_to_blockProgram (j := 297)
    (cliPolyEncoderMerge_297_rebase_cro W h261 h257 h291 h263 h290)

/-- Generic caller-lifted `withLsCodeRoLoaded` contract for Block `297`
    (`PolynomialEncoder::merge`), ready for `Chunked.*` and `V1State` callers. -/
theorem cliPolyEncoderMerge_at_block_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (W : CliHooks) {ext : String → Option (State → State)} [CliSpqrExt W ext]
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h261 : DecodeErrorFrom261ClOk ext) (h257 : DecodeErrorPush257ClOk ext)
    (h291 : DecodeVarint291ClOk ext) (h263 : SkipField263ClOk ext)
    (h290 : BytesMerge290CroOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A0)) := by
  have h := cliPolyEncoderMerge_297_rebase_cro W h261 h257 h291 h263 h290
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 297)]
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 297) h hi (by decide) (by decide)

/-!
### 6. Blocks `311` & `312`: `Unchunked.{EkSentCt1Received, Ct1Sent}` Caller-Lifting Wrappers
-/

/-- Lift own-block `UnchunkedEkSentCt1Received311CroOk` (`Block 311`) to any caller block
    `i < 619` (`Chunked.*` / `V1State`). -/
theorem liftUnchunkedEkSentCt1Received_311_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h311 : UnchunkedEkSentCt1Received311CroOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      311 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_311 (Rust.withPanics ext))
      311 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 311) h311 hi (by decide) (by decide)

/-- Lift own-block `UnchunkedCt1Sent312CroOk` (`Block 312`) to any caller block
    `i < 619` (`Chunked.*` / `V1State`). -/
theorem liftUnchunkedCt1Sent_312_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (h312 : UnchunkedCt1Sent312CroOk ext) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      312 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_312 (Rust.withPanics ext))
      312 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cro (i := i) (j := 312) h312 hi (by decide) (by decide)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInst
