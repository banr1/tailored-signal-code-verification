/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsW
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget

/-!
# Budget-Threaded `DefsW` Prost Decoding Leaf Specifications

Defines the `RustCliAllocBudget`-threaded contracts (`*SpecW`) and relocatable `[LibsignalPlacement]`
`subroutine_ok` obligations (`*PlacedOkW`) for `DecodeError::from` / `push`,
`drop_glue::<DecodeError>` (Block `5`), `decode_varint_slice` (Block `76`), `int32::merge`
(Block `8`), `skip_field` (Block `1`), and `bytes::merge` (Block `7`) at `*StackW`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsWBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpecWithStack decodeErrorPushBudgetSpecWithStack)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded
   blkPC_1 blkPl_1 blkPC_4 blkPl_4 blkPC_7 blkPl_7 blkPC_8 blkPl_8 blkPC_76 blkPl_76)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSliceGhost Int32MergeGhost SkipFieldGhost BytesMergeGhost)
open CryptoVerification.LibsignalTripleRatchet.Prost.X
  (decodeErrorHookStackW decodeVarintSliceStackW int32MergeStackW skipFieldStackW
   bytesMergeStackW dropDecodeErrorStackW)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (dropDecodeErrorSpecGen decodeVarintSliceSpecGen int32MergeSpecGen skipFieldSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeRawSpecGen)

/-! ## Stack budget definitional alignment -/

theorem dropDecodeErrorStackW_eq_gen :
    0x20 + (allocHookStack + extHookStack) = dropDecodeErrorStackW := rfl

theorem decodeVarintSliceStackW_eq_gen :
    0x50 + decodeErrorHookStackW = decodeVarintSliceStackW := rfl

theorem int32MergeStackW_eq_gen :
    0x50 + (0x50 + decodeErrorHookStackW) = int32MergeStackW := rfl

theorem skipFieldStackW_eq_gen (depth : Nat) :
    (depth + 1) * 0x60 + (0x50 + decodeErrorHookStackW) = skipFieldStackW depth := rfl

theorem bytesMergeStackW_eq_gen :
    0xe0 + (0x50 + decodeErrorHookStackW) = bytesMergeStackW := rfl

/-! ## `DecodeError::from` and `DecodeError::push` hooks -/

/-- Budget-threaded `DecodeError::from` contract at `decodeErrorHookStackW`. -/
def decodeErrorFromSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × M.σ) :=
  decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackW

/-- Budget-threaded `DecodeError::push` contract at `decodeErrorHookStackW`. -/
def decodeErrorPushSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × Nat × M.σ) :=
  decodeErrorPushBudgetSpecWithStack M A lim decodeErrorHookStackW

/-! ## Prost decoding leaf specifications at `*StackW` -/

/-- Budget-threaded `drop_glue::<DecodeError>` contract at `dropDecodeErrorStackW`. -/
def dropDecodeErrorSpecW [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × M.σ) :=
  dropDecodeErrorSpecGen A lim (allocHookStack + extHookStack)

/-- Budget-threaded `decode_varint_slice` contract at `decodeVarintSliceStackW`. -/
def decodeVarintSliceSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSliceGhost × M.σ) :=
  decodeVarintSliceSpecGen A lim decodeErrorHookStackW

/-- Budget-threaded `int32::merge::<&mut &[u8]>` contract at `int32MergeStackW`. -/
def int32MergeSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Int32MergeGhost × M.σ) :=
  int32MergeSpecGen A lim decodeErrorHookStackW

/-- Budget-threaded `skip_field::<&mut &[u8]> [local#1]` contract at `skipFieldStackW`. -/
def skipFieldSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SkipFieldGhost × M.σ) :=
  skipFieldSpecGen A lim decodeErrorHookStackW

/-- Budget-threaded `bytes::merge::<Vec<u8>, &mut &[u8]> [local#1]` raw contract at
`bytesMergeStackW` (`x.bs.length < 2 ^ 62`, `reqCap = false`). -/
def bytesMergeRawSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  bytesMergeRawSpecGen A lim decodeErrorHookStackW false

/-! ## Relocatable `[LibsignalPlacement]` obligations -/

/-- `bytesMergeRawSpecW A lim` under `LibsignalCodeRoLoaded lsmpl`. -/
def bytesMergePlacedSpecW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (bytesMergeRawSpecW A lim)

/-- `drop_glue::<DecodeError>` (Block `5`) meets `dropDecodeErrorSpecW` under `[LibsignalPlacement]`. -/
def DropDecodeErrorPlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_4).rebase (blkPl_4).base H)
    (blkPl_4).base (withLsCodeLoaded lsmpl (dropDecodeErrorSpecW A lim))

/-- `decode_varint_slice` (Block `76`) meets `decodeVarintSliceSpecW` under `[LibsignalPlacement]`. -/
def DecodeVarintSlicePlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
    (blkPl_76).base (withLsCodeLoaded lsmpl (decodeVarintSliceSpecW A lim))

/-- `int32::merge` (Block `8`) meets `int32MergeSpecW` under `[LibsignalPlacement]`. -/
def Int32MergePlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
    (blkPl_8).base (withLsCodeLoaded lsmpl (int32MergeSpecW A lim))

/-- `skip_field` (Block `1`) meets `skipFieldSpecW` under `[LibsignalPlacement]`. -/
def SkipFieldPlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
    (blkPl_1).base (withLsCodeLoaded lsmpl (skipFieldSpecW A lim))

/-- `bytes::merge` (Block `7`) meets `bytesMergePlacedSpecW` under `[LibsignalPlacement]`. -/
def BytesMergePlacedOkW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
    (blkPl_7).base (bytesMergePlacedSpecW A lim)

end LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsWBudget
