/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded Stage-1 `X` Contract Definitions

Defines `VmPreserved`-augmented zero-allocation `[LibsignalPlacement]` contracts for
`libsignal_protocol::crypto::hmac_sha256` (`hmacSpecX`, `HmacPlacedOkX`, Block `73`) and
`<RatchetState>::find_receiver_chain_index` (`findIndexPlacedSpecX`, `FindIndexPlacedOkX`, Block `26`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Stage1X.DefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (VmPreserved)
open CryptoGames.HMAC (hmacWith)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl
   withLsCodeLoaded withLsCl
   blkPC_26 blkPl_26 blkPC_73 blkPl_73 lsLogFilterAddr)
open CryptoVerification.LibsignalTripleRatchet (ls_subroutine_ok_cl_of_callee)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalSession (FindIndexGhost)
open Proofs.libsignal.Stage1X (hmacStackX findIndexStackX)

/-! ## `crypto::hmac_sha256` (`0` allocations, `VmPreserved`) -/

/-- `VmPreserved`-augmented contract of `crypto::hmac_sha256` with `hmacStackX = 18432` B stack
(`0` allocations, `onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def hmacSpecX (F : ShaCompress) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, ka, key, ia, inp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ka ∧ (s.readReg64 .x2).toNat = key.length ∧
      s.readReg64 .x3 = ia ∧ (s.readReg64 .x4).toNat = inp.length ∧
      key.length = 32 ∧ inp.length = 1⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s.sp hmacStackX
  post := fun (out, ka, key, ia, inp) s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
    (out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s0.sp hmacStackX

/-- `HmacPlacedOkX`: `hmac_sha256` (Block `73`) meets `DefsBudget.hmacSpecX` under
`[LibsignalPlacement]`. -/
abbrev HmacPlacedOkX [LibsignalPlacement] (F : ShaCompress) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_73).rebase (blkPl_73).base H)
    (blkPl_73).base
    (withLsCodeLoaded lsmpl (hmacSpecX F))

theorem hmac_placed_ok_cl [LibsignalPlacement] {F : ShaCompress} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : HmacPlacedOkX F H) :
    subroutine_ok callerProg (lsmpl.base 73) (withLsCl lsmpl (hmacSpecX F)) :=
  ls_subroutine_ok_cl_of_callee h

/-! ## `<RatchetState>::find_receiver_chain_index` (`0` allocations, `VmPreserved`) -/

/-- `VmPreserved`-augmented relocatable `[LibsignalPlacement]` contract of
`find_receiver_chain_index` with `findIndexStackX = 17408` B stack (`0` allocations; callers pass
`A.repAlloc` and transport `A.pool lim st` via `VmPreserved s0 sf`). -/
def findIndexPlacedSpecX [LibsignalPlacement] (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp findIndexStackX
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace ∧
      match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp findIndexStackX

/-- `FindIndexPlacedOkX`: `find_receiver_chain_index` (Block `26`) meets
`DefsBudget.findIndexPlacedSpecX` under `[LibsignalPlacement]`. -/
abbrev FindIndexPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_26).rebase (blkPl_26).base H)
    (blkPl_26).base
    (withLsCodeLoaded lsmpl (findIndexPlacedSpecX A))

theorem findIndex_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : FindIndexPlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 26) (withLsCl lsmpl (findIndexPlacedSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

end LibsignalBinary.Proofs.SessionRecordAt.Stage1X.DefsBudget
