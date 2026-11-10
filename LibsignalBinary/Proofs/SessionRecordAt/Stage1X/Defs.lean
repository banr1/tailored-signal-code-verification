/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Shared Stage-1 `X` Contract Definitions

Defines the shared `SP2Ext` and `[LibsignalPlacement]` contract symbols, stack budgets
(`extHookStack = 16384`), and specifications for `libsignal_protocol::crypto::hmac_sha256`
(`hmacStackX = 18432`, Block `73`) and
`<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index`
(`findIndexStackX = 17408`, Block `26`).
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.Stage1X

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

theorem L1_Stage1X_Defs : True := trivial

-- `Stage1X.SP2Ext` is an alias of `Proofs.libsignal.Hooks2.SP2Ext` (`contractProg b ext`).
export Proofs.libsignal.Hooks2 (SP2Ext)

/- External hook stack budget (`16384`): an alias of `LibsignalTripleRatchet.extHookStack`;
`= RustSpec.externStack` by `Proofs.libsignal.HookStack.externStack_eq_extHookStack` (`rfl`). -/
export CryptoVerification.LibsignalTripleRatchet (extHookStack)

/-! ## `crypto::hmac_sha256` -/

/-- `crypto::hmac_sha256` symbol name. -/
abbrev hmacName : String := "libsignal_protocol::crypto::hmac_sha256"

/-- Stack budget for `crypto::hmac_sha256` with `externStack = 16384`:
`2048 + 16384 = 18432` bytes (480 B own frame + 544 B `new_from_slice` + 1024 B slack + 16384 B
hook stack). -/
abbrev hmacStackX : Nat := 2048 + CryptoVerification.LibsignalTripleRatchet.extHookStack

/-- Contract of `crypto::hmac_sha256` with `hmacStackX = 18432` B stack. -/
def hmacSpecX (F : ShaCompress) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, ka, key, ia, inp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ka ∧ (s.readReg64 .x2).toNat = key.length ∧
      s.readReg64 .x3 = ia ∧ (s.readReg64 .x4).toNat = inp.length ∧
      key.length = 32 ∧ inp.length = 1⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s.sp hmacStackX
  post := fun (out, ka, key, ia, inp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s0.sp hmacStackX

/-- `HmacOkX`: `hmac_sha256` meets `hmacSpecX` on `SP2Ext img.base ext`. -/
abbrev HmacOkX (img : Obj.Image) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr hmacName)
    ((hmacSpecX F).inImage img)

/-! ## `<RatchetState>::find_receiver_chain_index` -/

/-- Symbol name of `<RatchetState>::find_receiver_chain_index`. -/
abbrev findIndexName : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index"

/-- Stack budget for `find_receiver_chain_index` with `externStack = 16384`:
`1024 + 16384 = 17408` bytes. -/
abbrev findIndexStackX : Nat := 1024 + CryptoVerification.LibsignalTripleRatchet.extHookStack

/-- Contract of `find_receiver_chain_index` with `findIndexStackX = 17408` B stack. -/
def findIndexSpecX (img : Obj.Image) (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp findIndexStackX
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s0.sp findIndexStackX

/-- `subroutine_ok` for `find_receiver_chain_index` on `SP2Ext img.base ext` at
`findIndexStackX = 17408` B. -/
abbrev FindIndexOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (SP2Ext img.base ext)
    ((SP2Ext img.base ext).fnAddr findIndexName)
    ((findIndexSpecX img A).inImage img)

/-! ## Relocatable `[LibsignalPlacement]` specifications -/

section Placed

/-- `HmacPlacedOkX`: `hmac_sha256` (Block `73`) meets `hmacSpecX` under `[LibsignalPlacement]`. -/
abbrev HmacPlacedOkX [LibsignalPlacement] (F : ShaCompress) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_73).rebase (blkPl_73).base H)
    (blkPl_73).base
    (withLsCodeLoaded lsmpl (hmacSpecX F))

theorem hmac_placed_ok_cl [LibsignalPlacement] {F : ShaCompress} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : HmacPlacedOkX F H) :
    subroutine_ok callerProg (lsmpl.base 73) (withLsCl lsmpl (hmacSpecX F)) :=
  ls_subroutine_ok_cl_of_callee h

/-- Relocatable `[LibsignalPlacement]` contract of `find_receiver_chain_index` with
`findIndexStackX = 17408` B stack (`lsLogFilterAddr ↦₆₄ 0#64`). -/
def findIndexPlacedSpecX [LibsignalPlacement] (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp findIndexStackX
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp findIndexStackX

/-- `FindIndexPlacedOkX`: `find_receiver_chain_index` (Block `26`) meets `findIndexPlacedSpecX`
under `[LibsignalPlacement]`. -/
abbrev FindIndexPlacedOkX [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_26).rebase (blkPl_26).base H)
    (blkPl_26).base
    (withLsCodeLoaded lsmpl (findIndexPlacedSpecX A))

theorem findIndex_placed_ok_cl [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (h : FindIndexPlacedOkX A H) :
    subroutine_ok callerProg (lsmpl.base 26) (withLsCl lsmpl (findIndexPlacedSpecX A)) :=
  ls_subroutine_ok_cl_of_callee h

end Placed

end Proofs.libsignal.Stage1X
