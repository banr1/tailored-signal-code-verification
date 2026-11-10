/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.All -- shake: keep

/-!
# Call-Site Lemmas for In-Image Whole-Crate Callees

Restates the contracts for `PublicKey::try_from`, `ServiceId::parse_from_service_id_string`,
`PrivateKey::serialize`, and `<ProtocolAddress as Display>::fmt` at call-site offset
`fnAddr name + k` (as well as relocatable cross-block `[LibsignalPlacement]` call sites).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr

/-- Transport `subroutine_ok` from `fnAddr callee` to `fnAddr name + k` when
`fnOff name + k = fnOff callee`. -/
theorem inImage_ok_at_rebase {α : Type} {b : BitVec 64}
    {H : String → Option (State → State)} {spec : Spec α}
    {name callee : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr callee) spec) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) spec := by
  rwa [← Program.fnAddr_rel rfl rfl hk]

theorem inImage_ok_at {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {spec : Spec α}
    {name callee : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr callee) spec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) spec :=
  inImage_ok_at_rebase hk h

theorem pk_try_from_ok_at_ext (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pkTryFromName) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k) (pkTryFromCodeSpec img) :=
  inImage_ok_at_rebase hk (pkTryFrom_ok_ext img ext himg)

theorem pk_try_from_ok_at (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pkTryFromName) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k) (pkTryFromCodeSpec img) :=
  inImage_ok_at hk (pkTryFrom_ok img C ctl abs himg)

/-- Contract-backed `ServiceId::parse_from_service_id_string` at call distance `k` from `name`. -/
theorem parse_sid_ok_at_of_contract (b : BitVec 64)
    (H : String → Option (State → State))
    (huuid : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseSpec uuidTryParse))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff parseSidName) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      (parseSidCodeSpec uuidTryParse) :=
  inImage_ok_at_rebase hk (parseSid_ok_of_contract b H huuid)

/-- Stack-framed contract-backed `ServiceId::parse_from_service_id_string` at call distance `k`. -/
theorem parse_sid_ok_at_of_contract_stack (b : BitVec 64)
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr uuidTryParseName)
      (uuidTryParseStackSpec hookStack))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff parseSidName) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      (parseSidCodeStackSpec hookStack) :=
  inImage_ok_at_rebase hk (parseSid_ok_of_contract_stack b H hookStack huuid)

theorem parse_sid_ok_at_ext (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff parseSidName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (parseSidCodeSpec uuidTryParse) :=
  inImage_ok_at_rebase hk (parseSid_ok_ext b C A ctl S ext hC)

theorem parse_sid_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff parseSidName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (parseSidCodeSpec uuidTryParse) :=
  inImage_ok_at hk (parseSid_ok b C ctl abs)

theorem priv_serialize_ok_at_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hC : AllocContracts b A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff privSerializeName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (privSerializeSpec A) :=
  inImage_ok_at_rebase hk (privSerialize_ok_ext b A ext hC)

theorem priv_serialize_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff privSerializeName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (privSerializeSpec A) :=
  inImage_ok_at hk (privSerialize_ok b C A ctl abs hA)

theorem addr_display_ok_at_ext (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff addrDisplayName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (addrDisplaySpec A) :=
  inImage_ok_at_rebase hk (addrDisplay_ok_ext b C A ctl S ext hC)

theorem addr_display_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff addrDisplayName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (addrDisplaySpec A) :=
  inImage_ok_at hk (addrDisplay_ok b C A ctl abs hW)

/-- Image-invariant stack-framed `ServiceId::parse_from_service_id_string` at call distance `k`. -/
theorem parse_sid_ok_at_of_contract_stack_inImage (img : Obj.Image)
    (H : String → Option (State → State)) (hookStack : Nat := 0)
    (huuid : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr uuidTryParseName)
      ((uuidTryParseStackSpec hookStack).inImage img))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff parseSidName) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr name + BitVec.ofNat 64 k)
      ((parseSidCodeStackSpec hookStack).inImage img) :=
  inImage_ok_at_rebase hk (parseSid_ok_of_contract_stack_inImage img H hookStack huuid)

theorem priv_serialize_ok_at_ext_x (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (hC : AllocContractsX img A ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff privSerializeName) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((privSerializeSpecX A).inImage img) :=
  inImage_ok_at_rebase hk (privSerialize_ok_ext_x hC)

theorem addr_display_ok_at_ext_x (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    (ext : String → Option (State → State)) (hC : Stage2ContractsX img C A encFn decFn ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff addrDisplayName) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((addrDisplaySpec A).inImage img) :=
  inImage_ok_at_rebase hk (addrDisplay_ok_ext_x hC)

/-! ## Relocatable Cross-Block Call-Site Lemmas (`[LibsignalPlacement]`) -/

/-- Relocatable `PublicKey::try_from` (Block `211`) lifted to any caller block `prog`. -/
theorem pk_try_from_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 211) (withLsCodeLoaded lsmpl pkTryFromPlacedSpec) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (pkTryFrom_placed_ok H)) (_hi := hi)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any caller block
`prog` from `huuid` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_contract [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (uuidTryParseSpec uuidTryParse))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_contract H huuid) (_hi := hi)

/-- Relocatable stack-framed `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any
caller block `prog` from `huuid` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_contract_stack [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H] (hookStack : Nat := 0)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack)))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_contract_stack H hookStack huuid) (_hi := hi)

/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) lifted to any caller block
`prog` from `uuidTryParseCodeSpec uuidTryParse` on Block `252`. -/
theorem parse_sid_placed_ok_at_of_code [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (parseSid_placed_ok_of_code H huuid) (_hi := hi)

/-- Relocatable `PrivateKey::serialize` (Block `208`) lifted to any caller block `prog`. -/
theorem priv_serialize_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok hshim halloc hpanic))
    (_hi := hi)

/-- Relocatable `PrivateKey::serialize` (`privSerializeSpecX A`, Block `208`) lifted to any caller
block `prog`. -/
theorem priv_serialize_placed_ok_at_x [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 208)
      (withLsCodeLoaded lsmpl (privSerializeSpecX A)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (privSerialize_placed_ok_x hshim halloc hpanic))
    (_hi := hi)

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) lifted to any caller block `prog`. -/
theorem addr_display_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hW : HookSat H lsFmtWriteSym (fmtWriteSpec A))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 215)
      (withLsCodeLoaded lsmpl (addrDisplaySpec A)) :=
  ls_subroutine_ok_of_block (callerProg := prog)
    (subroutine_ok_withLsCodeLoaded_of_plain (addrDisplay_placed_ok hW))
    (_hi := hi)

end CryptoVerification.LibsignalTripleRatchet
