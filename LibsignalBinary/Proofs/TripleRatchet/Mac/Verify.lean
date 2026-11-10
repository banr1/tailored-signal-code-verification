/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Mac.MacCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacWithAddresses
import ProofLib.SepLogic.WPFrozen

/-!
# Top-Level Composition for `<SignalMessage>::verify_mac_with_addresses`

Composes `serialize_addresses`, `compute_mac`, and `VerifyMacWithAddresses` into top-level
`subroutine_ok` contracts on `tripleRatchetProgAt`, `tripleRatchetProgAtExt`, and
`[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

theorem verifyMacWithAddresses_subroutine_ok_of_base_aligned_contracts
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name) (compress256Spec C.F))
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName) blackBoxSpec)
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName) (uuidTryParseCodeSpec uuidTryParse))
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_compute_ext img C A ext hb hA hbb_raw huuid
    (computeMac_subroutine_ok_of_contracts img C A ext hA hcomp hnew hpk)

theorem verifyMacWithAddresses_subroutine_ok_of_contracts
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name) (compress256Spec C.F))
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName) blackBoxSpec)
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName) (uuidTryParseCodeSpec uuidTryParse))
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_loads_ext img himg C A ext hA hbb_raw huuid
    (computeMac_subroutine_ok_of_contracts img C A ext hA hcomp hnew hpk)

theorem verifyMacWithAddresses_subroutine_ok_ext
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel)
    (ext : String → Option (State → State))
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkExt img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_contracts img himg C A ext
    hC.toAllocContracts hC.compress256 hC.black_box hC.uuid_try_parse hnew hpk

theorem verifyMacWithAddresses_subroutine_ok_of_base_aligned_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocHooks A abs)
    (hnew : NewFromSliceOk_trap img C abs)
    (hpk : PublicKeySerializeOk_trap img.base C A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_compute_trap img C A abs hb hA
    (computeMac_subroutine_ok_trap img C A abs hA hnew hpk)

theorem verifyMacWithAddresses_subroutine_ok_of_base_aligned
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocHooks A abs)
    (hnew : NewFromSliceOk img C ctl abs)
    (hpk : PublicKeySerializeOk img.base C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_compute img C A ctl abs hb hA
    (computeMac_subroutine_ok img C A ctl abs hA hnew hpk)

theorem verifyMacWithAddresses_subroutine_ok_trap
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hnew : NewFromSliceOk_trap img C abs)
    (hpk : PublicKeySerializeOk_trap img.base C A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_loads_trap img himg C A abs hA
    (computeMac_subroutine_ok_trap img C A abs hA hnew hpk)

theorem verifyMacWithAddresses_subroutine_ok
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hnew : NewFromSliceOk img C ctl abs)
    (hpk : PublicKeySerializeOk img.base C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_loads img himg C A ctl abs hA
    (computeMac_subroutine_ok img C A ctl abs hA hnew hpk)


def VerifyMacWithAddressesOkX
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
    ((verifyMacWithAddressesSpecX img C.F A parse).inImage img)

theorem verifyMacWithAddresses_subroutine_ok_of_base_aligned_contracts_x
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContractsX img A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name)
      ((withStack (compress256Spec C.F) extHookStack).inImage img))
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((withStack (uuidTryParseSpec uuidTryParse) extHookStack).inImage img))
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkX img A ext) :
    VerifyMacWithAddressesOkX img C A uuidTryParse ext :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_compute_ext_x img C A ext hb hA hbb_raw huuid
    (computeMac_subroutine_ok_of_contracts_x img C A ext hA hcomp hnew hpk)

theorem verifyMacWithAddresses_subroutine_ok_of_contracts_x
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hcomp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name)
      ((withStack (compress256Spec C.F) extHookStack).inImage img))
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((withStack (uuidTryParseSpec uuidTryParse) extHookStack).inImage img))
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkX img A ext) :
    VerifyMacWithAddressesOkX img C A uuidTryParse ext :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_subroutine_ok_of_loads_ext_x img himg C A ext hA hbb_raw huuid
    (computeMac_subroutine_ok_of_contracts_x img C A ext hA hcomp hnew hpk)

theorem verifyMacWithAddresses_subroutine_ok_ext_x
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State))
    (hC : Stage2ContractsX img C A encFn decFn ext)
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((withStack (uuidTryParseSpec uuidTryParse) extHookStack).inImage img))
    (hnew : NewFromSliceOkExt img C ext)
    (hpk : PublicKeySerializeOkX img A ext) :
    VerifyMacWithAddressesOkX img C A uuidTryParse ext :=
  verifyMacWithAddresses_subroutine_ok_of_contracts_x img himg C A ext
    hC.toAllocContractsX hC.compress256 hC.black_box huuid hnew hpk

/-! ## Relocatable `[LibsignalPlacement]` top-level contracts -/

private theorem ls_subroutine_ok_lscl_of_block [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

theorem verifyMacWithAddresses_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpec)
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_placed_ok_of_compute C A parse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc hpanic))
    (ls_subroutine_ok_lscl_of_block (computeMac_placed_ok C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_ok_x [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec extHookStack)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX A)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym)
      (withStack blackBoxU8Spec extHookStack))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecX C.F A uuidTryParse)) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_placed_ok_of_compute_x C A uuidTryParse H
    hdealloc hbb_raw
    (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok_x hparse hshim halloc hpanic))
    (ls_subroutine_ok_lscl_of_block (computeMac_placed_ok_x C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

theorem verifyMacWithAddresses_placed_cro_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec parse)))
    (hnew : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 114)
      (withLsCodeRoLoaded lsmpl (newFromSliceSpec C.F)))
    (hpk : subroutine_ok ((blkPC_60).rebase (blkPl_60).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpec A)))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpec)
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hpanic : H lsMacHandleErrorSym = some Rust.panicked)
    (hmemcpy : HookSat H lsMacMemcpySym sessionMemcpyRegionSpec)
    (hcompress : HookSat H lsMacCompress256Sym (compress256Spec C.F))
    (hmemset : HookSat H lsMacMemsetSym sessionMemsetRegionSpec) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  Mac.VerifyMacWithAddresses.verifyMacWithAddresses_placed_cro_ok_of_compute C A parse H
    hdealloc hbb_raw
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_lscl_of_block (serialize_addresses_placed_ok hparse hshim halloc hpanic)))
    (keys_ls_subroutine_ok_of_block_cro (computeMac_placed_cro_ok C A H hnew hpk hmemcpy hcompress hdealloc hmemset))

end CryptoVerification.LibsignalTripleRatchet

