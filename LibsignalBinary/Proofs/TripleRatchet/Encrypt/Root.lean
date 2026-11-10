/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict
import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core

/-!
# Root Theorems for `OutgoingTripleRatchet::encrypt`

Instantiates `otrEncrypt_body_ok` and its relocatable `[LibsignalPlacement]` counterparts to establish:
- `otrEncrypt_run`: general `SpqrModel` contract given `SpqrSendOk`;
- `otrEncryptEmpty_run`: empty post-quantum state (`pqrState = []`) via `SpqrSendEmpty`;
- `otrEncryptV1_run`: SPQR v1 state via `SpqrSendV1Stmt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Encrypt

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1

/-- Under `SpqrSendOk` and the four chain/message-key callee contracts,
`OTR::encrypt::<HookRng>` (`0x33e0c`) meets `otrEncryptSpec` (`OtrEncryptRunStmt`). -/
theorem otrEncrypt_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hMK : MessageKeysOk img C A ctl abs)
    (hGK : GenerateKeysOk img C A ctl abs)
    (hNew : SignalMessageNewOk img C A ctl uuidTryParse abs)
    (hNCK : NextChainKeyOk img C ctl abs) :
    OtrEncryptRunStmt C A ctl S abs img := by
  intro hHooks hSend himg
  apply root_of_tripleRatchetProgAt himg
  rw [← spec_pre_true (otrEncryptSpec C A ctl uuidTryParse S img)]
  refine otrEncrypt_body_ok (fun _ => True) C A ctl S abs img hHooks himg ?_ hMK hGK hNew hNCK
  rw [spec_pre_true]
  unfold SpqrSendOk at hSend
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt himg,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg spqrSendName] at hSend

/-- Under the four chain/message-key callee contracts, `OTR::encrypt::<HookRng>` (`0x33e0c`)
meets `otrEncryptSpec` restricted to `x.ot.pqrState = []` (`OtrEncryptEmptyRunStmt`) via
`SpqrSendEmpty.spqrSendEmpty_run'`. -/
theorem otrEncryptEmpty_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hMK : MessageKeysOk img C A ctl abs)
    (hGK : GenerateKeysOk img C A ctl abs)
    (hNew : SignalMessageNewOk img C A ctl uuidTryParse abs)
    (hNCK : NextChainKeyOk img C ctl abs) :
    OtrEncryptEmptyRunStmt C A ctl S abs img := by
  intro hHooks hEmpty himg
  apply root_of_tripleRatchetProgAt himg
  refine otrEncrypt_body_ok (· = []) C A ctl S abs img hHooks himg ?_ hMK hGK hNew hNCK
  have hSendEmpty := SpqrSendEmpty.spqrSendEmpty_run' C A ctl S abs img hHooks hEmpty himg
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt himg,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg spqrSendName] at hSendEmpty

/-- Under the four chain/message-key callee contracts and `SpqrSendV1Stmt`,
`OTR::encrypt::<HookRng>` (`0x33e0c`) meets `otrEncryptSpecT` (`OtrEncryptV1RunStmt`). -/
theorem otrEncryptV1_run (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hSendV1 : SpqrSendV1Stmt C A ctl K abs img)
    (hMK : MessageKeysOk img C A ctl abs)
    (hGK : GenerateKeysOk img C A ctl abs)
    (hNew : SignalMessageNewOk img C A ctl uuidTryParse abs)
    (hNCK : NextChainKeyOk img C ctl abs) :
    OtrEncryptV1RunStmt C A ctl K abs img := by
  intro hHooks hSpqr himg
  apply root_of_tripleRatchetProgAt himg
  refine otrEncrypt_body_ok_frame (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    (TokenInit img) C A ctl (spqrV1 C.F K) abs img hHooks himg ?_ hMK hGK hNew hNCK
  have hSend := hSendV1 hHooks hSpqr himg
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt himg,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg spqrSendName] at hSend

theorem otrEncrypt_ext_ok (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName) (spqrSendSpec A ctl S img))
    (hMK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName) (messageKeysSpec C.F A img))
    (hGK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName) ((generateKeysSpec C.F A).inImage img))
    (hNew : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName) ((signalMessageNewSpec C.F A uuidTryParse).inImage img))
    (hNCK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName) (nextChainKeySpec C.F img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrEncryptName) (otrEncryptSpec C A ctl uuidTryParse S img) := by
  rw [← spec_pre_true (otrEncryptSpec C A ctl uuidTryParse S img)]
  refine otrEncrypt_body_ok_ext (fun _ => True) C A ctl S ext img hC himg ?_ hMK hGK hNew hNCK
  rw [spec_pre_true]
  exact hSend

theorem otrEncryptEmpty_ext_ok (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hEmpty : S.SendEmptyOk)
    (himg : Obj.Loads libsignalSessionImage img)
    (hMK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName) (messageKeysSpec C.F A img))
    (hGK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName) ((generateKeysSpec C.F A).inImage img))
    (hNew : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName) ((signalMessageNewSpec C.F A uuidTryParse).inImage img))
    (hNCK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName) (nextChainKeySpec C.F img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrEncryptName)
      { otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s => ⌜x.ot.pqrState = []⌝ ∗ (otrEncryptSpec C A ctl uuidTryParse S img).pre x s } :=
  otrEncrypt_body_ok_ext (· = []) C A ctl S ext img hC himg
    (SpqrSendEmpty.spqrSendEmpty_base_ext C A ctl S ext img hC hEmpty) hMK hGK hNew hNCK

theorem otrEncryptV1_ext_ok (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName) (spqrSendSpecT A ctl S img))
    (hMK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName) (messageKeysSpec C.F A img))
    (hGK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName) ((generateKeysSpec C.F A).inImage img))
    (hNew : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName) ((signalMessageNewSpec C.F A uuidTryParse).inImage img))
    (hNCK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName) (nextChainKeySpec C.F img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrEncryptName)
      (otrEncryptSpecT C A ctl uuidTryParse S img) :=
  otrEncrypt_body_ok_ext_frame (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    (TokenInit img) C A ctl S ext img hC himg hSend hMK hGK hNew hNCK

/-! ## Relocatable `[LibsignalPlacement]` Root Theorems (Blocks `125` and `544`) -/

open CryptoVerification

theorem otrEncrypt_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 124) (withLsCodeRoLoaded lsmpl (spqrSendPlacedSpec A ctl S)))
    (hMK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_125).rebase (blkPl_125).base H) (blkPl_125).base
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpec C A ctl uuidTryParse S)) := by
  have h := otrEncrypt_placed_body_ok (fun _ => True) C A ctl S H
    h_aes h_fmt h_dealloc
    (by simpa only [spec_pre_true] using hSend) hMK hGK hNew hNCK
  simpa only [spec_pre_true] using h

theorem otrEncryptEmpty_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 124)
      (withLsCodeRoLoaded lsmpl
        { spqrSendPlacedSpec A ctl S with
          pre := fun x s => ⌜x.st.bytes = []⌝ ∗ (spqrSendPlacedSpec A ctl S).pre x s }))
    (hMK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_125).rebase (blkPl_125).base H) (blkPl_125).base
      (withLsCodeRoLoaded lsmpl
        { otrEncryptPlacedSpec C A ctl uuidTryParse S with
          pre := fun x s => ⌜x.ot.pqrState = []⌝ ∗ (otrEncryptPlacedSpec C A ctl uuidTryParse S).pre x s }) :=
  otrEncrypt_placed_body_ok (· = []) C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

theorem otrEncrypt_coins_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427) (withLsCodeRoLoaded lsmpl (spqrSendPlacedSpec A ctl S)))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpec C A ctl uuidTryParse S)) := by
  have h := otrEncrypt_coins_placed_body_ok (fun _ => True) C A ctl S H
    h_aes h_fmt h_dealloc
    (by simpa only [spec_pre_true] using hSend) hMK hGK hNew hNCK
  simpa only [spec_pre_true] using h

end CryptoVerification.LibsignalTripleRatchet.Encrypt
