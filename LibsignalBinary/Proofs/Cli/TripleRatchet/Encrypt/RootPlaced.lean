/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.CorePlaced
public import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Root Theorems for `OutgoingTripleRatchet::encrypt::<Coins>` (Block `428`)

Instantiates the relocatable `OutgoingTripleRatchet::encrypt::<Coins>` body proof at unrestricted,
empty-PQ-state, and SPQR v1 preconditions.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.CliRatchet.Placed

theorem otrEncrypt_coins_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427) (withLsCodeRoLoaded lsmpl (spqrSendCoinsPlacedSpec A ctl S)))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec C A ctl uuidTryParse S)) := by
  have h := otrEncrypt_coins_placed_body_ok (fun _ => True) C A ctl S H
    h_aes h_fmt h_dealloc
    (by simpa only [spec_pre_true] using hSend) hMK hGK hNew hNCK
  simpa only [otrEncryptPlacedSpecQ, spec_pre_true] using h

theorem otrEncryptEmpty_coins_placed_ok_of_send [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl (spqrSendEmptyCoinsPlacedSpec A ctl S)))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQ (· = []) C A ctl uuidTryParse S)) :=
  otrEncrypt_coins_placed_body_ok (· = []) C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

theorem otrEncryptEmpty_coins_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hEmpty : S.SendEmptyOk)
    (hmc : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQ (· = []) C A ctl uuidTryParse S)) := by
  have _ := CryptoVerification.CliRatchet.SendPlaced.instIsLsBlockProg_427 H
  have hSend0 := SpqrSendEmpty.spqrSendEmpty_coins_placed_ok A ctl S hEmpty hmc
  have hSend := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := (blkPC_428).rebase (blkPl_428).base H) hSend0)
  exact otrEncryptEmpty_coins_placed_ok_of_send C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

theorem otrEncryptV1_coins_placed_ok [LibsignalPlacement] (F : SepProp) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec A ctl S with
          pre := fun x s => ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ F ∗ (spqrSendCoinsPlacedSpec A ctl S).pre x s
          post := fun x s0 sf => F ∗ (spqrSendCoinsPlacedSpec A ctl S).post x s0 sf }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length) F C A ctl uuidTryParse S)) :=
  otrEncrypt_coins_placed_body_ok_frame (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length) F
    C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

end CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt
