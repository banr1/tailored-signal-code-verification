/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import ProofLib.SepLogic.WPp

/-!
# Relocatable `OTR::encrypt` over SPQR V1

Relocatable `[LibsignalPlacement]` specifications and proofs for `OTR::encrypt::<HookRng>`
(Block `125`) and `OTR::encrypt::<CoinsRng>` (Block `428`) with `tokenInitPlacedAt` framed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.LibsignalSpqrV1.M4

open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.SpqrV1.GF.Mul2U16

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

variable [LibsignalPlacement]

/-- Relocatable `spqrSendPlacedSpec` with `tokenInitPlacedAt` framed (DEV-SPQR1), the state shorter
    than `2^32` bytes (DEV-SPQR3), and at least 64 random-tape bytes left (DEV-SPQR5). -/
def spqrSendPlacedSpecT (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) : Spec SendCall :=
  { spqrSendPlacedSpec A ctl S with
    pre := fun x s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ tokenInitPlacedAt ∗
        (spqrSendPlacedSpec A ctl S).pre x s
    post := fun x s0 sf => tokenInitPlacedAt ∗ (spqrSendPlacedSpec A ctl S).post x s0 sf }

/-- Relocatable `otrEncryptPlacedSpec` with `tokenInitPlacedAt` framed (DEV-SPQR1), the SPQR send
    state shorter than `2^32` bytes (DEV-SPQR3), and at least 64 bytes on the random tape (DEV-SPQR5). -/
def otrEncryptPlacedSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) : Spec OtrEncryptGhost :=
  { otrEncryptPlacedSpec C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.ot.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ tokenInitPlacedAt ∗
        (otrEncryptPlacedSpec C A ctl uuidParse S).pre x s
    post := fun x s0 sf => tokenInitPlacedAt ∗ (otrEncryptPlacedSpec C A ctl uuidParse S).post x s0 sf }

theorem otrEncrypt_placed_body_ok_frame
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 124)
      (withLsCodeRoLoaded lsmpl
        { spqrSendPlacedSpec A ctl S with
          pre := fun x s => ⌜Q x.st.bytes x.rest⌝ ∗ F ∗ (spqrSendPlacedSpec A ctl S).pre x s
          post := fun x s0 sf => F ∗ (spqrSendPlacedSpec A ctl S).post x s0 sf }))
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
          pre := fun x s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (otrEncryptPlacedSpec C A ctl uuidTryParse S).pre x s
          post := fun x s0 sf => F ∗ (otrEncryptPlacedSpec C A ctl uuidTryParse S).post x s0 sf }) :=
  CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncrypt_placed_body_ok_frame
    Q F C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

theorem otrEncrypt_coins_placed_body_ok_frame
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendPlacedSpec A ctl S with
          pre := fun x s => ⌜Q x.st.bytes x.rest⌝ ∗ F ∗ (spqrSendPlacedSpec A ctl S).pre x s
          post := fun x s0 sf => F ∗ (spqrSendPlacedSpec A ctl S).post x s0 sf }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        { otrEncryptPlacedSpec C A ctl uuidTryParse S with
          pre := fun x s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (otrEncryptPlacedSpec C A ctl uuidTryParse S).pre x s
          post := fun x s0 sf => F ∗ (otrEncryptPlacedSpec C A ctl uuidTryParse S).post x s0 sf }) :=
  CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncrypt_coins_placed_body_ok_frame
    Q F C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

/-- Relocatable `OTR::encrypt::<HookRng>` (`Block 125`) meets `withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpecT C A ctl uuidTryParse S)`
    from `spqr::send` (`Block 124`) meeting `withLsCodeRoLoaded lsmpl (spqrSendPlacedSpecT A ctl S)`
    and the 4 callee contracts. -/
theorem otrEncryptT_placed_ok_of_send
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 124) (withLsCodeRoLoaded lsmpl (spqrSendPlacedSpecT A ctl S)))
    (hMK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_125).rebase (blkPl_125).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_125).rebase (blkPl_125).base H) (blkPl_125).base
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpecT C A ctl uuidTryParse S)) :=
  otrEncrypt_placed_body_ok_frame (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    tokenInitPlacedAt C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

/-- Relocatable `OTR::encrypt::<CoinsRng>` (`Block 428`) meets `withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpecT C A ctl uuidTryParse S)`
    from `spqr::send` (`Block 427`) meeting `withLsCodeRoLoaded lsmpl (spqrSendPlacedSpecT A ctl S)`
    and the 4 callee contracts. -/
theorem otrEncryptT_coins_placed_ok_of_send
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncSpec C.E A))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427) (withLsCodeRoLoaded lsmpl (spqrSendPlacedSpecT A ctl S)))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec C.F A uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpecT C A ctl uuidTryParse S)) :=
  otrEncrypt_coins_placed_body_ok_frame (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    tokenInitPlacedAt C A ctl S H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

end CryptoVerification.LibsignalSpqrV1.M4
