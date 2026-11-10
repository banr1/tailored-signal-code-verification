/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Slow

/-!
# In-Image Prost Varint and `DecodeError` Contracts

Establishes `subroutine_ok` on `tripleRatchetProgAt` under `AllocHooks A abs` for the compiled
`prost` entry points:
- `decode_varint_slow::<&mut &[u8]>` (`decodeVarintSlowSpec A`);
- `<DecodeError as From<DecodeErrorKind>>::from` (`decodeErrorFromSpec A`);
- `<DecodeError>::push` (`decodeErrorPushSpec A`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap

theorem decodeVarintSlow_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr varintSlowName)
      (decodeVarintSlowSpec A) :=
  InImage.VarintSlow.decodeVarintSlow_ok_aux_trap b C A abs hA

theorem decodeVarintSlow_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr varintSlowName)
      (decodeVarintSlowSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr varintSlowName]
  exact subroutine_ok_kit_of_trTrap (decodeVarintSlow_ok_trap b C A abs hA)

theorem decodeErrorFrom_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A) := by
  exact InImage.DecodeErrorFrom.decodeErrorFrom_ok_aux_trap b C A abs hA

theorem decodeErrorFrom_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeErrorFromName]
  exact subroutine_ok_kit_of_trTrap (decodeErrorFrom_ok_trap b C A abs hA)

theorem decodeErrorPush_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A) := by
  exact InImage.DecodeErrorPush.decodeErrorPush_ok'_trap b C A abs hA

theorem decodeErrorPush_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeErrorPushName]
  exact subroutine_ok_kit_of_trTrap (decodeErrorPush_ok_trap b C A abs hA)

end CryptoVerification.LibsignalTripleRatchet
