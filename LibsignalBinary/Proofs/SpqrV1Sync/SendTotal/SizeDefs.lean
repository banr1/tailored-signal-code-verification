/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Proofs.SpqrV1Sync.TopSize
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

set_option warningAsError false

/-!
# Serialized Braid Size Statement

Defines `BSizeStmt` in a standalone module so `StateSizeBase` simp lemmas only enter the size-bound
proof files.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoGames.LibsignalSession (ShaCompress)
/-- Every `BOk` braid state satisfies `rawV1State st.into_pb ≤ 2 ^ 40`. -/
def BSizeStmt (F : ShaCompress) : Prop :=
  ∀ st : St F, BOk st → CryptoVerification.SpqrV1.Top.StateSize.rawV1State st.into_pb ≤ 2 ^ 40

end CryptoVerification.SpqrV1Sync.SendTotal
