/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHStep5 -- shake: keep

/-!
# Arithmetic and Bitvector Helpers for `S3CommitSpec`

Small arithmetic and byte-truncation helper lemmas (`le_of_eq_succ_lt`, `setWidth8_zeroExtend64`)
used in the top-level `S3CommitSpec` assembly.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
open CryptoVerification.LibsignalSession
open BS10

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace BS10

theorem le_of_eq_succ_lt {m n : Nat} (heq : m = n + 1) (hlt : n < 2 ^ 32) : m ≤ 2 ^ 32 := by
  omega

end BS10

private theorem setWidth8_zeroExtend64 (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 8 = w.setWidth 8 := by
  exact BitVec.setWidth_setWidth_of_le w (by decide)

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
