/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase

/-!
# 104-Byte `Chain` Slot Chunk-Splitting Lemmas for Stage P3

Stack-offset specialization lemmas (`chunks104W6QAt_sp_0x3e0_eq`, `chunks104W6QAt_sp_0xb20_eq`)
splitting 104-byte `Chain` scratch slots into `8 + 6×16` byte chunks for Stage P3.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

/-! ## 104-Byte `chunks104W6QAt` Stack-Offset Lemmas -/

theorem chunks104W6QAt_sp_0x3e0_eq (sp : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt (sp + 0x3e0#64) w0 q0 q1 q2 q3 q4 q5 =
      ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp + 0x3f0#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp + 0x3f8#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((sp + 0x400#64) ↦₆₄ q1.extractLsb' 64 64) ∗
        ((sp + 0x408#64) ↦₆₄ q2.extractLsb' 0 64) ∗
      ((sp + 0x410#64) ↦₆₄ q2.extractLsb' 64 64) ∗ ((sp + 0x418#64) ↦₆₄ q3.extractLsb' 0 64) ∗
        ((sp + 0x420#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((sp + 0x428#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((sp + 0x430#64) ↦₆₄ q4.extractLsb' 64 64) ∗
        ((sp + 0x438#64) ↦₆₄ q5.extractLsb' 0 64) ∗
      ((sp + 0x440#64) ↦₆₄ q5.extractLsb' 64 64) := by
  unfold chunks104W6QAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem chunks104W6QAt_sp_0xb20_eq (sp : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt (sp + 0xb20#64) w0 q0 q1 q2 q3 q4 q5 =
      ((sp + 0xb20#64) ↦₆₄ w0) ∗ ((sp + 0xb28#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp + 0xb30#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp + 0xb38#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((sp + 0xb40#64) ↦₆₄ q1.extractLsb' 64 64) ∗
        ((sp + 0xb48#64) ↦₆₄ q2.extractLsb' 0 64) ∗
      ((sp + 0xb50#64) ↦₆₄ q2.extractLsb' 64 64) ∗ ((sp + 0xb58#64) ↦₆₄ q3.extractLsb' 0 64) ∗
        ((sp + 0xb60#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((sp + 0xb68#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((sp + 0xb70#64) ↦₆₄ q4.extractLsb' 64 64) ∗
        ((sp + 0xb78#64) ↦₆₄ q5.extractLsb' 0 64) ∗
      ((sp + 0xb80#64) ↦₆₄ q5.extractLsb' 64 64) := by
  unfold chunks104W6QAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

end CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

end
