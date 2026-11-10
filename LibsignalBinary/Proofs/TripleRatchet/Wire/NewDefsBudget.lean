/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs

/-!
# Budget-Threaded Specification for `<SignalMessage>::new`

Defines the exact allocator event sequence `signalMessageNewEvents`, envelope `SignalMessageNewEnv`,
and budget-threaded specifications `signalMessageNewSpecWithStack`, `signalMessageNewSpec`, and
`signalMessageNewSpecX` for `<libsignal_protocol::protocol::SignalMessage>::new` (Block `63`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (ShaCompress SignalMessage)
open CryptoVerification.LibsignalProtoCodec (encode)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SignalMessageGhost UuidParser signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet
  (signalMessageNewName signalMessageNewStack signalMessageNewStackX SignalMessageNewGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (computeMacEvents)

/-! ## Re-Exports from `Wire.NewDefs` -/

abbrev signalMessageNewName := CryptoVerification.LibsignalTripleRatchet.signalMessageNewName
abbrev signalMessageNewStack := CryptoVerification.LibsignalTripleRatchet.signalMessageNewStack
abbrev signalMessageNewStackX := CryptoVerification.LibsignalTripleRatchet.signalMessageNewStackX
abbrev SignalMessageNewGhost := CryptoVerification.LibsignalTripleRatchet.SignalMessageNewGhost

/-! ## Allocator Event List & Envelope for `<SignalMessage>::new` -/

/-- Exact allocator event sequence of `<SignalMessage>::new` (Block `63`), in execution order:
1. Optional 36-byte `serialize_addresses` buffer (`rustAllocEvents 36 1` when `(x.addresses parse).isSome`);
2. 33-byte temporary `PublicKey::serialize` buffer (`publicKeySerializeEvents`);
3. Temporary `ciphertext` copy (`rustAllocEvents x.ciphertext.length 1` when non-empty);
4. Temporary `pq_ratchet` copy (`rustAllocEvents x.pqRatchet.length 1` when non-empty);
5. `serialized: Vec<u8>` buffer of exact capacity `(encode (x.protoMsg parse)).length + 9`;
6. `compute_mac` (`computeMacEvents`);
7. Final `ciphertext: Box<[u8]>` clone (`rustAllocEvents x.ciphertext.length 1` when non-empty);
8. Final `pq_ratchet: Vec<u8>` clone (`rustAllocEvents x.pqRatchet.length 1` when non-empty);
9. Deallocations of temporary `ratchet_key` (`33` B), `ciphertext`, and `pq_ratchet` buffers. -/
def signalMessageNewEvents (parse : UuidParser) (x : SignalMessageNewGhost) : List AllocEvent :=
  (if (x.addresses parse).isSome then rustAllocEvents 36 1 else []) ++
    publicKeySerializeEvents ++
    (if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1) ++
    (if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1) ++
    rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1 ++
    computeMacEvents ++
    (if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1) ++
    (if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1) ++
    rustDeallocEvents 33 1 ++
    (if x.ciphertext.isEmpty then [] else rustDeallocEvents x.ciphertext.length 1) ++
    (if x.pqRatchet.isEmpty then [] else rustDeallocEvents x.pqRatchet.length 1)

/-- Allocator event envelope of `<SignalMessage>::new`. -/
def SignalMessageNewEnv (parse : UuidParser) (x : SignalMessageNewGhost)
    (evs : List AllocEvent) : Prop :=
  evs = signalMessageNewEvents parse x

theorem fitsEnv_signalMessageNew_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (parse : UuidParser) (x : SignalMessageNewGhost) :
    FitsEnv M lim st (SignalMessageNewEnv parse x) ↔
      FitsEvents M lim st (signalMessageNewEvents parse x) :=
  FitsEnv.eq_iff

/-! ## Budget-Threaded Specifications of `<SignalMessage>::new` (Block `63`) -/

/-- Stack-parameterized budget contract of `<SignalMessage>::new`
(`totalStack = signalMessageNewStack` or `signalMessageNewStackX`).
Under `FitsEnv M lim st (SignalMessageNewEnv parse x)`, `onPanic = ⌜False⌝` and
`onOom = ⌜False⌝`. -/
def signalMessageNewSpecWithStack [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) (totalStack : Nat) :
    Spec (SignalMessageNewGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.messageVersion ∧
      s.readReg64 .x1 = x.macKeyA ∧ s.readReg64 .x2 = 32#64 ∧
      s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64) ∧
      (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x4 = x.remA ∧
      s.readReg64 .x5 = x.senderRatchetKeyA ∧
      (s.readReg64 .x6).setWidth 32 = x.counter ∧
      (s.readReg64 .x7).setWidth 32 = x.previousCounter ∧
      s.readReg64 .x8 = x.ret ∧
      x.ciphertext.length ≤ 2 ^ 32 ∧ x.pqRatchet.length < 2 ^ 32 ∧
      FitsEnv M lim st (SignalMessageNewEnv parse x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      x.inputsAt A.repAlloc s.sp ∗
      memRegion x.ret 120 ∗ A.pool lim st s ∗ stackAt s.sp totalStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      x.inputsAt A.repAlloc s0.sp ∗
      (∃∗ g : SignalMessageGhost, signalMessageAt A.repAlloc g x.ret (x.model F parse)) ∗
      A.pool lim (M.stepEvents (signalMessageNewEvents parse x) st) sf ∗
      stackAt s0.sp totalStack

/-- Budget-threaded `signalMessageNewSpec` (`signalMessageNewStack`). -/
abbrev signalMessageNewSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) :
    Spec (SignalMessageNewGhost × M.σ) :=
  signalMessageNewSpecWithStack M A lim F parse signalMessageNewStack

/-- Budget-threaded `signalMessageNewSpecX` (`signalMessageNewStackX`). -/
abbrev signalMessageNewSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) :
    Spec (SignalMessageNewGhost × M.σ) :=
  signalMessageNewSpecWithStack M A lim F parse signalMessageNewStackX

abbrev signalMessageNewBudgetSpecWithStack [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) (totalStack : Nat) :
    Spec (SignalMessageNewGhost × M.σ) :=
  signalMessageNewSpecWithStack M A lim F parse totalStack

abbrev signalMessageNewBudgetSpec [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) :
    Spec (SignalMessageNewGhost × M.σ) :=
  signalMessageNewSpec M A lim F parse

abbrev signalMessageNewBudgetSpecX [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) (parse : UuidParser) :
    Spec (SignalMessageNewGhost × M.σ) :=
  signalMessageNewSpecX M A lim F parse

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
