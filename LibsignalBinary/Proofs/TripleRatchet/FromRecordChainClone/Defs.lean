/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2

/-!
# Specifications for `Chain::clone [local#2]` (`0x3846c`)

Defines the symbol name, stack budget, ghost state, receiver-chain clone specification
`chainCloneSpec`, and sender-chain clone corollary specification `senderChainCloneSpec` for
`<session_structure::Chain as Clone>::clone [local#2]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Symbol name and stack budget -/

/-- `<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]`
(image offset `0x3846c`, 218 instructions). -/
abbrev chainCloneName : String :=
  "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]"

set_option maxRecDepth 2000000 in
open ProofLib.ProgramReflection in
/-- Guard (kernel-checked): `chainCloneName` appears in the image's symbol table
exactly once (`fnAddr` takes the first match). -/
theorem chainCloneName_unique :
    ((libsignalSessionImage.symbols.filter (·.1 == chainCloneName)).length == 1) = true := by
  rfl_kernel

/-- Stack budget of `Chain::clone [local#2]`: `208 + allocHookStack` (`4304` B). -/
abbrev chainCloneStack : Nat := 208 + allocHookStack

/-! ## 1. `Chain::clone [local#2]` on `chainAt` (`0x3846c`, 218 instructions) -/

/-- Ghost arguments `(dst, src, gc)` for `Chain::clone [local#2]` (`0x3846c`). -/
structure ChainCloneGhost where
  /-- Destination buffer (`x0`, 104 bytes). -/
  dst : BitVec 64
  /-- Source `&Chain` (`x1`, 104 bytes). -/
  src : BitVec 64
  /-- Source ghost layout and `ReceiverChain` model value. -/
  gc : ChainGhost × ReceiverChain

/-- Specification of `<session_structure::Chain as Clone>::clone [local#2]` (`0x3846c`):
deep-clones `sender_ratchet_key`, `sender_ratchet_key_private`, optional `chain_key`, and the
`message_keys` vector (including each element's `seed`) from `x.src` into `x.dst`, preserving
`chainAt A x.gc x.src`, or panics via `alloc::raw_vec::handle_error` on allocation failure. -/
def chainCloneSpec (A : RustAlloc) : Spec ChainCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      memRegion x.dst 104 ∗ chainAt A x.gc x.src ∗ A.pool ∗ stackAt s.sp chainCloneStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ g' : ChainGhost,
        ⌜g'.srk.bytes = x.gc.1.srk.bytes ∧ g'.priv.bytes = x.gc.1.priv.bytes ∧
          g'.keys.length = x.gc.1.keys.length⌝ ∗
        chainAt A (g', x.gc.2) x.dst) ∗
      chainAt A x.gc x.src ∗ A.pool ∗ stackAt s0.sp chainCloneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def ChainCloneOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName)
    (chainCloneSpec A)

/-- Target `subroutine_ok` statement for `Chain::clone [local#2]` (`0x3846c`) at `chainCloneSpec`:
`Chain::clone [local#2]` meets `chainCloneSpec A` on `tripleRatchetProgAt b C ctl abs`. -/
def ChainCloneOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chainCloneName)
    (chainCloneSpec A)

/-! ## 2. Sender-Chain Clone Corollary -/

/-- Ghost arguments `(dst, src, g, sc)` for cloning a `Some` sender chain via `Chain::clone [local#2]`. -/
structure SenderChainCloneGhost where
  /-- Destination buffer (`x0`, 104 bytes). -/
  dst : BitVec 64
  /-- Source `&Chain` (`x1`, 104 bytes). -/
  src : BitVec 64
  /-- Source `SenderChainGhost`. -/
  g : SenderChainGhost
  /-- Source `SenderChain` model value. -/
  sc : SenderChain

/-- Sender-chain corollary specification of `<session_structure::Chain as Clone>::clone [local#2]`:
clones `optSenderChainAt A x.src (some x.g) (some x.sc)` into `x.dst` while preserving `x.src`, or
panics on allocation failure. -/
def senderChainCloneSpec (A : RustAlloc) : Spec SenderChainCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      memRegion x.dst 104 ∗ optSenderChainAt A x.src (some x.g) (some x.sc) ∗
      A.pool ∗ stackAt s.sp chainCloneStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ g' : SenderChainGhost,
        ⌜g'.srk.bytes = x.g.srk.bytes ∧ g'.priv.bytes = x.g.priv.bytes⌝ ∗
        optSenderChainAt A x.dst (some g') (some x.sc)) ∗
      optSenderChainAt A x.src (some x.g) (some x.sc) ∗
      A.pool ∗ stackAt s0.sp chainCloneStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def SenderChainCloneOkExt (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr chainCloneName)
    (senderChainCloneSpec A)

/-- Target `subroutine_ok` statement for `Chain::clone [local#2]` (`0x3846c`) at
`senderChainCloneSpec`: `Chain::clone [local#2]` meets `senderChainCloneSpec A` on
`tripleRatchetProgAt b C ctl abs`. -/
def SenderChainCloneOk (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr chainCloneName)
    (senderChainCloneSpec A)

end CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
