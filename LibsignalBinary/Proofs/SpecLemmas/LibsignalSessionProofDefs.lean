/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalHmac
public import GeneratedLean.LibsignalSessionObj
public import ProofLib.Hoare.LibcHooks
public import ProofLib.ObjectLoad
public import LibsignalBinary.Proofs.SpecLemmas.RustHeapAllocProofDefs

/-!
# Proof-Side `RatchetState::consume_message_key` Specification

Defines the machine-level ghost state (`ConsumeMessageKeyGhost`), Hoare contract
(`consumeMessageKeySpec`), correctness statement (`ConsumeMessageKeyMeetsSpec`), and non-vacuity
predicate (`ConsumeMessageKeySpecSatisfiable`) for `RatchetState::consume_message_key`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession
open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- The program: the loaded session image with the hooks, panics via `Rust.withPanics`. -/
abbrev sessionProg (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Program :=
  Program.ofImage img (Rust.withPanics (sessionExterns F alloc))

/-- Entry of `RatchetState::consume_message_key`, by symbol name. It is image offset `0xded8`
(`cmkEntry_eq` in `LibsignalBinary/Proofs/ConsumeMessageKey/Defs.lean`). -/
abbrev cmkEntry (img : Obj.Image) : BitVec 64 :=
  (Program.ofImage img).fnAddr "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

/-- Stack the method may use below `sp`: its 480-byte frame, the deepest callee chain
(`hmac_sha256` 480 + `new_from_slice` 544) and hook stacks, rounded up. -/
abbrev cmkStack : Nat := 8192

/-- Ghost of a cmk call: the session model's state and arguments, the ghost layout, and the
argument addresses. -/
structure ConsumeMessageKeyGhost where
  /-- `self: &mut RatchetState` (`x0`). -/
  self : BitVec 64
  G : RatchetGhost
  st : RatchetState
  /-- `their_ephemeral: &PublicKey` (`x1`, 32 bytes). -/
  their : PublicKey
  theirA : BitVec 64
  /-- `chain_key: ChainKey` (by value; passed as a pointer `x2` to a 36-byte caller copy that the
  callee owns and mutates). -/
  ck : ChainKey
  ckA : BitVec 64
  /-- `counter: u32` (`w3`). -/
  counter : BitVec 32
  /-- `original_message_type: CiphertextMessageType` (`w4`, `repr(u8)`). -/
  msgType : MessageType
  /-- The sret (`x8`, 88 bytes). -/
  ret : BitVec 64

/-- The session model's result and final state of the call. -/
def ConsumeMessageKeyGhost.model (F : ShaState → List (BitVec 8) → ShaState) (x : ConsumeMessageKeyGhost) :
    Except SignalProtocolError MessageKeyGenerator × RatchetState :=
  (RatchetState.consumeMessageKey F x.their x.ck x.counter x.msgType).exec x.st

/-- The receiver chain a call may rewrite: on success, the chain of `their` (removing a stored
skipped key when `counter < index`, or storing skipped keys and advancing the chain key when
`counter ≥ index`); on an error result (missing chain, duplicated message, or counter too far in the
future), none. -/
def ConsumeMessageKeyGhost.touched (F : ShaState → List (BitVec 8) → ShaState) (x : ConsumeMessageKeyGhost) : Option Nat :=
  match (x.model F).1 with
  | .ok _ => x.st.findReceiverChainIndex x.their
  | .error _ => none

/-- The binding spec of `consume_message_key`. From a state holding the representation of the
session model's state `st` (`ratchetAt A self G st`) and the arguments, with logging off:
* normal return only if the model does not panic. Then `self` holds the model's final state
  with a ghost layout `G'` that equals `G` except at the one chain the call rewrites
  (`x.touched F`), where only its `message_keys` buffer, key pins and chain-key pin may change. So
  the `receiver_chains` buffer, every other chain's `Vec`s (headers, buffers, contents) and the
  rewritten chain's key `Vec`s are unchanged. The sret holds the model's result, `their`, the stack
  and the allocator pool are given back, the chain-key copy is consumed, and the trace is unchanged;
* panic only if the model panics or the allocator reported a failure, with the trace extended.
  The memory is unconstrained, which is justified by `panic = "abort"` (a build-profile deviation
  from upstream's unwind default; DEV-M7);
* `x5` / `x6` (`remote_address_for_logging: &str`) are not read with logging off.

SepLogic is affine, so the spec does not state leak freedom.
-/
def consumeMessageKeySpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) (img : Obj.Image) :
    Spec ConsumeMessageKeyGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ckA ∧
          (s.readReg64 .x3).setWidth 32 = x.counter ∧
          (s.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s.readReg64 .x8 = x.ret⌝ ∗
        ratchetAt A x.self x.G x.st ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
        memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s.sp cmkStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜(x.model F).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : RatchetGhost,
          ⌜x.G.AgreeExcept G' (x.touched F)⌝ ∗ ratchetAt A x.self G' (x.model F).2) ∗
        consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model F).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

/-- The headline. For an image of `libsignalSessionImage`, the compiled
`consume_message_key` meets `consumeMessageKeySpec F A img` on the session program whose allocator hooks `alloc`
meet the contracts of `A`. Proved as `theorem consume_message_key_run (F A alloc img) :
ConsumeMessageKeyMeetsSpec F A alloc img`
(`LibsignalBinary/Proofs/ConsumeMessageKey/Assembly.lean`). -/
def ConsumeMessageKeyMeetsSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  AllocHooks A alloc → Obj.Loads libsignalSessionImage img →
    subroutine_ok (sessionProg img F alloc) (cmkEntry img) (consumeMessageKeySpec F A img)

/-- Non-vacuity of `consumeMessageKeySpec`. For every image of `libsignalSessionImage`, the following exist:
* allocator hooks that meet the contracts of some `A` and fail only when no unmapped block fits
  (`AllocSucceedsWithRoom`);
* a running, `sp`-aligned entry state that meets the precondition and has 1 MiB of unmapped,
  aligned, non-null room (far more than the call allocates);
* a model call that returns `Ok` with `counter > index + 1`. So the skipped-key store loop runs and stores
  at least two keys, into a `message_keys` buffer of capacity 0, and `grow_one` / `finish_grow`
  and the allocator run.

The room conjunct is what excludes the always-null allocator: at `s0` itself, the hook must return
non-null. This does not give "the call returns normally" with `ConsumeMessageKeyMeetsSpec`. `subroutine_ok`
does not expose the states at the inner hook calls. `onPanic`'s `allocFailedIn` disjunct is reachable
only through the allocator's null branch, which such hooks take only when no unmapped block fits. No
specification of a 64-bit allocator can exclude that. Proved as `cmkSpec_nonvacuous_ok`
(`Computational/Tests/NonVacuity/NonVac.lean`). -/
def ConsumeMessageKeySpecSatisfiable (F : ShaState → List (BitVec 8) → ShaState) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    ∃ (A : RustAlloc) (alloc : String → Option (State → State)),
      AllocHooks A alloc ∧ AllocSucceedsWithRoom A alloc ∧
      ∃ (x : ConsumeMessageKeyGhost) (s0 : State), s0.status = .Running ∧ s0.spAligned = true ∧
        (s0.mem ⊨ (consumeMessageKeySpec F A img).pre x s0) ∧
        (∃ p : BitVec 64, p ≠ 0 ∧ p.toNat % 8 = 0 ∧ Unmapped s0.mem p (2 ^ 20)) ∧
        x.counter.toNat > x.ck.index.toNat + 1 ∧
        (∃ i, x.st.findReceiverChainIndex x.their = some i ∧
          ∃ (h : i < x.G.chains.length), x.G.chains[i].mkCap = 0) ∧
        ∃ k, (x.model F).1 = .ok k

end CryptoVerification.LibsignalSession
