/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.ModelDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import ProofLib.VCGen

/-!
# Checkpoint PCs, Seam States, and Segment Contracts for `RatchetState::consume_message_key`

Decomposes `RatchetState::consume_message_key` (`cmkEntry img = img.base + 0xded8#64`, 649
instructions) into six segment contracts across internal checkpoint PCs:
- **Prologue & split** (`+0x000`): `ProloguePastSpec`, `PrologueTooFarSpec`, `PrologueAdvanceEntrySpec`.
- **Take path** (`+0x05c`): `TakePathSpec` (`counter < ck.index`).
- **Too-far path** (`+0x170`): `TooFarPathSpec` (`max_forward_jumps < counter - ck.index`).
- **Store loop** (`+0x334`): `StoreLoopIterSpec` and multi-step `StoreLoopSpec` (`storeLoop_of_iter`).
- **Advance epilogue** (`+0x4dc`): `AdvanceEpilogueSpec` (`ckc.index = counter`).
- **Panic paths** (`+0x334`, `+0x4dc`): `LoopNoChainPanicSpec` and `EpiloguePanicSpec`.

Proves `chainsOk_of_ratchetAt`, loop induction `storeLoop_of_iter`, and top-level composition
`cmk_of_seams`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

/-! ## Checkpoint PCs -/

/-- Take-path entry (`+0x05c`): `bl find_receiver_chain_index` when `counter < ck.index`. -/
abbrev cmkTakePC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x5c#64

/-- Too-far check entry (`+0x170`): `max_forward_jumps` comparison when `ck.index ≤ counter`. -/
abbrev cmkTooFarPC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x170#64

/-- Store-loop header (`+0x334`): `while chain_key.index < counter`. -/
abbrev cmkLoopPC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x334#64

/-- Post-loop epilogue entry (`+0x4dc`): `ckc.index = counter`. -/
abbrev cmkEpiloguePC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x4dc#64

/-- Shared register-restore return epilogue (`+0x77c .. +0x798`). -/
abbrev cmkRetEpiloguePC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x77c#64

/-- Cold panic block (`+0x974`): `expect_failed` in `store_skipped_key`. -/
abbrev cmkLoopNoChainPanicPC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x974#64

/-- Cold panic block (`+0x99c`): `expect_failed` in `set_receiver_chain_key`. -/
abbrev cmkEpilogueNoChainPanicPC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x99c#64

/-- Cold panic block (`+0x9b4`): `handle_error(1, 32)` on 32-byte allocation OOM. -/
abbrev cmkOom32PanicPC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x9b4#64

/-- Cold panic block (`+0x9c0`): `panic_const_add_overflow` when `counter = u32::MAX`. -/
abbrev cmkOverflowPanicPC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x9c0#64

/-- Cold panic block (`+0x9f4`): `handle_error(1, 36)` on 36-byte error-string allocation OOM. -/
abbrev cmkOom36PanicPC (img : Obj.Image) : BitVec 64 := cmkEntry img + 0x9f4#64

/-! ## Stack Frame Layout and Seam State Predicates -/

/-- Callee-saved register save area `[sp0 - 96#64 .. sp0]` (`[sp + 0x180 .. sp + 0x1e0]`, 96 bytes)
written by the prologue `+0x004 .. +0x018` and restored by `+0x77c .. +0x790`. -/
def cmkSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Local frame `[sp0 - 480#64 .. sp0 - 96#64]` (`[sp .. sp + 0x180]`, 384 bytes) during S3/S4/S5:
`[sp + 0x70] = sp0 - 368#64` holds `x.ret` (stored at `+0x328`, read at `+0x5c8`) and
`[sp + 0x7c] = sp0 - 356#64` holds `x.counter` (stored at `+0x03c`, read at `+0x4a8`).
The 256-byte region `[sp0 - 352#64 .. sp0 - 96#64]` covers the 1-byte/32-byte scratch at
`sp + 0xa0 = sp0 - 320#64` and the 32-byte `hmac_sha256` output buffer at `x27 = sp + 0x100 = sp0 - 224#64`. -/
def cmkLoopFrame (sp0 ret : BitVec 64) (counter : BitVec 32) : SepProp :=
  memRegion (sp0 - 480#64) 112 ∗
  ((sp0 - 368#64) ↦₆₄ ret) ∗
  memRegion (sp0 - 360#64) 4 ∗
  ((sp0 - 356#64) ↦₃₂ counter) ∗
  memRegion (sp0 - 352#64) 256

/-- Common machine metadata invariant at every internal checkpoint after the prologue:
`s` is `.Running` with `sp = s0.sp - 480#64` (16-byte aligned), `x29 = s0.sp - 96#64`,
`trace` unchanged from `s0`, and the image's frozen sections and symbol table preserved. -/
def cmkMidMeta (img : Obj.Image) (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 480#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  s.trace = s0.trace ∧
  img.FrozenLoaded s ∧
  s.symtab = img.symtab ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

def CmkTakeRegs (x : ConsumeMessageKeyGhost) (s0 s : State) : Prop :=
  s.readReg64 .x0 = x.G.chainsPtr ∧
  s.readReg64 .x1 = BitVec.ofNat 64 x.st.receiverChains.length ∧
  s.readReg64 .x2 = x.theirA ∧
  s.readReg64 .x20 = x.counter.zeroExtend 64 ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.st.receiverChains.length ∧
  s.readReg64 .x22 = x.ret ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x24 = x.G.chainsPtr ∧
  s.readReg64 .x26 = x.theirA ∧
  s.readReg64 .x27 = s0.sp - 224#64 ∧
  s.readReg64 .x28 = x.ck.index.zeroExtend 64

def cmkPreLoopHeap (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  ratchetAt A x.self x.G x.st ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  memRegion (s0.sp - 480#64) 384 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

def cmkPreLoopHeapAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  ratchetAt A x.self x.G x.st ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  memRegion (s0.sp - 480#64) 384 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

def CmkTakeState (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = cmkTakePC img ∧
  cmkMidMeta img s0 s ∧
  CmkTakeRegs x s0 s ∧
  (s.mem ⊨ cmkPreLoopHeap A img x s0 ∗ R)

/-- Live registers at `cmkTooFarPC img` (`+0x170`, S2 entry, `ck.index ≤ counter`).
`x9 = jump` is set by `subs w9, w3, w28` (`+0x38`); `msgType` is still in `x4` (copied to `w19` at
`+0x188` on the too-far path); `ckA` is still in `x2` (`mov x21, x2` only at `+0x278`). -/
def CmkTooFarRegs (x : ConsumeMessageKeyGhost) (s0 s : State) : Prop :=
  s.readReg64 .x2 = x.ckA ∧
  (s.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧
  s.readReg64 .x9 = (x.counter - x.ck.index).zeroExtend 64 ∧
  s.readReg64 .x20 = x.counter.zeroExtend 64 ∧
  s.readReg64 .x22 = x.ret ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x26 = x.theirA ∧
  s.readReg64 .x27 = s0.sp - 224#64 ∧
  s.readReg64 .x28 = x.ck.index.zeroExtend 64

def CmkTooFarState (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = cmkTooFarPC img ∧
  cmkMidMeta img s0 s ∧
  CmkTooFarRegs x s0 s ∧
  (s.mem ⊨ cmkPreLoopHeap A img x s0 ∗ R)

/-- Live registers at `cmkLoopPC img` (`+0x334`, S3/S5) and `cmkEpiloguePC img` (`+0x4dc`, S4/S5)
for current chain key `ckc`. (`x19 = 1#64` is required only at `+0x334`: see `CmkLoopState`.) -/
def CmkLoopRegs (x : ConsumeMessageKeyGhost) (ckc : ChainKey) (s0 s : State) : Prop :=
  s.readReg64 .x21 = x.ckA ∧
  s.readReg64 .x23 = x.self ∧
  s.readReg64 .x26 = x.theirA ∧
  s.readReg64 .x27 = s0.sp - 224#64 ∧
  s.readReg64 .x28 = ckc.index.zeroExtend 64

def cmkLoopHeap (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State) : SepProp :=
  ratchetAt A x.self Gc stc ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

def cmkLoopHeapAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State) : SepProp :=
  ratchetAt A x.self Gc stc ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

/-- Full state at `pc` (`cmkLoopPC img` or `cmkEpiloguePC img`) with `(Gc, stc, ckc)`.
At the loop header, `x19 = 1` (set by `mov w19, #1` at `+0x330`, kept across iterations; it is the
dangling pointer of the empty `cipher`/`mac`/`iv` `Vec`s and the `0x01` HMAC byte). The direct
`b.hs 0x4dc` at `+0x32c` skips `+0x330`, so nothing is assumed about `x19` at the epilogue
(which sets `w19 = 1` itself at `+0x594`). -/
def CmkLoopState (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (R : SepProp)
    (pc : BitVec 64) (s0 s : State) : Prop :=
  s.pc = pc ∧
  cmkMidMeta img s0 s ∧
  CmkLoopRegs x ckc s0 s ∧
  (pc = cmkLoopPC img → s.readReg64 .x19 = 1#64) ∧
  (s.mem ⊨ cmkLoopHeap A img x Gc stc ckc s0 ∗ R)

/-! ## Segment Contracts -/

/-- Prologue contract for `x.counter < x.ck.index` (`+0x000 → +0x05c`). -/
def ProloguePastSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
      s0.pc = cmkEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (consumeMessageKeySpec F A img).pre x s0 ∗ R) →
      x.counter < x.ck.index →
      reaches_pc (sessionProg img F alloc) (cmkTakePC img) s0
        (CmkTakeState A img x R s0)

/-- Prologue contract for `x.ck.index ≤ x.counter` (`+0x000 → +0x170`). -/
def PrologueTooFarSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
      s0.pc = cmkEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (consumeMessageKeySpec F A img).pre x s0 ∗ R) →
      x.ck.index ≤ x.counter →
      reaches_pc (sessionProg img F alloc) (cmkTooFarPC img) s0
        (CmkTooFarState A img x R s0)

/-- Prologue contract for `x.ck.index ≤ x.counter` within `maxForwardJumps` (`+0x000 → +0x334` or
`+0x4dc`). -/
def PrologueAdvanceEntrySpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
      s0.pc = cmkEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (consumeMessageKeySpec F A img).pre x s0 ∗ R) →
      x.ck.index ≤ x.counter →
      (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps →
      let targetPC := if x.ck.index < x.counter then cmkLoopPC img else cmkEpiloguePC img
      reaches_pc (sessionProg img F alloc) targetPC s0
        (CmkLoopState A img x x.G x.st x.ck R targetPC s0)

/-- Take-path contract (`+0x05c → +0x798`): removes and returns a matching stored key or writes
`DuplicatedMessage(ck.index, counter)`. -/
def TakePathSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  AllocHooks A alloc → Obj.Loads libsignalSessionImage img → FindIndexOk img F alloc A →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.counter < x.ck.index →
      CmkTakeState A img x R s0 s →
      reaches_outcome (sessionProg img F alloc) (consumeMessageKeySpec F A img) x R s0 s

/-- Too-far contract (`+0x170 → +0x798 / +0x9f4`): allocates the 36-byte error string and writes
`InvalidMessage`, or panics on OOM. -/
def TooFarPathSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  AllocHooks A alloc → Obj.Loads libsignalSessionImage img →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index ≤ x.counter →
      x.st.maxForwardJumps < (x.counter - x.ck.index).toNat →
      CmkTooFarState A img x R s0 s →
      reaches_outcome (sessionProg img F alloc) (consumeMessageKeySpec F A img) x R s0 s

/-- Single-iteration store-loop contract (`+0x334 → +0x334 / +0x4dc` or OOM panic): prepends
`ckc.messageKeys F` to chain `ci` (evicting index 2000 if full) and steps `ckc` to `chainStepN F 1 ckc`. -/
def StoreLoopIterSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  AllocHooks A alloc → Obj.Loads libsignalSessionImage img →
    FindIndexOk img F alloc A → HmacOk img F alloc → GrowOneOk img F alloc A →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState A img x Gc stc ckc R (cmkLoopPC img) s0 s →
      (sessionProg img F alloc).CodeLoaded s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC img else cmkEpiloguePC img
      ∃ s', Steps (sessionProg img F alloc) s s' ∧
        ((∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState A img x G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 s' ∗ R)))

/-- Multi-iteration store-loop contract (`+0x334 → +0x4dc` or OOM panic) across all
`n = (x.counter - ckc.index).toNat` skipped keys. -/
def StoreLoopSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  AllocHooks A alloc → Obj.Loads libsignalSessionImage img →
    FindIndexOk img F alloc A → HmacOk img F alloc → GrowOneOk img F alloc A →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState A img x Gc stc ckc R (cmkLoopPC img) s0 s →
      (sessionProg img F alloc).CodeLoaded s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps (sessionProg img F alloc) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState A img x G' st_end ck_end R (cmkEpiloguePC img) s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 s' ∗ R)))

/-- Epilogue contract (`+0x4dc → +0x798 / +0x9b4`): updates chain `ci`'s key to `chainStepN F 1 ckc`,
writes `.ok (ckc.messageKeys F)` to `x.ret`, and returns (or panics on OOM). -/
def AdvanceEpilogueSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  AllocHooks A alloc → Obj.Loads libsignalSessionImage img →
    FindIndexOk img F alloc A → HmacOk img F alloc →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      x.counter ≠ BitVec.allOnes 32 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      x.G.AgreeExcept Gc (some ci) →
      (x.model F).1 = .ok (ckc.messageKeys F) →
      (x.model F).2 =
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with chainKey := some (chainStepN F 1 ckc) } } →
      x.touched F = some ci →
      CmkLoopState A img x Gc stc ckc R (cmkEpiloguePC img) s0 s →
      reaches_outcome (sessionProg img F alloc) (consumeMessageKeySpec F A img) x R s0 s

/-- Store-loop missing-chain panic contract (`+0x334 → +0x974 / +0x9b4`). -/
def LoopNoChainPanicSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  AllocHooks A alloc → Obj.Loads libsignalSessionImage img →
    FindIndexOk img F alloc A → HmacOk img F alloc →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index < x.counter →
      x.st.findReceiverChainIndex x.their = none →
      (x.model F).1 = .error .panic →
      CmkLoopState A img x x.G x.st x.ck R (cmkLoopPC img) s0 s →
      reaches_outcome (sessionProg img F alloc) (consumeMessageKeySpec F A img) x R s0 s

/-- Epilogue `u32::MAX` overflow and missing-chain panic contract (`+0x4dc → +0x9c0 / +0x99c`). -/
def EpiloguePanicSpec (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    FindIndexOk img F alloc A → HmacOk img F alloc →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      (x.counter = BitVec.allOnes 32 ∨ stc.findReceiverChainIndex x.their = none) →
      (x.model F).1 = .error .panic →
      CmkLoopState A img x Gc stc ckc R (cmkEpiloguePC img) s0 s →
      reaches_outcome (sessionProg img F alloc) (consumeMessageKeySpec F A img) x R s0 s

/-! ## `ChainsOk` and `.rodata` Helpers -/

theorem forall_of_arrayAt {α : Type} {elem : α → BitVec 64 → SepProp} {stride : Nat}
    {P : α → Prop} (helem : ∀ x a R m, (m ⊨ elem x a ∗ R) → P x) :
    ∀ (xs : List α) (base : BitVec 64) (R : SepProp) (m : Memory),
      (m ⊨ arrayAt elem stride base xs ∗ R) → ∀ x ∈ xs, P x
  | [], _, _, _, _, _, hx => by cases hx
  | x :: xs, base, R, m, hm, y, hy => by
    simp only [arrayAt, sepConj_assoc] at hm
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact helem y base _ m hm
    · rw [sepConj_left_comm] at hm
      exact forall_of_arrayAt helem xs (base + BitVec.ofNat 64 stride) (elem x base ∗ R) m hm y hy'

theorem forall_of_vecAt {α : Type} {A : RustAlloc} {stride align : Nat}
    {elem : α → BitVec 64 → SepProp} {P : α → Prop}
    (helem : ∀ x a R m, (m ⊨ elem x a ∗ R) → P x)
    {v cap ptr : BitVec 64} {xs : List α} {R : SepProp} {m : Memory}
    (h : m ⊨ vecAt A stride align elem v cap ptr xs ∗ R) :
    ∀ x ∈ xs, P x := by
  unfold vecAt vecBuf at h
  have h' : m ⊨ ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
       (if cap = 0 then emp
        else A.live ptr (cap.toNat * stride) align ∗ arrayAt elem stride ptr xs ∗
          memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride)) ∗ R) :=
    Satisfies.of_eq h
  rw [satisfies_pure_sepConj] at h'
  rcases h' with ⟨⟨hlen, _, _⟩, h'⟩
  by_cases hcap : cap = 0
  · subst hcap
    have h0 : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst h0
    intro _ hx; cases hx
  · simp only [hcap, ↓reduceIte] at h'
    have harr : m ⊨ arrayAt elem stride ptr xs ∗
        (vecHeader v cap ptr (BitVec.ofNat 64 xs.length) ∗
         A.live ptr (cap.toNat * stride) align ∗
         memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride) ∗ R) :=
      Satisfies.of_eq h'
    exact forall_of_arrayAt helem xs ptr _ m harr

/-- Every state satisfying `ratchetAt A self G st ∗ R` satisfies `ChainsOk st`. -/
theorem chainsOk_of_ratchetAt {A : RustAlloc} {self : BitVec 64} {G : RatchetGhost}
    {st : RatchetState} {R : SepProp} {m : Memory}
    (h : m ⊨ ratchetAt A self G st ∗ R) : ChainsOk st := by
  unfold ratchetAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hlen, _, _⟩, hvec⟩
  have hvec' : m ⊨ vecAt A 104 8 (chainAt A) self G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
      (((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
       ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
       ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4 ∗ R) :=
    Satisfies.of_eq hvec
  have hchains := forall_of_vecAt (P := fun gc : ChainGhost × ReceiverChain =>
      gc.2.messageKeys.length ≤ maxMessageKeys ∧ ∀ k ∈ gc.2.messageKeys, k.seed ≠ [])
    (fun gc a R' m' hc => by
      unfold chainAt at hc
      rw [sepConj_assoc, satisfies_pure_sepConj] at hc
      rcases hc with ⟨⟨_, hmk_le, hkeys_len, _, _⟩, hc_rest⟩
      refine ⟨hmk_le, ?_⟩
      have hmk_vec : m' ⊨ vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (gc.1.keys.zip gc.2.messageKeys) ∗
          (vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
           optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗ R') :=
        Satisfies.of_eq hc_rest
      have hkeys := forall_of_vecAt (P := fun gk : MessageKeyGhost × MessageKeyGenerator => gk.2.seed ≠ [])
        (fun gk b R'' m'' hk => by
          unfold messageKeyAt at hk
          rw [sepConj_assoc, satisfies_pure_sepConj] at hk
          exact hk.1)
        hmk_vec
      intro k hk
      rw [List.mem_iff_getElem] at hk
      rcases hk with ⟨i, hi, rfl⟩
      have hi' : i < gc.1.keys.length := hkeys_len.symm ▸ hi
      exact hkeys (gc.1.keys[i], gc.2.messageKeys[i])
        (by
          rw [List.mem_iff_getElem]
          refine ⟨i, by simp [hi, hi'], by simp⟩))
    hvec'
  intro c hc
  rw [List.mem_iff_getElem] at hc
  rcases hc with ⟨i, hi, rfl⟩
  have hi' : i < G.chains.length := hlen.symm ▸ hi
  exact hchains (G.chains[i], st.receiverChains[i])
    (by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [hi, hi'], by simp⟩)

theorem map_snd_zip_chains {G : RatchetGhost} {st : RatchetState}
    (h : G.chains.length = st.receiverChains.length) :
    (G.chains.zip st.receiverChains).map (·.2) = st.receiverChains := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp

/-! ## Store-Loop Induction -/

private theorem take_append_take_of_le {α : Type} :
    ∀ (xs ys : List α) {m k : Nat}, m ≤ k →
      (xs ++ ys.take k).take m = (xs ++ ys).take m
  | [], ys, m, k, hmk => by simp [List.take_take, Nat.min_eq_left hmk]
  | x :: xs, ys, 0, k, _ => rfl
  | x :: xs, ys, m + 1, k, hmk => by
    simp only [List.cons_append, List.take_succ_cons]
    exact congrArg (x :: ·) (take_append_take_of_le xs ys (Nat.le_of_succ_le hmk))

private theorem take_append_take_eq {α : Type} (xs ys : List α) (m : Nat) :
    (xs ++ ys.take m).take m = (xs ++ ys).take m :=
  take_append_take_of_le xs ys (Nat.le_refl m)

private theorem set_set_same {α : Type} (xs : List α) (i : Nat) (a b : α) :
    (xs.set i a).set i b = xs.set i b := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.set, ih]

private theorem getElem?_set_self {α : Type} {xs : List α} {i : Nat} (hi : i < xs.length) (a : α) :
    (xs.set i a)[i]? = some a := by
  rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_set_self]

private theorem storeLoop_loop_ind (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image)
    (hiter : StoreLoopIterSpec F A alloc img)
    (hA : AllocHooks A alloc) (himg : Obj.Loads libsignalSessionImage img)
    (hfind : FindIndexOk img F alloc A) (hhmac : HmacOk img F alloc) (hgrow : GrowOneOk img F alloc A)
    (x : ConsumeMessageKeyGhost) (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter →
      (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState A img x Gc stc ckc R (cmkLoopPC img) s0 s →
      (sessionProg img F alloc).CodeLoaded s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps (sessionProg img F alloc) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState A img x G' st_end ck_end R (cmkEpiloguePC img) s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 s' ∗ R)))
  | 0, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq
      change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC img else cmkEpiloguePC img) =
        cmkEpiloguePC img := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨G', hG', hst'⟩ | hpan⟩ :=
      hiter hA himg hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst'
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, G', hG', ?_⟩⟩
      simpa [chainStepN, skippedKeys] using hst'
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by
      rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC img else cmkEpiloguePC img) =
        cmkLoopPC img := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨G1, hG1, hst1⟩ | hpan1⟩ :=
      hiter hA himg hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]
        exact hci
      obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | hpan2⟩ :=
        storeLoop_loop_ind F A alloc img hiter hA himg hfind hhmac hgrow x ci R s0
          k G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1 (hsteps1.codeLoaded hL)
      · refine ⟨s2, hsteps1.trans hsteps2, Or.inl ⟨hck_end, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]
          rw [set_set_same]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (Ratchet.chainHmac F ckc.key Ratchet.chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq]
            simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

/-- Lift `StoreLoopIterSpec` across `n = (x.counter - ckc.index).toNat` iterations to `StoreLoopSpec`. -/
theorem storeLoop_of_iter {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {alloc : String → Option (State → State)} {img : Obj.Image}
    (hiter : StoreLoopIterSpec F A alloc img) : StoreLoopSpec F A alloc img := by
  intro hA himg hfind hhmac hgrow x Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 := ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only
  rw [hk]
  exact storeLoop_loop_ind F A alloc img hiter hA himg hfind hhmac hgrow x ci R s0
    k Gc stc ckc chc s hlt hk hci hchc hstate hL

/-! ## Top-Level Seam Composition -/

theorem findReceiverChainIndex_some_getElem? {st : RatchetState} {their : PublicKey}
    {ci : Nat} (h : st.findReceiverChainIndex their = some ci) :
    ∃ ch, st.receiverChains[ci]? = some ch := by
  unfold RatchetState.findReceiverChainIndex at h
  have hlt : ci < st.receiverChains.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
  exact ⟨st.receiverChains[ci], List.getElem?_eq_getElem hlt⟩

abbrev reaches_outcome_steps := @Arm64.reaches_outcome_steps

/-- Compose all six segment contracts into `ConsumeMessageKeyMeetsSpec`. -/
theorem cmk_of_seams {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {alloc : String → Option (State → State)} {img : Obj.Image}
    (hfind : FindIndexOk img F alloc A)
    (hhmac : HmacOk img F alloc)
    (hgrow : GrowOneOk img F alloc A)
    (hs0_past : ProloguePastSpec F A alloc img)
    (hs0_tooFar : PrologueTooFarSpec F A alloc img)
    (hs0_adv : PrologueAdvanceEntrySpec F A alloc img)
    (hs1 : TakePathSpec F A alloc img)
    (hs2 : TooFarPathSpec F A alloc img)
    (hs3_iter : StoreLoopIterSpec F A alloc img)
    (hs4 : AdvanceEpilogueSpec F A alloc img)
    (hs5_loop : LoopNoChainPanicSpec F A alloc img)
    (hs5_ep : EpiloguePanicSpec F A alloc img) :
    ConsumeMessageKeyMeetsSpec F A alloc img := by
  intro hA himg
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have hratchet : s0.mem ⊨ ratchetAt A x.self x.G x.st ∗
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
       ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.theirA ∧ s0.readReg64 .x2 = x.ckA ∧
         (s0.readReg64 .x3).setWidth 32 = x.counter ∧
         (s0.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s0.readReg64 .x8 = x.ret⌝ ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStack ∗ A.pool ∗ R) := by
    simp only [consumeMessageKeySpec, Spec.inImage] at hpre
    exact Satisfies.of_eq hpre
  have hok : ChainsOk x.st := chainsOk_of_ratchetAt hratchet
  by_cases hlt : x.counter < x.ck.index
  · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
      hs0_past himg x R s0 hpc hrun hsp hpre hlt hL
    exact reaches_outcome_steps hsteps1 (hs1 hA himg hfind x R s0 s1 hlt hst1)
  · have hle : x.ck.index ≤ x.counter := BitVec.not_lt.mp hlt
    by_cases hj : (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps
    · obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
        hs0_adv himg x R s0 hpc hrun hsp hpre hle hj hL
      have hL1 := hsteps1.codeLoaded hL
      by_cases hck_lt : x.ck.index < x.counter
      · simp only [hck_lt, ↓reduceIte] at hst1
        cases hci : x.st.findReceiverChainIndex x.their with
        | none =>
          have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, Or.inr hci⟩
          exact reaches_outcome_steps hsteps1
            (hs5_loop hA himg hfind hhmac x R s0 s1 hck_lt hci hpan_model hst1)
        | some ci =>
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨s2, hsteps2, ⟨hck_end, G2, hG2, hst2⟩ | ⟨hpan2, hq2⟩⟩ :=
            storeLoop_of_iter hs3_iter hA himg hfind hhmac hgrow x x.G x.st x.ck ci ch R s0 s1
              hck_lt hci hch hst1 hL1
          · refine reaches_outcome_steps (hsteps1.trans hsteps2) ?_
            let n := (x.counter - x.ck.index).toNat
            let ckc := chainStepN F n x.ck
            let chc : ReceiverChain :=
              { ch with messageKeys := (skippedKeys F n x.ck ++ ch.messageKeys).take maxMessageKeys }
            let stc : RatchetState := { x.st with receiverChains := x.st.receiverChains.set ci chc }
            by_cases hc_max : x.counter = BitVec.allOnes 32
            · have hpan_model : (x.model F).1 = .error .panic :=
                (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
                  ⟨hle, hj, Or.inl hc_max⟩
              exact hs5_ep himg hfind hhmac x G2 stc ckc R s0 s2 hck_end (Or.inl hc_max) hpan_model hst2
            · obtain ⟨ch', hch', hmodel⟩ :=
                consumeMessageKey_advance F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
              rw [hch] at hch'; cases hch'
              have hci_lt : ci < x.st.receiverChains.length := (List.getElem?_eq_some_iff.mp hch).1
              have hchc_get : stc.receiverChains[ci]? = some chc := getElem?_set_self hci_lt chc
              have hci_stc : stc.findReceiverChainIndex x.their = some ci := by
                rw [findReceiverChainIndex_set x.st x.their ci chc ⟨ch, hch, rfl⟩]
                exact hci
              have hm1 : (x.model F).1 = .ok (ckc.messageKeys F) := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
              have hm2 : (x.model F).2 =
                  { stc with
                    receiverChains := stc.receiverChains.set ci
                      { chc with chainKey := some (chainStepN F 1 ckc) } } := by
                unfold ConsumeMessageKeyGhost.model; rw [hmodel]
                dsimp only [stc, chc]
                rw [set_set_same]
              have htouch : x.touched F = some ci := by
                unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
              exact hs4 hA himg hfind hhmac x G2 stc ckc ci chc R s0 s2
                hck_end hc_max hci_stc hchc_get hG2 hm1 hm2 htouch hst2
          · exact reaches_outcome_steps (hsteps1.trans hsteps2) (reaches_outcome_refl_panic hpan2 hq2)
      · simp only [hck_lt, ↓reduceIte] at hst1
        have hck_eq : x.ck.index = x.counter :=
          BitVec.le_antisymm hle (BitVec.not_lt.mp hck_lt)
        by_cases hpan_cond : x.counter = BitVec.allOnes 32 ∨ x.st.findReceiverChainIndex x.their = none
        · have hpan_model : (x.model F).1 = .error .panic :=
            (consumeMessageKey_panic_iff F x.st x.their x.ck x.counter x.msgType).mpr
              ⟨hle, hj, hpan_cond⟩
          exact reaches_outcome_steps hsteps1
            (hs5_ep himg hfind hhmac x x.G x.st x.ck R s0 s1 hck_eq hpan_cond hpan_model hst1)
        · rw [not_or] at hpan_cond
          rcases hpan_cond with ⟨hc_max, hci_ne⟩
          obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp hci_ne
          obtain ⟨ch, hch⟩ := findReceiverChainIndex_some_getElem? hci
          obtain ⟨ch', hch', hmodel⟩ :=
            consumeMessageKey_advance F x.st x.their x.ck x.counter x.msgType hc_max hle hj ci hci hok
          rw [hch] at hch'; cases hch'
          have hn0 : (x.counter - x.ck.index).toNat = 0 := by rw [hck_eq, BitVec.sub_self]; rfl
          have htake : ch.messageKeys.take maxMessageKeys = ch.messageKeys :=
            List.take_of_length_le (hok ch (List.mem_of_getElem? hch)).1
          have hm1 : (x.model F).1 = .ok (x.ck.messageKeys F) := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]; simp [hn0, chainStepN]
          have hm2 : (x.model F).2 =
              { x.st with
                receiverChains := x.st.receiverChains.set ci
                  { ch with chainKey := some (chainStepN F 1 x.ck) } } := by
            unfold ConsumeMessageKeyGhost.model; rw [hmodel]
            simp [hn0, chainStepN, skippedKeys, htake]
          have htouch : x.touched F = some ci := by
            unfold ConsumeMessageKeyGhost.touched; rw [hm1, hci]
          exact reaches_outcome_steps hsteps1
            (hs4 hA himg hfind hhmac x x.G x.st x.ck ci ch R s0 s1
              hck_eq hc_max hci hch (RatchetGhost.AgreeExcept.refl x.G (some ci))
              hm1 hm2 htouch hst1)
    · have hj_gt : x.st.maxForwardJumps < (x.counter - x.ck.index).toNat := Nat.lt_of_not_ge hj
      obtain ⟨s1, hsteps1, ⟨_, _, hst1⟩ | ⟨_, ⟨⟩⟩⟩ :=
        hs0_tooFar himg x R s0 hpc hrun hsp hpre hle hL
      exact reaches_outcome_steps hsteps1 (hs2 hA himg x R s0 s1 hle hj_gt hst1)

end CryptoVerification.LibsignalSession
