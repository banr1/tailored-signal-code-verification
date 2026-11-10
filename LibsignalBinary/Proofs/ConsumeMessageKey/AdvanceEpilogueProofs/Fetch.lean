/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.ConsumeCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.Seams
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock

@[expose] public section

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace CryptoVerification.LibsignalSession.AdvanceEpilogue

open Arm64 ProofLib ProofLib.ProgramReflection Lean Meta Elab Command

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1244) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1504), (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1916) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1944),
    (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 2484) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 2492)]

/-- Introduce instruction-fetch hypotheses for `count` instructions from relative offset `relStart`. -/
elab "advanceEpilogue_fetches " b:term:max H:term:max hfn:term:max relStart:num count:num : tactic => do
  let r0 := relStart.getNat
  let n := count.getNat
  let fnOff := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  let fetchAdd := mkIdent ``CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:n] do
    let k := r0 + 4 * i
    let off := fnOff + k
    let hexStr := String.ofList (Nat.toDigits 16 off)
    let dec := mkIdent (Name.str `CryptoVerification.LibsignalSession.AdvanceEpilogue ("libsignalSessionBin_decode_0x" ++ hexStr))
    let kq := Syntax.mkNumLit (toString k)
    Tactic.evalTactic (← `(tactic|
      have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end CryptoVerification.LibsignalSession.AdvanceEpilogue

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

/-! ## Relocatable Checkpoint PCs, States, and Segment Contracts (Block 24) -/

abbrev cmkRustAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev cmkRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

abbrev cmkRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev cmkHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

abbrev cmkExpectFailedSym : String :=
  "_RNvNtCskxtBwYRO61I_4core6option13expect_failed"

abbrev cmkPanicAddOverflowSym : String :=
  "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow"

abbrev cmkBlackBoxU8Sym : String :=
  "subtle::black_box::<u8>"

def cmkShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

def CmkAllocHooks (A : RustAlloc) (H : String → Option (State → State)) : Prop :=
  HookSat H cmkRustAllocSym (rustAllocSpec A) ∧
  HookSat H cmkRustDeallocSym (rustDeallocSpec A) ∧
  HookSat H cmkRustNoAllocShimSym cmkShimSpec ∧
  H cmkHandleErrorSym = some Rust.panicked ∧
  H cmkExpectFailedSym = some Rust.panicked ∧
  H cmkPanicAddOverflowSym = some Rust.panicked

theorem cmk_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (k := k) (by simp [hk, hget]) hi hunmut

theorem cmk_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by simp [hk, hget]) hsat hi hunmut

abbrev cmkEntry_placed [LibsignalPlacement] : BitVec 64 := (blkPl_24).base
abbrev cmkTakePC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x5c#64
abbrev cmkTooFarPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x170#64
abbrev cmkLoopPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x334#64
abbrev cmkEpiloguePC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x4dc#64
abbrev cmkRetEpiloguePC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x77c#64
abbrev cmkLoopNoChainPanicPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x974#64
abbrev cmkEpilogueNoChainPanicPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x99c#64
abbrev cmkOom32PanicPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x9b4#64
abbrev cmkOverflowPanicPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x9c0#64
abbrev cmkOom36PanicPC_placed [LibsignalPlacement] : BitVec 64 := cmkEntry_placed + 0x9f4#64

def cmkMidMeta_placed [LibsignalPlacement] (s0 s : State) : Prop :=
  s.status = .Running ∧
  s.sp = s0.sp - 480#64 ∧
  s0.spAligned = true ∧
  s.spAligned = true ∧
  s.readReg64 .x29 = s0.sp - 96#64 ∧
  s.trace = s0.trace ∧
  LibsignalCodeLoaded lsmpl s.mem ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

def cmkDummyImg [LibsignalPlacement] : Obj.Image :=
  { (default : Obj.Image) with base := lsLogFilterAddr - logFilterAddr { (default : Obj.Image) with base := 0 } }

@[simp, arm64_norm, wp_norm]
theorem logFilterAddr_cmkDummyImg [LibsignalPlacement] :
    logFilterAddr cmkDummyImg = lsLogFilterAddr := by
  simp only [cmkDummyImg, logFilterAddr]
  bv_omega

def cmkPreLoopHeap_placed [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  ratchetAt A x.self x.G x.st ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  memRegion x.ret 88 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  memRegion (s0.sp - 480#64) 384 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

theorem cmkPreLoopHeap_placed_eq [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost) (s0 : State) :
    cmkPreLoopHeap_placed A x s0 = cmkPreLoopHeap A cmkDummyImg x s0 := by
  unfold cmkPreLoopHeap_placed cmkPreLoopHeap
  rw [logFilterAddr_cmkDummyImg]

theorem cmkPreLoopHeap_placed_eq_at [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost) (s0 : State) :
    cmkPreLoopHeap_placed A x s0 = cmkPreLoopHeapAt A lsLogFilterAddr x s0 :=
  rfl

def CmkTakeState_placed [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = cmkTakePC_placed ∧
  cmkMidMeta_placed s0 s ∧
  CmkTakeRegs x s0 s ∧
  (s.mem ⊨ cmkPreLoopHeap_placed A x s0 ∗ R)

def CmkTooFarState_placed [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = cmkTooFarPC_placed ∧
  cmkMidMeta_placed s0 s ∧
  CmkTooFarRegs x s0 s ∧
  (s.mem ⊨ cmkPreLoopHeap_placed A x s0 ∗ R)

def cmkLoopHeap_placed [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State) : SepProp :=
  ratchetAt A x.self Gc stc ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 7712 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

theorem cmkLoopHeap_placed_eq [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State) :
    cmkLoopHeap_placed A x Gc stc ckc s0 = cmkLoopHeap A cmkDummyImg x Gc stc ckc s0 := by
  unfold cmkLoopHeap_placed cmkLoopHeap
  rw [logFilterAddr_cmkDummyImg]

theorem cmkLoopHeap_placed_eq_at [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (s0 : State) :
    cmkLoopHeap_placed A x Gc stc ckc s0 = cmkLoopHeapAt A lsLogFilterAddr x Gc stc ckc s0 :=
  rfl

def CmkLoopState_placed [LibsignalPlacement] (A : RustAlloc) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey) (R : SepProp)
    (pc : BitVec 64) (s0 s : State) : Prop :=
  s.pc = pc ∧
  cmkMidMeta_placed s0 s ∧
  CmkLoopRegs x ckc s0 s ∧
  (pc = cmkLoopPC_placed → s.readReg64 .x19 = 1#64) ∧
  (s.mem ⊨ cmkLoopHeap_placed A x Gc stc ckc s0 ∗ R)

def findIndexPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec FindIndexGhost where
  pre := fun (p, cs, theirA, their) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = cs.length ∧ s.readReg64 .x2 = theirA ∧
      cs.length * 104 < 2 ^ 63⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp 1024
  post := fun (p, cs, theirA, their) s0 sf =>
    ⌜sf.trace = s0.trace ∧
      match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
      | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
      | none => sf.readReg64 .x0 = 0#64⌝ ∗
    arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp 1024

def FindIndexPlacedOk [LibsignalPlacement] (H : String → Option (State → State)) (A : RustAlloc) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
    (withLsCodeLoaded lsmpl (findIndexPlacedSpec A))

def HmacPlacedOk [LibsignalPlacement] (H : String → Option (State → State))
    (F : ShaState → List (BitVec 8) → ShaState) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73)
    (withLsCodeLoaded lsmpl (hmacSpec F))

def HmacPlacedRoOk [LibsignalPlacement] (H : String → Option (State → State))
    (F : ShaState → List (BitVec 8) → ShaState) : Prop :=
  subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73)
    (withLsCodeLoaded lsmpl
      { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ })

def cmkPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc) :
    Spec ConsumeMessageKeyGhost :=
  withLsCodeLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x2 = x.ckA ∧
          (s.readReg64 .x3).setWidth 32 = x.counter ∧
          (s.readReg64 .x4).setWidth 8 = msgTypeByte x.msgType ∧ s.readReg64 .x8 = x.ret⌝ ∗
        ratchetAt A x.self x.G x.st ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
        memRegion x.ret 88 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp cmkStack ∗ A.pool
      post := fun x s0 sf =>
        ⌜(x.model F).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
        (∃∗ G' : RatchetGhost,
          ⌜x.G.AgreeExcept G' (x.touched F)⌝ ∗ ratchetAt A x.self G' (x.model F).2) ∗
        consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp cmkStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜((x.model F).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def ProloguePastPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
    s0.pc = cmkEntry_placed → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cmkPlacedSpec F A).pre x s0 ∗ R) →
    x.counter < x.ck.index →
    reaches_pc ((blkPC_24).rebase (blkPl_24).base H) cmkTakePC_placed s0
      (CmkTakeState_placed A x R s0)

def PrologueTooFarPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
    s0.pc = cmkEntry_placed → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cmkPlacedSpec F A).pre x s0 ∗ R) →
    x.ck.index ≤ x.counter →
    reaches_pc ((blkPC_24).rebase (blkPl_24).base H) cmkTooFarPC_placed s0
      (CmkTooFarState_placed A x R s0)

def PrologueAdvanceEntryPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State),
    s0.pc = cmkEntry_placed → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cmkPlacedSpec F A).pre x s0 ∗ R) →
    x.ck.index ≤ x.counter →
    (x.counter - x.ck.index).toNat ≤ x.st.maxForwardJumps →
    let targetPC := if x.ck.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    reaches_pc ((blkPC_24).rebase (blkPl_24).base H) targetPC s0
      (CmkLoopState_placed A x x.G x.st x.ck R targetPC s0)

def AdvanceEpiloguePlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H → FindIndexPlacedOk H A → HmacPlacedOk H F →
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
      CmkLoopState_placed A x Gc stc ckc R cmkEpiloguePC_placed s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

def LoopNoChainPanicPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H → FindIndexPlacedOk H A → HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index < x.counter →
      x.st.findReceiverChainIndex x.their = none →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A x x.G x.st x.ck R cmkLoopPC_placed s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

def EpiloguePanicPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  H cmkExpectFailedSym = some Rust.panicked →
    H cmkPanicAddOverflowSym = some Rust.panicked →
    FindIndexPlacedOk H A → HmacPlacedOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      (x.counter = BitVec.allOnes 32 ∨ stc.findReceiverChainIndex x.their = none) →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A x Gc stc ckc R cmkEpiloguePC_placed s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

def AdvanceEpiloguePlacedRoSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H → FindIndexPlacedOk H A → HmacPlacedRoOk H F →
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
      CmkLoopState_placed A x Gc stc ckc R cmkEpiloguePC_placed s0 s →
      LibsignalRoLoaded lsmpl s.mem →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

def LoopNoChainPanicPlacedRoSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H → FindIndexPlacedOk H A → HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index < x.counter →
      x.st.findReceiverChainIndex x.their = none →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A x x.G x.st x.ck R cmkLoopPC_placed s0 s →
      LibsignalRoLoaded lsmpl s.mem →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

def EpiloguePanicPlacedRoSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  H cmkExpectFailedSym = some Rust.panicked →
    H cmkPanicAddOverflowSym = some Rust.panicked →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F →
    ∀ (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (R : SepProp) (s0 s : State),
      ckc.index = x.counter →
      (x.counter = BitVec.allOnes 32 ∨ stc.findReceiverChainIndex x.their = none) →
      (x.model F).1 = .error .panic →
      CmkLoopState_placed A x Gc stc ckc R cmkEpiloguePC_placed s0 s →
      LibsignalRoLoaded lsmpl s.mem →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

end CryptoVerification.LibsignalSession
