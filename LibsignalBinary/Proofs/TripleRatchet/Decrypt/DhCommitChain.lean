/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WPp

/-!
# DH Step Commit Sub-Segment: Chain Layout & Checkpoint Definitions

Defines `chainAt` byte-slice decompositions, `Vec<Chain>` push/eviction bridges, and the mid-segment
checkpoint state `DhCommitState` and contract `DhCommitSpec` (`+0x8ac → +0x3e4`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DhCommitFacts

theorem spAligned_of_sp_eq {s1 s2 : State} (heq : s2.sp = s1.sp) (hal : s1.spAligned = true) :
    s2.spAligned = true := by
  unfold State.spAligned at hal ⊢
  rw [heq]
  exact hal

end DhCommitFacts

/-! ## 1. Fetch Macro and Hook Helpers on `tripleRatchetProgAt` -/

open Lean Elab Tactic in
/-- `code_fetches_from <code> <decPrefix> b H hfn off k0 len` adds `<code>_fetch_fnAddr`
    hypotheses for the instructions `k = k0, k0 + 4, …, k0 + len - 4` of the function at offset
    `off` (`hfn : <code>.fnOff name = off`), using `<decPrefix>_decode_0x<off+k>`. -/
elab "code_fetches_from " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max k0:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let k0 := k0.getNat
  let len := len.getNat
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  for i in [0:len / 4] do
    let k := k0 + 4 * i
    let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-- Fetch hypotheses for `try_decrypt_with_state::<HookRng>` (`hfn : fnOff tryDecryptName = 0x3439c`),
    from fn-relative offset `k0`, `len` bytes. -/
macro "td_fetches " b:term:max H:term:max hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H $hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) $k0 $len)

/-- Add instruction-fetch hypotheses for a function in `libsignalSessionCode` on `tripleRatchetProgAt`. -/
elab "tripleRatchetProgAt_fetches " b:term:max H:term:max hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "tripleRatchetProgAt_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "tripleRatchetProgAt_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin $b $H $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

theorem hookSessionMemmove_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveSpec hookStack) := by
  refine HookOk.of_trace (hookMemmove_ok hookStack) fun _ _ _ ht hpost => ?_
  simp only [libcMemmoveSpec, sessionMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

/-- `memmove` (`0x47f38` = `294712`) meets `sessionMemmoveSpec` on `tripleRatchetProgAt`. -/
theorem memmove_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memmove" := by fnoff_eq)
    (stackSize : Nat := 4096) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveSpec stackSize) :=
  hook_ok_at (hname := "memmove") rfl hk (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol])
    ⟨hookMemmove, rfl, hookSessionMemmove_ok (hookStack := stackSize)⟩

/-! ## 2. `chainAt` ↔ 104-Byte Block + Detached Inner Heap Buffers -/

/-- Padding byte count in `Option<chain::ChainKey>` (24 bytes when `none`, 4 bytes when `some`). -/
def optChainKeyPadLen : Option ChainKey → Nat
  | none => 24
  | some _ => 4

/-- The 32-byte in-struct representation of `Option<chain::ChainKey>` with padding `pad`. -/
def optChainKeyTailBytes (pin : VecPin) (o : Option ChainKey) (pad : List (BitVec 8)) :
    List (BitVec 8) :=
  match o with
  | none => unpack64 optChainKeyNone ++ pad
  | some ck => vecHeaderBytes pin.cap pin.ptr 32#64 ++ (unpack32 ck.index ++ pad)

theorem optChainKeyTailBytes_length (pin : VecPin) (o : Option ChainKey) {pad : List (BitVec 8)}
    (hpad : pad.length = optChainKeyPadLen o) :
    (optChainKeyTailBytes pin o pad).length = 32 := by
  cases o with
  | none =>
    simp [optChainKeyTailBytes, optChainKeyPadLen] at hpad ⊢
    omega
  | some ck =>
    simp [optChainKeyTailBytes, optChainKeyPadLen] at hpad ⊢
    omega

/-- Detached heap buffer of `Option<chain::ChainKey>`. -/
def optChainKeyHeap (A : RustAlloc) (pin : VecPin) : Option ChainKey → SepProp
  | none => emp
  | some ck => vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)

theorem optChainKeyAt_eq_exists_bytes (A : RustAlloc) (pin : VecPin) (o : Option ChainKey)
    (a : BitVec 64) :
    optChainKeyAt A pin o a =
      (∃∗ pad : List (BitVec 8),
        ⌜pad.length = optChainKeyPadLen o⌝ ∗ (a ↦ₛ optChainKeyTailBytes pin o pad)) ∗
      optChainKeyHeap A pin o := by
  cases o with
  | none =>
    simp only [optChainKeyAt, optChainKeyPadLen, optChainKeyTailBytes, optChainKeyHeap, sepConj_emp]
    rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 8#64) 24 (by decide),
        sepExists_sepConj_right]
    apply congrArg SepProp.sepExists
    funext pad
    have h8 : a + 8#64 = a + BitVec.ofNat 64 (unpack64 optChainKeyNone).length := by
      simp [unpack64_length]
    rw [sepConj_pure_left_comm, h8, ← pointsToBytes_append]
  | some ck =>
    simp only [optChainKeyAt, optChainKeyPadLen, optChainKeyTailBytes, optChainKeyHeap]
    rw [vecU8At_eq_header_sep_buf, vecHeader_eq_pointsToBytes, pointsTo32_eq_pointsToBytes,
        memRegion_eq_exists_bytes (a + 28#64) 4 (by decide)]
    simp only [length_keyToBytes32, sepConj_assoc]
    have hpull :
        ((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
          vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key) ∗
          ((a + 24#64) ↦ₛ unpack32 ck.index) ∗
          (∃∗ bs : List (BitVec 8), ⌜bs.length = 4⌝ ∗ ((a + 28#64) ↦ₛ bs))) =
        (((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
          ((a + 24#64) ↦ₛ unpack32 ck.index) ∗
          (∃∗ bs : List (BitVec 8), ⌜bs.length = 4⌝ ∗ ((a + 28#64) ↦ₛ bs))) ∗
         vecU8Buf A pin.cap pin.ptr (keyToBytes32 ck.key)) := by
      ac_rfl
    rw [hpull]
    congr 1
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    apply congrArg SepProp.sepExists
    funext pad
    have h24 : a + 24#64 = a + BitVec.ofNat 64 (vecHeaderBytes pin.cap pin.ptr 32#64).length := by
      simp [vecHeaderBytes_length]
    have h28 : a + 28#64 = (a + 24#64) + BitVec.ofNat 64 (unpack32 ck.index).length := by
      simp [unpack32_length]
    have hpull2 :
        ((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
          (((a + 24#64) ↦ₛ unpack32 ck.index) ∗
            (⌜pad.length = 4⌝ ∗ ((a + 28#64) ↦ₛ pad)))) =
        (⌜pad.length = 4⌝ ∗
          ((a ↦ₛ vecHeaderBytes pin.cap pin.ptr 32#64) ∗
            (((a + 24#64) ↦ₛ unpack32 ck.index) ∗ ((a + 28#64) ↦ₛ pad)))) := by
      ac_rfl
    rw [hpull2, h28, ← pointsToBytes_append, h24, ← pointsToBytes_append]

/-- The 72-byte prefix of a `session_structure::Chain` (three 24-byte `Vec` headers: `srk`, `priv`,
`message_keys`). -/
def chainHeaderBytes (gc : ChainGhost × ReceiverChain) : List (BitVec 8) :=
  vecHeaderBytes gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ++
    (vecHeaderBytes gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ++
      vecHeaderBytes gc.1.mkCap gc.1.mkPtr
        (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length))

@[local simp]
theorem chainHeaderBytes_length (gc : ChainGhost × ReceiverChain) :
    (chainHeaderBytes gc).length = 72 := by
  simp [chainHeaderBytes]

/-- The 104-byte in-buffer representation of a `session_structure::Chain` with padding `pad`. -/
def chainBytes (gc : ChainGhost × ReceiverChain) (pad : List (BitVec 8)) : List (BitVec 8) :=
  chainHeaderBytes gc ++ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad

theorem chainBytes_length (gc : ChainGhost × ReceiverChain) {pad : List (BitVec 8)}
    (hpad : pad.length = optChainKeyPadLen gc.2.chainKey) :
    (chainBytes gc pad).length = 104 := by
  simp [chainBytes, optChainKeyTailBytes_length gc.1.ck gc.2.chainKey hpad]

theorem pointsToBytes_chainHeaderBytes (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    (a ↦ₛ chainHeaderBytes gc) =
      vecHeader a gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        vecHeader (a + 24#64) gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        vecHeader (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) := by
  unfold chainHeaderBytes
  rw [pointsToBytes_append, pointsToBytes_append]
  simp only [vecHeaderBytes_length]
  rw [← vecHeader_eq_pointsToBytes, ← vecHeader_eq_pointsToBytes, ← vecHeader_eq_pointsToBytes]
  have h24 : a + BitVec.ofNat 64 24 = a + 24#64 := rfl
  have h48 : a + BitVec.ofNat 64 24 + BitVec.ofNat 64 24 = a + 48#64 := by bv_arith
  rw [h48, h24]

/-- Detached heap buffers owned by a `session_structure::Chain`, independent of its 104-byte slot. -/
def chainHeap (A : RustAlloc) (gc : ChainGhost × ReceiverChain) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
    gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗
    vecU8Buf A gc.1.srk.cap gc.1.srk.ptr gc.1.srk.bytes ∗
    vecU8Buf A gc.1.priv.cap gc.1.priv.ptr gc.1.priv.bytes ∗
    vecBuf A 104 8 (messageKeyAt A) gc.1.mkCap gc.1.mkPtr (gc.1.keys.zip gc.2.messageKeys) ∗
    optChainKeyHeap A gc.1.ck gc.2.chainKey

theorem chainAt_eq_headers_sep_heap (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    chainAt A gc a =
      (vecHeader a gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        vecHeader (a + 24#64) gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        vecHeader (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) ∗
        (∃∗ pad : List (BitVec 8),
          ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
            ((a + 72#64) ↦ₛ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad))) ∗
      chainHeap A gc := by
  unfold chainAt chainHeap vecGhostAt vecAt
  rw [vecU8At_eq_header_sep_buf A a,
      vecU8At_eq_header_sep_buf A (a + 24#64),
      optChainKeyAt_eq_exists_bytes A gc.1.ck gc.2.chainKey (a + 72#64)]
  ac_rfl

/-- Decompose `chainAt A gc a` into an existential 104-byte slice `a ↦ₛ chainBytes gc pad`
and the detached inner buffers `chainHeap A gc`. -/
theorem chainAt_eq_exists_bytes (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a =
      (∃∗ pad : List (BitVec 8),
        ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (a ↦ₛ chainBytes gc pad)) ∗
      chainHeap A gc := by
  rw [chainAt_eq_headers_sep_heap]
  congr 1
  have hhdr :
      (vecHeader a gc.1.srk.cap gc.1.srk.ptr (BitVec.ofNat 64 gc.1.srk.bytes.length) ∗
        vecHeader (a + 24#64) gc.1.priv.cap gc.1.priv.ptr (BitVec.ofNat 64 gc.1.priv.bytes.length) ∗
        vecHeader (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (BitVec.ofNat 64 (gc.1.keys.zip gc.2.messageKeys).length) ∗
        (∃∗ pad : List (BitVec 8),
          ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
            ((a + 72#64) ↦ₛ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad))) =
      (a ↦ₛ chainHeaderBytes gc) ∗
        (∃∗ pad : List (BitVec 8),
          ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
            ((a + 72#64) ↦ₛ optChainKeyTailBytes gc.1.ck gc.2.chainKey pad)) := by
    rw [pointsToBytes_chainHeaderBytes]
    ac_rfl
  rw [hhdr, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists
  funext pad
  have h72 : a + 72#64 = a + BitVec.ofNat 64 (chainHeaderBytes gc).length := by
    rw [chainHeaderBytes_length]
  rw [sepConj_pure_left_comm, h72, ← pointsToBytes_append]
  rfl

theorem chainAt_of_bytes (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64)
    {pad : List (BitVec 8)} (hpad : pad.length = optChainKeyPadLen gc.2.chainKey) :
    ((a ↦ₛ chainBytes gc pad) ∗ chainHeap A gc) ⊢ chainAt A gc a := by
  rw [chainAt_eq_exists_bytes]
  apply sepConj_mono_left
  exact Entails.sepExists_right pad (Entails.pure_right hpad (Entails.refl _))

/-- Detached heap buffers of a list of `Chain`s, in order. -/
def chainHeaps (A : RustAlloc) : List (ChainGhost × ReceiverChain) → SepProp
  | [] => emp
  | gc :: gcs => chainHeap A gc ∗ chainHeaps A gcs

@[local simp]
theorem chainHeaps_nil (A : RustAlloc) : chainHeaps A [] = emp := rfl

@[local simp]
theorem chainHeaps_cons (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (gcs : List (ChainGhost × ReceiverChain)) :
    chainHeaps A (gc :: gcs) = chainHeap A gc ∗ chainHeaps A gcs := rfl

/-- `ChainArrayBytes gcs bs` relates a list of `Chain`s `gcs` to the flat
`gcs.length * 104`-byte buffer slice `bs` holding their 104-byte struct representations. -/
inductive ChainArrayBytes : List (ChainGhost × ReceiverChain) → List (BitVec 8) → Prop
  | nil : ChainArrayBytes [] []
  | cons {gc : ChainGhost × ReceiverChain} {gcs : List (ChainGhost × ReceiverChain)}
      {pad bs : List (BitVec 8)}
      (hpad : pad.length = optChainKeyPadLen gc.2.chainKey)
      (hrest : ChainArrayBytes gcs bs) :
      ChainArrayBytes (gc :: gcs) (chainBytes gc pad ++ bs)

namespace ChainArrayBytes

theorem length_eq {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (h : ChainArrayBytes gcs bs) :
    bs.length = gcs.length * 104 := by
  induction h with
  | nil => rfl
  | @cons gc gcs pad bs hpad _ ih =>
    rw [List.length_append, chainBytes_length gc hpad, ih, List.length_cons, Nat.succ_mul]
    omega

end ChainArrayBytes

theorem arrayAt_chainAt_entails_bytes (A : RustAlloc) (base : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    arrayAt (chainAt A) 104 base gcs ⊢
      (∃∗ bs : List (BitVec 8), ⌜ChainArrayBytes gcs bs⌝ ∗ (base ↦ₛ bs)) ∗
        chainHeaps A gcs := by
  induction gcs generalizing base with
  | nil =>
    simp only [arrayAt_nil, chainHeaps_nil, sepConj_emp]
    apply Entails.sepExists_right []
    apply Entails.pure_right ChainArrayBytes.nil
    rw [pointsToBytes_nil]
    exact Entails.refl _
  | cons gc gcs ih =>
    rw [arrayAt_cons, chainAt_eq_exists_bytes, chainHeaps_cons]
    refine Entails.trans (sepConj_mono_right (ih (base + BitVec.ofNat 64 104))) ?_
    have hpull :
        (((∃∗ pad : List (BitVec 8),
            ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (base ↦ₛ chainBytes gc pad)) ∗
           chainHeap A gc) ∗
         ((∃∗ bs : List (BitVec 8), ⌜ChainArrayBytes gcs bs⌝ ∗
            ((base + BitVec.ofNat 64 104) ↦ₛ bs)) ∗
          chainHeaps A gcs)) =
        (((∃∗ pad : List (BitVec 8),
            ⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (base ↦ₛ chainBytes gc pad)) ∗
          (∃∗ bs : List (BitVec 8), ⌜ChainArrayBytes gcs bs⌝ ∗
            ((base + BitVec.ofNat 64 104) ↦ₛ bs))) ∗
         (chainHeap A gc ∗ chainHeaps A gcs)) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_left
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim
    intro pad
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro bs'
    have hpull2 :
        ((⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗ (base ↦ₛ chainBytes gc pad)) ∗
          (⌜ChainArrayBytes gcs bs'⌝ ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs'))) =
        (⌜pad.length = optChainKeyPadLen gc.2.chainKey⌝ ∗
          (⌜ChainArrayBytes gcs bs'⌝ ∗
            ((base ↦ₛ chainBytes gc pad) ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs')))) := by
      ac_rfl
    rw [hpull2]
    apply Entails.pure_left
    intro hpad
    apply Entails.pure_left
    intro hrest
    apply Entails.sepExists_right (chainBytes gc pad ++ bs')
    apply Entails.pure_right (.cons hpad hrest)
    rw [pointsToBytes_append, chainBytes_length gc hpad]
    exact Entails.refl _

theorem arrayAt_chainAt_of_bytes (A : RustAlloc) (base : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (hbs : ChainArrayBytes gcs bs) :
    ((base ↦ₛ bs) ∗ chainHeaps A gcs) ⊢ arrayAt (chainAt A) 104 base gcs := by
  induction hbs generalizing base with
  | nil =>
    simp only [pointsToBytes_nil, chainHeaps_nil, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  | @cons gc gcs pad bs' hpad _ ih =>
    rw [pointsToBytes_append, chainBytes_length gc hpad, chainHeaps_cons, arrayAt_cons]
    have hpull :
        (((base ↦ₛ chainBytes gc pad) ∗ ((base + BitVec.ofNat 64 104) ↦ₛ bs')) ∗
          (chainHeap A gc ∗ chainHeaps A gcs)) =
        (((base ↦ₛ chainBytes gc pad) ∗ chainHeap A gc) ∗
          (((base + BitVec.ofNat 64 104) ↦ₛ bs') ∗ chainHeaps A gcs)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono (chainAt_of_bytes A gc base hpad) (ih (base + BitVec.ofNat 64 104))

theorem vecBuf_chainAt_entails_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hcap : cap ≠ 0) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜ChainArrayBytes gcs bs ∧ bs.length = gcs.length * 104 ∧
          gcs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
        chainHeaps A gcs := by
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_left
  rintro ⟨hlen, hcap_lt, hptr⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (arrayAt_chainAt_entails_bytes A ptr gcs))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro bs
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (((⌜ChainArrayBytes gcs bs⌝ ∗ (ptr ↦ₛ bs)) ∗ chainHeaps A gcs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104))) =
      (⌜ChainArrayBytes gcs bs⌝ ∗
        (A.live ptr (cap.toNat * 104) 8 ∗
         (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
         chainHeaps A gcs)) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  intro hbs
  apply Entails.sepExists_right bs
  exact Entails.pure_right ⟨hbs, hbs.length_eq, hlen, hcap_lt, hptr⟩ (Entails.refl _)

theorem vecBuf_chainAt_of_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (hcap : cap ≠ 0)
    (hbs : ChainArrayBytes gcs bs)
    (hlen : gcs.length ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
      chainHeaps A gcs) ⊢
      vecBuf A 104 8 (chainAt A) cap ptr gcs := by
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
        chainHeaps A gcs) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (((ptr ↦ₛ bs) ∗ chainHeaps A gcs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104))) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_left (arrayAt_chainAt_of_bytes A ptr hbs))

/-- Precondition bridge for `growOneSpec` on `Vec<Chain>`. -/
theorem vecBuf_chainAt_full_entails_grow_one (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hfull : gcs.length = cap.toNat) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜ChainArrayBytes gcs bs ∧ bs.length = cap.toNat * 104⌝ ∗
        (⌜cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗ ⌜bs.length = cap.toNat * 104⌝)) ∗
        chainHeaps A gcs := by
  by_cases hcap : cap = 0
  · subst hcap
    have hgcs : gcs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hgcs
    rw [vecBuf_zero, ← sepConj_emp ⌜([] : List (ChainGhost × ReceiverChain)) = [] ∧ ptr ≠ 0⌝]
    apply Entails.pure_left
    rintro ⟨_, hptr⟩
    apply Entails.sepExists_right []
    simp only [↓reduceIte, chainHeaps_nil, sepConj_emp]
    apply Entails.pure_right ⟨.nil, rfl⟩
    exact Entails.pure_right_only ⟨by decide, hptr⟩ (Entails.refl _)
  · refine Entails.trans (vecBuf_chainAt_entails_bytes A cap ptr gcs hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.pure_left
    rintro ⟨hbs, hbs_len, _, hcap_lt, hptr⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hrem : (cap.toNat - gcs.length) * 104 = 0 := by omega
    rw [hrem, memRegion_zero]
    apply Entails.sepExists_right bs
    simp only [hcap, ↓reduceIte]
    apply Entails.pure_right ⟨hbs, hbs_cap⟩
    have hpull :
        (A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗ emp ∗ chainHeaps A gcs) =
        ((A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs)) ∗ chainHeaps A gcs) := by
      ac_rfl
    rw [hpull]
    apply sepConj_mono_left
    apply Entails.pure_right ⟨hcap_lt, hptr⟩
    apply sepConj_mono_right
    rw [sepConj_comm (ptr ↦ₛ bs)]
    exact Entails.pure_right hbs_cap (Entails.refl _)

/-- Postcondition bridge for `growOneSpec` on `Vec<Chain>`. -/
theorem vecBuf_chainAt_of_grow_one (A : RustAlloc) (cap newPtr : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {bs : List (BitVec 8)}
    (hfull : gcs.length = cap.toNat)
    (hbs : ChainArrayBytes gcs bs)
    (hnewPtr : newPtr ≠ 0)
    (hnew_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    let newCap := max (2 * cap.toNat) 4
    (A.live newPtr (newCap * 104) 8 ∗
      (newPtr ↦ₛ bs) ∗
      memRegion (newPtr + BitVec.ofNat 64 (cap.toNat * 104)) ((newCap - cap.toNat) * 104) ∗
      chainHeaps A gcs) ⊢
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 newCap) newPtr gcs := by
  intro newCap
  obtain ⟨hne0, htoNat, hlen_lt, hcap_lt⟩ := grow_one_newCap_props hfull hnew_lt
  have h := vecBuf_chainAt_of_bytes A (BitVec.ofNat 64 newCap) newPtr hne0 hbs
    (Nat.le_of_lt hlen_lt) hcap_lt hnewPtr
  rw [htoNat, hfull] at h
  exact h

/-- Split `vecBuf A 104 8 (chainAt A) cap ptr gcs` when `gcs.length < cap.toNat` to expose the
104-byte slot `memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104` for pushing a new `Chain`. -/
theorem vecBuf_chainAt_push_split (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hlen_lt : gcs.length < cap.toNat) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ⌜cap ≠ 0 ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen_lt; change gcs.length < 0 at hlen_lt; omega
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_left
  rintro ⟨_, hcap_lt, hptr⟩
  apply Entails.pure_right ⟨hcap, hcap_lt, hptr⟩
  have hsplit_len : (cap.toNat - gcs.length) * 104 =
      104 + (cap.toNat - (gcs.length + 1)) * 104 := by
    have : cap.toNat - gcs.length = 1 + (cap.toNat - (gcs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (gcs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [hsplit_len,
      memRegion_split (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 _ (by omega),
      hoff]
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        (memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
          memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((cap.toNat - (gcs.length + 1)) * 104))) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104)) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

/-- Reassemble `vecBuf A 104 8 (chainAt A) cap ptr (gcs ++ [gc])` after writing `chainAt A gc` at
`ptr + BitVec.ofNat 64 (gcs.length * 104)`. -/
theorem vecBuf_chainAt_push_reassemble (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (gc : ChainGhost × ReceiverChain)
    (hlen_lt : gcs.length < cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (chainAt A) 104 ptr gcs ∗
      chainAt A gc (ptr + BitVec.ofNat 64 (gcs.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
        ((cap.toNat - (gcs.length + 1)) * 104)) ⊢
      vecBuf A 104 8 (chainAt A) cap ptr (gcs ++ [gc]) := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen_lt; change gcs.length < 0 at hlen_lt; omega
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr (gcs ++ [gc]) hcap,
      List.length_append, List.length_singleton, arrayAt_concat]
  apply Entails.pure_right ⟨by omega, hcap_lt, hptr⟩
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 ptr gcs ∗
        chainAt A gc (ptr + BitVec.ofNat 64 (gcs.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (arrayAt (chainAt A) 104 ptr gcs ∗
          chainAt A gc (ptr + BitVec.ofNat 64 (gcs.length * 104))) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104)) := by
    ac_rfl
  rw [hpull]
  exact Entails.refl _

/-- Expose `vecBuf A 104 8 (chainAt A) cap ptr (gc₀ :: gcs)` for removing element 0 in the
eviction loop: splits out the 104-byte header `b₀ = chainBytes gc₀ pad₀` at `ptr` and the tail
bytes `bs_rest` at `ptr + 104` (`ChainArrayBytes gcs bs_rest`), plus `chainHeap A gc₀` and
`chainHeaps A gcs`. -/
theorem vecBuf_chainAt_expose_for_remove0 (A : RustAlloc) (cap ptr : BitVec 64)
    (gc₀ : ChainGhost × ReceiverChain) (gcs : List (ChainGhost × ReceiverChain)) :
    vecBuf A 104 8 (chainAt A) cap ptr (gc₀ :: gcs) ⊢
      ∃∗ pad₀ : List (BitVec 8), ∃∗ bs_rest : List (BitVec 8),
        ⌜pad₀.length = optChainKeyPadLen gc₀.2.chainKey ∧
          ChainArrayBytes gcs bs_rest ∧ bs_rest.length = gcs.length * 104 ∧
          gcs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ chainBytes gc₀ pad₀) ∗
        ((ptr + 104#64) ↦ₛ bs_rest) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104) ∗
        chainHeap A gc₀ ∗
        chainHeaps A gcs := by
  have hcap_or : cap = 0 ∨ cap ≠ 0 := Classical.em _
  rcases hcap_or with rfl | hcap
  · unfold vecBuf
    apply Entails.pure_left
    rintro ⟨hlen, _, _⟩
    simp at hlen
  · refine Entails.trans (vecBuf_chainAt_entails_bytes A cap ptr (gc₀ :: gcs) hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.pure_left
    rintro ⟨hbs, _, hlen, hcap_lt, hptr⟩
    cases hbs with
    | @cons _ _ pad₀ bs_rest hpad₀ hrest =>
      simp only [List.length_cons, chainHeaps_cons] at hlen ⊢
      rw [pointsToBytes_append, chainBytes_length gc₀ hpad₀]
      apply Entails.sepExists_right pad₀
      apply Entails.sepExists_right bs_rest
      apply Entails.pure_right ⟨hpad₀, hrest, hrest.length_eq, hlen, hcap_lt, hptr, hcap⟩
      have hpull :
          (A.live ptr (cap.toNat * 104) 8 ∗
            ((ptr ↦ₛ chainBytes gc₀ pad₀) ∗ ((ptr + BitVec.ofNat 64 104) ↦ₛ bs_rest)) ∗
            memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
              ((cap.toNat - (gcs.length + 1)) * 104) ∗
            (chainHeap A gc₀ ∗ chainHeaps A gcs)) =
          (A.live ptr (cap.toNat * 104) 8 ∗
            (ptr ↦ₛ chainBytes gc₀ pad₀) ∗
            ((ptr + 104#64) ↦ₛ bs_rest) ∗
            memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
              ((cap.toNat - (gcs.length + 1)) * 104) ∗
            chainHeap A gc₀ ∗
            chainHeaps A gcs) := by
        ac_rfl
      rw [hpull]
      exact Entails.refl _

/-- After `memmove(ptr, ptr + 104, gcs.length * 104)` on `b₀ ++ bs_rest` (`b₀.length = 104`,
`bs_rest.length = gcs.length * 104`), `listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104)` is
`bs_rest` followed by 104 trailing bytes, reassembling `vecBuf A 104 8 (chainAt A) cap ptr gcs`. -/
theorem vecBuf_chainAt_of_remove0 (A : RustAlloc) (cap ptr : BitVec 64)
    {gcs : List (ChainGhost × ReceiverChain)} {b₀ bs_rest : List (BitVec 8)}
    (hb₀ : b₀.length = 104)
    (hrest : ChainArrayBytes gcs bs_rest)
    (hlen : gcs.length + 1 ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (A.live ptr (cap.toNat * 104) 8 ∗
      (ptr ↦ₛ listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
        ((cap.toNat - (gcs.length + 1)) * 104) ∗
      chainHeaps A gcs) ⊢
      vecBuf A 104 8 (chainAt A) cap ptr gcs := by
  have hcap : cap ≠ 0 := by intro h0; rw [h0] at hlen; change gcs.length + 1 ≤ 0 at hlen; omega
  have hrest_len : bs_rest.length = gcs.length * 104 := hrest.length_eq
  have hmove : listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104) =
      bs_rest ++ (b₀ ++ bs_rest).drop (gcs.length * 104) := by
    unfold listMove
    simp only [List.take_zero, List.nil_append, Nat.zero_add]
    have hdrop104 : (b₀ ++ bs_rest).drop 104 = bs_rest := by
      rw [← hb₀, List.drop_left]
    rw [hdrop104, ← hrest_len, List.take_length]
  have htail_len : ((b₀ ++ bs_rest).drop (gcs.length * 104)).length = 104 := by
    rw [List.length_drop, List.length_append, hb₀, hrest_len]
    omega
  rw [hmove, pointsToBytes_append, hrest_len]
  have htail_reg := pointsToBytes_entails_memRegion
    (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((b₀ ++ bs_rest).drop (gcs.length * 104))
  rw [htail_len] at htail_reg
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right htail_reg))) ?_
  have hsplit_len : (cap.toNat - gcs.length) * 104 =
      104 + (cap.toNat - (gcs.length + 1)) * 104 := by
    have : cap.toNat - gcs.length = 1 + (cap.toNat - (gcs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (gcs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  have hpull :
      (A.live ptr (cap.toNat * 104) 8 ∗
        ((ptr ↦ₛ bs_rest) ∗ memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104) ∗
        memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((cap.toNat - (gcs.length + 1)) * 104) ∗
        chainHeaps A gcs) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        (ptr ↦ₛ bs_rest) ∗
        (memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 ∗
          memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((cap.toNat - (gcs.length + 1)) * 104)) ∗
        chainHeaps A gcs) := by
    ac_rfl
  rw [hpull, ← hoff,
      ← memRegion_split (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 _ (by omega),
      ← hsplit_len]
  exact vecBuf_chainAt_of_bytes A cap ptr hcap hrest (by omega) hcap_lt hptr

/-- For a non-empty list `c :: cs` with `(c :: cs).length ≥ 6`,
`RatchetState.evictReceiverChains (c :: cs)` equals `RatchetState.evictReceiverChains cs`. -/
theorem evictReceiverChains_cons_of_ge_six (c : ReceiverChain) (cs : List ReceiverChain)
    (h : 6 ≤ (c :: cs).length) :
    RatchetState.evictReceiverChains (c :: cs) = RatchetState.evictReceiverChains cs := by
  unfold RatchetState.evictReceiverChains
  simp only [List.length_cons] at h ⊢
  have hsub : cs.length + 1 - maxReceiverChains = (cs.length - maxReceiverChains) + 1 := by
    unfold maxReceiverChains at *; omega
  rw [hsub, List.drop_succ_cons]

theorem evictReceiverChains_of_le_five (cs : List ReceiverChain) (h : cs.length ≤ 5) :
    RatchetState.evictReceiverChains cs = cs := by
  unfold RatchetState.evictReceiverChains
  have hsub : cs.length - maxReceiverChains = 0 := by
    unfold maxReceiverChains; omega
  rw [hsub, List.drop_zero]

/-! ## 3. Mid-Segment Checkpoint (`+0x8ac` = `0x34c48`) for Commit + Push + Evict -/

/-- S3 commit checkpoint PC (`+0x8ac` = `0x34c48`), reached when the sending
`RootKey::create_chain` call at `+0x7d4` returns `Ok((finalRootKey, senderChainKey))` (`w8 = 0`). -/
abbrev segDhCommitPC (img : Obj.Image) : BitVec 64 := tryDecryptEntry img + 0x8ac#64

/-- S3 commit checkpoint state at `segDhCommitPC img` (`+0x8ac`) after both `RootKey::create_chain`
calls and `KeyPair::generate` succeed:
* `tr.ratchet.senderChain = some sc`, `tr.ratchet.rootKey` at `sp + 0xb8..0xd8` is zeroed, and
  `draws = min 32 x.rest.length`;
* `sp + 0x190..0x1d8` holds `createChainResultAt (sp + 0x190) (.ok (finalRootKey, senderChainKey))`;
* `sp + 0x3d0..0x3f4` holds `chainKeyBytes receiverChainKey` (`36` B), with staging copies at
  `sp + 0x4d0..0x4e0`, `sp + 0x10..0x14`, and `sp + 0x2b0..0x2c0`;
* `sp + 0x400..0x440` holds `newSenderKey`, and `[sp + 0x1c]` holds `msgW`
  (`msgW.setWidth 8 = msgTypeByte x.msgType`). -/
def DhCommitState (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  let draws := min 32 x.rest.length
  s.pc = segDhCommitPC img ∧
  tryDecryptMidMeta img s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x3d0#64 ∧
  ∃ (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 0x2c#64) 4 ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion (sp + 0x1d8#64) 0xd8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x110 ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x440#64) 0x80 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion (sp + 0x4e0#64) 0xa0 ∗
      tryDecryptCommonHeap A ctl img x draws s0 ∗ R)

def S3CommitSpecExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  AllocContracts img.base A ext →
  PublicKeySerializeOkExt img.base A ext →
  ChainKeyToPbOkExt img.base A ext →
  GrowOneChainOkExt img A ext →
  DropChainOkExt img.base A ext →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
      (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
      (finalRootKey : RootKey) (senderChainKey : ChainKey)
      (R : SepProp) (s0 s : State),
      tr.ratchet.senderChain = some sc →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      Ratchet.clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
      DhCommitState A ctl img x trG tr st1 receiverChainKey newSenderKey
        finalRootKey senderChainKey R s0 s →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      let newChain : ReceiverChain :=
        { senderRatchetKey := x.msg.senderRatchetKey
          chainKey := some receiverChainKey
          messageKeys := [] }
      let r1 : RatchetState :=
        { tr.ratchet with
          senderChain := some ⟨newSenderKey, senderChainKey⟩
          rootKey := finalRootKey
          previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
          receiverChains :=
            RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((∃ trG', ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-- S3 commit sub-segment contract (`+0x8ac → +0x3e4` or panic): updates `previous_counter` and
`root_key`, serializes `x.msg.senderRatchetKey`, converts `receiverChainKey` via `ChainKey::to_pb`,
pushes the new `ReceiverChain` (growing if `len = cap`), frees the serialized-key box, evicts oldest
chains until `len ≤ 5`, commits `sender_chain`, and branches to `segConsumeMsgKeyPC img` (`+0x3e4`). -/
def DhCommitSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
      (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
      (finalRootKey : RootKey) (senderChainKey : ChainKey)
      (R : SepProp) (s0 s : State),
      tr.ratchet.senderChain = some sc →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      Ratchet.clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
      DhCommitState A ctl img x trG tr st1 receiverChainKey newSenderKey
        finalRootKey senderChainKey R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let newChain : ReceiverChain :=
        { senderRatchetKey := x.msg.senderRatchetKey
          chainKey := some receiverChainKey
          messageKeys := [] }
      let r1 : RatchetState :=
        { tr.ratchet with
          senderChain := some ⟨newSenderKey, senderChainKey⟩
          rootKey := finalRootKey
          previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
          receiverChains :=
            RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
      ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
        ((∃ trG', ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1
            receiverChainKey (min 32 x.rest.length) R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

/-! ## 4. Relocatable `[LibsignalPlacement]` S3 Commit Checkpoint State and Seam -/

abbrev segDhCommitPC_at (entry : BitVec 64) : BitVec 64 := entry + 0x8ac#64

def DhCommitStatePlaced [LibsignalPlacement] (entry : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8)))
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 1504#64
  let draws := min 32 x.rest.length
  s.pc = segDhCommitPC_at entry ∧
  tryDecryptMidMetaPlaced s0 s ∧
  s.readReg64 .x19 = x.ret ∧
  s.readReg64 .x20 = sp + 0x140#64 ∧
  s.readReg64 .x21 = x.ss ∧
  s.readReg64 .x22 = x.msgA ∧
  s.readReg64 .x23 = sp + 0x500#64 ∧
  s.readReg64 .x25 = sp + 0x190#64 ∧
  s.readReg64 .x27 = sp + 0x38#64 ∧
  s.readReg64 .x28 = sp + 0x3d0#64 ∧
  ∃ (msgW : BitVec 32),
    msgW.setWidth 8 = msgTypeByte x.msgType ∧
    (s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A (sp + 0x38#64) trG { tr with ratchet := { tr.ratchet with rootKey := 0 } } ∗
      memRegion x.ret 48 ∗
      memRegion sp 0x10 ∗
      ((sp + 0x10#64) ↦ₛ ((chainKeyBytes receiverChainKey).drop 16).take 4) ∗
      memRegion (sp + 0x14#64) 8 ∗
      ((sp + 0x1c#64) ↦₃₂ msgW) ∗
      ((sp + 0x20#64) ↦₆₄ x.locA) ∗
      ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
      memRegion (sp + 0x2c#64) 4 ∗
      ((sp + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 0x140#64) 0x50 ∗
      ((sp + 0x190#64) ↦₃₂ 0#32) ∗
      ((sp + 0x194#64) ↦ₛ keyToBytes32 finalRootKey) ∗
      ((sp + 0x1b4#64) ↦ₛ chainKeyBytes senderChainKey) ∗
      memRegion (sp + 0x1d8#64) 0xd8 ∗
      memRegion (sp + 0x2b0#64) 0x10 ∗
      memRegion (sp + 0x2c0#64) 0x110 ∗
      ((sp + 0x3d0#64) ↦ₛ chainKeyBytes receiverChainKey) ∗
      memRegion (sp + 0x3f4#64) 12 ∗
      ((sp + 0x400#64) ↦ₛ newSenderKey.publicKey.bytes.toList) ∗
      ((sp + 0x420#64) ↦ₛ newSenderKey.privateKey.bytes.toList) ∗
      memRegion (sp + 0x440#64) 0x80 ∗
      ((sp + 0x4c0#64) ↦ₛ (chainKeyBytes receiverChainKey).drop 20) ∗
      ((sp + 0x4d0#64) ↦ₛ (chainKeyBytes receiverChainKey).take 16) ∗
      memRegion (sp + 0x4e0#64) 0xa0 ∗
      tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ R)

def S3CommitSeamPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (sc : SenderChain)
    (receiverChainKey : ChainKey) (newSenderKey : KeyPair)
    (finalRootKey : RootKey) (senderChainKey : ChainKey)
    (R : SepProp) (s0 s : State),
    tr.ratchet.senderChain = some sc →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    Ratchet.clampScalar newSenderKey.privateKey.bytes = newSenderKey.privateKey.bytes →
    DhCommitStatePlaced entry A ctl x trG tr st1 receiverChainKey newSenderKey
      finalRootKey senderChainKey R s0 s →
    prog.CodeLoaded s.mem →
    let newChain : ReceiverChain :=
      { senderRatchetKey := x.msg.senderRatchetKey
        chainKey := some receiverChainKey
        messageKeys := [] }
    let r1 : RatchetState :=
      { tr.ratchet with
        senderChain := some ⟨newSenderKey, senderChainKey⟩
        rootKey := finalRootKey
        previousCounter := BitVec.ofNat 32 (sc.chainKey.index.toNat - 1)
        receiverChains :=
          RatchetState.evictReceiverChains (tr.ratchet.receiverChains ++ [newChain]) }
    ∃ s', Steps prog s s' ∧
      ((∃ trG', ConsumeMsgKeyStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1
          receiverChainKey (min 32 x.rest.length) R s0 s') ∨
       (s'.status = .Panicked ∧
         (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
