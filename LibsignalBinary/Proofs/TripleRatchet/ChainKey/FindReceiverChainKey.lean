/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.ChainKeyCodeSym
import all Init.Data.String.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndex
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The base session program, rebased at `b`. -/
noncomputable abbrev SP_findReceiverChainKey (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))

/-- Close a `CalleeSavedPreserved s0 sf` goal after straight-line execution. -/
macro "findReceiverChainKey_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    State.writeVReg128_setPC, State.writeVReg128_setPState, State.writeVReg128_setMem,
    arm64_norm, *]
  done))

namespace FindReceiverChainKeyFacts

theorem findReceiverChainKey_fnOff : libsignalSessionCode.fnOff findReceiverChainKeyName = num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key")

end FindReceiverChainKeyFacts

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key") → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key" + 392)]

/-- Introduce instruction-fetch facts for `find_receiver_chain_key` (`0xe8fc`, 99 instructions = 396 bytes). -/
elab "findReceiverChainKey_fetches " b:term:max H:term:max : tactic => do
  let hfn := mkIdent ``FindReceiverChainKeyFacts.findReceiverChainKey_fnOff
  let fetchEntry := mkIdent ``CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent ``CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let currNs ← getCurrNamespace
  for i in [0 : 99] do
    let k := 4 * i
    let hex := String.ofList (Nat.toDigits 16 (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key") + k))
    let dec := mkIdent (currNs ++ Name.mkSimple s!"libsignalSessionBin_decode_0x{hex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end Fetch

/-! ## 1. Rodata & Address Helpers -/

open ProofLib.ProgramReflection

private theorem entails_of_eq {P P' Q : SepProp} (h : P = P') (hq : P' ⊢ Q) : P ⊢ Q :=
  h ▸ hq

private theorem memRegion_split_at (a : BitVec 64) (n k nk : Nat) {a' : BitVec 64}
    (hnk : n + k = nk) (ha : a + BitVec.ofNat 64 n = a') (h : nk ≤ 2 ^ 64) :
    memRegion a nk = memRegion a n ∗ memRegion a' k := by
  subst hnk ha
  exact memRegion_split a n k h

private theorem rodata_0x41bf8_eq :
    (libsignalSessionImage.data.drop (num% (ls_str% "missing receiver chain key") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 26 =
      invalidSessionStructureStr .missingReceiverChainKey := by
  rfl_kernel

private theorem rodata_missingReceiverChainKey_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "missing receiver chain key")) ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_str% "missing receiver chain key")) (secLen := 26) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x41bf8_eq] at h

private theorem adrp_missingReceiverChainKey {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key")) :
    ((entry + bv% (272)) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_str% "missing receiver chain key" - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) =
      img.base + bv% (ls_str% "missing receiver chain key") := by
  have hbal := ProofLib.base_aligned_of_loads himg
  rw [hentry]
  revert hbal
  bv_bits

private theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  simp only [leBytes, unpack32, List.range, List.range.loop, List.map]
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = (w >>> 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = (w >>> 16).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = (w >>> 24).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [h0, h1, h2, h3]
  unfold BitVec.extractLsb'
  rfl

private theorem pointsToBytes_chainKeyBytes_eq (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

/-! ## 2. `ratchetAt`, `chainAt`, and `optChainKeyAt` Exposure and Reassembly -/

def vecBufRest_shared_lb {α : Type} (A : RustAlloc) (stride align : Nat)
    (cap ptr : BitVec 64) (xs : List α) : SepProp :=
  ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  (if cap = 0 then emp
   else A.live ptr (cap.toNat * stride) align ∗
     memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))

private theorem vecBuf_expose_arrayAt {α : Type} (A : RustAlloc) {stride : Nat}
    (align : Nat) (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) :
    vecBuf A stride align elem cap ptr xs ⊢
      ⌜xs.length * stride < 2 ^ 63⌝ ∗
      arrayAt elem stride ptr xs ∗
      vecBufRest_shared_lb A stride align cap ptr xs := by
  unfold vecBuf vecBufRest_shared_lb
  apply Entails.pure_left
  rintro ⟨hlen, hlt, hptr⟩
  have hxs_lt : xs.length * stride < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right stride hlen) hlt
  apply Entails.pure_right hxs_lt
  rw [sepConj_pure_left_comm]
  apply Entails.pure_right ⟨hlen, hlt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [↓reduceIte, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact entails_of_eq (by ac_rfl) (Entails.refl _)

private theorem vecBuf_reassemble_arrayAt {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) :
    arrayAt elem stride ptr xs ∗ vecBufRest_shared_lb A stride align cap ptr xs ⊢
      vecBuf A stride align elem cap ptr xs := by
  unfold vecBuf vecBufRest_shared_lb
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hlen, hlt, hptr⟩
  apply Entails.pure_right ⟨hlen, hlt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [↓reduceIte, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact entails_of_eq (by ac_rfl) (Entails.refl _)

def ratchetTailRest (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost) (st : RatchetState) : SepProp :=
  ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
    st.maxForwardJumps < 2 ^ 64⌝ ∗
  (self ↦₆₄ G.chainsCap) ∗
  vecBufRest_shared_lb A 104 8 G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
  ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
  ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
  ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4

theorem ratchetAt_expose_findIndex (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    ratchetAt A self G st ⊢
      ⌜G.chains.length = st.receiverChains.length ∧
        (G.chains.zip st.receiverChains).length * 104 < 2 ^ 63⌝ ∗
      ((self + 8#64) ↦₆₄ G.chainsPtr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ∗
      arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) ∗
      ratchetTailRest A self G st := by
  set cs := G.chains.zip st.receiverChains
  unfold ratchetAt vecAt vecHeader ratchetTailRest
  apply Entails.pure_left
  rintro ⟨hchains_len, hpad, hmax⟩
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right
      (vecBuf_expose_arrayAt A 8 (chainAt A) G.chainsCap G.chainsPtr cs))) ?_
  rw [← sepConj_assoc, sepConj_pure_left_comm]
  simp only [sepConj_assoc]
  apply Entails.pure_left
  intro hcs_lt
  apply Entails.pure_right ⟨hchains_len, hcs_lt⟩
  simp only [sepConj_pure_left_comm]
  apply Entails.pure_right ⟨hchains_len, hpad, hmax⟩
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

theorem ratchetAt_reassemble_findIndex (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    ((self + 8#64) ↦₆₄ G.chainsPtr) ∗
    ((self + 16#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ∗
    arrayAt (chainAt A) 104 G.chainsPtr (G.chains.zip st.receiverChains) ∗
    ratchetTailRest A self G st ⊢
      ratchetAt A self G st := by
  set cs := G.chains.zip st.receiverChains
  unfold ratchetAt vecAt vecHeader ratchetTailRest
  rw [sepConj_pure_left_comm (arrayAt (chainAt A) 104 G.chainsPtr cs),
      sepConj_pure_left_comm ((self + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length),
      sepConj_pure_left_comm ((self + 8#64) ↦₆₄ G.chainsPtr)]
  apply Entails.pure_left
  rintro ⟨hchains_len, hpad, hmax⟩
  apply Entails.pure_right ⟨hchains_len, hpad, hmax⟩
  refine Entails.trans ?_
    (sepConj_mono_left (sepConj_mono_right
      (vecBuf_reassemble_arrayAt A 104 8 (chainAt A) G.chainsCap G.chainsPtr cs)))
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

def chainRest (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = .ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length ∧
    gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗
    vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys)

theorem chainAt_eq_optChainKeyAt (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    chainAt A gc a = optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗ chainRest A gc a := by
  unfold chainAt chainRest
  ac_rfl

def optChainKeySomeRest (A : RustAlloc) (pin : VecPin) (a : BitVec 64) : SepProp :=
  ⌜32 ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
  A.live pin.ptr pin.cap.toNat 1 ∗
  memRegion (pin.ptr + 32#64) (pin.cap.toNat - 32) ∗
  memRegion (a + 28#64) 4

theorem optChainKeyAt_some_expose (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin (some ck) a ⊢
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ pin.cap) ∗
      ((a + 8#64) ↦₆₄ pin.ptr) ∗
      ((a + 16#64) ↦₆₄ 32#64) ∗
      ((a + 24#64) ↦₃₂ ck.index) ∗
      (pin.ptr ↦ₛ keyToBytes32 ck.key) ∗
      optChainKeySomeRest A pin a := by
  dsimp only [optChainKeyAt, vecU8At, vecHeader, optChainKeySomeRest]
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [hlen]
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm ((a + 16#64) ↦₆₄ 32#64),
      sepConj_pure_left_comm ((a + 8#64) ↦₆₄ pin.ptr),
      sepConj_pure_left_comm (a ↦₆₄ pin.cap)]
  apply Entails.pure_left
  rintro ⟨h32, hlt, hptr⟩
  have hcap : pin.cap ≠ 0 := by
    intro h0; rw [h0] at h32; simp at h32
  simp only [hcap, ↓reduceIte]
  apply Entails.pure_right hlt
  rw [sepConj_pure_left_comm (pin.ptr ↦ₛ keyToBytes32 ck.key),
      sepConj_pure_left_comm ((a + 24#64) ↦₃₂ ck.index),
      sepConj_pure_left_comm ((a + 16#64) ↦₆₄ 32#64),
      sepConj_pure_left_comm ((a + 8#64) ↦₆₄ pin.ptr),
      sepConj_pure_left_comm (a ↦₆₄ pin.cap)]
  apply Entails.pure_right ⟨h32, hlt, hptr⟩
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

theorem optChainKeyAt_some_reassemble (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    (a ↦₆₄ pin.cap) ∗
    ((a + 8#64) ↦₆₄ pin.ptr) ∗
    ((a + 16#64) ↦₆₄ 32#64) ∗
    ((a + 24#64) ↦₃₂ ck.index) ∗
    (pin.ptr ↦ₛ keyToBytes32 ck.key) ∗
    optChainKeySomeRest A pin a ⊢
      optChainKeyAt A pin (some ck) a := by
  dsimp only [optChainKeyAt, vecU8At, vecHeader, optChainKeySomeRest]
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [hlen]
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm (pin.ptr ↦ₛ keyToBytes32 ck.key),
      sepConj_pure_left_comm ((a + 24#64) ↦₃₂ ck.index),
      sepConj_pure_left_comm ((a + 16#64) ↦₆₄ 32#64),
      sepConj_pure_left_comm ((a + 8#64) ↦₆₄ pin.ptr),
      sepConj_pure_left_comm (a ↦₆₄ pin.cap)]
  apply Entails.pure_left
  rintro ⟨h32, hlt, hptr⟩
  have hcap : pin.cap ≠ 0 := by
    intro h0; rw [h0] at h32; simp at h32
  simp only [hcap, ↓reduceIte]
  rw [sepConj_pure_left_comm ((a + 16#64) ↦₆₄ 32#64),
      sepConj_pure_left_comm ((a + 8#64) ↦₆₄ pin.ptr),
      sepConj_pure_left_comm (a ↦₆₄ pin.cap)]
  apply Entails.pure_right ⟨h32, hlt, hptr⟩
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

def optChainKeyNoneRest_shared_lb (a : BitVec 64) : SepProp :=
  memRegion (a + 80#64) 24

theorem chainAt_none_expose (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) (hnone : gc.2.chainKey = none) :
    chainAt A gc a =
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      optChainKeyNoneRest_shared_lb a ∗
      chainRest A gc a := by
  rw [chainAt_eq_optChainKeyAt A gc a, hnone]
  dsimp only [optChainKeyAt, optChainKeyNone, optChainKeyNoneRest_shared_lb]
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  rw [h80]
  ac_rfl

theorem chainAt_some_expose (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) (hsome : gc.2.chainKey = some ck) :
    chainAt A gc a ⊢
      ⌜gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
      ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
      ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗
      (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
      optChainKeySomeRest A gc.1.ck (a + 72#64) ∗
      chainRest A gc a := by
  rw [chainAt_eq_optChainKeyAt A gc a, hsome]
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have h96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  refine Entails.trans (sepConj_mono_left (optChainKeyAt_some_expose A gc.1.ck ck (a + 72#64))) ?_
  rw [h80, h88, h96]
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

theorem chainAt_some_reassemble (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (ck : ChainKey) (a : BitVec 64) (hsome : gc.2.chainKey = some ck) :
    ((a + 72#64) ↦₆₄ gc.1.ck.cap) ∗
    ((a + 80#64) ↦₆₄ gc.1.ck.ptr) ∗
    ((a + 88#64) ↦₆₄ 32#64) ∗
    ((a + 96#64) ↦₃₂ ck.index) ∗
    (gc.1.ck.ptr ↦ₛ keyToBytes32 ck.key) ∗
    optChainKeySomeRest A gc.1.ck (a + 72#64) ∗
    chainRest A gc a ⊢
      chainAt A gc a := by
  rw [chainAt_eq_optChainKeyAt A gc a, hsome]
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
  have h96 : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
  rw [← h80, ← h88, ← h96]
  refine Entails.trans ?_ (sepConj_mono_left (optChainKeyAt_some_reassemble A gc.1.ck ck (a + 72#64)))
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

/-! ## 3. Stack, Result Buffer, and Unaligned Copy Helpers -/

/-- Split `memRegion (sp - c) N` at `n` (`N = n + k`, `c' = c - n`). -/
private theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

private theorem stackAt_findReceiverChainKeyStack (sp : BitVec 64) :
    stackAt sp findReceiverChainKeyStack =
      memRegion (sp - 2048#64) 944 ∗
      stackAt (sp - 80#64) 1024 ∗
      memRegion (sp - 80#64) 32 ∗
      (∃∗ v29 : BitVec 64, (sp - 48#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 40#64) ↦₆₄ v30) ∗
      (∃∗ v21 : BitVec 64, (sp - 32#64) ↦₆₄ v21) ∗
      memRegion (sp - 24#64) 8 ∗
      (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
      (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19) := by
  unfold stackAt findReceiverChainKeyStack
  rw [mr_cut' sp 2048 1104 944 1104 2048 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 1104 80 1024 80 1104 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 80 48 32 48 80 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_eight (sp - 48#64), memRegion_eight (sp - 40#64), memRegion_eight (sp - 32#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  have h1104 : sp - 80#64 - 1024#64 = sp - 1104#64 := by bv_omega
  rw [h1104]

private theorem stackAt_findReceiverChainKeyStack_repack (sp : BitVec 64) (v29 v30 v21 v20 v19 : BitVec 64) :
    memRegion (sp - 2048#64) 944 ∗
    stackAt (sp - 80#64) 1024 ∗
    memRegion (sp - 80#64) 32 ∗
    ((sp - 48#64) ↦₆₄ v29) ∗
    ((sp - 40#64) ↦₆₄ v30) ∗
    ((sp - 32#64) ↦₆₄ v21) ∗
    memRegion (sp - 24#64) 8 ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp findReceiverChainKeyStack := by
  rw [stackAt_findReceiverChainKeyStack sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (Entails.sepExists_intro v29)
    (sepConj_mono (Entails.sepExists_intro v30)
      (sepConj_mono (Entails.sepExists_intro v21)
        (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro v20)
          (Entails.sepExists_intro v19)))))

theorem sp_scratch32_unpack (sp : BitVec 64) :
    memRegion (sp - 80#64) 32 =
      (∃∗ s0 : BitVec 16, (sp - 80#64) ↦₁₆ s0) ∗
      (∃∗ s2 : BitVec 8, (sp - 78#64) ↦₈ s2) ∗
      (∃∗ s3 : BitVec 64, (sp - 77#64) ↦₆₄ s3) ∗
      memRegion (sp - 69#64) 5 ∗
      (∃∗ s16 : BitVec 64, (sp - 64#64) ↦₆₄ s16) ∗
      (∃∗ s24 : BitVec 8, (sp - 56#64) ↦₈ s24) ∗
      memRegion (sp - 55#64) 7 := by
  rw [mr_cut' sp 80 78 2 30 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 78 77 1 29 30 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 77 69 8 21 29 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 69 64 5 16 21 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 64 56 8 8 16 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 56 55 1 7 8 rfl rfl (by decide) (by decide) (by decide),
      memRegion_two (sp - 80#64), memRegion_one (sp - 78#64), memRegion_eight (sp - 77#64),
      memRegion_eight (sp - 64#64), memRegion_one (sp - 56#64)]

theorem sp_scratch32_repack (sp : BitVec 64) (w0 : BitVec 64) (w8 : BitVec 16)
    (w10 : BitVec 8) (s16 : BitVec 64) (s24 : BitVec 8) :
    ((sp - 80#64) ↦₆₄ w0) ∗
    ((sp - 72#64) ↦₁₆ w8) ∗
    ((sp - 70#64) ↦₈ w10) ∗
    memRegion (sp - 69#64) 5 ∗
    ((sp - 64#64) ↦₆₄ s16) ∗
    ((sp - 56#64) ↦₈ s24) ∗
    memRegion (sp - 55#64) 7 ⊢
      memRegion (sp - 80#64) 32 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion (sp - 80#64) w0)
      (sepConj_mono (pointsTo16_entails_memRegion (sp - 72#64) w8)
        (sepConj_mono (pointsTo8_entails_memRegion (sp - 70#64) w10)
          (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion (sp - 64#64) s16)
            (sepConj_mono_left (pointsTo8_entails_memRegion (sp - 56#64) s24))))))) ?_
  rw [← mr_cut' sp 56 55 1 7 8 rfl rfl (by decide) (by decide) (by decide),
      ← mr_cut' sp 64 56 8 8 16 rfl rfl (by decide) (by decide) (by decide),
      ← mr_cut' sp 69 64 5 16 21 rfl rfl (by decide) (by decide) (by decide),
      ← mr_cut' sp 70 69 1 21 22 rfl rfl (by decide) (by decide) (by decide),
      ← mr_cut' sp 72 70 2 22 24 rfl rfl (by decide) (by decide) (by decide),
      ← mr_cut' sp 80 72 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  exact Entails.refl _

theorem mr_add_split (r : BitVec 64) (off n k off' nk : Nat)
    (hnk : n + k = nk) (hoff : off + n = off') (h : nk ≤ 2 ^ 64) :
    memRegion (r + BitVec.ofNat 64 off) nk =
      memRegion (r + BitVec.ofNat 64 off) n ∗ memRegion (r + BitVec.ofNat 64 off') k := by
  subst hnk hoff
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memRegion40_unpack_none (r : BitVec 64) :
    memRegion r 40 = (∃∗ t0 : BitVec 32, r ↦₃₂ t0) ∗ memRegion (r + 4#64) 36 := by
  rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split r 4 36 (by decide), memRegion_four r]

theorem memRegion40_unpack_err (r : BitVec 64) :
    memRegion r 40 =
      (∃∗ t0 : BitVec 32, r ↦₃₂ t0) ∗
      memRegion (r + 4#64) 4 ∗
      (∃∗ p0 : BitVec 64, (r + 8#64) ↦₆₄ p0) ∗
      (∃∗ l0 : BitVec 64, (r + 16#64) ↦₆₄ l0) ∗
      memRegion (r + 24#64) 16 := by
  rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split r 4 36 (by decide),
      mr_add_split r 4 4 32 8 36 rfl rfl (by decide),
      mr_add_split r 8 8 24 16 32 rfl rfl (by decide),
      mr_add_split r 16 8 16 24 24 rfl rfl (by decide),
      memRegion_four r, memRegion_eight (r + 8#64), memRegion_eight (r + 16#64)]

theorem memRegion40_unpack_some (r : BitVec 64) :
    memRegion r 40 =
      (∃∗ r0 : BitVec 32, r ↦₃₂ r0) ∗
      (∃∗ r4 : BitVec 32, (r + 4#64) ↦₃₂ r4) ∗
      (∃∗ r8 : BitVec 64, (r + 8#64) ↦₆₄ r8) ∗
      (∃∗ r16 : BitVec 16, (r + 16#64) ↦₁₆ r16) ∗
      (∃∗ r18 : BitVec 8, (r + 18#64) ↦₈ r18) ∗
      (∃∗ r19 : BitVec 32, (r + 19#64) ↦₃₂ r19) ∗
      (∃∗ r23 : BitVec 8, (r + 23#64) ↦₈ r23) ∗
      (∃∗ r24 : BitVec 16, (r + 24#64) ↦₁₆ r24) ∗
      (∃∗ r26 : BitVec 8, (r + 26#64) ↦₈ r26) ∗
      (∃∗ r27 : BitVec 64, (r + 27#64) ↦₆₄ r27) ∗
      (∃∗ r35 : BitVec 8, (r + 35#64) ↦₈ r35) ∗
      (∃∗ r36 : BitVec 32, (r + 36#64) ↦₃₂ r36) := by
  rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split r 4 36 (by decide),
      mr_add_split r 4 4 32 8 36 rfl rfl (by decide),
      mr_add_split r 8 8 24 16 32 rfl rfl (by decide),
      mr_add_split r 16 2 22 18 24 rfl rfl (by decide),
      mr_add_split r 18 1 21 19 22 rfl rfl (by decide),
      mr_add_split r 19 4 17 23 21 rfl rfl (by decide),
      mr_add_split r 23 1 16 24 17 rfl rfl (by decide),
      mr_add_split r 24 2 14 26 16 rfl rfl (by decide),
      mr_add_split r 26 1 13 27 14 rfl rfl (by decide),
      mr_add_split r 27 8 5 35 13 rfl rfl (by decide),
      mr_add_split r 35 1 4 36 5 rfl rfl (by decide),
      memRegion_four r, memRegion_four (r + 4#64), memRegion_eight (r + 8#64),
      memRegion_two (r + 16#64), memRegion_one (r + 18#64), memRegion_four (r + 19#64),
      memRegion_one (r + 23#64), memRegion_two (r + 24#64), memRegion_one (r + 26#64),
      memRegion_eight (r + 27#64), memRegion_one (r + 35#64), memRegion_four (r + 36#64)]

private theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem pointsToBytes_combine (a : BitVec 64) (xs ys : List (BitVec 8))
    {a' : BitVec 64} (ha : a + BitVec.ofNat 64 xs.length = a') :
    (a ↦ₛ xs) ∗ (a' ↦ₛ ys) = (a ↦ₛ (xs ++ ys)) := by
  subst ha
  exact (pointsToBytes_append a xs ys).symm

private theorem sp_11_repack_aux (a : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8) (v7 : BitVec 64) :
    (a ↦₁₆ v4) ∗ ((a + 2#64) ↦₈ v6) ∗ ((a + 3#64) ↦₆₄ v7) =
      (a ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
      ((a + 8#64) ↦₁₆ (v7.extractLsb' 40 16)) ∗
      ((a + 10#64) ↦₈ (v7.extractLsb' 56 8)) := by
  rw [pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes, pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1]
  rw [← sepConj_assoc, pointsToBytes_combine a (unpack16 v4) [v6] (by rfl),
      pointsToBytes_combine a (unpack16 v4 ++ [v6]) (unpack64 v7) (by rfl)]
  rw [← sepConj_assoc,
      pointsToBytes_combine a (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4))
        (unpack16 (v7.extractLsb' 40 16)) (by rfl),
      pointsToBytes_combine a
        (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4) ++ unpack16 (v7.extractLsb' 40 16))
        [v7.extractLsb' 56 8] (by rfl)]
  congr 1
  simp only [unpack16, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

theorem sp_11_repack (sp : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8) (v7 : BitVec 64) :
    ((sp - 80#64) ↦₁₆ v4) ∗ ((sp - 78#64) ↦₈ v6) ∗ ((sp - 77#64) ↦₆₄ v7) =
      ((sp - 80#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
      ((sp - 72#64) ↦₁₆ (v7.extractLsb' 40 16)) ∗
      ((sp - 70#64) ↦₈ (v7.extractLsb' 56 8)) := by
  have h78 : (sp - 80#64) + 2#64 = sp - 78#64 := by bv_omega
  have h77 : (sp - 80#64) + 3#64 = sp - 77#64 := by bv_omega
  have h72 : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
  have h70 : (sp - 80#64) + 10#64 = sp - 70#64 := by bv_omega
  rw [← h78, ← h77, ← h72, ← h70]
  exact sp_11_repack_aux (sp - 80#64) v4 v6 v7

theorem sp_11_repack_rest (sp : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8)
    (v7 : BitVec 64) (R : SepProp) :
    ((sp - 80#64) ↦₁₆ v4) ∗ ((sp - 78#64) ↦₈ v6) ∗ ((sp - 77#64) ↦₆₄ v7) ∗ R =
      ((sp - 80#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
      ((sp - 72#64) ↦₁₆ (v7.extractLsb' 40 16)) ∗
      ((sp - 70#64) ↦₈ (v7.extractLsb' 56 8)) ∗ R := by
  have h := congrArg (· ∗ R) (sp_11_repack sp v4 v6 v7)
  simpa only [sepConj_assoc] using h

private theorem ret_11_repack (a : BitVec 64) (v4 : BitVec 16) (v6 : BitVec 8) (v7 : BitVec 64) :
    ((a + 8#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
    ((a + 16#64) ↦₁₆ (((v7 >>> 40).truncate 32).truncate 16)) ∗
    ((a + 18#64) ↦₈ ((BitVec.zeroExtend 64 ((v7 >>> 40).truncate 32) >>> 16).truncate 8)) =
      ((a + 8#64) ↦₁₆ v4) ∗ ((a + 10#64) ↦₈ v6) ∗ ((a + 11#64) ↦₆₄ v7) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1,
      pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes]
  rw [← sepConj_assoc,
      pointsToBytes_combine (a + 8#64) (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4))
        (unpack16 (((v7 >>> 40).truncate 32).truncate 16)) (by rw [BitVec.add_assoc]; rfl),
      pointsToBytes_combine (a + 8#64)
        (unpack64 (v7.extractLsb' 0 40 ++ v6 ++ v4) ++
          unpack16 (((v7 >>> 40).truncate 32).truncate 16))
        [(BitVec.zeroExtend 64 ((v7 >>> 40).truncate 32) >>> 16).truncate 8] (by rw [BitVec.add_assoc]; rfl)]
  rw [← sepConj_assoc,
      pointsToBytes_combine (a + 8#64) (unpack16 v4) [v6] (by rw [BitVec.add_assoc]; rfl),
      pointsToBytes_combine (a + 8#64) (unpack16 v4 ++ [v6]) (unpack64 v7) (by rw [BitVec.add_assoc]; rfl)]
  congr 1
  simp only [unpack16, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

private theorem ret_8_repack (a : BitVec 64) (v15 : BitVec 64) :
    ((a + 19#64) ↦₃₂ (v15.truncate 32)) ∗
    ((a + 23#64) ↦₈ ((v15 >>> 32).truncate 8)) ∗
    ((a + 24#64) ↦₁₆ (((v15 >>> 40).truncate 32).truncate 16)) ∗
    ((a + 26#64) ↦₈ ((BitVec.zeroExtend 64 ((v15 >>> 40).truncate 32) >>> 16).truncate 8)) =
      ((a + 19#64) ↦₆₄ v15) := by
  rw [pointsTo32_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1,
      pointsTo16_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes]
  rw [← sepConj_assoc,
      pointsToBytes_combine (a + 19#64) (unpack32 (v15.truncate 32))
        [((v15 >>> 32).truncate 8)] (by rw [BitVec.add_assoc]; rfl),
      ← sepConj_assoc,
      pointsToBytes_combine (a + 19#64)
        (unpack32 (v15.truncate 32) ++ [((v15 >>> 32).truncate 8)])
        (unpack16 (((v15 >>> 40).truncate 32).truncate 16)) (by rw [BitVec.add_assoc]; rfl),
      pointsToBytes_combine (a + 19#64)
        (unpack32 (v15.truncate 32) ++ [((v15 >>> 32).truncate 8)] ++
          unpack16 (((v15 >>> 40).truncate 32).truncate 16))
        [(BitVec.zeroExtend 64 ((v15 >>> 40).truncate 32) >>> 16).truncate 8] (by rw [BitVec.add_assoc]; rfl)]
  congr 1
  simp only [unpack32, unpack16, unpack64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

def findReceiverChainKeyKeyChunks (a : BitVec 64) (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₁₆ v4) ∗ ((a + 6#64) ↦₈ v6) ∗
  ((a + 7#64) ↦₆₄ v7) ∗ ((a + 15#64) ↦₆₄ v15) ∗
  ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

namespace FindReceiverChainKeyFacts

theorem unpack32_16_8_eq (w0 : BitVec 64) :
    unpack32 (w0.extractLsb' 0 32) ++ unpack16 (w0.extractLsb' 32 16) ++ [w0.extractLsb' 48 8] =
      [w0.extractLsb' 0 8, w0.extractLsb' 8 8, w0.extractLsb' 16 8, w0.extractLsb' 24 8,
       w0.extractLsb' 32 8, w0.extractLsb' 40 8, w0.extractLsb' 48 8] := by
  simp only [unpack32, unpack16, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

theorem unpack64_shift8 (lo hi : BitVec 64) :
    unpack64 (hi.extractLsb' 0 56 ++ lo.extractLsb' 56 8) =
      [lo.extractLsb' 56 8, hi.extractLsb' 0 8, hi.extractLsb' 8 8, hi.extractLsb' 16 8,
       hi.extractLsb' 24 8, hi.extractLsb' 32 8, hi.extractLsb' 40 8, hi.extractLsb' 48 8] := by
  simp only [unpack64, List.cons.injEq, and_true]
  repeat (first | refine ⟨by first | rfl | bv_bits, ?_⟩ | first | rfl | bv_bits)

theorem findReceiverChainKeyResultAt_some_perm (p0 p4 p8 p16 p18 p19 p23 p24 p26 p27 p35 p36 p8' p10' p11' p19' : SepProp)
    (h11 : p8 ∗ p16 ∗ p18 = p8' ∗ p10' ∗ p11')
    (h8 : p19 ∗ p23 ∗ p24 ∗ p26 = p19') :
    p0 ∗ p4 ∗ p8 ∗ p16 ∗ p18 ∗ p19 ∗ p23 ∗ p24 ∗ p26 ∗ p27 ∗ p35 ∗ p36 =
      p0 ∗ ((p4 ∗ p8' ∗ p10' ∗ p11' ∗ p19' ∗ p27 ∗ p35) ∗ p36) := by
  have h1 : p8 ∗ (p16 ∗ (p18 ∗ (p19 ∗ (p23 ∗ (p24 ∗ (p26 ∗ (p27 ∗ (p35 ∗ p36)))))))) =
      p8' ∗ (p10' ∗ (p11' ∗ (p19' ∗ (p27 ∗ (p35 ∗ p36))))) := by
    have := congrArg₂ (· ∗ ·) h11 (congrArg (· ∗ (p27 ∗ (p35 ∗ p36))) h8)
    simpa only [sepConj_assoc] using this
  simpa only [sepConj_assoc] using congrArg (fun X => p0 ∗ (p4 ∗ X)) h1

end FindReceiverChainKeyFacts

theorem cells4_eq_findReceiverChainKeyKeyChunks (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) =
      findReceiverChainKeyKeyChunks a
        (w0.extractLsb' 0 32)
        (w0.extractLsb' 32 16)
        (w0.extractLsb' 48 8)
        (w1.extractLsb' 0 56 ++ w0.extractLsb' 56 8)
        (w2.extractLsb' 0 56 ++ w1.extractLsb' 56 8)
        (w3.extractLsb' 0 56 ++ w2.extractLsb' 56 8)
        (w3.extractLsb' 56 8) := by
  unfold findReceiverChainKeyKeyChunks
  rw [pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo16_eq_pointsToBytes,
      pointsTo8_eq_pointsToBytes1, pointsTo64_eq_pointsToBytes, pointsTo64_eq_pointsToBytes,
      pointsTo64_eq_pointsToBytes, pointsTo8_eq_pointsToBytes1]
  rw [← sepConj_assoc, pointsToBytes_combine a (unpack64 w0) (unpack64 w1) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a (unpack64 w0 ++ unpack64 w1) (unpack64 w2) (by rfl),
      pointsToBytes_combine a (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2) (unpack64 w3) (by rfl)]
  rw [← sepConj_assoc, pointsToBytes_combine a (unpack32 (w0.extractLsb' 0 32)) (unpack16 (w0.extractLsb' 32 16)) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ [w0.extractLsb' 48 8] (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ (unpack64 (w1.extractLsb' 0 56 ++ w0.extractLsb' 56 8)) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ (unpack64 (w2.extractLsb' 0 56 ++ w1.extractLsb' 56 8)) (by rfl),
      ← sepConj_assoc, pointsToBytes_combine a _ (unpack64 (w3.extractLsb' 0 56 ++ w2.extractLsb' 56 8)) (by rfl),
      pointsToBytes_combine a _ [w3.extractLsb' 56 8] (by rfl)]
  rw [FindReceiverChainKeyFacts.unpack32_16_8_eq w0, FindReceiverChainKeyFacts.unpack64_shift8 w0 w1, FindReceiverChainKeyFacts.unpack64_shift8 w1 w2, FindReceiverChainKeyFacts.unpack64_shift8 w2 w3]
  rfl

theorem exists_findReceiverChainKeyKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8)
      (v7 v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = findReceiverChainKeyKeyChunks a v0 v4 v6 v7 v15 v23 v31 := by
  obtain ⟨w0, w1, w2, w3, _, hw⟩ := exists_unpack64_of_length_32 h
  exact ⟨_, _, _, _, _, _, _, fun a => (hw a).trans (cells4_eq_findReceiverChainKeyKeyChunks a w0 w1 w2 w3)⟩

theorem findReceiverChainKeyResultAt_some_repack (r : BitVec 64) (ck : ChainKey)
    (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (v31 : BitVec 8)
    (hkey : ∀ a : BitVec 64, (a ↦ₛ keyToBytes32 ck.key) = findReceiverChainKeyKeyChunks a v0 v4 v6 v7 v15 v23 v31) :
    (r ↦₃₂ 1#32) ∗
    ((r + 4#64) ↦₃₂ v0) ∗
    ((r + 8#64) ↦₆₄ (v7.extractLsb' 0 40 ++ v6 ++ v4)) ∗
    ((r + 16#64) ↦₁₆ (((v7 >>> 40).truncate 32).truncate 16)) ∗
    ((r + 18#64) ↦₈ ((BitVec.zeroExtend 64 ((v7 >>> 40).truncate 32) >>> 16).truncate 8)) ∗
    ((r + 19#64) ↦₃₂ (v15.truncate 32)) ∗
    ((r + 23#64) ↦₈ ((v15 >>> 32).truncate 8)) ∗
    ((r + 24#64) ↦₁₆ (((v15 >>> 40).truncate 32).truncate 16)) ∗
    ((r + 26#64) ↦₈ ((BitVec.zeroExtend 64 ((v15 >>> 40).truncate 32) >>> 16).truncate 8)) ∗
    ((r + 27#64) ↦₆₄ v23) ∗
    ((r + 35#64) ↦₈ v31) ∗
    ((r + 36#64) ↦₃₂ ck.index) =
      findReceiverChainKeyResultAt r (.ok (some ck)) := by
  dsimp only [findReceiverChainKeyResultAt]
  rw [pointsToBytes_chainKeyBytes_eq (r + 4#64) ck,
      show r + 4#64 + 32#64 = r + 36#64 by bv_omega,
      hkey (r + 4#64)]
  unfold findReceiverChainKeyKeyChunks
  rw [show r + 4#64 + 4#64 = r + 8#64 by bv_omega,
      show r + 4#64 + 6#64 = r + 10#64 by bv_omega,
      show r + 4#64 + 7#64 = r + 11#64 by bv_omega,
      show r + 4#64 + 15#64 = r + 19#64 by bv_omega,
      show r + 4#64 + 23#64 = r + 27#64 by bv_omega,
      show r + 4#64 + 31#64 = r + 35#64 by bv_omega]
  exact FindReceiverChainKeyFacts.findReceiverChainKeyResultAt_some_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ret_11_repack r v4 v6 v7) (ret_8_repack r v15)

theorem findReceiverChainKeyResultAt_err_repack (r p : BitVec 64) :
    (r ↦₃₂ 2#32) ∗
    memRegion (r + 4#64) 4 ∗
    ((r + 8#64) ↦₆₄ p) ∗
    ((r + 16#64) ↦₆₄ 26#64) ∗
    memRegion (r + 24#64) 16 ∗
    (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ⊢
      findReceiverChainKeyResultAt r (.error (.invalidSessionStructure .missingReceiverChainKey)) := by
  dsimp only [findReceiverChainKeyResultAt, strRefAt]
  have hlen : BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length = 26#64 := by rfl_kernel
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  rw [hlen, ha16]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro p))))
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

/-! ## 4. Pure Model & Subroutine Helpers -/

theorem zip_map_snd {α β : Type} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (xs.zip ys).map (·.2) = ys
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [List.zip_cons_cons, zip_map_snd xs ys h]

theorem zip_length_eq {α β : Type} {xs : List α} {ys : List β}
    (h : xs.length = ys.length) :
    (xs.zip ys).length = ys.length := by
  simp [List.length_zip, h]

theorem findIdx_q_go_lt_shared_lb {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (k idx : Nat), List.findIdx?.go p xs k = some idx → idx < k + xs.length
  | [], _, _, h => by simp [List.findIdx?.go] at h
  | _ :: xs, k, idx, h => by
    simp only [List.findIdx?.go] at h
    split at h
    · injection h with h; subst h; simp only [List.length_cons]; omega
    · have ih := findIdx_q_go_lt_shared_lb p xs (k + 1) idx h
      simp only [List.length_cons]; omega

theorem findReceiverChainIndex_lt {st : RatchetState} {their : PublicKey} {idx : Nat}
    (h : st.findReceiverChainIndex their = some idx) :
    idx < st.receiverChains.length := by
  unfold RatchetState.findReceiverChainIndex List.findIdx? at h
  have := findIdx_q_go_lt_shared_lb (fun c => c.senderRatchetKey == their) st.receiverChains 0 idx h
  omega

theorem receiverChains_getElem?_eq_zip_snd {G : RatchetGhost} {st : RatchetState}
    (hlen : G.chains.length = st.receiverChains.length)
    {idx : Nat} (hidx : idx < (G.chains.zip st.receiverChains).length) :
    st.receiverChains[idx]? = some ((G.chains.zip st.receiverChains)[idx]).2 := by
  have hidx' : idx < st.receiverChains.length := by rwa [zip_length_eq hlen] at hidx
  rw [List.getElem?_eq_getElem hidx']
  simp [List.getElem_zip]

theorem findReceiverChainKey_of_none {st : RatchetState} {their : PublicKey}
    (h : st.findReceiverChainIndex their = none) :
    st.findReceiverChainKey their = .ok none := by
  simp [RatchetState.findReceiverChainKey, h]

theorem findReceiverChainKey_of_some_none {G : RatchetGhost} {st : RatchetState}
    {their : PublicKey} {idx : Nat}
    (hlen : G.chains.length = st.receiverChains.length)
    (hfind : st.findReceiverChainIndex their = some idx)
    (hidx : idx < (G.chains.zip st.receiverChains).length)
    (hck : ((G.chains.zip st.receiverChains)[idx]).2.chainKey = none) :
    st.findReceiverChainKey their =
      .error (.invalidSessionStructure .missingReceiverChainKey) := by
  unfold RatchetState.findReceiverChainKey
  rw [hfind]; dsimp only; rw [receiverChains_getElem?_eq_zip_snd hlen hidx]; dsimp only; rw [hck]

theorem findReceiverChainKey_of_some_some {G : RatchetGhost} {st : RatchetState}
    {their : PublicKey} {idx : Nat} {ck : ChainKey}
    (hlen : G.chains.length = st.receiverChains.length)
    (hfind : st.findReceiverChainIndex their = some idx)
    (hidx : idx < (G.chains.zip st.receiverChains).length)
    (hck : ((G.chains.zip st.receiverChains)[idx]).2.chainKey = some ck) :
    st.findReceiverChainKey their = .ok (some ck) := by
  unfold RatchetState.findReceiverChainKey
  rw [hfind]; dsimp only; rw [receiverChains_getElem?_eq_zip_snd hlen hidx]; dsimp only; rw [hck]

@[local arm64_norm]
theorem mul_104_eq (i : Nat) :
    BitVec.ofNat 64 i * 104#64 = BitVec.ofNat 64 (i * 104) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, BitVec.toNat_ofNat]

@[local arm64_norm]
theorem setWidth_32_16_of_64 (v : BitVec 16) :
    ((BitVec.setWidth 64 v).setWidth 32).setWidth 16 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_32_8_of_64 (v : BitVec 8) :
    ((BitVec.setWidth 64 v).setWidth 32).setWidth 8 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_16_of_64 (v : BitVec 16) :
    (BitVec.setWidth 64 v).setWidth 16 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_8_of_64 (v : BitVec 8) :
    (BitVec.setWidth 64 v).setWidth 8 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_32_of_64 (v : BitVec 32) :
    (BitVec.setWidth 64 v).setWidth 32 = v := by bv_bits

@[local arm64_norm]
theorem setWidth_16_of_32 (v : BitVec 16) :
    (BitVec.setWidth 32 v).setWidth 16 = v := by bv_bits

@[local arm64_norm]
private theorem setWidth_8_of_32 (v : BitVec 8) :
    (BitVec.setWidth 32 v).setWidth 8 = v := by bv_bits

theorem len_ule_idx_false {i n : Nat} (hi : i < n) (hn : n * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
  exact decide_eq_false (by omega)

private theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

private theorem findIndex_ok_at_findReceiverChainKey {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {A : RustAlloc}
    (himg : Obj.Loads libsignalSessionImage img)
    (hfind : FindIndexOk img F alloc A) :
    subroutine_ok (SP_findReceiverChainKey img.base F alloc)
      ((SP_findReceiverChainKey img.base F alloc).fnAddr findReceiverChainKeyName + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"))
      ((findIndexSpec img A).inImage img) := by
  unfold FindIndexOk at hfind
  rw [show sessionProg img F alloc = SP_findReceiverChainKey img.base F alloc from libsignalSessionCode_ofImage himg] at hfind
  have haddr : (SP_findReceiverChainKey img.base F alloc).fnAddr findReceiverChainKeyName + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key") = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key"), BitVec.add_assoc]; rfl
  rwa [haddr]

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left; intro hp; rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

private theorem findIndex_ok_at_state {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {A : RustAlloc} {img : Obj.Image}
    {addr : BitVec 64} {s : State}
    (hfind : subroutine_ok (SP_findReceiverChainKey b F alloc) addr ((findIndexSpec img A).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP_findReceiverChainKey b F alloc) addr
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (findIndexSpec img A).post } := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp
  refine hfind.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, findIndexSpec]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

private theorem SepWPp.conseq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem SepWPp_eq_pre_shared_lb {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h
private abbrev SepWPp.eq_pre := @SepWPp_eq_pre_shared_lb

theorem SepWPp_intro_rodata_missingReceiverChainKey_shared_lb {prog : Program} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s)
    (h : SepWPp prog ret s (((img.base + bv% (ls_str% "missing receiver chain key")) ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  unfold Obj.Image.FrozenLoaded at hfrozen
  have hm' : s.mem ⊨ (((img.base + bv% (ls_str% "missing receiver chain key")) ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact rodata_missingReceiverChainKey_intro himg hfrozen.2.1 hm
  exact h R hm' hL
private abbrev SepWPp.intro_rodata_missingReceiverChainKey := @SepWPp_intro_rodata_missingReceiverChainKey_shared_lb

namespace FindReceiverChainKeyFacts

theorem findIndex_ok_at_state_prog {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {addr : BitVec 64} {s : State}
    (hfind : subroutine_ok prog addr ((findIndexSpec img A).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok prog addr
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (findIndexSpec img A).post } := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp
  refine hfind.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, findIndexSpec]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem ratchet_reassemble_chain {P8 P16 Ch Chain Rest Tail Rat : SepProp}
    (hch : Ch ⊢ Chain)
    (hrat : P8 ∗ P16 ∗ (Chain ∗ Rest) ∗ Tail ⊢ Rat) :
    P8 ∗ P16 ∗ Ch ∗ Rest ∗ Tail ⊢ Rat := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hch))) ?_
  exact entails_of_eq (by ac_rfl) hrat

theorem stack_reassemble_scr {M944 S1024 Scr M32 Rest Stk : SepProp}
    (hscr : Scr ⊢ M32)
    (hstk : M944 ∗ S1024 ∗ M32 ∗ Rest ⊢ Stk) :
    M944 ∗ S1024 ∗ Scr ∗ Rest ⊢ Stk :=
  Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))) hstk

end FindReceiverChainKeyFacts

/-! ## 5. Main Proof -/

attribute [local irreducible] Program.fnOff

theorem findReceiverChainKey_ok_sessionProg {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hfind : FindIndexOk img F abs A) :
    subroutine_ok (sessionProg img F abs)
      ((SP_findReceiverChainKey img.base F abs).fnAddr findReceiverChainKeyName) (findReceiverChainKeySpec A img) := by
  rw [show sessionProg img F abs = SP_findReceiverChainKey img.base F abs from libsignalSessionCode_ofImage himg]
  have hfn := FindReceiverChainKeyFacts.findReceiverChainKey_fnOff
  have hfind_at := findIndex_ok_at_findReceiverChainKey himg hfind
  have hadrp : ((((SP_findReceiverChainKey img.base F abs).fnAddr findReceiverChainKeyName) + 272#64) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_str% "missing receiver chain key" - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296)) =
      img.base + bv% (ls_str% "missing receiver chain key") := by
    apply adrp_missingReceiverChainKey himg; rw [Program.fnAddr_rebase, hfn]
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0
  simp only [findReceiverChainKeySpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen0, hsym0⟩, ⟨hx0, hx1, hx8⟩, hmem⟩
  refine ⟨ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
    logOff img ∗ stackAt s0.sp findReceiverChainKeyStack, R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  apply SepWPp.conseq_pre (sepConj_mono_left (ratchetAt_expose_findIndex A x.self x.G x.st))
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hcs_lt⟩ => ?_
  set cs := x.G.chains.zip x.st.receiverChains
  have hcs_toNat : (BitVec.ofNat 64 cs.length).toNat = cs.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  unfold logOff; rw [stackAt_findReceiverChainKeyStack s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v29 => ?_
  dsimp only [SP_findReceiverChainKey] at hpc hfind_at hadrp ⊢
  findReceiverChainKey_fetches img.base (Rust.withPanics (sessionExterns F abs))
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (sessionExterns F abs))).fnAddr findReceiverChainKeyName = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics (sessionExterns F abs))) = prog reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  apply SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_key")) hfrozen0 hsym0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hfrozen1 hsym1
  have hfind1 := FindReceiverChainKeyFacts.findIndex_ok_at_state_prog hfind_at hfrozen1 hsym1
  apply SepWPp.of_sepWP_frozen (mid := entry + bv% (44)) hfrozen1 hsym1
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hfrozen2 hsym2
  have hmap_cs : cs.map (·.2) = x.st.receiverChains :=
    zip_map_snd x.G.chains x.st.receiverChains hchains_len
  have hidx_post : match x.st.findReceiverChainIndex x.their with
      | some i => sf.readReg64 (Reg.gpr 0#5) = 1#64 ∧ (sf.readReg64 (Reg.gpr 1#5)).toNat = i
      | none => sf.readReg64 (Reg.gpr 0#5) = 0#64 := by
    have h := hpost; rw [hmap_cs] at h; exact h
  cases hfind_res : x.st.findReceiverChainIndex x.their with
  | none =>
    rw [hfind_res] at hidx_post; dsimp only at hidx_post
    rw [memRegion40_unpack_none x.ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun t0 => ?_
    apply SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen2 hsym2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro _ _
    refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    rw [findReceiverChainKey_of_none hfind_res]; dsimp only [findReceiverChainKeyResultAt, logOff]
    refine Entails.pure_right (by simp only [wp_norm, arm64_norm, *]) ?_
    have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
    have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
    refine Entails.trans ?_
      (sepConj_mono hrat (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
    exact entails_of_eq (by dsimp only [cs, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
      (Entails.refl _)
  | some i =>
    rw [hfind_res] at hidx_post; rcases hidx_post with ⟨hx0_1, hx1_1⟩
    have hi_rc : i < x.st.receiverChains.length := findReceiverChainIndex_lt hfind_res
    have hi : i < cs.length := by rwa [zip_length_eq hchains_len]
    have hx1_eq : sf.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; rw [hx1_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hule : (BitVec.ofNat 64 cs.length).ule (BitVec.ofNat 64 i) = false :=
      len_ule_idx_false hi hcs_lt
    rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi]
    set elemAddr := x.G.chainsPtr + BitVec.ofNat 64 (i * 104)
    cases hck : cs[i].2.chainKey with
    | none =>
      rw [chainAt_none_expose A cs[i] elemAddr hck, memRegion40_unpack_err x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun p0 =>
        SepWPp.exists_elim fun t0 => ?_
      apply SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen2 hsym2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hfrozen3 _
      apply SepWPp.intro_rodata_missingReceiverChainKey himg hfrozen3
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_none hchains_len hfind_res hi hck]; dsimp only [logOff]
      refine Entails.pure_right (by simp only [wp_norm, arm64_norm, *]) ?_
      have herr := findReceiverChainKeyResultAt_err_repack x.ret (img.base + bv% (ls_str% "missing receiver chain key"))
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi,
          chainAt_none_expose A cs[i] elemAddr hck] at hrat
      refine Entails.trans ?_
        (sepConj_mono hrat (sepConj_mono_right (sepConj_mono herr (sepConj_mono_right hstk))))
      exact entails_of_eq (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
        (Entails.refl _)
    | some ck =>
      apply SepWPp.conseq_pre
        (sepConj_mono_left (sepConj_mono_left (chainAt_some_expose A cs[i] ck elemAddr hck)))
      apply SepWPp.eq_pre (by simp only [sepConj_assoc]; rfl)
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hcap_lt
      have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
      obtain ⟨v0, v4, v6, v7, v15, v23, v31, hkey⟩ :=
        exists_findReceiverChainKeyKeyChunks_of_length_32 hlen_key
      rw [hkey cs[i].1.ck.ptr]; unfold findReceiverChainKeyKeyChunks
      rw [sp_scratch32_unpack s0.sp, memRegion40_unpack_some x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun r36 => SepWPp.exists_elim fun r35 =>
        SepWPp.exists_elim fun r27 => SepWPp.exists_elim fun r26 =>
        SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r23 =>
        SepWPp.exists_elim fun r19 => SepWPp.exists_elim fun r18 =>
        SepWPp.exists_elim fun r16 => SepWPp.exists_elim fun r8 =>
        SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r0 =>
        SepWPp.exists_elim fun s24 => SepWPp.exists_elim fun s16 =>
        SepWPp.exists_elim fun s3 => SepWPp.exists_elim fun s2 =>
        SepWPp.exists_elim fun s0_scr => ?_
      apply SepWPp.of_sepWP_frozen (mid := entry + bv% (156)) hfrozen2 hsym2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hfrozen3 hsym3
      apply SepWPp.eq_pre (by simp only [sepConj_assoc, sp_11_repack_rest s0.sp v4 v6 v7]; rfl)
      apply SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen3 hsym3
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro _ _
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_some hchains_len hfind_res hi hck]; dsimp only [logOff]
      refine Entails.pure_right (by simp only [wp_norm, arm64_norm, *]) ?_
      have hres := findReceiverChainKeyResultAt_some_repack x.ret ck v0 v4 v6 v7 v15 v23 v31 hkey
      have hscr := sp_scratch32_repack s0.sp
        (v7.extractLsb' 0 40 ++ v6 ++ v4) (v7.extractLsb' 40 16) (v7.extractLsb' 56 8) v23 v31
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      have hch := chainAt_some_reassemble A cs[i] ck elemAddr hck
      rw [hkey cs[i].1.ck.ptr] at hch; unfold findReceiverChainKeyKeyChunks at hch
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi] at hrat
      have hrat' := FindReceiverChainKeyFacts.ratchet_reassemble_chain hch hrat
      have hstk' := FindReceiverChainKeyFacts.stack_reassemble_scr hscr hstk
      rw [← hres]
      refine Entails.trans ?_
        (sepConj_mono hrat' (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk'))))
      exact entails_of_eq
        (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
        (Entails.refl _)

theorem findReceiverChainKey_ok_of_findIndex_ext
    {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {abs ext : String → Option (State → State)}
    (hfind : FindIndexOk img F abs A)
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    (hloads : Obj.Loads libsignalSessionImage img) :
    FindReceiverChainKeyOkExt img A ext := by
  unfold FindReceiverChainKeyOkExt
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr findReceiverChainKeyName =
      (SP_findReceiverChainKey img.base F abs).fnAddr findReceiverChainKeyName := by
    simp only [tripleRatchetProgAtExt, SP_findReceiverChainKey, Program.fnAddr_rebase]
  rw [hfn]
  exact ConsumeMessageKeyTransfer.session_subroutine_ok_mono_ext hloads hle (findReceiverChainKey_ok_sessionProg hloads hfind)

theorem findReceiverChainKey_ok_ext
    {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {abs ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    (hloads : Obj.Loads libsignalSessionImage img) :
    FindReceiverChainKeyOkExt img A ext :=
  findReceiverChainKey_ok_of_findIndex_ext (find_receiver_chain_index_ok img F abs A hloads) hle hloads

theorem findReceiverChainKey_ok_of_findIndex
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hfind : FindIndexOk img C.F abs A)
    (hloads : Obj.Loads libsignalSessionImage img) :
    FindReceiverChainKeyOk img C A ctl abs :=
  findReceiverChainKey_ok_of_findIndex_ext hfind (ConsumeMessageKeyTransfer.sessionExterns_le C ctl abs) hloads

/-- `RatchetState::find_receiver_chain_key` satisfies `FindReceiverChainKeyOk` on
`tripleRatchetProgAt`. -/
theorem findReceiverChainKey_ok
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img) :
    FindReceiverChainKeyOk img C A ctl abs :=
  findReceiverChainKey_ok_of_findIndex (find_receiver_chain_index_ok img C.F abs A hloads) hloads

/-! ## 6. Relocatable `[LibsignalPlacement]` Contract (Block `25`) -/

def findReceiverChainKeyPlacedSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec FindReceiverChainKeyGhost where
  pre := fun x s =>
    ⌜LibsignalRoLoaded lsmpl s.mem ∧
      s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
    ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s.sp findReceiverChainKeyStack
  post := fun x s0 sf =>
    ⌜LibsignalRoLoaded lsmpl sf.mem ∧ sf.trace = s0.trace⌝ ∗
    ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
    findReceiverChainKeyResultAt x.ret (x.st.findReceiverChainKey x.their) ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp findReceiverChainKeyStack

private theorem sepWPp_seq_lscl_ro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem ∧ LibsignalRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen
    (fun (m _ : Memory) (hf : LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m) hkf =>
      ⟨hf.1.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hf.2 hkf⟩)
    ⟨hcl, hro⟩
    h

private theorem sepWPp_intro_rodata_missingReceiverChainKey_placed [LibsignalPlacement]
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (h : SepWPp prog ret s
      (((lsmpl.ρ "libsignal_protocol:.rodata..Lanon.290") ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ P)
      Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (((lsmpl.ρ "libsignal_protocol:.rodata..Lanon.290") ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact lsro_intro_chk hro (by decide +kernel) hm
  exact h R hm' hL

private theorem findIndex_placed_ok_at_state [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {addr : BitVec 64} {s : State}
    (hfind : subroutine_ok prog addr (withLsCodeLoaded lsmpl (FindReceiverChainIndex.findPlacedSpec A)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (FindReceiverChainIndex.findPlacedSpec A).post } := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨p, cs, theirA, their⟩ R s0 hpc hrun hm hsp
  refine hfind.mono_outcome (p, cs, theirA, their) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded, FindReceiverChainIndex.findPlacedSpec] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hx0, hx1, hx2, hlt⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx2, hlt, hsp⟩, hspatial⟩

set_option maxHeartbeats 1600000 in
theorem find_receiver_chain_key_placed_ok_of_find_index [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hfind : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (lsmpl.base 26)
      (withLsCodeLoaded lsmpl (FindReceiverChainIndex.findPlacedSpec A))) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [findReceiverChainKeyPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hro0, hx0, hx1, hx8⟩, hmem⟩
  refine ⟨ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ret 40 ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp findReceiverChainKeyStack, R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  apply SepWPp.conseq_pre (sepConj_mono_left (ratchetAt_expose_findIndex A x.self x.G x.st))
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hcs_lt⟩ => ?_
  set cs := x.G.chains.zip x.st.receiverChains
  have hcs_toNat : (BitVec.ofNat 64 cs.length).toNat = cs.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [stackAt_findReceiverChainKeyStack s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v19 => SepWPp.exists_elim fun v20 =>
    SepWPp.exists_elim fun v21 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v29 => ?_
  apply sepWPp_seq_lscl_ro (mid := lsmpl.base 26) hcl0 hro0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro ⟨hcl1, hro1⟩
  have hfind1 := findIndex_placed_ok_at_state hfind hcl1
  apply sepWPp_seq_lscl_ro (mid := (blkPl_25).base + 44#64) hcl1 hro1
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro ⟨hcl2, hro2⟩
  have hmap_cs : cs.map (·.2) = x.st.receiverChains :=
    zip_map_snd x.G.chains x.st.receiverChains hchains_len
  have hidx_post : match x.st.findReceiverChainIndex x.their with
      | some i => sf.readReg64 (Reg.gpr 0#5) = 1#64 ∧ (sf.readReg64 (Reg.gpr 1#5)).toNat = i
      | none => sf.readReg64 (Reg.gpr 0#5) = 0#64 := by
    have h := hpost; rw [hmap_cs] at h; exact h
  cases hfind_res : x.st.findReceiverChainIndex x.their with
  | none =>
    rw [hfind_res] at hidx_post; dsimp only at hidx_post
    rw [memRegion40_unpack_none x.ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun t0 => ?_
    apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl2 hro2
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro ⟨_, hro3⟩
    refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    rw [findReceiverChainKey_of_none hfind_res]; dsimp only [findReceiverChainKeyResultAt]
    refine Entails.pure_right ⟨hro3, by simp only [wp_norm, arm64_norm, *]⟩ ?_
    have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
    have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
      (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
    refine Entails.trans ?_
      (sepConj_mono hrat (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk))))
    exact entails_of_eq (by dsimp only [cs, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
      (Entails.refl _)
  | some i =>
    rw [hfind_res] at hidx_post; rcases hidx_post with ⟨hx0_1, hx1_1⟩
    have hi_rc : i < x.st.receiverChains.length := findReceiverChainIndex_lt hfind_res
    have hi : i < cs.length := by rwa [zip_length_eq hchains_len]
    have hx1_eq : sf.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; rw [hx1_1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hule : (BitVec.ofNat 64 cs.length).ule (BitVec.ofNat 64 i) = false :=
      len_ule_idx_false hi hcs_lt
    rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi]
    set elemAddr := x.G.chainsPtr + BitVec.ofNat 64 (i * 104)
    cases hck : cs[i].2.chainKey with
    | none =>
      rw [chainAt_none_expose A cs[i] elemAddr hck, memRegion40_unpack_err x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun p0 =>
        SepWPp.exists_elim fun t0 => ?_
      apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl2 hro2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro ⟨_, hro3⟩
      apply sepWPp_intro_rodata_missingReceiverChainKey_placed hro3
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_none hchains_len hfind_res hi hck]
      refine Entails.pure_right ⟨hro3, by simp only [wp_norm, arm64_norm, *]⟩ ?_
      have herr := findReceiverChainKeyResultAt_err_repack x.ret (lsmpl.ρ "libsignal_protocol:.rodata..Lanon.290")
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi,
          chainAt_none_expose A cs[i] elemAddr hck] at hrat
      refine Entails.trans ?_
        (sepConj_mono hrat (sepConj_mono_right (sepConj_mono herr (sepConj_mono_right hstk))))
      exact entails_of_eq (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
        (Entails.refl _)
    | some ck =>
      apply SepWPp.conseq_pre
        (sepConj_mono_left (sepConj_mono_left (chainAt_some_expose A cs[i] ck elemAddr hck)))
      apply SepWPp.eq_pre (by simp only [sepConj_assoc]; rfl)
      refine SepWPp.pure_elim fun hcap_lt => ?_
      have hcap_ne := cap_add_one_beq_zero_false hcap_lt
      have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
      obtain ⟨v0, v4, v6, v7, v15, v23, v31, hkey⟩ :=
        exists_findReceiverChainKeyKeyChunks_of_length_32 hlen_key
      rw [hkey cs[i].1.ck.ptr]; unfold findReceiverChainKeyKeyChunks
      rw [sp_scratch32_unpack s0.sp, memRegion40_unpack_some x.ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun r36 => SepWPp.exists_elim fun r35 =>
        SepWPp.exists_elim fun r27 => SepWPp.exists_elim fun r26 =>
        SepWPp.exists_elim fun r24 => SepWPp.exists_elim fun r23 =>
        SepWPp.exists_elim fun r19 => SepWPp.exists_elim fun r18 =>
        SepWPp.exists_elim fun r16 => SepWPp.exists_elim fun r8 =>
        SepWPp.exists_elim fun r4 => SepWPp.exists_elim fun r0 =>
        SepWPp.exists_elim fun s24 => SepWPp.exists_elim fun s16 =>
        SepWPp.exists_elim fun s3 => SepWPp.exists_elim fun s2 =>
        SepWPp.exists_elim fun s0_scr => ?_
      apply sepWPp_seq_lscl_ro (mid := (blkPl_25).base + 156#64) hcl2 hro2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro ⟨hcl3, hro3⟩
      apply SepWPp.eq_pre (by simp only [sepConj_assoc, sp_11_repack_rest s0.sp v4 v6 v7]; rfl)
      apply sepWPp_seq_lscl_ro (mid := s0.readReg64 Reg.lr) hcl3 hro3
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro ⟨_, hro4⟩
      refine SepWPp.done (by wp_norm_goal) (by wp_norm_goal) ⟨fun hm => ?_, rfl, by findReceiverChainKey_cc_close⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      rw [findReceiverChainKey_of_some_some hchains_len hfind_res hi hck]
      refine Entails.pure_right ⟨hro4, by simp only [wp_norm, arm64_norm, *]⟩ ?_
      have hres := findReceiverChainKeyResultAt_some_repack x.ret ck v0 v4 v6 v7 v15 v23 v31 hkey
      have hscr := sp_scratch32_repack s0.sp
        (v7.extractLsb' 0 40 ++ v6 ++ v4) (v7.extractLsb' 40 16) (v7.extractLsb' 56 8) v23 v31
      have hstk := stackAt_findReceiverChainKeyStack_repack s0.sp
        (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x21)
        (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19)
      have hch := chainAt_some_reassemble A cs[i] ck elemAddr hck
      rw [hkey cs[i].1.ck.ptr] at hch; unfold findReceiverChainKeyKeyChunks at hch
      have hrat := ratchetAt_reassemble_findIndex A x.self x.G x.st
      rw [arrayAt_split_at (chainAt A) 104 x.G.chainsPtr cs hi] at hrat
      have hrat' := FindReceiverChainKeyFacts.ratchet_reassemble_chain hch hrat
      have hstk' := FindReceiverChainKeyFacts.stack_reassemble_scr hscr hstk
      rw [← hres]
      refine Entails.trans ?_
        (sepConj_mono hrat' (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hstk'))))
      exact entails_of_eq
        (by dsimp only [cs, elemAddr, Reg.x19, Reg.x20, Reg.x21, Reg.lr, Reg.x29]; ac_rfl)
        (Entails.refl _)

theorem find_receiver_chain_key_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)) :=
  find_receiver_chain_key_placed_ok_of_find_index
    (ls_subroutine_ok_of_block (find_receiver_chain_index_placed_ok A h_bb))

end CryptoVerification.LibsignalTripleRatchet
