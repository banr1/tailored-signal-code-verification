/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalSession.StoreLoop

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Unfolded 104-byte slot layout of a `chain::MessageKey` at `a`. -/
def msgKeyPopSlots (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) : SepProp :=
  (a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
  ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
  ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
  ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
    ((a + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
  ((a + 96#64) ↦₃₂ gk.2.counter) ∗ memRegion (a + 100#64) 4

theorem vecHeader_unfold_off (base off cap ptr len : BitVec 64) :
    vecHeader (base + off) cap ptr len =
      ((base + off) ↦₆₄ cap) ∗ ((base + (off + 8#64)) ↦₆₄ ptr) ∗ ((base + (off + 16#64)) ↦₆₄ len) := by
  unfold vecHeader
  simp only [BitVec.add_assoc]

theorem headers_eq_msgKeyPopSlots (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    (vecHeader a gk.1.cipher.cap gk.1.cipher.ptr 0#64 ∗
      vecHeader (a + 24#64) gk.1.mac.cap gk.1.mac.ptr 0#64 ∗
      vecHeader (a + 48#64) gk.1.iv.cap gk.1.iv.ptr 0#64 ∗
      vecHeader (a + 72#64) gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) ∗
      ((a + 96#64) ↦₃₂ gk.2.counter) ∗ memRegion (a + 100#64) 4) =
    msgKeyPopSlots gk a := by
  unfold msgKeyPopSlots vecHeader
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_arith
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_arith
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_arith
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_arith
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_arith
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_arith
  rw [h32, h40, h56, h64, h80, h88]
  ac_rfl

theorem msgKeyPopSlots_entails_memRegion (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    msgKeyPopSlots gk a ⊢ memRegion a 104 := by
  rw [← headers_eq_msgKeyPopSlots]
  have hhdr :
      (vecHeader a gk.1.cipher.cap gk.1.cipher.ptr 0#64 ∗
        vecHeader (a + 24#64) gk.1.mac.cap gk.1.mac.ptr 0#64 ∗
        vecHeader (a + 48#64) gk.1.iv.cap gk.1.iv.ptr 0#64 ∗
        vecHeader (a + 72#64) gk.1.seed.cap gk.1.seed.ptr (BitVec.ofNat 64 gk.2.seed.length) ∗
        ((a + 96#64) ↦₃₂ gk.2.counter) ∗ memRegion (a + 100#64) 4) =
      ((a ↦ₛ messageKeyHeaderBytes gk) ∗ memRegion (a + 100#64) 4) := by
    rw [pointsToBytes_messageKeyHeaderBytes]
    ac_rfl
  rw [hhdr, messageKeyHeader_pad_eq_exists_bytes]
  apply Entails.sepExists_elim
  intro pad
  apply Entails.pure_left
  intro hpad
  have h := pointsToBytes_entails_memRegion a (messageKeyBytes gk pad)
  rwa [messageKeyBytes_length gk hpad] at h

def pinDealloc (A : RustAlloc) (pin : VecPin) : SepProp :=
  if pin.cap = 0#64 then emp else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

theorem messageKeyAt_entails_pop (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a ⊢
      ⌜gk.2.seed ≠ [] ∧
        gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
        gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
        gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
        gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
      msgKeyPopSlots gk a ∗
      pinDealloc A gk.1.cipher ∗
      pinDealloc A gk.1.mac ∗
      pinDealloc A gk.1.iv ∗
      pinDealloc A gk.1.seed := by
  rw [messageKeyAt_eq_headers_sep_heap, headers_eq_msgKeyPopSlots]
  refine Entails.trans (sepConj_mono_right (messageKeyHeap_entails_dealloc A gk)) ?_
  unfold pinDealloc
  change
    (msgKeyPopSlots gk a ∗
      (⌜gk.2.seed ≠ []⌝ ∗
        (⌜0 ≤ gk.1.cipher.cap.toNat ∧ gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0⌝ ∗
          (if gk.1.cipher.cap = 0#64 then emp else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗ memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat)) ∗
        (⌜0 ≤ gk.1.mac.cap.toNat ∧ gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0⌝ ∗
          (if gk.1.mac.cap = 0#64 then emp else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗ memRegion gk.1.mac.ptr gk.1.mac.cap.toNat)) ∗
        (⌜0 ≤ gk.1.iv.cap.toNat ∧ gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0⌝ ∗
          (if gk.1.iv.cap = 0#64 then emp else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗ memRegion gk.1.iv.ptr gk.1.iv.cap.toNat)) ∗
        (⌜gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
          (if gk.1.seed.cap = 0#64 then emp else A.live gk.1.seed.ptr gk.1.seed.cap.toNat 1 ∗ memRegion gk.1.seed.ptr gk.1.seed.cap.toNat)))) ⊢ _
  have hpull :
      (msgKeyPopSlots gk a ∗
        (⌜gk.2.seed ≠ []⌝ ∗
          (⌜0 ≤ gk.1.cipher.cap.toNat ∧ gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0⌝ ∗
            (if gk.1.cipher.cap = 0#64 then emp else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗ memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat)) ∗
          (⌜0 ≤ gk.1.mac.cap.toNat ∧ gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0⌝ ∗
            (if gk.1.mac.cap = 0#64 then emp else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗ memRegion gk.1.mac.ptr gk.1.mac.cap.toNat)) ∗
          (⌜0 ≤ gk.1.iv.cap.toNat ∧ gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0⌝ ∗
            (if gk.1.iv.cap = 0#64 then emp else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗ memRegion gk.1.iv.ptr gk.1.iv.cap.toNat)) ∗
          (⌜gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
            (if gk.1.seed.cap = 0#64 then emp else A.live gk.1.seed.ptr gk.1.seed.cap.toNat 1 ∗ memRegion gk.1.seed.ptr gk.1.seed.cap.toNat)))) =
      (⌜gk.2.seed ≠ []⌝ ∗
        ⌜0 ≤ gk.1.cipher.cap.toNat ∧ gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0⌝ ∗
        ⌜0 ≤ gk.1.mac.cap.toNat ∧ gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0⌝ ∗
        ⌜0 ≤ gk.1.iv.cap.toNat ∧ gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0⌝ ∗
        ⌜gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
        (msgKeyPopSlots gk a ∗
          (if gk.1.cipher.cap = 0#64 then emp else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗ memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat) ∗
          (if gk.1.mac.cap = 0#64 then emp else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗ memRegion gk.1.mac.ptr gk.1.mac.cap.toNat) ∗
          (if gk.1.iv.cap = 0#64 then emp else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗ memRegion gk.1.iv.ptr gk.1.iv.cap.toNat) ∗
          (if gk.1.seed.cap = 0#64 then emp else A.live gk.1.seed.ptr gk.1.seed.cap.toNat 1 ∗ memRegion gk.1.seed.ptr gk.1.seed.cap.toNat))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hseed
  apply Entails.pure_left; rintro ⟨_, hcip_lt, hcip_ptr⟩
  apply Entails.pure_left; rintro ⟨_, hmac_lt, hmac_ptr⟩
  apply Entails.pure_left; rintro ⟨_, hiv_lt, hiv_ptr⟩
  apply Entails.pure_left; rintro ⟨hseed_le, hseed_lt, hseed_ptr⟩
  exact Entails.pure_right
    ⟨hseed, hcip_lt, hcip_ptr, hmac_lt, hmac_ptr, hiv_lt, hiv_ptr, hseed_le, hseed_lt, hseed_ptr⟩
    (Entails.refl _)

def evictOldestKeyFootprint (A : RustAlloc) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (sp : BitVec 64) : SepProp :=
  ((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
  ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
  ((chainPtr + 64#64) ↦₆₄ 2001#64) ∗
  msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
  pinDealloc A gk.1.cipher ∗
  pinDealloc A gk.1.mac ∗
  pinDealloc A gk.1.iv ∗
  pinDealloc A gk.1.seed ∗
  A.pool ∗
  stackAt sp allocHookStack

def evictOldestKeyPostFootprint (A : RustAlloc) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (sp : BitVec 64) : SepProp :=
  ((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
  ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
  ((chainPtr + 64#64) ↦₆₄ 2000#64) ∗
  msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
  A.pool ∗
  stackAt sp allocHookStack

theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 ∧ cap ≠ 0xffffffffffffffff#64 := by
  refine ⟨?_, ?_⟩
  · intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change cap.toNat + 1 = 0 at ht
    omega
  · intro heq
    have ht := congrArg BitVec.toNat heq
    change cap.toNat = 18446744073709551615 at ht
    omega

theorem seed_cap_ne_zero {gk : MessageKeyGhost × MessageKeyGenerator}
    (hne : gk.2.seed ≠ []) (hle : gk.2.seed.length ≤ gk.1.seed.cap.toNat) :
    gk.1.seed.cap ≠ 0#64 := by
  have hpos : 0 < gk.2.seed.length := List.length_pos_of_ne_nil hne
  intro h0
  rw [h0] at hle
  change gk.2.seed.length ≤ 0 at hle
  omega

theorem evictOldestKey_wp {F : ShaState → List (BitVec 8) → ShaState} {A : RustAlloc}
    {alloc : String → Option (State → State)} {b : BitVec 64}
    (hA : AllocHooks A alloc)
    (x : ConsumeMessageKeyGhost) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP b F alloc).fnAddr cmkSym + 1020#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ [])
    (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (_hmac_lt : gk.1.mac.cap.toNat < 2 ^ 63)
    (_hiv_lt : gk.1.iv.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (_hseed_lt : gk.1.seed.cap.toNat < 2 ^ 63) :
    SepWP (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + 1140#64) s
      (evictOldestKeyFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ evictOldestKeyPostFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  unfold evictOldestKeyFootprint evictOldestKeyPostFootprint msgKeyPopSlots pinDealloc
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hdealloc := dealloc_ok_at (b := b) (F := F) hA hfn (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  cmk_fetches_range b (Rust.withPanics (sessionExterns F alloc)) hfn 255 285
  unfold SP cmkSym at *
  generalize (libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  examples_hide_fetches
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have ⟨hcip_add1, hcip_ne_max⟩ := cap_add_one_ne_zero hcip_lt
  have hseed_cap_ne : gk.1.seed.cap ≠ 0#64 := seed_cap_ne_zero hseed_ne hseed_le
  simp only [hseed_cap_ne, ↓reduceIte]
  wp_steps
  wp_if hcmn
  · exfalso; exact hcip_add1 hcmn
  · wp_steps
    wp_if hcip0 <;> (
      simp only [hcip0, ↓reduceIte, emp_sepConj, sepConj_assoc]
      wp_steps
      try (wp_call hdealloc (gk.1.cipher.ptr, gk.1.cipher.cap.toNat, 1); wp_steps))
    all_goals (
      wp_if hmac0 <;> (
        simp only [hmac0, ↓reduceIte, emp_sepConj, sepConj_assoc]
        wp_steps
        try (wp_call hdealloc (gk.1.mac.ptr, gk.1.mac.cap.toNat, 1); wp_steps)))
    all_goals (
      wp_if hiv0 <;> (
        simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
        wp_steps
        try (wp_call hdealloc (gk.1.iv.ptr, gk.1.iv.cap.toNat, 1); wp_steps)))
    all_goals (
      wp_if hseed0
      · exfalso; exact hseed_cap_ne hseed0
      · wp_steps
        wp_apply
        wp_done)

theorem zip_take_eq {α β : Type} :
    ∀ (n : Nat) (xs : List α) (ys : List β),
      (xs.take n).zip (ys.take n) = (xs.zip ys).take n
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _ :: _, [] => rfl
  | n + 1, x :: xs, y :: ys => by
    simp [zip_take_eq n xs ys]

theorem zip_take_cons_eq {α β : Type} (x : α) (xs : List α) (y : β) (ys : List β) (n : Nat) :
    ((x :: xs).take n).zip ((y :: ys).take n) = ((x, y) :: xs.zip ys).take n := by
  rw [zip_take_eq, List.zip_cons_cons]

theorem stackAt_7712_split (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 3616 ∗ stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack 3616 (by decide)
  simpa [allocHookStack] using h

theorem vecHeader_chainPtr_48 (chainPtr mkCap1 mkPtr1 len : BitVec 64) :
    vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 len =
      ((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
      ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
      ((chainPtr + 64#64) ↦₆₄ len) := by
  unfold vecHeader
  have h56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have h64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  rw [h56, h64]

theorem chainAt_sep_ratchetContextAt_entails_ratchetAt
    (A : RustAlloc) (self : BitVec 64) (G : RatchetGhost) (st : RatchetState)
    {i : Nat} (hi : i < st.receiverChains.length) (g' : ChainGhost) (c' : ReceiverChain) :
    (chainAt A (g', c') (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
      ratchetContextAt A self G st i) ⊢
      ratchetAt A self (G.setChain i g') (st.setChain i c') := by
  unfold ratchetContextAt
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, _⟩
  have hpull :
      (chainAt A (g', c') (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
        (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
          A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
          arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
            ((G.chains.zip st.receiverChains).drop (i + 1)) ∗
          memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
            ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
          ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
          ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
          ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
          ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4)) =
      (vecHeader self G.chainsCap G.chainsPtr (BitVec.ofNat 64 st.receiverChains.length) ∗
        A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
        chainAt A (g', c') (G.chainsPtr + BitVec.ofNat 64 (i * 104)) ∗
        arrayAt (chainAt A) 104 G.chainsPtr ((G.chains.zip st.receiverChains).take i) ∗
        arrayAt (chainAt A) 104 (G.chainsPtr + BitVec.ofNat 64 ((i + 1) * 104))
          ((G.chains.zip st.receiverChains).drop (i + 1)) ∗
        memRegion (G.chainsPtr + BitVec.ofNat 64 (st.receiverChains.length * 104))
          ((G.chainsCap.toNat - st.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) := by
    ac_rfl
  rw [hpull]
  exact ratchetAt_set_chain A self G st hi g' c' hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne

def evictOldestKeyFrame (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
  arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
  memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0

theorem evictOldestKeyHeap_entails_evictOldestKeyFootprint
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hmk_len : chc.messageKeys.length = 2000)
    (hgk_len : cg.keys.length = 2000) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
    have hgks1_len : gks1.length = 2000 + 1 := by
      simp [gks1, List.length_zip, hgk_len, hmk_len]
    let gk := gks1[2000]'(by omega)
    evictOldestKeyHeap F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ⊢
      ⌜gk.2.seed ≠ [] ∧
        gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
        gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
        gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
        gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
      evictOldestKeyFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗
      evictOldestKeyFrame F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 := by
  intro chainPtr gks1 hgks1_len gk
  unfold evictOldestKeyHeap evictOldestKeyFootprint evictOldestKeyFrame
  dsimp only
  have hpop := vecBuf_messageKeyAt_pop_split A mkCap1 mkPtr1 gks1 hgks1_len
  change vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1 gks1 ⊢
    ⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
      A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
      arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
      messageKeyAt A gk (mkPtr1 + 208000#64) ∗
      memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) at hpop
  have hpop2 := Entails.trans hpop
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (messageKeyAt_entails_pop A gk (mkPtr1 + 208000#64))))))
  rw [vecHeader_chainPtr_48 chainPtr mkCap1 mkPtr1 2001#64, stackAt_7712_split (s0.sp - 480#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpop2))))) ?_
  have hpull :
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        (((chainPtr + 48#64) ↦₆₄ mkCap1) ∗ ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗ ((chainPtr + 64#64) ↦₆₄ 2001#64)) ∗
        (⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
          A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
          (⌜gk.2.seed ≠ [] ∧
            gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
            gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
            gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
            gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
            msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
            pinDealloc A gk.1.cipher ∗
            pinDealloc A gk.1.mac ∗
            pinDealloc A gk.1.iv ∗
            pinDealloc A gk.1.seed) ∗
          memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104)) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        ratchetContextAt A x.self Gc stc ci ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗ stackAt (s0.sp - 480#64) allocHookStack) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool) =
      (⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
        ⌜gk.2.seed ≠ [] ∧
          gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
          gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
          gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
          gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
        ((((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
          ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
          ((chainPtr + 64#64) ↦₆₄ 2001#64) ∗
          msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
          pinDealloc A gk.1.cipher ∗
          pinDealloc A gk.1.mac ∗
          pinDealloc A gk.1.iv ∗
          pinDealloc A gk.1.seed ∗
          A.pool ∗
          stackAt (s0.sp - 480#64) allocHookStack) ∗
         (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
          vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
          memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
          ratchetContextAt A x.self Gc stc ci ∗
          (x.theirA ↦ₛ x.their.bytes.toList) ∗
          (x.ckA ↦ₛ chainKeyBytes ckc) ∗
          memRegion x.ret 88 ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
          cmkLoopFrame s0.sp x.ret x.counter ∗
          cmkSavedRegs s0.sp s0))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro hpure
  exact Entails.pure_right hpure (Entails.refl _)

theorem evictOldestKeyPost_entails_cmkLoopHeap
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (hci_stc : ci < stc.receiverChains.length)
    (hsrk : PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey)
    (hmk_len : chc.messageKeys.length = 2000)
    (hgk_len : cg.keys.length = 2000)
    (hmk_cap_le : 2001 ≤ mkCap1.toNat)
    (hmk_cap_lt : mkCap1.toNat * 104 < 2 ^ 63)
    (hmk_ptr_ne : mkPtr1 ≠ 0#64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    let cg' : ChainGhost :=
      { cg with mkCap := mkCap1, mkPtr := mkPtr1,
                keys := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys }
    (evictOldestKeyPostFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗
      evictOldestKeyFrame F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0) ⊢
      cmkLoopHeap A img x (Gc.setChain ci cg') (updatedRatchetState F stc ci chc ckc) ckc s0 := by
  intro chainPtr cg'
  unfold evictOldestKeyPostFootprint evictOldestKeyFrame cmkLoopHeap
  dsimp only
  set gks1 : List (MessageKeyGhost × MessageKeyGenerator) :=
    (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  set keys' := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys
  set messageKeys' := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys
  have hgks1_len : gks1.length = 2000 + 1 := by
    simp [gks1, List.length_zip, hgk_len, hmk_len]
  have hkeys'_len : keys'.length = 2000 := by
    simp [keys', hgk_len, maxMessageKeys]
  have hmk'_len : messageKeys'.length = 2000 := by
    simp [messageKeys', hmk_len, maxMessageKeys]
  have hzip_eq : gks1.take 2000 = keys'.zip messageKeys' := by
    simpa [gks1, keys', messageKeys', maxMessageKeys] using
      (zip_take_cons_eq (newMsgKeyGhost seedPtr) cg.keys (ckc.messageKeys F) chc.messageKeys 2000).symm
  have hhdr_len : (2000#64 : BitVec 64) = BitVec.ofNat 64 (keys'.zip messageKeys').length := by
    simp [List.length_zip, hkeys'_len, hmk'_len]
  have hslot_mem : msgKeyPopSlots gk (mkPtr1 + 208000#64) ⊢
      memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 :=
    msgKeyPopSlots_entails_memRegion gk (mkPtr1 + 208000#64)
  have hvec_reasm := vecBuf_messageKeyAt_pop_reassemble A mkCap1 mkPtr1 gks1
    hgks1_len hmk_cap_le hmk_cap_lt hmk_ptr_ne
  rw [hzip_eq] at hvec_reasm
  have hrat := chainAt_sep_ratchetContextAt_entails_ratchetAt A x.self Gc stc hci_stc
    cg' (updatedReceiverChain F chc ckc)
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hslot_mem))))) ?_
  have hpull :
      ((((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
        ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
        ((chainPtr + 64#64) ↦₆₄ 2000#64) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 ∗
        A.pool ∗
        stackAt (s0.sp - 480#64) allocHookStack) ∗
       (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        ratchetContextAt A x.self Gc stc ci ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0)) =
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       (((vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 2000#64 ∗
           (A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
            arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
            memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 ∗
            memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104))) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
         ratchetContextAt A x.self Gc stc ci) ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) := by
    rw [vecHeader_chainPtr_48 chainPtr mkCap1 mkPtr1 2000#64, stackAt_7712_split (s0.sp - 480#64)]
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  rintro ⟨hsrk_len, hpriv⟩
  have hchain := chainAt_of_update_messageKeys A cg chc chainPtr mkCap1 mkPtr1 keys' messageKeys'
    hsrk (by simp [hmk'_len, maxMessageKeys]) (by omega) hsrk_len hpriv
  apply sepConj_mono_left
  rw [hzip_eq, hhdr_len]
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right hvec_reasm))))) ?_
  refine Entails.trans (sepConj_mono_left hchain) ?_
  exact hrat

def evictOldestKeyFrameAt (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
  arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
  memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0

theorem evictOldestKeyHeapAt_entails_evictOldestKeyFootprint
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hmk_len : chc.messageKeys.length = 2000)
    (hgk_len : cg.keys.length = 2000) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    let gks1 := (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
    have hgks1_len : gks1.length = 2000 + 1 := by
      simp [gks1, List.length_zip, hgk_len, hmk_len]
    let gk := gks1[2000]'(by omega)
    evictOldestKeyHeapAt F A logAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ⊢
      ⌜gk.2.seed ≠ [] ∧
        gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
        gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
        gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
        gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
      evictOldestKeyFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗
      evictOldestKeyFrameAt F A logAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 := by
  intro chainPtr gks1 hgks1_len gk
  unfold evictOldestKeyHeapAt evictOldestKeyFootprint evictOldestKeyFrameAt
  dsimp only
  have hpop := vecBuf_messageKeyAt_pop_split A mkCap1 mkPtr1 gks1 hgks1_len
  change vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1 gks1 ⊢
    ⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
      A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
      arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
      messageKeyAt A gk (mkPtr1 + 208000#64) ∗
      memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) at hpop
  have hpop2 := Entails.trans hpop
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (messageKeyAt_entails_pop A gk (mkPtr1 + 208000#64))))))
  rw [vecHeader_chainPtr_48 chainPtr mkCap1 mkPtr1 2001#64, stackAt_7712_split (s0.sp - 480#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpop2))))) ?_
  have hpull :
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        (((chainPtr + 48#64) ↦₆₄ mkCap1) ∗ ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗ ((chainPtr + 64#64) ↦₆₄ 2001#64)) ∗
        (⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
          A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
          (⌜gk.2.seed ≠ [] ∧
            gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
            gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
            gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
            gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
            msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
            pinDealloc A gk.1.cipher ∗
            pinDealloc A gk.1.mac ∗
            pinDealloc A gk.1.iv ∗
            pinDealloc A gk.1.seed) ∗
          memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104)) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        ratchetContextAt A x.self Gc stc ci ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗ stackAt (s0.sp - 480#64) allocHookStack) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool) =
      (⌜2000 + 1 ≤ mkCap1.toNat ∧ mkCap1.toNat * 104 < 2 ^ 63 ∧ mkPtr1 ≠ 0⌝ ∗
        ⌜gk.2.seed ≠ [] ∧
          gk.1.cipher.cap.toNat < 2 ^ 63 ∧ gk.1.cipher.ptr ≠ 0 ∧
          gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.mac.ptr ≠ 0 ∧
          gk.1.iv.cap.toNat < 2 ^ 63 ∧ gk.1.iv.ptr ≠ 0 ∧
          gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63 ∧ gk.1.seed.ptr ≠ 0⌝ ∗
        ((((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
          ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
          ((chainPtr + 64#64) ↦₆₄ 2001#64) ∗
          msgKeyPopSlots gk (mkPtr1 + 208000#64) ∗
          pinDealloc A gk.1.cipher ∗
          pinDealloc A gk.1.mac ∗
          pinDealloc A gk.1.iv ∗
          pinDealloc A gk.1.seed ∗
          A.pool ∗
          stackAt (s0.sp - 480#64) allocHookStack) ∗
         (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
          vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
          arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
          memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
          ratchetContextAt A x.self Gc stc ci ∗
          (x.theirA ↦ₛ x.their.bytes.toList) ∗
          (x.ckA ↦ₛ chainKeyBytes ckc) ∗
          memRegion x.ret 88 ∗
          (logAddr ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
          cmkLoopFrame s0.sp x.ret x.counter ∗
          cmkSavedRegs s0.sp s0))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro hpure
  exact Entails.pure_right hpure (Entails.refl _)

theorem evictOldestKeyPost_entails_cmkLoopHeapAt
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost)
    (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (hci_stc : ci < stc.receiverChains.length)
    (hsrk : PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey)
    (hmk_len : chc.messageKeys.length = 2000)
    (hgk_len : cg.keys.length = 2000)
    (hmk_cap_le : 2001 ≤ mkCap1.toNat)
    (hmk_cap_lt : mkCap1.toNat * 104 < 2 ^ 63)
    (hmk_ptr_ne : mkPtr1 ≠ 0#64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    let cg' : ChainGhost :=
      { cg with mkCap := mkCap1, mkPtr := mkPtr1,
                keys := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys }
    (evictOldestKeyPostFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗
      evictOldestKeyFrameAt F A logAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0) ⊢
      cmkLoopHeapAt A logAddr x (Gc.setChain ci cg') (updatedRatchetState F stc ci chc ckc) ckc s0 := by
  intro chainPtr cg'
  unfold evictOldestKeyPostFootprint evictOldestKeyFrameAt cmkLoopHeapAt
  dsimp only
  set gks1 : List (MessageKeyGhost × MessageKeyGenerator) :=
    (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  set keys' := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys
  set messageKeys' := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys
  have hgks1_len : gks1.length = 2000 + 1 := by
    simp [gks1, List.length_zip, hgk_len, hmk_len]
  have hkeys'_len : keys'.length = 2000 := by
    simp [keys', hgk_len, maxMessageKeys]
  have hmk'_len : messageKeys'.length = 2000 := by
    simp [messageKeys', hmk_len, maxMessageKeys]
  have hzip_eq : gks1.take 2000 = keys'.zip messageKeys' := by
    simpa [gks1, keys', messageKeys', maxMessageKeys] using
      (zip_take_cons_eq (newMsgKeyGhost seedPtr) cg.keys (ckc.messageKeys F) chc.messageKeys 2000).symm
  have hhdr_len : (2000#64 : BitVec 64) = BitVec.ofNat 64 (keys'.zip messageKeys').length := by
    simp [List.length_zip, hkeys'_len, hmk'_len]
  have hslot_mem : msgKeyPopSlots gk (mkPtr1 + 208000#64) ⊢
      memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 :=
    msgKeyPopSlots_entails_memRegion gk (mkPtr1 + 208000#64)
  have hvec_reasm := vecBuf_messageKeyAt_pop_reassemble A mkCap1 mkPtr1 gks1
    hgks1_len hmk_cap_le hmk_cap_lt hmk_ptr_ne
  rw [hzip_eq] at hvec_reasm
  have hrat := chainAt_sep_ratchetContextAt_entails_ratchetAt A x.self Gc stc hci_stc
    cg' (updatedReceiverChain F chc ckc)
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left hslot_mem))))) ?_
  have hpull :
      ((((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
        ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
        ((chainPtr + 64#64) ↦₆₄ 2000#64) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 ∗
        A.pool ∗
        stackAt (s0.sp - 480#64) allocHookStack) ∗
       (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        ratchetContextAt A x.self Gc stc ci ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 480#64 - 7712#64) 3616 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0)) =
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       (((vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 2000#64 ∗
           (A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
            arrayAt (messageKeyAt A) 104 mkPtr1 (gks1.take 2000) ∗
            memRegion (mkPtr1 + BitVec.ofNat 64 (2000 * 104)) 104 ∗
            memRegion (mkPtr1 + BitVec.ofNat 64 ((2000 + 1) * 104)) ((mkCap1.toNat - (2000 + 1)) * 104))) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
         ratchetContextAt A x.self Gc stc ci) ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) := by
    rw [vecHeader_chainPtr_48 chainPtr mkCap1 mkPtr1 2000#64, stackAt_7712_split (s0.sp - 480#64)]
    ac_rfl
  rw [hpull]
  apply Entails.pure_left
  rintro ⟨hsrk_len, hpriv⟩
  have hchain := chainAt_of_update_messageKeys A cg chc chainPtr mkCap1 mkPtr1 keys' messageKeys'
    hsrk (by simp [hmk'_len, maxMessageKeys]) (by omega) hsrk_len hpriv
  apply sepConj_mono_left
  rw [hzip_eq, hhdr_len]
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right hvec_reasm))))) ?_
  refine Entails.trans (sepConj_mono_left hchain) ?_
  exact hrat

theorem evictOldestKey_ok {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {alloc : String → Option (State → State)} {img : Obj.Image} :
    EvictOldestKeySpec F A alloc img := by
  intro hA himg x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB hchc_get hSB hL
  rcases hSB with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hfrozen, hsymtab, hvregs⟩,
    ⟨hx19, hx21, hx22, hx23, hx25, hx26, _hx28⟩,
    ⟨hci_gc, hcg_eq⟩, hsrk, hmk_len, hgk_len, hmk_cap_le, hmk_cap_lt, hmk_ptr_ne, hmem⟩
  have hci_stc : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc_get).1
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set gks1 : List (MessageKeyGhost × MessageKeyGenerator) :=
    (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  have hgks1_len : gks1.length = 2000 + 1 := by
    simp [gks1, List.length_zip, hgk_len, hmk_len]
  set gk := gks1[2000]'(by omega)
  have hsplit := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyHeap_entails_evictOldestKeyFootprint F A img x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 hmk_len hgk_len)) hmem
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsplit
  rcases hsplit with ⟨⟨hseed_ne, hcip_lt, _, hmac_lt, _, hiv_lt, _, hseed_le, hseed_lt, _⟩, hmem_pre⟩
  have hpc' : sB.pc = (SP img.base F alloc).fnAddr cmkSym + 1020#64 := by
    rwa [cmkEvictOldestKeyPC_eq_fnAddr himg F alloc] at hpc
  have hL' : (SP img.base F alloc).CodeLoaded sB.mem := by
    rwa [← sessionProg_eq_SP himg F alloc]
  have hwp := evictOldestKey_wp (b := img.base) (F := F) hA x chainPtr mkCap1 mkPtr1 gk
    (evictOldestKeyFrame F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ∗ R)
    s0 sB hpc' hrun hsp hsp0_align hsp_align hx29 hx19 hx21 hx22 hx23 hx25 hx26
    hseed_ne hcip_lt hmac_lt hiv_lt hseed_le hseed_lt
  rcases hwp.elim hmem_pre hL' with ⟨sC, hsteps, ⟨hpc_sC, hrun_sC, P_f, hmf,
    himp, hsp_sC, hsp_align_sC, ⟨htrace_sC, hvregs_sC⟩, hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC, hx29_sC⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  rw [← sessionProg_eq_SP himg F alloc] at hsteps
  rw [← cmkAdvanceChainKeyPC_eq_fnAddr himg F alloc] at hpc_sC
  have hpost_fp := himp hmf
  rw [← sepConj_assoc] at hpost_fp
  set cg' : ChainGhost :=
    { cg with mkCap := mkCap1, mkPtr := mkPtr1,
              keys := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys }
  have hmem_sC := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyPost_entails_cmkLoopHeap F A img x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 gk hci_stc hsrk hmk_len hgk_len hmk_cap_le hmk_cap_lt hmk_ptr_ne))
    hpost_fp
  have hagree : Gc.AgreeExcept (Gc.setChain ci cg') (some ci) :=
    RatchetGhost.AgreeExcept.setChain Gc hci_gc cg' (by simp [cg', hcg_eq]) (by simp [cg', hcg_eq])
  refine ⟨sC, hsteps, Gc.setChain ci cg', hagree,
    hpc_sC,
    ⟨hrun_sC, hsp_sC, hsp0_align, hsp_align_sC, hx29_sC, htrace_sC.trans htrace,
      hfrozen.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans hsymtab, hvregs_sC.trans hvregs⟩,
    ⟨hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC⟩,
    hmem_sC⟩

set_option maxRecDepth 200000 in
theorem evictOldestKey_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A H)
    (x : ConsumeMessageKeyGhost) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1020#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ [])
    (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (_hmac_lt : gk.1.mac.cap.toNat < 2 ^ 63)
    (_hiv_lt : gk.1.iv.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (_hseed_lt : gk.1.seed.cap.toNat < 2 ^ 63) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1140#64) s
      (evictOldestKeyFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ evictOldestKeyPostFootprint A chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  unfold evictOldestKeyFootprint evictOldestKeyPostFootprint msgKeyPopSlots pinDealloc
  have hdealloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym) (rustDeallocSpec A) :=
    cmk_hook_ok_of_mem hA.2.1
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have ⟨hcip_add1, hcip_ne_max⟩ := cap_add_one_ne_zero hcip_lt
  have hseed_cap_ne : gk.1.seed.cap ≠ 0#64 := seed_cap_ne_zero hseed_ne hseed_le
  simp only [hseed_cap_ne, ↓reduceIte]
  wp_steps
  wp_if hcmn
  · exfalso; exact hcip_add1 hcmn
  · wp_steps
    wp_if hcip0 <;> (
      simp only [hcip0, ↓reduceIte, emp_sepConj, sepConj_assoc]
      wp_steps
      try (wp_call hdealloc (gk.1.cipher.ptr, gk.1.cipher.cap.toNat, 1); wp_steps))
    all_goals (
      wp_if hmac0 <;> (
        simp only [hmac0, ↓reduceIte, emp_sepConj, sepConj_assoc]
        wp_steps
        try (wp_call hdealloc (gk.1.mac.ptr, gk.1.mac.cap.toNat, 1); wp_steps)))
    all_goals (
      wp_if hiv0 <;> (
        simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
        wp_steps
        try (wp_call hdealloc (gk.1.iv.ptr, gk.1.iv.cap.toNat, 1); wp_steps)))
    all_goals (
      wp_if hseed0
      · exfalso; exact hseed_cap_ne hseed0
      · wp_steps
        wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1)
        wp_done)

theorem evictOldestKey_placed_ok [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)} :
    EvictOldestKeyPlacedSpec F A H := by
  intro hA x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB hchc_get hSB hL
  rcases hSB with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
    ⟨hx19, hx21, hx22, hx23, hx25, hx26, _hx28⟩,
    ⟨hci_gc, hcg_eq⟩, hsrk, hmk_len, hgk_len, hmk_cap_le, hmk_cap_lt, hmk_ptr_ne, hmem⟩
  have hci_stc : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc_get).1
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set gks1 : List (MessageKeyGhost × MessageKeyGenerator) :=
    (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  have hgks1_len : gks1.length = 2000 + 1 := by
    simp [gks1, List.length_zip, hgk_len, hmk_len]
  set gk := gks1[2000]'(by omega)
  have hsplit := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyHeapAt_entails_evictOldestKeyFootprint F A lsLogFilterAddr x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 hmk_len hgk_len)) hmem
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsplit
  rcases hsplit with ⟨⟨hseed_ne, hcip_lt, _, hmac_lt, _, hiv_lt, _, hseed_le, hseed_lt, _⟩, hmem_pre⟩
  have hpc' : sB.pc = (blkPl_24).base + 1020#64 := hpc
  have hwp := evictOldestKey_placed_wp hA x chainPtr mkCap1 mkPtr1 gk
    (evictOldestKeyFrameAt F A lsLogFilterAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ∗ R)
    s0 sB hpc' hrun hsp hsp0_align hsp_align hx29 hx19 hx21 hx22 hx23 hx25 hx26
    hseed_ne hcip_lt hmac_lt hiv_lt hseed_le hseed_lt
  rcases hwp.elim hmem_pre hL with ⟨sC, hsteps, ⟨hpc_sC, hrun_sC, P_f, hmf,
    himp, hsp_sC, hsp_align_sC, ⟨htrace_sC, hvregs_sC⟩, hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC, hx29_sC⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hpost_fp := himp hmf
  rw [← sepConj_assoc] at hpost_fp
  set cg' : ChainGhost :=
    { cg with mkCap := mkCap1, mkPtr := mkPtr1,
              keys := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys }
  have hmem_sC := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyPost_entails_cmkLoopHeapAt F A lsLogFilterAddr x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 gk hci_stc hsrk hmk_len hgk_len hmk_cap_le hmk_cap_lt hmk_ptr_ne))
    hpost_fp
  rw [← cmkLoopHeap_placed_eq_at] at hmem_sC
  have hagree : Gc.AgreeExcept (Gc.setChain ci cg') (some ci) :=
    RatchetGhost.AgreeExcept.setChain Gc hci_gc cg' (by simp [cg', hcg_eq]) (by simp [cg', hcg_eq])
  refine ⟨sC, hsteps, Gc.setChain ci cg', hagree,
    hpc_sC,
    ⟨hrun_sC, hsp_sC, hsp0_align, hsp_align_sC, hx29_sC, htrace_sC.trans htrace,
      hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sC.trans hvregs⟩,
    ⟨hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC⟩,
    hmem_sC⟩

end CryptoVerification.LibsignalSession.StoreLoop
