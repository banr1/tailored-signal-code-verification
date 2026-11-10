/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import ProofLib.SepLogic.WPp

/-!
# Shared Helpers for `drop_glue<SessionStructure>` (`0x25b4` and `0x35958`)

Provides separation-logic field-deallocation lemmas, stack splits, and common `SepWPp` helpers
shared by `drop_glue<SessionStructure> [local#1]` and `[local#2]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DropsCommon

theorem stackAt_split_bottom' (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem dealloc_hookSat_tripleRatchetExterns {A : RustAlloc} (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) "__rustc::__rust_dealloc"
      (rustDeallocSpec A) := by
  simpa [HookSat, Rust.withPanics, Rust.isPanicSymbol, tripleRatchetExterns,
    CryptoVerification.LibsignalSession.sessionExterns, dhName, pubFromSecretName,
    staticDropName, sharedDropName, rngFillName, uuidTryParseName,
    varintSlowName, noHookNames] using hA.dealloc

theorem dealloc_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_dealloc")) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_dealloc")
    (dealloc_hookSat_tripleRatchetExterns C ctl hA)

theorem SepWP.seq_clean {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _ hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-! ## Separation-logic deallocation helpers for `SessionStructure` (344 bytes) -/

def vecPinDealloc (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

def sgnPinDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

theorem slt_one_iff_eq_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]
  unfold BitVec.slt BitVec.toInt
  simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]
  omega

theorem vecU8At_entails_pin_dealloc (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDealloc
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro _
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

theorem vecGhostAt_entails_pin_dealloc (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_dealloc A a ⟨g.cap, g.ptr⟩ g.bytes

theorem header_cells_entails_memRegion_24 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8) ⊢ memRegion a 24 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem header_cells_entails_memRegion_32 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16) ⊢ memRegion a 32 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

end DropsCommon

theorem header_cells_entails_memRegion_48_shared_lb (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

namespace DropsCommon

theorem optTailVecAt_entails_dealloc (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        sgnPinDealloc A cap ptr := by
  cases opt with
  | none =>
    unfold optTailVecAt sgnPinDealloc
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    rw [hsplit,
        ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
          (b' := a + 16#64) rfl (by bv_omega) (by omega),
        memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right noneCap (Entails.sepExists_right ptr ?_)
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some g =>
    unfold optTailVecAt sgnPinDealloc
    apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat) := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      exact Entails.refl _
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right g.vec.cap (Entails.sepExists_right g.vec.ptr ?_)
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ⊢
          memRegion (a + 16#64) (size - 16) := by
      have hsplit : size - 16 = 8 + (size - 24) := by omega
      rw [hsplit,
          ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := size - 24)
            (b' := a + 24#64) rfl (by bv_omega) (by omega)]
      apply sepConj_mono (pointsTo64_entails_memRegion _ _)
      have hb := pointsToBytes_entails_memRegion (a + 24#64) g.tail
      rwa [htail] at hb
    have hpull1 :
        (((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) := by
      ac_rfl
    rw [hpull1]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

theorem optChainKeyAt_entails_dealloc (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        sgnPinDealloc A cap ptr := by
  cases ck with
  | none =>
    unfold optChainKeyAt sgnPinDealloc
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right optChainKeyNone (Entails.sepExists_right ptr ?_)
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some c =>
    unfold optChainKeyAt sgnPinDealloc
    have hvec : vecU8At A a pin.cap pin.ptr (keyToBytes32 c.key) ⊢
        (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          (if pin.cap.slt 1#64 = true then emp
           else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
      refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      exact Entails.refl _
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr ?_)
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ⊢
          memRegion (a + 16#64) 16 := by
      rw [ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
            (b' := a + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := a + 24#64) (n := 4) (k := 4)
            (b' := a + 28#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
    have hpull :
        (((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          (if pin.cap.slt 1#64 = true then emp
           else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) =
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
            ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ∗
          (if pin.cap.slt 1#64 = true then emp
           else A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

end DropsCommon

theorem cap_add_one_ne_zero_shared_lb {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have h1 : cap = 0xffffffffffffffff#64 := by
    revert heq; bv_kernel
  subst h1
  revert h; decide

theorem sender_none_entails_memRegion_104_shared_lb (a : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96) ⊢ memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 96) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

def srkRest_shared_lb (A : RustAlloc) (a : BitVec 64) (g : VecGhost) : SepProp :=
  ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
    (if g.cap = 0 then emp
     else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
       memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_eq_srkRest_shared_lb (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ srkRest_shared_lb A a g := by
  unfold vecGhostAt vecU8At vecHeader srkRest_shared_lb
  ac_rfl

theorem optSenderChainAt_some_expose_shared_lb (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) ⊢
      ⌜PublicKey.deserialize g.srk.bytes = .ok sc.ratchetKey.publicKey ∧
        g.srk.bytes.length ≤ g.srk.cap.toNat ∧ g.srk.cap.toNat < 2 ^ 63 ∧ g.srk.ptr ≠ 0 ∧
        g.srk.cap + 1#64 ≠ 0#64⌝ ∗
      (a ↦₆₄ g.srk.cap) ∗ srkRest_shared_lb A a g.srk ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
      optChainKeyAt A g.ck (some sc.chainKey) (a + 72#64) := by
  unfold optSenderChainAt
  apply Entails.pure_left; rintro ⟨hpk, _, _, _⟩
  rw [vecGhostAt_eq_srkRest_shared_lb A g.srk a, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr_ne⟩
  refine Entails.pure_right ⟨hpk, hlen, hcap_lt, hptr_ne, cap_add_one_ne_zero_shared_lb hcap_lt⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem chainAt_of_exposed_sender_shared_lb (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain)
    (hpk : PublicKey.deserialize g.srk.bytes = .ok sc.ratchetKey.publicKey)
    (hlen : g.srk.bytes.length ≤ g.srk.cap.toNat)
    (hcap_lt : g.srk.cap.toNat < 2 ^ 63)
    (hptr_ne : g.srk.ptr ≠ 0) :
    (a ↦₆₄ g.srk.cap) ∗ srkRest_shared_lb A a g.srk ∗
      vecGhostAt A g.priv (a + 24#64) ∗
      vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
      optChainKeyAt A g.ck (some sc.chainKey) (a + 72#64) ⊢
    protoChainAt A (⟨g.srk, g.priv, g.mkCap, g.mkPtr, [], g.ck⟩,
      ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩) a := by
  unfold protoChainAt
  dsimp only [List.length_nil, List.zip_nil_left]
  refine Entails.pure_right ⟨hpk, by decide, rfl⟩ ?_
  rw [vecGhostAt_eq_srkRest_shared_lb A g.srk a, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_right ⟨hlen, hcap_lt, hptr_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

namespace DropsCommon

theorem optSenderChainAt_some_entails_dealloc1 (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜g.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
        vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        ((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗ memRegion (a + 40#64) 8 ∗
        vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
        ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 80#64) ↦₆₄ ckPtr) ∗ memRegion (a + 88#64) 16 ∗
        sgnPinDealloc A ckCap ckPtr := by
  unfold optSenderChainAt
  apply Entails.pure_left; rintro ⟨_, _, _, _⟩
  have h1 : vecGhostAt A g.srk a ⊢
      ⌜g.srk.cap + 1#64 ≠ 0#64⌝ ∗
      (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A ⟨g.srk.cap, g.srk.ptr⟩ := by
    unfold vecGhostAt
    refine Entails.trans (vecU8At_entails_dealloc A a g.srk.cap g.srk.ptr g.srk.bytes) ?_
    unfold vecHeader vecPinDealloc
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    refine Entails.pure_right (cap_add_one_ne_zero_shared_lb hcap_lt) ?_
    have hbeq : ((g.srk.cap == 0#64) = true) ↔ g.srk.cap = 0 := beq_iff_eq
    simp only [hbeq]
    rw [sepConj_assoc, sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))
  have h2 := vecGhostAt_entails_pin_dealloc A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_dealloc A g.ck (some sc.chainKey) (a + 72#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ ha1, ha2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ckCap; refine Entails.sepExists_right ckCap ?_
  apply Entails.sepExists_elim; intro ckPtr; refine Entails.sepExists_right ckPtr ?_
  exact Entails.of_eq (by ac_rfl)

end DropsCommon

theorem sessionTail_entails_memRegion_16_shared_lb (ss : BitVec 64)
    (v1 v2 : BitVec 32) (regIds : List (BitVec 8)) (hreg : regIds.length = 8) :
    ((ss + 0x148#64) ↦₃₂ v1) ∗ ((ss + 0x14c#64) ↦₃₂ v2) ∗ ((ss + 0x150#64) ↦ₛ regIds) ⊢
      memRegion (ss + 328#64) 16 := by
  rw [ProofLib.memRegion_split' (b := ss + 328#64) (n := 4) (k := 12)
        (b' := ss + 332#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 332#64) (n := 4) (k := 8)
        (b' := ss + 336#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo32_entails_memRegion _ _) ?_)
  have hb := pointsToBytes_entails_memRegion (ss + 336#64) regIds
  rwa [hreg] at hb

theorem session_memRegions_entails_344_shared_lb (ss : BitVec 64) :
    memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
      memRegion (ss + 72#64) 24 ∗ memRegion (ss + 96#64) 24 ∗ memRegion (ss + 120#64) 24 ∗
      memRegion (ss + 144#64) 104 ∗ memRegion (ss + 248#64) 48 ∗
      memRegion (ss + 296#64) 32 ∗ memRegion (ss + 328#64) 16 ⊢
      memRegion ss 344 := by
  rw [ProofLib.memRegion_split' (b := ss) (n := 24) (k := 320) (b' := ss + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := ss + 24#64) (n := 24) (k := 296) (b' := ss + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 48#64) (n := 24) (k := 272) (b' := ss + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 72#64) (n := 24) (k := 248) (b' := ss + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 96#64) (n := 24) (k := 224) (b' := ss + 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 120#64) (n := 24) (k := 200) (b' := ss + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 104) (k := 96) (b' := ss + 248#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 248#64) (n := 48) (k := 48) (b' := ss + 296#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 296#64) (n := 32) (k := 16) (b' := ss + 328#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

@[reducible]
def ssFirst3HeadersAt_shared_lb (ss : BitVec 64) (G : SessionGhost) : SepProp :=
  (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8 ∗
  ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗ memRegion (ss + 40#64) 8 ∗
  ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ memRegion (ss + 64#64) 8

namespace DropsCommon

theorem ssFirst3_entails_dealloc (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    vecGhostAt A G.localIk ss ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ⊢
    ssFirst3HeadersAt_shared_lb ss G ∗
      vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root := by
  have h1 := vecGhostAt_entails_pin_dealloc A G.localIk ss
  have h2 := vecGhostAt_entails_pin_dealloc A G.remoteIk (ss + 24#64)
  have h3 := vecU8At_entails_pin_dealloc A (ss + 48#64) G.root (keyToBytes32 st.rootKey)
  have ha1 : (ss + 24#64) + 8#64 = ss + 32#64 := by bv_omega
  have ha2 : (ss + 24#64) + 16#64 = ss + 40#64 := by bv_omega
  have hb1 : (ss + 48#64) + 8#64 = ss + 56#64 := by bv_omega
  have hb2 : (ss + 48#64) + 16#64 = ss + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  unfold ssFirst3HeadersAt_shared_lb
  exact Entails.of_eq (by ac_rfl)

theorem ssFirst3HeadersAt_entails_memRegions (ss : BitVec 64) (G : SessionGhost) :
    ssFirst3HeadersAt_shared_lb ss G ⊢
      memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 := by
  unfold ssFirst3HeadersAt_shared_lb
  have h1 := header_cells_entails_memRegion_24 ss G.localIk.cap G.localIk.ptr
  have h2 := header_cells_entails_memRegion_24 (ss + 24#64) G.remoteIk.cap G.remoteIk.ptr
  have h3 := header_cells_entails_memRegion_24 (ss + 48#64) G.root.cap G.root.ptr
  have ha1 : (ss + 24#64) + 8#64 = ss + 32#64 := by bv_omega
  have ha2 : (ss + 24#64) + 16#64 = ss + 40#64 := by bv_omega
  have hb1 : (ss + 48#64) + 8#64 = ss + 56#64 := by bv_omega
  have hb2 : (ss + 48#64) + 16#64 = ss + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  have hgroup :
      ((ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8 ∗
        ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗ memRegion (ss + 40#64) 8 ∗
        ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ memRegion (ss + 64#64) 8) =
      (((ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8) ∗
       (((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗ memRegion (ss + 40#64) 8) ∗
       (((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ memRegion (ss + 64#64) 8)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

end DropsCommon

@[reducible]
def ssTail3HeadersAt_shared_lb (ss : BitVec 64) (pCap pPtr kCap kPtr : BitVec 64)
    (G : SessionGhost) : SepProp :=
  ((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32 ∗
  ((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16 ∗
  ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗ memRegion (ss + 112#64) 8

namespace DropsCommon

theorem ssTail3_entails_dealloc (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost) :
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      vecGhostAt A G.alice (ss + 0x60#64) ⊢
    ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
      ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A pCap pPtr ∗
      sgnPinDealloc A kCap kPtr ∗
      vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩ := by
  have h1 := optTailVecAt_entails_dealloc A 48 (by decide) (by decide) (ss + 248#64) G.pending
  have h2 := optTailVecAt_entails_dealloc A 32 (by decide) (by decide) (ss + 296#64) G.kyber
  have h3 := vecGhostAt_entails_pin_dealloc A G.alice (ss + 96#64)
  have ha1 : (ss + 248#64) + 8#64 = ss + 256#64 := by bv_omega
  have ha2 : (ss + 248#64) + 16#64 = ss + 264#64 := by bv_omega
  have hb1 : (ss + 296#64) + 8#64 = ss + 304#64 := by bv_omega
  have hb2 : (ss + 296#64) + 16#64 = ss + 312#64 := by bv_omega
  have hc1 : (ss + 96#64) + 8#64 = ss + 104#64 := by bv_omega
  have hc2 : (ss + 96#64) + 16#64 = ss + 112#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pCap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kCap
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kPtr
  refine Entails.sepExists_right pCap (Entails.sepExists_right pPtr
    (Entails.sepExists_right kCap (Entails.sepExists_right kPtr ?_)))
  unfold ssTail3HeadersAt_shared_lb
  exact Entails.of_eq (by ac_rfl)

theorem ssTail3HeadersAt_entails_memRegions (ss : BitVec 64)
    (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) :
    ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ⊢
      memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24 := by
  unfold ssTail3HeadersAt_shared_lb
  have h1 := header_cells_entails_memRegion_48_shared_lb (ss + 248#64) pCap pPtr
  have h2 := header_cells_entails_memRegion_32 (ss + 296#64) kCap kPtr
  have h3 := header_cells_entails_memRegion_24 (ss + 96#64) G.alice.cap G.alice.ptr
  have ha1 : (ss + 248#64) + 8#64 = ss + 256#64 := by bv_omega
  have ha2 : (ss + 248#64) + 16#64 = ss + 264#64 := by bv_omega
  have hb1 : (ss + 296#64) + 8#64 = ss + 304#64 := by bv_omega
  have hb2 : (ss + 296#64) + 16#64 = ss + 312#64 := by bv_omega
  have hc1 : (ss + 96#64) + 8#64 = ss + 104#64 := by bv_omega
  have hc2 : (ss + 96#64) + 16#64 = ss + 112#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [hc1, hc2] at h3
  have hgroup :
      (((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32 ∗
        ((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16 ∗
        ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗ memRegion (ss + 112#64) 8) =
      ((((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32) ∗
       (((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16) ∗
       (((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗ memRegion (ss + 112#64) 8)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

theorem sessionStateAt_entails_dealloc (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
        (ssFirst3HeadersAt_shared_lb ss G ∗
          vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A G.root) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (ss + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
        memRegion (ss + 328#64) 16 := by
  unfold sessionStateAt
  apply Entails.pure_left; rintro ⟨_, _, _, _, hreg, _, _⟩
  have hreord :
      (vecGhostAt A G.localIk ss ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds)) =
      ((vecGhostAt A G.localIk ss ∗
          vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
          vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey)) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
          optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
          vecGhostAt A G.alice (ss + 0x60#64)) ∗
        vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        (((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
          ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
          ((ss + 0x150#64) ↦ₛ G.regIds))) := by ac_rfl
  rw [hreord]
  have h1 := ssFirst3_entails_dealloc A ss G st
  have h2 := ssTail3_entails_dealloc A ss G
  have h3 := vecU8At_entails_pin_dealloc A (ss + 120#64) G.pq st.pqRatchetState
  have hpq1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
  have hpq2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
  rw [hpq1, hpq2] at h3
  have h4 := sessionTail_entails_memRegion_16_shared_lb ss st.sessionVersion st.previousCounter G.regIds hreg
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono h2 (sepConj_mono h3 h4))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pCap; refine Entails.sepExists_right pCap ?_
  apply Entails.sepExists_elim; intro pPtr; refine Entails.sepExists_right pPtr ?_
  apply Entails.sepExists_elim; intro kCap; refine Entails.sepExists_right kCap ?_
  apply Entails.sepExists_elim; intro kPtr; refine Entails.sepExists_right kPtr ?_
  exact Entails.of_eq (by ac_rfl)

end DropsCommon

/-! ## Common WP and stack helpers -/

theorem SepWP_align_pre_shared_lb {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

theorem SepWP_false_elim_shared_lb {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

theorem SepWP_false_elim_left_shared_lb {prog : Program} {target_pc : BitVec 64} {s : State}
    {Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

namespace DropsCommon

abbrev SepWP.align_pre := @SepWP_align_pre_shared_lb
abbrev SepWP.false_elim := @SepWP_false_elim_shared_lb
abbrev SepWP.false_elim_left := @SepWP_false_elim_left_shared_lb

theorem header24_weaken (v cap ptr : BitVec 64) (Rest : SepProp) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗ Rest ⊢
      memRegion v 24 ∗ Rest := by
  have heq :
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗ Rest) =
      (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗ Rest) := by ac_rfl
  rw [heq]
  exact sepConj_mono_left (header_cells_entails_memRegion_24 v cap ptr)

theorem drop4_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {traceProp : State → Prop} {rest : State → Prop}
    (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

end DropsCommon

theorem pq_header24_weaken_shared_lb (ss cap ptr : BitVec 64) (Rest : SepProp) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗ Rest ⊢
      memRegion (ss + 120#64) 24 ∗ Rest := by
  have h1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
  have h2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
  rw [← h1, ← h2]
  exact DropsCommon.header24_weaken (ss + 120#64) cap ptr Rest

theorem drop6_strengthen_post_shared_lb {prog : Program} {target_pc : BitVec 64} {s : State}
    {P R : SepProp} {S₁ S₂ : SepProp}
    {PostRest : State → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {traceProp : State → Prop} {rest : State → Prop}
    (himp : S₁ ⊢ S₂)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₁ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ x_4, ∃∗ x_5,
          ⌜traceProp sf⌝ ∗ S₂ ∗ PostRest sf x x_1 x_2 x_3 x_4 x_5) ∧ rest sf) := by
  refine SepWP.mono h fun sf _ _ _ ⟨h1, h2⟩ => ⟨fun hm => ?_, h2⟩
  refine Satisfies.mono ?_ (h1 hm)
  apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_
  apply Entails.sepExists_elim; intro x_1; refine Entails.sepExists_right x_1 ?_
  apply Entails.sepExists_elim; intro x_2; refine Entails.sepExists_right x_2 ?_
  apply Entails.sepExists_elim; intro x_3; refine Entails.sepExists_right x_3 ?_
  apply Entails.sepExists_elim; intro x_4; refine Entails.sepExists_right x_4 ?_
  apply Entails.sepExists_elim; intro x_5; refine Entails.sepExists_right x_5 ?_
  exact sepConj_mono_right (sepConj_mono_left himp)

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
