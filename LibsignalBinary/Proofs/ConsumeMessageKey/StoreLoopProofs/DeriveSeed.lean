/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
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

theorem leBytes_4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  change [BitVec.ofNat 8 (w.toNat / 1), BitVec.ofNat 8 (w.toNat / 256),
          BitVec.ofNat 8 (w.toNat / 65536), BitVec.ofNat 8 (w.toNat / 16777216)] =
    [BitVec.extractLsb' 0 8 w, BitVec.extractLsb' 8 8 w,
     BitVec.extractLsb' 16 8 w, BitVec.extractLsb' 24 8 w]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']
  · congr 1
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
    · congr 1
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
      · congr 1
        · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem pointsToBytes_chainKeyBytes (a : BitVec 64) (ck : CryptoGames.LibsignalSession.ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  rw [pointsToBytes_append, keyToBytes32_length, leBytes_4_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

theorem memRegion_one_eq_exists_byte (a : BitVec 64) :
    memRegion a 1 = ∃∗ b : BitVec 8, a ↦₈ b :=
  IsBlock.eq (IsBlock.memRegion a 1)
    (IsBlock.sepExists fun b => IsBlock.pointsTo8 a b)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_256_split_hmac (sp0 : BitVec 64) :
    memRegion (sp0 - 352#64) 256 =
      ∃∗ b0 : BitVec 8,
        memRegion (sp0 - 352#64) 32 ∗
          ((sp0 - 320#64) ↦₈ b0) ∗
          memRegion (sp0 - 319#64) 95 ∗
          memRegion (sp0 - 224#64) 32 ∗
          memRegion (sp0 - 192#64) 96 := by
  rw [show (256 : Nat) = 32 + 224 from rfl, memRegion_split (sp0 - 352#64) 32 224 (by decide),
      show (224 : Nat) = 1 + 223 from rfl, memRegion_split (sp0 - 352#64 + 32#64) 1 223 (by decide),
      show (223 : Nat) = 95 + 128 from rfl, memRegion_split (sp0 - 352#64 + 32#64 + 1#64) 95 128 (by decide),
      show (128 : Nat) = 32 + 96 from rfl, memRegion_split (sp0 - 352#64 + 32#64 + 1#64 + 95#64) 32 96 (by decide)]
  have h1 : sp0 - 352#64 + 32#64 = sp0 - 320#64 := by bv_arith
  have h2 : sp0 - 352#64 + 32#64 + 1#64 = sp0 - 319#64 := by bv_arith
  have h3 : sp0 - 352#64 + 32#64 + 1#64 + 95#64 = sp0 - 224#64 := by bv_arith
  have h4 : sp0 - 352#64 + 32#64 + 1#64 + 95#64 + 32#64 = sp0 - 192#64 := by bv_arith
  rw [h4, h3, h2, h1, memRegion_one_eq_exists_byte (sp0 - 320#64),
      sepExists_sepConj_left, sepExists_sepConj_right]

theorem pointsTo8_eq_pointsToBytes_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem stackAt_7712_eq_hmac (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 5664 ∗ stackAt sp 2048 := by
  simp only [stackAt]
  rw [show (7712 : Nat) = 5664 + 2048 from rfl, memRegion_split _ 5664 2048 (by decide)]
  have h : sp - 7712#64 + BitVec.ofNat 64 5664 = sp - 2048#64 := by bv_arith
  rw [h]

theorem stackAt_7712_eq_alloc (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 3616 ∗ stackAt sp allocHookStack := by
  simp only [stackAt, allocHookStack]
  rw [show (7712 : Nat) = 3616 + 4096 from rfl, memRegion_split _ 3616 4096 (by decide)]
  have h : sp - 7712#64 + BitVec.ofNat 64 3616 = sp - 4096#64 := by bv_arith
  rw [h]

theorem stackAt_7712_eq_find (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 6688 ∗ stackAt sp 1024 := by
  simp only [stackAt]
  rw [show (7712 : Nat) = 6688 + 1024 from rfl, memRegion_split _ 6688 1024 (by decide)]
  have h : sp - 7712#64 + BitVec.ofNat 64 6688 = sp - 1024#64 := by bv_arith
  rw [h]

theorem cmkLoopFrame_eq_deriveSeed (sp0 ret : BitVec 64) (counter : BitVec 32) :
    cmkLoopFrame sp0 ret counter =
      ∃∗ b0 : BitVec 8,
        memRegion (sp0 - 480#64) 112 ∗
          ((sp0 - 368#64) ↦₆₄ ret) ∗
          memRegion (sp0 - 360#64) 4 ∗
          ((sp0 - 356#64) ↦₃₂ counter) ∗
          memRegion (sp0 - 352#64) 32 ∗
          ((sp0 - 320#64) ↦₈ b0) ∗
          memRegion (sp0 - 319#64) 95 ∗
          memRegion (sp0 - 224#64) 32 ∗
          memRegion (sp0 - 192#64) 96 := by
  unfold cmkLoopFrame
  rw [memRegion_256_split_hmac, sepExists_sepConj_right, sepExists_sepConj_right,
      sepExists_sepConj_right, sepExists_sepConj_right]

theorem sepWP_elim_inv {prog : Program} {img : Obj.Image} {mid : BitVec 64}
    {s : State} {P R : SepProp} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hwp : SepWP prog mid s P post) :
    ∃ sm, Steps prog s sm ∧ sm.pc = mid ∧ sm.status = .Running ∧
      img.FrozenLoaded sm ∧ sm.symtab = img.symtab ∧
      prog.CodeLoaded sm.mem ∧
      ∃ Pm, (sm.mem ⊨ Pm ∗ R) ∧ post sm Pm := by
  rcases hwp.elim hm hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sm, hsteps, hpc, hrun, hfl.of_keepsFrozen hsteps.keepsFrozen,
      hsteps.symtab_eq.trans hsym, hsteps.codeLoaded hL, Pm, hmm, hpost⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem reaches_outcome_of_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {img : Obj.Image}
    (h : subroutine_ok prog entry (spec.inImage img))
    (x : α) (R : SepProp) (s : State)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hpre : s.mem ⊨ spec.pre x s ∗ R) (hsp : s.spAligned = true) :
    reaches_outcome prog spec x R s s := by
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hfl, hsym⟩, hpre⟩
  exact (h.to_outcome x R s hpc hrun hpre' hsp).mono_outcome fun _ hout => hout

theorem allocFailedIn_of_eq {F : ShaState → List (BitVec 8) → ShaState} {x : ConsumeMessageKeyGhost}
    {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    ((x.model F).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace := by
  refine ⟨Or.inr ?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem memRegion_32_eq_exists_words (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split a 8 24 (by decide),
      show (24 : Nat) = 8 + 16 from rfl, memRegion_split (a + 8#64) 8 16 (by decide),
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_arith
  have h24 : a + 8#64 + 8#64 + 8#64 = a + 24#64 := by bv_arith
  rw [h24, h16, memRegion_eight a, sepExists_sepConj_left]
  apply congrArg SepProp.sepExists; funext w0
  rw [memRegion_eight (a + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext w1
  rw [memRegion_eight (a + 16#64), sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext w2
  rw [memRegion_eight (a + 24#64), sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]

theorem vecU8Buf_32_of_alloc (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr ≠ 0) (hlen : bs.length = 32) :
    (A.live ptr 32 1 ∗ (ptr ↦ₛ bs)) ⊢ vecU8Buf A 32#64 ptr bs := by
  unfold vecU8Buf
  have hcap : (32#64 : BitVec 64) ≠ 0 := by decide
  have hcap_toNat : (32#64 : BitVec 64).toNat = 32 := rfl
  simp only [hcap, ↓reduceIte, hcap_toNat, hlen, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨Nat.le_refl 32, by decide, hptr⟩ (Entails.refl _)

theorem ratchetAt_expose_for_findIndex (A : RustAlloc) (self : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState) (hne : 0 < stc.receiverChains.length) :
    ratchetAt A self Gc stc ⊢
      ⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
        stc.maxForwardJumps < 2 ^ 64 ∧
        stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
        Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
      (self ↦₆₄ Gc.chainsCap) ∗
      ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
      A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
      arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
      memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
        ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
      ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
      ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
      ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
      ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4 := by
  unfold ratchetAt vecAt vecBuf
  apply Entails.pure_left
  rintro ⟨hchains_len, hpad_len, hmax_jumps⟩
  have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
    simp [hchains_len]
  rw [hzip_len]
  have hpull1 :
      ((vecHeader self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        (⌜stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
          Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0⌝ ∗
         if Gc.chainsCap = 0 then emp
         else
           A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
             memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
               ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104))) ∗
       ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
       ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
       ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) =
      (⌜stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
        Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0⌝ ∗
       (vecHeader self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        (if Gc.chainsCap = 0 then emp
         else
           A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
             arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
             memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
               ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104)) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4)) := by
    ac_rfl
  rw [hpull1]
  apply Entails.pure_left
  rintro ⟨hcap_le, hcap_lt, hptr_ne⟩
  have hcap_ne : Gc.chainsCap ≠ 0 := by
    intro h0; rw [h0] at hcap_le; change stc.receiverChains.length ≤ 0 at hcap_le; omega
  simp only [hcap_ne, ↓reduceIte]
  apply Entails.pure_right
    ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩
  unfold vecHeader
  have hpull2 :
      (((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length)) ∗
        (A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
          memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
            ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104)) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) =
      ((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
        ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) := by
    ac_rfl
  rw [hpull2]
  exact Entails.refl _

theorem ratchetAt_reassemble_after_findIndex (A : RustAlloc) (self : BitVec 64)
    (Gc : RatchetGhost) (stc : RatchetState)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hcap_ne : Gc.chainsCap ≠ 0) :
    ((self ↦₆₄ Gc.chainsCap) ∗
      ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
      ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
      A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
      arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
      memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
        ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
      ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
      ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
      ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
      ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) ⊢
      ratchetAt A self Gc stc := by
  unfold ratchetAt vecAt vecBuf
  have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
    simp [hchains_len]
  rw [hzip_len]
  simp only [hcap_ne, ↓reduceIte]
  apply Entails.pure_right ⟨hchains_len, hpad_len, hmax_jumps⟩
  have hhdr :
      vecHeader self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) =
        ((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length)) := rfl
  rw [hhdr]
  have hpull :
      ((self ↦₆₄ Gc.chainsCap) ∗
        ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
        ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) =
      ((((self ↦₆₄ Gc.chainsCap) ∗ ((self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
          ((self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length)) ∗
        (A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
          arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
          memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
             ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104))) ∗
       ((self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
       ((self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
       ((self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (self + 172#64) 4) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_left
  apply sepConj_mono_right
  exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr_ne⟩ (Entails.refl _)

theorem steps_of_sepWPp {prog : Program} {img : Obj.Image} {ret : BitVec 64}
    {s : State} {P R : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hm : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hwp : SepWPp prog ret s P Q Qp) :
    ∃ sf, Steps prog s sf ∧
      ((sf.pc = ret ∧ sf.status = .Running ∧ img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ Q sf P_f) ∨
       (sf.status = .Panicked ∧ ∃ P_f, (sf.mem ⊨ P_f ∗ R) ∧ Qp sf P_f)) := by
  rcases hwp R hm hL with
    ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, hfl.of_keepsFrozen hsteps.keepsFrozen,
      hsteps.symtab_eq.trans hsym, P_f, hmf, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr ⟨hpan, P_f, hmf, hqp⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem ci_lt_and_find_match {Gc : RatchetGhost} {stc : RatchetState}
    {their : PublicKey} {ci : Nat} {chc : ReceiverChain}
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hfind : stc.findReceiverChainIndex their = some ci)
    (hchc : stc.receiverChains[ci]? = some chc) :
    ci < stc.receiverChains.length ∧
      ((Gc.chains.zip stc.receiverChains).map (·.2)).findIdx?
        (fun c => c.senderRatchetKey == their) = some ci := by
  refine ⟨(List.getElem?_eq_some_iff.mp hchc).1, ?_⟩
  rw [map_snd_zip_chains hchains_len]
  exact hfind

theorem bitvec_ofNat_lt_eq_false {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ule (BitVec.ofNat 64 a) = false := by
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
  omega

theorem words_entails_memRegion_32 (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ⊢
      memRegion a 32 := by
  rw [memRegion_32_eq_exists_words a]
  exact Entails.sepExists_right w0
    (Entails.sepExists_right w1
      (Entails.sepExists_right w2
        (Entails.sepExists_right w3 (Entails.refl _))))

theorem words_entails_vecU8Buf_32 (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8))
    {w0 w1 w2 w3 : BitVec 64} (hptr : ptr ≠ 0) (hlen : bs.length = 32)
    (hpts : ∀ a : BitVec 64, (a ↦ₛ bs) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) :
    (A.live ptr 32 1 ∗ (ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗
      ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3)) ⊢
      vecU8Buf A 32#64 ptr bs := by
  rw [← hpts ptr]
  exact vecU8Buf_32_of_alloc A ptr bs hptr hlen

theorem cmkLoopFrame_of_deriveSeed (sp0 ret : BitVec 64) (counter : BitVec 32)
    (b0 : BitVec 8) (w0 w1 w2 w3 : BitVec 64) :
    (memRegion (sp0 - 480#64) 112 ∗
      ((sp0 - 368#64) ↦₆₄ ret) ∗
      memRegion (sp0 - 360#64) 4 ∗
      ((sp0 - 356#64) ↦₃₂ counter) ∗
      memRegion (sp0 - 352#64) 32 ∗
      ((sp0 - 320#64) ↦₈ b0) ∗
      memRegion (sp0 - 319#64) 95 ∗
      ((sp0 - 224#64) ↦₆₄ w0) ∗ ((sp0 - 216#64) ↦₆₄ w1) ∗
      ((sp0 - 208#64) ↦₆₄ w2) ∗ ((sp0 - 200#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 192#64) 96) ⊢
      cmkLoopFrame sp0 ret counter := by
  rw [cmkLoopFrame_eq_deriveSeed sp0 ret counter]
  apply Entails.sepExists_right b0
  have h1 : sp0 - 216#64 = (sp0 - 224#64) + 8#64 := by bv_arith
  have h2 : sp0 - 208#64 = (sp0 - 224#64) + 16#64 := by bv_arith
  have h3 : sp0 - 200#64 = (sp0 - 224#64) + 24#64 := by bv_arith
  rw [h1, h2, h3]
  have hpull :
      (memRegion (sp0 - 480#64) 112 ∗
        ((sp0 - 368#64) ↦₆₄ ret) ∗
        memRegion (sp0 - 360#64) 4 ∗
        ((sp0 - 356#64) ↦₃₂ counter) ∗
        memRegion (sp0 - 352#64) 32 ∗
        ((sp0 - 320#64) ↦₈ b0) ∗
        memRegion (sp0 - 319#64) 95 ∗
        ((sp0 - 224#64) ↦₆₄ w0) ∗ (((sp0 - 224#64) + 8#64) ↦₆₄ w1) ∗
        (((sp0 - 224#64) + 16#64) ↦₆₄ w2) ∗ (((sp0 - 224#64) + 24#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 192#64) 96) =
      (memRegion (sp0 - 480#64) 112 ∗
        ((sp0 - 368#64) ↦₆₄ ret) ∗
        memRegion (sp0 - 360#64) 4 ∗
        ((sp0 - 356#64) ↦₃₂ counter) ∗
        memRegion (sp0 - 352#64) 32 ∗
        ((sp0 - 320#64) ↦₈ b0) ∗
        memRegion (sp0 - 319#64) 95 ∗
        (((sp0 - 224#64) ↦₆₄ w0) ∗ (((sp0 - 224#64) + 8#64) ↦₆₄ w1) ∗
         (((sp0 - 224#64) + 16#64) ↦₆₄ w2) ∗ (((sp0 - 224#64) + 24#64) ↦₆₄ w3)) ∗
        memRegion (sp0 - 192#64) 96) := by ac_rfl
  rw [hpull]
  repeat' apply sepConj_mono_right
  exact sepConj_mono_left (words_entails_memRegion_32 (sp0 - 224#64) w0 w1 w2 w3)

theorem deriveSeed_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    DeriveSeedSpec F A alloc img := by
  intro hA himg hfind_ok hhmac_ok x Gc stc ckc ci chc R s0 s _hlt hfind_idx hchc hstate hL
  rcases hstate with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hfl, hsym, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, hx19_fn, hmem⟩
  have hx19 : s.readReg64 .x19 = 1#64 := hx19_fn rfl
  clear hx19_fn
  rw [sessionProg_eq_SP himg F alloc] at hL ⊢
  rw [cmkLoopPC_eq_fnAddr himg F alloc] at hpc
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hhmac := hmac_ok_at_cmk himg hhmac_ok
  have hshim := shim_ok_at (b := img.base) (F := F) (alloc := alloc) hfn (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  have halloc := alloc_ok_at (b := img.base) (F := F) hA hfn (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  have hfind := find_index_ok_at_cmk himg hfind_ok
  have hpanic := panic_at_handle_error (b := img.base) (F := F) (alloc := alloc) hfn (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  unfold Spec.inImage hmacSpec at hhmac
  unfold Spec.inImage findIndexSpec at hfind
  cmk_fetches_range img.base (Rust.withPanics (sessionExterns F alloc)) hfn 205 229
  cmk_fetches_range img.base (Rust.withPanics (sessionExterns F alloc)) hfn 621 624
  clear hfn
  have hpartB_eq := cmkInsertKeyPC_eq_fnAddr himg F alloc
  generalize_entry (SP img.base F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
  have hchains_pos : 0 < stc.receiverChains.length := by omega
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have hmsg1_len : ([1#8] : List (BitVec 8)).length = 1 := rfl
  have hseed_eq : (ckc.messageKeys F).seed = hmacWith F (keyToBytes32 ckc.key) [1#8] :=
    messageKeys_seed_eq F ckc
  have hseed_len : (hmacWith F (keyToBytes32 ckc.key) [1#8]).length = 32 :=
    hmacWith_length F (keyToBytes32 ckc.key) [1#8]
  obtain ⟨sw0, sw1, sw2, sw3, hseed_unpack, hseed_pts⟩ := exists_unpack64_of_length_32 hseed_len
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨Nat.zero_lt_succ 31, ⟨0, rfl⟩, by decide⟩
  have hwp : SepWPp (SP img.base F alloc) (entry + bv% (916)) s
      (cmkLoopHeap A img x Gc stc ckc s0)
      (fun sA P_f =>
        sA.sp = s0.sp - 480#64 ∧ sA.spAligned = true ∧
        sA.readReg64 .x29 = s0.sp - 96#64 ∧
        (sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0) ∧
        ∃ seedPtr, InsertKeyRegs x Gc ckc ci seedPtr s0 sA ∧ seedPtr ≠ 0#64 ∧
          (sA.mem ⊨ P_f ∗ R →
            sA.mem ⊨ (cmkLoopHeap A img x Gc stc ckc s0 ∗
              vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ∗ R))
      (fun sA P_f => (sA.mem ⊨ P_f ∗ R) → (sA.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 sA ∗ R)) := by
    conv =>
      arg 4
      unfold cmkLoopHeap
      rw [← hsp, pointsToBytes_chainKeyBytes x.ckA ckc, cmkLoopFrame_eq_deriveSeed s0.sp x.ret x.counter]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro b0
    apply SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl1 hsym1
    rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 1#8,
        stackAt_7712_eq_hmac s.sp]
    apply SepWPp.of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (864))
    wp_call hhmac (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [1#8])
    apply SepWP.fold (Entails.of_eq (stackAt_7712_eq_hmac s.sp).symm) (by sep_focus)
    rw [stackAt_7712_eq_alloc s.sp]
    wp_steps
    wp_apply
    have hsp1 : sf_1.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    wp_steps
    wp_apply
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hfl2 hsym2
    have hsp2 : sf_2.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    rw [hsp1]
    apply SepWPp.fold (Entails.of_eq (stackAt_7712_eq_alloc s.sp).symm) (by sep_focus)
    by_cases hoom : sf_2.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_pure_left_comm, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
      simpa only [consumeMessageKeySpec, Spec.inImage, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom' : sf_2.readReg64 Reg.x0 ≠ 0 := hoom
      have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [hoom', ite_false, sepConj_pure_left_comm, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_halign_alloc, htrace_alloc⟩ => ?_
      apply SepWPp.fold (ratchetAt_expose_for_findIndex A x.self Gc stc hchains_pos) (by sep_focus)
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩ => ?_
      have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
        simp [hchains_len]
      have hzip_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 := by
        rw [hzip_len]; omega
      have hlen_lt_64 : stc.receiverChains.length < 2 ^ 64 := by omega
      have hlen_toNat : (BitVec.ofNat 64 stc.receiverChains.length).toNat = (Gc.chains.zip stc.receiverChains).length := by
        rw [hzip_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt_64]
      have ⟨_, hfind_zip⟩ := ci_lt_and_find_match hchains_len hfind_idx hchc
      rw [hseed_pts (s0.sp - 224#64),
          memRegion_32_eq_exists_words (sf_2.readReg64 Reg.x0)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro dw0
      apply SepWPp.exists_elim; intro dw1
      apply SepWPp.exists_elim; intro dw2
      apply SepWPp.exists_elim; intro dw3
      apply SepWPp.of_sepWP_inv hfl2 hsym2 (mid := entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hfl3 hsym3
      rw [stackAt_7712_eq_find s.sp]
      apply SepWPp.of_sepWP_ret
      wp_apply
      rw [hsp2]
      apply SepWP.fold (Entails.of_eq (stackAt_7712_eq_find s.sp).symm) (by sep_focus)
      rw [hsp]
      have ⟨hx0_sf3, hx1_sf3⟩ : sf_3.readReg64 Reg.x0 = 1#64 ∧ (sf_3.readReg64 Reg.x1).toNat = ci := by
        simpa only [hfind_zip] using hpost_2
      have hx1_eq : sf_3.readReg64 Reg.x1 = BitVec.ofNat 64 ci := by
        apply BitVec.eq_of_toNat_eq
        rw [hx1_sf3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hcs_false : (BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = false :=
        bitvec_ofNat_lt_eq_false hci_lt hlen_lt_64
      wp_steps
      apply SepWP.fold
        (ratchetAt_reassemble_after_findIndex A x.self Gc stc
          hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne hcap_ne)
        (by sep_focus)
      apply SepWP.fold
        (words_entails_vecU8Buf_32 A (sf_2.readReg64 Reg.x0) (ckc.messageKeys F).seed
          hoom' (hseed_eq ▸ hseed_len) (hseed_eq ▸ hseed_pts))
        (by sep_focus)
      apply SepWP.fold
        (cmkLoopFrame_of_deriveSeed s0.sp x.ret x.counter 1#8 sw0 sw1 sw2 sw3)
        (by sep_focus)
      apply SepWP.fold
        (Entails.of_eq (pointsToBytes_chainKeyBytes x.ckA ckc).symm)
        (by sep_focus)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned, hsp_sf_3, hsp2, hsp] using hsp_align,
         by simp only [wp_norm, arm64_norm, *],
         ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
         sf_2.readReg64 Reg.x0, ?_, hoom, fun hm => ?_⟩
      · unfold InsertKeyRegs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
      · exact Satisfies.mono (Entails.of_eq (by unfold cmkLoopHeap; ac_rfl)) hm
  obtain ⟨sA, hsteps, ⟨hpcA, hrunA, hflA, hsymA, P_f, hmf, hspA, hsp_alignA, hx29A, htraceA,
      seedPtr, hregsA, hseed_ne, hmemA⟩ | ⟨hpanA, P_f, hmf, hqp⟩⟩ :=
    steps_of_sepWPp hfl hsym hmem hL hwp
  · refine ⟨sA, hsteps, Or.inl ⟨seedPtr, ?_⟩⟩
    exact ⟨hpartB_eq.symm ▸ hpcA, ⟨hrunA, hspA, hsp0_align, hsp_alignA, hx29A, htraceA.1, hflA, hsymA, htraceA.2⟩,
      hregsA, hseed_ne, hmemA hmf⟩
  · exact ⟨sA, hsteps, Or.inr ⟨hpanA, hqp hmf⟩⟩

set_option maxRecDepth 200000 in
private theorem deriveSeed_placed_ok_of_hmac [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    {Inv : Memory → Prop}
    (hinv_kf : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    (hinv_cl : ∀ {m}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hhmac_at : ∀ {sm : State}, Inv sm.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F sm))
    (hA : CmkAllocHooks A H) (hfind_ok : FindIndexPlacedOk H A)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (R : SepProp) (s0 s : State)
    (_hlt : ckc.index < x.counter)
    (hfind_idx : stc.findReceiverChainIndex x.their = some ci)
    (hchc : stc.receiverChains[ci]? = some chc)
    (hstate : CmkLoopState_placed A x Gc stc ckc R cmkLoopPC_placed s0 s)
    (hL : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem)
    (hinv : Inv s.mem) :
    ∃ sA, Steps ((blkPC_24).rebase (blkPl_24).base H) s sA ∧
      ((∃ seedPtr, InsertKeyState_placed F A x Gc stc ckc ci seedPtr R s0 sA) ∨
       (sA.status = .Panicked ∧ (sA.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sA ∗ R))) := by
  rcases hstate with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, hx19_fn, hmem⟩
  have hx19 : s.readReg64 .x19 = 1#64 := hx19_fn rfl
  clear hx19_fn
  have hpc' : s.pc = (blkPl_24).base + 820#64 := hpc
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have halloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym) (rustAllocSpec A) :=
    cmk_hook_ok_of_mem hA.1
  have hpanic : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkHandleErrorSym) = some Rust.panicked :=
    (cmk_externAt?_of_mem).trans hA.2.2.2.1
  have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
  have hchains_pos : 0 < stc.receiverChains.length := by omega
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have hmsg1_len : ([1#8] : List (BitVec 8)).length = 1 := rfl
  have hseed_eq : (ckc.messageKeys F).seed = hmacWith F (keyToBytes32 ckc.key) [1#8] :=
    messageKeys_seed_eq F ckc
  have hseed_len : (hmacWith F (keyToBytes32 ckc.key) [1#8]).length = 32 :=
    hmacWith_length F (keyToBytes32 ckc.key) [1#8]
  obtain ⟨sw0, sw1, sw2, sw3, hseed_unpack, hseed_pts⟩ := exists_unpack64_of_length_32 hseed_len
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨Nat.zero_lt_succ 31, ⟨0, rfl⟩, by decide⟩
  have hwp : SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + bv% (916)) s
      (cmkLoopHeap_placed A x Gc stc ckc s0)
      (fun sA P_f =>
        sA.sp = s0.sp - 480#64 ∧ sA.spAligned = true ∧
        sA.readReg64 .x29 = s0.sp - 96#64 ∧
        (sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0) ∧
        ∃ seedPtr, InsertKeyRegs x Gc ckc ci seedPtr s0 sA ∧ seedPtr ≠ 0#64 ∧
          (sA.mem ⊨ P_f ∗ R →
            sA.mem ⊨ (cmkLoopHeap_placed A x Gc stc ckc s0 ∗
              vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ∗ R))
      (fun sA P_f => (sA.mem ⊨ P_f ∗ R) → (sA.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sA ∗ R)) := by
    conv =>
      arg 4
      unfold cmkLoopHeap_placed
      rw [← hsp, pointsToBytes_chainKeyBytes x.ckA ckc, cmkLoopFrame_eq_deriveSeed s0.sp x.ret x.counter]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro b0
    apply SepWPp.seq_frozen hinv_kf hinv (mid := lsmpl.base 73)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hinv1
    have hhmac1 := hhmac_at hinv1
    have hcl1 := hinv_cl hinv1
    rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 1#8,
        stackAt_7712_eq_hmac s.sp]
    apply sepWPp_seq_lscl (mid := (blkPl_24).base + bv% (864)) hcl1
    wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [1#8])
    apply SepWP.fold (Entails.of_eq (stackAt_7712_eq_hmac s.sp).symm) (by sep_focus)
    rw [stackAt_7712_eq_alloc s.sp]
    wp_steps
    wp_call hshim ()
    have hsp1 : sf_1.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    wp_steps
    wp_call halloc (32, 1)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl2
    have hsp2 : sf_2.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
    rw [hsp1]
    apply SepWPp.fold (Entails.of_eq (stackAt_7712_eq_alloc s.sp).symm) (by sep_focus)
    by_cases hoom : sf_2.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_pure_left_comm, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace_oom => ?_
      apply SepWPp.of_sepWP (mid := lsρ cmkHandleErrorSym)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic fun hm => ?_
      simpa only [cmkPlacedSpec, withLsCodeLoaded, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · have hoom' : sf_2.readReg64 Reg.x0 ≠ 0 := hoom
      have hoom_beq : (sf_2.readReg64 Reg.x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
      simp only [hoom', ite_false, sepConj_pure_left_comm, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_halign_alloc, htrace_alloc⟩ => ?_
      apply SepWPp.fold (ratchetAt_expose_for_findIndex A x.self Gc stc hchains_pos) (by sep_focus)
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, hcap_ne⟩ => ?_
      have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
        simp [hchains_len]
      have hzip_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 := by
        rw [hzip_len]; omega
      have hlen_lt_64 : stc.receiverChains.length < 2 ^ 64 := by omega
      have hlen_toNat : (BitVec.ofNat 64 stc.receiverChains.length).toNat = (Gc.chains.zip stc.receiverChains).length := by
        rw [hzip_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt_64]
      have ⟨_, hfind_zip⟩ := ci_lt_and_find_match hchains_len hfind_idx hchc
      rw [hseed_pts (s0.sp - 224#64),
          memRegion_32_eq_exists_words (sf_2.readReg64 Reg.x0)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro dw0
      apply SepWPp.exists_elim; intro dw1
      apply SepWPp.exists_elim; intro dw2
      apply SepWPp.exists_elim; intro dw3
      apply sepWPp_seq_lscl (mid := lsmpl.base 26) hcl2
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hcl3
      have hfind1 := findIndex_placed_ok_at_state hfind_ok hcl3
      rw [stackAt_7712_eq_find s.sp]
      apply SepWPp.of_sepWP_ret
      wp_call hfind1 (Gc.chainsPtr, Gc.chains.zip stc.receiverChains, x.theirA, x.their)
      rw [hsp2]
      apply SepWP.fold (Entails.of_eq (stackAt_7712_eq_find s.sp).symm) (by sep_focus)
      rw [hsp]
      have ⟨hx0_sf3, hx1_sf3⟩ : sf_3.readReg64 Reg.x0 = 1#64 ∧ (sf_3.readReg64 Reg.x1).toNat = ci := by
        simpa only [hfind_zip] using hpost_1
      have hx1_eq : sf_3.readReg64 Reg.x1 = BitVec.ofNat 64 ci := by
        apply BitVec.eq_of_toNat_eq
        rw [hx1_sf3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hcs_false : (BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = false :=
        bitvec_ofNat_lt_eq_false hci_lt hlen_lt_64
      wp_steps
      apply SepWP.fold
        (ratchetAt_reassemble_after_findIndex A x.self Gc stc
          hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne hcap_ne)
        (by sep_focus)
      apply SepWP.fold
        (words_entails_vecU8Buf_32 A (sf_2.readReg64 Reg.x0) (ckc.messageKeys F).seed
          hoom' (hseed_eq ▸ hseed_len) (hseed_eq ▸ hseed_pts))
        (by sep_focus)
      apply SepWP.fold
        (cmkLoopFrame_of_deriveSeed s0.sp x.ret x.counter 1#8 sw0 sw1 sw2 sw3)
        (by sep_focus)
      apply SepWP.fold
        (Entails.of_eq (pointsToBytes_chainKeyBytes x.ckA ckc).symm)
        (by sep_focus)
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned, hsp_sf_2, hsp2, hsp] using hsp_align,
         by simp only [wp_norm, arm64_norm, *],
         ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
         sf_2.readReg64 Reg.x0, ?_, hoom, fun hm => ?_⟩
      · unfold InsertKeyRegs
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
      · exact Satisfies.mono (Entails.of_eq (by unfold cmkLoopHeap_placed; ac_rfl)) hm
  obtain ⟨sA, hsteps, ⟨hpcA, hrunA, hclA, P_f, hmf, hspA, hsp_alignA, hx29A, htraceA,
      seedPtr, hregsA, hseed_ne, hmemA⟩ | ⟨hpanA, P_f, hmf, hqp⟩⟩ :=
    steps_of_sepWPp_placed hcl hmem hL hwp
  · refine ⟨sA, hsteps, Or.inl ⟨seedPtr, ?_⟩⟩
    exact ⟨hpcA, ⟨hrunA, hspA, hsp0_align, hsp_alignA, hx29A, htraceA.1, hclA, htraceA.2⟩,
      hregsA, hseed_ne, hmemA hmf⟩
  · exact ⟨sA, hsteps, Or.inr ⟨hpanA, hqp hmf⟩⟩

theorem deriveSeed_placed_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    DeriveSeedPlacedSpec F A H := by
  intro hA hfind_ok hhmac_ok x Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hstate hL
  let ⟨_, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hstate
  exact deriveSeed_placed_ok_of_hmac F A H
    (Inv := LibsignalCodeLoaded lsmpl)
    (fun _ _ h hkf => h.of_keepsFrozen hkf) (fun h => h)
    (fun h => hmac_placed_ok_at_state hhmac_ok h)
    hA hfind_ok x Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hstate hL hcl

theorem deriveSeed_placed_ro_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    DeriveSeedPlacedRoSpec F A H := by
  intro hA hfind_ok hhmac_ok x Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hstate hL hro
  let ⟨_, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hstate
  exact deriveSeed_placed_ok_of_hmac F A H
    (Inv := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    (fun h => h.1)
    (fun ⟨hc, hr⟩ => hmac_placed_ro_ok_at_state hhmac_ok hc hr)
    hA hfind_ok x Gc stc ckc ci chc R s0 s hlt hfind_idx hchc hstate hL ⟨hcl, hro⟩

end CryptoVerification.LibsignalSession.StoreLoop
