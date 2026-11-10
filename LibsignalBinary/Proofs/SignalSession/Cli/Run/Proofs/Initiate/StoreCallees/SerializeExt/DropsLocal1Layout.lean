/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.DropsPure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.DropsLocal1Layout
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSession
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.DropsX

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

class PullPure (P : SepProp) (φ : outParam Prop) (Q : outParam SepProp) : Prop where
  eq : P = ⌜φ⌝ ∗ Q

instance (priority := 300) (φ : Prop) (R : SepProp) : PullPure (⌜φ⌝ ∗ R) φ R where
  eq := rfl

instance (priority := 250) (A : SepProp) (φ : Prop) : PullPure (A ∗ ⌜φ⌝) φ A where
  eq := sepConj_comm A ⌜φ⌝

instance (priority := 100) {A A' B : SepProp} {φ : Prop} [h : PullPure A φ A'] :
    PullPure (A ∗ B) φ (A' ∗ B) where
  eq := by rw [h.eq]; ac_rfl

instance (priority := 50) {A B B' : SepProp} {φ : Prop} [h : PullPure B φ B'] :
    PullPure (A ∗ B) φ (A ∗ B') where
  eq := by rw [h.eq]; ac_rfl

theorem sepWP_pull_pure {prog : Program} {t : BitVec 64} {s : State}
    {P Q : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    [h : PullPure P φ Q] (k : φ → SepWP prog t s Q post) :
    SepWP prog t s P post := by
  rw [h.eq]
  exact SepWP.pure_elim k

@[reducible]
def vecPinDeallocX (A : RustAlloc) (pin : VecPin) : SepProp :=
  if (pin.cap == 0#64) = true then emp
  else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗ A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat

@[reducible]
def sgnPinDeallocX (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

theorem vecU8At_entails_pin_deallocX (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDeallocX
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases h0 : pin.cap = 0
  · simp only [h0, ↓reduceIte]; exact Entails.refl _
  · simp only [h0, ↓reduceIte]
    have hpos : 0 < pin.cap.toNat :=
      Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
    exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)

theorem vecGhostAt_entails_pin_deallocX (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a ⊢
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A ⟨g.cap, g.ptr⟩ :=
  vecU8At_entails_pin_deallocX A a ⟨g.cap, g.ptr⟩ g.bytes

theorem optTailVecAt_entails_deallocX (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        sgnPinDeallocX A cap ptr := by
  unfold sgnPinDeallocX
  cases opt with
  | none =>
    unfold optTailVecAt
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
    unfold optTailVecAt
    apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat) := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      by_cases h0 : g.vec.cap = 0
      · simp only [h0, ↓reduceIte]; exact Entails.refl _
      · simp only [h0, ↓reduceIte]
        have hpos : 0 < g.vec.cap.toNat :=
          Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
        exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)
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
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗
             A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) := by
      ac_rfl
    rw [hpull1]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

theorem optChainKeyAt_entails_deallocX (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        sgnPinDeallocX A cap ptr := by
  unfold sgnPinDeallocX
  cases ck with
  | none =>
    unfold optChainKeyAt
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
    unfold optChainKeyAt
    have hvec : vecU8At A a pin.cap pin.ptr (keyToBytes32 c.key) ⊢
        (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          (if pin.cap.slt 1#64 = true then emp
           else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
             A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
      refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      by_cases h0 : pin.cap = 0
      · simp only [h0, ↓reduceIte]; exact Entails.refl _
      · simp only [h0, ↓reduceIte]
        have hpos : 0 < pin.cap.toNat :=
          Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
        exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)
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
           else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
             A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) =
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
            ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ∗
          (if pin.cap.slt 1#64 = true then emp
           else ⌜0 < pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63⌝ ∗
             A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat)) := by
      ac_rfl
    rw [hpull]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

theorem optSenderChainAt_some_entails_dealloc1X (A : RustAlloc) (a : BitVec 64)
    (g : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some g) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜g.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        ((a + 24#64) ↦₆₄ g.priv.cap) ∗ ((a + 32#64) ↦₆₄ g.priv.ptr) ∗ memRegion (a + 40#64) 8 ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr [] ∗
        ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 80#64) ↦₆₄ ckPtr) ∗ memRegion (a + 88#64) 16 ∗
        sgnPinDeallocX A ckCap ckPtr := by
  unfold optSenderChainAt
  apply Entails.pure_left; rintro ⟨_, _, _, _⟩
  have h1 : vecGhostAt A g.srk a ⊢
      ⌜g.srk.cap + 1#64 ≠ 0#64⌝ ∗
      (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ := by
    unfold vecGhostAt
    refine Entails.trans (vecU8At_entails_dealloc A a g.srk.cap g.srk.ptr g.srk.bytes) ?_
    unfold vecHeader vecPinDeallocX
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    refine Entails.pure_right (cap_add_one_ne_zero hcap_lt) ?_
    have hbeq : ((g.srk.cap == 0#64) = true) ↔ g.srk.cap = 0 := beq_iff_eq
    simp only [hbeq]
    rw [sepConj_assoc, sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
    by_cases h0 : g.srk.cap = 0
    · simp only [h0, ↓reduceIte]; exact Entails.refl _
    · simp only [h0, ↓reduceIte]
      have hpos : 0 < g.srk.cap.toNat :=
        Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
      exact Entails.pure_right ⟨hpos, hcap_lt⟩ (Entails.refl _)
  have h2 := vecGhostAt_entails_pin_deallocX A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_deallocX A g.ck (some sc.chainKey) (a + 72#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ckCap; refine Entails.sepExists_right ckCap ?_
  apply Entails.sepExists_elim; intro ckPtr; refine Entails.sepExists_right ckPtr ?_
  exact Entails.of_eq (by ac_rfl)

theorem ssFirst3_entails_deallocX (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    vecGhostAt A G.localIk ss ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ⊢
    ssFirst3HeadersAt ss G ∗
      vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
      vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDeallocX A G.root := by
  have h1 := vecGhostAt_entails_pin_deallocX A G.localIk ss
  have h2 := vecGhostAt_entails_pin_deallocX A G.remoteIk (ss + 24#64)
  have h3 := vecU8At_entails_pin_deallocX A (ss + 48#64) G.root (keyToBytes32 st.rootKey)
  have ha1 : (ss + 24#64) + 8#64 = ss + 32#64 := by bv_omega
  have ha2 : (ss + 24#64) + 16#64 = ss + 40#64 := by bv_omega
  have hb1 : (ss + 48#64) + 8#64 = ss + 56#64 := by bv_omega
  have hb2 : (ss + 48#64) + 16#64 = ss + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  unfold ssFirst3HeadersAt
  exact Entails.of_eq (by ac_rfl)

theorem ssTail3_entails_deallocX (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost) :
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      vecGhostAt A G.alice (ss + 0x60#64) ⊢
    ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
      ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDeallocX A pCap pPtr ∗
      sgnPinDeallocX A kCap kPtr ∗
      vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩ := by
  have h1 := optTailVecAt_entails_deallocX A 48 (by decide) (by decide) (ss + 248#64) G.pending
  have h2 := optTailVecAt_entails_deallocX A 32 (by decide) (by decide) (ss + 296#64) G.kyber
  have h3 := vecGhostAt_entails_pin_deallocX A G.alice (ss + 96#64)
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
  unfold ssTail3HeadersAt
  exact Entails.of_eq (by ac_rfl)

theorem sessionStateAt_entails_deallocX (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
        (ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A G.root) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A pCap pPtr ∗
          sgnPinDeallocX A kCap kPtr ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (ss + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
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
  have h1 := ssFirst3_entails_deallocX A ss G st
  have h2 := ssTail3_entails_deallocX A ss G
  have h3 := vecU8At_entails_pin_deallocX A (ss + 120#64) G.pq st.pqRatchetState
  have hpq1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
  have hpq2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
  rw [hpq1, hpq2] at h3
  have h4 := sessionTail_entails_memRegion_16 ss st.sessionVersion st.previousCounter G.regIds hreg
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono h2 (sepConj_mono h3 h4))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pCap; refine Entails.sepExists_right pCap ?_
  apply Entails.sepExists_elim; intro pPtr; refine Entails.sepExists_right pPtr ?_
  apply Entails.sepExists_elim; intro kCap; refine Entails.sepExists_right kCap ?_
  apply Entails.sepExists_elim; intro kPtr; refine Entails.sepExists_right kPtr ?_
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_ss_local1_split (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal1StackX =
      stackAt (sp - 32#64) Getters.dropVecChainStackX ∗ cells (sp - 32#64) 4 := by
  exact stackAt_split_cells sp Getters.dropVecChainStackX 4 (by decide)

theorem stackAt_dropVecChain_split_alloc (fsp : BitVec 64) :
    stackAt fsp Getters.dropVecChainStackX =
      memRegion (fsp - 16480#64) 96 ∗ stackAt fsp extHookStack := by
  rw [show Getters.dropVecChainStackX = extHookStack + 96 from rfl,
      stackAt_split_bottom' fsp extHookStack 96 (by decide)]
  rfl

theorem stackAt_dropVecChain_split_mk (fsp : BitVec 64) :
    stackAt fsp Getters.dropVecChainStackX =
      memRegion (fsp - 16480#64) 48 ∗ stackAt fsp Getters.dropVecMessageKeyStackX := by
  rw [show Getters.dropVecChainStackX = Getters.dropVecMessageKeyStackX + 48 from rfl,
      stackAt_split_bottom' fsp Getters.dropVecMessageKeyStackX 48 (by decide)]
  rfl

theorem stackAt_dropVecMessageKey_split_alloc (fsp : BitVec 64) :
    stackAt fsp Getters.dropVecMessageKeyStackX =
      memRegion (fsp - 16432#64) 48 ∗ stackAt fsp extHookStack := by
  rw [show Getters.dropVecMessageKeyStackX = extHookStack + 48 from rfl,
      stackAt_split_bottom' fsp extHookStack 48 (by decide)]
  rfl

theorem tail_stack_128_from_bottom (sp : BitVec 64) :
    memRegion (sp - 16512#64) 128 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) Getters.dropVecChainStackX ∗ cells (sp - 32#64) 4 := by
  rw [show (16512#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 128) from rfl,
      ← stackAt_split_bottom' sp extHookStack 128 (by decide),
      show extHookStack + 128 = dropSessionStructureLocal1StackX from rfl,
      ← stackAt_ss_local1_split sp]

theorem tail_dealloc_ss_local1_pre_weaken (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp : BitVec 64) (fp lr x19 v3 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 32#64) Getters.dropVecChainStackX ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    memRegion (ss + 120#64) 24 ∗ rest ∗ pool ∗
      memRegion (sp - 16512#64) 128 ∗ stackAt sp extHookStack ∗ live := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    have ha1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
    have ha2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
    rw [← ha1, ← ha2]
    exact header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 32#64) Getters.dropVecChainStackX ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      memRegion (sp - 16512#64) 128 ∗ stackAt sp extHookStack := by
    rw [tail_stack_128_from_bottom sp]
    cells_unfold
    refine Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x19 (Entails.sepExists_right v3 (Entails.refl _))))
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗
        stackAt (sp - 32#64) Getters.dropVecChainStackX ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗
         (stackAt (sp - 32#64) Getters.dropVecChainStackX ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem fnAddr_dropVecMessageKey_eq_ss_local1_add (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecMessageKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

theorem fnAddr_dropVecChain_eq_ss_local1_add (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName =
      (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

@[reducible]
def ssSender1HeadersAt (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) : SepProp :=
  ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8 ∗
  ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8 ∗
  ((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16

theorem ssSender1HeadersAt_entails_memRegions (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) :
    ssSender1HeadersAt ss sg ckCap ckPtr ⊢
      memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 := by
  unfold ssSender1HeadersAt
  have h1 := header_cells_entails_memRegion_24 (ss + 144#64) sg.srk.cap sg.srk.ptr
  have h2 := header_cells_entails_memRegion_24 (ss + 168#64) sg.priv.cap sg.priv.ptr
  have h3 := header_cells_entails_memRegion_32 (ss + 216#64) ckCap ckPtr
  have ha1 : (ss + 144#64) + 8#64 = ss + 152#64 := by bv_omega
  have ha2 : (ss + 144#64) + 16#64 = ss + 160#64 := by bv_omega
  have hb1 : (ss + 168#64) + 8#64 = ss + 176#64 := by bv_omega
  have hb2 : (ss + 168#64) + 16#64 = ss + 184#64 := by bv_omega
  have hc1 : (ss + 216#64) + 8#64 = ss + 224#64 := by bv_omega
  have hc2 : (ss + 216#64) + 16#64 = ss + 232#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [hc1, hc2] at h3
  have hgroup :
      (((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8 ∗
        ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8 ∗
        ((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16) =
      ((((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8) ∗
       (((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8) ∗
       (((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 24) (k := 24) (b' := ss + 168#64) rfl (by bv_omega) (by decide),
      show (memRegion (ss + 144#64) 24 ∗ memRegion (ss + 168#64) 24) ∗ memRegion (ss + 216#64) 32 =
        memRegion (ss + 144#64) 24 ∗ memRegion (ss + 168#64) 24 ∗ memRegion (ss + 216#64) 32 from sepConj_assoc _ _ _]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

theorem ssSender1_memRegions_entails_104 (ss : BitVec 64) :
    memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 ⊢
      memRegion (ss + 144#64) 104 := by
  have heq :
      (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) =
      (memRegion (ss + 144#64) 48 ∗ memRegion (ss + 192#64) 24 ∗ memRegion (ss + 216#64) 32) := by ac_rfl
  rw [heq,
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 48) (k := 56) (b' := ss + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 192#64) (n := 24) (k := 32) (b' := ss + 216#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem optSenderChainAt_some_entails_ss_local1X (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜sg.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (ssSender1HeadersAt ss sg ckCap ckPtr ∗
          vecPinDeallocX A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDeallocX A ckCap ckPtr) ∗
        vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] := by
  have h := optSenderChainAt_some_entails_dealloc1X A (ss + 144#64) sg sc
  have ha1 : (ss + 144#64) + 8#64 = ss + 152#64 := by bv_omega
  have ha2 : (ss + 144#64) + 16#64 = ss + 160#64 := by bv_omega
  have ha3 : (ss + 144#64) + 24#64 = ss + 168#64 := by bv_omega
  have ha4 : (ss + 144#64) + 32#64 = ss + 176#64 := by bv_omega
  have ha5 : (ss + 144#64) + 40#64 = ss + 184#64 := by bv_omega
  have ha6 : (ss + 144#64) + 48#64 = ss + 192#64 := by bv_omega
  have ha7 : (ss + 144#64) + 72#64 = ss + 216#64 := by bv_omega
  have ha8 : (ss + 144#64) + 80#64 = ss + 224#64 := by bv_omega
  have ha9 : (ss + 144#64) + 88#64 = ss + 232#64 := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9] at h
  refine Entails.trans h ?_
  apply Entails.sepExists_elim; intro ckCap; refine Entails.sepExists_right ckCap ?_
  apply Entails.sepExists_elim; intro ckPtr; refine Entails.sepExists_right ckPtr ?_
  unfold ssSender1HeadersAt
  exact Entails.of_eq (by ac_rfl)

theorem seq_cleanX {img : Obj.Image} {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → ImgCallInv img sm → Q sm → SepWP prog target sm P_mid post)
    (hinv : ImgCallInv img s := by assumption) :
    SepWP prog target s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  rcases h1.elim hm hL with ⟨sm, hst1, ⟨hpc1, hrun1, Pm, hmm, hent, hQ⟩ | hoom⟩
  · have hm_mid : sm.mem ⊨ P_mid ∗ R := Satisfies.mono (sepConj_mono_left hent) hmm
    rcases (h2 sm hpc1 hrun1 (ImgCallInv.of_steps hinv hst1) hQ).elim hm_mid (hst1.codeLoaded hL) with ⟨sf, hst2, hout⟩
    exact ⟨sf, hst1.trans hst2, hout⟩
  · exact ⟨sm, hst1, Or.inr hoom⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.DropsLocal1Layout
