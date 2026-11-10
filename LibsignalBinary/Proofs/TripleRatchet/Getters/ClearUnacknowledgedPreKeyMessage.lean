/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.OptImageHelper
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
import ProofLib.SepLogic.WPp

/-!
# Verification of `SessionState::clear_unacknowledged_pre_key_message` (`0x12404`, Block `35`)

Proves fixed-image (`clear_unacknowledged_pre_key_message_ok`, `clear_unacknowledged_pre_key_message_ok_x`)
and relocatable `[LibsignalPlacement]` (`clear_unacknowledged_pre_key_message_placed_ok`) contracts
for `<SessionState>::clear_unacknowledged_pre_key_message`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

/-- The part of `sessionStateAt` not touched by `clear_unacknowledged_pre_key_message`. -/
def sessionStateRest (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_split_upk (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        (match st.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
        G.chains.length = st.receiverChains.length ∧
        G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
        G.localIk.bytes.length = 33 ∧
        (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
      optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      sessionStateRest A ss G st := by
  unfold sessionStateAt sessionStateRest
  ac_rfl

theorem sessionStateAt_of_cleared_upk (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8)))
    (hloc : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hrem : match st.remoteIdentity with
            | none => G.remoteIk.bytes = []
            | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hchains : G.chains.length = st.receiverChains.length)
    (hreg : G.regIds.length = 8)
    (hlik_len : G.localIk.bytes.length = 33)
    (hrik_len : st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33) :
    (optTailVecAt A 48 (ss + 0xf8#64) none ∗
      optTailVecAt A 32 (ss + 0x128#64) none ∗
      sessionStateRest A ss G st) ⊢
      sessionStateAt A ss { G with pending := none, kyber := none }
        st.clearUnacknowledgedPreKeyMessage := by
  rw [sessionStateAt_split_upk]
  dsimp only [SessionState.clearUnacknowledgedPreKeyMessage, sessionStateRest]
  exact Entails.pure_right ⟨hloc, hrem, hchains, rfl, hreg, hlik_len, hrik_len⟩ (Entails.refl _)

private theorem slt_one_iff_eq_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]
  unfold BitVec.slt BitVec.toInt
  simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]
  omega

private theorem optTailVecAt_entails_deallocX (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        (if cap.slt 1#64 = true then emp
         else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
           A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
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

theorem optTailVecAt_none_of_cleared (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a ptr : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16)) ⊢
      optTailVecAt A size a none := by
  unfold optTailVecAt
  apply sepConj_mono_right
  have hsplit : size - 8 = 8 + (size - 16) := by omega
  rw [hsplit,
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
        (b' := a + 16#64) rfl (by bv_omega) (by omega)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) ptr)

theorem sessionStateAt_cleared_upk_intro (A : RustAlloc) (ss ptr1 ptr2 : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hloc : PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey)
    (hrem : match st.remoteIdentity with
            | none => G.remoteIk.bytes = []
            | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hchains : G.chains.length = st.receiverChains.length)
    (hreg : G.regIds.length = 8)
    (hlik_len : G.localIk.bytes.length = 33)
    (hrik_len : st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33) :
    ((ss + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗
      (ss + 256#64) ↦₆₄ ptr1 ∗
      memRegion (ss + 264#64) 32 ∗
      (ss + 296#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗
      (ss + 304#64) ↦₆₄ ptr2 ∗
      memRegion (ss + 312#64) 16 ∗
      sessionStateRest A ss G st) ⊢
      sessionStateAt A ss { G with pending := none, kyber := none }
        st.clearUnacknowledgedPreKeyMessage := by
  have h1 := optTailVecAt_none_of_cleared A 48 (by decide) (by decide) (ss + 0xf8#64) ptr1
  have h2 := optTailVecAt_none_of_cleared A 32 (by decide) (by decide) (ss + 0x128#64) ptr2
  have h3 := sessionStateAt_of_cleared_upk A ss G st hloc hrem hchains hreg hlik_len hrik_len
  have haddr1 : ss + 0xf8#64 + 8#64 = ss + 256#64 := by bv_omega
  have haddr2 : ss + 0xf8#64 + 16#64 = ss + 264#64 := by bv_omega
  have haddr3 : ss + 0x128#64 + 8#64 = ss + 304#64 := by bv_omega
  have haddr4 : ss + 0x128#64 + 16#64 = ss + 312#64 := by bv_omega
  rw [haddr1, haddr2] at h1
  rw [haddr3, haddr4] at h2
  have hassoc :
      ((ss + 248#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗
        (ss + 256#64) ↦₆₄ ptr1 ∗
        memRegion (ss + 264#64) 32 ∗
        (ss + 296#64) ↦₆₄ (bv% (2 ^ 64 - 1)) ∗
        (ss + 304#64) ↦₆₄ ptr2 ∗
        memRegion (ss + 312#64) 16 ∗
        sessionStateRest A ss G st) =
      (((ss + 0xf8#64) ↦₆₄ noneCap ∗
          (ss + 256#64) ↦₆₄ ptr1 ∗
          memRegion (ss + 264#64) (48 - 16)) ∗
        ((ss + 0x128#64) ↦₆₄ noneCap ∗
          (ss + 304#64) ↦₆₄ ptr2 ∗
          memRegion (ss + 312#64) (32 - 16)) ∗
        sessionStateRest A ss G st) := by
    dsimp only [noneCap]
    ac_rfl
  rw [hassoc]
  exact Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) h3

theorem clearUpk_strengthen_post {prog : Program} {target_pc : BitVec 64} {s : State}
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

def clearUpkSpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec ClearUpkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp (32 + hookStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A x.ss { x.G with pending := none, kyber := none }
        x.st.clearUnacknowledgedPreKeyMessage ∗
      A.pool ∗ stackAt s0.sp (32 + hookStack)

private theorem stackAt_clearUpk_opt {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (32 + hookStack) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 := by
  rw [Nat.add_comm 32 hookStack]
  exact stackAt_split_cells sp hookStack 4 hstack

@[local wp_norm] private theorem exists_two_pow_one : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[irreducible] private def optStop (pc : BitVec 64) : BitVec 64 := pc

private theorem SepWP.of_sepWP_stop {prog : Program}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog (optStop mid) s P
      (fun sm Pm => SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold optStop at h
  exact SepWP.cut h

private theorem SepWP.of_sepWP_optStop {prog : Program} {oimg : Option Obj.Image}
    {mid target_pc : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hinv : OptCallInv oimg s)
    (h : SepWP prog (optStop mid) s P
      (fun sm Pm => OptCallInv oimg sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold optStop at h
  exact SepWP.seq_optImage hinv h

private theorem SepWP.done_optStop {prog : Program} {mid : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running) (hpost : post s P) :
    SepWP prog (optStop mid) s P post := by
  unfold optStop
  exact SepWP.done hpc hrun hpost

/-- Unified parameterized proof of `SessionState::clear_unacknowledged_pre_key_message` (`0x12404`)
over `oimg : Option Obj.Image` and `hookStack : Nat`. -/
theorem clear_unacknowledged_pre_key_message_ok_of_dealloc_opt
    (oimg : Option Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hookStack : Nat)
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr clearUpkName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message"))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr clearUpkName)
      (specWithOptInv oimg (clearUpkSpecWithStack A hookStack)) := by
  unfold specWithOptInv clearUpkSpecWithStack
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message") (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message")) 88
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  subst h
  rw [sessionStateAt_split_upk, stackAt_clearUpk_opt (by omega) s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hloc, hrem, hchains, hpending, hreg, hlik_len, hrik_len⟩
  refine SepWP.weaken_pre
    (sepConj_mono
      (optTailVecAt_entails_deallocX A 48 (by decide) (by decide)
        (s0.readReg64 (Reg.gpr 0#5) + 0xf8#64) G.pending)
      (sepConj_mono_left
        (optTailVecAt_entails_deallocX A 32 (by decide) (by decide)
          (s0.readReg64 (Reg.gpr 0#5) + 0x128#64) G.kyber))) ?_
  wp_pull_exists
  rename_i cap2 ptr2 cap1 ptr1
  refine clearUpk_strengthen_post
    (sessionStateAt_cleared_upk_intro A (s0.readReg64 (Reg.gpr 0#5)) ptr1 ptr2 G st
      hloc hrem hchains hreg hlik_len hrik_len) ?_
  apply SepWP.of_sepWP_optStop hinv0
  wp_steps
  apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
  intro hinv_a
  by_cases h1 : cap1.slt 1#64 = true <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj] at hinv_a ⊢
  · apply SepWP.of_sepWP_optStop hinv_a
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    intro hinv_b
    by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj] at hinv_b ⊢
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      apply SepWP.of_sepWP_optStop hinv_b
      wp_steps
      apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
      intro hinv_c
      wp_call hdealloc (ptr2, cap2.toNat, 1)
      wp_steps
      wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos1, hlt1⟩
    have hlay1 : LayoutOk cap1.toNat 1 := ⟨hpos1, ⟨0, rfl⟩, by omega⟩
    apply SepWP.of_sepWP_optStop hinv_a
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    intro hinv_b
    apply SepWP.of_sepWP_optStop hinv_b
    wp_call hdealloc (ptr1, cap1.toNat, 1)
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    intro hinv_b'
    by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj] at hinv_b' ⊢
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      apply SepWP.of_sepWP_optStop hinv_b'
      wp_steps
      apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
      intro hinv_c
      wp_call hdealloc (ptr2, cap2.toNat, 1)
      rw [hsp_sf]
      wp_steps
      wp_done

theorem clear_unacknowledged_pre_key_message_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr clearUpkName)
      (clearUpkSpec A) :=
  subroutine_ok_of_optNone
    (clear_unacknowledged_pre_key_message_ok_of_dealloc_opt none b A ext allocHookStack (by decide)
      (dealloc_opt_of_base (name := clearUpkName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message")) hA (by fnoff_eq)))

theorem clear_unacknowledged_pre_key_message_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr clearUpkName)
      (clearUpkSpec A) :=
  clear_unacknowledged_pre_key_message_ok_ext b A _ (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

/-- `SessionState::clear_unacknowledged_pre_key_message` (`0x12404`) meets `clearUpkSpec A` on `tripleRatchetProgAt`. -/
theorem clear_unacknowledged_pre_key_message_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr clearUpkName)
      (clearUpkSpec A) :=
  subroutine_ok_kit_of_trTrap (clear_unacknowledged_pre_key_message_ok_trap b C A abs hA)

/-- `SessionState::clear_unacknowledged_pre_key_message` (`0x12404`) meets `(clearUpkSpecX A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem clear_unacknowledged_pre_key_message_ok_x (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr clearUpkName)
      ((clearUpkSpecX A).inImage img) :=
  clear_unacknowledged_pre_key_message_ok_of_dealloc_opt (some img) img.base A ext extHookStack (by decide)
    (dealloc_opt_of_x (name := clearUpkName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message")) hA (by fnoff_eq))

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `35`) -/

abbrev lsRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

theorem ls_hook_ok_rustDealloc [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {spec : Spec α} (hsat : HookSat H lsRustDeallocSym spec)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) spec := by
  have hmem : lsRustDeallocSym ∈ libsignalSessionExterns := by decide
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by simp [hk, hget]) hsat hi hunmut

/-- Block `35`: `SessionState::clear_unacknowledged_pre_key_message` meets `clearUpkSpecWithStack`
    under `[LibsignalPlacement]` given a `subroutine_ok` contract for `__rust_dealloc`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok_of_dealloc_opt [LibsignalPlacement]
    (oimg : Option Obj.Image) (A : RustAlloc)
    (H : String → Option (State → State)) (hookStack : Nat)
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_35).rebase (blkPl_35).base H)
      (lsρ lsRustDeallocSym)
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack))) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (specWithOptInv oimg (clearUpkSpecWithStack A hookStack)) := by
  unfold specWithOptInv clearUpkSpecWithStack
  wp_init x s0
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  subst h
  rw [sessionStateAt_split_upk, stackAt_clearUpk_opt (by omega) s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hloc, hrem, hchains, hpending, hreg, hlik_len, hrik_len⟩
  refine SepWP.weaken_pre
    (sepConj_mono
      (optTailVecAt_entails_deallocX A 48 (by decide) (by decide)
        (s0.readReg64 (Reg.gpr 0#5) + 0xf8#64) G.pending)
      (sepConj_mono_left
        (optTailVecAt_entails_deallocX A 32 (by decide) (by decide)
          (s0.readReg64 (Reg.gpr 0#5) + 0x128#64) G.kyber))) ?_
  wp_pull_exists
  rename_i cap2 ptr2 cap1 ptr1
  refine clearUpk_strengthen_post
    (sessionStateAt_cleared_upk_intro A (s0.readReg64 (Reg.gpr 0#5)) ptr1 ptr2 G st
      hloc hrem hchains hreg hlik_len hrik_len) ?_
  apply SepWP.of_sepWP_optStop hinv0
  wp_steps
  apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
  intro hinv_a
  by_cases h1 : cap1.slt 1#64 = true <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj] at hinv_a ⊢
  · apply SepWP.of_sepWP_optStop hinv_a
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    intro hinv_b
    by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj] at hinv_b ⊢
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      apply SepWP.of_sepWP_optStop hinv_b
      wp_steps
      apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
      intro hinv_c
      wp_call hdealloc (ptr2, cap2.toNat, 1)
      wp_steps
      wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos1, hlt1⟩
    have hlay1 : LayoutOk cap1.toNat 1 := ⟨hpos1, ⟨0, rfl⟩, by omega⟩
    apply SepWP.of_sepWP_optStop hinv_a
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    intro hinv_b
    apply SepWP.of_sepWP_optStop hinv_b
    wp_call hdealloc (ptr1, cap1.toNat, 1)
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    intro hinv_b'
    by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj] at hinv_b' ⊢
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      apply SepWP.of_sepWP_optStop hinv_b'
      wp_steps
      apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
      intro hinv_c
      wp_call hdealloc (ptr2, cap2.toNat, 1)
      rw [hsp_sf]
      wp_steps
      wp_done

/-- Block `35`: `SessionState::clear_unacknowledged_pre_key_message` meets `clearUpkSpecWithStack`
    under `[LibsignalPlacement]` given a `subroutine_ok` contract for `__rust_dealloc`
    (image-free). -/
theorem clear_unacknowledged_pre_key_message_placed_ok_of_dealloc [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) (hookStack : Nat)
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_35).rebase (blkPl_35).base H)
      (lsρ lsRustDeallocSym)
      (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpecWithStack A hookStack) := by
  unfold clearUpkSpecWithStack
  wp_init x s0
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  subst h
  rw [sessionStateAt_split_upk, stackAt_clearUpk_opt (by omega) s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hloc, hrem, hchains, hpending, hreg, hlik_len, hrik_len⟩
  refine SepWP.weaken_pre
    (sepConj_mono
      (optTailVecAt_entails_deallocX A 48 (by decide) (by decide)
        (s0.readReg64 (Reg.gpr 0#5) + 0xf8#64) G.pending)
      (sepConj_mono_left
        (optTailVecAt_entails_deallocX A 32 (by decide) (by decide)
          (s0.readReg64 (Reg.gpr 0#5) + 0x128#64) G.kyber))) ?_
  wp_pull_exists
  rename_i cap2 ptr2 cap1 ptr1
  refine clearUpk_strengthen_post
    (sessionStateAt_cleared_upk_intro A (s0.readReg64 (Reg.gpr 0#5)) ptr1 ptr2 G st
      hloc hrem hchains hreg hlik_len hrik_len) ?_
  apply SepWP.of_sepWP_stop
  wp_steps
  apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
  by_cases h1 : cap1.slt 1#64 = true <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply SepWP.of_sepWP_stop
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      apply SepWP.of_sepWP_stop
      wp_steps
      apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
      wp_call hdealloc (ptr2, cap2.toNat, 1)
      wp_steps
      wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_
    rintro ⟨hpos1, hlt1⟩
    have hlay1 : LayoutOk cap1.toNat 1 := ⟨hpos1, ⟨0, rfl⟩, by omega⟩
    apply SepWP.of_sepWP_stop
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    apply SepWP.of_sepWP_stop
    wp_call hdealloc (ptr1, cap1.toNat, 1)
    wp_steps
    apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
    by_cases h2 : cap2.slt 1#64 = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      apply SepWP.of_sepWP_stop
      wp_steps
      apply SepWP.done_optStop (by wp_norm_lhs) (by wp_norm_lhs)
      wp_call hdealloc (ptr2, cap2.toNat, 1)
      rw [hsp_sf]
      wp_steps
      wp_done

/-- Block `35`: `SessionState::clear_unacknowledged_pre_key_message` meets `clearUpkSpec A`
    under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpec A) :=
  clear_unacknowledged_pre_key_message_placed_ok_of_dealloc A H allocHookStack (by decide)
    (rustDeallocExternWithStack_of_rustDealloc
      (ls_hook_ok_rustDealloc hdealloc) (by decide) (by decide))

end CryptoVerification.LibsignalTripleRatchet.Getters
