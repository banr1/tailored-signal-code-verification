/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Stage P3 `SessionState` Folding, `try_decrypt_with_state` Bridge, and Version-Mismatch Funnel

Folds the 43-slot cloned `SessionState` at `sp + 0xa90` and `coroPtr + 0xf8`, bridges the version-4
`try_decrypt_with_state` call (`+0x1bac -> +0x1cd8`), and proves the `msgVer ≠ 4#32` error funnel.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Framing Helpers -/

theorem SepWPp.pure_left_focus {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P P_rest : SepProp} {Q Qp : State → SepProp → Prop} (hP : P = ⌜φ⌝ ∗ P_rest) (h : φ →
    SepWPp prog ret s P_rest Q Qp) : SepWPp prog ret s P Q Qp := by
  rw [hP]
  exact SepWPp.pure_elim h

theorem SepWPp.call_frame_inImage_nopanic {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop} (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hcall
    : subroutine_ok prog entry (spec.inImage img)) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc) (hspec : spec.pre x s = (⌜φ⌝ ∗
    T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned =
      true → CalleeSavedPreserved s sf → img.FrozenLoaded sf → sf.symtab = img.symtab → SepWPp prog
      ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_frame_frozen_nopanic hF hsym hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ) (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP
    hpan_false hexit_false hnext hoom_false
  dsimp only [Spec.inImage]
  rw [hspec, pure_sepConj_pure_assoc]

theorem SepWPp.call_inImage_frame {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop} (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (hcall
    : subroutine_ok prog entry (spec.inImage img)) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc) (hspec : spec.pre x s = (⌜φ⌝ ∗
    T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F)) (hnext : ∀ sf : State,
    sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → sf.spAligned = true →
    CalleeSavedPreserved s sf → img.FrozenLoaded sf → sf.symtab = img.symtab → SepWPp prog ret sf
    (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.call_inImage_frame hcall hF hsym hpc hrun hsp hlr (x := x) (T := T) (F := F)
    hspec hφ hP
    (fun sf code _ _ hpost => by
      rw [hexit_false] at hpost
      exact not_satisfies_false_sepConj hpost)
    hpanic
    (fun sf hpcm hrunm hspm hcsm hfz hsym' =>
      hnext sf hpcm hrunm hspm (by simpa [State.spAligned, hspm] using hsp) hcsm hfz hsym')
    (fun sf _ _ _hoom_post => by
      rw [hoom_false] at _hoom_post
      exact (not_satisfies_false_sepConj _hoom_post).elim)

theorem SepWPp.bind_oom_frame {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P₁ F : SepProp} {Q₁ Q₂ : State → SepProp → Prop} (h1 : SepWPp prog mid s P₁ Q₁
    (PanicOomProp s0)) (hP : P = P₁ ∗ F) (h2 : ∀ s1 P_f, s1.pc = mid → s1.status = .Running → Q₁ s1
    P_f → SepWPp prog ret s1 (P_f ∗ F) Q₂ (PanicOomProp s0)) :
    SepWPp prog ret s P Q₂ (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_f, hmm, hQ1⟩ |
      ⟨hpan, P_f, hmm, hQp⟩ | ⟨_, hoom⟩⟩ := h1 (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm P_f hpcm hrunm hQ1 R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_f ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h := hQp (F ∗ R') hmR'
      rw [← sepConj_assoc] at h
      exact allowPanic_frame id h⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. `SessionState` Folding Helpers (`sp + 0xa90` and `coroPtr + 0xf8`) -/

/-- Ghost layout for a freshly-initialized or cloned Bob `SessionState`
(`receiverChains = []`, `pqRatchetState = []`, `pending = none`, `kyber = none`). -/
def mkClonedGhost (locIdPtr remIdPtr rootKeyPtr aliceBasePtr : BitVec 64)
    (locIdBytes remIdBytes aliceBaseBytes : List (BitVec 8)) (sg : SenderChainGhost) (f248 f24c :
    BitVec 32) : SessionGhost :=
  { localIk := ⟨33#64, locIdPtr, locIdBytes⟩, remoteIk := ⟨33#64, remIdPtr, remIdBytes⟩,
    root := ⟨32#64, rootKeyPtr⟩, chainsCap := 0#64, chainsPtr := 8#64, chains := [], alice :=
    ⟨33#64, aliceBasePtr, aliceBaseBytes⟩, pq := ⟨0#64, 1#64⟩,
    sender := some sg, pending := none, kyber := none, regIds := unpack32 f248 ++ unpack32 f24c }

/-- Spatial layout of the 43 uninitialized stack slots + 8 bytes of padding at `sp + 0xa90..0xbe8`.
  -/
def spA90SlotsAt (sp : BitVec 64) (dv : DstVals) : SepProp :=
  ((sp + 0xa90#64) ↦₆₄ dv.w_ca0) ∗ ((sp + 0xa98#64) ↦₆₄ dv.w_ca8) ∗ ((sp + 0xaa0#64) ↦₆₄ dv.w_cb0) ∗
  ((sp + 0xaa8#64) ↦₆₄ dv.w_cb8) ∗ ((sp + 0xab0#64) ↦₆₄ dv.w_cc0) ∗ ((sp + 0xab8#64) ↦₆₄ dv.w_cc8) ∗
  ((sp + 0xac0#64) ↦₆₄ dv.w_cd0) ∗ ((sp + 0xac8#64) ↦₆₄ dv.w_cd8) ∗ ((sp + 0xad0#64) ↦₆₄ dv.w_ce0) ∗
  ((sp + 0xad8#64) ↦₆₄ dv.w_ce8) ∗ ((sp + 0xae0#64) ↦₆₄ dv.w_cf0) ∗ ((sp + 0xae8#64) ↦₆₄ dv.w_cf8) ∗
  ((sp + 0xaf0#64) ↦₆₄ dv.w_d00) ∗ ((sp + 0xaf8#64) ↦₆₄ dv.w_d08) ∗ ((sp + 0xb00#64) ↦₆₄ dv.w_d10) ∗
  ((sp + 0xb08#64) ↦₆₄ dv.w_d18) ∗ ((sp + 0xb10#64) ↦₆₄ dv.w_d20) ∗ ((sp + 0xb18#64) ↦₆₄ dv.w_d28) ∗
  ((sp + 0xb20#64) ↦₆₄ dv.w_d30) ∗
  ((sp + 0xb28#64) ↦₆₄ dv.q0.extractLsb' 0 64) ∗ ((sp + 0xb30#64) ↦₆₄ dv.q0.extractLsb' 64 64) ∗
  ((sp + 0xb38#64) ↦₆₄ dv.q1.extractLsb' 0 64) ∗ ((sp + 0xb40#64) ↦₆₄ dv.q1.extractLsb' 64 64) ∗
  ((sp + 0xb48#64) ↦₆₄ dv.q2.extractLsb' 0 64) ∗ ((sp + 0xb50#64) ↦₆₄ dv.q2.extractLsb' 64 64) ∗
  ((sp + 0xb58#64) ↦₆₄ dv.q3.extractLsb' 0 64) ∗ ((sp + 0xb60#64) ↦₆₄ dv.q3.extractLsb' 64 64) ∗
  ((sp + 0xb68#64) ↦₆₄ dv.q4.extractLsb' 0 64) ∗ ((sp + 0xb70#64) ↦₆₄ dv.q4.extractLsb' 64 64) ∗
  ((sp + 0xb78#64) ↦₆₄ dv.q5.extractLsb' 0 64) ∗ ((sp + 0xb80#64) ↦₆₄ dv.q5.extractLsb' 64 64) ∗
  ((sp + 0xb88#64) ↦₆₄ dv.w_d98) ∗ ((sp + 0xb90#64) ↦₆₄ dv.w_da0) ∗ ((sp + 0xb98#64) ↦₆₄ dv.w_da8) ∗
  ((sp + 0xba0#64) ↦₃₂ dv.w_db0) ∗ ((sp + 0xba4#64) ↦₃₂ dv.w_db4) ∗ ((sp + 0xba8#64) ↦₆₄ dv.w_db8) ∗
  ((sp + 0xbb0#64) ↦₃₂ dv.w_dc0) ∗ memRegion (sp + 0xbb4#64) 4 ∗
  ((sp + 0xbb8#64) ↦₆₄ dv.w_dc8) ∗ ((sp + 0xbc0#64) ↦₆₄ dv.w_dd0) ∗ ((sp + 0xbc8#64) ↦₆₄ dv.w_dd8) ∗
  ((sp + 0xbd0#64) ↦₃₂ dv.w_de0) ∗ memRegion (sp + 0xbd4#64) 4 ∗
  ((sp + 0xbd8#64) ↦₃₂ dv.w_de8) ∗ ((sp + 0xbdc#64) ↦₃₂ dv.w_dec) ∗
  ((sp + 0xbe0#64) ↦₃₂ dv.w_df0) ∗ ((sp + 0xbe4#64) ↦₃₂ dv.w_df4)

theorem memRegion_344_entails_spA90SlotsAt (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 344 ⊢ ∃∗ dv : DstVals, spA90SlotsAt sp dv := by
  have h := memRegion_344_entails_dstSlotsAt (sp - 0x210#64)
  have h0 : sp - 0x210#64 + 0xca0#64 = sp + 0xa90#64 := by bv_omega
  have hd : ∀ dv : DstVals, dstSlotsAt (sp - 0x210#64) dv = spA90SlotsAt sp dv := by
    intro dv
    unfold dstSlotsAt spA90SlotsAt chunks96_6QAt
    have hsub : ∀ k : BitVec 64, sp - 0x210#64 + k = sp + (k - 0x210#64) := by
      intro k; bv_omega
    simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, hsub, BitVec.reduceSub,
      BitVec.reduceAdd, sepConj_assoc]
  rw [h0] at h
  refine Entails.trans h ?_
  apply Entails.sepExists_elim; intro dv
  rw [hd dv]
  exact Entails.sepExists_right dv (Entails.refl _)

/-- Fold a Bob `SessionState` with `optSenderChainAt A (ss + 0x90#64) (some sg) (some sc)`
and `optTailVecAt` into `sessionStateAt A ss (mkClonedGhost ...) st`. -/
theorem bobSlots_entails_sessionStateAt {A : RustAlloc}
    (ss locIdPtr remIdPtr rootKeyPtr aliceBasePtr : BitVec 64) (locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes : List (BitVec 8)) (sg : SenderChainGhost) (sc : SenderChain) (prevCounter f248
    f24c : BitVec 32) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey) (hnew1 : locIdPtr
    ≠ 0#64) (hnew2 : remIdPtr ≠ 0#64) (hnew3 : rootKeyPtr ≠ 0#64) (hnew4 : aliceBasePtr ≠ 0#64)
    (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33) (halice_len :
    aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hroot_eq : rootKeyBytes = keyToBytes32
    st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain
    = some sc) (hpend : st.pendingPreKey = false) (hver : st.sessionVersion = 4#32) (hprev :
    st.previousCounter = prevCounter) : ((ss ↦₆₄ 33#64) ∗ ((ss + 0x08#64) ↦₆₄ locIdPtr) ∗ ((ss +
    0x10#64) ↦₆₄ 33#64) ∗ ((ss + 0x18#64) ↦₆₄ 33#64) ∗ ((ss + 0x20#64) ↦₆₄ remIdPtr) ∗ ((ss +
    0x28#64) ↦₆₄ 33#64) ∗ ((ss + 0x30#64) ↦₆₄ 32#64) ∗ ((ss + 0x38#64) ↦₆₄ rootKeyPtr) ∗ ((ss +
    0x40#64) ↦₆₄ 32#64) ∗ ((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗ ((ss + 0x58#64)
    ↦₆₄ 0#64) ∗ ((ss + 0x60#64) ↦₆₄ 33#64) ∗ ((ss + 0x68#64) ↦₆₄ aliceBasePtr) ∗ ((ss + 0x70#64) ↦₆₄
    33#64) ∗ ((ss + 0x78#64) ↦₆₄ 0#64) ∗ ((ss + 0x80#64) ↦₆₄ 1#64) ∗ ((ss + 0x88#64) ↦₆₄ 0#64) ∗
    optSenderChainAt A (ss + 0x90#64) (some sg) (some sc) ∗ optTailVecAt A 48 (ss + 0xf8#64) none ∗
    optTailVecAt A 32 (ss + 0x128#64) none ∗ ((ss + 0x148#64) ↦₃₂ 4#32) ∗ ((ss + 0x14c#64) ↦₃₂
    prevCounter) ∗ ((ss + 0x150#64) ↦₃₂ f248) ∗ ((ss + 0x154#64) ↦₃₂ f24c) ∗ A.live locIdPtr 33 1 ∗
    (locIdPtr ↦ₛ locIdBytes) ∗ A.live remIdPtr 33 1 ∗ (remIdPtr ↦ₛ remIdBytes) ∗ A.live rootKeyPtr
    32 1 ∗ (rootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live aliceBasePtr 33 1 ∗ (aliceBasePtr ↦ₛ
    aliceBaseBytes)) ⊢ sessionStateAt A ss
      (mkClonedGhost locIdPtr remIdPtr rootKeyPtr aliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st := by
  have hloc :
      (ss ↦₆₄ 33#64) ∗ ((ss + 0x08#64) ↦₆₄ locIdPtr) ∗ ((ss + 0x10#64) ↦₆₄ 33#64) ∗ A.live locIdPtr
      33 1 ∗ (locIdPtr ↦ₛ locIdBytes) ⊢ vecGhostAt A ⟨33#64, locIdPtr, locIdBytes⟩ ss := by
    unfold vecGhostAt vecU8At vecHeader
    have hcap0 : (33#64 : BitVec 64) ≠ 0 := by decide
    simp only [hloc_len, hcap0, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.sub_self, memRegion_zero, sepConj_emp]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, hnew1⟩ (Entails.refl _)))
  have hrem :
      ((ss + 0x18#64) ↦₆₄ 33#64) ∗ ((ss + 0x20#64) ↦₆₄ remIdPtr) ∗ ((ss + 0x28#64) ↦₆₄ 33#64) ∗
      A.live remIdPtr 33 1 ∗ (remIdPtr ↦ₛ remIdBytes) ⊢ vecGhostAt A ⟨33#64, remIdPtr, remIdBytes⟩
      (ss + 0x18#64) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 : ss + 0x18#64 + 8#64 = ss + 0x20#64 := by bv_omega
    have h2 : ss + 0x18#64 + 16#64 = ss + 0x28#64 := by bv_omega
    have hcap0 : (33#64 : BitVec 64) ≠ 0 := by decide
    simp only [h1, h2, hrem_len, hcap0, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.sub_self, memRegion_zero, sepConj_emp]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, hnew2⟩ (Entails.refl _)))
  have hroot :
      ((ss + 0x30#64) ↦₆₄ 32#64) ∗ ((ss + 0x38#64) ↦₆₄ rootKeyPtr) ∗ ((ss + 0x40#64) ↦₆₄ 32#64) ∗
      A.live rootKeyPtr 32 1 ∗ (rootKeyPtr ↦ₛ rootKeyBytes) ⊢ vecU8At A (ss + 0x30#64) 32#64
      rootKeyPtr (keyToBytes32 st.rootKey) := by
    unfold vecU8At vecHeader
    have h1 : ss + 0x30#64 + 8#64 = ss + 0x38#64 := by bv_omega
    have h2 : ss + 0x30#64 + 16#64 = ss + 0x40#64 := by bv_omega
    have h3 : (keyToBytes32 st.rootKey).length = 32 := length_keyToBytes32 st.rootKey
    have hcap0 : (32#64 : BitVec 64) ≠ 0 := by decide
    rw [hroot_eq]
    simp only [h1, h2, h3, hcap0, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.sub_self, memRegion_zero, sepConj_emp]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, hnew3⟩ (Entails.refl _)))
  have hchains :
      ((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗ ((ss + 0x58#64) ↦₆₄ 0#64) ⊢ vecAt A
      104 8 (chainAt A) (ss + 0x48#64) 0#64 8#64
        (([] : List ChainGhost).zip st.receiverChains) := by
    unfold vecAt vecHeader vecBuf
    have h1 : ss + 0x48#64 + 8#64 = ss + 0x50#64 := by bv_omega
    have h2 : ss + 0x48#64 + 16#64 = ss + 0x58#64 := by bv_omega
    rw [hrc]
    simp only [h1, h2, List.zip_nil_left, List.length_nil, ↓reduceIte]
    rw [← sepConj_emp (((ss + 0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗ ((ss + 0x58#64) ↦₆₄
      0#64))]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)))
  have halice :
      ((ss + 0x60#64) ↦₆₄ 33#64) ∗ ((ss + 0x68#64) ↦₆₄ aliceBasePtr) ∗ ((ss + 0x70#64) ↦₆₄ 33#64) ∗
      A.live aliceBasePtr 33 1 ∗ (aliceBasePtr ↦ₛ aliceBaseBytes) ⊢ vecGhostAt A ⟨33#64,
      aliceBasePtr, aliceBaseBytes⟩ (ss + 0x60#64) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 : ss + 0x60#64 + 8#64 = ss + 0x68#64 := by bv_omega
    have h2 : ss + 0x60#64 + 16#64 = ss + 0x70#64 := by bv_omega
    have hcap0 : (33#64 : BitVec 64) ≠ 0 := by decide
    simp only [h1, h2, halice_len, hcap0, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.sub_self, memRegion_zero, sepConj_emp]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, hnew4⟩ (Entails.refl _)))
  have hpq_hdr :
      ((ss + 0x78#64) ↦₆₄ 0#64) ∗ ((ss + 0x80#64) ↦₆₄ 1#64) ∗ ((ss + 0x88#64) ↦₆₄ 0#64) ⊢ vecU8At A
      (ss + 0x78#64) 0#64 1#64 st.pqRatchetState := by
    unfold vecU8At vecHeader
    have h1 : ss + 0x78#64 + 8#64 = ss + 0x80#64 := by bv_omega
    have h2 : ss + 0x78#64 + 16#64 = ss + 0x88#64 := by bv_omega
    rw [hpq]
    simp only [h1, h2, List.length_nil, ↓reduceIte]
    rw [← sepConj_emp (((ss + 0x78#64) ↦₆₄ 0#64) ∗ ((ss + 0x80#64) ↦₆₄ 1#64) ∗ ((ss + 0x88#64) ↦₆₄
      0#64))]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)))
  have htail :
      ((ss + 0x148#64) ↦₃₂ 4#32) ∗ ((ss + 0x14c#64) ↦₃₂ prevCounter) ∗ ((ss + 0x150#64) ↦₃₂ f248) ∗
      ((ss + 0x154#64) ↦₃₂ f24c) = ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂
      st.previousCounter) ∗ ((ss + 0x150#64) ↦ₛ (unpack32 f248 ++ unpack32 f24c)) := by
    have h154 : ss + 0x150#64 + 4#64 = ss + 0x154#64 := by bv_omega
    rw [hver, hprev, pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes, ←
      pointsTo32_eq_pointsToBytes, h154]
  unfold sessionStateAt mkClonedGhost
  dsimp only
  have hpure :
      PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey ∧ (match st.remoteIdentity
      with
       | none => remIdBytes = []
       | some ik => PublicKey.deserialize remIdBytes = .ok ik.publicKey) ∧ ([] : List
         ChainGhost).length = st.receiverChains.length ∧ (none : Option TailVecGhost).isSome =
         st.pendingPreKey ∧ (unpack32 f248 ++ unpack32 f24c).length = 8 ∧ locIdBytes.length = 33 ∧
         (st.remoteIdentity.isSome → remIdBytes.length = 33) := by
    refine ⟨hloc_deser, ?_, by simp [hrc], by simp [hpend], by simp, hloc_len, fun _ => hrem_len⟩
    rw [hrem_eq]; exact hrem_deser
  apply Entails.pure_right hpure
  rw [hsc, ← htail]
  refine Entails.trans
    (Q := ((ss ↦₆₄ 33#64) ∗ ((ss + 0x08#64) ↦₆₄ locIdPtr) ∗ ((ss + 0x10#64) ↦₆₄ 33#64) ∗
            A.live locIdPtr 33 1 ∗ (locIdPtr ↦ₛ locIdBytes)) ∗ (((ss + 0x18#64) ↦₆₄ 33#64) ∗ ((ss +
            0x20#64) ↦₆₄ remIdPtr) ∗ ((ss + 0x28#64) ↦₆₄ 33#64) ∗ A.live remIdPtr 33 1 ∗ (remIdPtr
            ↦ₛ remIdBytes)) ∗ (((ss + 0x30#64) ↦₆₄ 32#64) ∗ ((ss + 0x38#64) ↦₆₄ rootKeyPtr) ∗ ((ss +
            0x40#64) ↦₆₄ 32#64) ∗ A.live rootKeyPtr 32 1 ∗ (rootKeyPtr ↦ₛ rootKeyBytes)) ∗ (((ss +
            0x48#64) ↦₆₄ 0#64) ∗ ((ss + 0x50#64) ↦₆₄ 8#64) ∗ ((ss + 0x58#64) ↦₆₄ 0#64)) ∗ (((ss +
            0x60#64) ↦₆₄ 33#64) ∗ ((ss + 0x68#64) ↦₆₄ aliceBasePtr) ∗ ((ss + 0x70#64) ↦₆₄ 33#64) ∗
            A.live aliceBasePtr 33 1 ∗ (aliceBasePtr ↦ₛ aliceBaseBytes)) ∗ (((ss + 0x78#64) ↦₆₄
            0#64) ∗ ((ss + 0x80#64) ↦₆₄ 1#64) ∗ ((ss + 0x88#64) ↦₆₄ 0#64)) ∗ optSenderChainAt A (ss
            + 0x90#64) (some sg) (some sc) ∗ optTailVecAt A 48 (ss + 0xf8#64) none ∗ optTailVecAt A
            32 (ss + 0x128#64) none ∗ ((ss + 0x148#64) ↦₃₂ 4#32) ∗ ((ss + 0x14c#64) ↦₃₂ prevCounter)
            ∗ ((ss + 0x150#64) ↦₃₂ f248) ∗ ((ss + 0x154#64) ↦₃₂ f24c))
    (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono hloc
    (sepConj_mono hrem (sepConj_mono hroot (sepConj_mono hchains (sepConj_mono halice
    (sepConj_mono_left hpq_hdr)))))

/-- Fold the 43 cloned stack slots at `sp + 0xa90..0xbe8` (written by `p3_seg6_v4_wp` or
`p3_seg6_ver_ne_wp`), the two 4-byte tail padding regions at `sp + 0xbb4` and `sp + 0xbd4`,
and the cloned heap buffers into `sessionStateAt A (sp + 0xa90#64) G₁ st`. -/
theorem clonedSlots_sp_a90_entails_sessionStateAt {A : RustAlloc}
    (sp newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr c0 : BitVec 64) (sq0 sq1 sq2 sq3 sq4
    sq5 : BitVec 128) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List (BitVec 8)) (sg' :
    SenderChainGhost) (sc : SenderChain) (prevCounter f248 f24c : BitVec 32) (u_b90 u_b98 u_ba8
    u_bc0 u_bc8 : BitVec 64) (u_ba0 u_ba4 u_bb0 u_bd0 : BitVec 32) (st : SessionState (List (BitVec
    8))) (remIk : IdentityKey) (hnew1 : newLocIdPtr ≠ 0#64) (hnew2 : newRemIdPtr ≠ 0#64) (hnew3 :
    newRootKeyPtr ≠ 0#64) (hnew4 : newAliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33)
    (hrem_len : remIdBytes.length = 33) (halice_len : aliceBaseBytes.length = 33) (hloc_deser :
    PublicKey.deserialize locIdBytes = .ok st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity
    = some remIk) (hrem_deser : PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hroot_eq :
    rootKeyBytes = keyToBytes32 st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState
    = []) (hsc : st.senderChain = some sc) (hpend : st.pendingPreKey = false) (hver :
    st.sessionVersion = 4#32) (hprev : st.previousCounter = prevCounter) (hsc_inl :
    OptSenderChainInline (some sg') (some sc) (bytes104OfW6Q c0 sq0 sq1 sq2 sq3 sq4 sq5)) : (((sp +
    0xa90#64) ↦₆₄ 33#64) ∗ ((sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗ ((sp + 0xaa0#64) ↦₆₄ 33#64) ∗ ((sp +
    0xaa8#64) ↦₆₄ 33#64) ∗ ((sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((sp + 0xab8#64) ↦₆₄ 33#64) ∗ ((sp +
    0xac0#64) ↦₆₄ 32#64) ∗ ((sp + 0xac8#64) ↦₆₄ newRootKeyPtr) ∗ ((sp + 0xad0#64) ↦₆₄ 32#64) ∗ ((sp
    + 0xad8#64) ↦₆₄ 0#64) ∗ ((sp + 0xae0#64) ↦₆₄ 8#64) ∗ ((sp + 0xae8#64) ↦₆₄ 0#64) ∗ ((sp +
    0xaf0#64) ↦₆₄ 33#64) ∗ ((sp + 0xaf8#64) ↦₆₄ newAliceBasePtr) ∗ ((sp + 0xb00#64) ↦₆₄ 33#64) ∗
    ((sp + 0xb08#64) ↦₆₄ 0#64) ∗ ((sp + 0xb10#64) ↦₆₄ 1#64) ∗ ((sp + 0xb18#64) ↦₆₄ 0#64) ∗ ((sp +
    0xb20#64) ↦₆₄ c0) ∗ ((sp + 0xb28#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((sp + 0xb30#64) ↦₆₄
    sq0.extractLsb' 64 64) ∗ ((sp + 0xb38#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((sp + 0xb40#64) ↦₆₄
    sq1.extractLsb' 64 64) ∗ ((sp + 0xb48#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((sp + 0xb50#64) ↦₆₄
    sq2.extractLsb' 64 64) ∗ ((sp + 0xb58#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((sp + 0xb60#64) ↦₆₄
    sq3.extractLsb' 64 64) ∗ ((sp + 0xb68#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((sp + 0xb70#64) ↦₆₄
    sq4.extractLsb' 64 64) ∗ ((sp + 0xb78#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((sp + 0xb80#64) ↦₆₄
    sq5.extractLsb' 64 64) ∗ ((sp + 0xb88#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0xb90#64) ↦₆₄
    u_b90) ∗ ((sp + 0xb98#64) ↦₆₄ u_b98) ∗ ((sp + 0xba0#64) ↦₃₂ u_ba0) ∗ ((sp + 0xba4#64) ↦₃₂ u_ba4)
    ∗ ((sp + 0xba8#64) ↦₆₄ u_ba8) ∗ ((sp + 0xbb0#64) ↦₃₂ u_bb0) ∗ memRegion (sp + 0xbb4#64) 4 ∗ ((sp
    + 0xbb8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0xbc0#64) ↦₆₄ u_bc0) ∗ ((sp + 0xbc8#64) ↦₆₄
    u_bc8) ∗ ((sp + 0xbd0#64) ↦₃₂ u_bd0) ∗ memRegion (sp + 0xbd4#64) 4 ∗ ((sp + 0xbd8#64) ↦₃₂ 4#32)
    ∗ ((sp + 0xbdc#64) ↦₃₂ prevCounter) ∗ ((sp + 0xbe0#64) ↦₃₂ f248) ∗ ((sp + 0xbe4#64) ↦₃₂ f24c) ∗
    A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗ (newRemIdPtr
    ↦ₛ remIdBytes) ∗ A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ rootKeyBytes) ∗ A.live
    newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ aliceBaseBytes) ∗ optSenderChainHeap A (some sg')
    (some sc)) ⊢ sessionStateAt A (sp + 0xa90#64)
      (mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c) st := by
  have hsc_reasm :
      (((sp + 0xb20#64) ↦₆₄ c0) ∗ ((sp + 0xb28#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((sp + 0xb30#64) ↦₆₄
       sq0.extractLsb' 64 64) ∗ ((sp + 0xb38#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((sp + 0xb40#64) ↦₆₄
       sq1.extractLsb' 64 64) ∗ ((sp + 0xb48#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((sp + 0xb50#64) ↦₆₄
       sq2.extractLsb' 64 64) ∗ ((sp + 0xb58#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((sp + 0xb60#64) ↦₆₄
       sq3.extractLsb' 64 64) ∗ ((sp + 0xb68#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((sp + 0xb70#64) ↦₆₄
       sq4.extractLsb' 64 64) ∗ ((sp + 0xb78#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((sp + 0xb80#64) ↦₆₄
       sq5.extractLsb' 64 64) ∗ optSenderChainHeap A (some sg') (some sc)) ⊢ optSenderChainAt A (sp
       + 0xb20#64) (some sg') (some sc) := by
    have h := optSenderChainAt_of_chunks104W6Q A (sp + 0xb20#64) (some sg') (some sc) hsc_inl
    rw [chunks104W6QAt_sp_0xb20_eq] at h
    exact Entails.trans (Entails.of_eq (by ac_rfl)) h
  have hpend_reasm :
      (((sp + 0xb88#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0xb90#64) ↦₆₄ u_b90) ∗ ((sp + 0xb98#64)
       ↦₆₄ u_b98) ∗ ((sp + 0xba0#64) ↦₃₂ u_ba0) ∗ ((sp + 0xba4#64) ↦₃₂ u_ba4) ∗ ((sp + 0xba8#64) ↦₆₄
       u_ba8) ∗ ((sp + 0xbb0#64) ↦₃₂ u_bb0) ∗ memRegion (sp + 0xbb4#64) 4) ⊢ optTailVecAt A 48 (sp +
       0xb88#64) none := by
    unfold optTailVecAt noneCap
    have h8 : sp + 0xb88#64 + 8#64 = sp + 0xb90#64 := by bv_omega
    rw [h8]
    apply sepConj_mono_right
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _
      _) (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono
      (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _))))))) ?_
    rw [← ProofLib.memRegion_split' (b := sp + 0xbb0#64) (n := 4) (k := 4) (b' := sp + 0xbb4#64) rfl
      (by bv_omega) (by decide) ,
        ← ProofLib.memRegion_split' (b := sp + 0xba8#64) (n := 8) (k := 8) (b' := sp + 0xbb0#64) rfl
        (by bv_omega) (by decide) ,
        ← ProofLib.memRegion_split' (b := sp + 0xba4#64) (n := 4) (k := 16) (b' := sp + 0xba8#64)
        rfl (by bv_omega) (by decide) ,
        ← ProofLib.memRegion_split' (b := sp + 0xba0#64) (n := 4) (k := 20) (b' := sp + 0xba4#64)
        rfl (by bv_omega) (by decide) ,
        ← ProofLib.memRegion_split' (b := sp + 0xb98#64) (n := 8) (k := 24) (b' := sp + 0xba0#64)
        rfl (by bv_omega) (by decide) ,
        ← ProofLib.memRegion_split' (b := sp + 0xb90#64) (n := 8) (k := 32) (b' := sp + 0xb98#64)
        rfl (by bv_omega) (by decide) ]
    exact Entails.refl _
  have hkyb_reasm :
      (((sp + 0xbb8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0xbc0#64) ↦₆₄ u_bc0) ∗ ((sp + 0xbc8#64)
       ↦₆₄ u_bc8) ∗ ((sp + 0xbd0#64) ↦₃₂ u_bd0) ∗ memRegion (sp + 0xbd4#64) 4) ⊢ optTailVecAt A 32
       (sp + 0xbb8#64) none := by
    unfold optTailVecAt noneCap
    have h8 : sp + 0xbb8#64 + 8#64 = sp + 0xbc0#64 := by bv_omega
    rw [h8]
    apply sepConj_mono_right
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _
      _) (sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)))) ?_
    rw [← ProofLib.memRegion_split' (b := sp + 0xbd0#64) (n := 4) (k := 4) (b' := sp + 0xbd4#64) rfl
      (by bv_omega) (by decide) ,
        ← ProofLib.memRegion_split' (b := sp + 0xbc8#64) (n := 8) (k := 8) (b' := sp + 0xbd0#64) rfl
        (by bv_omega) (by decide) ,
        ← ProofLib.memRegion_split' (b := sp + 0xbc0#64) (n := 8) (k := 16) (b' := sp + 0xbc8#64)
        rfl (by bv_omega) (by decide) ]
    exact Entails.refl _
  have hbob := bobSlots_entails_sessionStateAt (A := A) (sp + 0xa90#64)
    newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes sg' sc prevCounter f248 f24c st remIk hnew1 hnew2 hnew3 hnew4 hloc_len hrem_len
    halice_len hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc hpend hver hprev
  have hsub : ∀ k : BitVec 64, sp + 0xa90#64 + k = sp + (0xa90#64 + k) := fun k => by bv_omega
  simp only [hsub, BitVec.reduceAdd] at hbob
  refine Entails.trans ?_ hbob
  refine Entails.trans
    (Q := (((sp + 0xb20#64) ↦₆₄ c0) ∗
            ((sp + 0xb28#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((sp + 0xb30#64) ↦₆₄ sq0.extractLsb' 64 64)
            ∗ ((sp + 0xb38#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((sp + 0xb40#64) ↦₆₄ sq1.extractLsb' 64
            64) ∗ ((sp + 0xb48#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((sp + 0xb50#64) ↦₆₄ sq2.extractLsb'
            64 64) ∗ ((sp + 0xb58#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((sp + 0xb60#64) ↦₆₄
            sq3.extractLsb' 64 64) ∗ ((sp + 0xb68#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((sp + 0xb70#64)
            ↦₆₄ sq4.extractLsb' 64 64) ∗ ((sp + 0xb78#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((sp +
            0xb80#64) ↦₆₄ sq5.extractLsb' 64 64) ∗ optSenderChainHeap A (some sg') (some sc)) ∗
            (((sp + 0xb88#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0xb90#64) ↦₆₄ u_b90) ∗ ((sp +
            0xb98#64) ↦₆₄ u_b98) ∗ ((sp + 0xba0#64) ↦₃₂ u_ba0) ∗ ((sp + 0xba4#64) ↦₃₂ u_ba4) ∗ ((sp
            + 0xba8#64) ↦₆₄ u_ba8) ∗ ((sp + 0xbb0#64) ↦₃₂ u_bb0) ∗ memRegion (sp + 0xbb4#64) 4) ∗
            (((sp + 0xbb8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0xbc0#64) ↦₆₄ u_bc0) ∗ ((sp +
            0xbc8#64) ↦₆₄ u_bc8) ∗ ((sp + 0xbd0#64) ↦₃₂ u_bd0) ∗ memRegion (sp + 0xbd4#64) 4) ∗
            (((sp + 0xa90#64) ↦₆₄ 33#64) ∗ ((sp + 0xa98#64) ↦₆₄ newLocIdPtr) ∗ ((sp + 0xaa0#64) ↦₆₄
            33#64) ∗ ((sp + 0xaa8#64) ↦₆₄ 33#64) ∗ ((sp + 0xab0#64) ↦₆₄ newRemIdPtr) ∗ ((sp +
            0xab8#64) ↦₆₄ 33#64) ∗ ((sp + 0xac0#64) ↦₆₄ 32#64) ∗ ((sp + 0xac8#64) ↦₆₄ newRootKeyPtr)
            ∗ ((sp + 0xad0#64) ↦₆₄ 32#64) ∗ ((sp + 0xad8#64) ↦₆₄ 0#64) ∗ ((sp + 0xae0#64) ↦₆₄ 8#64)
            ∗ ((sp + 0xae8#64) ↦₆₄ 0#64) ∗ ((sp + 0xaf0#64) ↦₆₄ 33#64) ∗ ((sp + 0xaf8#64) ↦₆₄
            newAliceBasePtr) ∗ ((sp + 0xb00#64) ↦₆₄ 33#64) ∗ ((sp + 0xb08#64) ↦₆₄ 0#64) ∗ ((sp +
            0xb10#64) ↦₆₄ 1#64) ∗ ((sp + 0xb18#64) ↦₆₄ 0#64) ∗ ((sp + 0xbd8#64) ↦₃₂ 4#32) ∗ ((sp +
            0xbdc#64) ↦₃₂ prevCounter) ∗ ((sp + 0xbe0#64) ↦₃₂ f248) ∗ ((sp + 0xbe4#64) ↦₃₂ f24c) ∗
            A.live newLocIdPtr 33 1 ∗ (newLocIdPtr ↦ₛ locIdBytes) ∗ A.live newRemIdPtr 33 1 ∗
            (newRemIdPtr ↦ₛ remIdBytes) ∗ A.live newRootKeyPtr 32 1 ∗ (newRootKeyPtr ↦ₛ
            rootKeyBytes) ∗ A.live newAliceBasePtr 33 1 ∗ (newAliceBasePtr ↦ₛ aliceBaseBytes)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hsc_reasm (sepConj_mono hpend_reasm (sepConj_mono_left hkyb_reasm))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Fold the freshly-initialized Bob `SessionState` at `coroPtr + 0xf8..0x250` into
`sessionStateAt A (coroPtr + 0xf8#64) (mkClonedGhost ...) st`. -/
theorem bobSlots_coro_0xf8_entails_sessionStateAt {A : RustAlloc}
    (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr : BitVec 64) (locIdBytes remIdBytes
    rootKeyBytes aliceBaseBytes : List (BitVec 8)) (sg : SenderChainGhost) (sc : SenderChain)
    (prevCounter f248 f24c : BitVec 32) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey)
    (hnew1 : locIdPtr ≠ 0#64) (hnew2 : remIdPtr ≠ 0#64) (hnew3 : rootKeyPtr ≠ 0#64) (hnew4 :
    aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (halice_len : aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hroot_eq : rootKeyBytes = keyToBytes32
    st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain
    = some sc) (hpend : st.pendingPreKey = false) (hver : st.sessionVersion = 4#32) (hprev :
    st.previousCounter = prevCounter) : (((coroPtr + 0xf8#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x100#64) ↦₆₄
    locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x110#64) ↦₆₄ 33#64) ∗ ((coroPtr +
    0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x128#64) ↦₆₄ 32#64) ∗
    ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗ ((coroPtr + 0x140#64)
    ↦₆₄ 0#64) ∗ ((coroPtr + 0x148#64) ↦₆₄ 8#64) ∗ ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr +
    0x158#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗ ((coroPtr + 0x168#64) ↦₆₄
    33#64) ∗ ((coroPtr + 0x170#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x178#64) ↦₆₄ 1#64) ∗ ((coroPtr +
    0x180#64) ↦₆₄ 0#64) ∗ optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗ optTailVecAt
    A 48 (coroPtr + 0x1f0#64) none ∗ optTailVecAt A 32 (coroPtr + 0x220#64) none ∗ ((coroPtr +
    0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗
    ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗ A.live locIdPtr 33 1 ∗ (locIdPtr ↦ₛ locIdBytes) ∗ A.live
    remIdPtr 33 1 ∗ (remIdPtr ↦ₛ remIdBytes) ∗ A.live rootKeyPtr 32 1 ∗ (rootKeyPtr ↦ₛ rootKeyBytes)
    ∗ A.live aliceBasePtr 33 1 ∗ (aliceBasePtr ↦ₛ aliceBaseBytes)) ⊢ sessionStateAt A (coroPtr +
    0xf8#64)
      (mkClonedGhost locIdPtr remIdPtr rootKeyPtr aliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st := by
  have hbob := bobSlots_entails_sessionStateAt (A := A) (coroPtr + 0xf8#64)
    locIdPtr remIdPtr rootKeyPtr aliceBasePtr locIdBytes remIdBytes rootKeyBytes aliceBaseBytes sg
    sc prevCounter f248 f24c st remIk hnew1 hnew2 hnew3 hnew4 hloc_len hrem_len halice_len
    hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc hpend hver hprev
  have hsub : ∀ k : BitVec 64, coroPtr + 0xf8#64 + k = coroPtr + (0xf8#64 + k) := fun k => by
    bv_omega
  simp only [hsub, BitVec.reduceAdd] at hbob
  exact hbob

/-! ## 3. Version-4 `try_decrypt_with_state` Bridge (`+0x1bac -> +0x1cd8`) -/

theorem stackAt_root_eq_chainClone (sp : BitVec 64) :
    stackAt sp rootStack = memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)
      ∗ stackAt sp chainCloneStack :=
  stackAt_split_bottom sp chainCloneStack (rootStack - chainCloneStack) (by decide)

def tryDecryptRawSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost where
  pre x s := ⌜x.st.pqRatchetState = [] ∧ s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧
      s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧ (s.readReg64
      .x5).setWidth 8 = msgTypeByte x.msgType ∧ x.st.remoteIdentity ≠ some x.st.localIdentity ∧
      SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc
      x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest
      ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool
  post x s0 sf := ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗ (∃∗ G' :
    SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidParse).1.toBool G'⌝ ∗ sessionStateAt A x.ss G'
    (x.model C S uuidParse).2) ∗ vecResultAt A x.ret (x.model C S uuidParse).1 ∗ protocolAddressAt A
    x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗ logOff img ∗
    stackAt s0.sp rootStack ∗ A.pool
  onPanic x s0 sf := ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.recvPanics x.st.pqRatchetState
      x.msg.pqRatchet ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev pqxdhTryDecryptModel (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (rem loc : AddrGhost) (msg : SignalMessage) (rest : List (BitVec 8)) (st : SessionState (List
    (BitVec 8))) : Except SignalProtocolError (List (BitVec 8)) × SessionState (List (BitVec 8)) :=
  Mut.exec (SessionState.tryDecryptWithState C S.spqr
    (serializeAddresses (serviceIdParse parse) rem loc) msg .preKey (coinsOf rest)) st

def mkClonedTryDecryptGhost (sp : BitVec 64)
    (newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr : BitVec 64) (locIdBytes remIdBytes
    aliceBaseBytes : List (BitVec 8)) (sg' : SenderChainGhost) (f248 f24c : BitVec 32) (st :
    SessionState (List (BitVec 8))) (remAddrPtr : BitVec 64) (rem : AddrGhost) (locAddrPtr : BitVec
    64) (loc : AddrGhost) (whisperMsgPtr : BitVec 64) (msgG : SignalMessageGhost) (msg :
    SignalMessage) (cur : BitVec 64) (rest : List (BitVec 8)) : TryDecryptGhost :=
  { ret := sp + 0x270#64, ss := sp + 0xa90#64,
    G := mkClonedGhost newLocIdPtr newRemIdPtr newRootKeyPtr newAliceBasePtr
      locIdBytes remIdBytes aliceBaseBytes sg' f248 f24c, st := st, remA := remAddrPtr, rem := rem,
      locA := locAddrPtr, loc := loc,
    msgA := whisperMsgPtr, msgG := msgG, msg := msg, msgType := .preKey, cur := cur, rest := rest }

def TryDecryptPanicProp (C : Crypto) (S : SpqrModel) (_parse : UuidParser)
    (rem loc : AddrGhost) (st : SessionState (List (BitVec 8))) (msg : SignalMessage) (rest : List
    (BitVec 8)) (s0 sf : State) (P : SepProp) : Prop := ∀ R, (sf.mem ⊨ P ∗ R) → sf.mem ⊨
      (⌜((pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 = .error .panic ∨
         S.recvPanics st.pqRatchetState msg.pqRatchet ∨ allocFailedIn s0 sf) ∧ s0.trace <+:
         sf.trace⌝ ∗ anyHeap) ∗ R

theorem panicOomProp_imp_tryDecryptPanicProp {C : Crypto} {S : SpqrModel} {_parse : UuidParser}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))} {msg : SignalMessage} {rest : List
    (BitVec 8)} {s0 sf : State} {P : SepProp} (h : PanicOomProp s0 sf P) : TryDecryptPanicProp C S
    _parse rem loc st msg rest s0 sf P := by
  intro R hm
  have h1 := h R hm
  refine Satisfies.mono (sepConj_mono_left ?_) h1
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  exact Entails.pure_right ⟨Or.inr (Or.inr halloc), hpref⟩ (Entails.refl _)

theorem SepWPp.mono_panic {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp₁ Qp₂ : State → SepProp → Prop} (hQp : ∀ sf P_f, Qp₁ sf P_f → Qp₂ sf P_f) (h : SepWPp prog
    ret s P Q Qp₁) : SepWPp prog ret s P Q Qp₂ := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨hpan, P_f, hmf, hQ1⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, hQp sf P_f hQ1⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem tryDecryptPanicProp_imp_panicOomProp {C : Crypto} {S : SpqrModel} {_parse : UuidParser}
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))} {msg : SignalMessage} {rest : List
    (BitVec 8)} {s0 sf : State} {P : SepProp} (hnpan1 : (pqxdhTryDecryptModel C S uuidTryParse rem
    loc msg rest st).1 ≠ .error .panic) (hnpan2 : ¬ S.recvPanics st.pqRatchetState msg.pqRatchet) (h
    : TryDecryptPanicProp C S _parse rem loc st msg rest s0 sf P) : PanicOomProp s0 sf P := by
  intro R hm
  have h1 := h R hm
  refine Satisfies.mono (sepConj_mono_left ?_) h1
  refine Entails.pure_left fun ⟨hor, hpref⟩ => ?_
  rcases hor with hpan1 | hpan2 | halloc
  · exact (hnpan1 hpan1).elim
  · exact (hnpan2 hpan2).elim
  · exact Entails.pure_right ⟨halloc, hpref⟩ (Entails.refl _)

/-! ## 4. Version-Mismatch Error Funnel (`+0x1bac -> s0.readReg64 .x30`) -/

theorem entails_anyHeap_10 {P P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 F : SepProp}
    (h : P = (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6 ∗ P7 ∗ P8 ∗ P9 ∗ P10) ∗ F) : P ⊢ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗
    P6 ∗ P7 ∗ P8 ∗ P9 ∗ P10 ∗ anyHeap := by
  rw [h]; simp only [sepConj_assoc]
  repeat apply sepConj_mono_right
  exact entails_anyHeap F

theorem fnAddr_growOneSpe_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : (trTrapProgAt b C
    abs).fnAddr growOneSpeName = b + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") := by
  rw [trTrapProgAt, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")]

theorem fnAddr_growOneSpe_eq (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : (tripleRatchetProgAt b C ctl
    abs).fnAddr growOneSpeName = b + 0x15c44#64 := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr growOneSpeName]
  exact fnAddr_growOneSpe_eq_trap b C abs

theorem logOff_eq_5b810 (img : Obj.Image) :
    logOff img = ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) := rfl

theorem growOneSpe_pre_zero_eq (A : RustAlloc) (sp errsPtr0 : BitVec 64) (s : State) :
    (growOneSpeSpec A).pre (sp + 0x3c8#64, 0#64, errsPtr0, []) s = (⌜s.readReg64 .x0 = sp + 0x3c8#64
      ∧ ([] : List (BitVec 8)).length = (0#64).toNat * 48 ∧ errsPtr0 ≠ 0 ∧ max (2 * (0#64).toNat) 4
      * 48 + 8 ≤ 2 ^ 63⌝ ∗ (((sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((sp + 0x3d0#64) ↦₆₄ errsPtr0) ∗ A.pool ∗
      stackAt s.sp growOneSpeStack)) := by
  dsimp only [growOneSpeSpec]
  have h3d0 : sp + 0x3c8#64 + 8#64 = sp + 0x3d0#64 := by bv_omega
  have hite : (if (0#64 : BitVec 64) = 0 then emp
    else A.live errsPtr0 ([] : List (BitVec 8)).length 8 ∗ (errsPtr0 ↦ₛ [])) = emp := rfl
  rw [h3d0, hite, emp_sepConj]

theorem growOneSpe_post_zero_eq (A : RustAlloc) (sp errsPtr0 : BitVec 64) (s0 sf : State) :
    (growOneSpeSpec A).post (sp + 0x3c8#64, 0#64, errsPtr0, []) s0 sf = (⌜sf.trace = s0.trace⌝ ∗ ∃∗
        p' : BitVec 64, ⌜p' ≠ 0⌝ ∗ ((sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((sp + 0x3d0#64) ↦₆₄ p') ∗ A.live p'
        192 8 ∗ memRegion p' 192 ∗ A.pool ∗ stackAt s0.sp growOneSpeStack) := by
  dsimp only [growOneSpeSpec]
  have h3d0 : sp + 0x3c8#64 + 8#64 = sp + 0x3d0#64 := by bv_omega
  rw [h3d0]
  refine congrArg (⌜sf.trace = s0.trace⌝ ∗ ·) (congrArg sepExists (funext fun p' => ?_))
  have hlen : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
  rw [hlen, BitVec.add_zero, pointsToBytes_nil, emp_sepConj]
  rfl

def vecGhostRestAt (A : RustAlloc) (g : VecGhost) (a : BitVec 64) : SepProp :=
  ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗ ⌜g.bytes.length ≤
    g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗ (if g.cap = 0 then emp
     else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗ memRegion (g.ptr + BitVec.ofNat 64
       g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_split_cap (A : RustAlloc) (g : VecGhost) (a : BitVec 64) :
    vecGhostAt A g a = (a ↦₆₄ g.cap) ∗ vecGhostRestAt A g a := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostRestAt, sepConj_assoc]

def sessionStateRestAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧ (match st.remoteIdentity
    with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧ G.chains.length =
       st.receiverChains.length ∧ G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
       G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
       vecGhostRestAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ vecU8At A (ss +
       0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗ vecAt A 104 8 (chainAt A) (ss +
       0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗ vecGhostAt A G.alice (ss + 0x60#64) ∗ vecU8At A (ss +
      0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗ optSenderChainAt A (ss + 0x90#64) G.sender
      st.senderChain ∗ optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗ optTailVecAt A 32 (ss +
      0x128#64) G.kyber ∗ ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂
      st.previousCounter) ∗ ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_expose_cap (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : sessionStateAt A ss G st = (ss ↦₆₄ G.localIk.cap) ∗
    sessionStateRestAt A ss G st := by
  unfold sessionStateAt sessionStateRestAt
  rw [vecGhostAt_split_cap A G.localIk ss]
  ac_rfl

theorem sp3e0_48_ver_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 48 = (∃∗ e5 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e2 :
      BitVec 64, ∃∗ u3ec : BitVec 32, ∃∗ u3e8 : BitVec 32, ∃∗ u3e0 : BitVec 64, ((sp + 0x3e0#64) ↦₆₄
      u3e0) ∗ ((sp + 0x3e8#64) ↦₃₂ u3e8) ∗ ((sp + 0x3ec#64) ↦₃₂ u3ec) ∗ ((sp + 0x3f0#64) ↦₆₄ e2) ∗
      ((sp + 0x3f8#64) ↦₆₄ e3) ∗ ((sp + 0x400#64) ↦₆₄ e4) ∗ ((sp + 0x408#64) ↦₆₄ e5)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 40)
        (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 4) (k := 36)
        (b' := sp + 0x3ec#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 32)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 24)
        (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 16)
        (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 8)
        (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x3e0#64), ProofLib.memRegion_four (sp + 0x3e8#64),
      ProofLib.memRegion_four (sp + 0x3ec#64), ProofLib.memRegion_eight (sp + 0x3f0#64),
      ProofLib.memRegion_eight (sp + 0x3f8#64), ProofLib.memRegion_eight (sp + 0x400#64),
      ProofLib.memRegion_eight (sp + 0x408#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem pointsTo32_pair_sp3e8 (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0x3e8#64) ↦₃₂ lo) ∗ ((sp + 0x3ec#64) ↦₃₂ hi)) = ((sp + 0x3e8#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0x3ec#64 = (sp + 0x3e8#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

theorem errs192_split_eq (errsPtr : BitVec 64) :
    memRegion errsPtr 192 = (∃∗ u_e5 : BitVec 64, ∃∗ u_e4 : BitVec 64, ∃∗ u_e3 : BitVec 64, ∃∗ u_e2
      : BitVec 64, ∃∗ u_e1 : BitVec 64, ∃∗ u_e0 : BitVec 64, ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗
      ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗ ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗ ((errsPtr + 0x18#64) ↦₆₄
      u_e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗ ((errsPtr + 0x28#64) ↦₆₄ u_e5) ∗ memRegion (errsPtr +
      48#64) 144) := by
  rw [ProofLib.memRegion_split' (b := errsPtr) (n := 8) (k := 184)
        (b' := errsPtr + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x8#64) (n := 8) (k := 176)
        (b' := errsPtr + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x10#64) (n := 8) (k := 168)
        (b' := errsPtr + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x18#64) (n := 8) (k := 160)
        (b' := errsPtr + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x20#64) (n := 8) (k := 152)
        (b' := errsPtr + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x28#64) (n := 8) (k := 144)
        (b' := errsPtr + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight errsPtr, ProofLib.memRegion_eight (errsPtr + 0x8#64),
      ProofLib.memRegion_eight (errsPtr + 0x10#64), ProofLib.memRegion_eight (errsPtr + 0x18#64),
      ProofLib.memRegion_eight (errsPtr + 0x20#64), ProofLib.memRegion_eight (errsPtr + 0x28#64)]
  conv_rhs => rw [show errsPtr + 0x0#64 = errsPtr from BitVec.add_zero errsPtr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem errs48_fold_ver (errsPtr e2 e3 e4 e5 : BitVec 64) (msgVer u3ec : BitVec 32) :
    ((errsPtr + 0x0#64) ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 0x8#64) ↦₆₄ (u3ec ++ msgVer)) ∗
    ((errsPtr + 0x10#64) ↦₆₄ e2) ∗ ((errsPtr + 0x18#64) ↦₆₄ e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
    ((errsPtr + 0x28#64) ↦₆₄ e5) ⊢ (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂
    msgVer) ∗ memRegion (errsPtr + 12#64) 36 := by
  have hpair : ((errsPtr + 0x8#64) ↦₆₄ (u3ec ++ msgVer)) = ((errsPtr + 8#64) ↦₃₂ msgVer) ∗ ((errsPtr
      + 12#64) ↦₃₂ u3ec) := by
    have h12 : errsPtr + 12#64 = (errsPtr + 8#64) + 4#64 := by bv_omega
    rw [h12, ← pointsTo32_pair]
  rw [BitVec.add_zero, hpair, sepConj_assoc, ProofLib.memRegion_split' (b := errsPtr + 12#64) (n :=
    4) (k := 32)
        (b' := errsPtr + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x10#64) (n := 8) (k := 24)
        (b' := errsPtr + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x18#64) (n := 8) (k := 16)
        (b' := errsPtr + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 0x20#64) (n := 8) (k := 8)
        (b' := errsPtr + 0x28#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

theorem errs48_144_join (errsPtr : BitVec 64) :
    memRegion errsPtr 48 ∗ memRegion (errsPtr + 48#64) 144 = memRegion errsPtr 192 :=
  (ProofLib.memRegion_split errsPtr 48 144 (by decide)).symm

theorem memRegion_17_split_eq (dfPtr : BitVec 64) :
    memRegion dfPtr 17 = (∃∗ u_df10 : BitVec 8, ∃∗ u_df8 : BitVec 64, ∃∗ u_df0 : BitVec 64, ((dfPtr
      + 0x0#64) ↦₆₄ u_df0) ∗ ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗ ((dfPtr + 0x10#64) ↦₈ u_df10)) := by
  rw [ProofLib.memRegion_split' (b := dfPtr) (n := 8) (k := 9)
        (b' := dfPtr + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dfPtr + 0x8#64) (n := 8) (k := 1)
        (b' := dfPtr + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight dfPtr, ProofLib.memRegion_eight (dfPtr + 0x8#64),
      ProofLib.memRegion_one (dfPtr + 0x10#64)]
  simp only [BitVec.add_zero, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem sp270_48_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x270#64) 48 = (∃∗ u_290 : BitVec 8, ∃∗ u_288 : BitVec 64, ∃∗ u_280 : BitVec 64,
      ∃∗ u_278 : BitVec 64, ∃∗ u_270 : BitVec 64, ((sp + 0x270#64) ↦₆₄ u_270) ∗ ((sp + 0x278#64) ↦₆₄
      u_278) ∗ ((sp + 0x280#64) ↦₆₄ u_280) ∗ ((sp + 0x288#64) ↦₆₄ u_288) ∗ ((sp + 0x290#64) ↦₈
      u_290) ∗ memRegion (sp + 0x291#64) 15) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x270#64) (n := 8) (k := 40)
        (b' := sp + 0x278#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x278#64) (n := 8) (k := 32)
        (b' := sp + 0x280#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x280#64) (n := 8) (k := 24)
        (b' := sp + 0x288#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x288#64) (n := 8) (k := 16)
        (b' := sp + 0x290#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x290#64) (n := 1) (k := 15)
        (b' := sp + 0x291#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x270#64), ProofLib.memRegion_eight (sp + 0x278#64),
      ProofLib.memRegion_eight (sp + 0x280#64), ProofLib.memRegion_eight (sp + 0x288#64),
      ProofLib.memRegion_one (sp + 0x290#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem sp278_40_resplit (sp w278 w280 w288 : BitVec 64) (b290 : BitVec 8) :
    ((sp + 0x278#64) ↦₆₄ w278) ∗ ((sp + 0x280#64) ↦₆₄ w280) ∗ ((sp + 0x288#64) ↦₆₄ w288) ∗ ((sp +
    0x290#64) ↦₈ b290) ∗ memRegion (sp + 0x291#64) 15 ⊢ ∃∗ v_298 : BitVec 64, ∃∗ v_290 : BitVec 64,
    ∃∗ v_28c : BitVec 32, ∃∗ v_284 : BitVec 64, ∃∗ v_27c : BitVec 64, ∃∗ v_278 : BitVec 32, ((sp +
    0x278#64) ↦₃₂ v_278) ∗ ((sp + 0x27c#64) ↦₆₄ v_27c) ∗ ((sp + 0x284#64) ↦₆₄ v_284) ∗ ((sp +
    0x28c#64) ↦₃₂ v_28c) ∗ ((sp + 0x290#64) ↦₆₄ v_290) ∗ ((sp + 0x298#64) ↦₆₄ v_298) := by
  have h1 :
      ((sp + 0x278#64) ↦₆₄ w278) ∗ ((sp + 0x280#64) ↦₆₄ w280) ∗ ((sp + 0x288#64) ↦₆₄ w288) ∗ ((sp +
      0x290#64) ↦₈ b290) ∗ memRegion (sp + 0x291#64) 15 ⊢ memRegion (sp + 0x278#64) 40 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x278#64) (n := 8) (k := 32)
          (b' := sp + 0x280#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x280#64) (n := 8) (k := 24)
          (b' := sp + 0x288#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x288#64) (n := 8) (k := 16)
          (b' := sp + 0x290#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x290#64) (n := 1) (k := 15)
          (b' := sp + 0x291#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _
      _) (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))))
  have h2 : memRegion (sp + 0x278#64) 40 = (∃∗ v_298 : BitVec 64, ∃∗ v_290 : BitVec 64, ∃∗ v_28c :
      BitVec 32, ∃∗ v_284 : BitVec 64, ∃∗ v_27c : BitVec 64, ∃∗ v_278 : BitVec 32, ((sp + 0x278#64)
      ↦₃₂ v_278) ∗ ((sp + 0x27c#64) ↦₆₄ v_27c) ∗ ((sp + 0x284#64) ↦₆₄ v_284) ∗ ((sp + 0x28c#64) ↦₃₂
      v_28c) ∗ ((sp + 0x290#64) ↦₆₄ v_290) ∗ ((sp + 0x298#64) ↦₆₄ v_298)) := by
    rw [ProofLib.memRegion_split' (b := sp + 0x278#64) (n := 4) (k := 36)
          (b' := sp + 0x27c#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x27c#64) (n := 8) (k := 28)
          (b' := sp + 0x284#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x284#64) (n := 8) (k := 20)
          (b' := sp + 0x28c#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x28c#64) (n := 4) (k := 16)
          (b' := sp + 0x290#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x290#64) (n := 8) (k := 8)
          (b' := sp + 0x298#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_four (sp + 0x278#64), ProofLib.memRegion_eight (sp + 0x27c#64),
        ProofLib.memRegion_eight (sp + 0x284#64), ProofLib.memRegion_four (sp + 0x28c#64),
        ProofLib.memRegion_eight (sp + 0x290#64), ProofLib.memRegion_eight (sp + 0x298#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  rwa [← h2]

theorem sp370_36_ver_f_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x370#64) 36 = (∃∗ u_38c : BitVec 64, ∃∗ u_384 : BitVec 64, ∃∗ u_380 : BitVec
      32, ∃∗ u_378 : BitVec 64, ∃∗ u_370 : BitVec 64, ((sp + 0x370#64) ↦₆₄ u_370) ∗ ((sp + 0x378#64)
      ↦₆₄ u_378) ∗ ((sp + 0x380#64) ↦₃₂ u_380) ∗ ((sp + 0x384#64) ↦₆₄ u_384) ∗ ((sp + 0x38c#64) ↦₆₄
      u_38c)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x370#64) (n := 8) (k := 28)
        (b' := sp + 0x378#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x378#64) (n := 8) (k := 20)
        (b' := sp + 0x380#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x380#64) (n := 4) (k := 16)
        (b' := sp + 0x384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x384#64) (n := 8) (k := 8)
        (b' := sp + 0x38c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x370#64), ProofLib.memRegion_eight (sp + 0x378#64),
      ProofLib.memRegion_four (sp + 0x380#64), ProofLib.memRegion_eight (sp + 0x384#64),
      ProofLib.memRegion_eight (sp + 0x38c#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem sp370_36_ver_f_to_tail_b (sp v_27c v_284 v_290 v_298 : BitVec 64) (v_28c : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ v_27c) ∗ ((sp + 0x378#64) ↦₆₄ v_284) ∗ ((sp + 0x380#64) ↦₃₂ v_28c) ∗ ((sp +
    0x384#64) ↦₆₄ v_290) ∗ ((sp + 0x38c#64) ↦₆₄ v_298) ⊢ ∃∗ u20 : BitVec 32, ∃∗ u18 : BitVec 64, ∃∗
    u10 : BitVec 64, ∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64, ((sp + 0x370#64) ↦₆₄ u0) ∗ ((sp +
    0x378#64) ↦₆₄ u8) ∗ ((sp + 0x380#64) ↦₆₄ u10) ∗ ((sp + 0x388#64) ↦₆₄ u18) ∗ ((sp + 0x390#64) ↦₃₂
    u20) := by
  have h := memRegion36_split_eq (sp + 0x370#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [← h, ProofLib.memRegion_split' (b := sp + 0x370#64) (n := 8) (k := 28)
        (b' := sp + 0x378#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x378#64) (n := 8) (k := 20)
        (b' := sp + 0x380#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x380#64) (n := 4) (k := 16)
        (b' := sp + 0x384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x384#64) (n := 8) (k := 8)
        (b' := sp + 0x38c#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo32_entails_memRegion _
    _) (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))

theorem optTailVecAt_none_1f0_eq (A : RustAlloc) (coroPtr : BitVec 64) :
    ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x1f8#64) 40 =
      optTailVecAt A 48 (coroPtr + 0x1f0#64) none := by
  dsimp only [optTailVecAt, noneCap]
  have h8 : coroPtr + 0x1f0#64 + 8#64 = coroPtr + 0x1f8#64 := by bv_omega
  rw [h8]

theorem optTailVecAt_none_220_eq (A : RustAlloc) (coroPtr : BitVec 64) :
    ((coroPtr + 0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x228#64) 24 =
      optTailVecAt A 32 (coroPtr + 0x220#64) none := by
  dsimp only [optTailVecAt, noneCap]
  have h8 : coroPtr + 0x220#64 + 8#64 = coroPtr + 0x228#64 := by bv_omega
  rw [h8]

theorem sp3e0_104_split_48 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 104 = memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 56 :=
  ProofLib.memRegion_split' rfl (by bv_omega) (by decide)

def stageP3ClonePre (A : RustAlloc) (sp coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr ctxPtr
    u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978
    u980 u988 : BitVec 64) (prevCounter f248 f24c u_30 u_34 u_5c u_7c : BitVec 32) (sg :
    SenderChainGhost) (sc : SenderChain) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes : List
    (BitVec 8)) : SepProp :=
  A.pool ∗ stackAt sp chainCloneStack ∗ memRegion (sp + 0x3e0#64) 104 ∗
  ((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64) ↦₆₄ 33#64) ∗ (locIdPtr ↦ₛ locIdBytes)
    ∗
  ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr + 0x120#64) ↦₆₄ 33#64) ∗ (remIdPtr ↦ₛ remIdBytes)
    ∗
  ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗ (rootKeyPtr ↦ₛ
    rootKeyBytes) ∗
  ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗ ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗ (aliceBasePtr ↦ₛ
    aliceBaseBytes) ∗
  ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗ optSenderChainAt A (coroPtr + 0x188#64) (some sg) (some sc) ∗
  ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((coroPtr + 0x220#64) ↦₆₄
    0xffffffffffffffff#64) ∗
  ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64) ↦₃₂ prevCounter) ∗
  ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
  ((sp + 0x30#64) ↦₃₂ u_30) ∗ ((sp + 0x34#64) ↦₃₂ u_34) ∗ ((sp + 0x38#64) ↦₆₄ u_38) ∗ ((sp +
    0x40#64) ↦₆₄ u_40) ∗
  ((sp + 0x48#64) ↦₆₄ u_48) ∗ ((sp + 0x50#64) ↦₆₄ u_50) ∗ ((sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((sp +
    0x60#64) ↦₆₄ u_60) ∗
  ((sp + 0x68#64) ↦₆₄ u_68) ∗ ((sp + 0x70#64) ↦₆₄ u_70) ∗ ((sp + 0x7c#64) ↦₃₂ u_7c) ∗ ((sp +
    0x98#64) ↦₆₄ u_98) ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  ((sp + 0x930#64) ↦₆₄ u930) ∗ ((sp + 0x938#64) ↦₆₄ u938) ∗ ((sp + 0x940#64) ↦₆₄ u940) ∗ ((sp +
    0x948#64) ↦₆₄ u948) ∗
  ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960) ∗ ((sp +
    0x968#64) ↦₆₄ u968) ∗
  ((sp + 0x970#64) ↦₆₄ u970) ∗ ((sp + 0x978#64) ↦₆₄ u978) ∗ ((sp + 0x980#64) ↦₆₄ u980) ∗ ((sp +
    0x988#64) ↦₆₄ u988)

def bobCoroRestAt (A : RustAlloc) (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr : BitVec 64) :
  SepProp :=
  ((coroPtr + 0xf8#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x110#64) ↦₆₄ 33#64) ∗
  ((coroPtr + 0x128#64) ↦₆₄ 32#64) ∗ ((coroPtr + 0x140#64) ↦₆₄ 0#64) ∗
  ((coroPtr + 0x148#64) ↦₆₄ 8#64) ∗ ((coroPtr + 0x158#64) ↦₆₄ 33#64) ∗
  ((coroPtr + 0x170#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x178#64) ↦₆₄ 1#64) ∗
  memRegion (coroPtr + 0x1f8#64) 40 ∗ memRegion (coroPtr + 0x228#64) 24 ∗
  A.live locIdPtr 33 1 ∗ A.live remIdPtr 33 1 ∗ A.live rootKeyPtr 32 1 ∗ A.live aliceBasePtr 33 1

theorem bobCoroRest_fold_sessionStateAt {A : RustAlloc}
    (coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr : BitVec 64) (locIdBytes remIdBytes
    rootKeyBytes aliceBaseBytes : List (BitVec 8)) (sg : SenderChainGhost) (sc : SenderChain)
    (prevCounter f248 f24c : BitVec 32) (st : SessionState (List (BitVec 8))) (remIk : IdentityKey)
    (hnew1 : locIdPtr ≠ 0#64) (hnew2 : remIdPtr ≠ 0#64) (hnew3 : rootKeyPtr ≠ 0#64) (hnew4 :
    aliceBasePtr ≠ 0#64) (hloc_len : locIdBytes.length = 33) (hrem_len : remIdBytes.length = 33)
    (halice_len : aliceBaseBytes.length = 33) (hloc_deser : PublicKey.deserialize locIdBytes = .ok
    st.localIdentity.publicKey) (hrem_eq : st.remoteIdentity = some remIk) (hrem_deser :
    PublicKey.deserialize remIdBytes = .ok remIk.publicKey) (hroot_eq : rootKeyBytes = keyToBytes32
    st.rootKey) (hrc : st.receiverChains = []) (hpq : st.pqRatchetState = []) (hsc : st.senderChain
    = some sc) (hpend : st.pendingPreKey = false) (hver : st.sessionVersion = 4#32) (hprev :
    st.previousCounter = prevCounter) : (((coroPtr + 0x100#64) ↦₆₄ locIdPtr) ∗ ((coroPtr + 0x108#64)
    ↦₆₄ 33#64) ∗ (locIdPtr ↦ₛ locIdBytes) ∗ ((coroPtr + 0x118#64) ↦₆₄ remIdPtr) ∗ ((coroPtr +
    0x120#64) ↦₆₄ 33#64) ∗ (remIdPtr ↦ₛ remIdBytes) ∗ ((coroPtr + 0x130#64) ↦₆₄ rootKeyPtr) ∗
    ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗ (rootKeyPtr ↦ₛ rootKeyBytes) ∗ ((coroPtr + 0x150#64) ↦₆₄
    0#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ aliceBasePtr) ∗ ((coroPtr + 0x168#64) ↦₆₄ 33#64) ∗
    (aliceBasePtr ↦ₛ aliceBaseBytes) ∗ ((coroPtr + 0x180#64) ↦₆₄ 0#64) ∗ optSenderChainAt A (coroPtr
    + 0x188#64) (some sg) (some sc) ∗ ((coroPtr + 0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((coroPtr +
    0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((coroPtr + 0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64)
    ↦₃₂ prevCounter) ∗ ((coroPtr + 0x248#64) ↦₃₂ f248) ∗ ((coroPtr + 0x24c#64) ↦₃₂ f24c) ∗
    bobCoroRestAt A coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr) ⊢ sessionStateAt A (coroPtr +
    0xf8#64)
      (mkClonedGhost locIdPtr remIdPtr rootKeyPtr aliceBasePtr
        locIdBytes remIdBytes aliceBaseBytes sg f248 f24c) st := by
  dsimp only [bobCoroRestAt]
  have h := bobSlots_coro_0xf8_entails_sessionStateAt (A := A)
    coroPtr locIdPtr remIdPtr rootKeyPtr aliceBasePtr locIdBytes remIdBytes rootKeyBytes
    aliceBaseBytes sg sc prevCounter f248 f24c st remIk hnew1 hnew2 hnew3 hnew4 hloc_len hrem_len
    halice_len hloc_deser hrem_eq hrem_deser hroot_eq hrc hpq hsc hpend hver hprev
  rw [← optTailVecAt_none_1f0_eq, ← optTailVecAt_none_220_eq] at h
  exact Entails.trans (Entails.of_eq (by ac_rfl)) h

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
