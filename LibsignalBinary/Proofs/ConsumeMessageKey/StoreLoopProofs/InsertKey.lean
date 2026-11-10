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
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.LibsignalSession.StoreLoop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open CryptoVerification.HookTrace

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? cmkDummyImg
attribute [-simp, -arm64_norm, -wp_norm] logFilterAddr_cmkDummyImg
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack, `SepWPp`, and Memory Slot Helpers -/

private theorem stackAt_7712_eq_grow (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 3104 ∗ stackAt sp 4608 := by
  simp only [stackAt]
  rw [show (7712 : Nat) = 3104 + 4608 from rfl, memRegion_split _ 3104 4608 (by decide)]
  have h : sp - 7712#64 + BitVec.ofNat 64 3104 = sp - 4608#64 := by bv_arith
  rw [h]

private theorem stackAt_7712_eq_4096 (sp : BitVec 64) :
    stackAt sp 7712 = memRegion (sp - 7712#64) 3616 ∗ stackAt sp 4096 := by
  simp only [stackAt]
  rw [show (7712 : Nat) = 3616 + 4096 from rfl, memRegion_split _ 3616 4096 (by decide)]
  have h : sp - 7712#64 + BitVec.ofNat 64 3616 = sp - 4096#64 := by bv_arith
  rw [h]

private theorem sepWP_elim_inv {prog : Program} {img : Obj.Image} {mid : BitVec 64}
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

private theorem steps_of_sepWPp {prog : Program} {img : Obj.Image} {ret : BitVec 64}
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

private theorem SepWPp.call_growOne {prog : Program} {img : Obj.Image}
    {entry ret : BitVec 64} {A : RustAlloc}
    (hsub : subroutine_ok prog entry ((growOneSpec A).inImage img))
    (x : GrowGhost) {s : State} {P F_frame : SepProp} {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hpre : P ⊢ (growOneSpec A).pre x s ∗ F_frame)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf ((growOneSpec A).onPanic x s sf ∗ F_frame))
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf ((growOneSpec A).post x s sf ∗ F_frame) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  exact ProofLib.SepWPp.call_wpp_frozen hsub (x := x) (F := F_frame) hfl hsym hpc hrun hsp rfl
    (fun R hm => by
      have hm1 : s.mem ⊨ ((growOneSpec A).pre x s ∗ F_frame) ∗ R :=
        Satisfies.mono (sepConj_mono_left hpre) hm
      rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfl, hsym⟩, by simpa only [sepConj_assoc] using hm1⟩)
    (fun _ _ _ _ hundef_mem => by
      unfold Spec.inImage growOneSpec at hundef_mem
      dsimp only at hundef_mem
      rw [satisfies_pure_sepConj] at hundef_mem
      exact hundef_mem.1)
    (fun sf hpanm _ => hpanic sf hpanm)
    (fun sf hpcm hrunm hspm hcsm hflm hsymm => by
      have hsp_alignm : sf.spAligned = true := by
        simpa [State.spAligned, hspm] using hsp
      exact hcont sf hpcm hspm hrunm hsp_alignm hcsm hflm hsymm)
    (fun _ _ _ hoom => (not_satisfies_false_sepConj hoom).elim)

private theorem growOne_panic_entails_cmkPanic (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (gx : GrowGhost)
    {s0 s sf : State} (F_frame F_rest R : SepProp)
    (hm : sf.mem ⊨ ((growOneSpec A).onPanic gx s sf ∗ F_frame) ∗ (F_rest ∗ R))
    (htr : s.trace = s0.trace) :
    sf.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 sf ∗ R := by
  unfold growOneSpec at hm
  dsimp only at hm
  rw [← sepConj_assoc _ F_rest R, sepConj_assoc _ F_frame F_rest] at hm
  have halloc_eq : allocFailedIn s sf = allocFailedIn s0 sf := by
    simp only [allocFailedIn, htr]
  unfold consumeMessageKeySpec Spec.inImage
  dsimp only
  exact allowPanic_frame (fun ⟨ha, hp⟩ => ⟨Or.inr (halloc_eq ▸ ha), htr ▸ hp⟩) hm

private theorem memRegion_104_entails_messageKey_words (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
      ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
      ∃∗ w12 : BitVec 32,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
        ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
        ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
        ((a + 96#64) ↦₃₂ w12) ∗ memRegion (a + 100#64) 4 := by
  refine Entails.trans (memRegion_104_entails_messageKey_slots a) ?_
  rw [memRegion_24_eq_exists_vecHeader a,
      memRegion_24_eq_exists_vecHeader (a + 24#64),
      memRegion_24_eq_exists_vecHeader (a + 48#64),
      memRegion_24_eq_exists_vecHeader (a + 72#64),
      memRegion_four (a + 96#64)]
  simp only [vecHeader, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w7
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w9
  apply Entails.sepExists_elim; intro w10
  apply Entails.sepExists_elim; intro w11
  apply Entails.sepExists_elim; intro w12
  apply Entails.sepExists_right w10
  apply Entails.sepExists_right w11
  apply Entails.sepExists_right w12
  apply Entails.sepExists_right w7
  apply Entails.sepExists_right w8
  apply Entails.sepExists_right w9
  apply Entails.sepExists_right w4
  apply Entails.sepExists_right w5
  apply Entails.sepExists_right w6
  apply Entails.sepExists_right w1
  apply Entails.sepExists_right w2
  apply Entails.sepExists_right w3
  apply Entails.sepExists_right w0
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_arith
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_arith
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_arith
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_arith
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_arith
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_arith
  rw [h32, h40, h56, h64, h80, h88]
  exact Entails.refl _

private theorem messageKeyAt_newMsgKeyGhost_intro (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (ckc : CryptoGames.LibsignalSession.ChainKey) (seedPtr a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
     ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
     ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
     ((a + 72#64) ↦₆₄ 32#64) ∗ ((a + 80#64) ↦₆₄ seedPtr) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
     ((a + 96#64) ↦₃₂ ckc.index) ∗ memRegion (a + 100#64) 4 ∗
     vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
    messageKeyAt A (newMsgKeyGhost seedPtr, ckc.messageKeys F) a := by
  have hseed_len : (ckc.messageKeys F).seed.length = 32 := messageKeys_seed_length F ckc
  have hseed_ne : (ckc.messageKeys F).seed ≠ [] := by
    intro hnil; rw [hnil] at hseed_len; contradiction
  have hctr : (ckc.messageKeys F).counter = ckc.index := rfl
  rw [messageKeyAt_eq_headers_sep_heap]
  unfold messageKeyHeap newMsgKeyGhost vecHeader
  dsimp only
  rw [hseed_len, hctr]
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_arith
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_arith
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_arith
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_arith
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_arith
  have h88 : a + 72#64 + 16#64 = a + 88#64 := by bv_arith
  rw [h32, h40, h56, h64, h80, h88]
  have hpure0 : emp ⊢ vecU8Buf A 0#64 1#64 [] := by
    unfold vecU8Buf
    simp only [BitVec.ofNat_eq_ofNat, ↓reduceIte]
    exact Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)
  have hassoc :
      ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
       ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
       ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
       ((a + 72#64) ↦₆₄ 32#64) ∗ ((a + 80#64) ↦₆₄ seedPtr) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
       ((a + 96#64) ↦₃₂ ckc.index) ∗ memRegion (a + 100#64) 4 ∗
       vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      (((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
       (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
       (((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64)) ∗
       (((a + 72#64) ↦₆₄ 32#64) ∗ ((a + 80#64) ↦₆₄ seedPtr) ∗ ((a + 88#64) ↦₆₄ 32#64)) ∗
       ((a + 96#64) ↦₃₂ ckc.index) ∗ memRegion (a + 100#64) 4) ∗
      (emp ∗ emp ∗ emp ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) := by
    ac_rfl
  rw [hassoc]
  apply sepConj_mono_right
  apply Entails.pure_right hseed_ne
  exact sepConj_mono hpure0 (sepConj_mono hpure0 (sepConj_mono_left hpure0))

theorem pointsToBytes_insert0_zero (ptr : BitVec 64) {bs slotBs : List (BitVec 8)}
    (hbs0 : bs.length = 0) (hslot : slotBs.length = 104) :
    (ptr ↦ₛ (bs ++ slotBs)) ⊢ memRegion ptr 104 ∗ ((ptr + 104#64) ↦ₛ bs) := by
  have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero hbs0
  subst hbs_nil
  simp only [List.nil_append, pointsToBytes_nil, sepConj_emp]
  have h := pointsToBytes_entails_memRegion ptr slotBs
  rwa [hslot] at h

private theorem vecBuf_messageKeyAt_bounds (A : RustAlloc) (cap ptr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) :
    vecBuf A 104 8 (messageKeyAt A) cap ptr gks ⊢
      ⌜gks.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        vecBuf A 104 8 (messageKeyAt A) cap ptr gks := by
  by_cases hcap : cap = 0
  · subst hcap
    rw [vecBuf_zero, ← sepConj_emp ⌜gks = [] ∧ ptr ≠ 0⌝]
    apply Entails.pure_left
    rintro ⟨hnil, hptr⟩
    apply Entails.pure_right ⟨by simp [hnil], by decide, hptr⟩
    exact Entails.pure_right ⟨hnil, hptr⟩ (Entails.refl _)
  · rw [vecBuf_of_ne_zero A 104 8 (messageKeyAt A) cap ptr gks hcap]
    apply Entails.pure_left
    rintro ⟨hlen, hcap_lt, hptr⟩
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    exact Entails.pure_right ⟨hlen, hcap_lt, hptr⟩ (Entails.refl _)

/-! ## Active and Passive Frame Split -/

def insertKeyActivePre (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (chainPtr : BitVec 64) (cg : ChainGhost) (chc : ReceiverChain)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (seedPtr sp : BitVec 64) : SepProp :=
  vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) ∗
  vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
  vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
  stackAt sp 7712 ∗
  A.pool

def insertKeyActiveMid (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (chainPtr mkCap1 mkPtr1 : BitVec 64) (cg : ChainGhost) (chc : ReceiverChain)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (seedPtr sp : BitVec 64)
    (bs : List (BitVec 8)) : SepProp :=
  vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 chc.messageKeys.length) ∗
  A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
  memRegion mkPtr1 104 ∗
  ((mkPtr1 + 104#64) ↦ₛ bs) ∗
  memRegion (mkPtr1 + BitVec.ofNat 64 ((chc.messageKeys.length + 1) * 104))
    ((mkCap1.toNat - (chc.messageKeys.length + 1)) * 104) ∗
  messageKeyHeaps A (cg.keys.zip chc.messageKeys) ∗
  vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
  stackAt sp 7712 ∗
  A.pool

def insertKeyActivePost (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (chainPtr mkCap1 mkPtr1 : BitVec 64) (cg : ChainGhost) (chc : ReceiverChain)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (seedPtr sp : BitVec 64) : SepProp :=
  vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
  vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
    ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
  stackAt sp 7712 ∗
  A.pool

private def insertKeyFrame (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0

private theorem insertKeyState_chains_len (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (seedPtr : BitVec 64) (s0 : State) :
    (cmkLoopHeap A img x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
      ⌜Gc.chains.length = stc.receiverChains.length⌝ ∗
        (cmkLoopHeap A img x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) := by
  unfold cmkLoopHeap ratchetAt
  simp only [sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨h1, h2, h3⟩
  exact Entails.pure_right h1 (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))

private theorem insertKeyState_split_active (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (seedPtr : BitVec 64) (s0 : State)
    (hchc : stc.receiverChains[ci]? = some chc)
    (hci_g : ci < Gc.chains.length) :
    let cg := Gc.chains[ci]
    (cmkLoopHeap A img x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
      ⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length⌝ ∗
        insertKeyActivePre F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) cg chc ckc seedPtr (s0.sp - 480#64) ∗
        insertKeyFrame A img x Gc stc ckc ci chc cg s0 := by
  intro cg
  have ⟨hci_st, hchc_get⟩ := List.getElem?_eq_some_iff.mp hchc
  unfold cmkLoopHeap
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_left (ratchetAt_split_chain A x.self Gc stc hci_st hci_g))) ?_
  rw [hchc_get]
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hchain_eq : chainAt A (Gc.chains[ci], chc) chainPtr =
      (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length ∧
        cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       (vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) := rfl
  rw [hchain_eq]
  have hpull0 :
      (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
          chc.messageKeys.length ≤ maxMessageKeys ∧
          cg.keys.length = chc.messageKeys.length ∧
          cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
         vecGhostAt A cg.srk chainPtr ∗
         vecGhostAt A cg.priv (chainPtr + 24#64) ∗
         (vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
          vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) ∗
         optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length ∧
        cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed)) := by
    ac_rfl
  rw [hpull0]
  apply Entails.pure_left; rintro ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  rw [hzip_len]
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  unfold insertKeyActivePre insertKeyFrame ratchetContextAt
  dsimp only
  have hpull :
      (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      ((vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool) ∗
       emp ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
       (emp ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_right
  rw [emp_sepConj]
  refine Entails.pure_right ⟨hsrk_len, hpriv⟩ ?_
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_left
  exact Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, h7⟩ (by rw [emp_sepConj]; exact Entails.refl _)

private theorem insertKeyPost_entails_evictOldestKeyHeap (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hlen2000 : chc.messageKeys.length = 2000) :
    (insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗
      insertKeyFrame A img x Gc stc ckc ci chc cg s0) ⊢
      evictOldestKeyHeap F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 := by
  unfold insertKeyActivePost insertKeyFrame evictOldestKeyHeap
  dsimp only
  rw [hlen2000]
  exact Entails.of_eq (by ac_rfl)

private theorem insertKeyPost_entails_cmkLoopHeap_D (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (img : Obj.Image) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hci_st : ci < stc.receiverChains.length)
    (hsrk : PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hlt2000 : chc.messageKeys.length < 2000) :
    let cg' : ChainGhost :=
      { cg with
        mkCap := mkCap1
        mkPtr := mkPtr1
        keys := newMsgKeyGhost seedPtr :: cg.keys }
    (insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗
      insertKeyFrame A img x Gc stc ckc ci chc cg s0) ⊢
      cmkLoopHeap A img x (Gc.setChain ci cg') (updatedRatchetState F stc ci chc ckc) ckc s0 := by
  intro cg'
  have htake : (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys =
      ckc.messageKeys F :: chc.messageKeys := by
    apply List.take_of_length_le
    simp only [List.length_cons, maxMessageKeys]
    omega
  have hupd_ch : updatedReceiverChain F chc ckc =
      { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys } := by
    unfold updatedReceiverChain
    rw [htake]
  have hupd_st : updatedRatchetState F stc ci chc ckc =
      stc.setChain ci { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys } := by
    unfold updatedRatchetState RatchetState.setChain
    rw [hupd_ch]
  rw [hupd_st]
  have hmax' : (ckc.messageKeys F :: chc.messageKeys).length ≤ maxMessageKeys := by
    simp only [List.length_cons, maxMessageKeys]; omega
  have hklen' : (newMsgKeyGhost seedPtr :: cg.keys).length =
      (ckc.messageKeys F :: chc.messageKeys).length := by
    simp [hklen]
  have hzip_cons :
      (newMsgKeyGhost seedPtr :: cg.keys).zip (ckc.messageKeys F :: chc.messageKeys) =
        (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys := rfl
  have hzip_len' :
      ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys).length =
        chc.messageKeys.length + 1 := by
    simp [hklen]
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  unfold insertKeyActivePost insertKeyFrame cmkLoopHeap ratchetContextAt
  dsimp only
  have hpull0 :
      ((vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool) ∗
       ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
       (⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
          stc.maxForwardJumps < 2 ^ 64 ∧
          stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
          Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0) =
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       ⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
        stc.maxForwardJumps < 2 ^ 64 ∧
        stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
        Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
       (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0)) := by ac_rfl
  rw [hpull0]
  apply Entails.pure_left; rintro ⟨hsrk_len, hpriv⟩
  apply Entails.pure_left; rintro ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, _⟩
  have hchain :
      (vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ⊢
      chainAt A (cg', { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys }) chainPtr := by
    have h := chainAt_of_update_messageKeys A cg chc chainPtr mkCap1 mkPtr1
      (newMsgKeyGhost seedPtr :: cg.keys) (ckc.messageKeys F :: chc.messageKeys)
      hsrk hmax' hklen' hsrk_len hpriv
    unfold vecAt at h
    rw [hzip_cons, hzip_len'] at h
    have heq :
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
            ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) =
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
           vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
             ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys)) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) := by ac_rfl
    rw [heq]
    exact h
  have hpull1 :
      (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0) =
      ((vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
            ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) := by ac_rfl
  rw [hpull1]
  apply sepConj_mono_left
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hchain))) ?_
  exact ratchetAt_set_chain A x.self Gc stc hci_st cg'
    { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys }
    hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne

private def insertKeyFrameAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (Gc : RatchetGhost) (stc : RatchetState) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (s0 : State) : SepProp :=
  let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
  vecGhostAt A cg.srk chainPtr ∗
  vecGhostAt A cg.priv (chainPtr + 24#64) ∗
  optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
  ratchetContextAt A x.self Gc stc ci ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes ckc) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  cmkLoopFrame s0.sp x.ret x.counter ∗
  cmkSavedRegs s0.sp s0

private theorem insertKeyStateAt_chains_len (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (seedPtr : BitVec 64) (s0 : State) :
    (cmkLoopHeapAt A logAddr x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
      ⌜Gc.chains.length = stc.receiverChains.length⌝ ∗
        (cmkLoopHeapAt A logAddr x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) := by
  unfold cmkLoopHeapAt ratchetAt
  simp only [sepConj_assoc]
  apply Entails.pure_left
  rintro ⟨h1, h2, h3⟩
  exact Entails.pure_right h1 (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))

private theorem insertKeyStateAt_split_active (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (seedPtr : BitVec 64) (s0 : State)
    (hchc : stc.receiverChains[ci]? = some chc)
    (hci_g : ci < Gc.chains.length) :
    let cg := Gc.chains[ci]
    (cmkLoopHeapAt A logAddr x Gc stc ckc s0 ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) ⊢
      ⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length⌝ ∗
        insertKeyActivePre F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) cg chc ckc seedPtr (s0.sp - 480#64) ∗
        insertKeyFrameAt A logAddr x Gc stc ckc ci chc cg s0 := by
  intro cg
  have ⟨hci_st, hchc_get⟩ := List.getElem?_eq_some_iff.mp hchc
  unfold cmkLoopHeapAt
  refine Entails.trans
    (sepConj_mono_left (sepConj_mono_left (ratchetAt_split_chain A x.self Gc stc hci_st hci_g))) ?_
  rw [hchc_get]
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hchain_eq : chainAt A (Gc.chains[ci], chc) chainPtr =
      (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length ∧
        cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       (vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) := rfl
  rw [hchain_eq]
  have hpull0 :
      (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
          chc.messageKeys.length ≤ maxMessageKeys ∧
          cg.keys.length = chc.messageKeys.length ∧
          cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
         vecGhostAt A cg.srk chainPtr ∗
         vecGhostAt A cg.priv (chainPtr + 24#64) ∗
         (vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
          vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) ∗
         optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      (⌜PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey ∧
        chc.messageKeys.length ≤ maxMessageKeys ∧
        cg.keys.length = chc.messageKeys.length ∧
        cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 (cg.keys.zip chc.messageKeys).length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed)) := by
    ac_rfl
  rw [hpull0]
  apply Entails.pure_left; rintro ⟨hsrk, hmax, hklen, hsrk_len, hpriv⟩
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  rw [hzip_len]
  apply Entails.pure_right ⟨hsrk, hmax, hklen⟩
  unfold insertKeyActivePre insertKeyFrameAt ratchetContextAt
  dsimp only
  have hpull :
      (vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      ((vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) ∗
        vecBuf A 104 8 (messageKeyAt A) cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool) ∗
       emp ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
       (emp ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logAddr ↦₆₄ 0#64) ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0) := by
    ac_rfl
  rw [hpull]
  apply sepConj_mono_right
  rw [emp_sepConj]
  refine Entails.pure_right ⟨hsrk_len, hpriv⟩ ?_
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_left
  exact Entails.pure_right ⟨h1, h2, h3, h4, h5, h6, h7⟩ (by rw [emp_sepConj]; exact Entails.refl _)

private theorem insertKeyPost_entails_evictOldestKeyHeapAt (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hlen2000 : chc.messageKeys.length = 2000) :
    (insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗
      insertKeyFrameAt A logAddr x Gc stc ckc ci chc cg s0) ⊢
      evictOldestKeyHeapAt F A logAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 := by
  unfold insertKeyActivePost insertKeyFrameAt evictOldestKeyHeapAt
  dsimp only
  rw [hlen2000]
  exact Entails.of_eq (by ac_rfl)

private theorem insertKeyPost_entails_cmkLoopHeapAt_D (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (ci : Nat) (chc : ReceiverChain)
    (cg : ChainGhost) (mkCap1 mkPtr1 seedPtr : BitVec 64) (s0 : State)
    (hci_st : ci < stc.receiverChains.length)
    (hsrk : PublicKey.deserialize cg.srk.bytes = .ok chc.senderRatchetKey)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hlt2000 : chc.messageKeys.length < 2000) :
    let cg' : ChainGhost :=
      { cg with
        mkCap := mkCap1
        mkPtr := mkPtr1
        keys := newMsgKeyGhost seedPtr :: cg.keys }
    (insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗
      insertKeyFrameAt A logAddr x Gc stc ckc ci chc cg s0) ⊢
      cmkLoopHeapAt A logAddr x (Gc.setChain ci cg') (updatedRatchetState F stc ci chc ckc) ckc s0 := by
  intro cg'
  have htake : (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys =
      ckc.messageKeys F :: chc.messageKeys := by
    apply List.take_of_length_le
    simp only [List.length_cons, maxMessageKeys]
    omega
  have hupd_ch : updatedReceiverChain F chc ckc =
      { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys } := by
    unfold updatedReceiverChain
    rw [htake]
  have hupd_st : updatedRatchetState F stc ci chc ckc =
      stc.setChain ci { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys } := by
    unfold updatedRatchetState RatchetState.setChain
    rw [hupd_ch]
  rw [hupd_st]
  have hmax' : (ckc.messageKeys F :: chc.messageKeys).length ≤ maxMessageKeys := by
    simp only [List.length_cons, maxMessageKeys]; omega
  have hklen' : (newMsgKeyGhost seedPtr :: cg.keys).length =
      (ckc.messageKeys F :: chc.messageKeys).length := by
    simp [hklen]
  have hzip_cons :
      (newMsgKeyGhost seedPtr :: cg.keys).zip (ckc.messageKeys F :: chc.messageKeys) =
        (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys := rfl
  have hzip_len' :
      ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys).length =
        chc.messageKeys.length + 1 := by
    simp [hklen]
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  unfold insertKeyActivePost insertKeyFrameAt cmkLoopHeapAt ratchetContextAt
  dsimp only
  have hpull0 :
      ((vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool) ∗
       ⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       vecGhostAt A cg.srk chainPtr ∗
       vecGhostAt A cg.priv (chainPtr + 24#64) ∗
       optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
       (⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
          stc.maxForwardJumps < 2 ^ 64 ∧
          stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
          Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logAddr ↦₆₄ 0#64) ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0) =
      (⌜cg.srk.bytes.length = 33 ∧ cg.priv.bytes = []⌝ ∗
       ⌜Gc.chains.length = stc.receiverChains.length ∧ Gc.senderPad.length = 100 ∧
        stc.maxForwardJumps < 2 ^ 64 ∧
        stc.receiverChains.length ≤ Gc.chainsCap.toNat ∧
        Gc.chainsCap.toNat * 104 < 2 ^ 63 ∧ Gc.chainsPtr ≠ 0 ∧ Gc.chainsCap ≠ 0⌝ ∗
       (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0)) := by ac_rfl
  rw [hpull0]
  apply Entails.pure_left; rintro ⟨hsrk_len, hpriv⟩
  apply Entails.pure_left; rintro ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, _⟩
  have hchain :
      (vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ⊢
      chainAt A (cg', { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys }) chainPtr := by
    have h := chainAt_of_update_messageKeys A cg chc chainPtr mkCap1 mkPtr1
      (newMsgKeyGhost seedPtr :: cg.keys) (ckc.messageKeys F :: chc.messageKeys)
      hsrk hmax' hklen' hsrk_len hpriv
    unfold vecAt at h
    rw [hzip_cons, hzip_len'] at h
    have heq :
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
            ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) =
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
           vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
             ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys)) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) := by ac_rfl
    rw [heq]
    exact h
  have hpull1 :
      (vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
        vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
          ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        A.pool ∗
        vecGhostAt A cg.srk chainPtr ∗
        vecGhostAt A cg.priv (chainPtr + 24#64) ∗
        optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64) ∗
        vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ chainKeyBytes ckc) ∗
        memRegion x.ret 88 ∗
        (logAddr ↦₆₄ 0#64) ∗
        cmkLoopFrame s0.sp x.ret x.counter ∗
        cmkSavedRegs s0.sp s0) =
      ((vecHeader x.self Gc.chainsCap Gc.chainsPtr (BitVec.ofNat 64 stc.receiverChains.length) ∗
        A.live Gc.chainsPtr (Gc.chainsCap.toNat * 104) 8 ∗
        (vecGhostAt A cg.srk chainPtr ∗
          vecGhostAt A cg.priv (chainPtr + 24#64) ∗
          vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 (chc.messageKeys.length + 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap1 mkPtr1
            ((newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys) ∗
          optChainKeyAt A cg.ck chc.chainKey (chainPtr + 72#64)) ∗
        arrayAt (chainAt A) 104 Gc.chainsPtr ((Gc.chains.zip stc.receiverChains).take ci) ∗
        arrayAt (chainAt A) 104 (Gc.chainsPtr + BitVec.ofNat 64 ((ci + 1) * 104))
          ((Gc.chains.zip stc.receiverChains).drop (ci + 1)) ∗
        memRegion (Gc.chainsPtr + BitVec.ofNat 64 (stc.receiverChains.length * 104))
          ((Gc.chainsCap.toNat - stc.receiverChains.length) * 104) ∗
        ((x.self + 24#64) ↦ₛ optSenderChainBytes stc.senderChain Gc.senderPad) ∗
        ((x.self + 128#64) ↦ₛ keyToBytes32 stc.rootKey) ∗
        ((x.self + 160#64) ↦₆₄ BitVec.ofNat 64 stc.maxForwardJumps) ∗
        ((x.self + 168#64) ↦₃₂ stc.previousCounter) ∗ memRegion (x.self + 172#64) 4) ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes ckc) ∗
       memRegion x.ret 88 ∗
       (logAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       cmkLoopFrame s0.sp x.ret x.counter ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) := by ac_rfl
  rw [hpull1]
  apply sepConj_mono_left
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hchain))) ?_
  exact ratchetAt_set_chain A x.self Gc stc hci_st cg'
    { chc with messageKeys := ckc.messageKeys F :: chc.messageKeys }
    hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne

/-! ## Pointer Arithmetic Helpers -/

theorem madd_chainPtr_eq (chainsPtr : BitVec 64) (ci : Nat) :
    chainsPtr + BitVec.ofNat 64 ci * 104#64 =
      chainsPtr + BitVec.ofNat 64 (ci * 104) := by
  rw [show (104#64 : BitVec 64) = BitVec.ofNat 64 104 from rfl, ← BitVec.ofNat_mul]

theorem madd_104_toNat {len : Nat} (hlen : len ≤ 2000) :
    (BitVec.ofNat 64 len * 104#64).toNat = len * 104 := by
  rw [← BitVec.ofNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem mkLen_beq_mkCap_false {len : Nat} {cap : BitVec 64}
    (hlt : len < cap.toNat) :
    (BitVec.ofNat 64 len == cap) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  have hcap : cap.toNat < 2 ^ 64 := cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  omega

theorem mkLen_eq_mkCap_of_eq {len : Nat} {cap : BitVec 64}
    (heq : len = cap.toNat) :
    BitVec.ofNat 64 len = cap := by
  apply BitVec.eq_of_toNat_eq
  have hcap : cap.toNat < 2 ^ 64 := cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), heq]

theorem mkLen_ule_1999_eq_true {len : Nat} (hlt : len < 2000) :
    (BitVec.ofNat 64 len).ule 1999#64 = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  change len ≤ 1999
  omega

theorem mkLen_ule_1999_eq_false {len : Nat} (heq : len = 2000) :
    (BitVec.ofNat 64 len).ule 1999#64 = false := by
  subst heq
  decide

theorem add_one_ofNat_64 (len : Nat) :
    BitVec.ofNat 64 len + 1#64 = BitVec.ofNat 64 (len + 1) := by
  rw [← BitVec.ofNat_add]

/-! ## Post-`memmove` Write Segment (`+0x3c4 → +0x474 / +0x3fc`) -/

theorem insertKey_from_964 (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image)
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (bs : List (BitVec 8))
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hbs : MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs)
    (hlen_lt : chc.messageKeys.length < mkCap1.toNat)
    (hcap1_lt : mkCap1.toNat * 104 < 2 ^ 63)
    (hptr1_ne : mkPtr1 ≠ 0#64)
    (s0 sM : State)
    (hpcM : sM.pc = (SP img.base F alloc).fnAddr cmkSym + 972#64)
    (hrunM : sM.status = .Running)
    (hspM : sM.sp = s0.sp - 480#64)
    (hsp_alignM : sM.spAligned = true)
    (hx29M : sM.readReg64 .x29 = s0.sp - 96#64)
    (htraceM : sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0)
    (hx19M : sM.readReg64 .x19 = 1#64)
    (hx20M : sM.readReg64 .x20 = seedPtr)
    (hx21M : sM.readReg64 .x21 = x.ckA)
    (hx22M : sM.readReg64 .x22 = x.theirA)
    (hx23M : sM.readReg64 .x23 = x.self)
    (hx24M : sM.readReg64 .x24 = mkPtr1)
    (hx25M : sM.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx26M : sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length)
    (hx27M : sM.readReg64 .x27 = s0.sp - 224#64)
    (hx28M : sM.readReg64 .x28 = ckc.index.zeroExtend 64) :
    SepWP (SP img.base F alloc)
      (if chc.messageKeys.length < 2000 then
        (SP img.base F alloc).fnAddr cmkSym + 1140#64
      else
        (SP img.base F alloc).fnAddr cmkSym + 1020#64)
      sM
      (insertKeyActiveMid F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs)
      (fun sB P_f =>
        sB.sp = s0.sp - 480#64 ∧ sB.spAligned = true ∧
        sB.readReg64 .x29 = s0.sp - 96#64 ∧
        (sB.trace = s0.trace ∧ calleeSavedVRegs sB = calleeSavedVRegs s0) ∧
        AdvanceChainKeyRegs x s0 sB ∧
        sB.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        sB.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sB.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        (P_f ⊢ insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64))) := by
  rcases htraceM with ⟨htraceM, hvregsM⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  cmk_fetches_range img.base (Rust.withPanics (sessionExterns F alloc)) hfn 243 255
  generalize_entry (SP img.base F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hlen_lt_zip : (cg.keys.zip chc.messageKeys).length < mkCap1.toNat := by
    rw [hzip_len]; exact hlen_lt
  unfold insertKeyActiveMid vecHeader
  apply SepWP.fold (memRegion_104_entails_messageKey_words mkPtr1) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8
  apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10
  apply SepWP.exists_elim; intro w11
  apply SepWP.exists_elim; intro w12
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  by_cases hlt2000 : chc.messageKeys.length < 2000
  · simp only [hlt2000, ↓reduceIte]
    have hls : (BitVec.ofNat 64 chc.messageKeys.length).ule 1999#64 = true :=
      mkLen_ule_1999_eq_true hlt2000
    wp_steps
    rw [add_one_ofNat_64 chc.messageKeys.length, hspM]
    apply SepWP.fold (messageKeyAt_newMsgKeyGhost_intro F A ckc seedPtr mkPtr1) (by sep_focus)
    rw [← hzip_len]
    apply SepWP.fold
      (vecBuf_messageKeyAt_of_insert0 A mkCap1 mkPtr1 (newMsgKeyGhost seedPtr, ckc.messageKeys F)
        hbs hlen_lt_zip hcap1_lt hptr1_ne)
      (by sep_focus)
    rw [hzip_len]
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_alignM,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩, ?_,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], ?_⟩
    · unfold AdvanceChainKeyRegs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    · unfold insertKeyActivePost vecHeader
      rw [hhdr56, hhdr64]
      exact Entails.of_eq (by ac_rfl)
  · simp only [hlt2000, ↓reduceIte]
    have hnot_lt : ¬ chc.messageKeys.length < 2000 := hlt2000
    have hls : (BitVec.ofNat 64 chc.messageKeys.length).ule 1999#64 = false := by
      rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      change ¬ chc.messageKeys.length ≤ 1999
      omega
    wp_steps
    rw [add_one_ofNat_64 chc.messageKeys.length, hspM]
    apply SepWP.fold (messageKeyAt_newMsgKeyGhost_intro F A ckc seedPtr mkPtr1) (by sep_focus)
    rw [← hzip_len]
    apply SepWP.fold
      (vecBuf_messageKeyAt_of_insert0 A mkCap1 mkPtr1 (newMsgKeyGhost seedPtr, ckc.messageKeys F)
        hbs hlen_lt_zip hcap1_lt hptr1_ne)
      (by sep_focus)
    rw [hzip_len]
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_alignM,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩, ?_,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], ?_⟩
    · unfold AdvanceChainKeyRegs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    · unfold insertKeyActivePost vecHeader
      rw [hhdr56, hhdr64]
      exact Entails.of_eq (by ac_rfl)

/-! ## `memmove` Shift Segment (`+0x3b8 → +0x3cc`) -/

private def sessionMemmoveSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) where
  pre := (libcMemmoveSpec hookStack).pre
  post := fun (base, buf, dst, src, len) s0 sf =>
    ⌜sf.readReg64 .x0 = base + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
    (base ↦ₛ listMove buf dst src len) ∗
    stackAt s0.sp hookStack

private theorem hookSessionMemmove_ok (hookStack : Nat := 4096) :
    HookOk hookMemmove (sessionMemmoveSpec hookStack) := by
  refine HookOk.of_trace (hookMemmove_ok hookStack) fun _ _ _ ht hpost => ?_
  simp only [libcMemmoveSpec, sessionMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht⟩, hpost.2⟩

private theorem session_memmove_ok_at {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "memmove"))
    (stackSize : Nat := 4096) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveSpec stackSize) :=
  hook_ok_at hfn hk (by decide) (ls_hook% "memmove")
    (by simp [Rust.isPanicSymbol])
    ⟨hookMemmove, rfl, hookSessionMemmove_ok (hookStack := stackSize)⟩

theorem insertKey_memmove_952 (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image)
    (_himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (bs slotBs : List (BitVec 8))
    (hmax : chc.messageKeys.length ≤ 2000)
    (hbs_len : bs.length = chc.messageKeys.length * 104)
    (hslot_len : slotBs.length = 104)
    (s0 sK : State)
    (hpcK : sK.pc = (SP img.base F alloc).fnAddr cmkSym + 952#64)
    (hrunK : sK.status = .Running)
    (hspK : sK.sp = s0.sp - 480#64)
    (hsp_alignK : sK.spAligned = true)
    (hx29K : sK.readReg64 .x29 = s0.sp - 96#64)
    (htraceK : sK.trace = s0.trace ∧ calleeSavedVRegs sK = calleeSavedVRegs s0)
    (hx19K : sK.readReg64 .x19 = 1#64)
    (hx20K : sK.readReg64 .x20 = seedPtr)
    (hx21K : sK.readReg64 .x21 = x.ckA)
    (hx22K : sK.readReg64 .x22 = x.theirA)
    (hx23K : sK.readReg64 .x23 = x.self)
    (hx24K : sK.readReg64 .x24 = mkPtr1)
    (hx25K : sK.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx26K : sK.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length)
    (hx27K : sK.readReg64 .x27 = s0.sp - 224#64)
    (hx28K : sK.readReg64 .x28 = ckc.index.zeroExtend 64) :
    SepWP (SP img.base F alloc) ((SP img.base F alloc).fnAddr cmkSym + 972#64) sK
      (vecHeader (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 chc.messageKeys.length) ∗
        A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
        (mkPtr1 ↦ₛ (bs ++ slotBs)) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 ((chc.messageKeys.length + 1) * 104))
          ((mkCap1.toNat - (chc.messageKeys.length + 1)) * 104) ∗
        messageKeyHeaps A (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt sK.sp 7712 ∗
        A.pool)
      (fun sM P_f =>
        sM.pc = (SP img.base F alloc).fnAddr cmkSym + 972#64 ∧
        sM.status = .Running ∧
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x24 = mkPtr1 ∧
        sM.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        (P_f ⊢ insertKeyActiveMid F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs)) := by
  rcases htraceK with ⟨htraceK, hvregsK⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hmemmove := session_memmove_ok_at (b := img.base) (F := F) (alloc := alloc) hfn (k := num% (ls_off% "memmove" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide)
  cmk_fetches_range img.base (Rust.withPanics (sessionExterns F alloc)) hfn 238 243
  generalize_entry (SP img.base F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  have hsp_and : ((s0.sp - 480#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hspK] using hsp_alignK
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa using hsp_and
  have hmadd : (BitVec.ofNat 64 chc.messageKeys.length * 104#64).toNat =
      chc.messageKeys.length * 104 := madd_104_toNat hmax
  have hbound1 : 104 + chc.messageKeys.length * 104 ≤ (bs ++ slotBs).length := by
    rw [List.length_append, hbs_len, hslot_len]; omega
  have hbound2 : 0 + chc.messageKeys.length * 104 ≤ (bs ++ slotBs).length := by
    rw [List.length_append, hbs_len, hslot_len]; omega
  rw [hspK, stackAt_7712_eq_4096 (s0.sp - 480#64)]
  wp_steps
  wp_call hmemmove (mkPtr1, bs ++ slotBs, 104, 0, chc.messageKeys.length * 104)
  apply SepWP.fold (pointsToBytes_listMove_insert0 mkPtr1 hbs_len hslot_len) (by sep_focus)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned, hsp_sf, hspK] using hsp_alignK,
     by simp only [wp_norm, arm64_norm, *],
     ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_⟩
  rw [hsp_sf, hspK]
  unfold insertKeyActiveMid
  rw [stackAt_7712_eq_4096 (s0.sp - 480#64)]
  have hsp_sub : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  rw [hsp_sub]
  exact Entails.of_eq (by ac_rfl)

/-! ## Capacity Check and Optional `grow_one` (`+0x394 → +0x3cc`) -/

private theorem insertKey_to_972_grow (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hgrow_ok : GrowOneOk img F alloc A)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (F_rest R : SepProp) (s0 sA : State)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hfull : chc.messageKeys.length = cg.mkCap.toNat)
    (hpc : sA.pc = (SP img.base F alloc).fnAddr cmkSym + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hfl : img.FrozenLoaded sA)
    (hsym : sA.symtab = img.symtab)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp (SP img.base F alloc) ((SP img.base F alloc).fnAddr cmkSym + 972#64) sA
      (insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ mkCap1 mkPtr1 bs,
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F_rest ∗ R)) → (sf.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 sf ∗ R)) := by
  intro chainPtr
  rcases htrace with ⟨htrace, hvregs⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hgrow := grow_one_ok_at_cmk himg hgrow_ok
  have hmm_fn := insertKey_memmove_952 F A alloc img himg x Gc ckc ci chc cg
  cmk_fetches_range img.base (Rust.withPanics (sessionExterns F alloc)) hfn 229 238
  cmk_fetches_range img.base (Rust.withPanics (sessionExterns F alloc)) hfn 306 311
  generalize_entry (SP img.base F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hmadd_ci : Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = chainPtr :=
    madd_chainPtr_eq Gc.chainsPtr ci
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  unfold insertKeyActivePre
  apply SepWPp.fold (vecBuf_messageKeyAt_bounds A cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) (by sep_focus)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, _, hptr_ne⟩ => ?_
  have hbeq_cap : (BitVec.ofNat 64 chc.messageKeys.length == cg.mkCap) = true := by
    rw [mkLen_eq_mkCap_of_eq hfull, beq_self_eq_true]
  have hfull_zip : (cg.keys.zip chc.messageKeys).length = cg.mkCap.toNat := by
    rw [hzip_len]; exact hfull
  apply SepWPp.fold
    (vecBuf_messageKeyAt_full_entails_grow_one A cg.mkCap cg.mkPtr
      (cg.keys.zip chc.messageKeys) hfull_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs_grow
  refine SepWPp.pure_elim fun ⟨hbs_grow, hbs_grow_len⟩ => ?_
  refine SepWPp.pure_elim fun ⟨_, _⟩ => ?_
  unfold vecHeader
  rw [hhdr56, hhdr64, stackAt_7712_eq_grow sA.sp]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hfl1 hsym1
  have hnew_lt : max (2 * cg.mkCap.toNat) 4 * 104 < 2 ^ 63 := by
    change chc.messageKeys.length ≤ 2000 at hmax
    omega
  have hnew_bound : max (2 * cg.mkCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
  refine SepWPp.call_growOne hgrow (chainPtr + 48#64, cg.mkCap, cg.mkPtr, bs_grow)
    hfl1 hsym1 rfl hrun (by simpa [State.spAligned] using hsp_align)
    (F_frame := ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length) ∗
      messageKeyHeaps A (cg.keys.zip chc.messageKeys) ∗
      vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
      memRegion (sA.sp - 7712#64) 3104)
    ?_
    (fun sf _ hm => growOne_panic_entails_cmkPanic F A img x _ _ F_rest R hm htrace) ?_
  · unfold growOneSpec
    dsimp only
    rw [hhdr56, hbs_grow_len, sepConj_assoc]
    apply Entails.pure_right ⟨rfl, rfl, hptr_ne, hnew_bound⟩
    by_cases hcap0 : cg.mkCap = 0
    · simp only [hcap0, ↓reduceIte]
      exact Entails.of_eq (by ac_rfl)
    · simp only [hcap0, ↓reduceIte, sepConj_pure_left_comm, sepConj_assoc]
      apply Entails.pure_left; intro _
      exact Entails.of_eq (by ac_rfl)
  intro sf_g hpc_g hsp_g hrun_g hsp_align_g hcs_g hfl_g hsym_g
  change sf_g.pc = entry + bv% (1232) at hpc_g
  have hx19_g : sf_g.readReg64 .x19 = 1#64 := (hcs_g.1).trans hx19
  have hx20_g : sf_g.readReg64 .x20 = seedPtr := (hcs_g.2.1).trans hx20
  have hx21_g : sf_g.readReg64 .x21 = x.ckA := (hcs_g.2.2.1).trans hx21
  have hx22_g : sf_g.readReg64 .x22 = x.theirA := hcs_g.2.2.2.1
  have hx23_g : sf_g.readReg64 .x23 = x.self := (hcs_g.2.2.2.2.1).trans hx23
  have hx25_g : sf_g.readReg64 .x25 = chainPtr := hcs_g.2.2.2.2.2.2.1
  have hx26_g : sf_g.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length :=
    (hcs_g.2.2.2.2.2.2.2.1).trans (mkLen_eq_mkCap_of_eq hfull).symm
  have hx27_g : sf_g.readReg64 .x27 = s0.sp - 224#64 := (hcs_g.2.2.2.2.2.2.2.2.1).trans hx27
  have hx28_g : sf_g.readReg64 .x28 = ckc.index.zeroExtend 64 := (hcs_g.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hx29_g : sf_g.readReg64 .x29 = s0.sp - 96#64 := (hcs_g.2.2.2.2.2.2.2.2.2.2.1).trans hx29
  have hvregs_g : calleeSavedVRegs sf_g = calleeSavedVRegs s0 := (hcs_g.2.2.2.2.2.2.2.2.2.2.2).trans hvregs
  unfold growOneSpec
  dsimp only
  rw [← hsp_g]
  change sf_g.sp = sA.sp at hsp_g
  rw [hsp_g]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_g => ?_
  have htrace_g : sf_g.trace = s0.trace := htr_g.trans htrace
  apply SepWPp.exists_elim; intro mkPtr1
  refine SepWPp.pure_elim fun hptr1_ne => ?_
  set mkCap1 := BitVec.ofNat 64 (max (2 * cg.mkCap.toNat) 4)
  obtain ⟨_, _, hlen_lt1_zip, hcap1_lt⟩ := grow_one_newCap_props hfull_zip hnew_lt
  have hlen_lt1 : chc.messageKeys.length < mkCap1.toNat := by
    rwa [hzip_len] at hlen_lt1_zip
  rw [hhdr56, hbs_grow_len]
  apply SepWPp.fold (Entails.of_eq (stackAt_7712_eq_grow sA.sp).symm) (by sep_focus)
  apply SepWPp.fold
    (vecBuf_messageKeyAt_of_grow_one A cg.mkCap mkPtr1 hfull_zip hbs_grow hptr1_ne hnew_lt)
    (by sep_focus)
  clear hfull hfull_zip hbeq_cap hbs_grow hbs_grow_len hcs_g hfl1 hsym1 htr_g
  apply SepWPp.fold
    (vecBuf_messageKeyAt_expose_for_insert0 A mkCap1 mkPtr1
      (cg.keys.zip chc.messageKeys) hlen_lt1_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro slotBs
  refine SepWPp.pure_elim fun ⟨hbs, hbs_len, hslot_len, _, _⟩ => ?_
  rw [hzip_len] at hbs_len ⊢
  have hhdr_fold :
      (((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
        ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length)) =
      vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 chc.messageKeys.length) := by
    unfold vecHeader; rw [hhdr56, hhdr64]
  apply SepWPp.of_sepWP_ret
  by_cases hlen0 : chc.messageKeys.length = 0
  · have hx26_zero : sf_g.readReg64 .x26 = 0#64 := by simp [hx26_g, hlen0]
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.fold (pointsToBytes_insert0_zero mkPtr1 (bs := bs) (by omega) hslot_len) (by sep_focus)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_align_g,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       mkCap1, mkPtr1, bs, by simp only [wp_norm, arm64_norm, *], hbs, hlen_lt1, hcap1_lt, hptr1_ne, ?_⟩
    rw [← hsp_g]
    unfold insertKeyActiveMid
    exact Entails.of_eq (by ac_rfl)
  · have hcbnz : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      exact hlen0 ht
    apply SepWP.of_sepWP_inv hfl_g hsym_g (mid := entry + bv% (952))
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro _ _
    rw [← hsp_g]
    rw [show (stackAt sf_g.sp 7712 ∗ A.pool ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      (vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗ stackAt sf_g.sp 7712 ∗ A.pool) by ac_rfl]
    refine SepWP.mono (hmm_fn mkCap1 mkPtr1 seedPtr bs slotBs hmax hbs_len hslot_len s0 _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simpa [State.spAligned] using hsp_align_g
    · simp only [wp_norm, arm64_norm, *]
    · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; try rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · intro sM P_f _ _ ⟨_, _, hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M,
        hx24M, hx25M, hx26M, hx27M, hx28M, himp⟩
      exact ⟨hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M,
        hx27M, hx28M, mkCap1, mkPtr1, bs, hx24M, hbs, hlen_lt1, hcap1_lt, hptr1_ne, himp⟩

private theorem insertKey_to_972_nogrow (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (F_rest R : SepProp) (s0 sA : State)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hnotfull : chc.messageKeys.length ≠ cg.mkCap.toNat)
    (hpc : sA.pc = (SP img.base F alloc).fnAddr cmkSym + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hfl : img.FrozenLoaded sA)
    (hsym : sA.symtab = img.symtab)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp (SP img.base F alloc) ((SP img.base F alloc).fnAddr cmkSym + 972#64) sA
      (insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ mkCap1 mkPtr1 bs,
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F_rest ∗ R)) → (sf.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 sf ∗ R)) := by
  intro chainPtr
  rcases htrace with ⟨htrace, hvregs⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  have hmm_fn := insertKey_memmove_952 F A alloc img himg x Gc ckc ci chc cg
  cmk_fetches_range img.base (Rust.withPanics (sessionExterns F alloc)) hfn 229 238
  generalize_entry (SP img.base F alloc).fnAddr cmkSym = entry
  examples_hide_fetches
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hmadd_ci : Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = chainPtr :=
    madd_chainPtr_eq Gc.chainsPtr ci
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  unfold insertKeyActivePre
  apply SepWPp.fold (vecBuf_messageKeyAt_bounds A cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) (by sep_focus)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hlen_le_cap, hcap_lt, hptr_ne⟩ => ?_
  rw [hzip_len] at hlen_le_cap
  have hlen_lt : chc.messageKeys.length < cg.mkCap.toNat := by omega
  have hlen_lt_zip : (cg.keys.zip chc.messageKeys).length < cg.mkCap.toNat := by
    rw [hzip_len]; exact hlen_lt
  have hbeq_cap : (BitVec.ofNat 64 chc.messageKeys.length == cg.mkCap) = false :=
    mkLen_beq_mkCap_false hlen_lt
  apply SepWPp.fold
    (vecBuf_messageKeyAt_expose_for_insert0 A cg.mkCap cg.mkPtr
      (cg.keys.zip chc.messageKeys) hlen_lt_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro slotBs
  refine SepWPp.pure_elim fun ⟨hbs, hbs_len, hslot_len, _, _⟩ => ?_
  rw [hzip_len] at hbs_len ⊢
  unfold vecHeader
  rw [hhdr56, hhdr64]
  simp only [sepConj_assoc]
  have hhdr_fold :
      (((chainPtr + 48#64) ↦₆₄ cg.mkCap) ∗
        ((chainPtr + 56#64) ↦₆₄ cg.mkPtr) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length)) =
      vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) := by
    unfold vecHeader; rw [hhdr56, hhdr64]
  apply SepWPp.of_sepWP_ret
  by_cases hlen0 : chc.messageKeys.length = 0
  · have hx26_zero : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = true := by simp [hlen0]
    simp only [hlen0] at hbeq_cap
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.fold (pointsToBytes_insert0_zero cg.mkPtr (bs := bs) (by omega) hslot_len) (by sep_focus)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_align,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       cg.mkCap, cg.mkPtr, bs, by simp only [wp_norm, arm64_norm, *], hbs, hlen_lt, hcap_lt, hptr_ne, ?_⟩
    unfold insertKeyActiveMid
    exact Entails.of_eq (by ac_rfl)
  · have hcbz : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      exact hlen0 ht
    apply SepWP.of_sepWP_inv hfl hsym (mid := entry + bv% (952))
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro _ _
    refine SepWP.mono (hmm_fn cg.mkCap cg.mkPtr seedPtr bs slotBs hmax hbs_len hslot_len s0 _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simpa [State.spAligned] using hsp_align
    · simp only [wp_norm, arm64_norm, *]
    · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; try rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · intro sM P_f _ _ ⟨_, _, hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M,
        hx24M, hx25M, hx26M, hx27M, hx28M, himp⟩
      exact ⟨hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M,
        hx27M, hx28M, cg.mkCap, cg.mkPtr, bs, hx24M, hbs, hlen_lt, hcap_lt, hptr_ne, himp⟩

theorem insertKey_to_972 (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hgrow_ok : GrowOneOk img F alloc A)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (F_rest R : SepProp) (s0 sA : State)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hpc : sA.pc = (SP img.base F alloc).fnAddr cmkSym + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hfl : img.FrozenLoaded sA)
    (hsym : sA.symtab = img.symtab)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp (SP img.base F alloc) ((SP img.base F alloc).fnAddr cmkSym + 972#64) sA
      (insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ mkCap1 mkPtr1 bs,
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F_rest ∗ R)) → (sf.mem ⊨ (consumeMessageKeySpec F A img).onPanic x s0 sf ∗ R)) := by
  by_cases hfull : chc.messageKeys.length = cg.mkCap.toNat
  · exact insertKey_to_972_grow F A alloc img himg hgrow_ok x Gc ckc ci chc cg seedPtr F_rest R s0 sA
      hmax hklen hfull hpc hrun hsp hsp_align hx29 htrace hfl hsym
      hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28
  · exact insertKey_to_972_nogrow F A alloc img himg x Gc ckc ci chc cg seedPtr F_rest R s0 sA
      hmax hklen hfull hpc hrun hsp hsp_align hx29 htrace hfl hsym
      hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28

/-! ## Top-Level `InsertKeySpec` Proof -/

theorem insertKey_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    InsertKeySpec F A alloc img := by
  intro himg hgrow_ok x Gc stc ckc ci chc seedPtr R s0 sA hchc hstate hL
  rcases hstate with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hfl, hsym, hvregs⟩,
    ⟨hx1, hx19, hx20, hx21, hx23, hx25, hx26, hx27, hx28⟩, _hseed_ne, hmem⟩
  have hci_st : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
  have hlen_mem := Satisfies.mono (sepConj_mono_left
    (insertKeyState_chains_len F A img x Gc stc ckc seedPtr s0)) hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hlen_mem
  have hchains_len : Gc.chains.length = stc.receiverChains.length := hlen_mem.1
  have hci_g : ci < Gc.chains.length := by omega
  have hsplit := Satisfies.mono (sepConj_mono_left
    (insertKeyState_split_active F A img x Gc stc ckc ci chc seedPtr s0 hchc hci_g)) hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsplit
  rcases hsplit with ⟨⟨hsrk, hmax, hklen⟩, hmem_act⟩
  rw [← hsp] at hmem_act
  generalize hcg_eq' : Gc.chains[ci] = cg at hsrk hklen hmem_act
  have hcg_eq : cg = Gc.chains[ci] := hcg_eq'.symm
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set F_rest := insertKeyFrame A img x Gc stc ckc ci chc cg s0
  have hmem_framed : sA.mem ⊨ insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp ∗ (F_rest ∗ R) := by
    simpa only [sepConj_assoc] using hmem_act
  clear hmem hlen_mem hmem_act
  rw [sessionProg_eq_SP himg F alloc] at hL ⊢
  rw [cmkInsertKeyPC_eq_fnAddr himg F alloc] at hpc
  have hwp_to_972 := insertKey_to_972 F A alloc img himg hgrow_ok x Gc ckc ci chc cg seedPtr
    F_rest R s0 sA hmax hklen hpc hrun hsp hsp_align hx29 ⟨htrace, hvregs⟩ hfl hsym
    hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28
  obtain ⟨sM, hsteps1, ⟨hpcM, hrunM, hflM, hsymM, P_m, hmm,
      hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M, hx27M, hx28M,
      mkCap1, mkPtr1, bs, hx24M, hbs, hlen_lt1, hcap1_lt, hptr1_ne, himpM⟩ | ⟨hpanM, P_p, hmp, hqp⟩⟩ :=
    steps_of_sepWPp hfl hsym hmem_framed hL hwp_to_972
  ·
    have hmm_mid : sM.mem ⊨ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs ∗ (F_rest ∗ R) :=
      Satisfies.mono (sepConj_mono_left himpM) hmm
    have hLM := hsteps1.codeLoaded hL
    have hwp2 := insertKey_from_964 F A alloc img himg x Gc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr bs hklen hbs hlen_lt1 hcap1_lt hptr1_ne s0 sM
      hpcM hrunM hspM halignM hx29M htrM hx19M hx20M hx21M hx22M hx23M hx24M hx25M hx26M hx27M hx28M
    obtain ⟨sB, hsteps2, hpcB, hrunB, hflB, hsymB, _, Pf, hmfB,
        hspB, halignB, hx29B, htrB, hregsD, hx25B, hx26B, hx28B, himpB⟩ :=
      sepWP_elim_inv hflM hsymM hmm_mid hLM hwp2
    have hmf_post : sB.mem ⊨ (insertKeyActivePost F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗ F_rest) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left himpB) hmfB
    have hpartC_eq := cmkEvictOldestKeyPC_eq_fnAddr himg F alloc
    have hpartD_eq := cmkAdvanceChainKeyPC_eq_fnAddr himg F alloc
    by_cases hlt2000 : chc.messageKeys.length < 2000
    · simp only [hlt2000, ↓reduceIte] at hpcB
      let cg' : ChainGhost :=
        { cg with
          mkCap := mkCap1
          mkPtr := mkPtr1
          keys := newMsgKeyGhost seedPtr :: cg.keys }
      have hG_agree : Gc.AgreeExcept (Gc.setChain ci cg') (some ci) :=
        RatchetGhost.AgreeExcept.setChain Gc hci_g cg'
          (by simp [cg', hcg_eq]) (by simp [cg', hcg_eq])
      have hmemD : sB.mem ⊨ cmkLoopHeap A img x (Gc.setChain ci cg')
          (updatedRatchetState F stc ci chc ckc) ckc s0 ∗ R :=
        Satisfies.mono (sepConj_mono_left
          (insertKeyPost_entails_cmkLoopHeap_D F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0
            hci_st hsrk hklen hlt2000)) hmf_post
      refine ⟨sB, hsteps1.trans hsteps2, Or.inl ⟨Gc.setChain ci cg', hG_agree, ?_⟩⟩
      exact ⟨hpartD_eq.symm ▸ hpcB, ⟨hrunB, hspB, hsp0_align, halignB, hx29B, htrB.1, hflB, hsymB, htrB.2⟩,
        hregsD, hmemD⟩
    · simp only [hlt2000, ↓reduceIte] at hpcB
      have hlen2000 : chc.messageKeys.length = 2000 := by
        change chc.messageKeys.length ≤ 2000 at hmax
        omega
      have hklen2000 : cg.keys.length = 2000 := by omega
      have hcap2001 : 2001 ≤ mkCap1.toNat := by omega
      have hmemC : sB.mem ⊨ evictOldestKeyHeap F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ∗ R :=
        Satisfies.mono (sepConj_mono_left
          (insertKeyPost_entails_evictOldestKeyHeap F A img x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 hlen2000)) hmf_post
      have hregsC : EvictOldestKeyRegs x Gc ckc ci mkPtr1 sB := by
        rcases hregsD with ⟨hx19B, hx21B, hx22B, hx23B, _⟩
        rw [hlen2000] at hx26B
        exact ⟨hx19B, hx21B, hx22B, hx23B, hx25B, hx26B, hx28B⟩
      refine ⟨sB, hsteps1.trans hsteps2, Or.inr (Or.inl ⟨cg, mkCap1, mkPtr1, ?_⟩)⟩
      exact ⟨hpartC_eq.symm ▸ hpcB, ⟨hrunB, hspB, hsp0_align, halignB, hx29B, htrB.1, hflB, hsymB, htrB.2⟩,
        hregsC, ⟨hci_g, hcg_eq⟩, hsrk, hlen2000, hklen2000, hcap2001, hcap1_lt, hptr1_ne, hmemC⟩
  · exact ⟨sM, hsteps1, Or.inr (Or.inr ⟨hpanM, hqp hmp⟩)⟩

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block 24) -/

private theorem SepWPp.call_growOne_placed [LibsignalPlacement] {prog : Program}
    {entry ret : BitVec 64} {A : RustAlloc}
    (hsub : subroutine_ok prog entry (withLsCodeLoaded lsmpl (growOneSpec A)))
    (x : GrowGhost) {s : State} {P F_frame : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hpre : P ⊢ (growOneSpec A).pre x s ∗ F_frame)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf ((growOneSpec A).onPanic x s sf ∗ F_frame))
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf ((growOneSpec A).post x s sf ∗ F_frame) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm1 : s.mem ⊨ ((growOneSpec A).pre x s ∗ F_frame) ∗ R :=
    Satisfies.mono (sepConj_mono_left hpre) hm
  have hm2 : s.mem ⊨ (withLsCodeLoaded lsmpl (growOneSpec A)).pre x s ∗ (F_frame ∗ R) :=
    introduce_withLsCodeLoaded hcl (by simpa only [sepConj_assoc] using hm1)
  obtain ⟨sm, hsteps1, hout, -⟩ := hsub.no_fault_before_outcome x (F_frame ∗ R) s hpc hrun hm2 hsp hL
  rcases hout with ⟨⟨hpcm, hspm, hrunm⟩, ⟨_, hcsm⟩, hpostm⟩ | ⟨hpanm, hpan_mem⟩ | ⟨_, _, hundef_mem⟩ | ⟨_, hoom⟩
  · have hsp_alignm : sm.spAligned = true := by
      simpa [State.spAligned, hspm] using hsp
    have hclm : LibsignalCodeLoaded lsmpl sm.mem := hcl.of_keepsFrozen hsteps1.keepsFrozen
    have hpostm' : sm.mem ⊨ ((growOneSpec A).post x s sm ∗ F_frame) ∗ R := by
      simpa only [withLsCodeLoaded, sepConj_assoc] using hpostm
    obtain ⟨sf, hsteps2, hout2⟩ :=
      hcont sm hpcm hspm hrunm hsp_alignm hcsm hclm R hpostm' (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · have hpan_mem' : sm.mem ⊨ ((growOneSpec A).onPanic x s sm ∗ F_frame) ∗ R := by
      simpa only [withLsCodeLoaded, sepConj_assoc] using hpan_mem
    exact ⟨sm, hsteps1, Or.inr (Or.inl ⟨hpanm, (growOneSpec A).onPanic x s sm ∗ F_frame, hpan_mem', hpanic sm hpanm⟩)⟩
  · exfalso
    unfold withLsCodeLoaded growOneSpec at hundef_mem
    dsimp only at hundef_mem
    rw [satisfies_pure_sepConj] at hundef_mem
    exact hundef_mem.1
  · exact (not_satisfies_false_sepConj hoom).elim

theorem insertKey_from_964_placed [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (bs : List (BitVec 8))
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hbs : MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs)
    (hlen_lt : chc.messageKeys.length < mkCap1.toNat)
    (hcap1_lt : mkCap1.toNat * 104 < 2 ^ 63)
    (hptr1_ne : mkPtr1 ≠ 0#64)
    (s0 sM : State)
    (hpcM : sM.pc = (blkPl_24).base + 972#64)
    (hrunM : sM.status = .Running)
    (hspM : sM.sp = s0.sp - 480#64)
    (hsp_alignM : sM.spAligned = true)
    (hx29M : sM.readReg64 .x29 = s0.sp - 96#64)
    (htraceM : sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0)
    (hx19M : sM.readReg64 .x19 = 1#64)
    (hx20M : sM.readReg64 .x20 = seedPtr)
    (hx21M : sM.readReg64 .x21 = x.ckA)
    (hx22M : sM.readReg64 .x22 = x.theirA)
    (hx23M : sM.readReg64 .x23 = x.self)
    (hx24M : sM.readReg64 .x24 = mkPtr1)
    (hx25M : sM.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx26M : sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length)
    (hx27M : sM.readReg64 .x27 = s0.sp - 224#64)
    (hx28M : sM.readReg64 .x28 = ckc.index.zeroExtend 64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H)
      (if chc.messageKeys.length < 2000 then
        (blkPl_24).base + 1140#64
      else
        (blkPl_24).base + 1020#64)
      sM
      (insertKeyActiveMid F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs)
      (fun sB P_f =>
        sB.sp = s0.sp - 480#64 ∧ sB.spAligned = true ∧
        sB.readReg64 .x29 = s0.sp - 96#64 ∧
        (sB.trace = s0.trace ∧ calleeSavedVRegs sB = calleeSavedVRegs s0) ∧
        AdvanceChainKeyRegs x s0 sB ∧
        sB.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        sB.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sB.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        (P_f ⊢ insertKeyActivePost F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64))) := by
  rcases htraceM with ⟨htraceM, hvregsM⟩
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hlen_lt_zip : (cg.keys.zip chc.messageKeys).length < mkCap1.toNat := by
    rw [hzip_len]; exact hlen_lt
  unfold insertKeyActiveMid vecHeader
  apply SepWP.fold (memRegion_104_entails_messageKey_words mkPtr1) (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro w7
  apply SepWP.exists_elim; intro w8
  apply SepWP.exists_elim; intro w9
  apply SepWP.exists_elim; intro w10
  apply SepWP.exists_elim; intro w11
  apply SepWP.exists_elim; intro w12
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  by_cases hlt2000 : chc.messageKeys.length < 2000
  · simp only [hlt2000, ↓reduceIte]
    have hls : (BitVec.ofNat 64 chc.messageKeys.length).ule 1999#64 = true :=
      mkLen_ule_1999_eq_true hlt2000
    wp_steps
    rw [add_one_ofNat_64 chc.messageKeys.length, hspM]
    apply SepWP.fold (messageKeyAt_newMsgKeyGhost_intro F A ckc seedPtr mkPtr1) (by sep_focus)
    rw [← hzip_len]
    apply SepWP.fold
      (vecBuf_messageKeyAt_of_insert0 A mkCap1 mkPtr1 (newMsgKeyGhost seedPtr, ckc.messageKeys F)
        hbs hlen_lt_zip hcap1_lt hptr1_ne)
      (by sep_focus)
    rw [hzip_len]
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_alignM,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩, ?_,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], ?_⟩
    · unfold AdvanceChainKeyRegs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    · unfold insertKeyActivePost vecHeader
      rw [hhdr56, hhdr64]
      exact Entails.of_eq (by ac_rfl)
  · simp only [hlt2000, ↓reduceIte]
    have hnot_lt : ¬ chc.messageKeys.length < 2000 := hlt2000
    have hls : (BitVec.ofNat 64 chc.messageKeys.length).ule 1999#64 = false := by
      rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      change ¬ chc.messageKeys.length ≤ 1999
      omega
    wp_steps
    rw [add_one_ofNat_64 chc.messageKeys.length, hspM]
    apply SepWP.fold (messageKeyAt_newMsgKeyGhost_intro F A ckc seedPtr mkPtr1) (by sep_focus)
    rw [← hzip_len]
    apply SepWP.fold
      (vecBuf_messageKeyAt_of_insert0 A mkCap1 mkPtr1 (newMsgKeyGhost seedPtr, ckc.messageKeys F)
        hbs hlen_lt_zip hcap1_lt hptr1_ne)
      (by sep_focus)
    rw [hzip_len]
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_alignM,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩, ?_,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], ?_⟩
    · unfold AdvanceChainKeyRegs
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]
    · unfold insertKeyActivePost vecHeader
      rw [hhdr56, hhdr64]
      exact Entails.of_eq (by ac_rfl)

set_option maxRecDepth 200000 in
private theorem session_memmove_placed_ok_at [LibsignalPlacement] {H : String → Option (State → State)}
    (hmm : H "memmove" = some hookMemmove) (stackSize : Nat := 4096) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ "memmove")
      (sessionMemmoveSpec stackSize) :=
  cmk_hook_ok_of_mem ⟨hookMemmove, hmm, hookSessionMemmove_ok (hookStack := stackSize)⟩

theorem insertKey_memmove_952_placed [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost)
    (mkCap1 mkPtr1 seedPtr : BitVec 64)
    (bs slotBs : List (BitVec 8))
    (hmax : chc.messageKeys.length ≤ 2000)
    (hbs_len : bs.length = chc.messageKeys.length * 104)
    (hslot_len : slotBs.length = 104)
    (s0 sK : State)
    (hpcK : sK.pc = (blkPl_24).base + 952#64)
    (hrunK : sK.status = .Running)
    (hspK : sK.sp = s0.sp - 480#64)
    (hsp_alignK : sK.spAligned = true)
    (hx29K : sK.readReg64 .x29 = s0.sp - 96#64)
    (htraceK : sK.trace = s0.trace ∧ calleeSavedVRegs sK = calleeSavedVRegs s0)
    (hx19K : sK.readReg64 .x19 = 1#64)
    (hx20K : sK.readReg64 .x20 = seedPtr)
    (hx21K : sK.readReg64 .x21 = x.ckA)
    (hx22K : sK.readReg64 .x22 = x.theirA)
    (hx23K : sK.readReg64 .x23 = x.self)
    (hx24K : sK.readReg64 .x24 = mkPtr1)
    (hx25K : sK.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx26K : sK.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length)
    (hx27K : sK.readReg64 .x27 = s0.sp - 224#64)
    (hx28K : sK.readReg64 .x28 = ckc.index.zeroExtend 64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sK
      (vecHeader (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 chc.messageKeys.length) ∗
        A.live mkPtr1 (mkCap1.toNat * 104) 8 ∗
        (mkPtr1 ↦ₛ (bs ++ slotBs)) ∗
        memRegion (mkPtr1 + BitVec.ofNat 64 ((chc.messageKeys.length + 1) * 104))
          ((mkCap1.toNat - (chc.messageKeys.length + 1)) * 104) ∗
        messageKeyHeaps A (cg.keys.zip chc.messageKeys) ∗
        vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
        stackAt sK.sp 7712 ∗
        A.pool)
      (fun sM P_f =>
        sM.pc = (blkPl_24).base + 972#64 ∧
        sM.status = .Running ∧
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x24 = mkPtr1 ∧
        sM.readReg64 .x25 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        (P_f ⊢ insertKeyActiveMid F A (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)) mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs)) := by
  rcases htraceK with ⟨htraceK, hvregsK⟩
  have hmemmove := session_memmove_placed_ok_at hmm
  have hsp_and : ((s0.sp - 480#64) &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hspK] using hsp_alignK
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa using hsp_and
  have hmadd : (BitVec.ofNat 64 chc.messageKeys.length * 104#64).toNat =
      chc.messageKeys.length * 104 := madd_104_toNat hmax
  have hbound1 : 104 + chc.messageKeys.length * 104 ≤ (bs ++ slotBs).length := by
    rw [List.length_append, hbs_len, hslot_len]; omega
  have hbound2 : 0 + chc.messageKeys.length * 104 ≤ (bs ++ slotBs).length := by
    rw [List.length_append, hbs_len, hslot_len]; omega
  rw [hspK, stackAt_7712_eq_4096 (s0.sp - 480#64)]
  wp_steps
  wp_call hmemmove (mkPtr1, bs ++ slotBs, 104, 0, chc.messageKeys.length * 104)
  apply SepWP.fold (pointsToBytes_listMove_insert0 mkPtr1 hbs_len hslot_len) (by sep_focus)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned, hsp_sf, hspK] using hsp_alignK,
     by simp only [wp_norm, arm64_norm, *],
     ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], ?_⟩
  rw [hsp_sf, hspK]
  unfold insertKeyActiveMid
  rw [stackAt_7712_eq_4096 (s0.sp - 480#64)]
  have hsp_sub : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  rw [hsp_sub]
  exact Entails.of_eq (by ac_rfl)

private theorem growOne_panic_entails_cmkPanic_placed [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (x : ConsumeMessageKeyGhost) (gx : GrowGhost)
    {s0 s sf : State} (F_frame F_rest R : SepProp)
    (hm : sf.mem ⊨ ((growOneSpec A).onPanic gx s sf ∗ F_frame) ∗ (F_rest ∗ R))
    (htr : s.trace = s0.trace) :
    sf.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sf ∗ R := by
  unfold growOneSpec at hm
  dsimp only at hm
  rw [← sepConj_assoc _ F_rest R, sepConj_assoc _ F_frame F_rest] at hm
  have halloc_eq : allocFailedIn s sf = allocFailedIn s0 sf := by
    simp only [allocFailedIn, htr]
  unfold cmkPlacedSpec withLsCodeLoaded
  dsimp only
  exact allowPanic_frame (fun ⟨ha, hp⟩ => ⟨Or.inr (halloc_eq ▸ ha), htr ▸ hp⟩) hm

private theorem insertKey_to_972_grow_placed [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (hgrow_ok : GrowOnePlacedOk H A)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (F_rest R : SepProp) (s0 sA : State)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hfull : chc.messageKeys.length = cg.mkCap.toNat)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hcl : LibsignalCodeLoaded lsmpl sA.mem)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ mkCap1 mkPtr1 bs,
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F_rest ∗ R)) → (sf.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sf ∗ R)) := by
  intro chainPtr
  rcases htrace with ⟨htrace, hvregs⟩
  have hmm_fn := insertKey_memmove_952_placed F A H hmm x Gc ckc ci chc cg
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hmadd_ci : Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = chainPtr :=
    madd_chainPtr_eq Gc.chainsPtr ci
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  unfold insertKeyActivePre
  apply SepWPp.fold (vecBuf_messageKeyAt_bounds A cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) (by sep_focus)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨_, _, hptr_ne⟩ => ?_
  have hbeq_cap : (BitVec.ofNat 64 chc.messageKeys.length == cg.mkCap) = true := by
    rw [mkLen_eq_mkCap_of_eq hfull, beq_self_eq_true]
  have hfull_zip : (cg.keys.zip chc.messageKeys).length = cg.mkCap.toNat := by
    rw [hzip_len]; exact hfull
  apply SepWPp.fold
    (vecBuf_messageKeyAt_full_entails_grow_one A cg.mkCap cg.mkPtr
      (cg.keys.zip chc.messageKeys) hfull_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs_grow
  refine SepWPp.pure_elim fun ⟨hbs_grow, hbs_grow_len⟩ => ?_
  refine SepWPp.pure_elim fun ⟨_, _⟩ => ?_
  unfold vecHeader
  rw [hhdr56, hhdr64, stackAt_7712_eq_grow sA.sp]
  simp only [sepConj_assoc]
  apply sepWPp_seq_lscl (mid := lsmpl.base 43) hcl
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl1
  have hnew_lt : max (2 * cg.mkCap.toNat) 4 * 104 < 2 ^ 63 := by
    change chc.messageKeys.length ≤ 2000 at hmax
    omega
  have hnew_bound : max (2 * cg.mkCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
  refine SepWPp.call_growOne_placed hgrow_ok (chainPtr + 48#64, cg.mkCap, cg.mkPtr, bs_grow)
    hcl1 rfl hrun (by simpa [State.spAligned] using hsp_align)
    (F_frame := ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length) ∗
      messageKeyHeaps A (cg.keys.zip chc.messageKeys) ∗
      vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗
      memRegion (sA.sp - 7712#64) 3104)
    ?_
    (fun sf _ hm => growOne_panic_entails_cmkPanic_placed F A x _ _ F_rest R hm htrace) ?_
  · unfold growOneSpec
    dsimp only
    rw [hhdr56, hbs_grow_len, sepConj_assoc]
    apply Entails.pure_right ⟨rfl, rfl, hptr_ne, hnew_bound⟩
    by_cases hcap0 : cg.mkCap = 0
    · simp only [hcap0, ↓reduceIte]
      exact Entails.of_eq (by ac_rfl)
    · simp only [hcap0, ↓reduceIte, sepConj_pure_left_comm, sepConj_assoc]
      apply Entails.pure_left; intro _
      exact Entails.of_eq (by ac_rfl)
  intro sf_g hpc_g hsp_g hrun_g hsp_align_g hcs_g _hcl_g
  change sf_g.pc = (blkPl_24).base + bv% (1232) at hpc_g
  have hx19_g : sf_g.readReg64 .x19 = 1#64 := (hcs_g.1).trans hx19
  have hx20_g : sf_g.readReg64 .x20 = seedPtr := (hcs_g.2.1).trans hx20
  have hx21_g : sf_g.readReg64 .x21 = x.ckA := (hcs_g.2.2.1).trans hx21
  have hx22_g : sf_g.readReg64 .x22 = x.theirA := hcs_g.2.2.2.1
  have hx23_g : sf_g.readReg64 .x23 = x.self := (hcs_g.2.2.2.2.1).trans hx23
  have hx25_g : sf_g.readReg64 .x25 = chainPtr := hcs_g.2.2.2.2.2.2.1
  have hx26_g : sf_g.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length :=
    (hcs_g.2.2.2.2.2.2.2.1).trans (mkLen_eq_mkCap_of_eq hfull).symm
  have hx27_g : sf_g.readReg64 .x27 = s0.sp - 224#64 := (hcs_g.2.2.2.2.2.2.2.2.1).trans hx27
  have hx28_g : sf_g.readReg64 .x28 = ckc.index.zeroExtend 64 := (hcs_g.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hx29_g : sf_g.readReg64 .x29 = s0.sp - 96#64 := (hcs_g.2.2.2.2.2.2.2.2.2.2.1).trans hx29
  have hvregs_g : calleeSavedVRegs sf_g = calleeSavedVRegs s0 := (hcs_g.2.2.2.2.2.2.2.2.2.2.2).trans hvregs
  unfold growOneSpec
  dsimp only
  rw [← hsp_g]
  change sf_g.sp = sA.sp at hsp_g
  rw [hsp_g]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_g => ?_
  have htrace_g : sf_g.trace = s0.trace := htr_g.trans htrace
  apply SepWPp.exists_elim; intro mkPtr1
  refine SepWPp.pure_elim fun hptr1_ne => ?_
  set mkCap1 := BitVec.ofNat 64 (max (2 * cg.mkCap.toNat) 4)
  obtain ⟨_, _, hlen_lt1_zip, hcap1_lt⟩ := grow_one_newCap_props hfull_zip hnew_lt
  have hlen_lt1 : chc.messageKeys.length < mkCap1.toNat := by
    rwa [hzip_len] at hlen_lt1_zip
  rw [hhdr56, hbs_grow_len]
  apply SepWPp.fold (Entails.of_eq (stackAt_7712_eq_grow sA.sp).symm) (by sep_focus)
  apply SepWPp.fold
    (vecBuf_messageKeyAt_of_grow_one A cg.mkCap mkPtr1 hfull_zip hbs_grow hptr1_ne hnew_lt)
    (by sep_focus)
  clear hfull hfull_zip hbeq_cap hbs_grow hbs_grow_len hcs_g hcl1 htr_g
  apply SepWPp.fold
    (vecBuf_messageKeyAt_expose_for_insert0 A mkCap1 mkPtr1
      (cg.keys.zip chc.messageKeys) hlen_lt1_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro slotBs
  refine SepWPp.pure_elim fun ⟨hbs, hbs_len, hslot_len, _, _⟩ => ?_
  rw [hzip_len] at hbs_len ⊢
  have hhdr_fold :
      (((chainPtr + 48#64) ↦₆₄ mkCap1) ∗
        ((chainPtr + 56#64) ↦₆₄ mkPtr1) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length)) =
      vecHeader (chainPtr + 48#64) mkCap1 mkPtr1 (BitVec.ofNat 64 chc.messageKeys.length) := by
    unfold vecHeader; rw [hhdr56, hhdr64]
  apply SepWPp.of_sepWP_ret
  by_cases hlen0 : chc.messageKeys.length = 0
  · have hx26_zero : sf_g.readReg64 .x26 = 0#64 := by simp [hx26_g, hlen0]
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.fold (pointsToBytes_insert0_zero mkPtr1 (bs := bs) (by omega) hslot_len) (by sep_focus)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_align_g,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       mkCap1, mkPtr1, bs, by simp only [wp_norm, arm64_norm, *], hbs, hlen_lt1, hcap1_lt, hptr1_ne, ?_⟩
    rw [← hsp_g]
    unfold insertKeyActiveMid
    exact Entails.of_eq (by ac_rfl)
  · have hcbnz : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      exact hlen0 ht
    apply SepWP.cut (mid := (blkPl_24).base + bv% (952))
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    rw [← hsp_g]
    rw [show (stackAt sf_g.sp 7712 ∗ A.pool ∗ vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed) =
      (vecU8Buf A 32#64 seedPtr (ckc.messageKeys F).seed ∗ stackAt sf_g.sp 7712 ∗ A.pool) by ac_rfl]
    refine SepWP.mono (hmm_fn mkCap1 mkPtr1 seedPtr bs slotBs hmax hbs_len hslot_len s0 _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simpa [State.spAligned] using hsp_align_g
    · simp only [wp_norm, arm64_norm, *]
    · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; try rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · intro sM P_f _ _ ⟨_, _, hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M,
        hx24M, hx25M, hx26M, hx27M, hx28M, himp⟩
      exact ⟨hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M,
        hx27M, hx28M, mkCap1, mkPtr1, bs, hx24M, hbs, hlen_lt1, hcap1_lt, hptr1_ne, himp⟩

private theorem insertKey_to_972_nogrow_placed [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (F_rest R : SepProp) (s0 sA : State)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hnotfull : chc.messageKeys.length ≠ cg.mkCap.toNat)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ mkCap1 mkPtr1 bs,
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F_rest ∗ R)) → (sf.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sf ∗ R)) := by
  intro chainPtr
  rcases htrace with ⟨htrace, hvregs⟩
  have hmm_fn := insertKey_memmove_952_placed F A H hmm x Gc ckc ci chc cg
  have hzip_len : (cg.keys.zip chc.messageKeys).length = chc.messageKeys.length := by
    simp [hklen]
  have hmadd_ci : Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = chainPtr :=
    madd_chainPtr_eq Gc.chainsPtr ci
  have hhdr56 : chainPtr + 48#64 + 8#64 = chainPtr + 56#64 := by bv_arith
  have hhdr64 : chainPtr + 48#64 + 16#64 = chainPtr + 64#64 := by bv_arith
  unfold insertKeyActivePre
  apply SepWPp.fold (vecBuf_messageKeyAt_bounds A cg.mkCap cg.mkPtr (cg.keys.zip chc.messageKeys)) (by sep_focus)
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hlen_le_cap, hcap_lt, hptr_ne⟩ => ?_
  rw [hzip_len] at hlen_le_cap
  have hlen_lt : chc.messageKeys.length < cg.mkCap.toNat := by omega
  have hlen_lt_zip : (cg.keys.zip chc.messageKeys).length < cg.mkCap.toNat := by
    rw [hzip_len]; exact hlen_lt
  have hbeq_cap : (BitVec.ofNat 64 chc.messageKeys.length == cg.mkCap) = false :=
    mkLen_beq_mkCap_false hlen_lt
  apply SepWPp.fold
    (vecBuf_messageKeyAt_expose_for_insert0 A cg.mkCap cg.mkPtr
      (cg.keys.zip chc.messageKeys) hlen_lt_zip)
    (by sep_focus)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro bs
  apply SepWPp.exists_elim; intro slotBs
  refine SepWPp.pure_elim fun ⟨hbs, hbs_len, hslot_len, _, _⟩ => ?_
  rw [hzip_len] at hbs_len ⊢
  unfold vecHeader
  rw [hhdr56, hhdr64]
  simp only [sepConj_assoc]
  have hhdr_fold :
      (((chainPtr + 48#64) ↦₆₄ cg.mkCap) ∗
        ((chainPtr + 56#64) ↦₆₄ cg.mkPtr) ∗
        ((chainPtr + 64#64) ↦₆₄ BitVec.ofNat 64 chc.messageKeys.length)) =
      vecHeader (chainPtr + 48#64) cg.mkCap cg.mkPtr (BitVec.ofNat 64 chc.messageKeys.length) := by
    unfold vecHeader; rw [hhdr56, hhdr64]
  apply SepWPp.of_sepWP_ret
  by_cases hlen0 : chc.messageKeys.length = 0
  · have hx26_zero : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = true := by simp [hlen0]
    simp only [hlen0] at hbeq_cap
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.fold (pointsToBytes_insert0_zero cg.mkPtr (bs := bs) (by omega) hslot_len) (by sep_focus)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], by simpa [State.spAligned] using hsp_align,
       by simp only [wp_norm, arm64_norm, *],
       ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       cg.mkCap, cg.mkPtr, bs, by simp only [wp_norm, arm64_norm, *], hbs, hlen_lt, hcap_lt, hptr_ne, ?_⟩
    unfold insertKeyActiveMid
    exact Entails.of_eq (by ac_rfl)
  · have hcbz : (BitVec.ofNat 64 chc.messageKeys.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      exact hlen0 ht
    apply SepWP.cut (mid := (blkPl_24).base + bv% (952))
    wp_steps
    apply SepWP.fold (Entails.of_eq hhdr_fold) (by sep_focus)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine SepWP.mono (hmm_fn cg.mkCap cg.mkPtr seedPtr bs slotBs hmax hbs_len hslot_len s0 _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simpa [State.spAligned] using hsp_align
    · simp only [wp_norm, arm64_norm, *]
    · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]; try rfl
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · simp only [wp_norm, arm64_norm, *]
    · intro sM P_f _ _ ⟨_, _, hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M,
        hx24M, hx25M, hx26M, hx27M, hx28M, himp⟩
      exact ⟨hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M,
        hx27M, hx28M, cg.mkCap, cg.mkPtr, bs, hx24M, hbs, hlen_lt, hcap_lt, hptr_ne, himp⟩

theorem insertKey_to_972_placed [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    (hmm : H "memmove" = some hookMemmove)
    (hgrow_ok : GrowOnePlacedOk H A)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (ckc : CryptoGames.LibsignalSession.ChainKey)
    (ci : Nat) (chc : ReceiverChain) (cg : ChainGhost) (seedPtr : BitVec 64)
    (F_rest R : SepProp) (s0 sA : State)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : cg.keys.length = chc.messageKeys.length)
    (hpc : sA.pc = (blkPl_24).base + 916#64)
    (hrun : sA.status = .Running)
    (hsp : sA.sp = s0.sp - 480#64)
    (hsp_align : sA.spAligned = true)
    (hx29 : sA.readReg64 .x29 = s0.sp - 96#64)
    (htrace : sA.trace = s0.trace ∧ calleeSavedVRegs sA = calleeSavedVRegs s0)
    (hcl : LibsignalCodeLoaded lsmpl sA.mem)
    (hx1 : sA.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx19 : sA.readReg64 .x19 = 1#64)
    (hx20 : sA.readReg64 .x20 = seedPtr)
    (hx21 : sA.readReg64 .x21 = x.ckA)
    (hx23 : sA.readReg64 .x23 = x.self)
    (hx25 : sA.readReg64 .x25 = Gc.chainsPtr)
    (hx26 : sA.readReg64 .x26 = x.theirA)
    (hx27 : sA.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : sA.readReg64 .x28 = ckc.index.zeroExtend 64) :
    let chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 972#64) sA
      (insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp)
      (fun sM P_f =>
        sM.sp = s0.sp - 480#64 ∧ sM.spAligned = true ∧
        sM.readReg64 .x29 = s0.sp - 96#64 ∧
        (sM.trace = s0.trace ∧ calleeSavedVRegs sM = calleeSavedVRegs s0) ∧
        sM.readReg64 .x19 = 1#64 ∧
        sM.readReg64 .x20 = seedPtr ∧
        sM.readReg64 .x21 = x.ckA ∧
        sM.readReg64 .x22 = x.theirA ∧
        sM.readReg64 .x23 = x.self ∧
        sM.readReg64 .x25 = chainPtr ∧
        sM.readReg64 .x26 = BitVec.ofNat 64 chc.messageKeys.length ∧
        sM.readReg64 .x27 = s0.sp - 224#64 ∧
        sM.readReg64 .x28 = ckc.index.zeroExtend 64 ∧
        ∃ mkCap1 mkPtr1 bs,
          sM.readReg64 .x24 = mkPtr1 ∧
          MessageKeyArrayBytes (cg.keys.zip chc.messageKeys) bs ∧
          chc.messageKeys.length < mkCap1.toNat ∧
          mkCap1.toNat * 104 < 2 ^ 63 ∧
          mkPtr1 ≠ 0#64 ∧
          (P_f ⊢ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F_rest ∗ R)) → (sf.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sf ∗ R)) := by
  by_cases hfull : chc.messageKeys.length = cg.mkCap.toNat
  · exact insertKey_to_972_grow_placed F A H hmm hgrow_ok x Gc ckc ci chc cg seedPtr F_rest R s0 sA
      hmax hklen hfull hpc hrun hsp hsp_align hx29 htrace hcl
      hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28
  · exact insertKey_to_972_nogrow_placed F A H hmm x Gc ckc ci chc cg seedPtr F_rest R s0 sA
      hmax hklen hfull hpc hrun hsp hsp_align hx29 htrace
      hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28

theorem insertKey_placed_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    InsertKeyPlacedSpec F A H := by
  intro hmm hgrow_ok x Gc stc ckc ci chc seedPtr R s0 sA hchc hstate hL
  rcases hstate with ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
    ⟨hx1, hx19, hx20, hx21, hx23, hx25, hx26, hx27, hx28⟩, _hseed_ne, hmem⟩
  rw [cmkLoopHeap_placed_eq_at] at hmem
  have hci_st : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
  have hlen_mem := Satisfies.mono (sepConj_mono_left
    (insertKeyStateAt_chains_len F A lsLogFilterAddr x Gc stc ckc seedPtr s0)) hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hlen_mem
  have hchains_len : Gc.chains.length = stc.receiverChains.length := hlen_mem.1
  have hci_g : ci < Gc.chains.length := by omega
  have hsplit := Satisfies.mono (sepConj_mono_left
    (insertKeyStateAt_split_active F A lsLogFilterAddr x Gc stc ckc ci chc seedPtr s0 hchc hci_g)) hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsplit
  rcases hsplit with ⟨⟨hsrk, hmax, hklen⟩, hmem_act⟩
  rw [← hsp] at hmem_act
  generalize hcg_eq' : Gc.chains[ci] = cg at hsrk hklen hmem_act
  have hcg_eq : cg = Gc.chains[ci] := hcg_eq'.symm
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set F_rest := insertKeyFrameAt A lsLogFilterAddr x Gc stc ckc ci chc cg s0
  have hmem_framed : sA.mem ⊨ insertKeyActivePre F A chainPtr cg chc ckc seedPtr sA.sp ∗ (F_rest ∗ R) := by
    simpa only [sepConj_assoc] using hmem_act
  clear hmem hlen_mem hmem_act
  have hpc' : sA.pc = (blkPl_24).base + 916#64 := hpc
  have hwp_to_972 := insertKey_to_972_placed F A H hmm hgrow_ok x Gc ckc ci chc cg seedPtr
    F_rest R s0 sA hmax hklen hpc' hrun hsp hsp_align hx29 ⟨htrace, hvregs⟩ hcl
    hx1 hx19 hx20 hx21 hx23 hx25 hx26 hx27 hx28
  obtain ⟨sM, hsteps1, ⟨hpcM, hrunM, hclM, P_m, hmm_sat,
      hspM, halignM, hx29M, htrM, hx19M, hx20M, hx21M, hx22M, hx23M, hx25M, hx26M, hx27M, hx28M,
      mkCap1, mkPtr1, bs, hx24M, hbs, hlen_lt1, hcap1_lt, hptr1_ne, himpM⟩ | ⟨hpanM, P_p, hmp, hqp⟩⟩ :=
    steps_of_sepWPp_placed hcl hmem_framed hL hwp_to_972
  · have hmm_mid : sM.mem ⊨ insertKeyActiveMid F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr sM.sp bs ∗ (F_rest ∗ R) :=
      Satisfies.mono (sepConj_mono_left himpM) hmm_sat
    have hLM := hsteps1.codeLoaded hL
    have hwp2 := insertKey_from_964_placed F A H x Gc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr bs hklen hbs hlen_lt1 hcap1_lt hptr1_ne s0 sM
      hpcM hrunM hspM halignM hx29M htrM hx19M hx20M hx21M hx22M hx23M hx24M hx25M hx26M hx27M hx28M
    obtain ⟨sB, hsteps2, hpcB, hrunB, hclB, _, Pf, hmfB,
        hspB, halignB, hx29B, htrB, hregsD, hx25B, hx26B, hx28B, himpB⟩ :=
      sepWP_elim_inv_placed hclM hmm_mid hLM hwp2
    have hmf_post : sB.mem ⊨ (insertKeyActivePost F A chainPtr mkCap1 mkPtr1 cg chc ckc seedPtr (s0.sp - 480#64) ∗ F_rest) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left himpB) hmfB
    by_cases hlt2000 : chc.messageKeys.length < 2000
    · simp only [hlt2000, ↓reduceIte] at hpcB
      let cg' : ChainGhost :=
        { cg with
          mkCap := mkCap1
          mkPtr := mkPtr1
          keys := newMsgKeyGhost seedPtr :: cg.keys }
      have hG_agree : Gc.AgreeExcept (Gc.setChain ci cg') (some ci) :=
        RatchetGhost.AgreeExcept.setChain Gc hci_g cg'
          (by simp [cg', hcg_eq]) (by simp [cg', hcg_eq])
      have hmemD : sB.mem ⊨ cmkLoopHeap_placed A x (Gc.setChain ci cg')
          (updatedRatchetState F stc ci chc ckc) ckc s0 ∗ R := by
        rw [cmkLoopHeap_placed_eq_at]
        exact Satisfies.mono (sepConj_mono_left
          (insertKeyPost_entails_cmkLoopHeapAt_D F A lsLogFilterAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0
            hci_st hsrk hklen hlt2000)) hmf_post
      refine ⟨sB, hsteps1.trans hsteps2, Or.inl ⟨Gc.setChain ci cg', hG_agree, ?_⟩⟩
      exact ⟨hpcB, ⟨hrunB, hspB, hsp0_align, halignB, hx29B, htrB.1, hclB, htrB.2⟩,
        hregsD, hmemD⟩
    · simp only [hlt2000, ↓reduceIte] at hpcB
      have hlen2000 : chc.messageKeys.length = 2000 := by
        change chc.messageKeys.length ≤ 2000 at hmax
        omega
      have hklen2000 : cg.keys.length = 2000 := by omega
      have hcap2001 : 2001 ≤ mkCap1.toNat := by omega
      have hmemC : sB.mem ⊨ evictOldestKeyHeap_placed F A x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 ∗ R :=
        Satisfies.mono (sepConj_mono_left
          (insertKeyPost_entails_evictOldestKeyHeapAt F A lsLogFilterAddr x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 hlen2000)) hmf_post
      have hregsC : EvictOldestKeyRegs x Gc ckc ci mkPtr1 sB := by
        rcases hregsD with ⟨hx19B, hx21B, hx22B, hx23B, _⟩
        rw [hlen2000] at hx26B
        exact ⟨hx19B, hx21B, hx22B, hx23B, hx25B, hx26B, hx28B⟩
      refine ⟨sB, hsteps1.trans hsteps2, Or.inr (Or.inl ⟨cg, mkCap1, mkPtr1, ?_⟩)⟩
      exact ⟨hpcB, ⟨hrunB, hspB, hsp0_align, halignB, hx29B, htrB.1, hclB, htrB.2⟩,
        hregsC, ⟨hci_g, hcg_eq⟩, hsrk, hlen2000, hklen2000, hcap2001, hcap1_lt, hptr1_ne, hmemC⟩
  · exact ⟨sM, hsteps1, Or.inr (Or.inr ⟨hpanM, hqp hmp⟩)⟩

end CryptoVerification.LibsignalSession.StoreLoop
