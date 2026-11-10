/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::new` Temporary Buffer Deallocations and Exit

Frees the four temporary heap clones (`kyberCopyPtr`, `bkSerPtr`, `ikSerPtr`, `msgCopyPtr`),
restores callee-saved registers and `sp`, and composes `SeamB → exit` (`+0x4c4..+0x608`) for
`preKeyMsgNewSpec A`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bitVec_ofNat_slt_one_eq_false (n : Nat) (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).slt 1#64 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold BitVec.slt BitVec.toInt
  rw [decide_eq_false_iff_not, htoNat, show (1#64).toNat = 1 by decide]
  omega

theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

theorem identityKey_serialize_length (ik : IdentityKey) : ik.serialize.length = 33 :=
  publicKey_serialize_length ik.publicKey

def not_satisfies_false_sepConj2 {α : Sort*} {m : Memory} {P Q : SepProp}
    (h : m ⊨ (⌜False⌝ ∗ P) ∗ Q) : α :=
  have h' : m ⊨ ⌜False⌝ ∗ (P ∗ Q) := by rwa [sepConj_assoc] at h
  (not_satisfies_false_sepConj h').elim

def PanicAllocPost (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem panicAllocPost_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    PanicAllocPost s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

private theorem trTrap_allocHooks' {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    AllocHooks A (trTrapExterns C abs) :=
  ⟨by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_alloc") (by decide) (by decide)] using hA.alloc,
   by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_dealloc") (by decide) (by decide)] using hA.dealloc,
   by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_realloc") (by decide) (by decide)] using hA.realloc⟩

/-! ## Deallocate `kyberCopyPtr` (`+0x584..+0x594`) -/

theorem preKeyMsg_dealloc_kyber_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc =
      if (match x.kp with
          | none => noneCap
          | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1428#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1428#64)
      s
      (optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
       ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  cases hkp : x.kp with
  | none =>
    simp only [hkp, show noneCap.slt 1#64 = true by decide, ↓reduceIte,
      optKyberCopyBuf, emp_sepConj] at hpc ⊢
    exact SepWPp.done hpc hrun ⟨⟨hsp, hsp_align, hx20, hx22, hx24, hx27, hx28, hx29, rfl, rfl⟩,
      Entails.refl _⟩
  | some k =>
    simp only [hkp, optKyberCopyBuf, boxU8Buf, sepConj_assoc] at hpc hx19 ⊢
    refine SepWPp.pure_elim fun ⟨_, hkb⟩ => ?_
    by_cases hct : k.ciphertext = []
    · simp only [hct, List.length_nil, show (BitVec.ofNat 64 0).slt 1#64 = true by decide,
        ↓reduceIte, emp_sepConj] at hpc ⊢
      exact SepWPp.done hpc hrun ⟨⟨hsp, hsp_align, hx20, hx22, hx24, hx27, hx28, hx29, rfl, rfl⟩,
        Entails.refl _⟩
    · have hct_pos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hct
      have hslt : (BitVec.ofNat 64 k.ciphertext.length).slt 1#64 = false :=
        bitVec_ofNat_slt_one_eq_false k.ciphertext.length hct_pos (by omega)
      have htoNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hslt, Bool.false_eq_true, ↓reduceIte, hct, sepConj_assoc] at hpc ⊢
      have hdealloc := preKeyMsg_dealloc_ok_ext (A := A) (b := b) (ext := ext) hA
      preKeyMsg_fetches_range b (Rust.withPanics ext) 0x584 0x590
      generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x15130))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := (g.kyberCopyPtr, k.ciphertext.length, 1))
        (F := ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
        hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        have hmem := pointsToBytes_entails_memRegion g.kyberCopyPtr k.ciphertext
        rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)] at hm
        simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        refine Satisfies.mono ?_ hm
        refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem)))
        exact entails_of_sep_focus (by sep_focus)
      intro sf1 hpc1 hrun1 hsp1 hcs1
      rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
      simp only [rustDeallocSpec, sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      have hsp_align1 : sf1.spAligned = true := by
        rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
      refine SepWPp.done hpc1 hrun1 ⟨?_, ?_⟩
      · refine ⟨by simp only [wp_norm, arm64_norm, *], hsp_align1,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      · rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)]
        simp only [hsp, arm64_norm]
        exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_dealloc_kyber_wpp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64) (s : State)
    (hpc : s.pc =
      if (match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1428#64
      else (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1412#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1428#64) s
      (optKyberCopyBuf A g.kyberCopyPtr x.kp ∗ ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧ sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧ sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧ sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) :=
  preKeyMsg_dealloc_kyber_wpp_ext (trTrap_allocHooks' hA) x g sp0 s hpc hrun hsp hsp_align
    hx19 hx20 hx22 hx24 hx27 hx28 hx29

/-! ## Deallocate `bkSerPtr` and `ikSerPtr` (`+0x594..+0x5bc`) -/

theorem preKeyMsg_dealloc_kyber_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc =
      if (match x.kp with
          | none => noneCap
          | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1428#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1428#64)
      s
      (optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
       ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWPp_kit_of_trTrap (preKeyMsg_dealloc_kyber_wpp_trap hA x g sp0 s hpc hrun hsp hsp_align hx19 hx20 hx22 hx24 hx27 hx28 hx29)

theorem preKeyMsg_dealloc_bk_ik_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1468#64)
      s
      (boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
       boxU8Buf A g.ikSerPtr x.ik.serialize ∗
       ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hdealloc := preKeyMsg_dealloc_ok_ext (A := A) (b := b) (ext := ext) hA
  have hbk_len := publicKey_serialize_length x.baseKey
  have hbk_ne : x.baseKey.serialize ≠ [] := by
    intro h; rw [h] at hbk_len; simp at hbk_len
  have hik_len := identityKey_serialize_length x.ik
  have hik_ne : x.ik.serialize ≠ [] := by
    intro h; rw [h] at hik_len; simp at hik_len
  unfold boxU8Buf
  simp only [hbk_ne, hik_ne, ↓reduceIte, hbk_len, hik_len, sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  have hpull_ik :
      A.live g.bkSerPtr 33 1 ∗
        (g.bkSerPtr ↦ₛ x.baseKey.serialize) ∗
        ⌜g.ikSerPtr ≠ 0#64 ∧ (33 : Nat) < 2 ^ 63⌝ ∗
        A.live g.ikSerPtr 33 1 ∗
        (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
        ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
        A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack =
      ⌜g.ikSerPtr ≠ 0#64 ∧ (33 : Nat) < 2 ^ 63⌝ ∗
        (A.live g.bkSerPtr 33 1 ∗
         (g.bkSerPtr ↦ₛ x.baseKey.serialize) ∗
         A.live g.ikSerPtr 33 1 ∗
         (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
         ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
         A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack) := by sep_focus
  rw [hpull_ik]
  clear hpull_ik
  refine SepWPp.pure_elim fun _ => ?_
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x594 0x5b8
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (g.bkSerPtr, 33, 1))
    (F := A.live g.ikSerPtr 33 1 ∗
          (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
          ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, arm64_norm] using hsp_align)
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have hmem_bk := pointsToBytes_entails_memRegion g.bkSerPtr x.baseKey.serialize
    rw [hbk_len] at hmem_bk
    rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)] at hm
    simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_bk)))
    exact entails_of_sep_focus (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
  simp only [rustDeallocSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hsp_align1 : sf1.spAligned = true := by
    rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (g.ikSerPtr, 33, 1))
    (F := ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, arm64_norm] using hsp_align1)
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have hmem_ik := pointsToBytes_entails_memRegion g.ikSerPtr x.ik.serialize
    rw [hik_len] at hmem_ik
    simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_ik)))
    exact entails_of_sep_focus (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
  simp only [rustDeallocSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2 => ?_
  have hsp_align2 : sf2.spAligned = true := by
    rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
  refine SepWPp.done hpc2 hrun2 ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *], hsp_align2,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
  · rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)]
    simp only [hsp1, hsp, arm64_norm]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_dealloc_bk_ik_wpp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64) (s : State)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1428#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 368#64) (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr) (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64) (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr) (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1468#64) s
      (boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗ boxU8Buf A g.ikSerPtr x.ik.serialize ∗
       ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧ sm.spAligned = true ∧ sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧ sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢ ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) :=
  preKeyMsg_dealloc_bk_ik_wpp_ext (trTrap_allocHooks' hA) x g sp0 s hpc hrun hsp hsp_align
    hx20 hx22 hx24 hx27 hx28 hx29

/-! ## Deallocate `msgCopyPtr` and Epilogue (`+0x5bc → lr`) -/

theorem preKeyMsg_dealloc_bk_ik_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1468#64)
      s
      (boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
       boxU8Buf A g.ikSerPtr x.ik.serialize ∗
       ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc ⊢
  exact SepWPp_kit_of_trTrap (preKeyMsg_dealloc_bk_ik_wpp_trap hA x g sp0 s hpc hrun hsp hsp_align hx20 hx22 hx24 hx27 hx28 hx29)

def preKeyMsgFrameRest (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64) : SepProp :=
  ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
  ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
  ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
  ((sp0 - 344#64) ↦₃₂ x.regId) ∗
  memRegion (sp0 - 340#64) 8 ∗
  ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
  ((sp0 - 328#64) ↦₃₂ x.spk) ∗
  ((sp0 - 324#64) ↦₃₂ g.kyberId32) ∗
  ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
  ((sp0 - 312#64) ↦₆₄ x.bkA) ∗
  ((sp0 - 304#64) ↦₆₄ x.ret) ∗
  ((sp0 - 296#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
  ((sp0 - 292#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
  ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
  ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
  memRegion (sp0 - 272#64) 128 ∗
  ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
  ((sp0 - 136#64) ↦₆₄ g.serPtr) ∗
  ((sp0 - 128#64) ↦₆₄ lenW) ∗
  memRegion (sp0 - 120#64) 24

theorem preKeyMsgFrameRest_entails_stackAt (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (s0 : State)
    (sp0 lenW : BitVec 64) :
    stackAt (sp0 - 368#64) preKeyMsgSubStack ∗
      preKeyMsgFrameRest x g sp0 lenW ∗
      preKeyMsgSavedRegs sp0 s0 ⊢
    stackAt sp0 preKeyMsgNewStack := by
  simpa only [preKeyMsgFrameRest, sepConj_assoc] using preKeyMsgFrameWords_entails_stackAt x g s0 sp0 lenW

theorem preKeyMsg_dealloc_msg_and_epilogue_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hmsg_lo : macLength + 1 ≤ x.msg.serialized.length)
    (hmsg_hi : x.msg.serialized.length < 2 ^ 40)
    (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 1468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt b ext)
      (s0.readReg64 .lr)
      s
      (boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
       preKeyMsgSavedRegs sp0 s0 ∗
       preKeyMsgFrameRest x g sp0 lenW ∗
       A.pool ∗
       stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s) := by
  have hsp_cancel : sp0 - 368#64 + 368#64 = sp0 := BitVec.sub_add_cancel sp0 368#64
  have hmsg_pos : 0 < x.msg.serialized.length := by unfold macLength at hmsg_lo; omega
  have hmsg_ne : x.msg.serialized ≠ [] := by
    intro h; simp [h] at hmsg_pos
  have hmsg_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmsg_ne0 : BitVec.ofNat 64 x.msg.serialized.length ≠ 0#64 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [hmsg_toNat, BitVec.toNat_zero] at ht
    omega
  have hmsg_beq : (BitVec.ofNat 64 x.msg.serialized.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hmsg_ne0
  have hdealloc := preKeyMsg_dealloc_ok_ext (A := A) (b := b) (ext := ext) hA
  unfold boxU8Buf
  simp only [hmsg_ne, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  unfold preKeyMsgSavedRegs
  simp only [sepConj_assoc]
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x5bc 0x5e8
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x15130))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (g.msgCopyPtr, x.msg.serialized.length, 1))
    (ret_pc := s0.readReg64 .lr)
    (F := memRegion (sp0 - 8192#64) 4096)
    hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, hsp, hsp_cancel, ← hsp0, arm64_norm] using hsp0_align)
    (by simp only [wp_norm, arm64_norm, *]) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have hst := preKeyMsgFrameRest_entails_stackAt x g s0 sp0 lenW
    unfold preKeyMsgSavedRegs at hst
    rw [stackAt_preKeyMsgNew_to_allocHook sp0,
      sepConj_comm (memRegion (sp0 - 8192#64) 4096)] at hst
    have hmem_msg := pointsToBytes_entails_memRegion g.msgCopyPtr x.msg.serialized
    simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    rw [← sepConj_assoc (stackAt sp0 allocHookStack)]
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hmem_msg (sepConj_mono_left hst))))
    exact entails_of_sep_focus (by sep_focus)
  intro sf hpcf hrunf hspf hcsf
  rcases hcsf with ⟨h19_f, h20_f, h21_f, h22_f, h23_f, h24_f, h25_f, h26_f, h27_f, h28_f, hfp_f, hvregs_f⟩
  simp only [rustDeallocSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_f => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
      by simp only [wp_norm, arm64_norm, *]⟩
  · rw [hsp0, stackAt_preKeyMsgNew_to_allocHook sp0]
    simp only [wp_norm, arm64_norm, *]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_dealloc_msg_and_epilogue_wpp_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hmsg_lo : macLength + 1 ≤ x.msg.serialized.length) (hmsg_hi : x.msg.serialized.length < 2 ^ 40)
    (s0 s : State) (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 1468#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 368#64) (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true) (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (trTrapProgAt b C abs) (s0.readReg64 .lr) s
      (boxU8Buf A g.msgCopyPtr x.msg.serialized ∗ preKeyMsgSavedRegs sp0 s0 ∗
       preKeyMsgFrameRest x g sp0 lenW ∗ A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s) :=
  preKeyMsg_dealloc_msg_and_epilogue_wpp_ext (trTrap_allocHooks' hA) x g sp0 lenW hmsg_lo hmsg_hi
    s0 s hpc hrun hsp hsp0 hsp0_align hsp_align hx20 hx27 htr hvregs

/-! ## `SeamB` to Exit Composition -/

theorem preKeyMsg_dealloc_msg_and_epilogue_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hmsg_lo : macLength + 1 ≤ x.msg.serialized.length)
    (hmsg_hi : x.msg.serialized.length < 2 ^ 40)
    (s0 s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 1468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      (s0.readReg64 .lr)
      s
      (boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
       preKeyMsgSavedRegs sp0 s0 ∗
       preKeyMsgFrameRest x g sp0 lenW ∗
       A.pool ∗
       stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc
  exact SepWPp_kit_of_trTrap (preKeyMsg_dealloc_msg_and_epilogue_wpp_trap hA x g sp0 lenW hmsg_lo hmsg_hi s0 s hpc hrun hsp hsp0 hsp0_align hsp_align hx20 hx27 htr hvregs)

theorem preKeyMsg_seq_wp' {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _hoom⟩⟩ := h1.elim hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_seq_wpp' {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, _hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_reaches_outcome_of_sepWPp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {P R : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
        (P_f ⊢
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          (s0.sp ↦₆₄ x.msgA) ∗
          memRegion x.kyA 24 ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          memRegion x.msgA 120 ∗
          A.pool ∗
          stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s0)) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (preKeyMsgNewSpec A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf, htrf⟩, hent⟩ | ⟨hpanf, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩⟩ :=
    hwp R hm hL
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩))
    have hpost : P_f ⊢ (preKeyMsgNewSpec A).post x s0 sf := by
      simpa only [preKeyMsgNewSpec, sepConj_assoc] using Entails.pure_right htrf hent
    exact Satisfies.mono (sepConj_mono_left hpost) hmf
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpanf, hqp R hmf⟩)))
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_reaches_outcome_of_sepWPp_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {P R : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
        (P_f ⊢
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          (s0.sp ↦₆₄ x.msgA) ∗
          memRegion x.kyA 24 ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          memRegion x.msgA 120 ∗
          A.pool ∗
          stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s0)) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext) (preKeyMsgNewSpec A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf, htrf⟩, hent⟩ | ⟨hpanf, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩⟩ :=
    hwp R hm hL
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩))
    have hpost : P_f ⊢ (preKeyMsgNewSpec A).post x s0 sf := by
      simpa only [preKeyMsgNewSpec, sepConj_assoc] using Entails.pure_right htrf hent
    exact Satisfies.mono (sepConj_mono_left hpost) hmf
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpanf, hqp R hmf⟩)))
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_reaches_outcome_of_sepWPp_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {P R : SepProp} {s0 s : State} (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (trTrapProgAt img.base C abs) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
        (P_f ⊢ (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗ (s0.sp ↦₆₄ x.msgA) ∗
          memRegion x.kyA 24 ∗ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗ memRegion x.msgA 120 ∗
          A.pool ∗ stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s0)) :
    reaches_outcome (trTrapProgAt img.base C abs) (preKeyMsgNewSpec A) x R s0 s :=
  preKeyMsg_reaches_outcome_of_sepWPp_ext hm hwp

theorem signalMessageBounds_of_seamB {A : RustAlloc} {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost}
    {s0 : State} {lenW : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ preKeyMsgFrameSlotsAt' A x g s0 lenW x.model.serialized ∗ preKeyMsgHeapAt A x g s0 ∗ R) :
    macLength + 1 ≤ x.msg.serialized.length ∧ x.msg.serialized.length < 2 ^ 40 := by
  have hpull :
      preKeyMsgFrameSlotsAt' A x g s0 lenW x.model.serialized ∗ preKeyMsgHeapAt A x g s0 ∗ R =
        signalMessageAt A x.msgG x.msgA x.msg ∗
          (preKeyMsgFrameSlotsAt' A x g s0 lenW x.model.serialized ∗
            (s0.sp ↦₆₄ x.msgA) ∗
            optKyberAt A x.kyA x.kyPtr x.kp ∗
            (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
            (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
            memRegion x.ret 248 ∗
            optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
            boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
            boxU8Buf A g.ikSerPtr x.ik.serialize ∗
            boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
            A.pool ∗
            stackAt (s0.sp - 0x170#64) preKeyMsgSubStack ∗ R) := by
    unfold preKeyMsgHeapAt
    ac_rfl
  rw [hpull] at hm
  unfold signalMessageAt at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact ⟨hm.1.1, hm.1.2.1⟩

theorem fields_epilogue_ok_aux_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost} {R : SepProp} {s0 s : State}
    (hA : AllocHooks A ext)
    (hB : SeamB img A x g R s0 s) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext) (preKeyMsgNewSpec A) x R s0 s := by
  rcases hB with ⟨hpc, ⟨hser_bound, hver, hpre, _⟩,
    ⟨hrun, hsp, hsp0_align, hsp_align, htr, hx29, hx19, hx20, hx21, hx22, hx24, hx25, hx27, hx28, hvregs⟩,
    hx8, hx23, hx26, lenW, hm⟩
  have ⟨hmsg_lo, hmsg_hi⟩ := signalMessageBounds_of_seamB hm
  have hpc' : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 1220#64 := by
    rw [fnAddr_preKeyMsgNew_ext]
    exact hpc
  have hsp' : s.sp = s0.sp - 368#64 := hsp
  have hx29' : s.readReg64 .x29 = s0.sp - 96#64 := hx29
  rw [← sepConj_assoc] at hm
  refine preKeyMsg_reaches_outcome_of_sepWPp_ext hm ?_
  refine preKeyMsg_seq_wp'
    (preKeyMsg_sret_stores_wp_ext x g s0.sp lenW hser_bound hver hpre s hpc' hrun hsp' hsp_align
      hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29')
    (by (conv => lhs; simp only [preKeyMsgFrameSlotsAt', preKeyMsgHeapAt, sepConj_assoc, arm64_norm]); sep_focus) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hvregs1⟩
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hvregs1' : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1.trans hvregs
  refine preKeyMsg_seq_wpp' htr1'
    (preKeyMsg_dealloc_kyber_wpp_ext hA x g s0.sp s1 hpc1 hrun1 hsp1 hsp_align1
      hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hvregs2⟩
  have htr2' : s2.trace = s0.trace := htr2.trans htr1'
  have hvregs2' : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans hvregs1'
  refine preKeyMsg_seq_wpp' htr2'
    (preKeyMsg_dealloc_bk_ik_wpp_ext hA x g s0.sp s2 hpc2 hrun2 hsp2 hsp_align2
      hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx20_3, hx27_3, _hx29_3, htr3, hvregs3⟩
  have htr3' : s3.trace = s0.trace := htr3.trans htr2'
  have hvregs3' : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs2'
  refine preKeyMsg_seq_wpp' htr3'
    (preKeyMsg_dealloc_msg_and_epilogue_wpp_ext hA x g s0.sp lenW hmsg_lo hmsg_hi s0 s3
      hpc3 hrun3 hsp3 rfl hsp0_align hsp_align3 hx20_3 hx27_3 htr3' hvregs3')
    (by (conv => rhs; arg 1; simp only [preKeyMsgFrameRest, sepConj_assoc, arm64_norm]); sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro sf hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  exact entails_of_sep_focus (by sep_focus)

theorem fields_epilogue_ok_aux_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost} {R : SepProp} {s0 s : State}
    (hA : AllocHooks A abs) (hB : SeamB img A x g R s0 s) :
    reaches_outcome (trTrapProgAt img.base C abs) (preKeyMsgNewSpec A) x R s0 s :=
  fields_epilogue_ok_aux_ext (trTrap_allocHooks' hA) hB

theorem fields_epilogue_ok_aux {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost} {R : SepProp} {s0 s : State}
    (hA : AllocHooks A abs)
    (hB : SeamB img A x g R s0 s) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs) (preKeyMsgNewSpec A) x R s0 s :=
  reaches_outcome_kit_of_trTrap (fields_epilogue_ok_aux_trap hA hB)

/-! ## Relocatable Placement Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem preKeyMsg_dealloc_kyber_wpp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc =
      if (match x.kp with
          | none => noneCap
          | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (blkPl_41).base + 1428#64
      else
        (blkPl_41).base + 1412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H)
      ((blkPl_41).base + 1428#64)
      s
      (optKyberCopyBuf A g.kyberCopyPtr x.kp ∗
       ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  cases hkp : x.kp with
  | none =>
    simp only [hkp, show noneCap.slt 1#64 = true by decide, ↓reduceIte,
      optKyberCopyBuf, emp_sepConj] at hpc ⊢
    exact SepWPp.done hpc hrun ⟨⟨hsp, hsp_align, hx20, hx22, hx24, hx27, hx28, hx29, rfl, rfl⟩,
      Entails.refl _⟩
  | some k =>
    simp only [hkp, optKyberCopyBuf, boxU8Buf, sepConj_assoc] at hpc hx19 ⊢
    refine SepWPp.pure_elim fun ⟨_, hkb⟩ => ?_
    by_cases hct : k.ciphertext = []
    · simp only [hct, List.length_nil, show (BitVec.ofNat 64 0).slt 1#64 = true by decide,
        ↓reduceIte, emp_sepConj] at hpc ⊢
      exact SepWPp.done hpc hrun ⟨⟨hsp, hsp_align, hx20, hx22, hx24, hx27, hx28, hx29, rfl, rfl⟩,
        Entails.refl _⟩
    · have hct_pos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hct
      have hslt : (BitVec.ofNat 64 k.ciphertext.length).slt 1#64 = false :=
        bitVec_ofNat_slt_one_eq_false k.ciphertext.length hct_pos (by omega)
      have htoNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hslt, Bool.false_eq_true, ↓reduceIte, hct, sepConj_assoc] at hpc ⊢
      have hdealloc_ok := preKeyMsg_dealloc_placed_ok hdealloc
      apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.call (x := (g.kyberCopyPtr, k.ciphertext.length, 1))
        (F := ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
        hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
      · intro R' hm
        have hmem := pointsToBytes_entails_memRegion g.kyberCopyPtr k.ciphertext
        rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)] at hm
        simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        refine Satisfies.mono ?_ hm
        refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem)))
        exact entails_of_sep_focus (by sep_focus)
      intro sf1 hpc1 hrun1 hsp1 hcs1
      rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
      simp only [rustDeallocSpec, sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      have hsp_align1 : sf1.spAligned = true := by
        rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
      refine SepWPp.done hpc1 hrun1 ⟨?_, ?_⟩
      · refine ⟨by simp only [wp_norm, arm64_norm, *], hsp_align1,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      · rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)]
        simp only [hsp, arm64_norm]
        exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_dealloc_bk_ik_wpp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64)
    (s : State)
    (hpc : s.pc = (blkPl_41).base + 1428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H)
      ((blkPl_41).base + 1468#64)
      s
      (boxU8Buf A g.bkSerPtr x.baseKey.serialize ∗
       boxU8Buf A g.ikSerPtr x.ik.serialize ∗
       ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
       A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (PanicAllocPost s) := by
  have hdealloc_ok := preKeyMsg_dealloc_placed_ok hdealloc
  have hbk_len := publicKey_serialize_length x.baseKey
  have hbk_ne : x.baseKey.serialize ≠ [] := by
    intro h; rw [h] at hbk_len; simp at hbk_len
  have hik_len := identityKey_serialize_length x.ik
  have hik_ne : x.ik.serialize ≠ [] := by
    intro h; rw [h] at hik_len; simp at hik_len
  unfold boxU8Buf
  simp only [hbk_ne, hik_ne, ↓reduceIte, hbk_len, hik_len, sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  have hpull_ik :
      A.live g.bkSerPtr 33 1 ∗
        (g.bkSerPtr ↦ₛ x.baseKey.serialize) ∗
        ⌜g.ikSerPtr ≠ 0#64 ∧ (33 : Nat) < 2 ^ 63⌝ ∗
        A.live g.ikSerPtr 33 1 ∗
        (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
        ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
        A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack =
      ⌜g.ikSerPtr ≠ 0#64 ∧ (33 : Nat) < 2 ^ 63⌝ ∗
        (A.live g.bkSerPtr 33 1 ∗
         (g.bkSerPtr ↦ₛ x.baseKey.serialize) ∗
         A.live g.ikSerPtr 33 1 ∗
         (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
         ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
         A.pool ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack) := by sep_focus
  rw [hpull_ik]
  clear hpull_ik
  refine SepWPp.pure_elim fun _ => ?_
  apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (g.bkSerPtr, 33, 1))
    (F := A.live g.ikSerPtr 33 1 ∗
          (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
          ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, arm64_norm] using hsp_align)
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have hmem_bk := pointsToBytes_entails_memRegion g.bkSerPtr x.baseKey.serialize
    rw [hbk_len] at hmem_bk
    rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)] at hm
    simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_bk)))
    exact entails_of_sep_focus (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
  simp only [rustDeallocSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hsp_align1 : sf1.spAligned = true := by
    rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
  apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (g.ikSerPtr, 33, 1))
    (F := ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, arm64_norm] using hsp_align1)
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have hmem_ik := pointsToBytes_entails_memRegion g.ikSerPtr x.ik.serialize
    rw [hik_len] at hmem_ik
    simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_ik)))
    exact entails_of_sep_focus (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
  simp only [rustDeallocSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2 => ?_
  have hsp_align2 : sf2.spAligned = true := by
    rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
  refine SepWPp.done hpc2 hrun2 ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *], hsp_align2,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
  · rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)]
    simp only [hsp1, hsp, arm64_norm]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_dealloc_msg_and_epilogue_wpp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hmsg_lo : macLength + 1 ≤ x.msg.serialized.length)
    (hmsg_hi : x.msg.serialized.length < 2 ^ 40)
    (s0 s : State)
    (hpc : s.pc = (blkPl_41).base + 1468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_41 H)
      (s0.readReg64 .lr)
      s
      (boxU8Buf A g.msgCopyPtr x.msg.serialized ∗
       preKeyMsgSavedRegs sp0 s0 ∗
       preKeyMsgFrameRest x g sp0 lenW ∗
       A.pool ∗
       stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool ∗ stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s) := by
  have hsp_cancel : sp0 - 368#64 + 368#64 = sp0 := BitVec.sub_add_cancel sp0 368#64
  have hmsg_pos : 0 < x.msg.serialized.length := by unfold macLength at hmsg_lo; omega
  have hmsg_ne : x.msg.serialized ≠ [] := by
    intro h; simp [h] at hmsg_pos
  have hmsg_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmsg_ne0 : BitVec.ofNat 64 x.msg.serialized.length ≠ 0#64 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [hmsg_toNat, BitVec.toNat_zero] at ht
    omega
  have hmsg_beq : (BitVec.ofNat 64 x.msg.serialized.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hmsg_ne0
  have hdealloc_ok := preKeyMsg_dealloc_placed_ok hdealloc
  unfold boxU8Buf
  simp only [hmsg_ne, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  unfold preKeyMsgSavedRegs
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.call (x := (g.msgCopyPtr, x.msg.serialized.length, 1))
    (ret_pc := s0.readReg64 .lr)
    (F := memRegion (sp0 - 8192#64) 4096)
    hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, hsp, hsp_cancel, ← hsp0, arm64_norm] using hsp0_align)
    (by simp only [wp_norm, arm64_norm, *]) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have hst := preKeyMsgFrameRest_entails_stackAt x g s0 sp0 lenW
    unfold preKeyMsgSavedRegs at hst
    rw [stackAt_preKeyMsgNew_to_allocHook sp0,
      sepConj_comm (memRegion (sp0 - 8192#64) 4096)] at hst
    have hmem_msg := pointsToBytes_entails_memRegion g.msgCopyPtr x.msg.serialized
    simp (config := { decide := true }) only [rustDeallocSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    rw [← sepConj_assoc (stackAt sp0 allocHookStack)]
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hmem_msg (sepConj_mono_left hst))))
    exact entails_of_sep_focus (by sep_focus)
  intro sf hpcf hrunf hspf hcsf
  rcases hcsf with ⟨h19_f, h20_f, h21_f, h22_f, h23_f, h24_f, h25_f, h26_f, h27_f, h28_f, hfp_f, hvregs_f⟩
  simp only [rustDeallocSpec, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_f => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
      by simp only [wp_norm, arm64_norm, *]⟩
  · rw [hsp0, stackAt_preKeyMsgNew_to_allocHook sp0]
    simp only [wp_norm, arm64_norm, *]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_reaches_outcome_of_sepWPp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {x : PreKeyMsgNewCall} {P R : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_41 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
        (P_f ⊢
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          (s0.sp ↦₆₄ x.msgA) ∗
          memRegion x.kyA 24 ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          memRegion x.msgA 120 ∗
          A.pool ∗
          stackAt s0.sp preKeyMsgNewStack))
      (PanicAllocPost s0)) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf, htrf⟩, hent⟩ | ⟨hpanf, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩⟩ :=
    hwp R hm hL
  · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩))
    have hpost : P_f ⊢ (preKeyMsgNewSpec A).post x s0 sf := by
      simpa only [preKeyMsgNewSpec, sepConj_assoc] using Entails.pure_right htrf hent
    exact Satisfies.mono (sepConj_mono_left hpost) hmf
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpanf, hqp R hmf⟩)))
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem fields_epilogue_placed_ok_aux [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : PreKeyMsgNewCall} {g : PreKeyMsgFrameGhost} {R : SepProp} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hB : SeamB_placed A x g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec A) x R s0 s := by
  rcases hB with ⟨hpc, _hcl, ⟨hser_bound, hver, hpre, _⟩,
    ⟨hrun, hsp, hsp0_align, hsp_align, htr, hx29, hx19, hx20, hx21, hx22, hx24, hx25, hx27, hx28, hvregs⟩,
    hx8, hx23, hx26, lenW, hm⟩
  have ⟨hmsg_lo, hmsg_hi⟩ := signalMessageBounds_of_seamB hm
  have hsp' : s.sp = s0.sp - 368#64 := hsp
  have hx29' : s.readReg64 .x29 = s0.sp - 96#64 := hx29
  rw [← sepConj_assoc] at hm
  refine preKeyMsg_reaches_outcome_of_sepWPp_placed hm ?_
  refine preKeyMsg_seq_wp'
    (preKeyMsg_sret_stores_wp_placed x g s0.sp lenW hser_bound hver hpre s hpc hrun hsp' hsp_align
      hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29')
    (by (conv => lhs; simp only [preKeyMsgFrameSlotsAt', preKeyMsgHeapAt, sepConj_assoc, arm64_norm]); sep_focus) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hvregs1⟩
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hvregs1' : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1.trans hvregs
  refine preKeyMsg_seq_wpp' htr1'
    (preKeyMsg_dealloc_kyber_wpp_placed hdealloc x g s0.sp s1 hpc1 hrun1 hsp1 hsp_align1
      hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hvregs2⟩
  have htr2' : s2.trace = s0.trace := htr2.trans htr1'
  have hvregs2' : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans hvregs1'
  refine preKeyMsg_seq_wpp' htr2'
    (preKeyMsg_dealloc_bk_ik_wpp_placed hdealloc x g s0.sp s2 hpc2 hrun2 hsp2 hsp_align2
      hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx20_3, hx27_3, _hx29_3, htr3, hvregs3⟩
  have htr3' : s3.trace = s0.trace := htr3.trans htr2'
  have hvregs3' : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs2'
  refine preKeyMsg_seq_wpp' htr3'
    (preKeyMsg_dealloc_msg_and_epilogue_wpp_placed hdealloc x g s0.sp lenW hmsg_lo hmsg_hi s0 s3
      hpc3 hrun3 hsp3 rfl hsp0_align hsp_align3 hx20_3 hx27_3 htr3' hvregs3')
    (by (conv => rhs; arg 1; simp only [preKeyMsgFrameRest, sepConj_assoc, arm64_norm]); sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro sf hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  exact entails_of_sep_focus (by sep_focus)

end Placed

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
