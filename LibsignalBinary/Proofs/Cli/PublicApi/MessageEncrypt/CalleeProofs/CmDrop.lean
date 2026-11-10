/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Callees
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# CLI `drop_glue<CiphertextMessage>` Proof

Verifies `core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage>` on the CLI
image (`trTrapProgAt` / `tripleRatchetProgAtExt`), covering both the `SignalMessage` and
`PreKeySignalMessage` variants.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[simp, arm64_norm]
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDropName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]"

gen_decodes libsignalSessionCode_tree cmDropBinCli [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]" + 0) → (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]" + 380)]

private abbrev cmActiveStack : Nat := allocHookStack + 32

private theorem stackAt_cmDrop_outer (sp : BitVec 64) :
    stackAt sp (allocHookStack + 0x40) =
      memRegion (sp - 4160#64) 32 ∗ stackAt sp cmActiveStack :=
  stackAt_split_bottom sp cmActiveStack 32 (by decide)

private theorem stackAt_cmActive_split (sp : BitVec 64) :
    stackAt sp cmActiveStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp allocHookStack 4 (by decide)

private theorem tail_stack_32_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  rw [← stackAt_split_bottom sp allocHookStack 32 (by decide),
      ← stackAt_cmActive_split sp]

private theorem cells4_entails_stack_bottom (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack := by
  rw [tail_stack_32_from_bottom sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private theorem stack_restore_32_cm (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    stackAt sp cmActiveStack := by
  rw [stackAt_cmActive_split sp, ← tail_stack_32_from_bottom sp]
  exact cells4_entails_stack_bottom sp fp lr x20 x19

@[reducible]
private def Saved32Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  s.sp = fsp ∧
  s.trace = s0.trace

@[reducible]
private def optBoxDealloc (A : RustAlloc) (p0 l0 : BitVec 64) : SepProp :=
  if (p0 == 0#64) = true then emp
  else vecPinDealloc A ⟨l0, p0⟩

private theorem vecU8At_entails_pin_dealloc_bound (A : RustAlloc) (a : BitVec 64) (pin : VecPin)
    (bs : List (BitVec 8)) :
    vecU8At A a pin.cap pin.ptr bs ⊢
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecPinDealloc A pin := by
  refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr bs) ?_
  unfold vecHeader vecPinDealloc
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap, _⟩
  refine Entails.pure_right hcap ?_
  have hbeq : ((pin.cap == 0#64) = true) ↔ pin.cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))

private theorem boxU8At_entails_dealloc (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs ⊢
      ∃∗ len : BitVec 64,
        (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ len) ∗
        vecPinDealloc A ⟨len, ptr⟩ := by
  have hpure : boxU8At A a ptr bs =
      ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
      ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))) := by
    unfold boxU8At; ac_rfl
  rw [hpure]
  apply Entails.pure_left; rintro ⟨_, hlen⟩
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_
  unfold vecPinDealloc
  have h64 : bs.length < 2 ^ 64 := by omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
  have hbeq : ((BitVec.ofNat 64 bs.length == 0#64) = true) ↔ bs = [] := by
    rw [beq_iff_eq, ← List.length_eq_zero_iff]
    constructor
    · intro h
      have ht := congrArg BitVec.toNat h
      simpa [htoNat] using ht
    · intro h; simp [h]
  simp only [hbeq, htoNat]
  by_cases hbs : bs = []
  · simp only [hbs, ↓reduceIte]
    exact Entails.refl _
  · simp only [hbs, ↓reduceIte]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (pointsToBytes_entails_memRegion ptr bs)))

private theorem optBoxU8At_entails_dealloc (A : RustAlloc) (a ptr : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optBoxU8At A a ptr opt ⊢
      ∃∗ p0 : BitVec 64, ∃∗ l0 : BitVec 64,
        (a ↦₆₄ p0) ∗ ((a + 8#64) ↦₆₄ l0) ∗ optBoxDealloc A p0 l0 := by
  cases opt with
  | none =>
    unfold optBoxU8At optBoxDealloc
    rw [ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro l0
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right l0 ?_)
    simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some bs =>
    unfold optBoxU8At optBoxDealloc
    have hptr : boxU8At A a ptr bs ⊢ ⌜ptr ≠ 0#64⌝ ∗ boxU8At A a ptr bs := by
      have hpure : boxU8At A a ptr bs =
          ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
          ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs))) := by
        unfold boxU8At; ac_rfl
      rw [hpure]
      apply Entails.pure_left; intro h
      exact Entails.pure_right h.1 (Entails.pure_right h (Entails.refl _))
    refine Entails.trans hptr ?_
    apply Entails.pure_left; intro hne
    refine Entails.trans (boxU8At_entails_dealloc A a ptr bs) ?_
    apply Entails.sepExists_elim; intro l0
    refine Entails.sepExists_right ptr (Entails.sepExists_right l0 ?_)
    have hbeq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hne
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    exact Entails.refl _

private theorem u32_pad4_entails_memRegion_8 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ∗ memRegion (a + 4#64) 4 ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 4) (b' := a + 4#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo32_entails_memRegion a v)

private theorem optU32At_entails_memRegion_8 (a : BitVec 64) (opt : Option (BitVec 32)) :
    optU32At a opt ⊢ memRegion a 8 := by
  cases opt with
  | none =>
    unfold optU32At
    exact u32_pad4_entails_memRegion_8 a 0#32
  | some v =>
    unfold optU32At
    refine Entails.trans (sepConj_mono_right (pointsTo32_entails_memRegion (a + 4#64) v)) ?_
    exact u32_pad4_entails_memRegion_8 a 1#32

private theorem optKyberAt_entails_dealloc (A : RustAlloc) (a ptr : BitVec 64)
    (kp : Option KyberPayload) :
    optKyberAt A a ptr kp ⊢
      ∃∗ p0 : BitVec 64, ∃∗ l0 : BitVec 64,
        (a ↦₆₄ p0) ∗ ((a + 8#64) ↦₆₄ l0) ∗ memRegion (a + 16#64) 8 ∗ optBoxDealloc A p0 l0 := by
  have hred : optKyberAt A a ptr kp ⊢
      optBoxU8At A a ptr (kp.map (·.ciphertext)) ∗ memRegion (a + 16#64) 8 := by
    cases kp with
    | none =>
      dsimp only [optKyberAt, optBoxU8At, Option.map]
      rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8)
            (b' := a + 16#64) rfl (by bv_omega) (by decide),
          sepConj_assoc]
      exact Entails.refl _
    | some k =>
      dsimp only [optKyberAt, optBoxU8At, Option.map]
      have h8 : ((a + 16#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 20#64) 4 ⊢ memRegion (a + 16#64) 8 := by
        have h20 : (a + 16#64) + 4#64 = a + 20#64 := by bv_omega
        simpa [h20] using u32_pad4_entails_memRegion_8 (a + 16#64) k.preKeyId
      exact sepConj_mono_right h8
  refine Entails.trans hred ?_
  refine Entails.trans (sepConj_mono_left (optBoxU8At_entails_dealloc A a ptr (kp.map (·.ciphertext)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p0
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro l0
  refine Entails.sepExists_right p0 (Entails.sepExists_right l0 ?_)
  exact Entails.of_eq (by ac_rfl)

private theorem u64x2_entails_memRegion_16 (a w1 w2 : BitVec 64) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ⊢ memRegion a 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a w1)
    (pointsTo64_entails_memRegion (a + 8#64) w2)

private theorem u32x2_u8_pad7_entails_memRegion_16 (a : BitVec 64) (v1 v2 : BitVec 32) (b : BitVec 8) :
    (a ↦₃₂ v1) ∗ ((a + 4#64) ↦₃₂ v2) ∗ ((a + 8#64) ↦₈ b) ∗ memRegion (a + 9#64) 7 ⊢
      memRegion a 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 12) (b' := a + 4#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 4) (k := 8) (b' := a + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 7) (b' := a + 9#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo32_entails_memRegion a v1)
    (sepConj_mono (pointsTo32_entails_memRegion (a + 4#64) v2)
      (sepConj_mono_left
        (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) b) (IsBlock.memRegion (a + 8#64) 1) fun _ _ => trivial)))

private theorem vec32_entails_memRegion_32 (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ v.toList) ⊢ memRegion a 32 := by
  have h := pointsToBytes_entails_memRegion a v.toList
  rwa [List.Vector.toList_length] at h

@[reducible]
private def smHeadersAt (a : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) : SepProp :=
  (a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
  ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ∗
  memRegion (a + 56#64) 32 ∗
  ((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL) ∗
  memRegion (a + 104#64) 16

private theorem smHeadersAt_entails_memRegion_120 (a : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) :
    smHeadersAt a g ctLen serLen addrP addrL ⊢ memRegion a 120 := by
  unfold smHeadersAt
  have h0 := header_cells_entails_memRegion_24 a g.pqCap g.pqPtr
  have h1 : ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ⊢ memRegion (a + 24#64) 16 := by
    have ha : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (a + 24#64) g.ctPtr ctLen
  have h2 : ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ⊢ memRegion (a + 40#64) 16 := by
    have ha : (a + 40#64) + 8#64 = a + 48#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (a + 40#64) g.serPtr serLen
  have h4 : ((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL) ⊢ memRegion (a + 88#64) 16 := by
    have ha : (a + 88#64) + 8#64 = a + 96#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (a + 88#64) addrP addrL
  have hgroup :
      ((a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
        ((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ∗
        memRegion (a + 56#64) 32 ∗
        ((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL) ∗
        memRegion (a + 104#64) 16) =
      (((a ↦₆₄ g.pqCap) ∗ ((a + 8#64) ↦₆₄ g.pqPtr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen)) ∗
       (((a + 40#64) ↦₆₄ g.serPtr) ∗ ((a + 48#64) ↦₆₄ serLen)) ∗
       memRegion (a + 56#64) 32 ∗
       (((a + 88#64) ↦₆₄ addrP) ∗ ((a + 96#64) ↦₆₄ addrL)) ∗
       memRegion (a + 104#64) 16) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 96) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 16) (k := 80) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 16) (k := 64) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 32) (k := 32) (b' := a + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 88#64) (n := 16) (k := 16) (b' := a + 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right (sepConj_mono_left h4))))

private theorem signalMessageAt_entails_dealloc (A : RustAlloc) (g : SignalMessageGhost)
    (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt A g a m ⊢
      ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64, ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
        ⌜g.pqCap.toNat < 2 ^ 63⌝ ∗
        smHeadersAt a g ctLen serLen addrP addrL ∗
        vecPinDealloc A ⟨ctLen, g.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.serPtr⟩ := by
  unfold signalMessageAt
  apply Entails.pure_left; intro _
  have hpq := vecU8At_entails_pin_dealloc_bound A a ⟨g.pqCap, g.pqPtr⟩ m.pqRatchet
  have hct := boxU8At_entails_dealloc A (a + 24#64) g.ctPtr m.ciphertext
  have hser := boxU8At_entails_dealloc A (a + 40#64) g.serPtr m.serialized
  have hsrk := vec32_entails_memRegion_32 (a + 56#64) m.senderRatchetKey.bytes
  have haddr := optBoxU8At_entails_dealloc A (a + 88#64) g.addrPtr m.addresses
  have htail :
      ((a + 104#64) ↦₃₂ m.counter) ∗ ((a + 108#64) ↦₃₂ m.previousCounter) ∗
        ((a + 112#64) ↦₈ m.messageVersion) ∗ memRegion (a + 113#64) 7 ⊢
      memRegion (a + 104#64) 16 := by
    have ha1 : (a + 104#64) + 4#64 = a + 108#64 := by bv_omega
    have ha2 : (a + 104#64) + 8#64 = a + 112#64 := by bv_omega
    have ha3 : (a + 104#64) + 9#64 = a + 113#64 := by bv_omega
    simpa [ha1, ha2, ha3] using u32x2_u8_pad7_entails_memRegion_16 (a + 104#64) m.counter m.previousCounter m.messageVersion
  refine Entails.trans (sepConj_mono hpq (sepConj_mono hct (sepConj_mono hser (sepConj_mono hsrk (sepConj_mono haddr htail))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro addrP
  apply Entails.sepExists_elim; intro addrL
  apply Entails.sepExists_elim; intro serLen
  apply Entails.sepExists_elim; intro ctLen
  refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
    (Entails.sepExists_right addrP (Entails.sepExists_right addrL ?_)))
  unfold smHeadersAt
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h48 : (a + 40#64) + 8#64 = a + 48#64 := by bv_omega
  have h96 : (a + 88#64) + 8#64 = a + 96#64 := by bv_omega
  rw [h32, h48, h96]
  exact Entails.of_eq (by ac_rfl)

@[reducible]
private def sigHeadersAt (p : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) : SepProp :=
  (p ↦₆₄ ctSignalTag) ∗
  ((p + 8#64) ↦₆₄ g.pqCap) ∗ ((p + 16#64) ↦₆₄ g.pqPtr) ∗ memRegion (p + 24#64) 8 ∗
  ((p + 32#64) ↦₆₄ g.ctPtr) ∗ ((p + 40#64) ↦₆₄ ctLen) ∗
  ((p + 48#64) ↦₆₄ g.serPtr) ∗ ((p + 56#64) ↦₆₄ serLen) ∗
  memRegion (p + 64#64) 32 ∗
  ((p + 96#64) ↦₆₄ addrP) ∗ ((p + 104#64) ↦₆₄ addrL) ∗
  memRegion (p + 112#64) 16 ∗
  memRegion (p + 128#64) 120

private theorem sigHeadersAt_eq (p : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) :
    (p ↦₆₄ ctSignalTag) ∗ smHeadersAt (p + 8#64) g ctLen serLen addrP addrL ∗
      memRegion (p + 128#64) 120 =
    sigHeadersAt p g ctLen serLen addrP addrL := by
  unfold smHeadersAt sigHeadersAt
  have h16 : (p + 8#64) + 8#64 = p + 16#64 := by bv_omega
  have h24 : (p + 8#64) + 16#64 = p + 24#64 := by bv_omega
  have h32 : (p + 8#64) + 24#64 = p + 32#64 := by bv_omega
  have h40 : (p + 8#64) + 32#64 = p + 40#64 := by bv_omega
  have h48 : (p + 8#64) + 40#64 = p + 48#64 := by bv_omega
  have h56 : (p + 8#64) + 48#64 = p + 56#64 := by bv_omega
  have h64 : (p + 8#64) + 56#64 = p + 64#64 := by bv_omega
  have h96 : (p + 8#64) + 88#64 = p + 96#64 := by bv_omega
  have h104 : (p + 8#64) + 96#64 = p + 104#64 := by bv_omega
  have h112 : (p + 8#64) + 104#64 = p + 112#64 := by bv_omega
  rw [h16, h24, h32, h40, h48, h56, h64, h96, h104, h112]
  ac_rfl

private theorem sigHeadersAt_entails_memRegion_248 (p : BitVec 64) (g : SignalMessageGhost)
    (ctLen serLen addrP addrL : BitVec 64) :
    sigHeadersAt p g ctLen serLen addrP addrL ⊢ memRegion p 248 := by
  rw [← sigHeadersAt_eq p g ctLen serLen addrP addrL,
      ProofLib.memRegion_split' (b := p) (n := 8) (k := 240) (b' := p + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 120) (k := 120) (b' := p + 128#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p ctSignalTag)
    (sepConj_mono_left (smHeadersAt_entails_memRegion_120 (p + 8#64) g ctLen serLen addrP addrL))

private theorem apiEncResultAt_signal_entails_dealloc (A : RustAlloc) (p : BitVec 64)
    (m : SignalMessage) :
    apiEncResultAt A p (.ok (.signalMessage m)) ⊢
      ∃∗ g : SignalMessageGhost, ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64,
      ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
        sigHeadersAt p g ctLen serLen addrP addrL ∗
        vecPinDealloc A ⟨ctLen, g.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.serPtr⟩ := by
  dsimp only [apiEncResultAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  have hsm : signalMessageAt A g (p + 8#64) m ⊢
      ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64, ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
        smHeadersAt (p + 8#64) g ctLen serLen addrP addrL ∗
        vecPinDealloc A ⟨ctLen, g.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.serPtr⟩ := by
    refine Entails.trans (signalMessageAt_entails_dealloc A g (p + 8#64) m) ?_
    apply Entails.sepExists_elim; intro ctLen
    apply Entails.sepExists_elim; intro serLen
    apply Entails.sepExists_elim; intro addrP
    apply Entails.sepExists_elim; intro addrL
    refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
      (Entails.sepExists_right addrP (Entails.sepExists_right addrL ?_)))
    exact Entails.pure_left fun _ => Entails.refl _
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hsm)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ctLen
  apply Entails.sepExists_elim; intro serLen
  apply Entails.sepExists_elim; intro addrP
  apply Entails.sepExists_elim; intro addrL
  refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
    (Entails.sepExists_right addrP (Entails.sepExists_right addrL ?_)))
  rw [← sigHeadersAt_eq p g ctLen serLen addrP addrL]
  exact Entails.of_eq (by ac_rfl)

@[reducible]
private def preKeyMsgHeadersAt (p : BitVec 64) (g : PreKeyMsgGhost)
    (ctLen serLen addrP addrL pserLen kyP kyL : BitVec 64) : SepProp :=
  smHeadersAt p g.msg ctLen serLen addrP addrL ∗
  memRegion (p + 120#64) 8 ∗
  ((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen) ∗
  ((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL) ∗
  memRegion (p + 160#64) 88

private theorem preKeyMsgHeadersAt_entails_memRegion_248 (p : BitVec 64) (g : PreKeyMsgGhost)
    (ctLen serLen addrP addrL pserLen kyP kyL : BitVec 64) :
    preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ⊢ memRegion p 248 := by
  unfold preKeyMsgHeadersAt
  have hsm := smHeadersAt_entails_memRegion_120 p g.msg ctLen serLen addrP addrL
  have hser : ((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen) ⊢ memRegion (p + 128#64) 16 := by
    have ha : (p + 128#64) + 8#64 = p + 136#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (p + 128#64) g.serPtr pserLen
  have hky : ((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL) ⊢ memRegion (p + 144#64) 16 := by
    have ha : (p + 144#64) + 8#64 = p + 152#64 := by bv_omega
    simpa [ha] using u64x2_entails_memRegion_16 (p + 144#64) kyP kyL
  have hgroup :
      (smHeadersAt p g.msg ctLen serLen addrP addrL ∗
        memRegion (p + 120#64) 8 ∗
        ((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen) ∗
        ((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL) ∗
        memRegion (p + 160#64) 88) =
      (smHeadersAt p g.msg ctLen serLen addrP addrL ∗
        memRegion (p + 120#64) 8 ∗
        (((p + 128#64) ↦₆₄ g.serPtr) ∗ ((p + 136#64) ↦₆₄ pserLen)) ∗
        (((p + 144#64) ↦₆₄ kyP) ∗ ((p + 152#64) ↦₆₄ kyL)) ∗
        memRegion (p + 160#64) 88) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := p) (n := 120) (k := 128) (b' := p + 120#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := p + 120#64) (n := 8) (k := 120) (b' := p + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 128#64) (n := 16) (k := 104) (b' := p + 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 144#64) (n := 16) (k := 88) (b' := p + 160#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono hsm (sepConj_mono_right (sepConj_mono hser (sepConj_mono_left hky)))

private theorem preKeyMsgAt_entails_dealloc (A : RustAlloc) (g : PreKeyMsgGhost)
    (p : BitVec 64) (m : PreKeySignalMessage) :
    preKeyMsgAt A g p m ⊢
      ∃∗ ctLen : BitVec 64, ∃∗ serLen : BitVec 64, ∃∗ addrP : BitVec 64, ∃∗ addrL : BitVec 64,
      ∃∗ pserLen : BitVec 64, ∃∗ kyP : BitVec 64, ∃∗ kyL : BitVec 64,
        ⌜g.msg.pqCap.toNat < 2 ^ 63⌝ ∗
        preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
        optBoxDealloc A kyP kyL ∗
        vecPinDealloc A ⟨ctLen, g.msg.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.msg.pqCap, g.msg.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.msg.serPtr⟩ ∗
        vecPinDealloc A ⟨pserLen, g.serPtr⟩ := by
  unfold preKeyMsgAt
  have hsm := signalMessageAt_entails_dealloc A g.msg p m.message
  have hpk := optU32At_entails_memRegion_8 (p + 120#64) m.preKeyId
  have hpser := boxU8At_entails_dealloc A (p + 128#64) g.serPtr m.serialized
  have hky := optKyberAt_entails_dealloc A (p + 144#64) g.kyberPtr m.kyberPayload
  have hbk := vec32_entails_memRegion_32 (p + 168#64) m.baseKey.bytes
  have hik := vec32_entails_memRegion_32 (p + 200#64) m.identityKey.publicKey.bytes
  have htail :
      ((p + 232#64) ↦₃₂ m.registrationId) ∗ ((p + 236#64) ↦₃₂ m.signedPreKeyId) ∗
        ((p + 240#64) ↦₈ m.messageVersion) ∗ memRegion (p + 241#64) 7 ⊢
      memRegion (p + 232#64) 16 := by
    have ha1 : (p + 232#64) + 4#64 = p + 236#64 := by bv_omega
    have ha2 : (p + 232#64) + 8#64 = p + 240#64 := by bv_omega
    have ha3 : (p + 232#64) + 9#64 = p + 241#64 := by bv_omega
    simpa [ha1, ha2, ha3] using u32x2_u8_pad7_entails_memRegion_16 (p + 232#64) m.registrationId m.signedPreKeyId m.messageVersion
  refine Entails.trans (sepConj_mono hsm (sepConj_mono hpk (sepConj_mono hpser (sepConj_mono hky (sepConj_mono hbk (sepConj_mono hik htail)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kyP
  apply Entails.sepExists_elim; intro kyL
  apply Entails.sepExists_elim; intro pserLen
  apply Entails.sepExists_elim; intro ctLen
  apply Entails.sepExists_elim; intro serLen
  apply Entails.sepExists_elim; intro addrP
  apply Entails.sepExists_elim; intro addrL
  refine Entails.sepExists_right ctLen (Entails.sepExists_right serLen
    (Entails.sepExists_right addrP (Entails.sepExists_right addrL
      (Entails.sepExists_right pserLen (Entails.sepExists_right kyP (Entails.sepExists_right kyL ?_))))))
  unfold preKeyMsgHeadersAt
  have h136 : (p + 128#64) + 8#64 = p + 136#64 := by bv_omega
  have h152 : (p + 144#64) + 8#64 = p + 152#64 := by bv_omega
  have h160 : (p + 144#64) + 16#64 = p + 160#64 := by bv_omega
  have hm88 :
      memRegion (p + 160#64) 88 =
        memRegion (p + 160#64) 8 ∗ (memRegion (p + 168#64) 32 ∗ (memRegion (p + 200#64) 32 ∗ memRegion (p + 232#64) 16)) := by
    rw [ProofLib.memRegion_split' (b := p + 160#64) (n := 8) (k := 80) (b' := p + 168#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := p + 168#64) (n := 32) (k := 48) (b' := p + 200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := p + 200#64) (n := 32) (k := 16) (b' := p + 232#64) rfl (by bv_omega) (by decide)]
  rw [h136, h152, h160, hm88]
  exact Entails.of_eq (by ac_rfl)

private theorem cm_cap0_weaken {Hdr : SepProp} (p : BitVec 64)
    (hHdr : Hdr ⊢ memRegion p 248)
    (Pool : SepProp) (sp fp lr x20 x19 : BitVec 64) :
    Hdr ∗ Pool ∗
      stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
      memRegion (sp - 4160#64) 32 ⊢
    memRegion p 248 ∗ Pool ∗ (memRegion (sp - 4160#64) 32 ∗ stackAt sp cmActiveStack) := by
  have hst := stack_restore_32_cm sp fp lr x20 x19
  have hgroup :
      (Hdr ∗ Pool ∗
        stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
        memRegion (sp - 4160#64) 32) =
      (Hdr ∗ Pool ∗ memRegion (sp - 4160#64) 32 ∗
        (stackAt (sp - 32#64) allocHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono hHdr (sepConj_mono_right (sepConj_mono_right hst))

private theorem cm_tail_dealloc_pre_weaken {Hdr : SepProp} (p : BitVec 64)
    (hHdr : Hdr ⊢ memRegion p 248)
    (Live Pool : SepProp) (sp fp lr x20 x19 : BitVec 64) :
    Hdr ∗ Live ∗ Pool ∗
      stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
      memRegion (sp - 4160#64) 32 ⊢
    memRegion p 248 ∗ Live ∗ Pool ∗
      memRegion (sp - 4128#64) 32 ∗ memRegion (sp - 4160#64) 32 ∗ stackAt sp allocHookStack := by
  have hst := cells4_entails_stack_bottom sp fp lr x20 x19
  have hgroup :
      (Hdr ∗ Live ∗ Pool ∗
        stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ∗
        memRegion (sp - 4160#64) 32) =
      (Hdr ∗ Live ∗ Pool ∗ memRegion (sp - 4160#64) 32 ∗
        (stackAt (sp - 32#64) allocHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono hHdr (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hst)))) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem cm_tail_dealloc_post (p : BitVec 64) (Pool : SepProp) (sp : BitVec 64) :
    Pool ∗ stackAt sp allocHookStack ∗ memRegion p 248 ∗
      memRegion (sp - 4128#64) 32 ∗ memRegion (sp - 4160#64) 32 ⊢
    memRegion p 248 ∗ Pool ∗ (memRegion (sp - 4160#64) 32 ∗ stackAt sp cmActiveStack) := by
  rw [stackAt_cmActive_split sp, ← tail_stack_32_from_bottom sp]
  exact Entails.of_eq (by ac_rfl)

private theorem SepWP.align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) :=
  heq ▸ h

attribute [local semireducible] SepWP in

private theorem SepWP.pure_elim_left {prog : Program} {target : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog target s P post) :
    SepWP prog target s (⌜φ⌝ ∗ P) post := by
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

attribute [local arm64_norm] conditionHolds_mi_subsPState64 conditionHolds_eq_subsPState64

private theorem msb_eq_false_of_lt {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap.msb = false := by
  rw [BitVec.msb_eq_false_iff_two_mul_lt]
  omega

private theorem fnAddr_tripleRatchetProgAt {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (tripleRatchetProgAt b C ctl abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, h]

private theorem fnAddr_trTrapProgAt {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (trTrapProgAt b C abs).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, h]

private theorem fnAddr_trExtProgAt {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {off : Nat}
    (h : libsignalSessionCode.fnOff name = off) :
    (tripleRatchetProgAtExt b ext).fnAddr name = b + BitVec.ofNat 64 off := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, h]

set_option maxHeartbeats 1600000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_fn_ok_ext
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDropName)
      (cmDropSpec A) := by
  simp only [cmDropSpec, stackAt_cmDrop_outer]
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDropName = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]") := by
    fnoff_eq
  have hdealloc := dealloc_ok_at_ext b A ext hA
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDropName
    (num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]")))
    (by fnoff_eq)
  simp only [rustDeallocSpec] at hdealloc
  code_fetches CryptoVerification.libsignalSessionCode cmDropBinCli b
    (Rust.withPanics ext) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]") 384
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDropName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨p, m⟩ := x
  dsimp only at *
  subst h
  let p := s0.readReg64 (Reg.gpr 0#5)
  nth_rw 1 [stackAt_cmActive_split s0.sp]
  cells_unfold
  wp_pull_exists
  cases m with
  | signalMessage sm =>
    refine SepWP.weaken_pre (sepConj_mono_left (apiEncResultAt_signal_entails_dealloc A p sm)) ?_
    wp_pull_exists
    rename_i g ctLen serLen addrP addrL
    refine seq_clean (mid := entry + 264#64) (P_mid :=
      (sigHeadersAt p g ctLen serLen addrP addrL ∗
        vecPinDealloc A ⟨g.pqCap, g.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.serPtr⟩) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
       memRegion (s0.sp - 4160#64) 32))
      (Q := fun s1 => Saved32Preserved s0 s1 (s0.sp - 32#64) ∧ s1.readReg64 .x19 = p)
      ?_ ?_
    · dsimp only [sigHeadersAt, ctSignalTag, vecPinDealloc]
      by_cases hct : (ctLen == 0#64) = true <;>
        simp only [hct, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.align_pre (by ac_rfl) ?_
        wp_done
      · wp_steps
        wp_apply
        refine SepWP.align_pre (by ac_rfl) ?_
        wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1, hsp_1, htrace_1⟩, hx19_1⟩
      refine seq_clean (mid := entry + 284#64) (P_mid :=
        (sigHeadersAt p g ctLen serLen addrP addrL ∗
          optBoxDealloc A addrP addrL ∗
          vecPinDealloc A ⟨serLen, g.serPtr⟩) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
         memRegion (s0.sp - 4160#64) 32))
        (Q := fun s2 => Saved32Preserved s0 s2 (s0.sp - 32#64) ∧ s2.readReg64 .x19 = p)
        ?_ ?_
      · dsimp only [sigHeadersAt, vecPinDealloc]
        by_cases hpq : (g.pqCap == 0#64) = true <;>
          simp only [hpq, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_apply
          refine SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
          wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2, hsp_2, htrace_2⟩, hx19_2⟩
        refine seq_clean (mid := entry + 308#64) (P_mid :=
          (sigHeadersAt p g ctLen serLen addrP addrL ∗
            vecPinDealloc A ⟨serLen, g.serPtr⟩) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
           ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
           ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
           memRegion (s0.sp - 4160#64) 32))
          (Q := fun s3 => Saved32Preserved s0 s3 (s0.sp - 32#64) ∧ s3.readReg64 .x19 = p)
          ?_ ?_
        · dsimp only [sigHeadersAt, optBoxDealloc, vecPinDealloc]
          by_cases hp0 : (addrP == 0#64) = true <;>
            simp only [hp0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            wp_done
          · by_cases hl0 : (addrL == 0#64) = true <;>
              simp only [hl0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              wp_done
            · wp_steps
              wp_apply
              refine SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
              wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hvregs_3, hsp_3, htrace_3⟩, hx19_3⟩
          dsimp only [sigHeadersAt, vecPinDealloc]
          by_cases hser : (serLen == 0#64) = true <;>
            simp only [hser, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            have hpost := cm_cap0_weaken p (sigHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL)
              A.pool s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
            dsimp only [sigHeadersAt] at hpost
            refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hpost) ?_
            wp_done
          · wp_steps
            have hpre := cm_tail_dealloc_pre_weaken p (sigHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL)
              (A.live g.serPtr serLen.toNat 1 ∗ memRegion g.serPtr serLen.toNat)
              A.pool s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
            dsimp only [sigHeadersAt] at hpre
            refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hpre) ?_
            wp_apply
            refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) (cm_tail_dealloc_post p A.pool s0.sp)) ?_
            wp_done
  | preKeySignalMessage psm =>
    dsimp only [apiEncResultAt]
    wp_pull_exists
    rename_i g
    refine SepWP.weaken_pre (sepConj_mono_left (preKeyMsgAt_entails_dealloc A g p psm)) ?_
    wp_pull_exists
    rename_i ctLen serLen addrP addrL pserLen kyP kyL
    refine SepWP.pure_elim_left fun hpq_lt => ?_
    have hmsb : g.msg.pqCap.msb = false := msb_eq_false_of_lt hpq_lt
    refine seq_clean (mid := entry + 128#64) (P_mid :=
      (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
        vecPinDealloc A ⟨ctLen, g.msg.ctPtr⟩ ∗
        vecPinDealloc A ⟨g.msg.pqCap, g.msg.pqPtr⟩ ∗
        optBoxDealloc A addrP addrL ∗
        vecPinDealloc A ⟨serLen, g.msg.serPtr⟩ ∗
        vecPinDealloc A ⟨pserLen, g.serPtr⟩) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
       memRegion (s0.sp - 4160#64) 32))
      (Q := fun s1 => Saved32Preserved s0 s1 (s0.sp - 32#64) ∧
        s1.readReg64 .x19 = p ∧ s1.readReg64 .x20 = g.msg.pqCap)
      ?_ ?_
    · dsimp only [preKeyMsgHeadersAt, smHeadersAt, optBoxDealloc, vecPinDealloc]
      by_cases hkyP : (kyP == 0#64) = true <;>
        simp only [hkyP, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.align_pre (by ac_rfl) ?_
        wp_done
      · by_cases hkyL : (kyL == 0#64) = true <;>
          simp only [hkyL, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.align_pre (by ac_rfl) ?_
          wp_done
        · wp_steps
          wp_apply
          refine SepWP.align_pre (by ac_rfl) ?_
          wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1, hsp_1, htrace_1⟩, hx19_1, hx20_1⟩
      refine seq_clean (mid := entry + 148#64) (P_mid :=
        (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
          vecPinDealloc A ⟨g.msg.pqCap, g.msg.pqPtr⟩ ∗
          optBoxDealloc A addrP addrL ∗
          vecPinDealloc A ⟨serLen, g.msg.serPtr⟩ ∗
          vecPinDealloc A ⟨pserLen, g.serPtr⟩) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
         memRegion (s0.sp - 4160#64) 32))
        (Q := fun s2 => Saved32Preserved s0 s2 (s0.sp - 32#64) ∧
          s2.readReg64 .x19 = p ∧ s2.readReg64 .x20 = g.msg.pqCap)
        ?_ ?_
      · dsimp only [preKeyMsgHeadersAt, smHeadersAt, vecPinDealloc]
        by_cases hct : (ctLen == 0#64) = true <;>
          simp only [hct, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_apply
          refine SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
          wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2, hsp_2, htrace_2⟩, hx19_2, hx20_2⟩
        refine seq_clean (mid := entry + 168#64) (P_mid :=
          (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
            optBoxDealloc A addrP addrL ∗
            vecPinDealloc A ⟨serLen, g.msg.serPtr⟩ ∗
            vecPinDealloc A ⟨pserLen, g.serPtr⟩) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
           ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
           ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
           memRegion (s0.sp - 4160#64) 32))
          (Q := fun s3 => Saved32Preserved s0 s3 (s0.sp - 32#64) ∧ s3.readReg64 .x19 = p)
          ?_ ?_
        · dsimp only [preKeyMsgHeadersAt, smHeadersAt, vecPinDealloc]
          by_cases hpq : (g.msg.pqCap == 0#64) = true <;>
            simp only [hpq, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            wp_done
          · wp_steps
            wp_apply
            refine SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
            wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hvregs_3, hsp_3, htrace_3⟩, hx19_3⟩
          refine seq_clean (mid := entry + 192#64) (P_mid :=
            (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
              vecPinDealloc A ⟨serLen, g.msg.serPtr⟩ ∗
              vecPinDealloc A ⟨pserLen, g.serPtr⟩) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
             memRegion (s0.sp - 4160#64) 32))
            (Q := fun s4 => Saved32Preserved s0 s4 (s0.sp - 32#64) ∧ s4.readReg64 .x19 = p)
            ?_ ?_
          · dsimp only [preKeyMsgHeadersAt, smHeadersAt, optBoxDealloc, vecPinDealloc]
            by_cases hp0 : (addrP == 0#64) = true <;>
              simp only [hp0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              wp_done
            · by_cases hl0 : (addrL == 0#64) = true <;>
                simp only [hl0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · wp_steps
                wp_done
              · wp_steps
                wp_apply
                refine SepWP.align_pre (by rw [hsp_3]; ac_rfl) ?_
                wp_done
          · intro s4 hpc4 hrun4 ⟨⟨hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hvregs_4, hsp_4, htrace_4⟩, hx19_4⟩
            refine seq_clean (mid := entry + 212#64) (P_mid :=
              (preKeyMsgHeadersAt p g ctLen serLen addrP addrL pserLen kyP kyL ∗
                vecPinDealloc A ⟨pserLen, g.serPtr⟩) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x29) ∗
               ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x30) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
               ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
               memRegion (s0.sp - 4160#64) 32))
              (Q := fun s5 => Saved32Preserved s0 s5 (s0.sp - 32#64) ∧ s5.readReg64 .x19 = p)
              ?_ ?_
            · dsimp only [preKeyMsgHeadersAt, smHeadersAt, vecPinDealloc]
              by_cases hser : (serLen == 0#64) = true <;>
                simp only [hser, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · wp_steps
                wp_done
              · wp_steps
                wp_apply
                refine SepWP.align_pre (by rw [hsp_4]; ac_rfl) ?_
                wp_done
            · intro s5 hpc5 hrun5 ⟨⟨hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hvregs_5, hsp_5, htrace_5⟩, hx19_5⟩
              dsimp only [preKeyMsgHeadersAt, smHeadersAt, vecPinDealloc]
              by_cases hpser : (pserLen == 0#64) = true <;>
                simp only [hpser, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
              · wp_steps
                have hpost := cm_cap0_weaken p (preKeyMsgHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL pserLen kyP kyL)
                  A.pool s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
                dsimp only [preKeyMsgHeadersAt, smHeadersAt] at hpost
                refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hpost) ?_
                wp_done
              · wp_steps
                have hpre := cm_tail_dealloc_pre_weaken p (preKeyMsgHeadersAt_entails_memRegion_248 p g ctLen serLen addrP addrL pserLen kyP kyL)
                  (A.live g.serPtr pserLen.toNat 1 ∗ memRegion g.serPtr pserLen.toNat)
                  A.pool s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x20) (s0.readReg64 .x19)
                dsimp only [preKeyMsgHeadersAt, smHeadersAt] at hpre
                refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hpre) ?_
                wp_apply
                refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) (cm_tail_dealloc_post p A.pool s0.sp)) ?_
                wp_done

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_fn_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDropName)
      (cmDropSpec A) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_fn_ok_ext
    ((CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.allocHooks_trTrap_iff C A abs).mpr hA)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_fn_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDropName)
      (cmDropSpec A) :=
  subroutine_ok_kit_of_trTrap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_fn_ok_trap hA)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_ok_ext
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) (_himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]"))
      (cmDropSpec A) := by
  have h := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_fn_ok_ext (b := img.base) hA
  rwa [fnAddr_trExtProgAt (off := (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]")) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]")] at h

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {abs : String → Option (State → State)} (h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_trap img C A abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_ok_ext h3.alloc himg

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} (h3 : PublicApiHooks C A S encRecord abs)
    (_himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk img C A ctl abs := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk
  have h := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_fn_ok (b := img.base) (C := C) (ctl := ctl) h3.alloc
  rwa [fnAddr_tripleRatchetProgAt (off := (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]")) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#2]")] at h

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop
