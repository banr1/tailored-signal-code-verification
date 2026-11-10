/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.KeysCodeSym
public import LibsignalBinary.Proofs.CodeLayout
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WPp

/-!
# Verification of `<PrivateKey>::calculate_agreement`

Verifies `<libsignal_core::curve::PrivateKey>::calculate_agreement` (X25519 scalar clamping,
Diffie-Hellman agreement, constant-time all-zero check, heap `Box<[u8]>` allocation, and
stack zeroization) on both rebased images and relocatable `[LibsignalPlacement]` blocks.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Keys

open Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement") → (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 220)]

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Frozen-image stepping invariant helpers -/

structure FrozenInv (img : Obj.Image) (s : State) : Prop where
  frozen : img.FrozenLoaded s
  symtab : s.symtab = img.symtab

theorem FrozenInv.of_steps {prog : Program} {img : Obj.Image} {s sf : State}
    (h : FrozenInv img s) (hsteps : Steps prog s sf) : FrozenInv img sf :=
  ⟨h.1.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans h.2⟩

theorem SepWPp.of_sepWP_frozen {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (h : SepWP prog mid s P
      (fun sm Pm => FrozenInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hF.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

@[irreducible] def frozenStop (pc : BitVec 64) : BitVec 64 := pc

theorem SepWP.of_sepWP_frozen {prog : Program} {img : Obj.Image} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (h : SepWP prog (frozenStop mid) s P
      (fun sm Pm => FrozenInv img sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold frozenStop at h
  exact _root_.ProofLib.SepWP.of_sepWP_frozen hF.1 hF.2
    (_root_.ProofLib.SepWP.mono h fun _ _ _ _ hnext hfz hsym => hnext ⟨hfz, hsym⟩)

theorem SepWP.done_frozen {prog : Program} {mid : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running) (hpost : post s P) :
    SepWP prog (frozenStop mid) s P post := by
  unfold frozenStop
  exact SepWP.done hpc hrun hpost

theorem subroutine_ok_inImage_rodata' {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr : BitVec 64} {roBytes : List (BitVec 8)} {spec : Spec α}
    (hro_intro : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr ↦ᵣ roBytes) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜FrozenInv img s⌝ ∗ (roAddr ↦ᵣ roBytes) ∗ spec.pre x s
        post := fun x s0 sf => (roAddr ↦ᵣ roBytes) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨ (⌜FrozenInv img s0⌝ ∗ (roAddr ↦ᵣ roBytes) ∗ spec.pre x s0) ∗ R := by
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hL.1, hL.2⟩, hro_intro hL.1.roData hpre⟩
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq
    rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr hoom))

namespace AgreeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem dh_fnOff : libsignalSessionCode.fnOff dhName = num% (ls_off% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman")

theorem sharedDrop_fnOff : libsignalSessionCode.fnOff sharedDropName = num% (ls_off% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop")

theorem staticDrop_fnOff : libsignalSessionCode.fnOff staticDropName = num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")

theorem handleAllocError_fnOff : libsignalSessionCode.fnOff handleAllocErrorName = num% (ls_off% "alloc::alloc::handle_alloc_error") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "alloc::alloc::handle_alloc_error")

theorem ctEq_fnOff : libsignalSessionCode.fnOff ctEqName = num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")

theorem calculateAgreement_fnOff : libsignalSessionCode.fnOff calculateAgreementName = num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement")

end AgreeStateSimp

open AgreeStateSimp

theorem rodata_0x49f6a {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 104) (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 108))) ↦ᵣ List.replicate 32 0#8) ∗ P := by
  have hsec : (num% (ls_xref% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 104) (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 108)), 32) ∈ libsignalSessionImage.roData :=
    List.mem_of_elem_eq_true (by rfl_kernel)
  have ⟨h1, h2⟩ := rodata_readBytes_disjoint himg (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44))) rfl hsec
    (by decide) (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) m hro
  have hbytes : (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 104) (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 108)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 32 =
      List.replicate 32 0#8 := by rfl_kernel
  rw [hbytes] at h2
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem zeroize32_hookOk : HookOk zeroizeSecretHook zeroizeSecretSpec := by
  refine retHook_ok fun a R s0 _ hpre _ => ?_
  simp only [zeroizeSecretSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hmem⟩
  have hlen : (List.replicate 32 0#8).length = 32 := by decide
  have hmem' : s0.mem ⊨ memRegion a (List.replicate 32 0#8).length ∗ R := by
    rwa [hlen]
  have hle : (List.replicate 32 0#8).length ≤ 2 ^ 64 := by decide
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · rw [hx0]
    exact keepsFrozen_writeBytes_of_memRegion (List.replicate 32 0#8) hle hmem'
  · simp only [zeroizeSecretSpec, retHook,
      State.trace_setPC, State.trace_setMem, State.mem_setMem, hx0,
      sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_writeBytes (List.replicate 32 0#8) hle hmem'

theorem dh_ok_at_tripleRatchet_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dhName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (diffieHellmanSpec C.X) :=
  dh_ok_at_trap b C abs name k hk

theorem dh_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff dhName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (diffieHellmanSpec C.X) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (dh_ok_at_tripleRatchet_trap (b := b) (C := C) (abs := abs) hk)

theorem sharedDrop_ok_at_tripleRatchet_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff sharedDropName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      zeroizeSecretSpec :=
  shared_drop_ok_at_trap b C abs name k hk

theorem sharedDrop_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff sharedDropName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      zeroizeSecretSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (sharedDrop_ok_at_tripleRatchet_trap (b := b) (C := C) (abs := abs) hk)

theorem staticDrop_ok_at_tripleRatchet_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff staticDropName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      zeroizeSecretSpec :=
  static_drop_ok_at_trap b C abs name k hk

theorem staticDrop_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff staticDropName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      zeroizeSecretSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (staticDrop_ok_at_tripleRatchet_trap (b := b) (C := C) (abs := abs) hk)

theorem sub_ok_at_rebase {α : Type} {b : BitVec 64}
    {H : String → Option (State → State)} {spec : Spec α}
    {name callee : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr callee) spec) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k) spec := by
  rwa [← Program.fnAddr_rel rfl rfl hk]

theorem panic_at_handle_alloc_error_rebase {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff handleAllocErrorName := by fnoff_eq) :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (hname := handleAllocErrorName) rfl hk
    (by rw [handleAllocError_fnOff]; decide)
    (fun H => by rw [handleAllocError_fnOff]; exact (ls_hook% "alloc::alloc::handle_alloc_error") H)
    (by decide +kernel)

theorem panic_at_handle_alloc_error2_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff handleAllocErrorName := by fnoff_eq) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_alloc_error_trap b C abs name k hk

theorem panic_at_handle_alloc_error2 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff handleAllocErrorName := by fnoff_eq) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_alloc_error b C ctl abs name k hk

/-! ## Unaligned overlapping views and X25519 scalar clamping -/

def w1_8 (v : List.Vector (BitVec 8) 32) : BitVec 64 :=
  pack64 (v.get 1) (v.get 2) (v.get 3) (v.get 4) (v.get 5) (v.get 6) (v.get 7) (v.get 8)

def w9_16 (v : List.Vector (BitVec 8) 32) : BitVec 64 :=
  pack64 (v.get 9) (v.get 10) (v.get 11) (v.get 12) (v.get 13) (v.get 14) (v.get 15) (v.get 16)

def w15_22 (v : List.Vector (BitVec 8) 32) : BitVec 64 :=
  pack64 (v.get 15) (v.get 16) (v.get 17) (v.get 18) (v.get 19) (v.get 20) (v.get 21) (v.get 22)

def w23_30 (v : List.Vector (BitVec 8) 32) : BitVec 64 :=
  pack64 (v.get 23) (v.get 24) (v.get 25) (v.get 26) (v.get 27) (v.get 28) (v.get 29) (v.get 30)

def b1_14 (v : List.Vector (BitVec 8) 32) : List (BitVec 8) :=
  [v.get 1, v.get 2, v.get 3, v.get 4, v.get 5, v.get 6, v.get 7,
   v.get 8, v.get 9, v.get 10, v.get 11, v.get 12, v.get 13, v.get 14]

def b17_31 (v : List.Vector (BitVec 8) 32) : List (BitVec 8) :=
  [v.get 17, v.get 18, v.get 19, v.get 20, v.get 21, v.get 22, v.get 23,
   v.get 24, v.get 25, v.get 26, v.get 27, v.get 28, v.get 29, v.get 30, v.get 31]

theorem vec32_toList_eq (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get 0] ++
      ([v.get 1, v.get 2, v.get 3, v.get 4, v.get 5, v.get 6, v.get 7, v.get 8] ++
      ([v.get 9, v.get 10, v.get 11, v.get 12, v.get 13, v.get 14, v.get 15, v.get 16] ++
      b17_31 v)) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  rfl

theorem vec32_toList_eq2 (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get 0] ++ (b1_14 v ++
      ([v.get 15, v.get 16, v.get 17, v.get 18, v.get 19, v.get 20, v.get 21, v.get 22] ++
      ([v.get 23, v.get 24, v.get 25, v.get 26, v.get 27, v.get 28, v.get 29, v.get 30] ++
      [v.get 31]))) := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  rfl

theorem vec32_view1 (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ v.toList) =
      (a ↦₈ v.get 0) ∗ ((a + 1#64) ↦₆₄ w1_8 v) ∗
        ((a + 9#64) ↦₆₄ w9_16 v) ∗ ((a + 17#64) ↦ₛ b17_31 v) := by
  conv_lhs => rw [vec32_toList_eq v]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  rw [pointsToBytes_singleton, pointsToBytes8_eq_pointsTo64, pointsToBytes8_eq_pointsTo64]
  change (a ↦₈ v.get 0) ∗
    (((a + 1#64) ↦₆₄ w1_8 v) ∗
      (((a + 1#64 + 8#64) ↦₆₄ w9_16 v) ∗ ((a + 1#64 + 8#64 + 8#64) ↦ₛ b17_31 v))) = _
  have h9 : a + 1#64 + 8#64 = a + 9#64 := by bv_kernel
  have h17 : a + 9#64 + 8#64 = a + 17#64 := by bv_kernel
  rw [h9, h17]

theorem vec32_view2 (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ v.toList) =
      (a ↦₈ v.get 0) ∗ ((a + 1#64) ↦ₛ b1_14 v) ∗
        ((a + 15#64) ↦₆₄ w15_22 v) ∗ ((a + 23#64) ↦₆₄ w23_30 v) ∗
        ((a + 31#64) ↦₈ v.get 31) := by
  conv_lhs => rw [vec32_toList_eq2 v]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  rw [pointsToBytes_singleton, pointsToBytes8_eq_pointsTo64, pointsToBytes8_eq_pointsTo64,
    pointsToBytes_singleton]
  change (a ↦₈ v.get 0) ∗
    (((a + 1#64) ↦ₛ b1_14 v) ∗
      (((a + 1#64 + 14#64) ↦₆₄ w15_22 v) ∗
        (((a + 1#64 + 14#64 + 8#64) ↦₆₄ w23_30 v) ∗
          ((a + 1#64 + 14#64 + 8#64 + 8#64) ↦₈ v.get 31)))) = _
  have h15 : a + 1#64 + 14#64 = a + 15#64 := by bv_kernel
  have h23 : a + 15#64 + 8#64 = a + 23#64 := by bv_kernel
  have h31 : a + 23#64 + 8#64 = a + 31#64 := by bv_kernel
  rw [h15, h23, h31]

theorem vec32_view1_to_view2 (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦₈ v.get 0) ∗ ((a + 1#64) ↦₆₄ w1_8 v) ∗
      ((a + 9#64) ↦₆₄ w9_16 v) ∗ ((a + 17#64) ↦ₛ b17_31 v) =
    (a ↦₈ v.get 0) ∗ ((a + 1#64) ↦ₛ b1_14 v) ∗
      ((a + 15#64) ↦₆₄ w15_22 v) ∗ ((a + 23#64) ↦₆₄ w23_30 v) ∗
      ((a + 31#64) ↦₈ v.get 31) := by
  rw [← vec32_view1, vec32_view2]

theorem clampScalar_view2 (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    (a ↦ₛ (Ratchet.clampScalar v).toList) =
      (a ↦₈ (v.get 0 &&& 0xf8#8)) ∗ ((a + 1#64) ↦ₛ b1_14 v) ∗
        ((a + 15#64) ↦₆₄ w15_22 v) ∗ ((a + 23#64) ↦₆₄ w23_30 v) ∗
        ((a + 31#64) ↦₈ ((v.get 31 &&& 0x7f#8) ||| 0x40#8)) := by
  rw [vec32_view2 a (Ratchet.clampScalar v)]
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  rfl

theorem memRegion_32_view1 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗
        (∃∗ u1 : BitVec 64, (a + 1#64) ↦₆₄ u1) ∗
        (∃∗ u9 : BitVec 64, (a + 9#64) ↦₆₄ u9) ∗
        memRegion (a + 17#64) 15 := by
  rw [show (32 : Nat) = 1 + (8 + (8 + 15)) by rfl,
    memRegion_split a 1 31 (by decide),
    memRegion_split (a + 1#64) 8 23 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 15 (by decide),
    memRegion_one, memRegion_eight, memRegion_eight]
  have h9 : a + 1#64 + 8#64 = a + 9#64 := by bv_kernel
  have h17 : a + 9#64 + 8#64 = a + 17#64 := by bv_kernel
  rw [h9, h17]

theorem stur_q0_reframe (a : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    ((a + 1#64) ↦₆₄ w1_8 v) ∗ ((a + 9#64) ↦₆₄ w9_16 v) ∗ memRegion (a + 17#64) 15 ⊢
      ((a + 1#64) ↦ₛ b1_14 v) ∗
        (∃∗ u15 : BitVec 64, (a + 15#64) ↦₆₄ u15) ∗
        (∃∗ u23 : BitVec 64, (a + 23#64) ↦₆₄ u23) ∗
        (∃∗ b31 : BitVec 8, (a + 31#64) ↦₈ b31) := by
  have hw1 : ((a + 1#64) ↦₆₄ w1_8 v) =
      ((a + 1#64) ↦ₛ [v.get 1, v.get 2, v.get 3, v.get 4, v.get 5, v.get 6, v.get 7, v.get 8]) := by
    rw [pointsToBytes8_eq_pointsTo64]; rfl
  have hw9 : ((a + 9#64) ↦₆₄ w9_16 v) =
      ((a + 9#64) ↦ₛ [v.get 9, v.get 10, v.get 11, v.get 12, v.get 13, v.get 14, v.get 15, v.get 16]) := by
    rw [pointsToBytes8_eq_pointsTo64]; rfl
  have hcomb : ((a + 1#64) ↦₆₄ w1_8 v) ∗ ((a + 9#64) ↦₆₄ w9_16 v) =
      ((a + 1#64) ↦ₛ b1_14 v) ∗ ((a + 15#64) ↦ₛ [v.get 15, v.get 16]) := by
    have h9 : a + 9#64 =
        a + 1#64 + BitVec.ofNat 64 [v.get 1, v.get 2, v.get 3, v.get 4, v.get 5, v.get 6, v.get 7, v.get 8].length := by
      change a + 9#64 = a + 1#64 + 8#64; bv_kernel
    rw [hw1, hw9, h9,
      ← pointsToBytes_append (a + 1#64)
        [v.get 1, v.get 2, v.get 3, v.get 4, v.get 5, v.get 6, v.get 7, v.get 8]
        [v.get 9, v.get 10, v.get 11, v.get 12, v.get 13, v.get 14, v.get 15, v.get 16],
      show ([v.get 1, v.get 2, v.get 3, v.get 4, v.get 5, v.get 6, v.get 7, v.get 8] ++
        [v.get 9, v.get 10, v.get 11, v.get 12, v.get 13, v.get 14, v.get 15, v.get 16]) =
        b1_14 v ++ [v.get 15, v.get 16] from rfl,
      pointsToBytes_append (a + 1#64) (b1_14 v) [v.get 15, v.get 16]]
    have h15 : a + 1#64 + BitVec.ofNat 64 (b1_14 v).length = a + 15#64 := by
      change a + 1#64 + 14#64 = a + 15#64; bv_kernel
    rw [h15]
  have hm17 : memRegion (a + 15#64) 2 ∗ memRegion (a + 17#64) 15 =
      (∃∗ u15 : BitVec 64, (a + 15#64) ↦₆₄ u15) ∗
      (∃∗ u23 : BitVec 64, (a + 23#64) ↦₆₄ u23) ∗
      (∃∗ b31 : BitVec 8, (a + 31#64) ↦₈ b31) := by
    have h1 : a + 17#64 = a + 15#64 + 2#64 := by bv_kernel
    rw [h1, ← memRegion_split (a + 15#64) 2 15 (by decide),
      show (2 + 15 : Nat) = 8 + (8 + 1) by rfl,
      memRegion_split (a + 15#64) 8 9 (by decide),
      memRegion_split (a + 15#64 + 8#64) 8 1 (by decide),
      memRegion_eight, memRegion_eight, memRegion_one]
    have h23 : a + 15#64 + 8#64 = a + 23#64 := by bv_kernel
    have h31 : a + 23#64 + 8#64 = a + 31#64 := by bv_kernel
    rw [h23, h31]
  rw [← sepConj_assoc, hcomb, sepConj_assoc, ← hm17]
  exact sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion (a + 15#64) [v.get 15, v.get 16]))

theorem memRegion_32_view1_sp (sp : BitVec 64) :
    memRegion (sp - 160#64) 32 =
      (∃∗ b0 : BitVec 8, (sp - 160#64) ↦₈ b0) ∗
        (∃∗ u1 : BitVec 64, (sp - 159#64) ↦₆₄ u1) ∗
        (∃∗ u9 : BitVec 64, (sp - 151#64) ↦₆₄ u9) ∗
        memRegion (sp - 143#64) 15 := by
  simpa [bv_sub_add_lit] using memRegion_32_view1 (sp - 160#64)

theorem stur_q0_reframe_sp (sp : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    ((sp - 159#64) ↦₆₄ w1_8 v) ∗ ((sp - 151#64) ↦₆₄ w9_16 v) ∗ memRegion (sp - 143#64) 15 ⊢
      ((sp - 159#64) ↦ₛ b1_14 v) ∗
        (∃∗ u15 : BitVec 64, (sp - 145#64) ↦₆₄ u15) ∗
        (∃∗ u23 : BitVec 64, (sp - 137#64) ↦₆₄ u23) ∗
        (∃∗ b31 : BitVec 8, (sp - 129#64) ↦₈ b31) := by
  simpa [bv_sub_add_lit] using stur_q0_reframe (sp - 160#64) v

theorem clampScalar_view2_sp (sp : BitVec 64) (v : List.Vector (BitVec 8) 32) :
    ((sp - 160#64) ↦₈ (v.get 0 &&& 0xf8#8)) ∗ ((sp - 159#64) ↦ₛ b1_14 v) ∗
      ((sp - 145#64) ↦₆₄ w15_22 v) ∗ ((sp - 137#64) ↦₆₄ w23_30 v) ∗
      ((sp - 129#64) ↦₈ ((v.get 31 &&& 0x7f#8) ||| 0x40#8)) =
    ((sp - 160#64) ↦ₛ (Ratchet.clampScalar v).toList) := by
  simpa [bv_sub_add_lit] using (clampScalar_view2 (sp - 160#64) v).symm

theorem memRegion_48_eq_stackFrameFor_ct_eq (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage ctEqName sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor, ctEqName, libsignalSessionCode_frameBytes_0x3eda8, reduceStackFrameAt]

theorem stackAt_allocHookStack_eq_ctEq (sp : BitVec 64) :
    stackAt sp allocHookStack =
      stackFrameFor libsignalSessionImage ctEqName sp ∗ stackAt (sp - 48#64) 4048 := by
  rw [sepConj_comm]
  simp only [stackAt, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4096) (n := 4048) (k := 48)
    (b' := sp - 48#64) rfl (by bv_omega) (by decide),
    memRegion_48_eq_stackFrameFor_ct_eq]
  have hsub : sp - 48#64 - BitVec.ofNat 64 4048 = sp - BitVec.ofNat 64 4096 := by bv_kernel
  rw [hsub]

def ctEqROAllocStackSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp allocHookStack
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp allocHookStack

theorem ctEqROAllocStackSpec_pre_eq (p1 : BitVec 64) (k1 : List (BitVec 8))
    (p2 : BitVec 64) (k2 : List (BitVec 8)) (sp : BitVec 64) (s : State) (R : SepProp) :
    ctEqROAllocStackSpec.pre (p1, k1, p2, k2, sp) s ∗ R =
      ctEqSliceROSpec.pre (p1, k1, p2, k2, sp) s ∗ (stackAt (sp - 48#64) 4048 ∗ R) := by
  change (⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp allocHookStack) ∗ R =
    (⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackFrameFor libsignalSessionImage ctEqName sp) ∗
    (stackAt (sp - 48#64) 4048 ∗ R)
  rw [stackAt_allocHookStack_eq_ctEq]
  generalize stackFrameFor libsignalSessionImage ctEqName sp = F
  ac_rfl

theorem ctEqROAllocStackSpec_post_eq (p1 : BitVec 64) (k1 : List (BitVec 8))
    (p2 : BitVec 64) (k2 : List (BitVec 8)) (sp : BitVec 64) (s0 sf : State) (R : SepProp) :
    ctEqSliceROSpec.post (p1, k1, p2, k2, sp) s0 sf ∗ (stackAt (sp - 48#64) 4048 ∗ R) =
      ctEqROAllocStackSpec.post (p1, k1, p2, k2, sp) s0 sf ∗ R := by
  change (⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackFrameFor libsignalSessionImage ctEqName sp) ∗
    (stackAt (sp - 48#64) 4048 ∗ R) =
    (⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp allocHookStack) ∗ R
  rw [stackAt_allocHookStack_eq_ctEq]
  generalize stackFrameFor libsignalSessionImage ctEqName sp = F
  ac_rfl

theorem ctEqROAllocStack_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hct : CtEqROOk_trap b C abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr ctEqName)
      ctEqROAllocStackSpec := by
  refine subroutine_ok_map hct ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 48#64) 4048 ∗ R, ?_, ?_⟩
  · rwa [← ctEqROAllocStackSpec_pre_eq]
  · intro sf hpost
    rwa [← ctEqROAllocStackSpec_post_eq]

theorem ctEqROAllocStack_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hct : CtEqROOk b C ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr ctEqName)
      ctEqROAllocStackSpec := by
  refine subroutine_ok_map hct ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 48#64) 4048 ∗ R, ?_, ?_⟩
  · rwa [← ctEqROAllocStackSpec_pre_eq]
  · intro sf hpost
    rwa [← ctEqROAllocStackSpec_post_eq]

theorem ctEqROAllocStack_ok_at_tripleRatchet_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hct : CtEqROOk_trap b C abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff ctEqName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      ctEqROAllocStackSpec :=
  sub_ok_at_rebase hk (ctEqROAllocStack_ok_trap hct)

theorem ctEqROAllocStack_ok_at_tripleRatchet {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hct : CtEqROOk b C ctl abs) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff ctEqName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ctEqROAllocStackSpec :=
  sub_ok_at_rebase hk (ctEqROAllocStack_ok hct)

@[scoped simp, scoped arm64_norm]
theorem clamp_byte0_norm (b0 : BitVec 8) :
    (b0.zeroExtend 64 &&& 1065151889656#64).truncate 8 =
      b0 &&& 0xf8#8 := by
  bv_kernel

@[scoped simp, scoped arm64_norm]
theorem clamp_byte0_norm32 (b0 : BitVec 8) :
    ((b0.zeroExtend 32 &&& 0xf8#32).zeroExtend 64).truncate 8 =
      b0 &&& 0xf8#8 := by
  bv_kernel

@[scoped simp, scoped arm64_norm]
theorem clamp_byte31_bfxil_norm (b31 : BitVec 8) :
    BitVec.zeroExtend 8
      (64#64 ||| (b31.zeroExtend 64 >>> 0) &&& 63#64) =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_kernel

@[scoped simp, scoped arm64_norm]
theorem clamp_byte31_bfxil_norm' (b31 : BitVec 8) :
    BitVec.zeroExtend 8
      (64#64 &&& ~~~63#64 ||| (b31.zeroExtend 64 >>> 0) &&& 63#64) =
      (b31 &&& 0x7f#8) ||| 0x40#8 := by
  bv_kernel

theorem subroutine_ok_inImage_rodata {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr : BitVec 64} {roBytes : List (BitVec 8)} {spec : Spec α}
    (hro_intro : ∀ {m : Memory} (_ : img.RoDataLoaded m) {P : SepProp},
      (m ⊨ P) → (m ⊨ (roAddr ↦ᵣ roBytes) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => (roAddr ↦ᵣ roBytes) ∗ spec.pre x s
        post := fun x s0 sf => (roAddr ↦ᵣ roBytes) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, hpre⟩
  have hpre' : s0.mem ⊨ ((roAddr ↦ᵣ roBytes) ∗ spec.pre x s0) ∗ R := by
    rw [sepConj_assoc]
    exact hro_intro hL.1.roData hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only at hq
    rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

theorem memRegion_24_err (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ u0 : BitVec 64, a ↦₆₄ u0) ∗
        (∃∗ b8 : BitVec 8, (a + 8#64) ↦₈ b8) ∗
        memRegion (a + 9#64) 15 := by
  rw [show (24 : Nat) = 8 + (1 + 15) by rfl,
    memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 1 15 (by decide),
    memRegion_eight, memRegion_one]
  have h9 : a + 8#64 + 1#64 = a + 9#64 := by bv_kernel
  rw [h9]

theorem memRegion_24_ok (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ u0 : BitVec 64, a ↦₆₄ u0) ∗
        (∃∗ u1 : BitVec 64, (a + 8#64) ↦₆₄ u1) ∗
        (∃∗ u2 : BitVec 64, (a + 16#64) ↦₆₄ u2) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
    memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_kernel
  rw [h16]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ u0 : BitVec 64, a ↦₆₄ u0) ∗
        (∃∗ u1 : BitVec 64, (a + 8#64) ↦₆₄ u1) ∗
        (∃∗ u2 : BitVec 64, (a + 16#64) ↦₆₄ u2) ∗
        (∃∗ u3 : BitVec 64, (a + 24#64) ↦₆₄ u3) := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl,
    memRegion_split a 8 24 (by decide),
    memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_kernel
  have h24 : a + 16#64 + 8#64 = a + 24#64 := by bv_kernel
  rw [h16, h24]

theorem stackAt_calculateAgreementAt_split (sp : BitVec 64) {subStack : Nat}
    (hbound : 160 + subStack ≤ 2 ^ 64) :
    stackAt sp (160 + subStack) =
      stackAt (sp - 160#64) subStack ∗
        memRegion (sp - 160#64) 32 ∗
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((sp - 128#64) ↦₆₄ c0) ∗ ((sp - 120#64) ↦₆₄ c1) ∗
          ((sp - 112#64) ↦₆₄ c2) ∗ ((sp - 104#64) ↦₆₄ c3)) ∗
        memRegion (sp - 96#64) 32 ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
          ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
          ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have hsub : sp - 160#64 - BitVec.ofNat 64 subStack = sp - BitVec.ofNat 64 (160 + subStack) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hb' : sp - BitVec.ofNat 64 (160 + subStack) + BitVec.ofNat 64 subStack = sp - 160#64 := by
    rw [← hsub, BitVec.sub_add_cancel]
  simp only [stackAt]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (160 + subStack)) (n := subStack) (k := 160)
      (b' := sp - 160#64) (Nat.add_comm 160 subStack) hb'.symm hbound,
    ProofLib.memRegion_split' (b := sp - 160#64) (n := 32) (k := 128)
      (b' := sp - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 128#64) (n := 32) (k := 96)
      (b' := sp - 96#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 96#64) (n := 32) (k := 64)
      (b' := sp - 64#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 (160 + subStack)) subStack ∗
    (memRegion (sp - 160#64) 32 ∗
      (memRegion (sp - 128#64) (8 * 4) ∗
        (memRegion (sp - 96#64) 32 ∗ memRegion (sp - 64#64) (8 * 8)))) = _
  rw [memRegion_cells (sp - 128#64) 4 (by decide),
    memRegion_cells (sp - 64#64) 8 (by decide)]
  have hc4 : cells (sp - 128#64) 4 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
        ((sp - 128#64) ↦₆₄ c0) ∗ ((sp - 120#64) ↦₆₄ c1) ∗
        ((sp - 112#64) ↦₆₄ c2) ∗ ((sp - 104#64) ↦₆₄ c3)) := by
    cells_unfold
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
        ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
        ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [hsub, hc4, hc8]

theorem stackAt_calculateAgreement_split (sp : BitVec 64) :
    stackAt sp calculateAgreementStack =
      stackAt (sp - 160#64) allocHookStack ∗
        memRegion (sp - 160#64) 32 ∗
        (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
          ((sp - 128#64) ↦₆₄ c0) ∗ ((sp - 120#64) ↦₆₄ c1) ∗
          ((sp - 112#64) ↦₆₄ c2) ∗ ((sp - 104#64) ↦₆₄ c3)) ∗
        memRegion (sp - 96#64) 32 ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗
          ((sp - 48#64) ↦₆₄ v2) ∗ ((sp - 40#64) ↦₆₄ v3) ∗
          ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) :=
  stackAt_calculateAgreementAt_split sp (by decide)

theorem rejoin_stack_calculateAgreementAt (sp : BitVec 64) {subStack : Nat}
    (hbound : 160 + subStack ≤ 2 ^ 64)
    {l1 l2 l3 l4 : List (BitVec 8)}
    (hl1 : l1.length = 32) (hl2 : l2.length = 32) (hl3 : l3.length = 32) (hl4 : l4.length = 32)
    (v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 160#64) subStack ∗
      ((sp - 160#64) ↦ₛ l1) ∗
      ((sp - 128#64) ↦ₛ l2) ∗
      ((sp - 96#64) ↦ₛ l3) ∗
      ((sp - 64#64) ↦ₛ l4) ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      stackAt sp (160 + subStack) := by
  have hsub : sp - 160#64 - BitVec.ofNat 64 subStack = sp - BitVec.ofNat 64 (160 + subStack) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have hb' : sp - BitVec.ofNat 64 (160 + subStack) + BitVec.ofNat 64 subStack = sp - 160#64 := by
    rw [← hsub, BitVec.sub_add_cancel]
  have heq : stackAt sp (160 + subStack) =
      stackAt (sp - 160#64) subStack ∗
        memRegion (sp - 160#64) 32 ∗
        memRegion (sp - 128#64) 32 ∗
        memRegion (sp - 96#64) 32 ∗
        memRegion (sp - 64#64) 32 ∗
        cells (sp - 32#64) 4 := by
    simp only [stackAt]
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (160 + subStack)) (n := subStack) (k := 160)
        (b' := sp - 160#64) (Nat.add_comm 160 subStack) hb'.symm hbound,
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 32) (k := 128)
        (b' := sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 32) (k := 96)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 32) (k := 64)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 32) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide)]
    change memRegion (sp - BitVec.ofNat 64 (160 + subStack)) subStack ∗
      (memRegion (sp - 160#64) 32 ∗
        (memRegion (sp - 128#64) 32 ∗
          (memRegion (sp - 96#64) 32 ∗
            (memRegion (sp - 64#64) 32 ∗ memRegion (sp - 32#64) (8 * 4))))) = _
    rw [memRegion_cells (sp - 32#64) 4 (by decide), hsub]
  rw [heq]
  have hm1 : ((sp - 160#64) ↦ₛ l1) ⊢ memRegion (sp - 160#64) 32 :=
    hl1 ▸ pointsToBytes_entails_memRegion (sp - 160#64) l1
  have hm2 : ((sp - 128#64) ↦ₛ l2) ⊢ memRegion (sp - 128#64) 32 :=
    hl2 ▸ pointsToBytes_entails_memRegion (sp - 128#64) l2
  have hm3 : ((sp - 96#64) ↦ₛ l3) ⊢ memRegion (sp - 96#64) 32 :=
    hl3 ▸ pointsToBytes_entails_memRegion (sp - 96#64) l3
  have hm4 : ((sp - 64#64) ↦ₛ l4) ⊢ memRegion (sp - 64#64) 32 :=
    hl4 ▸ pointsToBytes_entails_memRegion (sp - 64#64) l4
  have hc4 : ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢ cells (sp - 32#64) 4 := by
    cells_unfold
    exact Entails.sepExists_right v0
      (Entails.sepExists_right v1
        (Entails.sepExists_right v2
          (Entails.sepExists_right v3 (Entails.refl _))))
  exact sepConj_mono_right (sepConj_mono hm1 (sepConj_mono hm2 (sepConj_mono hm3 (sepConj_mono hm4 hc4))))

theorem rejoin_stack_calculateAgreement (sp : BitVec 64)
    {l1 l2 l3 l4 : List (BitVec 8)}
    (hl1 : l1.length = 32) (hl2 : l2.length = 32) (hl3 : l3.length = 32) (hl4 : l4.length = 32)
    (v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 160#64) allocHookStack ∗
      ((sp - 160#64) ↦ₛ l1) ∗
      ((sp - 128#64) ↦ₛ l2) ∗
      ((sp - 96#64) ↦ₛ l3) ∗
      ((sp - 64#64) ↦ₛ l4) ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      stackAt sp calculateAgreementStack :=
  rejoin_stack_calculateAgreementAt sp (by decide) hl1 hl2 hl3 hl4 v0 v1 v2 v3

theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

theorem pointsToBytes_entails_memRegion_of_eq {a : BitVec 64} {l : List (BitVec 8)} {n : Nat}
    (h : l.length = n) : (a ↦ₛ l) ⊢ memRegion a n :=
  h ▸ pointsToBytes_entails_memRegion a l

theorem calculateAgreementResultAt_some_intro (A : RustAlloc) (r ptr : BitVec 64)
    (shared : List.Vector (BitVec 8) 32) (hptr : ptr ≠ 0#64) :
    (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ 32#64) ∗
      A.live ptr 32 1 ∗ (ptr ↦ₛ shared.toList) ⊢
      calculateAgreementResultAt A r (some shared) := by
  have hlen : shared.toList.length = 32 := List.Vector.toList_length shared
  have hne : shared.toList ≠ [] := by
    intro h; rw [h] at hlen; contradiction
  dsimp only [calculateAgreementResultAt]
  refine sepConj_mono_right (Entails.sepExists_right ptr ?_)
  dsimp only [boxU8At]
  simp only [hne, ↓reduceIte]
  rw [hlen, eq_true (⟨hptr, by decide⟩ : ptr ≠ 0 ∧ 32 < 2 ^ 63), pure_true, emp_sepConj]
  have hr16 : r + 8#64 + 8#64 = r + 16#64 := by bv_kernel
  rw [hr16]
  exact Entails.refl _

theorem SepWPp.split_alloc {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {sp sp' : BitVec 64} {subStack : Nat}
    {tr : List TraceEvent} {size align : Nat} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hsp : sp = sp')
    (hnull : s.readReg64 (.gpr 0#5) = 0#64 → s.trace = tr ++ [allocFailedEvent] →
      SepWPp prog ret s (A.pool ∗ stackAt sp' subStack ∗ F) Q Qp)
    (hok : s.readReg64 (.gpr 0#5) ≠ 0#64 →
      (s.readReg64 (.gpr 0#5)).toNat % align = 0 → s.trace = tr →
      SepWPp prog ret s
        (A.pool ∗ stackAt sp' subStack ∗
          A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) Q Qp) :
    SepWPp prog ret s
      (A.pool ∗ stackAt sp subStack ∗
        (if s.readReg64 (.gpr 0#5) = 0 then ⌜s.trace = tr ++ [allocFailedEvent]⌝
        else ⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0 ∧ s.trace = tr⌝ ∗
          A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size) ∗ F) Q Qp := by
  subst hsp
  by_cases h0 : s.readReg64 (.gpr 0#5) = 0
  · simp only [h0, ↓reduceIte]
    intro R hm
    have hm' : s.mem ⊨ ⌜s.trace = tr ++ [allocFailedEvent]⌝ ∗
        ((A.pool ∗ stackAt sp subStack ∗ F) ∗ R) := by
      ac_nf at hm ⊢
    rw [satisfies_pure_sepConj] at hm'
    exact hnull h0 hm'.1 R hm'.2
  · simp only [h0, ↓reduceIte]
    intro R hm
    have hm' : s.mem ⊨ ⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0 ∧ s.trace = tr⌝ ∗
        ((A.pool ∗ stackAt sp subStack ∗
          A.live (s.readReg64 (.gpr 0#5)) size align ∗
          memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) ∗ R) := by
      ac_nf at hm ⊢
    rw [satisfies_pure_sepConj] at hm'
    exact hok h0 hm'.1.1 hm'.1.2 R hm'.2

theorem allocFailedIn_panicked_of_append {s0 sf : State}
    (htr : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace := by
  simp [allocFailedIn, Rust.panicked, htr]

theorem calculateAgreement_eq_none {X : Ratchet.X25519Fn} {their : PublicKey} {our : PrivateKey}
    (h : (X (Ratchet.clampScalar our.bytes) their.bytes).toList = List.replicate 32 0#8) :
    calculateAgreement X their our = none := by
  unfold calculateAgreement; dsimp only; simp only [h, ↓reduceIte]

theorem calculateAgreement_eq_some {X : Ratchet.X25519Fn} {their : PublicKey} {our : PrivateKey}
    (h : (X (Ratchet.clampScalar our.bytes) their.bytes).toList ≠ List.replicate 32 0#8) :
    calculateAgreement X their our = some (X (Ratchet.clampScalar our.bytes) their.bytes) := by
  unfold calculateAgreement; dsimp only; simp only [h, ↓reduceIte]

/-! ## Stack-parameterized call-site specs for `calculate_agreement` -/

def calculateAgreementSpecAt (X : Ratchet.X25519Fn) (A : RustAlloc) (subStack : Nat) :
    Spec CalculateAgreementGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ourA ∧ s.readReg64 .x1 = x.theirA ∧ s.readReg64 .x8 = x.ret⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp (160 + subStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ourA ↦ₛ x.our.bytes.toList) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
      calculateAgreementResultAt A x.ret (calculateAgreement X x.their x.our) ∗
      A.pool ∗ stackAt s0.sp (160 + subStack)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def dhCallSpecAt (img : Obj.Image) (X : Ratchet.X25519Fn) (subStack : Nat) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 32 ×
      BitVec 64 × BitVec 64) where
  pre := fun (secA, sec, pubA, pub, ret, sp) s =>
    ⌜FrozenInv img s ∧ s.readReg64 .x0 = secA ∧ s.readReg64 .x1 = pubA ∧ s.readReg64 .x8 = ret ∧
      s.sp = sp⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ memRegion ret 32 ∗ stackAt sp subStack
  post := fun (secA, sec, pubA, pub, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ (ret ↦ₛ (X sec pub).toList) ∗
      stackAt sp subStack

def zeroizeCallSpecAt (img : Obj.Image) (subStack : Nat) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (a, sp) s =>
    ⌜FrozenInv img s ∧ s.readReg64 .x0 = a ∧ s.sp = sp⌝ ∗ memRegion a 32 ∗ stackAt sp subStack
  post := fun (a, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (a ↦ₛ List.replicate 32 0#8) ∗ stackAt sp subStack

def ctEqCallSpecAt (img : Obj.Image) (subStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜FrozenInv img s ∧ s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧
      k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp subStack
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = (if k1 = k2 then 1#8 else 0#8) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp subStack

def shimCallSpecAt (img : Obj.Image) (subStack : Nat) : Spec (BitVec 64) where
  pre := fun sp s => ⌜FrozenInv img s ∧ s.sp = sp⌝ ∗ stackAt sp subStack
  post := fun sp s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt sp subStack

def allocCallSpecAt (img : Obj.Image) (A : RustAlloc) (subStack : Nat) :
    Spec (Nat × Nat × BitVec 64) where
  pre := fun (size, align, sp) s =>
    ⌜FrozenInv img s ∧ (s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      LayoutOk size align ∧ s.sp = sp⌝ ∗
      A.pool ∗ stackAt sp subStack
  post := fun (size, align, sp) s0 sf =>
    A.pool ∗ stackAt sp subStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
      else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
        A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)

private theorem dhCallAt_of_raw {img : Obj.Image} {X : Ratchet.X25519Fn} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (diffieHellmanSpec X)) :
    subroutine_ok prog entry (dhCallSpecAt img X subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨secA, sec, pubA, pub, ret, sp⟩ R s0 hpre
  dsimp only [dhCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hx8, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(secA, sec, pubA, pub, ret), stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [diffieHellmanSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [diffieHellmanSpec, dhCallSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem zeroizeCallAt_of_raw {img : Obj.Image} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry zeroizeSecretSpec) :
    subroutine_ok prog entry (zeroizeCallSpecAt img subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨a, sp⟩ R s0 hpre
  dsimp only [zeroizeCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hsp⟩, hpre⟩
  subst hsp
  refine ⟨a, stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [zeroizeSecretSpec, zeroizeCallSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem ctEqCallAt_of_allocStack {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry ctEqROAllocStackSpec) :
    subroutine_ok prog entry (ctEqCallSpecAt img allocHookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  refine ⟨(p1, k1, p2, k2, sp), R, ?_, ?_⟩
  · dsimp only [ctEqROAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  · intro sf hpost
    dsimp only [ctEqROAllocStackSpec, ctEqCallSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hres, htr⟩, hpost⟩
    refine ⟨⟨?_, htr⟩, hpost⟩
    rw [hres]; split <;> rfl

private theorem shimCallAt_of_raw {img : Obj.Image} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry noAllocShimSpec) :
    subroutine_ok prog entry (shimCallSpecAt img subStack) := by
  refine subroutine_ok_map h ?_
  rintro sp R s0 hpre
  dsimp only [shimCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hsp⟩, hpre⟩
  refine ⟨(), stackAt sp subStack ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ emp ∗ (stackAt sp subStack ∗ R)
    simpa only [emp_sepConj] using hpre
  · intro sf hpost
    change sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗ (stackAt sp subStack ∗ R) at hpost
    dsimp only [shimCallSpecAt]
    rwa [sepConj_assoc]

private theorem allocCallAt_of_allocStack {img : Obj.Image} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustAllocSpec A)) :
    subroutine_ok prog entry (allocCallSpecAt img A allocHookStack) := by
  rw [← rustAllocSpecWithStack_eq_rustAllocSpec A] at h
  refine subroutine_ok_map h ?_
  rintro ⟨size, align, sp⟩ R s0 hpre
  dsimp only [allocCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hlay, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(size, align), R, ?_, ?_⟩
  · dsimp only [rustAllocSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, hpre⟩
  · intro sf hpost
    dsimp only [rustAllocSpecWithStack, allocCallSpecAt] at hpost ⊢
    exact hpost

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  calculateAgreement_fnOff ctEq_fnOff dh_fnOff sharedDrop_fnOff staticDrop_fnOff handleAllocError_fnOff
  (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement")
  (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq")
  (ls_stub% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman")
  (ls_stub% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "alloc::alloc::handle_alloc_error")
  (ls_hook% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman")
  (ls_hook% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
  (ls_hook% "alloc::alloc::handle_alloc_error")

theorem stackAt_calculateAgreementExt_split (sp : BitVec 64) :
    stackAt sp calculateAgreementExtStack =
      stackAt (sp - 4256#64) 12288 ∗ stackAt sp calculateAgreementStack := by
  change memRegion (sp - 16544#64) 16544 =
    memRegion (sp - 4256#64 - 12288#64) 12288 ∗ memRegion (sp - 4256#64) 4256
  have hsub : sp - 4256#64 - 12288#64 = sp - 16544#64 := by bv_kernel
  rw [hsub]
  exact ProofLib.memRegion_split' (b := sp - 16544#64) (n := 12288) (k := 4256)
    (b' := sp - 4256#64) rfl (by bv_omega) (by decide)

theorem ctEqROAllocStack_ok_rebase {b : BitVec 64} {H : String → Option (State → State)}
    (hct : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr ctEqName) ctEqSliceROSpec) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr ctEqName)
      ctEqROAllocStackSpec := by
  refine subroutine_ok_map hct ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 48#64) 4048 ∗ R, ?_, ?_⟩
  · rwa [← ctEqROAllocStackSpec_pre_eq]
  · intro sf hpost
    rwa [← ctEqROAllocStackSpec_post_eq]

theorem ctEqROAllocStack_ok_at_rebase {b : BitVec 64} {H : String → Option (State → State)}
    (hct : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr ctEqName) ctEqSliceROSpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff ctEqName := by fnoff_eq) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr name + BitVec.ofNat 64 k)
      ctEqROAllocStackSpec := by
  rw [← Program.fnAddr_rel rfl rfl hk]
  exact ctEqROAllocStack_ok_rebase hct

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
/-- Unified stack-parameterized `<PrivateKey>::calculate_agreement` (`0x3e5fc`): verified once for
any `subStack` (`160 + subStack ≤ 2 ^ 64`) under `FrozenInv`-aware call-site specs. -/
theorem calculateAgreement_ok_of_hooks_gen {img : Obj.Image} {X : Ratchet.X25519Fn} {A : RustAlloc}
    {ext : String → Option (State → State)} {subStack : Nat}
    (hbound : 160 + subStack ≤ 2 ^ 64)
    (himg : Obj.Loads libsignalSessionImage img)
    (h_dh : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      (dhCallSpecAt img X subStack))
    (h_shdrop : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      (zeroizeCallSpecAt img subStack))
    (h_cteq : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      (ctEqCallSpecAt img subStack))
    (h_shim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      (shimCallSpecAt img subStack))
    (h_alloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      (allocCallSpecAt img A subStack))
    (h_stdrop : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      (zeroizeCallSpecAt img subStack)) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName)
      ((calculateAgreementSpecAt X A subStack).inImage img) := by
  refine subroutine_ok_inImage_rodata' (rodata_0x49f6a himg) ?_
  have hfn : libsignalSessionCode.fnOff calculateAgreementName =
      num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement") :=
    calculateAgreement_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")) 224
  have h_pan := panic_at_handle_alloc_error_rebase (b := img.base) (ext := ext)
    (name := calculateAgreementName)
    (k := num% (ls_off% "alloc::alloc::handle_alloc_error" -
      ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
    (by rw [calculateAgreement_fnOff, handleAllocError_fnOff])
  have hadrp : ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      calculateAgreementName + 104#64 &&&
      bv% (2 ^ 64 - 4096)) +
      bv% (ls_xref% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 104)
        (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 108) -
        page% (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature_for_multipart_message" + 652)) =
      img.base + bv% (ls_xref% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 104)
        (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 108)) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      calculateAgreementName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨ourA, our, theirA, their, ret⟩
  dsimp only at *
  have hF0 : FrozenInv img s0 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = ourA› ‹s0.readReg64 (.gpr 1#5) = theirA›
    ‹s0.readReg64 (.gpr 8#5) = ret›
  obtain ⟨t0, t1, t2, t3, _, htheir_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length their.bytes)
  have htheir_sp : ∀ sp : BitVec 64,
      ((sp - 64#64) ↦₆₄ t0) ∗ ((sp - 56#64) ↦₆₄ t1) ∗
        ((sp - 48#64) ↦₆₄ t2) ∗ ((sp - 40#64) ↦₆₄ t3) =
      ((sp - 64#64) ↦ₛ their.bytes.toList) := by
    intro sp; simpa [bv_sub_add_lit] using (htheir_pts (sp - 64#64)).symm
  let ss := X (Ratchet.clampScalar our.bytes) their.bytes
  obtain ⟨ss0, ss1, ss2, ss3, _, hss_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ss)
  have hss_sp96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) =
      ((s0.sp - 96#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 96#64)).symm
  have hss_sp128 :
      ((s0.sp - 128#64) ↦₆₄ ss0) ∗ ((s0.sp - 120#64) ↦₆₄ ss1) ∗
        ((s0.sp - 112#64) ↦₆₄ ss2) ∗ ((s0.sp - 104#64) ↦₆₄ ss3) =
      ((s0.sp - 128#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 128#64)).symm
  have hss_mem96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) ⊢
      memRegion (s0.sp - 96#64) 32 := by
    rw [hss_sp96]
    exact pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length ss)
  have hclamp_mem :
      ((s0.sp - 160#64) ↦ₛ (Ratchet.clampScalar our.bytes).toList) ⊢
      memRegion (s0.sp - 160#64) 32 :=
    pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length (Ratchet.clampScalar our.bytes))
  refine SepWPp.rw_pre (by
    rw [stackAt_calculateAgreementAt_split s0.sp (by omega),
      memRegion_32_view1_sp s0.sp,
      vec32_view1 (s0.readReg64 (.gpr 0#5)) our.bytes,
      htheir_pts (s0.readReg64 (.gpr 1#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_frozen (mid := entry + bv% (120)) hF0 ?_
  apply SepWP.of_sepWP_frozen hF0
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) our.bytes)) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (stur_q0_reframe_sp s0.sp our.bytes) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view2 (s0.readReg64 (.gpr 0#5)) our.bytes).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_pts (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (clampScalar_view2_sp s0.sp our.bytes)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_sp s0.sp)) (by sep_focus) ?_
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF1
  apply SepWP.of_sepWP_frozen hF1
  wp_call h_dh (s0.sp - 160#64, Ratchet.clampScalar our.bytes, s0.sp - 64#64, their.bytes,
    s0.sp - 96#64, s0.sp - 160#64)
  refine SepWP.fold (Entails.of_eq hss_sp96.symm) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
  refine SepWP.fold hss_mem96 (by sep_focus) ?_
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF2
  apply SepWP.of_sepWP_frozen hF2
  wp_call h_shdrop (s0.sp - 96#64, s0.sp - 160#64)
  wp_steps
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF3
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
  have hzero_len : (List.replicate 32 0#8).length = 32 := by decide
  wp_call h_cteq (s0.sp - 128#64, ss.toList,
    img.base + bv% (ls_xref% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 104)
      (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" + 108)),
    List.replicate 32 0#8, s0.sp - 160#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF4
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres : calculateAgreement X their our = none := calculateAgreement_eq_none hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.rw_pre (by rw [memRegion_24_err (s0.readReg64 (.gpr 8#5))]) ?_
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    apply SepWP.of_sepWP_frozen hF4
    wp_steps
    refine SepWP.fold hclamp_mem (by sep_focus) ?_
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF5
    wp_call h_stdrop (s0.sp - 160#64, s0.sp - 160#64)
    wp_steps
    refine SepWP.fold (rejoin_stack_calculateAgreementAt s0.sp (by omega) hzero_len hzero_len hzero_len
      (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
    simp only [hres, calculateAgreementResultAt]
    wp_done
  · have hres : calculateAgreement X their our = some ss := calculateAgreement_eq_some hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.of_sepWP_frozen (mid := entry + bv% (160)) hF4 ?_
    apply SepWP.of_sepWP_frozen hF4
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF5
    apply SepWP.of_sepWP_frozen hF5
    wp_call h_shim (s0.sp - 160#64)
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF6
    have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call h_alloc (32, 1, s0.sp - 160#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF7
    refine SepWPp.split_alloc (sp' := s0.sp - 160#64) (by wp_norm_lhs)
      (fun halloc htr_alloc => ?_) (fun halloc halign htr_alloc => ?_)
    · refine SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.rw_pre (by
        rw [memRegion_24_ok (s0.readReg64 (.gpr 8#5)),
          memRegion_32_cells,
          ← hss_sp128]) ?_
      sep_elim_exists
      apply SepWPp.of_sepWP_ret
      apply SepWP.of_sepWP_frozen hF7
      wp_steps
      refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hss_pts _).symm) (by sep_focus) ?_
      refine SepWP.fold hclamp_mem (by sep_focus) ?_
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF8
      wp_call h_stdrop (s0.sp - 160#64, s0.sp - 160#64)
      wp_steps
      refine SepWP.fold (rejoin_stack_calculateAgreementAt s0.sp (by omega) hzero_len hss_len hzero_len
        (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (calculateAgreementResultAt_some_intro A (s0.readReg64 (.gpr 8#5))
        _ ss halloc) (by sep_focus) ?_
      rw [hres]
      wp_done

/-- Contract-backed `<PrivateKey>::calculate_agreement` (`0x3e5fc`): verified on
`libsignalSessionCode.rebase img.base (Rust.withPanics ext)` given `subroutine_ok` contracts for
`dhName`, `sharedDropName`, `ctEqName`, `shimName`, `allocName`, and `staticDropName`. -/
theorem calculateAgreement_ok_of_contracts {img : Obj.Image} {X : Ratchet.X25519Fn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (h_dh_entry : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dhName)
      (diffieHellmanSpec X))
    (h_shdrop_entry : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr sharedDropName)
      zeroizeSecretSpec)
    (hct : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr ctEqName)
      ctEqSliceROSpec)
    (h_shim_entry : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
        "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      noAllocShimSpec)
    (h_alloc_entry : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "__rustc::__rust_alloc")
      (rustAllocSpec A))
    (h_stdrop_entry : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr staticDropName)
      zeroizeSecretSpec) :
    subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr calculateAgreementName)
      ((calculateAgreementSpec X A).inImage img) := by
  exact calculateAgreement_ok_of_hooks_gen (subStack := allocHookStack) (by decide) himg
    (dhCallAt_of_raw (sub_ok_at_rebase (name := calculateAgreementName) (callee := dhName)
      (k := num% (ls_off% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [calculateAgreement_fnOff, dh_fnOff]) h_dh_entry))
    (zeroizeCallAt_of_raw (sub_ok_at_rebase (name := calculateAgreementName) (callee := sharedDropName)
      (k := num% (ls_off% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [calculateAgreement_fnOff, sharedDrop_fnOff]) h_shdrop_entry))
    (ctEqCallAt_of_allocStack (ctEqROAllocStack_ok_at_rebase hct (name := calculateAgreementName)
      (k := num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [calculateAgreement_fnOff, ctEq_fnOff])))
    (shimCallAt_of_raw (sub_ok_at_rebase (name := calculateAgreementName)
      (callee := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
      h_shim_entry))
    (allocCallAt_of_allocStack (sub_ok_at_rebase (name := calculateAgreementName)
      (callee := "__rustc::__rust_alloc")
      (k := num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_alloc")]) h_alloc_entry))
    (zeroizeCallAt_of_raw (sub_ok_at_rebase (name := calculateAgreementName) (callee := staticDropName)
      (k := num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [calculateAgreement_fnOff, staticDrop_fnOff]) h_stdrop_entry))

theorem calculateAgreement_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hct : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ctEqName) ctEqSliceROSpec)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName)
      ((calculateAgreementSpec C.X A).inImage img) :=
  calculateAgreement_ok_of_contracts himg hC.dh hC.shared_drop hct hC.shim hC.alloc hC.static_drop

theorem calculateAgreement_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hct : CtEqROOk_trap img.base C abs)
    (hA : AllocHooks A abs) :
    CalculateAgreementOk_trap img C A abs := by
  have h_dh := dh_ok_at_tripleRatchet_trap (b := img.base) (C := C)
    (abs := abs) (name := dhName) (k := 0)
  have h_shdrop := sharedDrop_ok_at_tripleRatchet_trap (b := img.base) (C := C)
    (abs := abs) (name := sharedDropName) (k := 0)
  have h_shim := noAllocShim_ok_at_trap (b := img.base) (C := C)
    (abs := abs) (name := "__rustc::__rust_no_alloc_shim_is_unstable_v2") (k := 0)
  have h_alloc := alloc_ok_at_norm_trap (b := img.base) (C := C)
    (abs := abs) hA (name := "__rustc::__rust_alloc") (k := 0)
  have h_stdrop := staticDrop_ok_at_tripleRatchet_trap (b := img.base) (C := C)
    (abs := abs) (name := staticDropName) (k := 0)
  rw [BitVec.add_zero] at h_dh h_shdrop h_shim h_alloc h_stdrop
  exact calculateAgreement_ok_of_contracts himg h_dh h_shdrop hct h_shim h_alloc h_stdrop

theorem calculateAgreement_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hct : CtEqROOk img.base C ctl abs)
    (hA : AllocHooks A abs) :
    CalculateAgreementOk img C A ctl abs := by
  have h_dh := dh_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := dhName) (k := 0)
  have h_shdrop := sharedDrop_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := sharedDropName) (k := 0)
  have h_shim := noAllocShim_ok_at (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := "__rustc::__rust_no_alloc_shim_is_unstable_v2") (k := 0)
  have h_alloc := alloc_ok_at_norm (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) hA (name := "__rustc::__rust_alloc") (k := 0)
  have h_stdrop := staticDrop_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := staticDropName) (k := 0)
  rw [BitVec.add_zero] at h_dh h_shdrop h_shim h_alloc h_stdrop
  exact calculateAgreement_ok_of_contracts himg h_dh h_shdrop hct h_shim h_alloc h_stdrop

/-! ## Relocatable `[LibsignalPlacement]` contracts -/

structure LsFrozenInv (pl : Obj.MultiPlacement) (s : State) : Prop where
  code : LibsignalCodeLoaded pl s.mem
  ro : LibsignalRoLoaded pl s.mem

theorem LsFrozenInv.of_keepsFrozen {pl : Obj.MultiPlacement} {s sf : State}
    (h : LsFrozenInv pl s) (hk : s.mem.KeepsFrozen sf.mem) : LsFrozenInv pl sf :=
  ⟨h.1.of_keepsFrozen hk, libsignalRoLoaded_of_keepsFrozen h.2 hk⟩

theorem SepWPp.of_sepWP_lscro {prog : Program} {pl : Obj.MultiPlacement} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LsFrozenInv pl s)
    (h : SepWP prog mid s P
      (fun sm Pm => LsFrozenInv pl sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  sepWPp_seq_lscro ⟨hF.1, hF.2⟩
    (SepWP.mono h fun _ _ _ _ hnext hcro => hnext ⟨hcro.1, hcro.2⟩)

theorem SepWP.of_sepWP_lscro {prog : Program} {pl : Obj.MultiPlacement} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : LsFrozenInv pl s)
    (h : SepWP prog (frozenStop mid) s P
      (fun sm Pm => LsFrozenInv pl sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post := by
  unfold frozenStop at h
  exact sepWP_seq_lscro ⟨hF.1, hF.2⟩
    (SepWP.mono h fun _ _ _ _ hnext hcro => hnext ⟨hcro.1, hcro.2⟩)

theorem subroutine_ok_withLsCodeRoLoaded_rodata'' {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {roSym : String} {roBytes : List (BitVec 8)} {spec : Spec α}
    (hchk : lsroCheck roSym roBytes = true)
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜LsFrozenInv pl s⌝ ∗ (pl.ρ roSym ↦ᵣ roBytes) ∗ spec.pre x s
        post := fun x s0 sf => (pl.ρ roSym ↦ᵣ roBytes) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  refine subroutine_ok_withLsCodeRoLoaded_rodata' hchk ?_
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2⟩, hp.2⟩

abbrev lsDhSym : String :=
  "_RNvMs6_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecret14diffie_hellman"

abbrev lsSharedDropSym : String :=
  "_RNvXse_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12SharedSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop"

abbrev lsStaticDropSym : String :=
  "_RNvXsa_NtCscSWoUTnaXmu_12x25519_dalek6x25519NtB5_12StaticSecretNtNtNtCskxtBwYRO61I_4core3ops4drop4Drop4drop"

abbrev lsRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev lsRustAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev lsHandleAllocErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

abbrev lsRodataCst32Sym : String :=
  "libsignal_core:.rodata.cst32+0x0"

def dhPlacedCallSpec (pl : Obj.MultiPlacement) (X : Ratchet.X25519Fn) (subStack : Nat) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List.Vector (BitVec 8) 32 ×
      BitVec 64 × BitVec 64) where
  pre := fun (secA, sec, pubA, pub, ret, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = secA ∧ s.readReg64 .x1 = pubA ∧
      s.readReg64 .x8 = ret ∧ s.sp = sp⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ memRegion ret 32 ∗ stackAt sp subStack
  post := fun (secA, sec, pubA, pub, ret, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (secA ↦ₛ sec.toList) ∗ (pubA ↦ₛ pub.toList) ∗ (ret ↦ₛ (X sec pub).toList) ∗
      stackAt sp subStack

def zeroizePlacedCallSpec (pl : Obj.MultiPlacement) (subStack : Nat) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (a, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = a ∧ s.sp = sp⌝ ∗ memRegion a 32 ∗ stackAt sp subStack
  post := fun (a, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (a ↦ₛ List.replicate 32 0#8) ∗ stackAt sp subStack

def ctEqPlacedCallSpec (pl : Obj.MultiPlacement) (subStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜LsFrozenInv pl s ∧ s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧
      k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp subStack
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = (if k1 = k2 then 1#8 else 0#8) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp subStack

def shimPlacedCallSpec (pl : Obj.MultiPlacement) (subStack : Nat) : Spec (BitVec 64) where
  pre := fun sp s => ⌜LsFrozenInv pl s ∧ s.sp = sp⌝ ∗ stackAt sp subStack
  post := fun sp s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt sp subStack

def allocPlacedCallSpec (pl : Obj.MultiPlacement) (A : RustAlloc) (subStack : Nat) :
    Spec (Nat × Nat × BitVec 64) where
  pre := fun (size, align, sp) s =>
    ⌜LsFrozenInv pl s ∧ (s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      LayoutOk size align ∧ s.sp = sp⌝ ∗
      A.pool ∗ stackAt sp subStack
  post := fun (size, align, sp) s0 sf =>
    A.pool ∗ stackAt sp subStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
      else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
        A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)

private theorem dhPlacedCallAt_of_raw {pl : Obj.MultiPlacement} {X : Ratchet.X25519Fn} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (diffieHellmanSpec X)) :
    subroutine_ok prog entry (dhPlacedCallSpec pl X subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨secA, sec, pubA, pub, ret, sp⟩ R s0 hpre
  dsimp only [dhPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hx8, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(secA, sec, pubA, pub, ret), stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [diffieHellmanSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [diffieHellmanSpec, dhPlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem zeroizePlacedCallAt_of_raw {pl : Obj.MultiPlacement} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry zeroizeSecretSpec) :
    subroutine_ok prog entry (zeroizePlacedCallSpec pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨a, sp⟩ R s0 hpre
  dsimp only [zeroizePlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hsp⟩, hpre⟩
  subst hsp
  refine ⟨a, stackAt s0.sp subStack ∗ R, ?_, ?_⟩
  · dsimp only [zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [zeroizeSecretSpec, zeroizePlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

private theorem ctEqPlacedCallAt_of_withLsCodeLoaded {pl : Obj.MultiPlacement} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl ctEqSliceROSpec)) :
    subroutine_ok prog entry (ctEqPlacedCallSpec pl allocHookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfr, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 48#64) 4048 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr.1, ?_⟩
    rw [← ctEqROAllocStackSpec_pre_eq]
    dsimp only [ctEqROAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [ctEqROAllocStackSpec_post_eq] at hpost
    dsimp only [ctEqROAllocStackSpec, ctEqPlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hres, htr⟩, hpost⟩
    refine ⟨⟨?_, htr⟩, hpost⟩
    rw [hres]; split <;> rfl

private theorem stackAt_allocHookStack_eq_mem48 (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 48#64) 48 ∗ stackAt (sp - 48#64) 4048 := by
  rw [sepConj_comm]
  simp only [stackAt, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 4096) (n := 4048) (k := 48)
    (b' := sp - 48#64) rfl (by bv_omega) (by decide)]
  have hsub : sp - 48#64 - BitVec.ofNat 64 4048 = sp - BitVec.ofNat 64 4096 := by bv_kernel
  rw [hsub]

private theorem ctEqROAllocStackSpec_pre_mem_eq (p1 : BitVec 64) (k1 : List (BitVec 8))
    (p2 : BitVec 64) (k2 : List (BitVec 8)) (sp : BitVec 64) (s : State) (R : SepProp) :
    ctEqROAllocStackSpec.pre (p1, k1, p2, k2, sp) s ∗ R =
      ctEqSliceROMemSpec.pre (p1, k1, p2, k2, sp) s ∗ (stackAt (sp - 48#64) 4048 ∗ R) := by
  change (⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp allocHookStack) ∗ R =
    (⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ memRegion (sp - 48#64) 48) ∗
    (stackAt (sp - 48#64) 4048 ∗ R)
  rw [stackAt_allocHookStack_eq_mem48]
  generalize memRegion (sp - 48#64) 48 = F
  ac_rfl

private theorem ctEqROAllocStackSpec_post_mem_eq (p1 : BitVec 64) (k1 : List (BitVec 8))
    (p2 : BitVec 64) (k2 : List (BitVec 8)) (sp : BitVec 64) (s0 sf : State) (R : SepProp) :
    ctEqSliceROMemSpec.post (p1, k1, p2, k2, sp) s0 sf ∗ (stackAt (sp - 48#64) 4048 ∗ R) =
      ctEqROAllocStackSpec.post (p1, k1, p2, k2, sp) s0 sf ∗ R := by
  change (⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ memRegion (sp - 48#64) 48) ∗
    (stackAt (sp - 48#64) 4048 ∗ R) =
    (⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp allocHookStack) ∗ R
  rw [stackAt_allocHookStack_eq_mem48]
  generalize memRegion (sp - 48#64) 48 = F
  ac_rfl

private theorem ctEqPlacedCallAt_of_mem_withLsCodeLoaded {pl : Obj.MultiPlacement} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl ctEqSliceROMemSpec)) :
    subroutine_ok prog entry (ctEqPlacedCallSpec pl allocHookStack) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfr, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  refine ⟨(p1, k1, p2, k2, sp), stackAt (sp - 48#64) 4048 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr.1, ?_⟩
    rw [← ctEqROAllocStackSpec_pre_mem_eq]
    dsimp only [ctEqROAllocStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded] at hpost
    rw [ctEqROAllocStackSpec_post_mem_eq] at hpost
    dsimp only [ctEqROAllocStackSpec, ctEqPlacedCallSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hres, htr⟩, hpost⟩
    refine ⟨⟨?_, htr⟩, hpost⟩
    rw [hres]; split <;> rfl

private theorem shimPlacedCallAt_of_raw {pl : Obj.MultiPlacement} {subStack : Nat}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry noAllocShimSpec) :
    subroutine_ok prog entry (shimPlacedCallSpec pl subStack) := by
  refine subroutine_ok_map h ?_
  rintro sp R s0 hpre
  dsimp only [shimPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hsp⟩, hpre⟩
  refine ⟨(), stackAt sp subStack ∗ R, ?_, ?_⟩
  · change s0.mem ⊨ emp ∗ (stackAt sp subStack ∗ R)
    simpa only [emp_sepConj] using hpre
  · intro sf hpost
    change sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗ (stackAt sp subStack ∗ R) at hpost
    dsimp only [shimPlacedCallSpec]
    rwa [sepConj_assoc]

private theorem allocPlacedCallAt_of_allocStack {pl : Obj.MultiPlacement} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustAllocSpec A)) :
    subroutine_ok prog entry (allocPlacedCallSpec pl A allocHookStack) := by
  rw [← rustAllocSpecWithStack_eq_rustAllocSpec A] at h
  refine subroutine_ok_map h ?_
  rintro ⟨size, align, sp⟩ R s0 hpre
  dsimp only [allocPlacedCallSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, hx0, hx1, hlay, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(size, align), R, ?_, ?_⟩
  · dsimp only [rustAllocSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, hpre⟩
  · intro sf hpost
    dsimp only [rustAllocSpecWithStack, allocPlacedCallSpec] at hpost ⊢
    exact hpost

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
/-- Relocatable stack-parameterized `<PrivateKey>::calculate_agreement` (Block `207`). -/
theorem calculateAgreement_placed_ok_of_hooks_gen [LibsignalPlacement]
    {X : Ratchet.X25519Fn} {A : RustAlloc}
    {H : String → Option (State → State)} {subStack : Nat}
    (hbound : 160 + subStack ≤ 2 ^ 64)
    (h_dh : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsDhSym)
      (dhPlacedCallSpec lsmpl X subStack))
    (h_shdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsSharedDropSym)
      (zeroizePlacedCallSpec lsmpl subStack))
    (h_cteq : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (ctEqPlacedCallSpec lsmpl subStack))
    (h_shim : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustNoAllocShimSym)
      (shimPlacedCallSpec lsmpl subStack))
    (h_alloc : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustAllocSym)
      (allocPlacedCallSpec lsmpl A subStack))
    (h_stdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsStaticDropSym)
      (zeroizePlacedCallSpec lsmpl subStack))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpecAt X A subStack)) := by
  have h_pan : ((blkPC_207).rebase (blkPl_207).base H).externAt? (lsρ lsHandleAllocErrorSym) =
      some Rust.panicked :=
    (keys_ls_externAt?_of_mem).trans hpanic
  refine subroutine_ok_withLsCodeRoLoaded_rodata'' (roSym := lsRodataCst32Sym)
    (roBytes := List.replicate 32 0#8) (by decide) ?_
  wpp_init x s0
  rcases x with ⟨ourA, our, theirA, their, ret⟩
  dsimp only at *
  have hF0 : LsFrozenInv lsmpl s0 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = ourA› ‹s0.readReg64 (.gpr 1#5) = theirA›
    ‹s0.readReg64 (.gpr 8#5) = ret›
  obtain ⟨t0, t1, t2, t3, _, htheir_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length their.bytes)
  have htheir_sp : ∀ sp : BitVec 64,
      ((sp - 64#64) ↦₆₄ t0) ∗ ((sp - 56#64) ↦₆₄ t1) ∗
        ((sp - 48#64) ↦₆₄ t2) ∗ ((sp - 40#64) ↦₆₄ t3) =
      ((sp - 64#64) ↦ₛ their.bytes.toList) := by
    intro sp; simpa [bv_sub_add_lit] using (htheir_pts (sp - 64#64)).symm
  let ss := X (Ratchet.clampScalar our.bytes) their.bytes
  obtain ⟨ss0, ss1, ss2, ss3, _, hss_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ss)
  have hss_sp96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) =
      ((s0.sp - 96#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 96#64)).symm
  have hss_sp128 :
      ((s0.sp - 128#64) ↦₆₄ ss0) ∗ ((s0.sp - 120#64) ↦₆₄ ss1) ∗
        ((s0.sp - 112#64) ↦₆₄ ss2) ∗ ((s0.sp - 104#64) ↦₆₄ ss3) =
      ((s0.sp - 128#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 128#64)).symm
  have hss_mem96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) ⊢
      memRegion (s0.sp - 96#64) 32 := by
    rw [hss_sp96]
    exact pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length ss)
  have hclamp_mem :
      ((s0.sp - 160#64) ↦ₛ (Ratchet.clampScalar our.bytes).toList) ⊢
      memRegion (s0.sp - 160#64) 32 :=
    pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length (Ratchet.clampScalar our.bytes))
  refine SepWPp.rw_pre (by
    rw [stackAt_calculateAgreementAt_split s0.sp (by omega),
      memRegion_32_view1_sp s0.sp,
      vec32_view1 (s0.readReg64 (.gpr 0#5)) our.bytes,
      htheir_pts (s0.readReg64 (.gpr 1#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_207).base + 120#64) hF0 ?_
  apply SepWP.of_sepWP_lscro hF0
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) our.bytes)) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (stur_q0_reframe_sp s0.sp our.bytes) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view2 (s0.readReg64 (.gpr 0#5)) our.bytes).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_pts (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (clampScalar_view2_sp s0.sp our.bytes)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_sp s0.sp)) (by sep_focus) ?_
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF1
  apply SepWP.of_sepWP_lscro hF1
  wp_call h_dh (s0.sp - 160#64, Ratchet.clampScalar our.bytes, s0.sp - 64#64, their.bytes,
    s0.sp - 96#64, s0.sp - 160#64)
  refine SepWP.fold (Entails.of_eq hss_sp96.symm) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
  refine SepWP.fold hss_mem96 (by sep_focus) ?_
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF2
  apply SepWP.of_sepWP_lscro hF2
  wp_call h_shdrop (s0.sp - 96#64, s0.sp - 160#64)
  apply blkPC_207_pairStep_0x68 (blkPl_207).base H rfl (by wp_norm_lhs) (by wp_norm_lhs)
  wp_steps
  apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
  intro hF3
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
  have hzero_len : (List.replicate 32 0#8).length = 32 := by decide
  wp_call h_cteq (s0.sp - 128#64, ss.toList,
    lsρ lsRodataCst32Sym,
    List.replicate 32 0#8, s0.sp - 160#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF4
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres : calculateAgreement X their our = none := calculateAgreement_eq_none hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.rw_pre (by rw [memRegion_24_err (s0.readReg64 (.gpr 8#5))]) ?_
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    apply SepWP.of_sepWP_lscro hF4
    wp_steps
    refine SepWP.fold hclamp_mem (by sep_focus) ?_
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF5
    wp_call h_stdrop (s0.sp - 160#64, s0.sp - 160#64)
    wp_steps
    refine SepWP.fold (rejoin_stack_calculateAgreementAt s0.sp (by omega) hzero_len hzero_len hzero_len
      (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
    simp only [hres, calculateAgreementResultAt]
    wp_done
  · have hres : calculateAgreement X their our = some ss := calculateAgreement_eq_some hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_207).base + 160#64) hF4 ?_
    apply SepWP.of_sepWP_lscro hF4
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF5
    apply SepWP.of_sepWP_lscro hF5
    wp_call h_shim (s0.sp - 160#64)
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF6
    have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call h_alloc (32, 1, s0.sp - 160#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF7
    refine SepWPp.split_alloc (sp' := s0.sp - 160#64) (by wp_norm_lhs)
      (fun halloc htr_alloc => ?_) (fun halloc halign htr_alloc => ?_)
    · refine SepWPp.of_sepWP (mid := lsρ lsHandleAllocErrorSym) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by simpa using h_pan)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.rw_pre (by
        rw [memRegion_24_ok (s0.readReg64 (.gpr 8#5)),
          memRegion_32_cells,
          ← hss_sp128]) ?_
      sep_elim_exists
      apply SepWPp.of_sepWP_ret
      apply SepWP.of_sepWP_lscro hF7
      wp_steps
      refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hss_pts _).symm) (by sep_focus) ?_
      refine SepWP.fold hclamp_mem (by sep_focus) ?_
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF8
      wp_call h_stdrop (s0.sp - 160#64, s0.sp - 160#64)
      wp_steps
      refine SepWP.fold (rejoin_stack_calculateAgreementAt s0.sp (by omega) hzero_len hss_len hzero_len
        (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (calculateAgreementResultAt_some_intro A (s0.readReg64 (.gpr 8#5))
        _ ss halloc) (by sep_focus) ?_
      rw [hres]
      wp_done

/-- Contract-backed relocatable `<PrivateKey>::calculate_agreement` (Block `207`). -/
theorem calculateAgreement_placed_ok_of_contracts [LibsignalPlacement]
    {X : Ratchet.X25519Fn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dh : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsDhSym)
      (diffieHellmanSpec X))
    (h_shdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsSharedDropSym)
      zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec))
    (h_shim : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustNoAllocShimSym)
      noAllocShimSpec)
    (h_alloc : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustAllocSym)
      (rustAllocSpec A))
    (h_stdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsStaticDropSym)
      zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec X A)) :=
  calculateAgreement_placed_ok_of_hooks_gen (subStack := allocHookStack) (by decide)
    (dhPlacedCallAt_of_raw h_dh)
    (zeroizePlacedCallAt_of_raw h_shdrop)
    (ctEqPlacedCallAt_of_withLsCodeLoaded hct)
    (shimPlacedCallAt_of_raw h_shim)
    (allocPlacedCallAt_of_allocStack h_alloc)
    (zeroizePlacedCallAt_of_raw h_stdrop)
    hpanic

/-- Relocatable `<PrivateKey>::calculate_agreement` (Block `207`) from `HookSat` hypotheses. -/
theorem calculateAgreement_placed_ok [LibsignalPlacement]
    {X : Ratchet.X25519Fn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec X A)) :=
  calculateAgreement_placed_ok_of_contracts
    (keys_ls_hook_ok_of_mem h_dh)
    (keys_ls_hook_ok_of_mem h_shdrop)
    hct
    (keys_ls_hook_ok_of_mem h_shim)
    (keys_ls_hook_ok_of_mem h_alloc)
    (keys_ls_hook_ok_of_mem h_stdrop)
    hpanic

/-- Image-free contract-backed relocatable `<PrivateKey>::calculate_agreement` (Block `207`)
taking `ctEqSliceROMemSpec`. -/
theorem calculateAgreement_placed_ok_of_contracts' [LibsignalPlacement]
    {X : Ratchet.X25519Fn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dh : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsDhSym)
      (diffieHellmanSpec X))
    (h_shdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsSharedDropSym)
      zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROMemSpec))
    (h_shim : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustNoAllocShimSym)
      noAllocShimSpec)
    (h_alloc : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsRustAllocSym)
      (rustAllocSpec A))
    (h_stdrop : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsρ lsStaticDropSym)
      zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec X A)) :=
  calculateAgreement_placed_ok_of_hooks_gen (subStack := allocHookStack) (by decide)
    (dhPlacedCallAt_of_raw h_dh)
    (zeroizePlacedCallAt_of_raw h_shdrop)
    (ctEqPlacedCallAt_of_mem_withLsCodeLoaded hct)
    (shimPlacedCallAt_of_raw h_shim)
    (allocPlacedCallAt_of_allocStack h_alloc)
    (zeroizePlacedCallAt_of_raw h_stdrop)
    hpanic

/-- Image-free relocatable `<PrivateKey>::calculate_agreement` (Block `207`) from `HookSat`
hypotheses and `ctEqSliceROMemSpec`. -/
theorem calculateAgreement_placed_ok' [LibsignalPlacement]
    {X : Ratchet.X25519Fn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROMemSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpec X A)) :=
  calculateAgreement_placed_ok_of_contracts'
    (keys_ls_hook_ok_of_mem h_dh)
    (keys_ls_hook_ok_of_mem h_shdrop)
    hct
    (keys_ls_hook_ok_of_mem h_shim)
    (keys_ls_hook_ok_of_mem h_alloc)
    (keys_ls_hook_ok_of_mem h_stdrop)
    hpanic

theorem subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec
    {pl : Obj.MultiPlacement} {X : Ratchet.X25519Fn} {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl (calculateAgreementSpec X A))) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (calculateAgreementSpecX X A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨ (withLsCodeRoLoaded pl (calculateAgreementSpec X A)).pre x s0 ∗
      (stackAt (s0.sp - 4256#64) 12288 ∗ R) := by
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec, calculateAgreementSpecX,
      calculateAgreementStackX] at hpre ⊢
    rw [stackAt_calculateAgreementExt_split s0.sp] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x (stackAt (s0.sp - 4256#64) 12288 ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec, calculateAgreementSpecX,
      calculateAgreementStackX] at hq ⊢
    rw [stackAt_calculateAgreementExt_split s0.sp]
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeRoLoaded, calculateAgreementSpec, calculateAgreementSpecX] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2
  · dsimp only [withLsCodeRoLoaded, calculateAgreementSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, calculateAgreementSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Relocatable `<PrivateKey>::calculate_agreement` (Block `207`) at `calculateAgreementStackX`. -/
theorem calculateAgreement_placed_ok_x [LibsignalPlacement]
    {X : Ratchet.X25519Fn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dh : HookSat H lsDhSym (diffieHellmanSpec X))
    (h_shdrop : HookSat H lsSharedDropSym zeroizeSecretSpec)
    (hct : subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_stdrop : HookSat H lsStaticDropSym zeroizeSecretSpec)
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_207).rebase (blkPl_207).base H) (blkPl_207).base
      (withLsCodeRoLoaded lsmpl (calculateAgreementSpecX X A)) :=
  subroutine_ok_calculateAgreementSpecX_of_calculateAgreementSpec
    (calculateAgreement_placed_ok h_dh h_shdrop hct h_shim h_alloc h_stdrop hpanic)

end CryptoVerification.LibsignalTripleRatchet.Keys
