/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.Cli.ShardFill.DropGlueErrorSignalProtocolErrorL3
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.Entry

/-!
# `ext`-Parameterized `drop_spe2`, `drop_spe2_ver`, and `pqxdh_log_closure`

Lifts `drop_spe2_ok`, `drop_spe2_ver_ok`, and `pqxdh_log_closure_ok` to
`tripleRatchetProgAtExt img.base ext` under `AllocContracts img.base A ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters hiding
  tail_stack_32_from_bottom cells4_entails_stack_bottom SatEntails
  rodata_0x3f000_eq rodata_speJumpTable_intro speJumpTable_byte
  strRefAt_entails_memRegion16 spe_u64_at_8_entails_40 spe_u8_at_8_entails_40
  spe_u8_at_32_entails_16 spe_u32x2_at_8_entails_40 spe_strRef_at_8_entails_40
  vecU8_at_8_expose spe_str_words_entails_48 spe_tail_dealloc_pre_weaken
  speAt_invalidState_expose invalidMessageStrAt_entails_vecU8
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open DropGlueFacts

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

private theorem tail_stack_32_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  rw [← stackAt_split_bottom sp allocHookStack 32 (by decide),
      show allocHookStack + 32 = dropSpeStack from rfl,
      ← stackAt_dropSpe_split sp]

private theorem cells4_entails_stack_bottom (sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack := by
  rw [tail_stack_32_from_bottom sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x20 (Entails.sepExists_right x19 (Entails.refl _))))

private def SatEntails (P Q : SepProp) : Prop :=
  ∀ (m : Memory) (R : SepProp), (m ⊨ P ∗ R) → (m ⊨ Q ∗ R)

private theorem SatEntails.refl (P : SepProp) : SatEntails P P :=
  fun _ _ hm => hm

private theorem SatEntails.of_eq {P Q : SepProp} (h : P = Q) : SatEntails P Q :=
  h ▸ SatEntails.refl P

private theorem SatEntails.of_entails {P Q : SepProp} (h : P ⊢ Q) : SatEntails P Q :=
  fun _ _ hm => Satisfies.mono (sepConj_mono_left h) hm

private theorem SatEntails.trans {P Q S : SepProp}
    (h1 : SatEntails P Q) (h2 : SatEntails Q S) : SatEntails P S :=
  fun m R hm => h2 m R (h1 m R hm)

private theorem SatEntails.drop_left (P Q : SepProp) : SatEntails (P ∗ Q) Q := by
  intro m R hm
  rw [sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.drop_right (P Q : SepProp) : SatEntails (P ∗ Q) P := by
  intro m R hm
  rw [sepConj_comm P Q, sepConj_assoc] at hm
  exact Satisfies.of_sep_right hm

private theorem SatEntails.sepConj_mono {P₁ P₂ Q₁ Q₂ : SepProp}
    (h1 : SatEntails P₁ P₂) (h2 : SatEntails Q₁ Q₂) :
    SatEntails (P₁ ∗ Q₁) (P₂ ∗ Q₂) := by
  intro m R hm
  rw [sepConj_assoc] at hm
  have hm1 := h1 m (Q₁ ∗ R) hm
  rw [← sepConj_assoc, sepConj_comm P₂ Q₁, sepConj_assoc] at hm1
  have hm2 := h2 m (P₂ ∗ R) hm1
  rw [← sepConj_assoc, sepConj_comm Q₂ P₂] at hm2
  exact hm2

private theorem SatEntails.sepConj_mono_left {P₁ P₂ : SepProp}
    (h : SatEntails P₁ P₂) {Q : SepProp} : SatEntails (P₁ ∗ Q) (P₂ ∗ Q) :=
  SatEntails.sepConj_mono h (SatEntails.refl Q)

private theorem SatEntails.sepConj_mono_right {P Q₁ Q₂ : SepProp}
    (h : SatEntails Q₁ Q₂) : SatEntails (P ∗ Q₁) (P ∗ Q₂) :=
  SatEntails.sepConj_mono (SatEntails.refl P) h

private theorem SatEntails.sepExists_elim {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, SatEntails (P x) Q) : SatEntails (∃∗ x, P x) Q := by
  intro m R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x m R hx

private theorem SatEntails.sepExists_right {α : Type} {P : SepProp} {Q : α → SepProp}
    (x : α) (h : SatEntails P (Q x)) : SatEntails P (∃∗ y, Q y) :=
  SatEntails.trans h (SatEntails.of_entails (Entails.sepExists_right x (Entails.refl _)))

private theorem weaken_pre_sat {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (himp : SatEntails P P')
    (h : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  exact h R (himp s.mem R hm)

private theorem rodata_0x3f000_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) - num% (ls_xref% 0x2440 0x2444))).take 28 = speJumpTable := by
  rfl_kernel

private theorem rodata_speJumpTable_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) (secLen := 28) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x3f000_eq] at h

private theorem intro_rodata_speJumpTable {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWP prog target_pc s
      (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (rodata_speJumpTable_intro himg hro hm)

private theorem speJumpTable_byte (base : BitVec 64) (i : Nat) (off : BitVec 64) (b : BitVec 8)
    (hoff : bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) + BitVec.ofNat 64 i = off)
    (heq : speJumpTable = speJumpTable.take i ++ (b :: speJumpTable.drop (i + 1)))
    (hlen : (speJumpTable.take i).length = i) :
    SatEntails ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) ((base + off) ↦₈ᵣ b) := by
  have h : ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) =
      ((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable.take i) ∗
        ((((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 i) ↦₈ᵣ b) ∗
         (((base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 i + 1#64) ↦ᵣ
           speJumpTable.drop (i + 1))) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h, BitVec.add_assoc base (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) (BitVec.ofNat 64 i), hoff]
  exact SatEntails.trans (SatEntails.drop_left _ _) (SatEntails.drop_right _ _)

private theorem strRefAt_entails_memRegion16 (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt a lit) (memRegion a 16) := by
  unfold strRefAt
  apply SatEntails.sepExists_elim
  intro p
  refine SatEntails.trans (SatEntails.sepConj_mono_right (SatEntails.drop_right _ _)) ?_
  apply SatEntails.of_entails
  rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a p)
    (pointsTo64_entails_memRegion (a + 8#64) _)

private theorem spe_u64_at_8_entails_40 (a : BitVec 64) (v : BitVec 64) :
    ((a + 8#64) ↦₆₄ v) ∗ memRegion (a + 16#64) 32 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) v)

private theorem spe_u8_at_8_entails_40 (a : BitVec 64) (v : BitVec 8) :
    ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39 ⊢ memRegion (a + 8#64) 40 := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 1 ∗ memRegion (a + 9#64) 39 := by
    rw [show (40 : Nat) = 1 + 39 from rfl, memRegion_split (a + 8#64) 1 39 (by decide),
        show a + 8#64 + 1#64 = a + 9#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 8#64) v)
      (IsBlock.memRegion (a + 8#64) 1) fun _ _ => trivial)

private theorem spe_u8_at_32_entails_16 (a : BitVec 64) (v : BitVec 8) :
    ((a + 32#64) ↦₈ v) ∗ memRegion (a + 33#64) 15 ⊢ memRegion (a + 32#64) 16 := by
  have h : memRegion (a + 32#64) 16 = memRegion (a + 32#64) 1 ∗ memRegion (a + 33#64) 15 := by
    rw [show (16 : Nat) = 1 + 15 from rfl, memRegion_split (a + 32#64) 1 15 (by decide),
        show a + 32#64 + 1#64 = a + 33#64 by bv_omega]
  rw [h]
  exact sepConj_mono_left
    (IsBlock.entails (IsBlock.pointsTo8 (a + 32#64) v)
      (IsBlock.memRegion (a + 32#64) 1) fun _ _ => trivial)

private theorem spe_u32x2_at_8_entails_40 (a : BitVec 64) (v1 v2 : BitVec 32) :
    ((a + 8#64) ↦₃₂ v1) ∗ ((a + 12#64) ↦₃₂ v2) ∗ memRegion (a + 16#64) 32 ⊢
      memRegion (a + 8#64) 40 := by
  have h1 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 4 ∗ memRegion (a + 12#64) 36 := by
    rw [show (40 : Nat) = 4 + 36 from rfl, memRegion_split (a + 8#64) 4 36 (by decide),
        show a + 8#64 + 4#64 = a + 12#64 by bv_omega]
  have h2 : memRegion (a + 12#64) 36 = memRegion (a + 12#64) 4 ∗ memRegion (a + 16#64) 32 := by
    rw [show (36 : Nat) = 4 + 32 from rfl, memRegion_split (a + 12#64) 4 32 (by decide),
        show a + 12#64 + 4#64 = a + 16#64 by bv_omega]
  rw [h1, h2]
  exact sepConj_mono
    (IsBlock.entails (IsBlock.pointsTo32 (a + 8#64) v1)
      (IsBlock.memRegion (a + 8#64) 4) fun _ _ => trivial)
    (sepConj_mono_left
      (IsBlock.entails (IsBlock.pointsTo32 (a + 12#64) v2)
        (IsBlock.memRegion (a + 12#64) 4) fun _ _ => trivial))

private theorem spe_strRef_at_8_entails_40 (a : BitVec 64) (lit : List (BitVec 8)) :
    SatEntails (strRefAt (a + 8#64) lit ∗ memRegion (a + 24#64) 24) (memRegion (a + 8#64) 40) := by
  have h : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 16 ∗ memRegion (a + 24#64) 24 := by
    rw [show (40 : Nat) = 16 + 24 from rfl, memRegion_split (a + 8#64) 16 24 (by decide),
        show a + 8#64 + 16#64 = a + 24#64 by bv_omega]
  rw [h]
  exact SatEntails.sepConj_mono_left (strRefAt_entails_memRegion16 (a + 8#64) lit)

private theorem vecU8_at_8_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (a + 8#64) bs ∗ memRegion (a + 32#64) 16 ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hexp := vecU8At_entails_pin_dealloc A (a + 8#64) ⟨cap, ptr⟩ bs
  unfold vecPinDealloc at hexp
  dsimp only at hexp
  refine Entails.trans (sepConj_mono_left hexp) ?_
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have h24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
  have hm : memRegion (a + 24#64) 24 = memRegion (a + 24#64) 8 ∗ memRegion (a + 32#64) 16 := by
    rw [show (24 : Nat) = 8 + 16 from rfl, memRegion_split (a + 24#64) 8 16 (by decide),
        show a + 24#64 + 8#64 = a + 32#64 by bv_omega]
  rw [h16, h24, hm]
  exact Entails.of_eq (by ac_rfl)

private theorem spe_str_words_entails_48 (a w cap ptr : BitVec 64) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ⊢
      memRegion a 48 := by
  have h1 : memRegion a 48 = memRegion a 8 ∗ memRegion (a + 8#64) 40 := by
    rw [show (48 : Nat) = 8 + 40 from rfl, memRegion_split a 8 40 (by decide)]
  have h2 : memRegion (a + 8#64) 40 = memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 := by
    rw [show (40 : Nat) = 8 + 32 from rfl, memRegion_split (a + 8#64) 8 32 (by decide),
        show a + 8#64 + 8#64 = a + 16#64 by bv_omega]
  have h3 : memRegion (a + 16#64) 32 = memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split (a + 16#64) 8 24 (by decide),
        show a + 16#64 + 8#64 = a + 24#64 by bv_omega]
  rw [h1, h2, h3]
  exact sepConj_mono (pointsTo64_entails_memRegion a w)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) cap)
      (sepConj_mono_left (pointsTo64_entails_memRegion (a + 16#64) ptr)))

private theorem spe_tail_dealloc_pre_weaken (a w cap ptr sp : BitVec 64)
    (fp lr x20 x19 : BitVec 64) (ro live pool : SepProp) :
    SatEntails
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live ∗ pool ∗ stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))
      (memRegion a 48 ∗ pool ∗ memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack ∗ live) := by
  have hro : SatEntails (ro ∗ pool) pool := SatEntails.drop_left ro pool
  have ha := SatEntails.of_entails (spe_str_words_entails_48 a w cap ptr)
  have hst := SatEntails.of_entails (cells4_entails_stack_bottom sp fp lr x20 x19)
  have hreord :
      (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24 ∗
        ro ∗ live ∗ pool ∗ stackAt (sp - 32#64) allocHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗ memRegion (a + 24#64) 24) ∗
        ((ro ∗ pool) ∗
         ((stackAt (sp - 32#64) allocHookStack ∗
           ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
           ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗ live)) := by ac_rfl
  rw [hreord]
  refine SatEntails.trans
    (SatEntails.sepConj_mono ha (SatEntails.sepConj_mono hro (SatEntails.sepConj_mono_left hst))) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem speAt_invalidState_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) :
    SatEntails (speAt A fnName a .invalidState)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 1) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  simp only [speAt]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro bs
  refine SatEntails.trans
    (SatEntails.sepConj_mono_right
      (SatEntails.sepConj_mono_right (strRefAt_entails_memRegion16 (a + 32#64) fnName))) ?_
  apply SatEntails.of_entails
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem invalidMessageStrAt_entails_vecU8 (A : RustAlloc) (a : BitVec 64)
    (r : InvalidMessageReason) :
    invalidMessageStrAt A a r ⊢ ∃∗ bs : List (BitVec 8), vecU8 A a bs := by
  cases r with
  | tooFarInFuture =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right tooFarInFutureStr (Entails.refl _)
  | macFailed =>
    simp only [invalidMessageStrAt]
    exact Entails.sepExists_right macFailedStr (Entails.refl _)
  | pqRatchet =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | badCiphertext =>
    simp only [invalidMessageStrAt]
    exact Entails.refl _
  | decryptionFailed =>
    simp only [invalidMessageStrAt]
    rw [← sepConj_emp ⌜False⌝]
    exact Entails.pure_left nofun

private theorem speAt_invalidMessage_expose (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) (t : MessageType) (r : InvalidMessageReason) :
    SatEntails (speAt A fnName a (.invalidMessage t r))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord 24) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) := by
  apply SatEntails.of_entails
  simp only [speAt]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (invalidMessageStrAt_entails_vecU8 A (a + 8#64) r)
      (spe_u8_at_32_entails_16 a (msgTypeByte t)))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  refine Entails.trans (sepConj_mono_right (vecU8_at_8_expose A a bs)) ?_
  simp only [sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem spe_str_pre_weaken (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (e : SignalProtocolError) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte)
    (he : SatEntails (speAt A fnName a e)
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ speWord i) ∗ ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗
        (if cap == 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)))
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (speAt A fnName a e ∗ rest))
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ w) ∗
        ((a + 8#64) ↦₆₄ cap) ∗ ((a + 16#64) ↦₆₄ ptr) ∗
        memRegion (a + 24#64) 24 ∗ ro_byte ∗
        (if cap == 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_left he)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SatEntails.sepExists_elim; intro cap
  apply SatEntails.sepExists_elim; intro ptr
  refine SatEntails.sepExists_right cap (SatEntails.sepExists_right ptr ?_)
  exact SatEntails.of_eq (by ac_rfl)

private theorem spe_unit_pre_weaken (A : RustAlloc) (fnName : List (BitVec 8))
    (a : BitVec 64) {ro_tbl ro_byte : SepProp} (e : SignalProtocolError) (i : Nat) (w : BitVec 64)
    (hw : speWord i = w)
    (hbyte : SatEntails ro_tbl ro_byte)
    (he : SatEntails (speAt A fnName a e) ((a ↦₆₄ speWord i) ∗ memRegion (a + 8#64) 40))
    (rest : SepProp) :
    SatEntails (ro_tbl ∗ (speAt A fnName a e ∗ rest))
      ((a ↦₆₄ w) ∗ memRegion (a + 8#64) 40 ∗ ro_byte ∗ rest) := by
  subst hw
  refine SatEntails.trans (SatEntails.sepConj_mono hbyte (SatEntails.sepConj_mono_left he)) ?_
  exact SatEntails.of_eq (by ac_rfl)

private theorem sepWP_false_elim {prog : Program} {target_pc : BitVec 64} {s : State}
    {P Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (P ∗ ⌜False⌝ ∗ Q) post := by
  unfold SepWP
  intro R hm
  have heq : (P ∗ ⌜False⌝ ∗ Q) ∗ R = ⌜False⌝ ∗ (P ∗ Q ∗ R) := by ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact False.elim hm.1

set_option maxHeartbeats 800000 in
theorem drop_spe2_of_dealloc_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.dropSpe2Name)
      ((dropSpeSpec A).inImage img) := by
  simp only [Spec.inImage, dropSpeSpec, pure_sepConj_pure_assoc]
  have hdealloc := sub_ok_at_of_fnAddr (b := img.base) (ext := ext) (sym := deallocName)
    hdealloc_fn CryptoVerification.Cli.dropSpe2Name
    (num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")))
    (by fnoff_eq)
  clear hdealloc_fn
  simp only [rustDeallocSpec] at hdealloc
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" +
        40#64) &&&
      18446744073709547520#64) = img.base + (bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40))) :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.speJumpTable_adrp_eq hb
      (fnAddr_rebase_eq_add_of_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.dropSpe2Name, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, fnName, e⟩ := x
  dsimp only at *
  subst h
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp h_2).2.1
  refine intro_rodata_speJumpTable himg hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  cases e with
  | panic =>
    simp only [speAt]
    exact sepWP_false_elim
  | invalidState =>
    refine weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidState
        1 0x8000000000000001#64 rfl
        (speJumpTable_byte img.base 1 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 1)) 0x00#8 rfl rfl rfl)
        (speAt_invalidState_expose A fnName (s0.readReg64 (Reg.gpr 0#5))) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine weaken_pre_sat
        (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre
        (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidMessage t r =>
    refine weaken_pre_sat
      (spe_str_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidMessage t r)
        24 0x8000000000000018#64 rfl
        (speJumpTable_byte img.base 24 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 24)) 0x00#8 rfl rfl rfl)
        (speAt_invalidMessage_expose A fnName (s0.readReg64 (Reg.gpr 0#5)) t r) _) ?_
    wp_pull_exists
    rename_i cap ptr
    by_cases hcap : cap = 0#64
    · simp only [hcap, beq_self_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps
      refine weaken_pre_sat
        (DropGlueFacts.spe_str_cap0_pre_weaken_full _ _ _ _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine weaken_pre_sat
        (spe_tail_dealloc_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) _ cap ptr s0.sp
          _ _ _ _ _ _ _) ?_
      wp_call hdealloc (ptr, cap.toNat, 1)
      refine SepWP.weaken_pre
        (DropGlueFacts.spe_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done
  | invalidProtobufEncoding =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidProtobufEncoding
        2 0x8000000000000002#64 rfl
        (speJumpTable_byte img.base 2 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 2)) 0x1b#8 rfl rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | ciphertextMessageTooShort n =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.ciphertextMessageTooShort n)
        3 0x8000000000000003#64 rfl
        (speJumpTable_byte img.base 3 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 3)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | legacyCiphertextVersion v =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.legacyCiphertextVersion v)
        4 0x8000000000000004#64 rfl
        (speJumpTable_byte img.base 4 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 4)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | unrecognizedCiphertextVersion v =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.unrecognizedCiphertextVersion v)
        5 0x8000000000000005#64 rfl
        (speJumpTable_byte img.base 5 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 5)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | noKeyTypeIdentifier =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .noKeyTypeIdentifier
        7 0x8000000000000007#64 rfl
        (speJumpTable_byte img.base 7 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 7)) 0x1b#8 rfl rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyType t =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyType t)
        8 0x8000000000000008#64 rfl
        (speJumpTable_byte img.base 8 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 8)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u8_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | badKeyLength n =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.badKeyLength n)
        9 0x8000000000000009#64 rfl
        (speJumpTable_byte img.base 9 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 9)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u64_at_8_entails_40 _ _))) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidKeyAgreement =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) .invalidKeyAgreement
        10 0x800000000000000a#64 rfl
        (speJumpTable_byte img.base 10 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 10)) 0x1b#8 rfl rfl rfl)
        (SatEntails.refl _) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | invalidSessionStructure r =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.invalidSessionStructure r)
        20 0x8000000000000014#64 rfl
        (speJumpTable_byte img.base 20 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 20)) 0x1b#8 rfl rfl rfl)
        (by simp only [speAt]
            exact SatEntails.sepConj_mono_right (spe_strRef_at_8_entails_40 _ _)) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done
  | duplicatedMessage idx c =>
    refine weaken_pre_sat
      (spe_unit_pre_weaken A fnName (s0.readReg64 (Reg.gpr 0#5)) (.duplicatedMessage idx c)
        23 0x8000000000000017#64 rfl
        (speJumpTable_byte img.base 23 (bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 23)) 0x1b#8 rfl rfl rfl)
        (SatEntails.of_entails
          (by simp only [speAt]; exact sepConj_mono_right (spe_u32x2_at_8_entails_40 _ _ _))) _) ?_
    wp_steps
    refine weaken_pre_sat (DropGlueFacts.spe_noop_pre_weaken_full _ _ s0.sp _ _ _ _ _ _) ?_
    wp_done

theorem drop_spe2_of_allocHooks_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hAlloc : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.dropSpe2Name)
      ((dropSpeSpec A).inImage img) :=
  drop_spe2_of_dealloc_ext himg
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext img.base A ext hAlloc deallocName 0 (Nat.add_zero _))

theorem drop_spe2_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.dropSpe2Name)
      ((dropSpeSpec A).inImage img) :=
  drop_spe2_of_dealloc_ext himg hA.dealloc

section VerAndLogClosure

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
theorem drop_spe2_ver_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (img.base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")))
      ((dropSpeVerSpec A).inImage img) := by
  simp only [Spec.inImage, dropSpeVerSpec, pure_sepConj_pure_assoc]
  have hfn_eq :
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.dropSpe2Name = img.base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) := by
    simp only [tripleRatchetProgAtExt, CryptoVerification.Cli.dropSpe2Name, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")]
  rw [← hfn_eq]
  clear hfn_eq
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" +
        40#64) &&&
      18446744073709547520#64) = img.base + (bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40))) :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.speJumpTable_adrp_eq hb
      (fnAddr_rebase_eq_add_of_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.dropSpe2Name, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, msgVer⟩ := x
  dsimp only at *
  subst h
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp h_2).2.1
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWP.intro_rodata_5a526 himg hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp lr x20 x19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨fun hm => ?_, by simp_all [arm64_norm], by simp_all [CalleeSavedPreserved, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  refine ⟨by simp_all [arm64_norm], ?_⟩
  have ha := spe_ver_entails_48 (s0.readReg64 (Reg.gpr 0#5)) msgVer
  have hst := cells4_entails_dropSpeStack s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
  rw [sepConj_assoc ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) ↦₈ᵣ 27#8)] at hm
  have hm1 := Satisfies.of_sep_right hm
  have hent :
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ 9223372036854775814#64 ∗
        (s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₃₂ msgVer ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 12#64) 36 ∗
            A.pool ∗
              stackAt (s0.sp - 32#64) allocHookStack ∗
                (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                  (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ A.pool ∗ stackAt s0.sp dropSpeStack :=
    Entails.trans
      (Q := (((s0.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x8000000000000006#64) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₃₂ msgVer) ∗
             memRegion (s0.readReg64 (Reg.gpr 0#5) + 12#64) 36) ∗
            A.pool ∗
            (stackAt (s0.sp - 32#64) allocHookStack ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
      (Entails.of_eq (by ac_rfl))
      (sepConj_mono ha (sepConj_mono (Entails.refl A.pool) hst))
  have hm2 := Satisfies.mono (sepConj_mono_left hent) hm1
  simpa only [sepConj_assoc] using hm2

private theorem stackAt_pqxdhClosure (sp : BitVec 64) :
    stackAt sp pqxdhClosureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) ∗
      stackAt (sp - 96#64) 304 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 336 12 (by decide)
  have h2 := stackAt_split_bottom (sp - 96#64) 304 32 (by decide)
  have hsub : (sp - 96#64) - BitVec.ofNat 64 (304 + 32) = sp - 432#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (32 : Nat) = 8 * 4 by rfl,
      ProofLib.memRegion_cells (sp - 432#64) 4 (by decide)] at h2
  change stackAt sp pqxdhClosureStack = stackAt (sp - 96#64) 336 ∗ cells (sp - 96#64) 12 at h1
  have hc4 : cells (sp - 432#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 432#64) ↦₆₄ v0) ∗ ((sp - 424#64) ↦₆₄ v1) ∗
        ((sp - 416#64) ↦₆₄ v2) ∗ ((sp - 408#64) ↦₆₄ v3)) := by
    cells_unfold
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
        ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ∗
        ((sp - 48#64) ↦₆₄ w6) ∗ ((sp - 40#64) ↦₆₄ w7) ∗ ((sp - 32#64) ↦₆₄ w8) ∗
        ((sp - 24#64) ↦₆₄ w9) ∗ ((sp - 16#64) ↦₆₄ w10) ∗ ((sp - 8#64) ↦₆₄ w11)) := by
    cells_unfold
  rw [h1, h2, hc4, hc12, sepConj_assoc]

private theorem pqxdhLogClosure_adrp_addr_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 36#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 36)))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  subst he; bv_arith

set_option maxHeartbeats 800000 in
theorem pqxdh_log_closure_ok_ext {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName)
      ((pqxdhLogClosureSpec img).inImage img) := by
  simp only [Spec.inImage, pqxdhLogClosureSpec, logOff, CryptoVerification.LibsignalSession.logFilterAddr, stackAt_pqxdhClosure,
    sepExists_sepConj_left, sepExists_sepConj_right]
  unfold tripleRatchetProgAtExt
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName =
      (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") :=
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hentry : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName =
      img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, hfn]
  have hadrp : (((((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName + 36#64) &&&
      18446744073709547520#64) + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 36) - (page% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 36)))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 36) (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" + 44)) % 4096)) = img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) :=
    pqxdhLogClosure_adrp_addr_eq hb hentry
  clear hentry
  responder_fetches_from_cli img.base
    (Rust.withPanics ext) hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") 0 56
  responder_fetches_from_cli img.base
    (Rust.withPanics ext) hfn (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") 0x310 32
  clear hfn himg
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName = entry
  wp_init x s0
  examples_hide_fetches
  wp_steps
  wp_done

end VerAndLogClosure

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
