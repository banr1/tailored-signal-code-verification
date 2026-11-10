/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropsChainExt
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `drop_glue::<SessionStructure> [local#1]` (`0x25b4`)

Verifies `core::ptr::drop_glue::<SessionStructure> [local#1]` (`0x25b4`, Block `6`) against
`dropSessionStructureLocal1SpecX A` on `SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts CryptoVerification.LibsignalTripleRatchet.FromRecordCallees Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_DropSsLocal1Ext : True := trivial

@[reducible]
def Saved32Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧ s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

@[reducible] def ssPresQ (s0 : State) (fsp ss : BitVec 64) : State → Prop :=
  fun sm => Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss

theorem stackAt_dropSessionStructureLocal1StackX_eq :
    dropSessionStructureLocal1StackX = 32 + dropVecChainStackX := rfl

theorem stackAt_ss_local1_split_x (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal1StackX =
      stackAt (sp - 32#64) dropVecChainStackX ∗ cells (sp - 32#64) 4 := by
  have heq : dropSessionStructureLocal1StackX = dropVecChainStackX + 8 * 4 := by
    change 32 + (48 + (48 + Stage1X.extHookStack)) = (48 + (48 + Stage1X.extHookStack)) + 32; omega
  rw [heq]; exact LibsignalTripleRatchet.stackAt_split_cells sp dropVecChainStackX 4 (by decide)

theorem stackAt_dropVecChainX_split_alloc (fsp : BitVec 64) :
    stackAt fsp dropVecChainStackX = memRegion (fsp - 16480#64) 96 ∗ stackAt fsp Stage1X.extHookStack :=
  ProofLib.stackAt_split_bottom fsp Stage1X.extHookStack 96 (by decide)

theorem stackAt_dropVecChainX_split_mk (fsp : BitVec 64) :
    stackAt fsp dropVecChainStackX = memRegion (fsp - 16480#64) 48 ∗ stackAt fsp dropVecMessageKeyStackX := by
  have heq : dropVecChainStackX = dropVecMessageKeyStackX + 48 := by
    change 48 + dropVecMessageKeyStackX = dropVecMessageKeyStackX + 48; omega
  rw [heq]; have h := ProofLib.stackAt_split_bottom fsp dropVecMessageKeyStackX 48 (by decide)
  have hsub : fsp - BitVec.ofNat 64 (dropVecMessageKeyStackX + 48) = fsp - 16480#64 := rfl
  rwa [hsub] at h

theorem stackAt_dropVecMessageKeyX_split_alloc (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStackX = memRegion (fsp - 16432#64) 48 ∗ stackAt fsp Stage1X.extHookStack :=
  stackAt_dropVecMessageKeyX_split_bottom fsp

theorem tail_stack_128_from_bottom_ext (sp : BitVec 64) :
    memRegion (sp - 16512#64) 128 ∗ stackAt sp Stage1X.extHookStack =
      stackAt (sp - 32#64) dropVecChainStackX ∗ cells (sp - 32#64) 4 := by
  have hsplit := ProofLib.stackAt_split_bottom sp Stage1X.extHookStack 128 (by decide)
  have hext : sp - BitVec.ofNat 64 (Stage1X.extHookStack + 128) = sp - 16512#64 := rfl
  rw [hext] at hsplit; rw [← hsplit, show Stage1X.extHookStack + 128 = dropSessionStructureLocal1StackX from rfl, stackAt_ss_local1_split_x]

theorem ss_epilogue_pure_extract (A : RustAlloc) (ss : BitVec 64) (pq : VecPin)
    (hcap : ¬(pq.cap == 0#64) = true) (Rest : SepProp) :
    ((ss + 120#64) ↦₆₄ pq.cap) ∗ ((ss + 128#64) ↦₆₄ pq.ptr) ∗ memRegion (ss + 136#64) 8 ∗
      vecPinDeallocX A pq ∗ Rest =
    ⌜pq.cap.toNat < 2 ^ 63⌝ ∗
      (((ss + 120#64) ↦₆₄ pq.cap) ∗ ((ss + 128#64) ↦₆₄ pq.ptr) ∗ memRegion (ss + 136#64) 8 ∗
        (A.live pq.ptr pq.cap.toNat 1 ∗ memRegion pq.ptr pq.cap.toNat) ∗ Rest) := by
  unfold vecPinDeallocX
  have hfalse : ((pq.cap == 0#64) = true) = False := eq_false hcap
  simp only [hfalse, ↓reduceIte]
  ac_rfl

theorem tail_dealloc_ss_local1_pre_weaken_ext (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp : BitVec 64) (fp lr x19 v3 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 32#64) dropVecChainStackX ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    memRegion (ss + 120#64) 24 ∗ rest ∗ pool ∗
      memRegion (sp - 16512#64) 128 ∗ stackAt sp Stage1X.extHookStack ∗ live := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    rw [← show (ss + 120#64) + 8#64 = ss + 128#64 by bv_omega, ← show (ss + 120#64) + 16#64 = ss + 136#64 by bv_omega]
    exact header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 32#64) dropVecChainStackX ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      memRegion (sp - 16512#64) 128 ∗ stackAt sp Stage1X.extHookStack := by
    rw [tail_stack_128_from_bottom_ext sp]; cells_unfold
    exact Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x19 (Entails.sepExists_right v3 (Entails.refl _))))
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗ stackAt (sp - 32#64) dropVecChainStackX ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗ ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗ (stackAt (sp - 32#64) dropVecChainStackX ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗ ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3))) := by ac_rfl
  rw [hreord]
  exact Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) (Entails.of_eq (by ac_rfl))

theorem fnAddr_dropVecMessageKey_eq_ss_local1_add_ext (img : Obj.Image)
    (ext : String → Option (State → State)) :
    (SP2Ext img.base ext).fnAddr dropVecMessageKeyName =
      (SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) := by
  unfold SP2Ext
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

theorem fnAddr_dropVecChain_eq_ss_local1_add_ext (img : Obj.Image)
    (ext : String → Option (State → State)) :
    (SP2Ext img.base ext).fnAddr dropVecChainName =
      (SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) := by
  unfold SP2Ext
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

theorem dealloc_ok_at_state_ss1_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    {entry : BitVec 64} {s : State}
    (hdealloc : subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP2Ext b ext)
      (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      { pre := fun (p, size, align) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = size ∧
            (s'.readReg64 .x2).toNat = align ∧ LayoutOk size align⌝ ∗
          A.live p size align ∗ memRegion p size ∗
          A.pool ∗ stackAt s'.sp Stage1X.extHookStack
        post := (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).post } := by
  refine subroutine_ok_mono_entails hdealloc (fun ⟨p, size, align⟩ s0 => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack]
  exact pure_and_entails_pure_sep_of_x fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq (s0 := s0) (s := s) hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem drop_vec_chain_ok_at_state_ext {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {target : BitVec 64} {s : State}
    (hdrop_vc : subroutine_ok prog target
      ((dropVecChainSpecX A).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok prog target
      { pre := fun x s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧ s'.readReg64 .x0 = x.v⌝ ∗
          vecAt A 104 8 (chainAt A) x.v x.cap x.ptr x.cs ∗ A.pool ∗
          stackAt s'.sp dropVecChainStackX
        post := (dropVecChainSpecX A).post } := by
  refine subroutine_ok_mono_entails hdrop_vc (fun x s0 => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [Spec.inImage, dropVecChainSpecX]
  exact pure_and_entails_pure_sep_of_x fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq (s0 := s0) (s := s) hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem dealloc_ok_at_ss_local1_raw {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img) :=
  hA.dealloc_ok_at (name := dropSessionStructureLocal1Name)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) (by simp only [arm64_norm])

abbrev sgnPinDeallocX := ckDeallocX

theorem optTailVecAt_entails_dealloc_x (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        sgnPinDeallocX A cap ptr := by
  cases opt with
  | none =>
    unfold optTailVecAt
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    rw [hsplit,
        ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
          (b' := a + 16#64) rfl (by bv_omega) (by omega),
        ProofLib.memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right noneCap (Entails.sepExists_right ptr ?_)
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [sgnPinDeallocX, ckDeallocX, hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some g =>
    unfold optTailVecAt
    apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          sgnPinDeallocX A g.vec.cap g.vec.ptr := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader sgnPinDeallocX ckDeallocX
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      by_cases hc : g.vec.cap = 0
      · simp only [hc, ↓reduceIte, sepConj_emp, emp_sepConj]
        exact Entails.refl _
      · have hfalse : (g.vec.cap = 0) = False := eq_false hc
        have hslt_false : (g.vec.cap.slt 1#64 = true) = False := by
          apply eq_false; rw [slt_one_iff_eq_zero hcap_lt]; exact hc
        simp only [hfalse, hslt_false, ↓reduceIte]
        exact Entails.trans (Entails.pure_right hcap_lt (Entails.refl _)) (Entails.of_eq (by ac_rfl))
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
          sgnPinDeallocX A g.vec.cap g.vec.ptr) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          sgnPinDeallocX A g.vec.cap g.vec.ptr) := by
      ac_rfl
    rw [hpull1]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

theorem optChainKeyAt_entails_dealloc_x (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        sgnPinDeallocX A cap ptr :=
  optChainKeyAt_entails_deallocX A pin ck a

@[reducible]
def ssFirst3HeadersAt (ss : BitVec 64) (G : SessionGhost) : SepProp :=
  (ss ↦₆₄ G.localIk.cap) ∗ ((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗ memRegion (ss + 16#64) 8 ∗
  ((ss + 24#64) ↦₆₄ G.remoteIk.cap) ∗ ((ss + 32#64) ↦₆₄ G.remoteIk.ptr) ∗ memRegion (ss + 40#64) 8 ∗
  ((ss + 48#64) ↦₆₄ G.root.cap) ∗ ((ss + 56#64) ↦₆₄ G.root.ptr) ∗ memRegion (ss + 64#64) 8

theorem ssFirst3_entails_dealloc_x (A : RustAlloc) (ss : BitVec 64)
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
  have hofs : ((ss + 24#64) + 8#64 = ss + 32#64) ∧ ((ss + 24#64) + 16#64 = ss + 40#64) ∧
      ((ss + 48#64) + 8#64 = ss + 56#64) ∧ ((ss + 48#64) + 16#64 = ss + 64#64) := by and_intros <;> bv_omega
  rcases hofs with ⟨ha1, ha2, hb1, hb2⟩
  rw [ha1, ha2] at h2; rw [hb1, hb2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  unfold ssFirst3HeadersAt
  exact Entails.of_eq (by ac_rfl)

theorem ssFirst3HeadersAt_entails_memRegions_x (ss : BitVec 64) (G : SessionGhost) :
    ssFirst3HeadersAt ss G ⊢
      memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 := by
  unfold ssFirst3HeadersAt
  have h1 := header_cells_entails_memRegion_24 ss G.localIk.cap G.localIk.ptr
  have h2 := header_cells_entails_memRegion_24 (ss + 24#64) G.remoteIk.cap G.remoteIk.ptr
  have h3 := header_cells_entails_memRegion_24 (ss + 48#64) G.root.cap G.root.ptr
  rw [show (ss + 24#64) + 8#64 = ss + 32#64 by bv_omega, show (ss + 24#64) + 16#64 = ss + 40#64 by bv_omega] at h2
  rw [show (ss + 48#64) + 8#64 = ss + 56#64 by bv_omega, show (ss + 48#64) + 16#64 = ss + 64#64 by bv_omega] at h3
  refine Entails.trans ?_ (sepConj_mono h1 (sepConj_mono h2 h3))
  exact Entails.of_eq (by ac_rfl)

@[reducible]
def ssTail3HeadersAt (ss : BitVec 64) (pCap pPtr kCap kPtr : BitVec 64)
    (G : SessionGhost) : SepProp :=
  ((ss + 248#64) ↦₆₄ pCap) ∗ ((ss + 256#64) ↦₆₄ pPtr) ∗ memRegion (ss + 264#64) 32 ∗
  ((ss + 296#64) ↦₆₄ kCap) ∗ ((ss + 304#64) ↦₆₄ kPtr) ∗ memRegion (ss + 312#64) 16 ∗
  ((ss + 96#64) ↦₆₄ G.alice.cap) ∗ ((ss + 104#64) ↦₆₄ G.alice.ptr) ∗ memRegion (ss + 112#64) 8

theorem ssTail3_entails_dealloc_x (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost) :
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      vecGhostAt A G.alice (ss + 0x60#64) ⊢
    ∃∗ pCap : BitVec 64, ∃∗ pPtr : BitVec 64, ∃∗ kCap : BitVec 64, ∃∗ kPtr : BitVec 64,
      ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDeallocX A pCap pPtr ∗
      sgnPinDeallocX A kCap kPtr ∗
      vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩ := by
  have h1 := optTailVecAt_entails_dealloc_x A 48 (by decide) (by decide) (ss + 248#64) G.pending
  have h2 := optTailVecAt_entails_dealloc_x A 32 (by decide) (by decide) (ss + 296#64) G.kyber
  have h3 := vecGhostAt_entails_pin_deallocX A G.alice (ss + 96#64)
  have hofs : ((ss + 248#64) + 8#64 = ss + 256#64) ∧ ((ss + 248#64) + 16#64 = ss + 264#64) ∧
      ((ss + 296#64) + 8#64 = ss + 304#64) ∧ ((ss + 296#64) + 16#64 = ss + 312#64) ∧
      ((ss + 96#64) + 8#64 = ss + 104#64) ∧ ((ss + 96#64) + 16#64 = ss + 112#64) := by and_intros <;> bv_omega
  rcases hofs with ⟨ha1, ha2, hb1, hb2, hc1, hc2⟩
  rw [ha1, ha2] at h1; rw [hb1, hb2] at h2; rw [hc1, hc2] at h3
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

theorem header_cells_entails_memRegion_48 (a cap ptr : BitVec 64) :
    ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32) ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem ssTail3HeadersAt_entails_memRegions_x (ss : BitVec 64)
    (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) :
    ssTail3HeadersAt ss pCap pPtr kCap kPtr G ⊢
      memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24 := by
  unfold ssTail3HeadersAt
  have h1 := header_cells_entails_memRegion_48 (ss + 248#64) pCap pPtr
  have h2 := header_cells_entails_memRegion_32 (ss + 296#64) kCap kPtr
  have h3 := header_cells_entails_memRegion_24 (ss + 96#64) G.alice.cap G.alice.ptr
  rw [show (ss + 248#64) + 8#64 = ss + 256#64 by bv_omega, show (ss + 248#64) + 16#64 = ss + 264#64 by bv_omega] at h1
  rw [show (ss + 296#64) + 8#64 = ss + 304#64 by bv_omega, show (ss + 296#64) + 16#64 = ss + 312#64 by bv_omega] at h2
  rw [show (ss + 96#64) + 8#64 = ss + 104#64 by bv_omega, show (ss + 96#64) + 16#64 = ss + 112#64 by bv_omega] at h3
  refine Entails.trans ?_ (sepConj_mono h1 (sepConj_mono h2 h3))
  exact Entails.of_eq (by ac_rfl)

theorem sessionTail_entails_memRegion_16 (ss : BitVec 64)
    (v1 v2 : BitVec 32) (regIds : List (BitVec 8)) (hreg : regIds.length = 8) :
    ((ss + 0x148#64) ↦₃₂ v1) ∗ ((ss + 0x14c#64) ↦₃₂ v2) ∗ ((ss + 0x150#64) ↦ₛ regIds) ⊢
      memRegion (ss + 328#64) 16 := by
  rw [ProofLib.memRegion_split' (b := ss + 328#64) (n := 4) (k := 12) (b' := ss + 332#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 332#64) (n := 4) (k := 8) (b' := ss + 336#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo32_entails_memRegion _ _) ?_)
  have hb := pointsToBytes_entails_memRegion (ss + 336#64) regIds
  rwa [hreg] at hb

theorem sessionStateAt_entails_dealloc_x (A : RustAlloc) (ss : BitVec 64)
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
  have h1 := ssFirst3_entails_dealloc_x A ss G st
  have h2 := ssTail3_entails_dealloc_x A ss G
  have h3 := vecU8At_entails_pin_deallocX A (ss + 120#64) G.pq st.pqRatchetState
  rw [show (ss + 120#64) + 8#64 = ss + 128#64 by bv_omega, show (ss + 120#64) + 16#64 = ss + 136#64 by bv_omega] at h3
  have h4 := sessionTail_entails_memRegion_16 ss st.sessionVersion st.previousCounter G.regIds hreg
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono h2 (sepConj_mono h3 h4))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply Entails.sepExists_elim; intro x; refine Entails.sepExists_right x ?_)
  exact Entails.of_eq (by ac_rfl)

@[reducible]
def ssSender1HeadersAt (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) : SepProp :=
  ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8 ∗
  ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8 ∗
  ((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16

theorem ssSender1HeadersAt_entails_memRegions_x (ss : BitVec 64) (sg : SenderChainGhost)
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

theorem cap_add_one_ne_zero_x {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_arith

theorem optSenderChainAt_some_entails_dealloc1_x (A : RustAlloc) (a : BitVec 64)
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
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
    refine Entails.pure_right (cap_add_one_ne_zero_x hcap_lt) ?_
    unfold vecHeader vecPinDeallocX
    have hbeq : ((g.srk.cap == 0#64) = true) ↔ g.srk.cap = 0 := beq_iff_eq
    simp only [hbeq]
    have hgroup1 : ((a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.srk.bytes.length)) ∗
        (if g.srk.cap = 0 then emp else A.live g.srk.ptr g.srk.cap.toNat 1 ∗ memRegion g.srk.ptr g.srk.cap.toNat) =
        (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.srk.bytes.length) ∗
          (if g.srk.cap = 0 then emp else A.live g.srk.ptr g.srk.cap.toNat 1 ∗ memRegion g.srk.ptr g.srk.cap.toNat)) := by ac_rfl
    have hgroup2 : (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ memRegion (a + 16#64) 8 ∗
        (if g.srk.cap = 0 then emp else ⌜g.srk.cap.toNat < 2 ^ 63⌝ ∗ (A.live g.srk.ptr g.srk.cap.toNat 1 ∗ memRegion g.srk.ptr g.srk.cap.toNat)) =
        (a ↦₆₄ g.srk.cap) ∗ ((a + 8#64) ↦₆₄ g.srk.ptr) ∗ (memRegion (a + 16#64) 8 ∗
          (if g.srk.cap = 0 then emp else ⌜g.srk.cap.toNat < 2 ^ 63⌝ ∗ (A.live g.srk.ptr g.srk.cap.toNat 1 ∗ memRegion g.srk.ptr g.srk.cap.toNat))) := by ac_rfl
    rw [hgroup1, hgroup2]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
    by_cases hc : g.srk.cap = 0
    · simp only [hc, ite_true]; exact Entails.refl _
    · simp only [hc, ite_false]; exact Entails.pure_right hcap_lt (Entails.refl _)
  have h2 := vecGhostAt_entails_pin_deallocX A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_dealloc_x A g.ck (some sc.chainKey) (a + 72#64)
  have hofs : ((a + 24#64) + 8#64 = a + 32#64) ∧ ((a + 24#64) + 16#64 = a + 40#64) ∧
      ((a + 72#64) + 8#64 = a + 80#64) ∧ ((a + 72#64) + 16#64 = a + 88#64) := by and_intros <;> bv_omega
  rcases hofs with ⟨ha1, ha2, hc1, hc2⟩
  rw [ha1, ha2] at h2; rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ckCap; refine Entails.sepExists_right ckCap ?_
  apply Entails.sepExists_elim; intro ckPtr; refine Entails.sepExists_right ckPtr ?_
  exact Entails.of_eq (by ac_rfl)

theorem optSenderChainAt_some_entails_ss_local1_x (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜sg.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (ssSender1HeadersAt ss sg ckCap ckPtr ∗
          vecPinDeallocX A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDeallocX A ckCap ckPtr) ∗
        vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] := by
  have h := optSenderChainAt_some_entails_dealloc1_x A (ss + 144#64) sg sc
  have hofs : ((ss + 144#64) + 8#64 = ss + 152#64) ∧ ((ss + 144#64) + 16#64 = ss + 160#64) ∧
      ((ss + 144#64) + 24#64 = ss + 168#64) ∧ ((ss + 144#64) + 32#64 = ss + 176#64) ∧
      ((ss + 144#64) + 40#64 = ss + 184#64) ∧ ((ss + 144#64) + 48#64 = ss + 192#64) ∧
      ((ss + 144#64) + 72#64 = ss + 216#64) ∧ ((ss + 144#64) + 80#64 = ss + 224#64) ∧
      ((ss + 144#64) + 88#64 = ss + 232#64) := by and_intros <;> bv_omega
  rcases hofs with ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9⟩
  rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9] at h
  refine Entails.trans h ?_
  apply Entails.sepExists_elim; intro ckCap; refine Entails.sepExists_right ckCap ?_
  apply Entails.sepExists_elim; intro ckPtr; refine Entails.sepExists_right ckPtr ?_
  unfold ssSender1HeadersAt
  exact Entails.of_eq (by ac_rfl)

theorem SepWP.align_pre_ss1 {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (heq : P = P_mid)
    (h : SepWP prog target s P_mid (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) := by
  cases heq
  exact h

theorem hcap_false_elim {cap : BitVec 64} (hcap : ((cap == 0#64) = true) = False) (hc : cap.toNat = 0) : False := by
  have h0 : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
  subst h0; revert hcap; decide

theorem hslt_false_elim {cap : BitVec 64} (hcap : ((cap.slt 1#64 = true) = False)) (hc : cap.toNat = 0) : False := by
  have h0 : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
  subst h0; revert hcap; decide

theorem drop_ss_local1_first3_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + 12#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (SP2Ext img.base ext)
        ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + 76#64)
        s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A G.root) ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          img.FrozenLoaded sm ∧
          sm.symtab = img.symtab) := by
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 12 64
  dsimp only [SP2Ext, contractProg, dropSessionStructureLocal1Name, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  examples_generalize_entry
  examples_hide_fetches
  intro G s Frame hfl hsym hpc hrun hpres hx0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_clean_inv (mid := entry + bv% (36)) (target_pc := entry + bv% (76)) hfl hsym
    (P_mid :=
      (ssFirst3HeadersAt ss G ∗
        vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A G.root) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
    (Q := ssPresQ s0 fsp ss) ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
    by_cases hcap : (G.localIk.cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
    · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
      have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl hsym
      wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.localIk.ptr, G.localIk.cap.toNat, 1)
      refine SepWP.align_pre_ss1 (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩ hfl_1 hsym_1
    refine SepWP.seq_clean_inv (mid := entry + bv% (56)) (target_pc := entry + bv% (76)) hfl_1 hsym_1
      (P_mid :=
        (ssFirst3HeadersAt ss G ∗ vecPinDeallocX A G.root) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
      (Q := ssPresQ s0 fsp ss) ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true
      · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
      · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
        have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl_1 hsym_1
        wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1)
        refine SepWP.align_pre_ss1 (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩ hfl_2 hsym_2
      have hstep3 : SepWP (SP2Ext img.base ext) (entry + bv% (76)) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDeallocX A G.root) ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
        by_cases hcap : (G.root.cap == 0#64) = true
        · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
        · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
          have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl_2 hsym_2
          wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.root.ptr, G.root.cap.toNat, 1)
          refine SepWP.align_pre_ss1 (by rw [hsp_2]; ac_rfl) ?_; wp_done
      refine SepWP.finish_inv hfl_2 hsym_2 ?_
      refine SepWP.mono hstep3 (fun sm Pm _ _ h hfl' hsym' =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions_x ss G)), h.2.1, h.2.2, hfl', hsym'⟩)

theorem ssSender1_memRegions_entails_104_x (ss : BitVec 64) :
    memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 ⊢
      memRegion (ss + 144#64) 104 := by
  rw [show (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) =
      (memRegion (ss + 144#64) 48 ∗ memRegion (ss + 192#64) 24 ∗ memRegion (ss + 216#64) 32) by ac_rfl,
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 48) (k := 56) (b' := ss + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 192#64) (n := 24) (k := 32) (b' := ss + 216#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem sender_none_entails_memRegion_104_x (a : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96) ⊢ memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 96) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)

theorem session_memRegions_entails_344_x (ss : BitVec 64) :
    memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
      memRegion (ss + 72#64) 24 ∗ memRegion (ss + 96#64) 24 ∗ memRegion (ss + 120#64) 24 ∗
      memRegion (ss + 144#64) 104 ∗ memRegion (ss + 248#64) 48 ∗
      memRegion (ss + 296#64) 32 ∗ memRegion (ss + 328#64) 16 ⊢ memRegion ss 344 := by
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

theorem pq_header24_weaken_x (ss cap ptr : BitVec 64) (Rest : SepProp) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗ Rest ⊢
      memRegion (ss + 120#64) 24 ∗ Rest := by
  have h := header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  rw [show (ss + 120#64) + 8#64 = ss + 128#64 by bv_omega, show (ss + 120#64) + 16#64 = ss + 136#64 by bv_omega] at h
  refine Entails.trans ?_ (sepConj_mono_left h)
  exact Entails.of_eq (by ac_rfl)

theorem SepWP.false_elim_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {Q : SepProp} {post : State → SepProp → Prop} :
    SepWP prog target_pc s (⌜False⌝ ∗ Q) post :=
  SepWP.pure_elim (fun h => False.elim h)

theorem drop_ss_local1_sender_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (hdrop_mk : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      ((dropVecMessageKeySpecX A).inImage img))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + 76#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (SP2Ext img.base ext)
        ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + 156#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          img.FrozenLoaded sm ∧
          sm.symtab = img.symtab) := by
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 76 80
  dsimp only [SP2Ext, contractProg, dropSessionStructureLocal1Name, BitVec.ofNat_eq_ofNat] at hdealloc hdrop_mk ⊢
  examples_generalize_entry
  examples_hide_fetches
  intro senderG senderSt s Frame hfl hsym hpc hrun hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      have hnone : optSenderChainAt A (ss + 144#64) none none =
          (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) := by
        unfold optSenderChainAt; rw [show (ss + 144#64) + 8#64 = ss + 152#64 by bv_omega]
      rw [hnone]
      have hstep : SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (entry + bv% (156)) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]; wp_steps; wp_done
      refine SepWP.finish_inv hfl hsym ?_
      refine SepWP.mono hstep (fun sm Pm _ _ h => fun hfl' hsym' => ⟨Entails.trans h.1 ?_, h.2.1, h.2.2, hfl', hsym'⟩)
      rw [show ss + 152#64 = (ss + 144#64) + 8#64 by bv_omega]
      exact sepConj_mono_left (sender_none_entails_memRegion_104_x (ss + 144#64))
    | some _ => simp only [optSenderChainAt]; exact SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none => simp only [optSenderChainAt]; exact SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_entails_ss_local1_x A ss sg sc)) ?_
      wp_pull_exists
      rename_i ckCap ckPtr
      refine SepWP.pure_elim ?_
      intro hcmn
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      rw [stackAt_dropVecMessageKeyX_split_alloc fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt ss sg ckCap ckPtr ∗
          vecPinDeallocX A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDeallocX A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Entails.of_eq (by dsimp only [ssSender1HeadersAt]; ac_rfl)) ?_
      refine SepWP.seq_clean_inv (mid := entry + bv% (104)) (target_pc := entry + bv% (156)) hfl hsym
        (P_mid :=
          (ssSender1HeadersAt ss sg ckCap ckPtr ∗
            vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
            sgnPinDeallocX A ckCap ckPtr) ∗
          A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
          (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Q := ssPresQ s0 fsp ss) ?_ ?_
      · dsimp only [ssSender1HeadersAt, vecPinDeallocX, sgnPinDeallocX, ckDeallocX]
        by_cases hcap : (sg.srk.cap == 0#64) = true
        · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
        · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
          have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl hsym
          wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (sg.srk.ptr, sg.srk.cap.toNat, 1)
          refine SepWP.align_pre_ss1 (by rw [hsp]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩ hfl_1 hsym_1
        refine SepWP.seq_clean_inv (mid := entry + bv% (124)) (target_pc := entry + bv% (156)) hfl_1 hsym_1
          (P_mid :=
            (ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A ckCap ckPtr) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
            (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              memRegion (fsp - 16432#64) 48 ∗ Frame))
          (Q := ssPresQ s0 fsp ss) ?_ ?_
        · dsimp only [ssSender1HeadersAt, vecPinDeallocX, sgnPinDeallocX, ckDeallocX]
          by_cases hcap : (sg.priv.cap == 0#64) = true
          · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
          · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
            have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl_1 hsym_1
            wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (sg.priv.ptr, sg.priv.cap.toNat, 1)
            refine SepWP.align_pre_ss1 (by rw [hsp_1]; ac_rfl) ?_; wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩ hfl_2 hsym_2
          refine SepWP.seq_clean_inv (mid := entry + bv% (148)) (target_pc := entry + bv% (156)) hfl_2 hsym_2
            (P_mid :=
              vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := ssPresQ s0 fsp ss) ?_ ?_
          · have hstep3 : SepWP (SP2Ext img.base ext) (entry + bv% (148)) s2
                ((ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A ckCap ckPtr) ∗
                  A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
                  (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 16432#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt ss sg ckCap ckPtr ∗
                    A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
                    (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              dsimp only [ssSender1HeadersAt, sgnPinDeallocX, ckDeallocX]
              by_cases hcap : ckCap.slt 1#64 = true
              · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
              · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
                refine SepWP.pure_elim fun hcap_lt => ?_
                have hlayout := layoutOk_u8_x (fun hc => hslt_false_elim (eq_false hcap) hc) hcap_lt
                have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl_2 hsym_2
                wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (ckPtr, ckCap.toNat, 1)
                refine SepWP.align_pre_ss1 (by rw [hsp_2]; ac_rfl) ?_; wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions_x ss sg ckCap ckPtr)) ?_
            rw [stackAt_dropVecMessageKeyX_split_alloc fsp]; exact Entails.of_eq (by ac_rfl)
          · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩ hfl_3 hsym_3
            have hdrop_mk0 := drop_vec_message_key_ok_at_state_ext hdrop_mk hfl_3 hsym_3
            refine SepWP.finish_inv hfl_3 hsym_3 ?_
            have hstep4 : SepWP (SP2Ext img.base ext) (entry + bv% (156)) s3
                (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                    A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              wp_steps; wp_call hdrop_mk0 ⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩
              refine SepWP.align_pre_ss1 (by rw [hsp_3]; ac_rfl) ?_; wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h hfl' hsym' => by
              have h1 := h.1
              rw [stackAt_dropVecMessageKeyX_split_alloc fsp] at h1
              exact ⟨Entails.trans h1 (sepConj_mono_left (ssSender1_memRegions_entails_104_x ss)), h.2.1, h.2.2, hfl', hsym'⟩)

theorem drop_ss_local1_tail3_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack).inImage img))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      img.FrozenLoaded s →
      s.symtab = img.symtab →
      s.pc = (SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + 164#64 →
      s.status = .Running →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (SP2Ext img.base ext)
        ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + 232#64)
        s
        ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A pCap pPtr ∗
          sgnPinDeallocX A kCap kPtr ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          img.FrozenLoaded sm ∧
          sm.symtab = img.symtab) := by
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 164 68
  dsimp only [SP2Ext, contractProg, dropSessionStructureLocal1Name, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  examples_generalize_entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hfl hsym hpc hrun hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_clean_inv (mid := entry + bv% (188)) (target_pc := entry + bv% (232)) hfl hsym
    (P_mid :=
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        sgnPinDeallocX A kCap kPtr ∗
        vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
    (Q := ssPresQ s0 fsp ss) ?_ ?_
  · dsimp only [ssTail3HeadersAt, sgnPinDeallocX, ckDeallocX, vecPinDeallocX]
    by_cases hcap : pCap.slt 1#64 = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
    · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := layoutOk_u8_x (fun hc => hslt_false_elim (eq_false hcap) hc) hcap_lt
      have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl hsym
      wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (pPtr, pCap.toNat, 1)
      refine SepWP.align_pre_ss1 (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩ hfl_1 hsym_1
    refine SepWP.seq_clean_inv (mid := entry + bv% (212)) (target_pc := entry + bv% (232)) hfl_1 hsym_1
      (P_mid :=
        (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
      (Q := ssPresQ s0 fsp ss) ?_ ?_
    · dsimp only [ssTail3HeadersAt, sgnPinDeallocX, ckDeallocX, vecPinDeallocX]
      by_cases hcap : kCap.slt 1#64 = true
      · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
      · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := layoutOk_u8_x (fun hc => hslt_false_elim (eq_false hcap) hc) hcap_lt
        have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl_1 hsym_1
        wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (kPtr, kCap.toNat, 1)
        refine SepWP.align_pre_ss1 (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩ hfl_2 hsym_2
      have hstep3 : SepWP (SP2Ext img.base ext) (entry + bv% (232)) s2
          ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt, vecPinDeallocX]
        by_cases hcap : (G.alice.cap == 0#64) = true
        · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
        · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
          have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl_2 hsym_2
          wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.alice.ptr, G.alice.cap.toNat, 1)
          refine SepWP.align_pre_ss1 (by rw [hsp_2]; ac_rfl) ?_; wp_done
      refine SepWP.finish_inv hfl_2 hsym_2 ?_
      refine SepWP.mono hstep3 (fun sm Pm _ _ h => fun hfl' hsym' =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions_x ss pCap pPtr kCap kPtr G)), h.2.1, h.2.2, hfl', hsym'⟩)

theorem drop4_strengthen_post_x {prog : Program} {target_pc : BitVec 64} {s : State}
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

@[reducible] def ssSavedFrame (sp fp lr x19 v3 : BitVec 64) : SepProp :=
  ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗ ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3)

@[reducible] def ssPqPart (A : RustAlloc) (ss : BitVec 64) (pq : VecPin) : SepProp :=
  ((ss + 120#64) ↦₆₄ pq.cap) ∗ ((ss + 128#64) ↦₆₄ pq.ptr) ∗ memRegion (ss + 136#64) 8 ∗ vecPinDeallocX A pq

@[reducible] def ssTail3Dealloc (A : RustAlloc) (ss pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) : SepProp :=
  ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗ sgnPinDeallocX A pCap pPtr ∗ sgnPinDeallocX A kCap kPtr ∗ vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩
@[reducible] def ssFirst3Mem (ss : BitVec 64) : SepProp :=
  memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24
@[reducible] def ss9MemRegions (ss : BitVec 64) : SepProp :=
  memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
  memRegion (ss + 72#64) 24 ∗ memRegion (ss + 96#64) 24 ∗ memRegion (ss + 144#64) 104 ∗
  memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 328#64) 16

theorem drop_session_structure_local1_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    DropSessionStructureLocal1OkX img A ext := by
  unfold DropSessionStructureLocal1OkX
  simp only [dropSessionStructureLocal1SpecX]
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  have hdealloc_raw := dealloc_ok_at_ss_local1_raw hA
  have hdrop_mk_raw : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      ((dropVecMessageKeySpecX A).inImage img) := by
    rw [← fnAddr_dropVecMessageKey_eq_ss_local1_add_ext]
    exact drop_vec_message_key_ok_ext hA
  have hdrop_vc_raw : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      ((dropVecChainSpecX A).inImage img) := by
    rw [← fnAddr_dropVecChain_eq_ss_local1_add_ext]
    exact drop_vec_chain_ok_ext hA
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 0 12
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 156 8
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 232 40
  clear hfn
  wp_init x s0
  have hdealloc := hdealloc_raw
  have hdrop_vc := hdrop_vc_raw
  have hfirst3 := drop_ss_local1_first3_ext (A := A) (img := img) (ext := ext) hdealloc_raw
  have hsender := drop_ss_local1_sender_ext (A := A) (img := img) (ext := ext) hdealloc_raw hdrop_mk_raw
  have htail3 := drop_ss_local1_tail3_ext (A := A) (img := img) (ext := ext) hdealloc_raw
  clear hdealloc_raw hdrop_mk_raw hdrop_vc_raw
  dsimp only [SP2Ext, contractProg, dropSessionStructureLocal1Name, BitVec.ofNat_eq_ofNat] at hfirst3 hsender htail3 hdrop_vc hdealloc
  dsimp only [SP2Ext, contractProg, dropSessionStructureLocal1Name, BitVec.ofNat_eq_ofNat]
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [stackAt_ss_local1_split_x s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine drop4_strengthen_post_x (session_memRegions_entails_344_x (s0.readReg64 (Reg.gpr 0#5))) ?_
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc_x A (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine SepWP.seq_clean_inv (mid := entry + bv% (12)) (target_pc := s0.readReg64 .lr) h_2 h_1
    (P_mid :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) Stage1X.extHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 96 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
    (Q := fun sm =>
      Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
    have hsp_sub : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine SepWP.align_pre_ss1 (by dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt, ssTail3Dealloc, ssPqPart, ssSavedFrame, Reg.x19, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩ hfl_1 hsym_1
    refine SepWP.seq_clean_inv (mid := entry + bv% (76)) (target_pc := s0.readReg64 .lr) hfl_1 hsym_1
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropVecMessageKeyStackX ∗
        (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 48 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
      (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hfl_1 hsym_1 hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2.1, h.2.2.1⟩
      rw [stackAt_dropVecMessageKeyX_split_alloc (s0.sp - 32#64)]
      have hsp_sub1 : (s0.sp - 32#64) - 16432#64 = s0.sp - 16464#64 := by bv_omega
      rw [hsp_sub1,
          ProofLib.memRegion_split' (b := s0.sp - 16512#64) (n := 48) (k := 48)
            (b' := s0.sp - 16464#64) rfl (by bv_omega) (by decide)]
      dsimp only [ssFirst3Mem]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2⟩ hfl_2 hsym_2
      refine SepWP.seq_clean_inv (mid := entry + bv% (156)) (target_pc := s0.readReg64 .lr) hfl_2 hsym_2
        (P_mid :=
          vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropVecChainStackX ∗
          (ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          ssPqPart A (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
          ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
        (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hfl_2 hsym_2 hpc2 hrun2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2.1, h.2.2.1⟩
        rw [stackAt_dropVecChainX_split_mk (s0.sp - 32#64)]
        have hsp_sub2 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
        rw [hsp_sub2]
        exact Entails.of_eq (by ac_rfl)
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩ hfl_3 hsym_3
        refine SepWP.seq_clean_inv (mid := entry + bv% (164)) (target_pc := s0.readReg64 .lr) hfl_3 hsym_3
          (P_mid :=
            ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            A.pool ∗ stackAt (s0.sp - 32#64) Stage1X.extHookStack ∗
            (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
            ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 16512#64) 96 ∗
            ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
          (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
          ?_ ?_
        · have hs3_align : (s3.sp &&& 15#64 == 0#64) = true := by
            rw [hsp_3]; exact hfsp_align
          wp_steps
          have hdrop_vc0 := drop_vec_chain_ok_at_state_ext hdrop_vc hfl_3 hsym_3
          wp_call hdrop_vc0 ⟨s0.readReg64 (Reg.gpr 0#5) + 72#64, G.chainsCap, G.chainsPtr,
            G.chains.zip st.receiverChains⟩
          refine SepWP.align_pre_ss1 ?_ ?_
          · rw [hsp_3, stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
            have hsp_sub3 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub3]; dsimp only [ssTail3HeadersAt, ssTail3Dealloc, ssFirst3Mem, ssSavedFrame]; ac_rfl
          · wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩ hfl_4 hsym_4
          refine SepWP.seq_clean_inv (mid := entry + bv% (232)) (target_pc := s0.readReg64 .lr) hfl_4 hsym_4
            (P_mid :=
              ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq ∗
              ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) dropVecChainStackX ∗
              ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
            (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
            ?_ ?_
          · refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                hfl_4 hsym_4 hpc4 hrun4 ⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩ hx19_4) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2.1, h.2.2.1⟩
            rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
            have hsp_sub4 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub4]
            dsimp only [ss9MemRegions, ssFirst3Mem]
            exact Entails.of_eq (by ac_rfl)
          · intro s5 hpc5 hrun5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩ hfl_5 hsym_5
            dsimp only [ssSavedFrame]
            by_cases hcap : (G.pq.cap == 0#64) = true
            · dsimp only [vecPinDeallocX]
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
              wp_steps
              refine SepWP.weaken_pre (pq_header24_weaken_x (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
              wp_done
            · rw [ss_epilogue_pure_extract A (s0.readReg64 (Reg.gpr 0#5)) G.pq hcap]
              refine SepWP.pure_elim fun hcap_lt => ?_
              have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
              have hdealloc0 := dealloc_ok_at_state_ss1_ext (entry := entry) hdealloc hfl_5 hsym_5
              wp_steps
              refine SepWP.weaken_pre
                (tail_dealloc_ss_local1_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  _ _ _ s0.sp _ _ _ _) ?_
              have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
              wp_call hdealloc0 (G.pq.ptr, G.pq.cap.toNat, 1)
              refine SepWP.weaken_pre (P' :=
                (memRegion (s0.readReg64 (Reg.gpr 0#5) + 120#64) 24 ∗
                  ss9MemRegions (s0.readReg64 (Reg.gpr 0#5))) ∗
                A.pool ∗
                (stackAt (s0.sp - 32#64) dropVecChainStackX ∗ cells (s0.sp - 32#64) 4))
                (by rw [← tail_stack_128_from_bottom_ext s0.sp]; dsimp only [ss9MemRegions]; exact Entails.of_eq (by ac_rfl)) ?_
              cells_unfold; wp_pull_exists; wp_done

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `6`) -/

section Placed

private theorem seq_clean_lscl_ss1 [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

private theorem drop_ss_local1_placed_first3_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 12#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 76#64)
        s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A G.root) ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  intro G s Frame hpc hrun hcl hpres hx0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_clean_lscl_ss1 hcl (mid := (blkPl_6).base + 36#64)
    (P_mid :=
      (ssFirst3HeadersAt ss G ∗
        vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A G.root) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
    (Q := ssPresQ s0 fsp ss) ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
    by_cases hcap : (G.localIk.cap == 0#64) = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
    · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
      have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl
      wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.localIk.ptr, G.localIk.cap.toNat, 1)
      refine SepWP.align_pre_ss1 (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl_ss1 hcl1 (mid := (blkPl_6).base + 56#64)
      (P_mid :=
        (ssFirst3HeadersAt ss G ∗ vecPinDeallocX A G.root) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
      (Q := ssPresQ s0 fsp ss) ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true
      · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
      · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
        have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl1
        wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1)
        refine SepWP.align_pre_ss1 (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 76#64) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDeallocX A G.root) ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt, vecPinDeallocX]
        by_cases hcap : (G.root.cap == 0#64) = true
        · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
        · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
          have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl2
          wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.root.ptr, G.root.cap.toNat, 1)
          refine SepWP.align_pre_ss1 (by rw [hsp_2]; ac_rfl) ?_; wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions_x ss G)), h.2⟩)

private theorem drop_ss_local1_placed_sender_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsmpl.base 3) (withLsCl lsmpl (dropVecMessageKeySpecX A)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 76#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 156#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  intro senderG senderSt s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      have hnone : optSenderChainAt A (ss + 144#64) none none =
          (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) := by
        unfold optSenderChainAt; rw [show (ss + 144#64) + 8#64 = ss + 152#64 by bv_omega]
      rw [hnone]
      have hstep : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]; wp_steps; wp_done
      refine SepWP.mono hstep (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
      rw [show ss + 152#64 = (ss + 144#64) + 8#64 by bv_omega]
      exact sepConj_mono_left (sender_none_entails_memRegion_104_x (ss + 144#64))
    | some _ => simp only [optSenderChainAt]; exact SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none => simp only [optSenderChainAt]; exact SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_entails_ss_local1_x A ss sg sc)) ?_
      wp_pull_exists
      rename_i ckCap ckPtr
      refine SepWP.pure_elim fun hcmn => ?_
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      rw [stackAt_dropVecMessageKeyX_split_alloc fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt ss sg ckCap ckPtr ∗
          vecPinDeallocX A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDeallocX A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Entails.of_eq (by dsimp only [ssSender1HeadersAt]; ac_rfl)) ?_
      refine seq_clean_lscl_ss1 hcl (mid := (blkPl_6).base + 104#64)
        (P_mid :=
          (ssSender1HeadersAt ss sg ckCap ckPtr ∗
            vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
            sgnPinDeallocX A ckCap ckPtr) ∗
          A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
          (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Q := ssPresQ s0 fsp ss) ?_ ?_
      · dsimp only [ssSender1HeadersAt, vecPinDeallocX, sgnPinDeallocX, ckDeallocX]
        by_cases hcap : (sg.srk.cap == 0#64) = true
        · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
        · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
          have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl
          wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (sg.srk.ptr, sg.srk.cap.toNat, 1)
          refine SepWP.align_pre_ss1 (by rw [hsp]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
        refine seq_clean_lscl_ss1 hcl1 (mid := (blkPl_6).base + 124#64)
          (P_mid :=
            (ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A ckCap ckPtr) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
            (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              memRegion (fsp - 16432#64) 48 ∗ Frame))
          (Q := ssPresQ s0 fsp ss) ?_ ?_
        · dsimp only [ssSender1HeadersAt, vecPinDeallocX, sgnPinDeallocX, ckDeallocX]
          by_cases hcap : (sg.priv.cap == 0#64) = true
          · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
          · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
            have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl1
            wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (sg.priv.ptr, sg.priv.cap.toNat, 1)
            refine SepWP.align_pre_ss1 (by rw [hsp_1]; ac_rfl) ?_; wp_done
        · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          refine seq_clean_lscl_ss1 hcl2 (mid := (blkPl_6).base + 148#64)
            (P_mid :=
              vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := ssPresQ s0 fsp ss) ?_ ?_
          · have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 148#64) s2
                ((ssSender1HeadersAt ss sg ckCap ckPtr ∗ sgnPinDeallocX A ckCap ckPtr) ∗
                  A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
                  (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 16432#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt ss sg ckCap ckPtr ∗
                    A.pool ∗ stackAt fsp Stage1X.extHookStack ∗
                    (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              dsimp only [ssSender1HeadersAt, sgnPinDeallocX, ckDeallocX]
              by_cases hcap : ckCap.slt 1#64 = true
              · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
              · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
                refine SepWP.pure_elim fun hcap_lt => ?_
                have hlayout := layoutOk_u8_x (fun hc => hslt_false_elim (eq_false hcap) hc) hcap_lt
                have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl2
                wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (ckPtr, ckCap.toNat, 1)
                refine SepWP.align_pre_ss1 (by rw [hsp_2]; ac_rfl) ?_; wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions_x ss sg ckCap ckPtr)) ?_
            rw [stackAt_dropVecMessageKeyX_split_alloc fsp]; exact Entails.of_eq (by ac_rfl)
          · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
            have hstep4 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s3
                (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                    A.pool ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 3)
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              intro hcl_mk
              have hdrop_mk0 := lscall_of_withLsCl hdrop_mk hcl_mk
              wp_call hdrop_mk0 ⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩
              refine SepWP.align_pre_ss1 (by rw [hsp_3]; ac_rfl) ?_; wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h => ?_)
            rw [← stackAt_dropVecMessageKeyX_split_alloc fsp]
            exact ⟨Entails.trans h.1 (sepConj_mono_left (ssSender1_memRegions_entails_104_x ss)), h.2⟩

private theorem drop_ss_local1_placed_tail3_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ CryptoVerification.lsRustDeallocSym)
      (withLsCl lsmpl (Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A Stage1X.extHookStack)))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 164#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 232#64)
        s
        ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDeallocX A pCap pPtr ∗
          sgnPinDeallocX A kCap kPtr ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_clean_lscl_ss1 hcl (mid := (blkPl_6).base + 188#64)
    (P_mid :=
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        sgnPinDeallocX A kCap kPtr ∗
        vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
    (Q := ssPresQ s0 fsp ss) ?_ ?_
  · dsimp only [ssTail3HeadersAt, sgnPinDeallocX, ckDeallocX, vecPinDeallocX]
    by_cases hcap : pCap.slt 1#64 = true
    · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
    · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlayout := layoutOk_u8_x (fun hc => hslt_false_elim (eq_false hcap) hc) hcap_lt
      have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl
      wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (pPtr, pCap.toNat, 1)
      refine SepWP.align_pre_ss1 (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl_ss1 hcl1 (mid := (blkPl_6).base + 212#64)
      (P_mid :=
        (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
      (Q := ssPresQ s0 fsp ss) ?_ ?_
    · dsimp only [ssTail3HeadersAt, sgnPinDeallocX, ckDeallocX, vecPinDeallocX]
      by_cases hcap : kCap.slt 1#64 = true
      · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
      · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlayout := layoutOk_u8_x (fun hc => hslt_false_elim (eq_false hcap) hc) hcap_lt
        have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl1
        wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (kPtr, kCap.toNat, 1)
        refine SepWP.align_pre_ss1 (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 232#64) s2
          ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗ A.pool ∗ stackAt fsp Stage1X.extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt, vecPinDeallocX]
        by_cases hcap : (G.alice.cap == 0#64) = true
        · simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]; wp_steps; refine SepWP.align_pre_ss1 (by ac_rfl) ?_; wp_done
        · simp only [eq_false hcap, ↓reduceIte, sepConj_assoc, ProofLib.sepConj_pure_left_comm]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
          have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl2
          wp_steps; have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩; wp_call hdealloc0 (G.alice.ptr, G.alice.cap.toNat, 1)
          refine SepWP.align_pre_ss1 (by rw [hsp_2]; ac_rfl) ?_; wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions_x ss pCap pPtr kCap kPtr G)), h.2⟩)

/-- Relocatable `core::ptr::drop_glue::<SessionStructure> [local#1]` (Block `6`) satisfies
`withLsCodeLoaded lsmpl (dropSessionStructureLocal1SpecX A)` under
`Stage1X.AllocContractsPlaced A H`. -/
theorem drop_session_structure_local1_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    DropSessionStructureLocal1PlacedOkX A H := by
  unfold DropSessionStructureLocal1PlacedOkX
  unfold withLsCodeLoaded dropSessionStructureLocal1SpecX
  wp_init x s0
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ss
  have hdealloc_raw := hA.dealloc (callerProg := (blkPC_6).rebase (blkPl_6).base H)
  have hdrop_mk_raw := drop_vec_message_key_placed_ok_cl
    (callerProg := (blkPC_6).rebase (blkPl_6).base H) hA
  have hdrop_vc_raw := drop_vec_chain_placed_ok_cl
    (callerProg := (blkPC_6).rebase (blkPl_6).base H) hA
  have hdealloc := hdealloc_raw
  have hdrop_vc := hdrop_vc_raw
  have hfirst3 := drop_ss_local1_placed_first3_ext hdealloc_raw
  have hsender := drop_ss_local1_placed_sender_ext hdealloc_raw hdrop_mk_raw
  have htail3 := drop_ss_local1_placed_tail3_ext hdealloc_raw
  clear hdealloc_raw hdrop_mk_raw hdrop_vc_raw
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [stackAt_ss_local1_split_x s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine drop4_strengthen_post_x (session_memRegions_entails_344_x (s0.readReg64 (Reg.gpr 0#5))) ?_
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc_x A (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine seq_clean_lscl_ss1 hcl0 (mid := (blkPl_6).base + 12#64)
    (P_mid :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) Stage1X.extHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 96 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
    (Q := fun sm =>
      Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
    have hsp_sub : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine SepWP.align_pre_ss1 (by dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt, ssTail3Dealloc, ssPqPart, ssSavedFrame, Reg.x19, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hpres1, hx0_1⟩
    refine seq_clean_lscl_ss1 hcl1 (mid := (blkPl_6).base + 76#64)
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropVecMessageKeyStackX ∗
        (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 48 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
      (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hpc1 hrun1 hcl1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropVecMessageKeyX_split_alloc (s0.sp - 32#64)]
      have hsp_sub1 : (s0.sp - 32#64) - 16432#64 = s0.sp - 16464#64 := by bv_omega
      rw [hsp_sub1,
          ProofLib.memRegion_split' (b := s0.sp - 16512#64) (n := 48) (k := 48)
            (b' := s0.sp - 16464#64) rfl (by bv_omega) (by decide)]
      dsimp only [ssFirst3Mem]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2⟩
      refine seq_clean_lscl_ss1 hcl2 (mid := (blkPl_6).base + 156#64)
        (P_mid :=
          vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropVecChainStackX ∗
          (ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          ssPqPart A (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
          ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
        (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hpc2 hrun2 hcl2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        rw [stackAt_dropVecChainX_split_mk (s0.sp - 32#64)]
        have hsp_sub2 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
        rw [hsp_sub2]
        exact Entails.of_eq (by ac_rfl)
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean_lscl_ss1 hcl3 (mid := (blkPl_6).base + 164#64)
          (P_mid :=
            ssTail3Dealloc A (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            A.pool ∗ stackAt (s0.sp - 32#64) Stage1X.extHookStack ∗
            (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
            ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 16512#64) 96 ∗
            ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
          (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
          ?_ ?_
        · have hs3_align : (s3.sp &&& 15#64 == 0#64) = true := by
            rw [hsp_3]; exact hfsp_align
          apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 2)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro hcl_vc
          have hdrop_vc0 := lscall_of_withLsCl hdrop_vc hcl_vc
          wp_call hdrop_vc0 ⟨s0.readReg64 (Reg.gpr 0#5) + 72#64, G.chainsCap, G.chainsPtr,
            G.chains.zip st.receiverChains⟩
          refine SepWP.align_pre_ss1 ?_ ?_
          · rw [hsp_3, stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
            have hsp_sub3 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub3]; dsimp only [ssTail3HeadersAt, ssTail3Dealloc, ssFirst3Mem, ssSavedFrame]; ac_rfl
          · wp_done
        · intro s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine seq_clean_lscl_ss1 hcl4 (mid := (blkPl_6).base + 232#64)
            (P_mid :=
              ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A G.pq ∗
              ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) dropVecChainStackX ∗
              ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
            (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
            ?_ ?_
          · refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                hpc4 hrun4 hcl4 ⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩ hx19_4) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
            have hsp_sub4 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub4]
            dsimp only [ss9MemRegions, ssFirst3Mem]
            exact Entails.of_eq (by ac_rfl)
          · intro s5 hpc5 hrun5 hcl5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            dsimp only [ssSavedFrame]
            by_cases hcap : (G.pq.cap == 0#64) = true
            · dsimp only [vecPinDeallocX]
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
              wp_steps
              refine SepWP.weaken_pre (pq_header24_weaken_x (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
              wp_done
            · rw [ss_epilogue_pure_extract A (s0.readReg64 (Reg.gpr 0#5)) G.pq hcap]
              refine SepWP.pure_elim fun hcap_lt => ?_
              have hlayout := layoutOk_u8_x (fun hc => hcap_false_elim (eq_false hcap) hc) hcap_lt
              have hdealloc0 := dealloc_placed_ok_at_stateX hdealloc hcl5
              wp_steps
              refine SepWP.weaken_pre
                (tail_dealloc_ss_local1_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  _ _ _ s0.sp _ _ _ _) ?_
              have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
              wp_call hdealloc0 (G.pq.ptr, G.pq.cap.toNat, 1)
              refine SepWP.weaken_pre (P' :=
                (memRegion (s0.readReg64 (Reg.gpr 0#5) + 120#64) 24 ∗
                  ss9MemRegions (s0.readReg64 (Reg.gpr 0#5))) ∗
                A.pool ∗
                (stackAt (s0.sp - 32#64) dropVecChainStackX ∗ cells (s0.sp - 32#64) 4))
                (by rw [← tail_stack_128_from_bottom_ext s0.sp]; dsimp only [ss9MemRegions]; exact Entails.of_eq (by ac_rfl)) ?_
              cells_unfold; wp_pull_exists; wp_done

theorem drop_session_structure_local1_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hA : Proofs.libsignal.Stage1X.AllocContractsPlaced A H) :
    subroutine_ok callerProg (lsmpl.base 6)
      (withLsCl lsmpl (dropSessionStructureLocal1SpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (drop_session_structure_local1_placed_ok_ext hA)

end Placed
