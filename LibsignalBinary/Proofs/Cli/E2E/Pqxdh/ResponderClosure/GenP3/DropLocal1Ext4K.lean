/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropVecExt4K
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `dealloc`-Only `drop_session_structure_local1` on `tripleRatchetProgAtExt`

Proves `drop_session_structure_local1_of_dealloc_ext` and `drop_session_structure_local1_ok_ext_4k`
on `tripleRatchetProgAtExt b ext` under `AllocContractsMem4K b A ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[reducible]
private def Saved32Preserved4K (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem stackAt_ss_local1_split_4k (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal1Stack =
      stackAt (sp - 32#64) dropVecChainStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp dropVecChainStack 4 (by decide)

private theorem stackAt_dropVecChain_split_alloc_4k (fsp : BitVec 64) :
    stackAt fsp dropVecChainStack =
      memRegion (fsp - 4192#64) 96 ∗ stackAt fsp allocHookStack := by
  rw [show dropVecChainStack = allocHookStack + 96 from rfl,
      stackAt_split_bottom' fsp allocHookStack 96 (by decide)]

private theorem stackAt_dropVecChain_split_mk_4k (fsp : BitVec 64) :
    stackAt fsp dropVecChainStack =
      memRegion (fsp - 4192#64) 48 ∗ stackAt fsp dropVecMessageKeyStack := by
  rw [show dropVecChainStack = dropVecMessageKeyStack + 48 from rfl,
      stackAt_split_bottom' fsp dropVecMessageKeyStack 48 (by decide)]
  rfl

private theorem stackAt_dropVecMessageKey_split_alloc_4k (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [show dropVecMessageKeyStack = allocHookStack + 48 from rfl,
      stackAt_split_bottom' fsp allocHookStack 48 (by decide)]

private theorem tail_stack_128_from_bottom_4k (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) dropVecChainStack ∗ cells (sp - 32#64) 4 := by
  rw [← stackAt_split_bottom' sp allocHookStack 128 (by decide),
      show allocHookStack + 128 = dropSessionStructureLocal1Stack from rfl,
      ← stackAt_ss_local1_split_4k sp]

private theorem tail_dealloc_ss_local1_pre_weaken_4k (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp : BitVec 64) (fp lr x19 v3 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 32#64) dropVecChainStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    memRegion (ss + 120#64) 24 ∗ rest ∗ pool ∗
      memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    have ha1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
    have ha2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
    rw [← ha1, ← ha2]
    exact header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 32#64) dropVecChainStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_128_from_bottom_4k sp]
    cells_unfold
    refine Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x19 (Entails.sepExists_right v3 (Entails.refl _))))
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗
        stackAt (sp - 32#64) dropVecChainStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗
         (stackAt (sp - 32#64) dropVecChainStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3))) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem fnAddr_dropVecMessageKey_eq_ss_local1_add_4k (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecMessageKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

private theorem fnAddr_dropVecChain_eq_ss_local1_add_4k (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName =
      (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

@[reducible]
private def ssSender1HeadersAt_4k (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) : SepProp :=
  ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8 ∗
  ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8 ∗
  ((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16

private theorem ssSender1HeadersAt_entails_memRegions_4k (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) :
    ssSender1HeadersAt_4k ss sg ckCap ckPtr ⊢
      memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 := by
  unfold ssSender1HeadersAt_4k
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

private theorem ssSender1_memRegions_entails_104_4k (ss : BitVec 64) :
    memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 ⊢
      memRegion (ss + 144#64) 104 := by
  have heq :
      (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) =
      (memRegion (ss + 144#64) 48 ∗ memRegion (ss + 192#64) 24 ∗ memRegion (ss + 216#64) 32) := by ac_rfl
  rw [heq,
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 48) (k := 56) (b' := ss + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 192#64) (n := 24) (k := 32) (b' := ss + 216#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

private theorem optSenderChainAt_some_entails_ss_local1_4k (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜sg.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
          vecPinDealloc A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDealloc A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A ckCap ckPtr) ∗
        vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] := by
  have h := optSenderChainAt_some_entails_dealloc1 A (ss + 144#64) sg sc
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
  unfold ssSender1HeadersAt_4k
  exact Entails.of_eq (by ac_rfl)

private theorem drop_ss_local1_first3_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 12#64 →
      s.status = .Running →
      Saved32Preserved4K s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 76#64)
        s
        ((ssFirst3HeadersAt_shared_lb ss G ∗
          vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A G.root) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32Preserved4K s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 12 64
  examples_generalize_entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (36)) (P_mid :=
    (ssFirst3HeadersAt_shared_lb ss G ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_apply
      refine DropsCommon.SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (56)) (P_mid :=
      (ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_apply
        refine DropsCommon.SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (76)) s2
          ((ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A G.root) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt_shared_lb ss G ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32Preserved4K s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_apply
          refine DropsCommon.SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

private theorem drop_ss_local1_sender_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      (rustDeallocSpec A))
    (hdrop_mk : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      (dropVecMessageKeySpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 76#64 →
      s.status = .Running →
      Saved32Preserved4K s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 156#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved32Preserved4K s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  simp only [dropVecMessageKeySpec] at hdrop_mk
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 76 80
  examples_generalize_entry
  examples_hide_fetches
  intro senderG senderSt s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      have hnone : optSenderChainAt A (ss + 144#64) none none =
          (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) := by
        unfold optSenderChainAt
        have ha : (ss + 144#64) + 8#64 = ss + 152#64 := by bv_omega
        rw [ha]
      rw [hnone]
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (156)) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
            Saved32Preserved4K s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wp_steps
        wp_done
      refine SepWP.mono hstep (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
      have ha : ss + 152#64 = (ss + 144#64) + 8#64 := by bv_omega
      rw [ha]
      exact sepConj_mono_left (sender_none_entails_memRegion_104_shared_lb (ss + 144#64))
    | some _ =>
      simp only [optSenderChainAt]
      exact SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_entails_ss_local1_4k A ss sg sc)) ?_
      wp_pull_exists
      rename_i ckCap ckPtr
      refine SepWP.pure_elim ?_
      intro hcmn
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      rw [stackAt_dropVecMessageKey_split_alloc_4k fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
          vecPinDealloc A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDealloc A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame))
        (Entails.of_eq (by dsimp only [ssSender1HeadersAt_4k]; ac_rfl)) ?_
      refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (104)) (P_mid :=
        (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
          vecPinDealloc A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A ckCap ckPtr) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame))
        (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
        ?_ ?_
      · dsimp only [ssSender1HeadersAt_4k, vecPinDealloc, sgnPinDealloc]
        by_cases hcap : (sg.srk.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine DropsCommon.SepWP.align_pre (by ac_rfl) ?_
          wp_done
        · wp_steps
          wp_apply
          refine DropsCommon.SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
          wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
        refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (124)) (P_mid :=
          (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗ sgnPinDealloc A ckCap ckPtr) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 4144#64) 48 ∗ Frame))
          (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
          ?_ ?_
        · dsimp only [ssSender1HeadersAt_4k, vecPinDealloc, sgnPinDealloc]
          by_cases hcap : (sg.priv.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            wp_done
          · wp_steps
            wp_apply
            refine DropsCommon.SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
            wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (148)) (P_mid :=
            vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗
            ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
            ?_ ?_
          · have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (148)) s2
                ((ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗ sgnPinDealloc A ckCap ckPtr) ∗
                  A.pool ∗ stackAt fsp allocHookStack ∗
                  (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 4144#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
                    A.pool ∗ stackAt fsp allocHookStack ∗
                    (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 4144#64) 48 ∗ Frame)) ∧
                  Saved32Preserved4K s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              dsimp only [ssSender1HeadersAt_4k, sgnPinDealloc]
              by_cases hcap : ckCap.slt 1#64 = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
              · wp_steps
                wp_done
              · wp_steps
                wp_apply
                refine DropsCommon.SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
                wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions_4k ss sg ckCap ckPtr)) ?_
            rw [stackAt_dropVecMessageKey_split_alloc_4k fsp]
            exact Entails.of_eq (by ac_rfl)
          · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
            have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (156)) s3
                (vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                    A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
                  Saved32Preserved4K s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              wp_steps
              wp_apply
              refine DropsCommon.SepWP.align_pre (by rw [hsp_3]; ac_rfl) ?_
              wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            rw [← stackAt_dropVecMessageKey_split_alloc_4k fsp]
            exact sepConj_mono_left (ssSender1_memRegions_entails_104_4k ss)

private theorem drop_ss_local1_tail3_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 164#64 →
      s.status = .Running →
      Saved32Preserved4K s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 232#64)
        s
        ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32Preserved4K s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 164 68
  examples_generalize_entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (188)) (P_mid :=
    (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A kCap kPtr ∗
      vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_apply
      refine DropsCommon.SepWP.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (212)) (P_mid :=
      (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_apply
        refine DropsCommon.SepWP.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (232)) s2
          ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
            vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32Preserved4K s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_apply
          refine DropsCommon.SepWP.align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

set_option maxHeartbeats 1200000 in
/-- `core::ptr::drop_glue::<SessionStructure> [local#1]` meets `dropSessionStructureLocal1Spec A`
(`DropSessionStructureLocal1OkExt`) on `tripleRatchetProgAtExt b ext` assuming only `dealloc`. -/
theorem drop_session_structure_local1_of_dealloc_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)) :
    DropSessionStructureLocal1OkExt b A ext := by
  unfold DropSessionStructureLocal1OkExt
  simp only [dropSessionStructureLocal1Spec]
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  have hdealloc_raw :
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name +
          BitVec.ofNat 64
            (num% (ls_off% "__rustc::__rust_dealloc" -
              ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
        (rustDeallocSpec A) :=
    sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := deallocName) hdc
      dropSessionStructureLocal1Name
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      (by fnoff_eq)
  have hdrop_mk_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      (dropVecMessageKeySpec A) := by
    rw [← fnAddr_dropVecMessageKey_eq_ss_local1_add_4k]
    exact drop_vec_message_key_of_dealloc_ext hdc
  have hdrop_vc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")))
      (dropVecChainSpec A) := by
    rw [← fnAddr_dropVecChain_eq_ss_local1_add_4k]
    exact drop_vec_chain_of_dealloc_ext hdc
  clear hdc
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 0 12
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 156 8
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 232 40
  clear hfn
  wp_init x s0
  have hdealloc := hdealloc_raw
  have hdrop_vc := hdrop_vc_raw
  have hfirst3 := drop_ss_local1_first3_4k (b := b) (ext := ext) hdealloc_raw
  have hsender := drop_ss_local1_sender_4k (b := b) (ext := ext) hdealloc_raw hdrop_mk_raw
  have htail3 := drop_ss_local1_tail3_4k (b := b) (ext := ext) hdealloc_raw
  clear hdealloc_raw hdrop_mk_raw hdrop_vc_raw
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at hfirst3 hsender htail3 hdrop_vc hdealloc
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [stackAt_ss_local1_split_4k s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine drop4_strengthen_post (session_memRegions_entails_344_shared_lb (s0.readReg64 (Reg.gpr 0#5))) ?_
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc A (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (12))
    (P_mid :=
      (ssFirst3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 4224#64) 96 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
    (Q := fun sm =>
      Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChain_split_alloc_4k (s0.sp - 32#64)]
    have hsp_sub : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine DropsCommon.SepWP.align_pre (by dsimp only [ssFirst3HeadersAt_shared_lb, ssTail3HeadersAt_shared_lb, Reg.x19, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (76))
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropVecMessageKeyStack ∗
        (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 4224#64) 48 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
      (Q := fun sm =>
        Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropVecMessageKey_split_alloc_4k (s0.sp - 32#64)]
      have hsp_sub1 : (s0.sp - 32#64) - 4144#64 = s0.sp - 4176#64 := by bv_omega
      rw [hsp_sub1,
          ProofLib.memRegion_split' (b := s0.sp - 4224#64) (n := 48) (k := 48)
            (b' := s0.sp - 4176#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2⟩
      refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (156))
        (P_mid :=
          vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropVecChainStack ∗
          ((ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            sgnPinDealloc A pCap pPtr ∗
            sgnPinDealloc A kCap kPtr ∗
            vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
        (Q := fun sm =>
          Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hpc2 hrun2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        rw [stackAt_dropVecChain_split_mk_4k (s0.sp - 32#64)]
        have hsp_sub2 : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
        rw [hsp_sub2]
        exact Entails.of_eq (by ac_rfl)
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (164))
          (P_mid :=
            (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
              sgnPinDealloc A pCap pPtr ∗
              sgnPinDealloc A kCap kPtr ∗
              vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 4224#64) 96 ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
          (Q := fun sm =>
            Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
            sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
          ?_ ?_
        · wp_steps
          wp_apply
          refine DropsCommon.SepWP.align_pre ?_ ?_
          · rw [hsp_3, stackAt_dropVecChain_split_alloc_4k (s0.sp - 32#64)]
            have hsp_sub3 : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
            rw [hsp_sub3]
            dsimp only [ssTail3HeadersAt_shared_lb]
            ac_rfl
          · wp_done
        · intro s4 hpc4 hrun4 ⟨hpres4, hx19_4⟩
          refine DropsCommon.SepWP.seq_clean (mid := entry + bv% (232))
            (P_mid :=
              ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) dropVecChainStack ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3))
            (Q := fun sm =>
              Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
              sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                hpc4 hrun4 hpres4 hx19_4) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            rw [stackAt_dropVecChain_split_alloc_4k (s0.sp - 32#64)]
            have hsp_sub4 : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
            rw [hsp_sub4]
            exact Entails.of_eq (by ac_rfl)
          · intro s5 hpc5 hrun5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            dsimp only [vecPinDealloc]
            by_cases hcap : (G.pq.cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              refine SepWP.weaken_pre (pq_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
              wp_done
            · wp_steps
              refine SepWP.weaken_pre
                (tail_dealloc_ss_local1_pre_weaken_4k (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  _ _ _ s0.sp _ _ _ _) ?_
              wp_apply
              refine SepWP.weaken_pre (P' :=
                (memRegion (s0.readReg64 (Reg.gpr 0#5) + 120#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
                A.pool ∗
                (stackAt (s0.sp - 32#64) dropVecChainStack ∗ cells (s0.sp - 32#64) 4))
                (by rw [← tail_stack_128_from_bottom_4k s0.sp]; exact Entails.of_eq (by ac_rfl)) ?_
              cells_unfold
              wp_pull_exists
              wp_done

/-- `core::ptr::drop_glue::<SessionStructure> [local#1]` meets `DropSessionStructureLocal1OkExt b A ext`
under `AllocContractsMem4K b A ext`. -/
theorem drop_session_structure_local1_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext) :
    DropSessionStructureLocal1OkExt b A ext :=
  drop_session_structure_local1_of_dealloc_ext hA.dealloc

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
