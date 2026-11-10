/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessage
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Verification of `drop_glue<Vec<Chain>>`

Proves `dropVecChainSpec` for
`core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>`
on `tripleRatchetProgAt` and under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Getters

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open DropGlueFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?


private theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 :=
  DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr

private theorem chain_memRegions_entails_104 (a : BitVec 64) :
    memRegion (a + 48#64) 24 ∗ memRegion a 48 ∗ memRegion (a + 72#64) 32 ⊢ memRegion a 104 :=
  DropGlueFacts.chain_memRegions_entails_104 a


private theorem fnAddr_dropVecMessageKey_eq_dropVecChain_add (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecMessageKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 180#64 := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"), (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")]
  bv_omega

private theorem stackAt_dropVecMessageKey_split_bottom (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [← stackAt_split_bottom fsp allocHookStack 48 (by decide)]
  rfl

private theorem tail_stack_96_from_bottom (sp : BitVec 64) :
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack =
      stackAt (sp - 48#64) dropVecMessageKeyStack ∗ cells (sp - 48#64) 6 := by
  rw [← stackAt_split_bottom sp allocHookStack 96 (by decide),
      show allocHookStack + 96 = dropVecChainStack from rfl,
      ← stackAt_dropVecChain_split sp]

private theorem cells6_vecChain_entails_stack_bottom (sp : BitVec 64)
    (fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 48#64) dropVecMessageKeyStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack := by
  rw [tail_stack_96_from_bottom sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

private theorem tail_dealloc_vecChain_pre_weaken (v cap ptr : BitVec 64) (Live Pool : SepProp)
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      Live ∗ Pool ∗
      stackAt (sp - 48#64) dropVecMessageKeyStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    Pool ∗ Live ∗ stackAt sp allocHookStack ∗
      (memRegion v 24 ∗ memRegion (sp - 4192#64) 96) := by
  refine Entails.trans (header24_weaken v cap ptr _) ?_
  have hstk := cells6_vecChain_entails_stack_bottom sp fp lr x22 x21 x20 x19
  have hgroup :
      (memRegion v 24 ∗ Live ∗ Pool ∗
        stackAt (sp - 48#64) dropVecMessageKeyStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) =
      ((stackAt (sp - 48#64) dropVecMessageKeyStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ∗
        (Pool ∗ Live ∗ memRegion v 24)) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_left hstk) ?_
  apply Entails.of_eq
  ac_rfl

private theorem drop_vec_chain_body {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
      (rustDeallocSpec A))
    (hdrop_mk : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 180#64)
      (dropVecMessageKeySpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 56#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = cnt →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 44#64)
        s
        (chainAt A (g, c) cur ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧
          sm.readReg64 .x22 = cnt) := by
  simp only [rustDeallocSpec] at hdealloc
  simp only [dropVecMessageKeySpec] at hdrop_mk
  dsimp only [tripleRatchetProgAtExt, dropVecChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  intro cur cnt g c s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_dealloc A cur g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  rw [stackAt_dropVecMessageKey_split_bottom fsp]
  refine DropGlueFacts.seq_clean (mid := entry + bv% (76)) (P_mid :=
    (chainOuterHeadersAt cur g ckCap ckPtr ∗
      vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDealloc A ckCap ckPtr) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗
    (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
      memRegion (fsp - 4144#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
    ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine DropGlueFacts.align_pre (by ac_rfl) ?_
      wp_done
    · wp_steps
      wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine DropGlueFacts.seq_clean (mid := entry + bv% (96)) (P_mid :=
      (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 4144#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
      ?_ ?_
    · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
      by_cases hcap : (g.priv.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_apply
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine DropGlueFacts.seq_clean (mid := entry + bv% (36)) (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗
        ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
        ?_ ?_
      · have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (36)) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗
              (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 4144#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                A.pool ∗ stackAt fsp allocHookStack ∗
                (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 4144#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          dsimp only [chainOuterHeadersAt, ckDealloc]
          by_cases hcap : ckCap.slt 1#64 = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            wp_done
          · wp_steps
            wp_apply
            wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [stackAt_dropVecMessageKey_split_bottom fsp]
        apply Entails.of_eq
        ac_rfl
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        rw [← stackAt_dropVecMessageKey_split_bottom fsp]
        have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + bv% (44)) s3
            (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          wp_steps
          wp_apply
          refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
          wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chain_memRegions_entails_104 cur)), h.2⟩)

private theorem drop_vec_chain_loop {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
      (rustDeallocSpec A))
    (hdrop_mk : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 180#64)
      (dropVecMessageKeySpec A))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 56#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 124#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_chain_body hdealloc hdrop_mk s0 fsp v ptr hfsp_align
  dsimp only [tripleRatchetProgAtExt, dropVecChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (chainAt A) 104 cur ((g, c) :: tl) =
          chainAt A (g, c) cur ∗ arrayAt (chainAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine DropGlueFacts.seq_clean (mid := entry + bv% (44))
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c s
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      wp_steps
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption)
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4
          (by simp only [wp_norm, arm64_norm, add_104_add_48])
          rfl) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

theorem drop_vec_chain_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName)
      (dropVecChainSpec A) := by
  simp only [dropVecChainSpec]
  have hdealloc_raw := hA.dealloc_ok_at dropVecChainName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")]; simp only [arm64_norm])
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hdrop_mk_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropVecChainName + 180#64)
      (dropVecMessageKeySpec A) := by
    rw [← fnAddr_dropVecMessageKey_eq_dropVecChain_add]
    exact drop_vec_message_key_ok_ext hA
  have hloop := drop_vec_chain_loop (b := b) (ext := ext) hdealloc_raw hdrop_mk_raw
  code_fetches libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") (num% (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>")) 180
  dsimp only [tripleRatchetProgAtExt, dropVecChainName, BitVec.ofNat_eq_ofNat] at hdealloc hloop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, cs⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChain_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine DropGlueFacts.seq_clean (mid := entry + bv% (124))
    (P_mid :=
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      wp_steps
      have hpre_eq :
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
            (if cap = 0 then emp
             else A.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
          (arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStack ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              (if cap = 0 then emp
               else A.live ptr (cap.toNat * 104) 8 ∗
                 memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
        ac_rfl
      rw [hpre_eq]
      refine SepWP.mono
        (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align (hd :: tl) ptr _ _
          (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl rfl rfl rfl) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      apply Entails.of_eq
      ac_rfl
  · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre (post_loop_weaken A (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (DropGlueFacts.cap0_weaken_48_vecChain (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · wp_steps
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.weaken_pre
        (tail_dealloc_vecChain_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ _ s0.sp _ _ _ _ _ _) ?_
      wp_apply
      refine SepWP.weaken_pre (DropGlueFacts.vecChain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done

theorem drop_vec_chain_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropVecChainName)
      (dropVecChainSpec A) :=
  drop_vec_chain_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

theorem drop_vec_chain_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropVecChainName)
      (dropVecChainSpec A) :=
  subroutine_ok_kit_of_trTrap (drop_vec_chain_ok_trap hA)

/-! ## Relocatable `[LibsignalPlacement]` Contract -/

open Arm64.Obj CryptoVerification

private theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  apply sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

private theorem drop_vec_chain_placed_body [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec A)))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain)
      (s : State) (Frame : SepProp),
      s.pc = (blkPl_2).base + 56#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = cnt →
      SepWP ((blkPC_2).rebase (blkPl_2).base H)
        ((blkPl_2).base + 44#64)
        s
        (chainAt A (g, c) cur ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧
          sm.readReg64 .x22 = cnt) := by
  simp only [rustDeallocSpec] at hdealloc
  simp only [withLsCodeLoaded, dropVecMessageKeySpec] at hdrop_mk
  intro cur cnt g c s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_dealloc A cur g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  rw [stackAt_dropVecMessageKey_split_bottom fsp]
  refine seq_clean_lscl hcl (mid := (blkPl_2).base + 76#64) (P_mid :=
    (chainOuterHeadersAt cur g ckCap ckPtr ∗
      vecPinDealloc A ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDealloc A ckCap ckPtr) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗
    (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
      memRegion (fsp - 4144#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
    ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine DropGlueFacts.align_pre (by ac_rfl) ?_
      wp_done
    · wp_steps; wp_apply
      refine DropGlueFacts.align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_clean_lscl hcl1 (mid := (blkPl_2).base + 96#64) (P_mid :=
      (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗
      (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 4144#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
      ?_ ?_
    · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
      by_cases hcap : (g.priv.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply
        refine DropGlueFacts.align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_clean_lscl hcl2 (mid := (blkPl_2).base + 36#64) (P_mid :=
        vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
        A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗
        ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt)
        ?_ ?_
      · have hstep3 : SepWP ((blkPC_2).rebase (blkPl_2).base H) ((blkPl_2).base + 36#64) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDealloc A ckCap ckPtr) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗
              (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 4144#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                A.pool ∗ stackAt fsp allocHookStack ∗
                (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 4144#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          dsimp only [chainOuterHeadersAt, ckDealloc]
          by_cases hcap : ckCap.slt 1#64 = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps
            refine DropGlueFacts.align_pre (by rw [hsp_2]; ac_rfl) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [stackAt_dropVecMessageKey_split_bottom fsp]
        apply Entails.of_eq; ac_rfl
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        rw [← stackAt_dropVecMessageKey_split_bottom fsp]
        have hstep4 : SepWP ((blkPC_2).rebase (blkPl_2).base H) ((blkPl_2).base + 44#64) s3
            (vecAt A 104 8 (messageKeyAt A) (cur + 48#64) g.mkCap g.mkPtr (g.keys.zip c.messageKeys) ∗
              A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          wp_steps; wp_apply
          refine DropGlueFacts.align_pre (by rw [hsp_3]; ac_rfl) ?_
          wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (chain_memRegions_entails_104 cur)), h.2⟩)

private theorem drop_vec_chain_placed_loop [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec A)))
    (s0 : State) (fsp v ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_2).base + 56#64 →
      s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP ((blkPC_2).rebase (blkPl_2).base H)
        ((blkPl_2).base + 124#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_chain_placed_body hdealloc hdrop_mk s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (chainAt A) 104 cur ((g, c) :: tl) =
          chainAt A (g, c) cur ∗ arrayAt (chainAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_lscl hcl (mid := (blkPl_2).base + 44#64)
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c s
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      wp_steps; wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption) hcl4
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩
          hx19_4 hx20_4
          (by simp only [wp_norm, arm64_norm, add_104_add_48]) rfl) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

theorem drop_vec_chain_placed_ok_of_dealloc_and_mk [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hdrop_mk_raw : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCodeLoaded lsmpl (dropVecMessageKeySpec A))) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainSpec A)) := by
  simp only [withLsCodeLoaded, dropVecChainSpec]
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hloop := drop_vec_chain_placed_loop hdealloc_raw hdrop_mk_raw
  wp_init x s0
  obtain ⟨v, cap, ptr, cs⟩ := x
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChain_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine DropGlueFacts.seq_clean (mid := (blkPl_2).base + 124#64)
    (P_mid :=
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps; wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      apply sepWP_seq_lscl hcl0 (mid := (blkPl_2).base + 56#64)
      wp_steps
      apply SepWP.done
      · wp_norm_lhs
      · wp_norm_lhs
      intro hcl_loop
      have hpre_eq :
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
            (if cap = 0 then emp
             else A.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
          (arrayAt (chainAt A) 104 ptr (hd :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStack ∗
            ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              (if cap = 0 then emp
               else A.live ptr (cap.toNat * 104) 8 ∗
                 memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104)) ((cap.toNat - (hd :: tl).length) * 104)) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
        ac_rfl
      rw [hpre_eq]
      refine SepWP.mono
        (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align (hd :: tl) ptr _ _
          (List.cons_ne_nil _ _) hlen_lt rfl (by assumption) hcl_loop
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl rfl rfl rfl) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      apply Entails.of_eq; ac_rfl
  · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre (post_loop_weaken A (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (DropGlueFacts.cap0_weaken_48_vecChain (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ s0.sp _ _ _ _ _ _) ?_
      wp_done
    · wp_steps
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine SepWP.weaken_pre
        (tail_dealloc_vecChain_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) cap ptr _ _ s0.sp _ _ _ _ _ _) ?_
      wp_apply
      refine SepWP.weaken_pre (DropGlueFacts.vecChain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
      wp_done

theorem drop_vec_chain_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H) (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainSpec A)) := by
  have hmk0 : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H) (lsmpl.base 3)
      (dropVecMessageKeySpec A) :=
    drop_vec_message_key_placed_ok h_dealloc
  have hmk := ls_subroutine_ok_of_block (callerProg := (blkPC_2).rebase (blkPl_2).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hmk0)
  exact drop_vec_chain_placed_ok_of_dealloc_and_mk (ls_hook_ok_rustDealloc h_dealloc) hmk

end CryptoVerification.LibsignalTripleRatchet.Getters
