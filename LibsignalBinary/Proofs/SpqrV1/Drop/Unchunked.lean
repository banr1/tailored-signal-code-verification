/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedRepr
public import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for Unchunked and Protobuf Unchunked States

**Checked by Lean.**

Proves subroutine contracts for:
- `core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]` (`0x35d40`, Block `141`)
- `core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]` (`0x4c99c`, Block `279`)
- `core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>` (`0x4ca24`, Block `280`)
- `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]` (`0x352fc`, Block `133`)
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>` (`0x4ce90`, Block `286`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L15

open Lean Elab Tactic ProofLib

elab "code_fetches_sym " codeId:ident decPrefix:ident b:term:max H:term:max
    sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← CodeLookup.lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offLit $len))

end CryptoVerification.SpqrV1.Layout.L15

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L15

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Specifications -/

/-- Ghost arguments for `drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent>` (`0x35d40` & `0x4c99c`). -/
structure DropUnchunkedCt1SentGhost (F : ShaCompress) where
  a : BitVec 64
  st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)

def dropUnchunkedCt1SentSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (DropUnchunkedCt1SentGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      unchunkedCt1SentAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a unchunkedCt1SentSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

/-- Ghost arguments for `drop_glue::<spqr::v1::unchunked::send_ek::EkSent>` (`0x4ca24`). -/
structure DropUnchunkedEkSentGhost (F : ShaCompress) where
  a : BitVec 64
  st : Unchunked.SendEk.EkSent (spqrAuthApi F)

def dropUnchunkedEkSentSpec (A : RustAlloc) (F : ShaCompress) :
    Spec (DropUnchunkedEkSentGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      unchunkedEkSentAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a unchunkedEkSentSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

/-- Ghost arguments for `drop_glue::<Option<proto::pq_ratchet::v1_state::unchunked::Ct1Sent>>` (`0x352fc`). -/
structure DropOptProtoUnchunkedCt1SentGhost where
  a : BitVec 64
  optSt : Option V1State.Unchunked.Ct1Sent

def dropOptProtoUnchunkedCt1SentSpec (A : RustAlloc) :
    Spec DropOptProtoUnchunkedCt1SentGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      optProtoUnchunkedCt1SentAt A x.a x.optSt ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoUnchunkedCt1SentSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

/-- Ghost arguments for `drop_glue::<proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>` (`0x4ce90`). -/
structure DropProtoUnchunkedCt1SentEkReceivedGhost where
  a : BitVec 64
  st : V1State.Unchunked.Ct1SentEkReceived

def dropProtoUnchunkedCt1SentEkReceivedSpec (A : RustAlloc) :
    Spec DropProtoUnchunkedCt1SentEkReceivedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      protoUnchunkedCt1SentEkReceivedAt A x.a x.st ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a protoUnchunkedCt1SentEkReceivedSize ∗
      A.pool ∗ stackAt s0.sp dropStack32

/-! ## `drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]` (`0x35d40`) -/

local macro "unchunked_ct1_sent_steps " entry:term : tactic => `(tactic| (
  wp_init x s0
  rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropUnchunkedCt1SentGhost.a, DropUnchunkedCt1SentGhost.st] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre (sepConj_mono_left (unchunkedCt1SentAt_entails_dealloc A a st)) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro g
  refine seq_clean (mid := $entry + 36#64)
    (P_mid := (fiveVec128HeadersAt a g ∗
      vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
      vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
      vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 56#64)
      (P_mid := (fiveVec128HeadersAt a g ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 76#64)
        (P_mid := (fiveVec128HeadersAt a g ∗
          vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean (mid := $entry + 96#64)
          (P_mid := (fiveVec128HeadersAt a g ∗
            vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
          (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          dsimp only [fiveVec128HeadersAt, vecCapPtrDealloc]
          by_cases hc5 : (g.v5.cap == 0#64) = true <;>
            simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (fiveVec128HeadersAt_entails_memRegion_128 a g)
              (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
            wp_done
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (sepConj_mono_left (fiveVec128HeadersAt_entails_memRegion_128 a g))
              (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
            wp_apply
            refine SepWP.weaken_pre (tail_dealloc_unchunked_post a 128 A.pool s0.sp) ?_
            wp_done))

theorem drop_unchunked_ct1_sent_local1_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal1Name)
      (dropUnchunkedCt1SentSpec A F) := by
  simp only [dropUnchunkedCt1SentSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal1Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]" 136
  dsimp only [dropProgAtExt, dropUnchunkedCt1SentLocal1Name, unchunkedCt1SentSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#1]" = entry
  examples_hide_fetches
  unchunked_ct1_sent_steps entry

theorem drop_unchunked_ct1_sent_local1_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_141).rebase (blkPl_141).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_141).rebase (blkPl_141).base H) (blkPl_141).base
      (dropUnchunkedCt1SentSpec A F) := by
  simp only [dropUnchunkedCt1SentSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [unchunkedCt1SentSize] at *
  unchunked_ct1_sent_steps (blkPl_141).base

/-! ## `drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]` (`0x4c99c`) -/

theorem drop_unchunked_ct1_sent_local2_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal2Name)
      (dropUnchunkedCt1SentSpec A F) := by
  simp only [dropUnchunkedCt1SentSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedCt1SentLocal2Name +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" 136
  dsimp only [dropProgAtExt, dropUnchunkedCt1SentLocal2Name, unchunkedCt1SentSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]" = entry
  examples_hide_fetches
  unchunked_ct1_sent_steps entry

theorem drop_unchunked_ct1_sent_local2_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_279).rebase (blkPl_279).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_279).rebase (blkPl_279).base H) (blkPl_279).base
      (dropUnchunkedCt1SentSpec A F) := by
  simp only [dropUnchunkedCt1SentSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [unchunkedCt1SentSize] at *
  unchunked_ct1_sent_steps (blkPl_279).base

/-! ## `drop_glue::<spqr::v1::unchunked::send_ek::EkSent>` (`0x4ca24`) -/

local macro "unchunked_ek_sent_steps " entry:term : tactic => `(tactic| (
  wp_init x s0
  rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropUnchunkedEkSentGhost.a, DropUnchunkedEkSentGhost.st] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre (sepConj_mono_left (unchunkedEkSentAt_entails_dealloc A a st)) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro g
  refine seq_clean (mid := $entry + 36#64)
    (P_mid := (threeVec80HeadersAt a g ∗
      vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [threeVec80HeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 56#64)
      (P_mid := (threeVec80HeadersAt a g ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [threeVec80HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [threeVec80HeadersAt, vecCapPtrDealloc]
      by_cases hc3 : (g.v3.cap == 0#64) = true <;>
        simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono
          (threeVec80HeadersAt_entails_memRegion_80 a g)
          (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
        wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono
          (sepConj_mono_left (threeVec80HeadersAt_entails_memRegion_80 a g))
          (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
        wp_apply
        refine SepWP.weaken_pre (tail_dealloc_unchunked_post a 80 A.pool s0.sp) ?_
        wp_done))

theorem drop_unchunked_ek_sent_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedEkSentName)
      (dropUnchunkedEkSentSpec A F) := by
  simp only [dropUnchunkedEkSentSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropUnchunkedEkSentName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" 96
  dsimp only [dropProgAtExt, dropUnchunkedEkSentName, unchunkedEkSentSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::v1::unchunked::send_ek::EkSent>" = entry
  examples_hide_fetches
  unchunked_ek_sent_steps entry

theorem drop_unchunked_ek_sent_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_280).rebase (blkPl_280).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_280).rebase (blkPl_280).base H) (blkPl_280).base
      (dropUnchunkedEkSentSpec A F) := by
  simp only [dropUnchunkedEkSentSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [unchunkedEkSentSize] at *
  unchunked_ek_sent_steps (blkPl_280).base

/-! ## `drop_glue::<proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>` (`0x4ce90`) -/

def auth72HeadersAt (a : BitVec 64) (ga : TwoVecGhost) : SepProp :=
  ((a + 72#64) ↦₆₄ ga.v1.cap) ∗ ((a + 80#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 88#64) 8 ∗
  ((a + 96#64) ↦₆₄ ga.v2.cap) ∗ ((a + 104#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 112#64) 8

theorem twoVecHeadersAt_72_eq (a : BitVec 64) (ga : TwoVecGhost) :
    twoVecHeadersAt (a + 72#64) ga = auth72HeadersAt a ga := by
  unfold twoVecHeadersAt auth72HeadersAt
  have h1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have h2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  have h3 : (a + 72#64) + 24#64 = a + 96#64 := by bv_omega
  have h4 : (a + 72#64) + 32#64 = a + 104#64 := by bv_omega
  have h5 : (a + 72#64) + 40#64 = a + 112#64 := by bv_omega
  rw [h1, h2, h3, h4, h5]

theorem auth72HeadersAt_entails_memRegion_48 (a : BitVec 64) (ga : TwoVecGhost) :
    auth72HeadersAt a ga ⊢ memRegion (a + 72#64) 48 := by
  rw [← twoVecHeadersAt_72_eq]
  exact twoVecHeadersAt_entails_memRegion_48 (a + 72#64) ga

theorem optProtoAuthenticatorAt_72_none (A : RustAlloc) (a : BitVec 64) :
    optProtoAuthenticatorAt A (a + 72#64) none =
      ((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40 := by
  have h1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  rw [optProtoAuthenticatorAt_none, h1]

theorem optProtoAuthenticatorAt_72_none_entails_memRegion_48 (A : RustAlloc) (a : BitVec 64) :
    ((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40 ⊢ memRegion (a + 72#64) 48 := by
  have h1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  rw [← h1]
  exact optProtoAuthenticatorAt_none_entails_memRegion_48 A (a + 72#64)

private theorem protoUnchunked3Vec_auth_some_entails (A : RustAlloc) (a : BitVec 64)
    (g : ThreeVecGhost) (auth : ProtoAuthenticator) (Rest : SepProp) :
    protoUnchunked3VecHeadersAt a g ∗
      protoAuthenticatorAt A (a + 72#64) auth ∗
      memRegion (a + 120#64) 8 ∗
      vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
      vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ Rest ⊢
    ∃∗ ga : TwoVecGhost,
      ⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗
      ((protoUnchunked3VecHeadersAt a g ∗
        (auth72HeadersAt a ga ∗
          vecCapPtrDealloc A ga.v1.cap ga.v1.ptr ∗
          vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
        memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ Rest) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (protoAuthenticatorAt_entails_dealloc A (a + 72#64) auth))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ga
  refine Entails.sepExists_right ga ?_
  rw [twoVecHeadersAt_72_eq]
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗
      ((protoUnchunked3VecHeadersAt a g ∗
        (auth72HeadersAt a ga ∗
          vecCapPtrDealloc A ga.v1.cap ga.v1.ptr ∗
          vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
        memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ Rest) by ac_rfl))
    (Entails.refl _)

local macro "proto_unchunked_ct1_sent_ek_received_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  wp_init x s0
  rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropProtoUnchunkedCt1SentEkReceivedGhost.a,
    DropProtoUnchunkedCt1SentEkReceivedGhost.st] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_left (protoUnchunkedCt1SentEkReceivedAt_entails_dealloc A a st)) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_left; intro g
  wp_focus_pure; intro _
  refine seq_clean (mid := $entry + 64#64)
    (P_mid := (protoUnchunked3VecHeadersAt a g ∗
      memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
      vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
      vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · cases hauth : st.auth with
    | none =>
      rw [optProtoAuthenticatorAt_72_none]
      have hstep : SepWP $prog ($entry + 64#64) s0
          ((protoUnchunked3VecHeadersAt a g ∗
            (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
            memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
            vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((s0.sp - 32#64) ↦₆₄ fp_old) ∗ ((s0.sp - 24#64) ↦₆₄ lr_old) ∗
            ((s0.sp - 16#64) ↦₆₄ x19_old) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))
          (fun sm Pm =>
            (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
              (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
              memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
            Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) := by
        wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]) ?_; wp_done
      exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (SepWP.strengthen_entails_const
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
            (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A a))))
          hstep)
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre
        (protoUnchunked3Vec_auth_some_entails A a g auth _) ?_
      apply SepWP.exists_left; intro ga
      wp_focus_pure; intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine seq_clean (mid := $entry + 44#64)
        (P_mid := (protoUnchunked3VecHeadersAt a g ∗
          (auth72HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
          memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [auth72HeadersAt, vecCapPtrDealloc]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
      · intro sa1 hpca1 hruna1 ⟨⟨hx20_a1, hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1⟩
        have hstepa2 : SepWP $prog ($entry + 64#64) sa1
            ((protoUnchunked3VecHeadersAt a g ∗
              (auth72HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
            (fun sm Pm =>
              (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
                auth72HeadersAt a ga ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
                A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old))) ∧
              Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) := by
          dsimp only [auth72HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
            (auth72HeadersAt_entails_memRegion_48 a ga))))
          hstepa2
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := $entry + 84#64)
      (P_mid := (protoUnchunked3VecHeadersAt a g ∗
        memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean (mid := $entry + 104#64)
        (P_mid := (protoUnchunked3VecHeadersAt a g ∗
          memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)))
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre (sepConj_mono
            (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)
            (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
          wp_done
        · wp_steps
          refine SepWP.weaken_pre (sepConj_mono
            (Entails.trans
              (Entails.of_eq (show _ =
                (protoUnchunked3VecHeadersAt a g ∗ memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8) ∗
                (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) by
                  unfold protoUnchunked3VecHeadersAt; ac_rfl))
              (sepConj_mono_left (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)))
            (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
          wp_apply
          refine SepWP.weaken_pre (tail_dealloc_unchunked_post a 128 A.pool s0.sp) ?_
          wp_done))

theorem drop_proto_unchunked_ct1_sent_ek_received_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A) := by
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoUnchunkedCt1SentEkReceivedName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" 144
  dsimp only [dropProgAtExt, dropProtoUnchunkedCt1SentEkReceivedName,
    protoUnchunkedCt1SentEkReceivedSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>" = entry
  examples_hide_fetches
  proto_unchunked_ct1_sent_ek_received_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

theorem drop_proto_unchunked_ct1_sent_ek_received_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_286).rebase (blkPl_286).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_286).rebase (blkPl_286).base H) (blkPl_286).base
      (dropProtoUnchunkedCt1SentEkReceivedSpec A) := by
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [protoUnchunkedCt1SentEkReceivedSize] at *
  proto_unchunked_ct1_sent_ek_received_steps ((blkPC_286).rebase (blkPl_286).base H) (blkPl_286).base

/-! ## `drop_glue::<Option<proto::pq_ratchet::v1_state::unchunked::Ct1Sent>>` (`0x352fc`) -/

local macro "opt_proto_unchunked_ct1_sent_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  wp_init x s0
  rcases x with ⟨a, optSt⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropOptProtoUnchunkedCt1SentGhost.a,
    DropOptProtoUnchunkedCt1SentGhost.optSt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x20_old x19_old
  cases optSt with
  | none =>
    rw [optProtoUnchunkedCt1SentAt_none]
    wp_steps
    refine SepWP.weaken_pre (sepConj_mono
      (optProtoUnchunkedCt1SentAt_none_entails_memRegion_128 A a)
      (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
    wp_done
  | some st =>
    rw [optProtoUnchunkedCt1SentAt_some]
    refine SepWP.weaken_pre
      (sepConj_mono_left (protoUnchunkedCt1SentAt_entails_dealloc A a st)) ?_
    rw [sepExists_sepConj_left]
    apply SepWP.exists_left; intro g
    wp_focus_pure; intro hcap1_lt
    have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
    refine seq_clean (mid := $entry + 76#64)
      (P_mid := (protoUnchunked3VecHeadersAt a g ∗
        memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
      ?_ ?_
    · cases hauth : st.auth with
      | none =>
        rw [optProtoAuthenticatorAt_72_none]
        have hstep : SepWP $prog ($entry + 76#64) s0
            ((protoUnchunked3VecHeadersAt a g ∗
              (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
              memRegion (a + 120#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
              ((s0.sp - 32#64) ↦₆₄ fp_old) ∗ ((s0.sp - 24#64) ↦₆₄ lr_old) ∗
              ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old))
            (fun sm Pm =>
              (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
                (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
                A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) := by
          dsimp only [protoUnchunked3VecHeadersAt]
          wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x20, Reg.x19]) ?_; wp_done
        exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A a))))
            hstep)
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.weaken_pre
          (protoUnchunked3Vec_auth_some_entails A a g auth _) ?_
        apply SepWP.exists_left; intro ga
        wp_focus_pure; intro hga_lt
        have hne_none := cap_add_one_beq_zero_false hga_lt
        refine seq_clean (mid := $entry + 56#64)
          (P_mid := (protoUnchunked3VecHeadersAt a g ∗
            (auth72HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
            memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
            vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, auth72HeadersAt, vecCapPtrDealloc]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
        · intro sa1 hpca1 hruna1 ⟨⟨hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
          have hstepa2 : SepWP $prog ($entry + 76#64) sa1
              ((protoUnchunked3VecHeadersAt a g ∗
                (auth72HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
                memRegion (a + 120#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
                vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
                A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (fun sm Pm =>
                (Pm ⊢ (protoUnchunked3VecHeadersAt a g ∗
                  auth72HeadersAt a ga ∗
                  memRegion (a + 120#64) 8 ∗
                  vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                  vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
                  vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
                  A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
                  (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
                sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) := by
            dsimp only [auth72HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
          exact SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (auth72HeadersAt_entails_memRegion_48 a ga))))
            hstepa2
    · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
      refine seq_clean (mid := $entry + 96#64)
        (P_mid := (protoUnchunked3VecHeadersAt a g ∗
          memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
        ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc1 : (g.v1.cap == 0#64) = true <;>
          simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine seq_clean (mid := $entry + 116#64)
          (P_mid := (protoUnchunked3VecHeadersAt a g ∗
            memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ∗
            vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
          dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)
              (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
            wp_done
          · wp_steps
            refine SepWP.weaken_pre (sepConj_mono
              (Entails.trans
                (Entails.of_eq (show _ =
                  (protoUnchunked3VecHeadersAt a g ∗ memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8) ∗
                  (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) by
                    unfold protoUnchunked3VecHeadersAt; ac_rfl))
                (sepConj_mono_left (protoUnchunked3VecHeadersAt_entails_memRegion_128 a g)))
              (sepConj_mono_right (cells4_entails_stack32_bottom s0.sp _ _ _ _))) ?_
            wp_apply
            refine SepWP.weaken_pre (tail_dealloc_unchunked_post a 128 A.pool s0.sp) ?_
            wp_done))

theorem drop_opt_proto_unchunked_ct1_sent_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoUnchunkedCt1SentName)
      (dropOptProtoUnchunkedCt1SentSpec A) := by
  simp only [dropOptProtoUnchunkedCt1SentSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoUnchunkedCt1SentName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]" 156
  dsimp only [dropProgAtExt, dropOptProtoUnchunkedCt1SentName,
    protoUnchunkedCt1SentSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]" = entry
  examples_hide_fetches
  opt_proto_unchunked_ct1_sent_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

theorem drop_opt_proto_unchunked_ct1_sent_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_133).rebase (blkPl_133).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_133).rebase (blkPl_133).base H) (blkPl_133).base
      (dropOptProtoUnchunkedCt1SentSpec A) := by
  simp only [dropOptProtoUnchunkedCt1SentSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [protoUnchunkedCt1SentSize] at *
  opt_proto_unchunked_ct1_sent_steps ((blkPC_133).rebase (blkPl_133).base H) (blkPl_133).base

end CryptoVerification.SpqrV1.Drop
