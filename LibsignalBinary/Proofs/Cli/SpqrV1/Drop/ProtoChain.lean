/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.Decodes
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# CLI SPQR V1 `proto::pq_ratchet::Chain` Drop Glue (`[local#2]`)

Proves `drop_proto_spqr_chain_ok_ext` (`dropProtoSpqrChainSpec A`) for
`core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]` on `tripleRatchetProgAtExt`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L13

end CryptoVerification.SpqrV1.Layout.L13

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L13

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp]
private theorem optEpochDirectionPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optEpochDirectionPBAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48) := rfl

@[local simp]
private theorem optEpochDirectionPBAt_some (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

private theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_body {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp a lPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB)
      (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a →
      s.readReg64 .x20 = lPtr →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 56#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName + 36#64)
        s
        (chainEpochPBAt A cur ep ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_len libsignalSessionCode spqrDropChainEpochBinCli b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" 224
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" = entry
  examples_hide_fetches
  intro cur cnt ep s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  unfold chainEpochPBAt
  refine seq_clean (mid := entry + 96#64) (P_mid :=
    (memRegion cur 56 ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64)
    ?_ ?_
  · cases hsend : ep.send with
    | none =>
      rw [optEpochDirectionPBAt_none]
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 96#64) s
          (((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
            optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗
              optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
            sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (sepConj_mono_left (optEpochDirectionPBAt_none_entails_memRegion_56 A cur)))
        hstep
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_left (epochDirectionPBAt_entails_dealloc A cur d))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]
      apply SepWP.exists_left; intro gs
      wp_focus_pure; intro hcap_lt_s
      have hne_none_s := cap_add_one_beq_zero_false hcap_lt_s
      refine seq_clean (mid := entry + 76#64) (P_mid :=
        ((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
          optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64)
        ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gs.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
        have hstep2 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 96#64) s1
            (((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
              optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (epochDirPBHeadersAt cur gs ∗
                optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gs.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (sepConj_mono_left (epochDirPBHeadersAt_entails_memRegion_56 cur gs)))
          hstep2
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
    cases hrecv : ep.recv with
    | none =>
      rw [optEpochDirectionPBAt_none]
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 36#64) s2
          ((memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
            sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (Entails.trans
          (sepConj_mono_right (optEpochDirectionPBAt_none_entails_memRegion_56 A (cur + 56#64)))
          (chainEpochPB_regions_entails_112 cur)))
        hstep
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (epochDirectionPBAt_entails_dealloc A (cur + 56#64) d))) ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_left]
      apply SepWP.exists_left; intro gr
      wp_focus_pure; intro hcap_lt_r
      have hne_none_r := cap_add_one_beq_zero_false hcap_lt_r
      refine seq_clean (mid := entry + 124#64) (P_mid :=
        (memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64)
        ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gr.next.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 36#64) s3
            ((memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (memRegion cur 56 ∗ epochDirPBHeadersAt (cur + 56#64) gr) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gr.prev.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (Entails.trans
            (sepConj_mono_right (epochDirPBHeadersAt_entails_memRegion_56 (cur + 56#64) gr))
            (chainEpochPB_regions_entails_112 cur)))
          hstep4

private theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_loop {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp a lPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a →
      s.readReg64 .x20 = lPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 56#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName + 148#64)
        s
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 cur rest ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = lPtr) := by
  have hbody := CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_body (b := b) (ext := ext)
    hdealloc s0 fsp a lPtr hfsp_align
  dsimp only [dropProgAtExt, CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_len libsignalSessionCode spqrDropChainEpochBinCli b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" 224
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]
    rw [sep_pull_body]
    refine seq_clean (mid := entry + 36#64)
      (P_mid := memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 (cur + 112#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (ep :: tl).length ∧
        sm.readReg64 .x22 = cur + 56#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep s _ hpc hrun hpres hx19 hx20 hx21 hx22)
      ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨ep2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps
      wp_done
    · have hlen_tl : (ep2 :: tl2).length * 112 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := entry + 48#64)
        (P_mid := arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 (cur + 112#64) (ep2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 112 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (ep2 :: tl2).length ∧
          sm.readReg64 .x22 = (cur + 112#64) + 56#64)
        ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]
        wp_steps
        rw [add_112_add_56]
        wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 112#64) s2 (memRegion cur 112 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul ep (ep2 :: tl2) 112
        have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
        exact Entails.refl _

theorem _root_.CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A) := by
  simp only [dropProtoSpqrChainSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" "__rustc::__rust_dealloc")
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hloop := CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_loop (b := b) (ext := ext) hdealloc_raw
  code_fetches_len libsignalSessionCode spqrDropChainEpochBinCli b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" 224
  dsimp only [dropProgAtExt, CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName, chainPBSize, BitVec.ofNat_eq_ofNat] at hloop hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]" = entry
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨a, ch⟩
  dsimp only [DropProtoSpqrChainGhost.a, DropProtoSpqrChainGhost.ch] at *
  refine SepWP.weaken_pre (sepConj_mono_left (chainPBAt_entails_dealloc A a ch)) ?_
  wp_pull_exists
  rename_i g
  nth_rw 1 [stackAt_dropStack48_split s0.sp]
  cells_unfold
  wp_pull_exists
  wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  refine seq_clean (mid := entry + 148#64)
    (P_mid :=
      (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
      (if g.links.cap = 0 then emp
       else A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
         memRegion g.links.ptr (g.links.cap.toNat * 112)) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      memRegion (a + 40#64) 40 ∗
      vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.links.ptr)
    ?_ ?_
  · generalize hxs : ch.links = xs at hlen_le ⊢
    cases xs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj]
      wp_steps
      refine align_pre (by ac_rfl) ?_
      wp_done
    | cons ep tl =>
      have hlen_pos : 0 < (ep :: tl).length := by simp
      have hlen_lt : (ep :: tl).length * 112 < 2 ^ 63 := by
        have : (ep :: tl).length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
        omega
      have hne0 := ofNat_beq_zero_false_112 hlen_pos hlen_lt
      have hcap_ne : g.links.cap ≠ 0 := by
        intro hc0; rw [hc0] at hlen_le; simp at hlen_le
      simp only [hcap_ne, ↓reduceIte]
      refine seq_clean (mid := entry + 48#64)
        (P_mid :=
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr (ep :: tl) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (ep :: tl).length) ∗
           A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
           memRegion (g.links.ptr + BitVec.ofNat 64 ((ep :: tl).length * 112))
             ((g.links.cap.toNat - (ep :: tl).length) * 112) ∗
           ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
           memRegion (a + 40#64) 40 ∗
           vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.links.ptr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (ep :: tl).length ∧
          sm.readReg64 .x22 = g.links.ptr + 56#64)
        ?_ ?_
      · wp_steps
        refine align_pre (by ac_rfl) ?_
        wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop s0 (s0.sp - 48#64) a g.links.ptr hfsp_align (ep :: tl) g.links.ptr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx19_loop hx20_loop hx21_loop hx22_loop)
        have hsplit : g.links.cap.toNat * 112 =
            (ep :: tl).length * 112 + (g.links.cap.toNat - (ep :: tl).length) * 112 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (ep :: tl).length * 112 + (g.links.cap.toNat - (ep :: tl).length) * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        conv_rhs =>
          arg 2; arg 2; arg 2; arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.links.ptr ((ep :: tl).length * 112)
                ((g.links.cap.toNat - (ep :: tl).length) * 112) hbound]
        exact Entails.of_eq (by ac_rfl)
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
    refine seq_clean (mid := entry + 176#64)
      (P_mid :=
        (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗
        vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
        A.pool ∗
        stackAt (s0.sp - 48#64) allocHookStack ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc : g.links.cap = 0
      · have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        wp_done
      · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        simp only [hc, ↓reduceIte]
        wp_steps
        wp_call hdealloc_raw (g.links.ptr, g.links.cap.toNat * 112, 8)
        refine align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [vecCapPtrDealloc]
      by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr)
          (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr)
          (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        rw [stackAt_dropStack48_split_bottom s0.sp]
        wp_call hdealloc_raw (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1)
        rw [← stackAt_dropStack48_split_bottom s0.sp]
        wp_done

end CryptoVerification.SpqrV1.Drop
