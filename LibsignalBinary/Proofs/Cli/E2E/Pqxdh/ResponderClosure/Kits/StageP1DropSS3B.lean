/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `drop_session_structure3` Verification — Part B

Completes the receiver-chain teardown loop, tail deallocations, and `subroutine_ok` proof for
`core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#5]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.DropSS3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSession

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 2000000 in
theorem drop_ss2_receiver_loop {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A))
    (s0 : State) (fsp ss ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cur →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 132#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          sm.readReg64 .x20 = ptr) := by
  simp only [dropChainSpec] at hdrop_chain
  have hfn : libsignalSessionCode.fnOff dropSessionStructure3Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 112 20
  examples_generalize_entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    rw [show arrayAt (chainAt A) 104 cur ((g, c) :: tl) =
          chainAt A (g, c) cur ∗ arrayAt (chainAt A) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean (mid := entry + 120#64)
      (P_mid := memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = cur ∧ sm.readReg64 .x22 = BitVec.ofNat 64 ((g, c) :: tl).length)
      ?_ ?_
    · wp_steps
      wp_call hdrop_chain ⟨cur, (g, c)⟩
      refine align_pre (by rw [hsp]) ?_
      wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩,
      hx19_1, hx20_1, hx21_1, hx22_1⟩
      cases tl with
      | nil =>
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
          arrayAt, emp_sepConj] at hx22_1 ⊢
        wp_steps
        wp_done
      | cons hd2 tl2 =>
        have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
        have htl_len := tail_len_mul_lt hlen
        rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
            ofNat_succ_eq_add_one] at hx22_1
        have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        wp_steps
        have hpc_next : (BitVec.ofNat 64 (hd2 :: tl2).length + 1#64 != 1#64) = true := by
          rw [bne_iff_ne]
          intro h
          exact hne1 (beq_iff_eq.mpr h)
        rw [sep_push_body]
        refine SepWP.mono
          (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
            htl_ne htl_len (by simp only [State.setPC, hpc_next, ↓reduceIte]) (by assumption)
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
            hx19_1 hx20_1 rfl rfl) ?_
        intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
        have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit,
          ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
        exact Entails.refl _

set_option maxHeartbeats 2000000 in
theorem drop_ss2_tail3 {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 160#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + 228#64)
        s
        ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗
            memRegion (ss + 96#64) 24) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructure3Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 160 68
  examples_generalize_entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_clean (mid := entry + 184#64) (P_mid :=
    (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A kCap kPtr ∗
      vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_call hdealloc (pPtr, pCap.toNat, 1)
      refine align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := entry + 208#64) (P_mid :=
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_call hdealloc (kPtr, kCap.toNat, 1)
        refine align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
        (tripleRatchetExterns C ctl abs))) (entry + 228#64) s2
          ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗ A.pool ∗ stackAt fsp allocHookStack ∗
              Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt, vecPinDealloc]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (G.alice.ptr, G.alice.cap.toNat, 1)
          refine align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left
          (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

set_option maxHeartbeats 2000000 in
/-- `subroutine_ok` proof for
`core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#5]`. -/
theorem drop_session_structure3_ok_std3 {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A) := by
  have hdc := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain2_ok (b := b) (C := C) (ctl := ctl) hA
  simp only [dropSessionStructureLocal2Spec]
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  have hdealloc_raw := dealloc_ok_at (b := b) (C := C) (ctl := ctl)
    hA hfn (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) (by decide)
  have hdrop_chain_raw : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss2_add]
    exact hdc
  have hdrop_proto_chain_raw : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss2_add]
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_proto_chain2_ok hA
  clear hdc
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 0 16
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 100 12
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 132 28
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 228 48
  clear hfn
  wp_init x s0
  have hdealloc := hdealloc_raw
  have hfirst3 := drop_ss2_first3 (b := b) (C := C) (ctl := ctl) hdealloc_raw
  have hsender := drop_ss2_sender (b := b) (C := C) (ctl := ctl) hdrop_proto_chain_raw
  have hloop := drop_ss2_receiver_loop (b := b) (C := C) (ctl := ctl) hdrop_chain_raw
  have htail3 := drop_ss2_tail3 (b := b) (C := C) (ctl := ctl) hdealloc_raw
  clear hdealloc_raw hdrop_chain_raw hdrop_proto_chain_raw
  dsimp only [tripleRatchetProgAt, dropSessionStructure3Name] at hfirst3 hsender hloop htail3 hdealloc
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st⟩ := x
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  rw [stackAt_ss2_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3 v4 v5
  refine drop6_strengthen_post (session_memRegions_entails_344 (s0.readReg64 (Reg.gpr 0#5))) ?_
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc A (s0.readReg64 (Reg.gpr 0#5)) G st)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine seq_clean (mid := entry + 16#64)
    (P_mid :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A pCap pPtr ∗
          sgnPinDealloc A kCap kPtr ∗
          vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 4192#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
    have hsp_sub : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine align_pre
      (by dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt, Reg.x19, Reg.x20,
            Reg.x21, Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine seq_clean (mid := entry + 80#64)
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain ∗
        A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
        (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
      have hsp_sub1 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
      rw [hsp_sub1]
      exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2⟩
      refine seq_clean (mid := entry + 100#64)
        (P_mid :=
          vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip st.receiverChains) ∗
          (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
          A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 48#64) (s0.readReg64
            (Reg.gpr 0#5)) hfsp_align G.sender st.senderChain s2 _
            hpc2 hrun2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩,
        hx19_3⟩
        refine SepWP.weaken_pre
          (sepConj_mono_left (vecAt_expose_loop_at_72 A 104 8 (chainAt A)
            (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
              (G.chains.zip st.receiverChains))) ?_
        rw [sepConj_assoc]
        refine SepWP.pure_elim ?_
        rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
        generalize G.chains.zip st.receiverChains = cs at hlen_le hlen_lt ⊢
        refine seq_clean (mid := entry + 132#64)
          (P_mid :=
            ((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            memRegion G.chainsPtr (cs.length * 104) ∗
            (if G.chainsCap = 0 then emp
             else A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
               memRegion (G.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((G.chainsCap.toNat - cs.length) * 104)) ∗
            (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
            A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          (Q := fun sm =>
            Saved48Preserved s0 sm (s0.sp - 48#64) ∧
            sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧
            sm.readReg64 .x20 = G.chainsPtr)
          ?_ ?_
        · cases cs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
            wp_steps
            refine align_pre (by dsimp only [ssTail3HeadersAt]; ac_rfl) ?_
            wp_done
          | cons hd tl =>
            have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
            wp_steps
            refine SepWP.weaken_pre (P' :=
              arrayAt (chainAt A) 104 G.chainsPtr (hd :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
              (((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if G.chainsCap = 0 then emp
                 else A.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
                   memRegion (G.chainsPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                     ((G.chainsCap.toNat - (hd :: tl).length) * 104)) ∗
                (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (Entails.of_eq (by dsimp only [ssTail3HeadersAt]; ac_rfl)) ?_
            refine SepWP.mono
              (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) G.chainsPtr hfsp_align
                (hd :: tl) G.chainsPtr _ _
                (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
                ⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
                hx19_3 rfl rfl rfl) ?_
            intro sm Pm _ _ h
            exact ⟨Entails.trans h.1 (Entails.of_eq (by dsimp only [ssTail3HeadersAt]; ac_rfl)),
              h.2⟩
        · intro sm hpcm hrunm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
          refine SepWP.weaken_pre
            (post_loop_weaken_at_72 A (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
              cs.length hlen_le hcap_lt _) ?_
          refine seq_clean (mid := entry + 160#64)
            (P_mid :=
              (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
                sgnPinDealloc A pCap pPtr ∗
                sgnPinDealloc A kCap kPtr ∗
                vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
              memRegion (s0.sp - 4192#64) 48 ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm =>
              Saved48Preserved s0 sm (s0.sp - 48#64) ∧
              sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
            have hsp_subm : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
            rw [hsp_subm]
            by_cases hcap : (G.chainsCap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, emp_sepConj]
            · wp_steps
              refine SepWP.weaken_pre
                (chains_header24_weaken (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _) ?_
              refine align_pre (by dsimp only [ssTail3HeadersAt]; ac_rfl) ?_
              wp_done
            · wp_steps
              have hmul : 104#64 * G.chainsCap = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by
                bv_omega
              have hmul2 : G.chainsCap * 104#64 = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by
                bv_omega
              wp_call hdealloc (G.chainsPtr, G.chainsCap.toNat * 104, 8)
              refine SepWP.weaken_pre
                (sepConj_mono_right (sepConj_mono_right
                  (chains_header24_weaken (s0.readReg64
                    (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _))) ?_
              refine align_pre (by rw [hsp_m]; dsimp only [ssTail3HeadersAt]; ac_rfl) ?_
              wp_done
          · intro s4 hpc4 hrun4 ⟨hpres4, hx19_4⟩
            refine seq_clean (mid := entry + 228#64)
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
                A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
              (Q := fun sm =>
                Saved48Preserved s0 sm (s0.sp - 48#64) ∧
                sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
              ?_ ?_
            · refine SepWP.mono
                (htail3 s0 (s0.sp - 48#64) (s0.readReg64
                  (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G s4 _
                  hpc4 hrun4 hpres4 hx19_4) ?_
              intro sm Pm _ _ h
              refine ⟨Entails.trans h.1 ?_, h.2⟩
              rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
              have hsp_sub4 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
              rw [hsp_sub4]
              exact Entails.of_eq (by ac_rfl)
            · intro s5 hpc5 hrun5 ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5,
              htrace_5, hvregs_5⟩, hx19_5⟩
              dsimp only [vecPinDealloc]
              by_cases hcap : (G.pq.cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte]
              · wp_steps
                refine SepWP.weaken_pre (pq_header24_weaken (s0.readReg64
                  (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
                wp_done
              · wp_steps
                refine SepWP.weaken_pre
                  (tail_dealloc_ss2_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                    _ _ _ s0.sp _ _ _ _ _ _) ?_
                wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
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
                  (stackAt (s0.sp - 48#64) dropChainStack ∗ cells (s0.sp - 48#64) 6))
                  (by
                    rw [← tail_stack_ss2_96_from_bottom s0.sp]
                    exact Entails.of_eq (by ac_rfl)) ?_
                cells_unfold
                wp_pull_exists
                wp_done

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.DropSS3
