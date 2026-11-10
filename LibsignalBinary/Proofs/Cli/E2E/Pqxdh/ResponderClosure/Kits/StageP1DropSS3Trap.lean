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
# `drop_session_structure3` over `trTrapProgAt`

Proves `subroutine_ok` over `trTrapProgAt b C abs` for `SessionStructure` drop glue, reusing the
separation-logic decomposition from `StageP1DropSS3A`.
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

theorem dealloc_hookSat_trTrapExterns {A : RustAlloc} (C : Crypto)
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    HookSat (Rust.withPanics (trTrapExterns C abs)) "__rustc::__rust_dealloc"
      (rustDeallocSpec A) := by
  have heq : Rust.withPanics (trTrapExterns C abs) "__rustc::__rust_dealloc" =
      Rust.withPanics (tripleRatchetExterns C 0#64 abs) "__rustc::__rust_dealloc" :=
    withPanics_trTrap_ne C abs (by unfold rngFillName; decide)
  unfold HookSat
  rw [heq]
  exact dealloc_hookSat_tripleRatchetExterns C 0#64 hA

theorem dealloc_ok_at_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_dealloc")) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_dealloc")
    (dealloc_hookSat_trTrapExterns C hA)

theorem fnAddr_dropChain_eq_ss2_add_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name =
      (trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64) := by
  unfold trTrapProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  bv_omega

set_option maxHeartbeats 1200000 in
theorem drop_ss2_first3_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 80#64)
        s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A G.root) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructure3Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 16 64
  examples_generalize_entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine seq_clean (mid := entry + 40#64) (P_mid :=
    (ssFirst3HeadersAt ss G ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1)
      refine align_pre (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean (mid := entry + 60#64) (P_mid :=
      (ssFirst3HeadersAt ss G ∗ vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1)
        refine align_pre (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
        (trTrapExterns C abs))) (entry + 80#64) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDealloc A G.root) ∗ A.pool ∗
            stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1)
          refine align_pre (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

set_option maxHeartbeats 1200000 in
theorem drop_ss2_sender_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 80#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 100#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [dropProtoChainSpec] at hdrop_chain
  have hfn : libsignalSessionCode.fnOff dropSessionStructure3Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 80 20
  examples_generalize_entry
  examples_hide_fetches
  intro senderG senderSt s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      unfold optSenderChainAt
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics
        (trTrapExterns C abs))) (entry + 100#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
            A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
              A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wp_steps
        wp_done
      exact SepWP.mono hstep (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (sender_none_entails_memRegion_104 (ss + 144#64))),
          h.2⟩)
    | some _ =>
      simp only [optSenderChainAt]
      exact false_elim_left
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_expose A
        (ss + 144#64) sg sc)) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hpk, hlen, hcap_lt, hptr_ne, hcmn⟩
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      wp_steps
      refine SepWP.weaken_pre
        (sepConj_mono_left (chainAt_of_exposed_sender A
          (ss + 144#64) sg sc hpk hlen hcap_lt hptr_ne)) ?_
      wp_call hdrop_chain ⟨ss + 144#64, (⟨sg.srk, sg.priv, sg.mkCap, sg.mkPtr, [], sg.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩)⟩
      refine align_pre (by rw [hsp]) ?_
      wp_done

set_option maxHeartbeats 1200000 in
theorem drop_ss2_receiver_loop_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A))
    (s0 : State) (fsp ss ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cur →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 132#64)
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
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 112 20
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

set_option maxHeartbeats 1200000 in
theorem drop_ss2_tail3_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 160#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 228#64)
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
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, dropSessionStructure3Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 160 68
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
        (trTrapExterns C abs))) (entry + 228#64) s2
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

set_option maxHeartbeats 1200000 in
theorem drop_ss2_receivers_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A))
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (chainsCap chainsPtr : BitVec 64) (cs : List (ChainGhost × ReceiverChain))
      (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 100#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + 160#64)
        s
        (vecAt A 104 8 (chainAt A) (ss + 72#64) chainsCap chainsPtr cs ∗
          A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 72#64) 24 ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  have hloop := drop_ss2_receiver_loop_trap (b := b) (C := C) (abs := abs) hdrop_chain
  clear hdrop_chain
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructure3Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, dropSessionStructure3Name] at hloop hdealloc ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 100 12
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 132 28
  examples_generalize_entry
  examples_hide_fetches
  intro chainsCap chainsPtr cs s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop_at_72 A 104 8 (chainAt A) ss chainsCap chainsPtr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  refine seq_clean (mid := entry + 132#64)
    (P_mid :=
      ((ss + 72#64) ↦₆₄ chainsCap) ∗
      ((ss + 80#64) ↦₆₄ chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion chainsPtr (cs.length * 104) ∗
      (if chainsCap = 0 then emp
       else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
         memRegion (chainsPtr + BitVec.ofNat 64 (cs.length * 104))
           ((chainsCap.toNat - cs.length) * 104)) ∗
      A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
    (Q := fun sm =>
      Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ss ∧
      sm.readReg64 .x20 = chainsPtr)
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps
      refine align_pre (by ac_rfl) ?_
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      wp_steps
      refine SepWP.weaken_pre (P' :=
        arrayAt (chainAt A) 104 chainsPtr (hd :: tl) ∗
        A.pool ∗ stackAt fsp dropChainStack ∗
        (((ss + 72#64) ↦₆₄ chainsCap) ∗
          ((ss + 80#64) ↦₆₄ chainsPtr) ∗
          ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
          (if chainsCap = 0 then emp
           else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
             memRegion (chainsPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
               ((chainsCap.toNat - (hd :: tl).length) * 104)) ∗
          Frame))
        (Entails.of_eq (by ac_rfl)) ?_
      refine SepWP.mono
        (hloop s0 fsp ss chainsPtr hfsp_align
          (hd :: tl) chainsPtr _ _
          (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
          ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
          hx19 rfl rfl rfl) ?_
      intro sm Pm _ _ h
      exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩
  · intro sm hpcm hrunm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
      hx19_m, hx20_m⟩
    refine SepWP.weaken_pre
      (post_loop_weaken_at_72 A ss chainsCap chainsPtr cs.length hlen_le hcap_lt _) ?_
    have hstep2 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics (trTrapExterns C abs)))
        (entry + 160#64) sm
        (((ss + 72#64) ↦₆₄ chainsCap) ∗ ((ss + 80#64) ↦₆₄ chainsPtr) ∗ memRegion (ss + 88#64) 8 ∗
          (if (chainsCap == 0#64) = true then emp
           else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗ memRegion chainsPtr (chainsCap.toNat * 104)) ∗
          A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sf Pf =>
          (Pf ⊢ memRegion (ss + 72#64) 24 ∗ A.pool ∗
            memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sf fsp ∧
          sf.readReg64 .x19 = ss) := by
      rw [stackAt_dropChain_split_alloc fsp]
      by_cases hcap : (chainsCap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (chains_header24_weaken ss chainsCap chainsPtr _) ?_
        refine align_pre (by ac_rfl) ?_
        wp_done
      · wp_steps
        have hmul : 104#64 * chainsCap = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
        have hmul2 : chainsCap * 104#64 = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
        have htoNat : (BitVec.ofNat 64 (chainsCap.toNat * 104)).toNat = chainsCap.toNat * 104 :=
          Nat.mod_eq_of_lt (Nat.lt_trans hcap_lt (by decide))
        wp_call hdealloc (chainsPtr, chainsCap.toNat * 104, 8)
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right
            (chains_header24_weaken ss chainsCap chainsPtr _))) ?_
        refine align_pre (by rw [hsp_m]; ac_rfl) ?_
        wp_done
    refine SepWP.mono hstep2 (fun sf Pf _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
    rw [stackAt_dropChain_split_alloc fsp]
    exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- `subroutine_ok` proof over `trTrapProgAt` for
`core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#5]`. -/
theorem drop_session_structure3_ok_std3_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A) := by
  have hdc := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain2_ok_trap (b := b) (C := C) hA
  simp only [dropSessionStructureLocal2Spec]
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  have hdealloc_raw := dealloc_ok_at_trap (b := b) (C := C)
    hA hfn (k := num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) (by decide)
  have hdrop_chain_raw : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss2_add_trap]
    exact hdc
  have hdrop_proto_chain_raw : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSessionStructure3Name + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss2_add_trap]
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_proto_chain2_ok_trap hA
  clear hdc
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 0 16
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs3BinCliKits b
    (Rust.withPanics (trTrapExterns C abs)) hfn (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 228 48
  clear hfn
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at *
  wp_init x s0
  have hdealloc := hdealloc_raw
  have hfirst3 := drop_ss2_first3_trap (b := b) (C := C) hdealloc_raw
  have hsender := drop_ss2_sender_trap (b := b) (C := C) hdrop_proto_chain_raw
  have hreceivers := drop_ss2_receivers_trap (b := b) (C := C) hdrop_chain_raw hdealloc_raw
  have htail3 := drop_ss2_tail3_trap (b := b) (C := C) hdealloc_raw
  clear hdealloc_raw hdrop_chain_raw hdrop_proto_chain_raw
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, dropSessionStructure3Name] at hfirst3 hsender hreceivers htail3 hdealloc
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
          A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
          ((ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
      · intro s3 hpc3 hrun3 ⟨hpres3, hx19_3⟩
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
        · refine SepWP.mono
            (hreceivers s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
              G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) s3 _
              hpc3 hrun3 hpres3 hx19_3) ?_
          intro sm Pm _ _ h
          refine ⟨Entails.trans h.1 ?_, h.2⟩
          rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
          have hsp_sub3 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
          rw [hsp_sub3]
          exact Entails.of_eq (by ac_rfl)
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
