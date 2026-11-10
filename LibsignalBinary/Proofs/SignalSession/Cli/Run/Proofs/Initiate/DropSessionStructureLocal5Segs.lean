/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# Segment Lemmas for `drop_glue::<SessionStructure> [local#5]`

Proves per-segment symbolic execution lemmas for `core::ptr::drop_glue::<SessionStructure> [local#5]`
on `trTrapProgAt` and `tripleRatchetProgAtExt`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 1200000 in
theorem drop_ss5_first3_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr dropSs5Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSs5Name + 80#64)
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
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 16 64
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_clean (mid := entry + 40#64) (P_mid :=
    (ssFirst3HeadersAt ss G ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1)
      refine SepWP.align_pre_local5 (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_clean (mid := entry + 60#64) (P_mid :=
      (ssFirst3HeadersAt ss G ∗ vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1)
        refine SepWP.align_pre_local5 (by rw [hsp_1]; ac_rfl) ?_
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
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1)
          refine SepWP.align_pre_local5 (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

set_option maxHeartbeats 1200000 in
theorem drop_ss5_sender_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr dropSs5Name + 80#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSs5Name + 100#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [dropProtoChainSpec] at hdrop_chain
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 80 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
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
      exact SepWP.false_elim_left_local5
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact SepWP.false_elim_left_local5
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
      refine SepWP.align_pre_local5 (by rw [hsp]) ?_
      wp_done

set_option maxHeartbeats 1200000 in
theorem drop_ss5_receiver_loop_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A))
    (s0 : State) (fsp ss ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (trTrapProgAt b C abs).fnAddr dropSs5Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cur →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSs5Name + 132#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          sm.readReg64 .x20 = ptr) := by
  simp only [dropChainSpec] at hdrop_chain
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 112 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
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
    refine SepWP.seq_clean (mid := entry + 120#64)
      (P_mid := memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = cur ∧ sm.readReg64 .x22 = BitVec.ofNat 64 ((g, c) :: tl).length)
      ?_ ?_
    · wp_steps
      wp_call hdrop_chain ⟨cur, (g, c)⟩
      refine SepWP.align_pre_local5 (by rw [hsp]) ?_
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
theorem drop_ss5_tail3_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (trTrapProgAt b C abs).fnAddr dropSs5Name + 160#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr dropSs5Name + 228#64)
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
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 160 68
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_clean (mid := entry + 184#64) (P_mid :=
    (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A kCap kPtr ∗
      vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_call hdealloc (pPtr, pCap.toNat, 1)
      refine SepWP.align_pre_local5 (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_clean (mid := entry + 208#64) (P_mid :=
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_call hdealloc (kPtr, kCap.toNat, 1)
        refine SepWP.align_pre_local5 (by rw [hsp_1]; ac_rfl) ?_
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
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (G.alice.ptr, G.alice.cap.toNat, 1)
          refine SepWP.align_pre_local5 (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left
          (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

/-! ## Segment lemmas on `tripleRatchetProgAtExt` -/

theorem dealloc_hookSat_ext {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext) :
    HookSat (Rust.withPanics ext) "__rustc::__rust_dealloc"
      (rustDeallocSpec A) := by
  simpa [HookSat, Rust.withPanics, Rust.isPanicSymbol] using hA.dealloc

theorem dealloc_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext)
    {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% "__rustc::__rust_dealloc")) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocSpec A) :=
  hook_ok_at_raw hfn hk (by decide) (ls_hook% "__rustc::__rust_dealloc")
    (dealloc_hookSat_ext hA)

theorem fnAddr_dropChain_eq_ss5_add_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name =
      (tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64) := by
  unfold tripleRatchetProgAtExt dropSs5Name
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  bv_omega

set_option maxHeartbeats 1200000 in
theorem drop_ss5_first3_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 80#64)
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
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 16 64
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_clean (mid := entry + 40#64) (P_mid :=
    (ssFirst3HeadersAt ss G ∗
      vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A G.root) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1)
      refine SepWP.align_pre_local5 (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_clean (mid := entry + 60#64) (P_mid :=
      (ssFirst3HeadersAt ss G ∗ vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1)
        refine SepWP.align_pre_local5 (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 80#64) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDealloc A G.root) ∗ A.pool ∗
            stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1)
          refine SepWP.align_pre_local5 (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

set_option maxHeartbeats 1200000 in
theorem drop_ss5_sender_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 80#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 100#64)
        s
        (optSenderChainAt A (ss + 144#64) senderG senderSt ∗
          A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [dropProtoChainSpec] at hdrop_chain
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 80 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro senderG senderSt s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      unfold optSenderChainAt
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 100#64) s
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
      exact SepWP.false_elim_left_local5
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact SepWP.false_elim_left_local5
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
      refine SepWP.align_pre_local5 (by rw [hsp]) ?_
      wp_done

set_option maxHeartbeats 1200000 in
theorem drop_ss5_receiver_loop_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A))
    (s0 : State) (fsp ss ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cur →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 132#64)
        s
        (arrayAt (chainAt A) 104 cur rest ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ A.pool ∗ stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          sm.readReg64 .x20 = ptr) := by
  simp only [dropChainSpec] at hdrop_chain
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 112 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
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
    refine SepWP.seq_clean (mid := entry + 120#64)
      (P_mid := memRegion cur 104 ∗ A.pool ∗ stackAt fsp dropChainStack ∗
        (arrayAt (chainAt A) 104 (cur + 104#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = cur ∧ sm.readReg64 .x22 = BitVec.ofNat 64 ((g, c) :: tl).length)
      ?_ ?_
    · wp_steps
      wp_call hdrop_chain ⟨cur, (g, c)⟩
      refine SepWP.align_pre_local5 (by rw [hsp]) ?_
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
theorem drop_ss5_tail3_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (s0 : State) (fsp ss : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 160#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 228#64)
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
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 160 68
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_clean (mid := entry + 184#64) (P_mid :=
    (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A kCap kPtr ∗
      vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      wp_done
    · wp_steps
      wp_call hdealloc (pPtr, pCap.toNat, 1)
      refine SepWP.align_pre_local5 (by rw [hsp]; ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_clean (mid := entry + 208#64) (P_mid :=
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        wp_done
      · wp_steps
        wp_call hdealloc (kPtr, kCap.toNat, 1)
        refine SepWP.align_pre_local5 (by rw [hsp_1]; ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 228#64) s2
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
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          wp_done
        · wp_steps
          wp_call hdealloc (G.alice.ptr, G.alice.cap.toNat, 1)
          refine SepWP.align_pre_local5 (by rw [hsp_2]; ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left
          (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

end CryptoVerification.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5
