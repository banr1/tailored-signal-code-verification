/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2Ext
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5Segs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Proof of `drop_glue::<SessionStructure> [local#5]`

Composes the per-segment drop lemmas to prove `dropSessionStructureLocal2Spec` for
`core::ptr::drop_glue::<SessionStructure> [local#5]` on `trTrapProgAt` and `tripleRatchetProgAtExt`.
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
theorem drop_ss5_prologue_to_100_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (hdrop_proto_chain : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A))
    (s0 : State) (ss v0 v1 v2 v3 v4 v5 : BitVec 64)
    (G : SessionGhost) (senderSt : Option SenderChain) (Frame : SepProp)
    (hpc : s0.pc = (trTrapProgAt b C abs).fnAddr dropSs5Name)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 (Reg.gpr 0#5) = ss) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name + 100#64)
      s0
      ((ssFirst3HeadersAt ss G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root ∗
        optSenderChainAt A (ss + 144#64) G.sender senderSt) ∗
       A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
       (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
         ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
         ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
            memRegion (ss + 144#64) 104) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
          Frame) ∧
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = ss) := by
  have hfirst3 := drop_ss5_first3_trap (b := b) (C := C) hdealloc
  have hsender := drop_ss5_sender_trap (b := b) (C := C) hdrop_proto_chain
  clear hdealloc hdrop_proto_chain
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 0 16
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  subst hx0
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 hsp_align (by decide)
  refine SepWP.seq_clean (mid := entry + 16#64)
    (P_mid :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender senderSt ∗
        memRegion (s0.sp - 4192#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        Frame))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
    have hsp_sub : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine SepWP.align_pre_local5
      (by dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine SepWP.seq_clean (mid := entry + 80#64)
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender senderSt ∗
        A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
        ((memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
         Frame))
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
      refine SepWP.mono
        (hsender s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender senderSt s2 _
          hpc2 hrun2 hpres2 hx19_2) ?_
      intro sm Pm _ _ h
      exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩

set_option maxHeartbeats 1200000 in
theorem drop_ss5_mid_100_to_160_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hdealloc : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (hdrop_chain : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A))
    (s0 s3 : State) (fsp ss chainsCap chainsPtr : BitVec 64)
    (cs_raw : List (ChainGhost × ReceiverChain)) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (trTrapProgAt b C abs).fnAddr dropSs5Name + 100#64)
    (hrun3 : s3.status = .Running)
    (hpres3 : Saved48Preserved s0 s3 fsp)
    (hx19_3 : s3.readReg64 .x19 = ss) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name + 160#64)
      s3
      (vecAt A 104 8 (chainAt A) (ss + 72#64) chainsCap chainsPtr cs_raw ∗
        A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (ss + 72#64) 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss) := by
  have hloop := drop_ss5_receiver_loop_trap (b := b) (C := C) hdrop_chain
  clear hdrop_chain
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [trTrapProgAt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 100 12
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 132 28
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics
    (trTrapExterns C abs))).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  rcases hpres3 with ⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop_at_72 A 104 8 (chainAt A) ss chainsCap chainsPtr cs_raw)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  generalize cs_raw = cs at hlen_le hlen_lt ⊢
  refine SepWP.seq_clean (mid := entry + 132#64)
    (P_mid :=
      ((ss + 72#64) ↦₆₄ chainsCap) ∗
      ((ss + 80#64) ↦₆₄ chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion chainsPtr (cs.length * 104) ∗
      (if chainsCap = 0 then emp
       else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
         memRegion (chainsPtr + BitVec.ofNat 64 (cs.length * 104))
           ((chainsCap.toNat - cs.length) * 104)) ∗
      (A.pool ∗ stackAt fsp dropChainStack ∗ Frame))
    (Q := fun sm =>
      Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ss ∧
      sm.readReg64 .x20 = chainsPtr)
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps
      refine SepWP.align_pre_local5 (by ac_rfl) ?_
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
        (hloop s0 fsp ss chainsPtr hfsp_align (hd :: tl) chainsPtr _ _
          (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
          ⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
          hx19_3 rfl rfl rfl) ?_
      intro sm Pm _ _ h
      exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩
  · intro sm hpcm hrunm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
      hx19_m, hx20_m⟩
    refine SepWP.weaken_pre
      (post_loop_weaken_at_72 A ss chainsCap chainsPtr cs.length hlen_le hcap_lt _) ?_
    rw [stackAt_dropChain_split_alloc fsp]
    by_cases hcap : (chainsCap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (chains_header24_weaken ss chainsCap chainsPtr _) ?_
      refine SepWP.align_pre_local5 (by ac_rfl) ?_
      wp_done
    · wp_steps
      have hmul : 104#64 * chainsCap = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
      have hmul2 : chainsCap * 104#64 = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
      wp_call hdealloc (chainsPtr, chainsCap.toNat * 104, 8)
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (chains_header24_weaken ss chainsCap chainsPtr _))) ?_
      refine SepWP.align_pre_local5 (by rw [hsp_m]; ac_rfl) ?_
      wp_done

/-! ## Proof on `trTrapProgAt` -/

set_option maxHeartbeats 1200000 in
theorem drop_session_structure5_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name)
      (dropSessionStructureLocal2Spec A) := by
  have hdc := CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain2_ok_trap
    (b := b) (C := C) hA
  simp only [dropSessionStructureLocal2Spec]
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  have hdealloc_raw := dealloc_ok_at_trap (b := b) (C := C) hA hfn
    (k := num% (ls_off% "__rustc::__rust_dealloc" -
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (by decide)
  have hdrop_chain_raw : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss5_add]
    exact hdc
  have hdrop_proto_chain_raw : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss5_add]
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_proto_chain2_ok_trap hA
  clear hdc
  dsimp only [trTrapProgAt, dropSs5Name] at hfn ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics (trTrapExterns C abs)) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 228 48
  clear hfn
  wp_init x s0
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hprol := drop_ss5_prologue_to_100_trap (b := b) (C := C) hdealloc_raw hdrop_proto_chain_raw
  have hmid := drop_ss5_mid_100_to_160_trap (b := b) (C := C) hdealloc_raw hdrop_chain_raw
  have htail3 := drop_ss5_tail3_trap (b := b) (C := C) hdealloc_raw
  clear hdealloc_raw hdrop_chain_raw hdrop_proto_chain_raw
  dsimp only [trTrapProgAt, dropSs5Name] at hprol hmid htail3 hdealloc
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
  refine SepWP.seq_clean (mid := entry + 100#64)
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
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
       (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · refine SepWP.weaken_pre (P' :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root ∗
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
      (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) ∗
       (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
         sgnPinDealloc A pCap pPtr ∗
         sgnPinDealloc A kCap kPtr ∗
         vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
       (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
       memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16))
      (Entails.of_eq (by dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt]; ac_rfl)) ?_
    refine SepWP.mono
      (hprol s0 (s0.readReg64 (Reg.gpr 0#5)) v0 v1 v2 v3 v4 v5 G st.senderChain _
        (by assumption) (by assumption) (by assumption) rfl) ?_
    intro sm Pm _ _ hp
    exact ⟨Entails.trans hp.1 (Entails.of_eq (by ac_rfl)), hp.2⟩
  · intro s3 hpc3 hrun3 ⟨hpres3, hx19_3⟩
    refine SepWP.seq_clean (mid := entry + 160#64)
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
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
         memRegion ((s0.sp - 48#64) - 4144#64) 48 ∗
         (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hmid s0 s3 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) _ hfsp_align hpc3 hrun3 hpres3 hx19_3) ?_
      intro sm Pm _ _ hm
      exact ⟨Entails.trans hm.1 (Entails.of_eq (by ac_rfl)), hm.2⟩
    · intro s4 hpc4 hrun4 ⟨hpres4, hx19_4⟩
      refine SepWP.seq_clean (mid := entry + 228#64)
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
          (htail3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G
            s4 _ hpc4 hrun4 hpres4 hx19_4) ?_
        intro sm Pm _ _ ht
        refine ⟨Entails.trans ht.1 ?_, ht.2⟩
        rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
        exact Entails.of_eq (by ac_rfl)
      · intro s5 hpc5 hrun5 ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5,
          htrace_5, hvregs_5⟩, hx19_5⟩
        dsimp only [vecPinDealloc]
        by_cases hcap : (G.pq.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (pq_header24_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
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

/-! ## Generalization to `tripleRatchetProgAtExt` -/

set_option maxHeartbeats 1200000 in
theorem drop_ss5_prologue_to_100_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (hdrop_proto_chain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A))
    (s0 : State) (ss v0 v1 v2 v3 v4 v5 : BitVec 64)
    (G : SessionGhost) (senderSt : Option SenderChain) (Frame : SepProp)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSs5Name)
    (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 (Reg.gpr 0#5) = ss) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 100#64)
      s0
      ((ssFirst3HeadersAt ss G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root ∗
        optSenderChainAt A (ss + 144#64) G.sender senderSt) ∗
       A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
       (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
         ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
         ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24 ∗
            memRegion (ss + 144#64) 104) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
          Frame) ∧
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = ss) := by
  have hfirst3 := drop_ss5_first3_ext (b := b) hdealloc
  have hsender := drop_ss5_sender_ext (b := b) hdrop_proto_chain
  clear hdealloc hdrop_proto_chain
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 0 16
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  subst hx0
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 hsp_align (by decide)
  refine SepWP.seq_clean (mid := entry + 16#64)
    (P_mid :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender senderSt ∗
        memRegion (s0.sp - 4192#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        Frame))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
    have hsp_sub : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
    rw [hsp_sub]
    wp_steps
    refine SepWP.align_pre_local5
      (by dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.lr, Reg.fp]; ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine SepWP.seq_clean (mid := entry + 80#64)
      (P_mid :=
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender senderSt ∗
        A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
        ((memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
         Frame))
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
      refine SepWP.mono
        (hsender s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G.sender senderSt s2 _
          hpc2 hrun2 hpres2 hx19_2) ?_
      intro sm Pm _ _ h
      exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩

set_option maxHeartbeats 1200000 in
theorem drop_ss5_mid_100_to_160_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (rustDeallocSpec A))
    (hdrop_chain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A))
    (s0 s3 : State) (fsp ss chainsCap chainsPtr : BitVec 64)
    (cs_raw : List (ChainGhost × ReceiverChain)) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 100#64)
    (hrun3 : s3.status = .Running)
    (hpres3 : Saved48Preserved s0 s3 fsp)
    (hx19_3 : s3.readReg64 .x19 = ss) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name + 160#64)
      s3
      (vecAt A 104 8 (chainAt A) (ss + 72#64) chainsCap chainsPtr cs_raw ∗
        A.pool ∗ stackAt fsp dropChainStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (ss + 72#64) 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss) := by
  have hloop := drop_ss5_receiver_loop_ext (b := b) hdrop_chain
  clear hdrop_chain
  simp only [rustDeallocSpec] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at *
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 100 12
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 132 28
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  rcases hpres3 with ⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop_at_72 A 104 8 (chainAt A) ss chainsCap chainsPtr cs_raw)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  generalize cs_raw = cs at hlen_le hlen_lt ⊢
  refine SepWP.seq_clean (mid := entry + 132#64)
    (P_mid :=
      ((ss + 72#64) ↦₆₄ chainsCap) ∗
      ((ss + 80#64) ↦₆₄ chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion chainsPtr (cs.length * 104) ∗
      (if chainsCap = 0 then emp
       else A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
         memRegion (chainsPtr + BitVec.ofNat 64 (cs.length * 104))
           ((chainsCap.toNat - cs.length) * 104)) ∗
      (A.pool ∗ stackAt fsp dropChainStack ∗ Frame))
    (Q := fun sm =>
      Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ss ∧
      sm.readReg64 .x20 = chainsPtr)
    ?_ ?_
  · cases cs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps
      refine SepWP.align_pre_local5 (by ac_rfl) ?_
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
        (hloop s0 fsp ss chainsPtr hfsp_align (hd :: tl) chainsPtr _ _
          (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
          ⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩
          hx19_3 rfl rfl rfl) ?_
      intro sm Pm _ _ h
      exact ⟨Entails.trans h.1 (Entails.of_eq (by ac_rfl)), h.2⟩
  · intro sm hpcm hrunm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
      hx19_m, hx20_m⟩
    refine SepWP.weaken_pre
      (post_loop_weaken_at_72 A ss chainsCap chainsPtr cs.length hlen_le hcap_lt _) ?_
    rw [stackAt_dropChain_split_alloc fsp]
    by_cases hcap : (chainsCap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (chains_header24_weaken ss chainsCap chainsPtr _) ?_
      refine SepWP.align_pre_local5 (by ac_rfl) ?_
      wp_done
    · wp_steps
      have hmul : 104#64 * chainsCap = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
      have hmul2 : chainsCap * 104#64 = BitVec.ofNat 64 (chainsCap.toNat * 104) := by bv_omega
      wp_call hdealloc (chainsPtr, chainsCap.toNat * 104, 8)
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (chains_header24_weaken ss chainsCap chainsPtr _))) ?_
      refine SepWP.align_pre_local5 (by rw [hsp_m]; ac_rfl) ?_
      wp_done

set_option maxHeartbeats 1200000 in
theorem drop_session_structure5_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name)
      (dropSessionStructureLocal2Spec A) := by
  have hdc := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.drop_chain2_of_allocHooks_ext
    (b := b) hA
  simp only [dropSessionStructureLocal2Spec]
  have hfn : libsignalSessionCode.fnOff dropSs5Name =
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
  have hdealloc_raw := dealloc_ok_at_ext (b := b) hA hfn
    (k := num% (ls_off% "__rustc::__rust_dealloc" -
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (by decide)
  have hdrop_chain_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss5_add_ext]
    exact hdc
  have hdrop_proto_chain_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSs5Name +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      (dropProtoChainSpec A) := by
    rw [← fnAddr_dropChain_eq_ss5_add_ext]
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.drop_proto_chain2_of_allocHooks_ext
      (b := b) hA
  clear hdc
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at hfn ⊢
  code_fetches_range CryptoVerification.libsignalSessionCode dropSs5BinCli b
    (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 228 48
  clear hfn
  wp_init x s0
  have hdealloc := hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc
  have hprol := drop_ss5_prologue_to_100_ext (b := b) hdealloc_raw hdrop_proto_chain_raw
  have hmid := drop_ss5_mid_100_to_160_ext (b := b) hdealloc_raw hdrop_chain_raw
  have htail3 := drop_ss5_tail3_ext (b := b) hdealloc_raw
  clear hdealloc_raw hdrop_chain_raw hdrop_proto_chain_raw
  dsimp only [tripleRatchetProgAtExt, dropSs5Name] at hprol hmid htail3 hdealloc
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
  refine SepWP.seq_clean (mid := entry + 100#64)
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
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
       (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · refine SepWP.weaken_pre (P' :=
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A G.root ∗
        optSenderChainAt A (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st.senderChain) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
      (((s0.sp - 48#64) ↦₆₄ v0) ∗ ((s0.sp - 40#64) ↦₆₄ v1) ∗
        ((s0.sp - 32#64) ↦₆₄ v2) ∗ ((s0.sp - 24#64) ↦₆₄ v3) ∗
        ((s0.sp - 16#64) ↦₆₄ v4) ∗ ((s0.sp - 8#64) ↦₆₄ v5)) ∗
      (vecAt A 104 8 (chainAt A) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) ∗
       (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
         sgnPinDealloc A pCap pPtr ∗
         sgnPinDealloc A kCap kPtr ∗
         vecPinDealloc A ⟨G.alice.cap, G.alice.ptr⟩) ∗
       (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
         ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
         memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A G.pq) ∗
       memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16))
      (Entails.of_eq (by dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt]; ac_rfl)) ?_
    refine SepWP.mono
      (hprol s0 (s0.readReg64 (Reg.gpr 0#5)) v0 v1 v2 v3 v4 v5 G st.senderChain _
        (by assumption) (by assumption) (by assumption) rfl) ?_
    intro sm Pm _ _ hp
    exact ⟨Entails.trans hp.1 (Entails.of_eq (by ac_rfl)), hp.2⟩
  · intro s3 hpc3 hrun3 ⟨hpres3, hx19_3⟩
    refine SepWP.seq_clean (mid := entry + 160#64)
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
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
           memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
         memRegion ((s0.sp - 48#64) - 4144#64) 48 ∗
         (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · refine SepWP.mono
        (hmid s0 s3 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) _ hfsp_align hpc3 hrun3 hpres3 hx19_3) ?_
      intro sm Pm _ _ hm
      exact ⟨Entails.trans hm.1 (Entails.of_eq (by ac_rfl)), hm.2⟩
    · intro s4 hpc4 hrun4 ⟨hpres4, hx19_4⟩
      refine SepWP.seq_clean (mid := entry + 228#64)
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
          (htail3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align pCap pPtr kCap kPtr G
            s4 _ hpc4 hrun4 hpres4 hx19_4) ?_
        intro sm Pm _ _ ht
        refine ⟨Entails.trans ht.1 ?_, ht.2⟩
        rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
        exact Entails.of_eq (by ac_rfl)
      · intro s5 hpc5 hrun5 ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5,
          htrace_5, hvregs_5⟩, hx19_5⟩
        dsimp only [vecPinDealloc]
        by_cases hcap : (G.pq.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (pq_header24_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
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

end CryptoVerification.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5
