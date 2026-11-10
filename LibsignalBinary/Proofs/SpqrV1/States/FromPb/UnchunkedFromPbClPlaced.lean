/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPb
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbEk
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Closed `[LibsignalPlacement]` Contracts for Unchunked `from_pb` (`UnchunkedFromPbClPlaced`)

Discharges `<Authenticator>::from_pb` (Block `330`) and `drop_glue::<unchunked::Ct1SentEkReceived>`
(Block `286`) for `<Ct1Sent>::from_pb` (Block `339`) and `<EkSentCt1Received>::from_pb` (Block `348`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.Unchunked

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero extractLsb'_0_64_append extractLsb'_64_64_append

private theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks} [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

abbrev spqrRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

/-! ## 1. Block `330`: `<Authenticator>::from_pb` Closed Contract -/

theorem auth_from_pb_pinned_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_330 (Rust.withPanics ext)) (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 330)]
  exact subroutine_ok_withLsCodeLoaded_of_plain (auth_from_pb_pinned_placed_ok
    (spqr_hook_ok_of_mem hshim) (spqr_hook_ok_of_mem halloc) (spqr_hook_ok_of_mem hmemcpy)
    (Eq.trans spqr_externAt?_of_mem hpanic))

theorem auth_from_pb_pinned_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 330 (Rust.withPanics ext)) (lsmpl.base 330)
      (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) :=
  ls_to_blockProgram (auth_from_pb_pinned_cl_placed_ok hshim halloc hmemcpy hpanic)

theorem auth_from_pb_pinned_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) :=
  ls_subroutine_ok_of_block (auth_from_pb_pinned_cl_placed_ok hshim halloc hmemcpy hpanic) hidx

theorem auth_from_pb_pinned_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 330) (withMemEq m (authFromPbPinnedSpec A)) :=
  lscall_blk_cl (auth_from_pb_pinned_cl_placed_ok hshim halloc hmemcpy hpanic) hcl hidx

/-! ## 2. Block `286`: `drop_glue::<unchunked::Ct1SentEkReceived>` Closed Contract -/

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_286 H) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 286)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_unchunked_ct1_sent_ek_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 286 H) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  ls_to_blockProgram (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc)

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_on [LibsignalPlacement]
    {A : RustAlloc} {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H]
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A)) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  ls_subroutine_ok_of_block (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hidx

theorem drop_proto_unchunked_ct1_sent_ek_received_mem_on [LibsignalPlacement]
    {A : RustAlloc} {callerProg : Program} {idx : Nat} {H : String → Option (State → State)}
    [IsLsBlockProg callerProg idx H] {m : Memory}
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  lscall_blk_cl (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hcl hidx

/-! ## 3. Shared `SepWP` / `SepWPp` Sequencing Helpers with `LibsignalCodeLoaded` -/

@[local arm64_norm] private theorem sub_beq_zero_eq_beq (x y : BitVec 64) :
    (x - y == 0#64) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x - y ≠ 0#64 := by intro h0; apply h; bv_omega
    simp [h, hne]

@[local arm64_norm] private theorem bne_eq_not_beq (x y : BitVec 64) : (x != y) = !(x == y) := rfl

private theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hP, hQ⟩ hclm =>
    SepWP.weaken_pre hP (h2 sm hpc hrun hclm hQ))

private theorem sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

private theorem sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hclm hq))

private theorem onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : sm.trace = s0.trace) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]; apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢; rw [htrace] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

private theorem sepWPp_pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (h : φ → SepWPp prog ret s P' Q Qp oom) (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp oom := by
  rw [hf]; exact SepWPp.pure_left h

private theorem sepWPp_call_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))
    (fun sf _ _ hm => False.elim (by rw [hoom_eq] at hm; exact not_satisfies_false_sepConj hm))

/-! ## 4. Block `339`: `<Ct1Sent>::from_pb` Closed Contract -/

private theorem authenticatorAt_sub168_unpack (A : RustAlloc) (sp : BitVec 64) (auth : Authenticator) :
    authenticatorAt A (sp - 168#64) auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64, ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        (((sp - 168#64) ↦₆₄ ca1) ∗ ((sp - 160#64) ↦₆₄ pa1) ∗
         ((sp - 152#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp - 144#64) ↦₆₄ ca2) ∗ ((sp - 136#64) ↦₆₄ pa2) ∗
         ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗ vecU8Payload A ca2 pa2 auth.macKey := by
  have h := authenticatorAt_unpack A (sp - 168#64) auth
  have h1 : (sp - 168#64) + 8#64 = sp - 160#64 := by bv_omega
  have h2 : (sp - 168#64) + 16#64 = sp - 152#64 := by bv_omega
  have h3 : (sp - 168#64) + 24#64 = sp - 144#64 := by bv_omega
  have h4 : (sp - 168#64) + 32#64 = sp - 136#64 := by bv_omega
  have h5 : (sp - 168#64) + 40#64 = sp - 128#64 := by bv_omega
  rwa [h1, h2, h3, h4, h5] at h

private theorem authenticatorPBPinnedAt_72_entails_dealloc (A : RustAlloc)
    (ga : AuthenticatorPBGhost) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 72#64) auth ⊢ auth72HeadersAt a ⟨ga.rootKey, ga.macKey⟩ ∗
      vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  rw [← twoVecHeadersAt_72_eq]; exact authenticatorPBPinnedAt_entails_dealloc A ga (a + 72#64) auth

private theorem memRegion_176_128_split_8_48_72 (sp : BitVec 64) :
    memRegion (sp - 176#64) 128 =
      memRegion (sp - 176#64) 8 ∗ memRegion (sp - 168#64) 48 ∗ memRegion (sp - 120#64) 72 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 120) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 48) (k := 72) (b' := sp - 120#64) rfl (by bv_omega) (by decide)]

private theorem sepWP_pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P Rest : SepProp} {Q : State → SepProp → Prop}
    (h : φ → SepWP prog ret s Rest Q) (heq : P = ⌜φ⌝ ∗ Rest := by sep_focus) :
    SepWP prog ret s P Q := by
  rw [heq]; exact SepWP.pure_elim h

local macro "saved48S0" sp:term "," s0:term : term =>
  `((($sp - 48#64) ↦₆₄ ($s0).readReg64 .fp) ∗ (($sp - 40#64) ↦₆₄ ($s0).readReg64 .lr) ∗
    (($sp - 32#64) ↦₆₄ ($s0).readReg64 .x22) ∗ (($sp - 24#64) ↦₆₄ ($s0).readReg64 .x21) ∗
    (($sp - 16#64) ↦₆₄ ($s0).readReg64 .x20) ∗ (($sp - 8#64) ↦₆₄ ($s0).readReg64 .x19))
local macro "saved48Vars" sp:term "," fp:term "," lr:term "," x22:term "," x21:term "," x20:term "," x19:term : term =>
  `((($sp - 48#64) ↦₆₄ $fp) ∗ (($sp - 40#64) ↦₆₄ $lr) ∗ (($sp - 32#64) ↦₆₄ $x22) ∗
    (($sp - 24#64) ↦₆₄ $x21) ∗ (($sp - 16#64) ↦₆₄ $x20) ∗ (($sp - 8#64) ↦₆₄ $x19))
local macro "ct1Tail" A:term "," s0:term : term =>
  `(($A).pool ∗ memRegion (($s0).sp - 4336#64) 64 ∗ stackAt (($s0).sp - 176#64) allocHookStack ∗
    memRegion (($s0).sp - 176#64) 128 ∗ (saved48S0 ($s0).sp, $s0))
local macro "ct1OutNone" out:term : term =>
  `(($out ↦₆₄ noneCap) ∗ (($out + 8#64) ↦₈ 0#8) ∗ memRegion ($out + 9#64) 119)
local macro "ct1Vecs" A:term "," pbA:term "," pb:term "," c1:term "," p1:term "," c2:term "," p2:term "," c3:term "," p3:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).hdr.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).es.length) ∗
    (($pbA + 48#64) ↦₆₄ $c3) ∗ (($pbA + 56#64) ↦₆₄ $p3) ∗ (($pbA + 64#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    (($pbA + 120#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).hdr ∗
    vecU8Payload $A $c2 $p2 ($pb).es ∗ vecU8Payload $A $c3 $p3 ($pb).ct1)
local macro "ct1Unpacked" A:term "," pbA:term "," pb:term "," authOpt:term "," c1:term "," p1:term "," c2:term "," p2:term "," c3:term "," p3:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).hdr.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).es.length) ∗
    (($pbA + 48#64) ↦₆₄ $c3) ∗ (($pbA + 56#64) ↦₆₄ $p3) ∗ (($pbA + 64#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    $authOpt ∗ (($pbA + 120#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).hdr ∗
    vecU8Payload $A $c2 $p2 ($pb).es ∗ vecU8Payload $A $c3 $p3 ($pb).ct1)

set_option maxHeartbeats 800000 in
private theorem ct1_sent_from_pb_err_drop_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA : BitVec 64} {pb : V1State.Unchunked.Ct1Sent}
    {R : SepProp} {s0 s1 : State} {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : ThreeVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_339).base + 236#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 119) ∗
        (protoUnchunked3VecHeadersAt pbA g ∗ optProtoAuthenticatorAt A (pbA + 72#64) pb.auth ∗
          memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)
      (WppPost (ct1SentFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPost, ct1SentFromPbSpec, Unchunked.SendCt.Ct1Sent.from_pb, hcond, Bool.false_eq_true, ↓reduceIte,
    ct1SentResultAt, stackAt_ct1SentFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := (blkPl_339).base + 296#64)
    (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗
      memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · cases pb.auth with
    | none =>
      rw [optProtoAuthenticatorAt_72_none]
      have hstep : SepWP ((blkPC_339).rebase (blkPl_339).base H) ((blkPl_339).base + 296#64) s1
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 119) ∗
            (protoUnchunked3VecHeadersAt pbA g ∗ (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40) ∗
              memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)
          (fun sm Pm => (Pm ⊢ ((ct1OutNone out) ∗
            (protoUnchunked3VecHeadersAt pbA g ∗ (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40) ∗
              memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)) ∧
            Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) := by
        wp_steps; refine align_pre (by dsimp only [noneCap]) ?_; wp_done
      exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A pbA))))) hstep
    | some a =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (protoAuthenticatorAt_entails_dealloc A (pbA + 72#64) a))))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga; rw [twoVecHeadersAt_72_eq]
      apply sepWP_pure_elim_focus (ga.v1.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine seq_clean (mid := (blkPl_339).base + 276#64)
        (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗
          (auth72HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 120#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [auth72HeadersAt, vecCapPtrDealloc]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine align_pre (by dsimp only [noneCap]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
      · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1⟩, hx19_a1⟩
        have hstepa2 : SepWP ((blkPC_339).rebase (blkPl_339).base H) ((blkPl_339).base + 296#64) sa1
            ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗
              (auth72HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 120#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)
            (fun sm Pm => (Pm ⊢ ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ auth72HeadersAt pbA ga ∗
              memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)) ∧
              Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) := by
          dsimp only [auth72HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
          (sepConj_mono_left (auth72HeadersAt_entails_memRegion_48 pbA ga))))) hstepa2
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    refine seq_clean (mid := (blkPl_339).base + 316#64)
      (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗
        memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      refine seq_clean (mid := (blkPl_339).base + 336#64)
        (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗
          memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
      · intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩, hx19_4⟩
        dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;> simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (protoUnchunked3VecHeadersAt_entails_memRegion_128 pbA g)
            (sepConj_mono_right (stackAt_ct1SentFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
          rw [stackAt_ct1SentFromPb_split_allocHook s0.sp]; wp_done
        · wp_steps
          refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
            (Entails.trans (Entails.of_eq (show _ =
              (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 8) ∗
              (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) by unfold protoUnchunked3VecHeadersAt; ac_rfl))
              (sepConj_mono_left (protoUnchunked3VecHeadersAt_entails_memRegion_128 pbA g)))
            (sepConj_mono_right (stackAt_ct1SentFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
          wp_apply; wp_done

private theorem ct1_sent_from_pb_err_drop_unpacked_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 c3 p3 : BitVec 64}
    {pb : V1State.Unchunked.Ct1Sent} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_339).base + 236#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (memRegion out 128 ∗ (ct1Unpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 72#64) pb.auth), c1, p1, c2, p2, c3, p3) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ (saved48S0 s0.sp, s0))
      (WppPost (ct1SentFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub176 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_128_err_split out)
    (sepConj_mono_left (unpacked_ct1Sent_entails_dealloc A pbA c1 p1
      (BitVec.ofNat 64 pb.hdr.length) c2 p2 (BitVec.ofNat 64 pb.es.length)
      c3 p3 (BitVec.ofNat 64 pb.ct1.length) pb.epoch pb.auth pb.hdr pb.es pb.ct1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (ct1_sent_from_pb_err_drop_placed (v_out0 := v_out0) (v_out8 := v_out8)
      (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩⟩) hdealloc_raw hcond hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)

set_option maxHeartbeats 1200000 in
private theorem ct1_sent_from_pb_ok_after_auth_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 c3 p3 : BitVec 64}
    {pb : V1State.Unchunked.Ct1Sent} {auth : ProtoAuthenticator}
    {ga : AuthenticatorPBGhost} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hpc1 : s1.pc = (blkPl_339).base + 92#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64))
    (hx19_1 : s1.readReg64 .x19 = pbA) (hx20_1 : s1.readReg64 .x20 = ga.rootKey.cap)
    (hx21_1 : s1.readReg64 .x21 = pb.epoch) (hx22_1 : s1.readReg64 .x22 = out)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (memRegion out 128 ∗ (ct1Unpacked A, pbA, pb, (authenticatorPBPinnedAt A ga (pbA + 72#64) auth), c1, p1, c2, p2, c3, p3) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 8 ∗
        authenticatorAt A (s0.sp - 168#64) (Authenticator.fromPb auth) ∗ memRegion (s0.sp - 120#64) 72 ∗ (saved48S0 s0.sp, s0))
      (WppPost (ct1SentFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPost, ct1SentFromPbSpec, Unchunked.SendCt.Ct1Sent.from_pb, hcond, hauth, ↓reduceIte,
    spqrAuthApi, ct1SentResultAt, stackAt_ct1SentFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := (blkPl_339).base + 180#64)
    (P_mid := (ct1SentAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
      (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8 ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ct1Tail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap) ?_ ?_
  · refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (authenticatorPBPinnedAt_72_entails_dealloc A ga pbA auth)))))))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (authenticatorAt_sub168_unpack A s0.sp (Authenticator.fromPb auth)))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.SepWP.exists_left; intro ca1; apply ProofLib.SepWP.exists_left; intro pa1
    apply ProofLib.SepWP.exists_left; intro ca2; apply ProofLib.SepWP.exists_left; intro pa2
    rw [ProofLib.memRegion_cells (s0.sp - 120#64) 9 (by decide), memRegion_128_eq_cells16 out]
    cells_unfold
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]
    wp_pull_exists; wp_steps; rw [stackAt_authFromPb_split_allocHook_sub176 s0.sp]
    have hpack_out := ct1SentAt_pack A (F := F) out ca1 pa1 ca2 pa2 c1 p1 c2 p2 c3 p3 pb.epoch (Authenticator.fromPb auth) pb.hdr pb.es pb.ct1
    have hpack_sp := memRegion_ct1Sent_scratch_restore s0.sp ca1 pa1 (BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length)
      ca2 pa2 (BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) c1 p1 (BitVec.ofNat 64 pb.hdr.length)
      c2 p2 (BitVec.ofNat 64 pb.es.length) c3 p3 (BitVec.ofNat 64 pb.ct1.length)
    have hpack_pb := unpacked_ct1Sent_headers_entails_memRegion_72_8 pbA c1 p1 (BitVec.ofNat 64 pb.hdr.length)
      c2 p2 (BitVec.ofNat 64 pb.es.length) c3 p3 (BitVec.ofNat 64 pb.ct1.length) pb.epoch
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) ∗
        ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((out + 96#64) ↦₆₄ c3) ∗ ((out + 104#64) ↦₆₄ p3) ∗ ((out + 112#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((out + 120#64) ↦₆₄ pb.epoch)) ∗
       vecU8Payload A ca1 pa1 (Authenticator.fromPb auth).rootKey ∗ vecU8Payload A ca2 pa2 (Authenticator.fromPb auth).macKey ∗
       vecU8Payload A c1 p1 pb.hdr ∗ vecU8Payload A c2 p2 pb.es ∗ vecU8Payload A c3 p3 pb.ct1) ∗
      (((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((pbA + 120#64) ↦₆₄ pb.epoch)) ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗
       vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗
      (memRegion (s0.sp - 176#64) 8 ∗
        (((s0.sp - 168#64) ↦₆₄ ca1) ∗ ((s0.sp - 160#64) ↦₆₄ pa1) ∗ ((s0.sp - 152#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
         ((s0.sp - 144#64) ↦₆₄ ca2) ∗ ((s0.sp - 136#64) ↦₆₄ pa2) ∗ ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)) ∗
        (((s0.sp - 120#64) ↦₆₄ c1) ∗ ((s0.sp - 112#64) ↦₆₄ p1) ∗ ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((s0.sp - 96#64) ↦₆₄ c2) ∗ ((s0.sp - 88#64) ↦₆₄ p2) ∗ ((s0.sp - 80#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((s0.sp - 72#64) ↦₆₄ c3) ∗ ((s0.sp - 64#64) ↦₆₄ p3) ∗ ((s0.sp - 56#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length))) ∗
      A.pool ∗ memRegion (s0.sp - 4336#64) 64 ∗ stackAt (s0.sp - 176#64) allocHookStack ∗ (saved48S0 s0.sp, s0) by ac_rfl))
      (sepConj_mono hpack_out (sepConj_mono (sepConj_mono_left hpack_pb) (sepConj_mono_left hpack_sp)))) ?_
    refine align_pre (by ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2, hx20_2⟩
    refine seq_clean (mid := (blkPl_339).base + 200#64)
      (P_mid := (ct1SentAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
        (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8 ∗
          vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ct1Tail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [auth72HeadersAt, vecCapPtrDealloc]
      by_cases hca1 : (ga.rootKey.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [auth72HeadersAt, vecCapPtrDealloc]
      by_cases hca2 : (ga.macKey.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (memRegion_72_auth72_8_entails_128 pbA ⟨ga.rootKey, ga.macKey⟩)
          (sepConj_mono_right (stackAt_ct1SentFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ct1SentFromPb_split_allocHook s0.sp]; wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans (Entails.of_eq (show _ =
            (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8) ∗
            (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ memRegion ga.macKey.ptr ga.macKey.cap.toNat) by unfold auth72HeadersAt; ac_rfl))
            (sepConj_mono_left (memRegion_72_auth72_8_entails_128 pbA ⟨ga.rootKey, ga.macKey⟩)))
          (sepConj_mono_right (stackAt_ct1SentFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply; wp_done

set_option maxHeartbeats 1200000 in
/-- Closed `[LibsignalPlacement]` contract for `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb` (Block `339`). -/
theorem ct1_sent_from_pb_cl_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_339 (Rust.withPanics ext)) (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 339)]
  change subroutine_ok ((blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext)) (blkPl_339).base _
  have hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  have hauth_cl : subroutine_ok ((blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext))
      (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) :=
    auth_from_pb_pinned_cl_on hshim halloc hmemcpy hpanic
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align_bv : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  have ⟨hm0, hx0, hx1⟩ : s0.mem ⊨ (memRegion out 128 ∗ protoUnchunkedCt1SentAt A pbA pb ∗
      A.pool ∗ stackAt s0.sp ct1SentFromPbStack) ∗ R ∧ s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = pbA := by
    simp only [ct1SentFromPbSpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; exact ⟨hpre.2, hpre.1⟩
  refine ⟨memRegion out 128 ∗ protoUnchunkedCt1SentAt A pbA pb ∗
    A.pool ∗ stackAt s0.sp ct1SentFromPbStack, R, hm0, ?_⟩
  rw [stackAt_ct1SentFromPb_split s0.sp]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left (protoUnchunkedCt1SentAt_unpack A pbA pb))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro c1; apply SepWPp.exists_elim; intro p1
  apply SepWPp.exists_elim; intro c2; apply SepWPp.exists_elim; intro p2
  apply SepWPp.exists_elim; intro c3; apply SepWPp.exists_elim; intro p3
  apply sepWPp_pure_elim_focus (pb.hdr.length < 2 ^ 63 ∧ pb.es.length < 2 ^ 63 ∧
    pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63); intro ⟨hl1, hl2, hl3, _⟩
  cells_unfold
  apply SepWPp.exists_elim; intro fp_old; apply SepWPp.exists_elim; intro lr_old
  apply SepWPp.exists_elim; intro x22_old; apply SepWPp.exists_elim; intro x21_old
  apply SepWPp.exists_elim; intro x20_old; apply SepWPp.exists_elim; intro x19_old
  by_cases hcond : (pb.hdr.length == HEADER_SIZE &&
      pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true
  · have hhdr_t : (BitVec.ofNat 64 pb.hdr.length == 64#64) = true := by
      rw [ofNat_beq_lit_iff hl1 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1.1
    have hes_t : (BitVec.ofNat 64 pb.es.length == 2080#64) = true := by
      rw [ofNat_beq_lit_iff hl2 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1.2
    have hct1_t : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true := by
      rw [ofNat_beq_lit_iff hl3 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.2
    cases hauth : pb.auth with
    | none =>
      apply SepWPp.of_sepWP_ret
      simp only [withMemEq, ct1SentFromPbSpec, Unchunked.SendCt.Ct1Sent.from_pb, hcond, hauth, ↓reduceIte,
        ct1SentResultAt, stackAt_ct1SentFromPb_split_dropStack32]
      rw [optProtoAuthenticatorAt_72_none]
      refine SepWP.weaken_pre (sepConj_mono_left (memRegion_128_err_split out)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
      refine seq_clean_lscl hcl (mid := lsmpl.base 286)
        (P_mid := (ct1OutNone out) ∗
          protoUnchunkedCt1SentEkReceivedAt A pbA { epoch := pb.epoch, auth := none, es := pb.hdr, ek := pb.es, ct1 := pb.ct1 } ∗
          A.pool ∗ (memRegion (s0.sp - 4336#64) 208 ∗ stackAt s0.sp dropStack32))
        (Q := fun sm => sm.readReg64 .x0 = pbA ∧ sm.readReg64 .lr = s0.readReg64 .lr ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) ?_ ?_
      · wp_steps
        have hpre_none :
            ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119 ∗
             (ct1Unpacked A, pbA, pb, (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40), c1, p1, c2, p2, c3, p3) ∗
             A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ saved48S0 s0.sp, s0) ⊢
            (ct1OutNone out) ∗
            protoUnchunkedCt1SentEkReceivedAt A pbA { epoch := pb.epoch, auth := none, es := pb.hdr, ek := pb.es, ct1 := pb.ct1 } ∗
            A.pool ∗ (memRegion (s0.sp - 4336#64) 208 ∗ stackAt s0.sp dropStack32) := by
          refine Entails.trans (Entails.of_eq (show _ =
            (ct1OutNone out) ∗
            (ct1Unpacked A, pbA, pb, (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40), c1, p1, c2, p2, c3, p3) ∗
            A.pool ∗ (stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ (saved48S0 s0.sp, s0)) by ac_rfl)) ?_
          exact sepConj_mono_right (sepConj_mono
            (unpacked_ct1Sent_auth_none_pack A pbA c1 p1 c2 p2 c3 p3 pb.epoch pb.hdr pb.es pb.ct1)
            (sepConj_mono_right (stackAt_ct1SentFromPb_tail_dropStack32 s0.sp _ _ _ _ _ _)))
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by
          dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl)) hpre_none) ?_; wp_done
      · intro sm hpcm hrunm hclm ⟨hx0_m, hlr_m, hsp_m, hcs_m, htr_m⟩
        have hdrop_raw := drop_proto_unchunked_ct1_sent_ek_received_mem_on
          (callerProg := (blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext)) hdealloc hclm
        simp only [withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop_raw
        dsimp only [protoUnchunkedCt1SentEkReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop_raw
        wp_apply; wp_done
    | some auth =>
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        optProtoAuthenticatorAt A (pbA + 72#64) (some auth) ∗
        (memRegion out 128 ∗ (ct1Vecs A, pbA, pb, c1, p1, c2, p2, c3, p3) ∗
         A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
         saved48Vars s0.sp, fp_old, lr_old, x22_old, x21_old, x20_old, x19_old) by ac_rfl))
        (sepConj_mono_left (optProtoAuthenticatorAt_some_unpack A (pbA + 72#64) auth))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro ga
      apply sepWPp_pure_elim_focus (ga.rootKey.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      rw [memRegion_176_128_split_8_48_72 s0.sp]
      refine sepWPp_seq_clean_lscl hcl (mid := lsmpl.base 330)
        (P_mid := (memRegion (s0.sp - 168#64) 48 ∗ authenticatorPBPinnedAt A ga (pbA + 72#64) auth ∗
          A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack) ∗
          (memRegion out 128 ∗ (ct1Vecs A, pbA, pb, c1, p1, c2, p2, c3, p3) ∗
           memRegion (s0.sp - 176#64) 8 ∗ memRegion (s0.sp - 120#64) 72 ∗ (saved48S0 s0.sp, s0)))
        (Q_regs := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧
          sm.readReg64 .x0 = s0.sp - 168#64 ∧ sm.readReg64 .x1 = pbA + 72#64 ∧
          sm.readReg64 .lr = (blkPl_339).base + 92#64 ∧
          sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap ∧
          sm.readReg64 .x21 = pb.epoch ∧ sm.readReg64 .x22 = out) ?_ ?_
      · wp_steps
        rw [← sepConj_assoc ((pbA + 72#64) ↦₆₄ ga.rootKey.cap),
            ← authenticatorPBPinnedAt_eq_cap_tail A ga (pbA + 72#64) auth]
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · intro sm hpcm hrunm hclm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx0_m, hx1_m, hlr_m, hx19_m, hx20_m, hx21_m, hx22_m⟩
        have hsp_align_m : sm.spAligned = true := by
          simp only [State.spAligned, hsp_m, sp_and_15_sub_aligned s0.sp 176#64 (by decide)]; exact hsp_align_bv
        refine sepWPp_call_ret hauth_cl (x := ⟨s0.sp - 168#64, pbA + 72#64, ga, auth⟩)
          hpcm hrunm hsp_align_m hlr_m ?_ ?_ (fun _ _ => rfl) ?_
        · intro R' hm'; dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hclm, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_m, hx1_m⟩, Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'⟩
        · intro sf; dsimp only [withLsCodeLoaded, withMemEq, authFromPbPinnedSpec, ct1SentFromPbSpec]
          exact onPanic_frame_entails htrace_m
        · intro s1 hpc1 hrun1 hsp1 ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
          rw [hx19_m] at hx19_1; rw [hx20_m] at hx20_1; rw [hx21_m] at hx21_1; rw [hx22_m] at hx22_1
          rw [hx23_m] at hx23_1; rw [hx24_m] at hx24_1; rw [hx25_m] at hx25_1; rw [hx26_m] at hx26_1
          rw [hx27_m] at hx27_1; rw [hx28_m] at hx28_1; rw [hsp_m] at hsp1
          dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; intro htrace_s1; rw [htrace_m] at htrace_s1
          exact SepWP.weaken_pre (Entails.of_eq (by rw [hsp_m]; ac_rfl))
            (ct1_sent_from_pb_ok_after_auth_placed hdealloc_raw hcond hauth hpc1 hrun1
              ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp1, htrace_s1, hvregs_1.trans hvregs_m⟩
              hx19_1 hx20_1 hx21_1 hx22_1 hsp_align_bv)
  · apply SepWPp.of_sepWP_ret
    have hcond_f : (pb.hdr.length == HEADER_SIZE &&
        pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false := Bool.eq_false_iff.mpr hcond
    refine seq_clean (mid := (blkPl_339).base + 236#64)
      (P_mid := (memRegion out 128 ∗ (ct1Unpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 72#64) pb.auth), c1, p1, c2, p2, c3, p3) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ (saved48S0 s0.sp, s0)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · by_cases h1 : (BitVec.ofNat 64 pb.hdr.length == 64#64) = true
      · by_cases h2 : (BitVec.ofNat 64 pb.es.length == 2080#64) = true
        · by_cases h3 : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true
          · exfalso; apply hcond
            rw [ofNat_beq_lit_iff hl1 (by decide)] at h1; rw [ofNat_beq_lit_iff hl2 (by decide)] at h2
            rw [ofNat_beq_lit_iff hl3 (by decide)] at h3
            simp [h1, h2, h3, HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE]
          · have h3_f : (BitVec.ofNat 64 pb.ct1.length == 960#64) = false := Bool.eq_false_iff.mpr h3
            wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
        · have h2_f : (BitVec.ofNat 64 pb.es.length == 2080#64) = false := Bool.eq_false_iff.mpr h2
          wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · have h1_f : (BitVec.ofNat 64 pb.hdr.length == 64#64) = false := Bool.eq_false_iff.mpr h1
        wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
      exact ct1_sent_from_pb_err_drop_unpacked_placed hdealloc_raw hcond_f hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv

theorem ct1_sent_from_pb_cl_blockProgram [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 339 (Rust.withPanics ext)) (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F)) :=
  ls_to_blockProgram (ct1_sent_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy hpanic)

theorem ct1_sent_from_pb_cl_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 339) (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F)) :=
  ls_subroutine_ok_of_block (ct1_sent_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy hpanic) hidx

theorem ct1_sent_from_pb_mem_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 339) (withMemEq m (ct1SentFromPbSpec A F)) :=
  lscall_blk_cl (ct1_sent_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy hpanic) hcl hidx

theorem ct1_sent_from_pb_on_333_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F)) :=
  ct1_sent_from_pb_cl_on hshim halloc hdealloc hmemcpy hpanic

/-! ## 5. Block `348`: `<EkSentCt1Received>::from_pb` Closed Contract -/

private theorem authenticatorPBPinnedAt_48_entails_dealloc (A : RustAlloc)
    (ga : AuthenticatorPBGhost) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 48#64) auth ⊢
      auth48HeadersAt a ⟨ga.rootKey, ga.macKey⟩ ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  rw [← twoVecHeadersAt_48_eq]; exact authenticatorPBPinnedAt_entails_dealloc A ga (a + 48#64) auth

private theorem protoUnchunked2VecHeadersAt_entails_memRegion_104 (a : BitVec 64) (g : TwoVecGhost) :
    protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ⊢ memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (twoVecHeadersAt_entails_memRegion_48 a g)

private theorem authenticatorAt_sub144_unpack (A : RustAlloc) (sp : BitVec 64) (auth : Authenticator) :
    authenticatorAt A (sp - 144#64) auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64, ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        (((sp - 144#64) ↦₆₄ ca1) ∗ ((sp - 136#64) ↦₆₄ pa1) ∗ ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp - 120#64) ↦₆₄ ca2) ∗ ((sp - 112#64) ↦₆₄ pa2) ∗ ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗ vecU8Payload A ca2 pa2 auth.macKey := by
  have h := authenticatorAt_unpack A (sp - 144#64) auth
  have h1 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h2 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  have h3 : (sp - 144#64) + 24#64 = sp - 120#64 := by bv_omega
  have h4 : (sp - 144#64) + 32#64 = sp - 112#64 := by bv_omega
  have h5 : (sp - 144#64) + 40#64 = sp - 104#64 := by bv_omega
  rwa [h1, h2, h3, h4, h5] at h

private theorem memRegion_144_96_split_48_48 (sp : BitVec 64) :
    memRegion (sp - 144#64) 96 = memRegion (sp - 144#64) 48 ∗ memRegion (sp - 96#64) 48 :=
  ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 48) (b' := sp - 96#64) rfl (by bv_omega) (by decide)

local macro "ekTail" A:term "," s0:term : term =>
  `(($A).pool ∗ memRegion (($s0).sp - 4304#64) 64 ∗ stackAt (($s0).sp - 144#64) allocHookStack ∗
    memRegion (($s0).sp - 144#64) 96 ∗ (saved48S0 ($s0).sp, $s0))
local macro "ekOutNone" out:term : term =>
  `(($out ↦₆₄ noneCap) ∗ (($out + 8#64) ↦₈ 0#8) ∗ memRegion ($out + 9#64) 95)
local macro "ekVecs" A:term "," pbA:term "," pb:term "," c1:term "," p1:term "," c2:term "," p2:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).dk.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    (($pbA + 96#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).dk ∗ vecU8Payload $A $c2 $p2 ($pb).ct1)
local macro "ekUnpacked" A:term "," pbA:term "," pb:term "," authOpt:term "," c1:term "," p1:term "," c2:term "," p2:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).dk.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    $authOpt ∗ (($pbA + 96#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).dk ∗ vecU8Payload $A $c2 $p2 ($pb).ct1)

set_option maxHeartbeats 800000 in
private theorem ek_sent_ct1_received_from_pb_err_drop_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_348).base + 176#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗ optProtoAuthenticatorAt A (pbA + 48#64) pb.auth ∗
          memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, Bool.false_eq_true, ↓reduceIte, ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := (blkPl_348).base + 236#64)
    (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗
      memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · cases pb.auth with
    | none =>
      rw [optProtoAuthenticatorAt_48_none]
      have hstep : SepWP ((blkPC_348).rebase (blkPl_348).base H) ((blkPl_348).base + 236#64) s1
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
            (protoUnchunked2VecHeadersAt pbA g ∗ (((pbA + 48#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 56#64) 40) ∗
              memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
          (fun sm Pm => (Pm ⊢ ((ekOutNone out) ∗
            (protoUnchunked2VecHeadersAt pbA g ∗ (((pbA + 48#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 56#64) 40) ∗
              memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)) ∧
            Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) := by
        wp_steps; refine align_pre (by dsimp only [noneCap]) ?_; wp_done
      exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A pbA))))) hstep
    | some a =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (protoAuthenticatorAt_entails_dealloc A (pbA + 48#64) a))))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga; rw [twoVecHeadersAt_48_eq]
      apply sepWP_pure_elim_focus (ga.v1.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine seq_clean (mid := (blkPl_348).base + 216#64)
        (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗
          (auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [auth48HeadersAt, vecCapPtrDealloc]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine align_pre (by dsimp only [noneCap]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
      · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1⟩, hx19_a1⟩
        have hstepa2 : SepWP ((blkPC_348).rebase (blkPl_348).base H) ((blkPl_348).base + 236#64) sa1
            ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗
              (auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 96#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
            (fun sm Pm => (Pm ⊢ ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ auth48HeadersAt pbA ga ∗
              memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)) ∧
              Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) := by
          dsimp only [auth48HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
          (sepConj_mono_left (auth48HeadersAt_entails_memRegion_48 pbA ga))))) hstepa2
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    refine seq_clean (mid := (blkPl_348).base + 256#64)
      (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗
        memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans (Entails.of_eq (show _ =
            (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
            (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
              unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; ac_rfl))
            (sepConj_mono_left (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply; wp_done

private theorem ek_sent_ct1_received_from_pb_err_drop_unpacked_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_348).base + 176#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) pb.auth), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_104_err_split out)
    (sepConj_mono_left (unpacked_ekSentCt1Received_entails_dealloc A pbA c1 p1
      (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch pb.auth pb.dk pb.ct1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (ek_sent_ct1_received_from_pb_err_drop_placed (v_out0 := v_out0) (v_out8 := v_out8) (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩)
      hdealloc_raw hcond hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)

set_option maxHeartbeats 800000 in
private theorem ek_sent_ct1_received_from_pb_auth_none_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (blkPl_348).base + 296#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, hauth, ↓reduceIte, ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := (blkPl_348).base + 328#64)
    (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗
      memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by dsimp only [noneCap]) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
    by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
      rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done
    · wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
        (Entails.trans (Entails.of_eq (show _ =
          (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
          (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
            unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; ac_rfl))
          (sepConj_mono_left (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
      wp_apply; wp_done

private theorem ek_sent_ct1_received_from_pb_auth_none_unpacked_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (blkPl_348).base + 296#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) none), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_104_err_split out)
    (sepConj_mono_left (Entails.trans
      (unpacked_ekSentCt1Received_entails_dealloc A pbA c1 p1
        (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch none pb.dk pb.ct1)
      (sepConj_mono_right (sepConj_mono_left (by
        rw [optProtoAuthenticatorAt_48_none]; exact optProtoAuthenticatorAt_48_none_entails_memRegion_48 A pbA)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (ek_sent_ct1_received_from_pb_auth_none_placed (v_out0 := v_out0) (v_out8 := v_out8) (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩)
      hdealloc_raw hcond hauth hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)

set_option maxHeartbeats 1200000 in
private theorem ek_sent_ct1_received_from_pb_ok_after_auth_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {auth : ProtoAuthenticator}
    {ga : AuthenticatorPBGhost} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hpc1 : s1.pc = (blkPl_348).base + 80#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx19_1 : s1.readReg64 .x19 = pbA) (hx20_1 : s1.readReg64 .x20 = ga.rootKey.cap)
    (hx21_1 : s1.readReg64 .x21 = pb.epoch) (hx22_1 : s1.readReg64 .x22 = out)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (authenticatorPBPinnedAt A ga (pbA + 48#64) auth), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗
        authenticatorAt A (s0.sp - 144#64) (Authenticator.fromPb auth) ∗ memRegion (s0.sp - 96#64) 48 ∗ (saved48S0 s0.sp, s0))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, hauth, ↓reduceIte, spqrAuthApi, ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := (blkPl_348).base + 140#64)
    (P_mid := (ekSentCt1ReceivedAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
      (memRegion pbA 48 ∗ auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ekTail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap) ?_ ?_
  · refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (authenticatorPBPinnedAt_48_entails_dealloc A ga pbA auth))))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (authenticatorAt_sub144_unpack A s0.sp (Authenticator.fromPb auth))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.SepWP.exists_left; intro ca1; apply ProofLib.SepWP.exists_left; intro pa1
    apply ProofLib.SepWP.exists_left; intro ca2; apply ProofLib.SepWP.exists_left; intro pa2
    rw [ProofLib.memRegion_cells (s0.sp - 96#64) 6 (by decide), memRegion_104_eq_cells13 out]
    cells_unfold
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]
    wp_pull_exists; wp_steps; rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
    have hpack_out := ekSentCt1ReceivedAt_pack A (F := F) out ca1 pa1 ca2 pa2 c1 p1 c2 p2 pb.epoch (Authenticator.fromPb auth) pb.dk pb.ct1
    have hpack_sp := memRegion_ekSentCt1Received_scratch_restore s0.sp ca1 pa1 (BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length)
      ca2 pa2 (BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) c1 p1 (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length)
    have hpack_pb := unpacked_ekSentCt1Received_headers_entails_memRegion_48_8 pbA c1 p1 (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) ∗
        ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((out + 96#64) ↦₆₄ pb.epoch)) ∗
       vecU8Payload A ca1 pa1 (Authenticator.fromPb auth).rootKey ∗ vecU8Payload A ca2 pa2 (Authenticator.fromPb auth).macKey ∗
       vecU8Payload A c1 p1 pb.dk ∗ vecU8Payload A c2 p2 pb.ct1) ∗
      (((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((pbA + 96#64) ↦₆₄ pb.epoch)) ∗
       auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗
      ((((s0.sp - 144#64) ↦₆₄ ca1) ∗ ((s0.sp - 136#64) ↦₆₄ pa1) ∗ ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((s0.sp - 120#64) ↦₆₄ ca2) ∗ ((s0.sp - 112#64) ↦₆₄ pa2) ∗ ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)) ∗
       (((s0.sp - 96#64) ↦₆₄ c1) ∗ ((s0.sp - 88#64) ↦₆₄ p1) ∗ ((s0.sp - 80#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((s0.sp - 72#64) ↦₆₄ c2) ∗ ((s0.sp - 64#64) ↦₆₄ p2) ∗ ((s0.sp - 56#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length))) ∗
      A.pool ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ (saved48S0 s0.sp, s0) by ac_rfl))
      (sepConj_mono hpack_out (sepConj_mono (sepConj_mono_left hpack_pb) (sepConj_mono_left hpack_sp)))) ?_
    refine align_pre (by ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2, hx20_2⟩
    refine seq_clean (mid := (blkPl_348).base + 160#64)
      (P_mid := (ekSentCt1ReceivedAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
        (memRegion pbA 48 ∗ auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ekTail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [auth48HeadersAt, vecCapPtrDealloc]
      by_cases hca1 : (ga.rootKey.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [auth48HeadersAt, vecCapPtrDealloc]
      by_cases hca2 : (ga.macKey.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans (Entails.of_eq (show _ =
            (memRegion pbA 48 ∗ auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8) ∗
            (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ memRegion ga.macKey.ptr ga.macKey.cap.toNat) by unfold auth48HeadersAt; ac_rfl))
            (sepConj_mono_left (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply; wp_done

set_option maxHeartbeats 1200000 in
/-- Closed `[LibsignalPlacement]` contract for `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (Block `348`). -/
theorem ek_sent_ct1_received_from_pb_cl_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_348 (Rust.withPanics ext)) (lsmpl.base 348)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 348)]
  change subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext)) (blkPl_348).base _
  have hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  have hauth_cl : subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext))
      (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) :=
    auth_from_pb_pinned_cl_on hshim halloc hmemcpy hpanic
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align_bv : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  have ⟨hm0, hx0, hx1⟩ : s0.mem ⊨ (memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A pbA pb ∗
      A.pool ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack) ∗ R ∧ s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = pbA := by
    simp only [ekSentCt1ReceivedFromPbSpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; exact ⟨hpre.2, hpre.1⟩
  refine ⟨memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A pbA pb ∗
    A.pool ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack, R, hm0, ?_⟩
  rw [stackAt_ekSentCt1ReceivedFromPb_split s0.sp]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_unpack A pbA pb))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro c1; apply SepWPp.exists_elim; intro p1
  apply SepWPp.exists_elim; intro c2; apply SepWPp.exists_elim; intro p2
  apply sepWPp_pure_elim_focus (pb.dk.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63)
  intro ⟨hl1, hl2, _⟩; cells_unfold
  apply SepWPp.exists_elim; intro fp_old; apply SepWPp.exists_elim; intro lr_old
  apply SepWPp.exists_elim; intro x22_old; apply SepWPp.exists_elim; intro x21_old
  apply SepWPp.exists_elim; intro x20_old; apply SepWPp.exists_elim; intro x19_old
  by_cases hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true
  · have hdk_t : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true := by
      rw [ofNat_beq_lit_iff hl1 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1
    have hct1_t : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true := by
      rw [ofNat_beq_lit_iff hl2 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.2
    cases hauth : pb.auth with
    | none =>
      apply SepWPp.of_sepWP_ret; rw [optProtoAuthenticatorAt_48_none]
      refine seq_clean (mid := (blkPl_348).base + 296#64)
        (P_mid := (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) none), c1, p1, c2, p2) ∗
          A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · wp_steps; rw [optProtoAuthenticatorAt_48_none]
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19, noneCap]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
        exact ek_sent_ct1_received_from_pb_auth_none_unpacked_placed hdealloc_raw hcond hauth hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv
    | some auth =>
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        optProtoAuthenticatorAt A (pbA + 48#64) (some auth) ∗
        (memRegion out 104 ∗ (ekVecs A, pbA, pb, c1, p1, c2, p2) ∗
         A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
         saved48Vars s0.sp, fp_old, lr_old, x22_old, x21_old, x20_old, x19_old) by ac_rfl))
        (sepConj_mono_left (optProtoAuthenticatorAt_some_unpack A (pbA + 48#64) auth))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply SepWPp.exists_elim; intro ga
      apply sepWPp_pure_elim_focus (ga.rootKey.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      rw [memRegion_144_96_split_48_48 s0.sp]
      refine sepWPp_seq_clean_lscl hcl (mid := lsmpl.base 330)
        (P_mid := (memRegion (s0.sp - 144#64) 48 ∗ authenticatorPBPinnedAt A ga (pbA + 48#64) auth ∗
          A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack) ∗
          (memRegion out 104 ∗ (ekVecs A, pbA, pb, c1, p1, c2, p2) ∗ memRegion (s0.sp - 96#64) 48 ∗ (saved48S0 s0.sp, s0)))
        (Q_regs := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧
          sm.readReg64 .x0 = s0.sp - 144#64 ∧ sm.readReg64 .x1 = pbA + 48#64 ∧ sm.readReg64 .lr = (blkPl_348).base + 80#64 ∧
          sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap ∧ sm.readReg64 .x21 = pb.epoch ∧ sm.readReg64 .x22 = out) ?_ ?_
      · wp_steps
        rw [← sepConj_assoc ((pbA + 48#64) ↦₆₄ ga.rootKey.cap), ← authenticatorPBPinnedAt_eq_cap_tail A ga (pbA + 48#64) auth]
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · intro sm hpcm hrunm hclm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx0_m, hx1_m, hlr_m, hx19_m, hx20_m, hx21_m, hx22_m⟩
        have hsp_align_m : sm.spAligned = true := by
          simp only [State.spAligned, hsp_m, sp_and_15_sub_aligned s0.sp 144#64 (by decide)]; exact hsp_align_bv
        refine sepWPp_call_ret hauth_cl (x := ⟨s0.sp - 144#64, pbA + 48#64, ga, auth⟩)
          hpcm hrunm hsp_align_m hlr_m ?_ ?_ (fun _ _ => rfl) ?_
        · intro R' hm'; dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hclm, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_m, hx1_m⟩, Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'⟩
        · intro sf; dsimp only [withLsCodeLoaded, authFromPbPinnedSpec, ekSentCt1ReceivedFromPbSpec]
          exact onPanic_frame_entails htrace_m
        · intro s1 hpc1 hrun1 hsp1 ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
          rw [hx19_m] at hx19_1; rw [hx20_m] at hx20_1; rw [hx21_m] at hx21_1; rw [hx22_m] at hx22_1
          rw [hx23_m] at hx23_1; rw [hx24_m] at hx24_1; rw [hx25_m] at hx25_1; rw [hx26_m] at hx26_1
          rw [hx27_m] at hx27_1; rw [hx28_m] at hx28_1; rw [hsp_m] at hsp1
          dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; intro htrace_s1; rw [htrace_m] at htrace_s1
          exact SepWP.weaken_pre (Entails.of_eq (by rw [hsp_m]; ac_rfl))
            (ek_sent_ct1_received_from_pb_ok_after_auth_placed hdealloc_raw hcond hauth hpc1 hrun1
              ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp1, htrace_s1, hvregs_1.trans hvregs_m⟩
              hx19_1 hx20_1 hx21_1 hx22_1 hsp_align_bv)
  · apply SepWPp.of_sepWP_ret
    have hcond_f : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false := Bool.eq_false_iff.mpr hcond
    refine seq_clean (mid := (blkPl_348).base + 176#64)
      (P_mid := (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) pb.auth), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · by_cases h1 : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true
      · by_cases h2 : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true
        · exfalso; apply hcond
          rw [ofNat_beq_lit_iff hl1 (by decide)] at h1; rw [ofNat_beq_lit_iff hl2 (by decide)] at h2
          simp [h1, h2, DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
        · have h2_f : (BitVec.ofNat 64 pb.ct1.length == 960#64) = false := Bool.eq_false_iff.mpr h2
          wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · have h1_f : (BitVec.ofNat 64 pb.dk.length == 2400#64) = false := Bool.eq_false_iff.mpr h1
        wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
      exact ek_sent_ct1_received_from_pb_err_drop_unpacked_placed hdealloc_raw hcond_f hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv

theorem ek_sent_ct1_received_from_pb_cl_blockProgram [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 348 (Rust.withPanics ext)) (lsmpl.base 348)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec A F)) :=
  ls_to_blockProgram (ek_sent_ct1_received_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy hpanic)

theorem ek_sent_ct1_received_from_pb_cl_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 348) (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec A F)) :=
  ls_subroutine_ok_of_block (ek_sent_ct1_received_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy hpanic) hidx

theorem ek_sent_ct1_received_from_pb_mem_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 348) (withMemEq m (ekSentCt1ReceivedFromPbSpec A F)) :=
  lscall_blk_cl (ek_sent_ct1_received_from_pb_cl_placed_ok hshim halloc hdealloc hmemcpy hpanic) hcl hidx

theorem ek_sent_ct1_received_from_pb_on_333_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpySpec)
    (hpanic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 348)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec A F)) :=
  ek_sent_ct1_received_from_pb_cl_on hshim halloc hdealloc hmemcpy hpanic

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  auth_from_pb_pinned_cl_placed_ok auth_from_pb_pinned_cl_blockProgram
  auth_from_pb_pinned_cl_on auth_from_pb_pinned_mem_on
  drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok
  drop_proto_unchunked_ct1_sent_ek_received_cl_blockProgram
  drop_proto_unchunked_ct1_sent_ek_received_cl_on
  drop_proto_unchunked_ct1_sent_ek_received_mem_on
  ct1_sent_from_pb_cl_placed_ok ct1_sent_from_pb_cl_blockProgram
  ct1_sent_from_pb_cl_on ct1_sent_from_pb_mem_on ct1_sent_from_pb_on_333_placed_ok
  ek_sent_ct1_received_from_pb_cl_placed_ok ek_sent_ct1_received_from_pb_cl_blockProgram
  ek_sent_ct1_received_from_pb_cl_on ek_sent_ct1_received_from_pb_mem_on
  ek_sent_ct1_received_from_pb_on_333_placed_ok)
end CryptoVerification.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.Unchunked
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  ct1_sent_from_pb_cl_placed_ok ct1_sent_from_pb_cl_blockProgram
  ct1_sent_from_pb_cl_on ct1_sent_from_pb_mem_on ct1_sent_from_pb_on_333_placed_ok
  ek_sent_ct1_received_from_pb_cl_placed_ok ek_sent_ct1_received_from_pb_cl_blockProgram
  ek_sent_ct1_received_from_pb_cl_on ek_sent_ct1_received_from_pb_mem_on
  ek_sent_ct1_received_from_pb_on_333_placed_ok)
end CryptoVerification.SpqrV1.Unchunked
