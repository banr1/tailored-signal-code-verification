/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

/-!
# Drop Glue for `Option<v1_state::InnerState>` (Loop Variants) and `PqRatchetState`

Proves the share-vector deallocation loops, the `ct1Acknowledged` and `ct1Sampled` variants, and
the full subroutine contracts for
`core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>`
(`0x4c0d4`, Block `267`) and `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>`
(`0x4c460`, Block `270`).
-/

namespace CryptoVerification.SpqrV1.Layout.L28
open Lean Elab Tactic Meta ProofLib
elab "code_fetches_sym_top " codeId:ident decPrefix:ident b:term:max H:term:max
    sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← CodeLookup.lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offLit $len))
end CryptoVerification.SpqrV1.Layout.L28

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L28

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Layout Coincidence of `Ct1Sent` and `Ct1SentEkReceived` (`128` B) -/

def ct1SentToCt1SentEkReceived (st : V1State.Unchunked.Ct1Sent) :
    V1State.Unchunked.Ct1SentEkReceived :=
  { es := st.hdr, ek := st.es, ct1 := st.ct1, auth := st.auth, epoch := st.epoch }

theorem protoUnchunkedCt1SentAt_eq_ct1SentEkReceived (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentAt A a st =
      protoUnchunkedCt1SentEkReceivedAt A a (ct1SentToCt1SentEkReceived st) := rfl

/-! ## Share-Vector Deallocation Loops (`+192..+224` and `+408..+440`) -/

local macro "opt_proto_body_steps " progTerm:term:max entry:term:max offLit:term:max : tactic => `(tactic| (
  intro cur cnt bs s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP $progTerm ($entry + $offLit) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep))

local macro "opt_proto_loop_steps " entry:term:max bodyOff:term:max hdrOff:term:max : tactic => `(tactic| (
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + $bodyOff)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := $entry + $hdrOff)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64) ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _))

private theorem drop_opt_proto_inner_state_body_192 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 204#64 →
      s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 192#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_sym_top libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext)
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" 692
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches
  opt_proto_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry 192#64

private theorem drop_opt_proto_inner_state_loop_192 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 204#64 →
      s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 444#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_opt_proto_inner_state_body_192 (b := b) (ext := ext) hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_sym_top libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext)
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" 692
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches
  opt_proto_loop_steps entry 192#64 204#64

private theorem drop_opt_proto_inner_state_body_408 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 420#64 →
      s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 408#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_sym_top libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext)
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" 692
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches
  opt_proto_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry 408#64

private theorem drop_opt_proto_inner_state_loop_408 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 420#64 →
      s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName + 444#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_opt_proto_inner_state_body_408 (b := b) (ext := ext) hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_sym_top libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext)
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" 692
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches
  opt_proto_loop_steps entry 408#64 420#64

section PlacedLoops
variable [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}

private theorem drop_opt_proto_inner_state_body_192_placed
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_267).base + 204#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 192#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  opt_proto_body_steps ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base 192#64

private theorem drop_opt_proto_inner_state_loop_192_placed
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_267).base + 204#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 444#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_opt_proto_inner_state_body_192_placed hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  opt_proto_loop_steps (blkPl_267).base 192#64 204#64

private theorem drop_opt_proto_inner_state_body_408_placed
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_267).base + 420#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 408#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  opt_proto_body_steps ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base 408#64

private theorem drop_opt_proto_inner_state_loop_408_placed
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_267).base + 420#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 444#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_opt_proto_inner_state_body_408_placed hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  opt_proto_loop_steps (blkPl_267).base 408#64 420#64

end PlacedLoops

/-! ## `ct1Acknowledged` and `ct1Sampled` Variant Proofs -/

local macro "opt_proto_ct1Acknowledged_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 164#64)
    (P_mid := ((a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
      optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
      memRegion (a + 176#64) 48) ∗ $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [optProtoUnchunkedCt1SentAt_none, h16]; wp_steps
      have hnone128 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 120 ⊢ memRegion (a + 8#64) 128 := by
        rw [← h16]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (a + 8#64)
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (a + 8#64) (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt; wp_steps
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (a + 8#64) cap ptr (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      wp_call hct1_sent ⟨a + 8#64, ct1SentToCt1SentEkReceived u⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_; wp_steps
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    have hjoin168 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 40 ⊢ memRegion (a + 8#64) 168 := by
      rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 40 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 168 ∗ memRegion (a + 176#64) 48 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x8000000000000009#64 168 48 176#64 (BitVec.add_assoc a 8#64 168#64).symm rfl
    cases hek : st.receivingEk with
    | none =>
      dsimp only [optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      rw [h144]; wp_steps
      have hnone40 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 32 ⊢ memRegion (a + 136#64) 40 := by
        rw [← h144]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 136#64)
      refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      wp_done
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 136#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      have h152 : (a + 136#64) + 16#64 = a + 152#64 := BitVec.add_assoc a 136#64 16#64
      have h160 : (a + 136#64) + 24#64 = a + 160#64 := BitVec.add_assoc a 136#64 24#64
      refine seq_clean (mid := $entry + 444#64)
        (P_mid := (a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
          ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 160#64) 16 ∗ memRegion (a + 176#64) 48 ∗ $jtExp ∗
          A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
            omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := $entry + 204#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
               ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 160#64) 16 ∗ memRegion (a + 176#64) 48 ∗ $jtExp ∗ memRegion (s0.sp - 4192#64) 48 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
          · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            refine SepWP.strengthen_entails_const ?_
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx19_loop hx20_loop hx21_loop hx22_loop)
            have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by ac_rfl)
      · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
        dsimp only [optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]
        have hhdr40 : ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
            ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 160#64) 16 ⊢ memRegion (a + 136#64) 40 := by
          rw [← h144, ← h152, ← h160]
          exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 136#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_2 hhdr40 ⊢; wp_steps
          refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_done
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt; simp only [hc, ↓reduceIte]; wp_steps
          refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_; wp_done))

theorem drop_opt_proto_inner_state_ct1Acknowledged {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.ct1Acknowledged st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hct1_sent : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"))
      (dropProtoUnchunkedCt1SentEkReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>")) (b := b) (X := Rust.withPanics ext)
      dropOptProtoInnerState_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>") (by decide))
    (drop_proto_unchunked_ct1_sent_ek_received_ok_ext hdealloc)
  have hloop := drop_opt_proto_inner_state_loop_192 (b := b) (ext := ext) hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  code_fetches_sym_top libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext)
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" 692
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt1AcknowledgedAt, optProtoInnerStateJumpTableAt,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hct1_sent hloop hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_ct1Acknowledged_steps entry (optProtoInnerStateJumpTableExpanded b)

theorem drop_opt_proto_inner_state_ct1Acknowledged_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hct1_sent : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 286) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (st : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct1Acknowledged st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  have hdealloc_raw := hdealloc
  have hloop := drop_opt_proto_inner_state_loop_192_placed hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1AcknowledgedAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hct1_sent hloop ⊢
  wp_init a s0
  opt_proto_ct1Acknowledged_steps (blkPl_267).base optProtoInnerStateJumpTablePlacedExpanded

theorem stackAt_sub48_eq_dropStack48 (sp : BitVec 64) :
    memRegion (sp - 4192#64) 48 ∗ stackAt (sp - 48#64) allocHookStack =
      stackAt (sp - 48#64) dropStack48 := by
  have hsub : (sp - 48#64) - 4144#64 = sp - 4192#64 := by bv_omega
  rw [stackAt_dropStack48_split_bottom (sp - 48#64), hsub]

local macro "opt_proto_ct1Sampled_steps " entry:term:max jtExp:term:max : tactic => `(tactic| (
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 348#64)
    (P_mid := (memRegion a 128 ∗
      optProtoPolynomialEncoderAt A (a + 128#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
      optProtoPolynomialDecoderAt A (a + 184#64) (st.receivingEk.map pbToProtoPolyDecoder)) ∗ $jtExp ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedCt1SentAt_none]; wp_steps
      have hnone128 : (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120 ⊢ memRegion a 128 :=
        optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A a
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A a (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none2 := cap_add_two_beq_zero_false hcap_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap_lt
      have hcc_false := cap_xor_highBit_cc_11_false hcap_lt; wp_steps
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A a cap ptr (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      wp_call hct1_sent ⟨a, ct1SentToCt1SentEkReceived u⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_; wp_steps
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    refine seq_clean (mid := $entry + 380#64)
      (P_mid := (memRegion a 184 ∗
        optProtoPolynomialDecoderAt A (a + 184#64) (st.receivingEk.map pbToProtoPolyDecoder)) ∗ $jtExp ∗
        A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
    · have hjoin184 : memRegion a 128 ∗ memRegion (a + 128#64) 56 ⊢ memRegion a 184 := by
        rw [ProofLib.memRegion_split a 128 56 (by decide)]; exact Entails.refl _
      cases hct1 : st.sendingCt1 with
      | none =>
        simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
        have h136 : (a + 128#64) + 8#64 = a + 136#64 := BitVec.add_assoc a 128#64 8#64
        rw [h136]; wp_steps
        have hnone56 : ((a + 128#64) ↦₆₄ noneCap) ∗ memRegion (a + 136#64) 48 ⊢ memRegion (a + 128#64) 56 := by
          rw [← h136]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 128#64)
        refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine align_pre (by ac_rfl) ?_; wp_done
      | some enc =>
        simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 128#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
        have hne_none := cap_add_one_beq_zero_false hcap_lt; wp_steps
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 128#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_eq_dropStack48 s0.sp)) (by sep_focus) ?_
        wp_call hpoly_enc ⟨a + 128#64, pbToProtoPolyEncoder enc⟩
        have hsp_eq : stackAt s1.sp dropStack48 = memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack := by
          rw [hsp_1, ← stackAt_sub48_eq_dropStack48]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_; wp_steps
        change _ at hjoin184; refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx0_2⟩
      have hjoin224 : memRegion a 184 ∗ memRegion (a + 184#64) 40 ⊢ memRegion a 224 := by
        rw [ProofLib.memRegion_split a 184 40 (by decide)]; exact Entails.refl _
      cases hek : st.receivingEk with
      | none =>
        dsimp only [optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
        have h192 : (a + 184#64) + 8#64 = a + 192#64 := BitVec.add_assoc a 184#64 8#64
        rw [h192]; wp_steps
        have hnone40 : ((a + 184#64) ↦₆₄ noneCap) ∗ memRegion (a + 192#64) 32 ⊢ memRegion (a + 184#64) 40 := by
          rw [← h192]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 184#64)
        refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        wp_done
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 184#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have h192 : (a + 184#64) + 8#64 = a + 192#64 := BitVec.add_assoc a 184#64 8#64
        have h200 : (a + 184#64) + 16#64 = a + 200#64 := BitVec.add_assoc a 184#64 16#64
        have h208 : (a + 184#64) + 24#64 = a + 208#64 := BitVec.add_assoc a 184#64 24#64
        refine seq_clean (mid := $entry + 444#64)
          (P_mid := memRegion a 184 ∗
            ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗ ((a + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            memRegion (a + 208#64) 16 ∗ $jtExp ∗
            A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
        · generalize hxs : pb.pts = xs at hpts_le ⊢
          cases xs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
            wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
              omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_clean (mid := $entry + 420#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                (memRegion a 184 ∗ ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗
                 ((a + 200#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ A.live g.ptr (g.cap.toNat * 24) 8 ∗
                 memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 208#64) 16 ∗ $jtExp ∗ memRegion (s0.sp - 4192#64) 48 ∗
                 (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
            · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
            · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              refine SepWP.strengthen_entails_const ?_
                (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx19_loop hx20_loop hx21_loop hx22_loop)
              have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
              conv_rhs =>
                arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
                rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
              exact Entails.of_eq (by ac_rfl)
        · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
          dsimp only [optProtoInnerStateJumpTableExpanded, optProtoInnerStateJumpTablePlacedExpanded]
          have hhdr40 : ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗
              ((a + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 208#64) 16 ⊢ memRegion (a + 184#64) 40 := by
            rw [← h192, ← h200, ← h208]
            exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 184#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
          by_cases hc : g.cap = 0
          · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_3 hhdr40 ⊢; wp_steps
            refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
            refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            wp_done
          · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpts_cap_lt; simp only [hc, ↓reduceIte]; wp_steps
            refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
            refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
            wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_; wp_done))

theorem drop_opt_proto_inner_state_ct1Sampled {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (st : V1State.Chunked.Ct1Sampled) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateVariantSpec A b (some (.ct1Sampled st))) := by
  simp only [dropOptProtoInnerStateVariantSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext) dropOptProtoInnerState_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hct1_sent : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"))
      (dropProtoUnchunkedCt1SentEkReceivedSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>"))
      (b := b) (X := Rust.withPanics ext) dropOptProtoInnerState_fnOff
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>") (by decide))
    (drop_proto_unchunked_ct1_sent_ek_received_ok_ext hdealloc)
  have hpoly_enc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"))
      (dropProtoPolyEncoderSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"))
      (b := b) (X := Rust.withPanics ext) dropOptProtoInnerState_fnOff
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>") (by decide))
    (drop_glue_proto_poly_encoder_ok_ext hdealloc)
  have hloop := drop_opt_proto_inner_state_loop_408 (b := b) (ext := ext) hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  have hadrp : ∀ (hb : b &&& 0xfff#64 = 0#64),
      (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr dropOptProtoInnerStateName + 68#64) &&&
        0xfffffffffffff000#64) = b + bv% (page% ((ls_off% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>") + 68)) := fnAddr_adrp_4c118
  code_fetches_sym_top libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext)
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" 692
  dsimp only [dropProgAtExt, dropOptProtoInnerStateName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt1SampledAt, optProtoInnerStateJumpTableAt,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hct1_sent hpoly_enc hloop hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" = entry
  examples_hide_fetches; wp_init a s0; have hadrp' := hadrp h
  opt_proto_ct1Sampled_steps entry (optProtoInnerStateJumpTableExpanded b)

theorem drop_opt_proto_inner_state_ct1Sampled_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hct1_sent : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 286) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hpoly_enc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (st : V1State.Chunked.Ct1Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct1Sampled st))) := by
  simp only [dropOptProtoInnerStatePlacedVariantSpec]
  have hdealloc_raw := hdealloc
  have hloop := drop_opt_proto_inner_state_loop_408_placed hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hct1_sent hpoly_enc hloop ⊢
  wp_init a s0
  opt_proto_ct1Sampled_steps (blkPl_267).base optProtoInnerStateJumpTablePlacedExpanded

/-! ## Top-Level `0x4c0d4` Proof (`drop_opt_proto_inner_state_ok_ext`) -/

theorem drop_opt_proto_inner_state_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName)
      (dropOptProtoInnerStateSpec A b) := by
  refine subroutine_ok_outcome_intro fun ⟨a, optSt⟩ R s0 hpc hrun hpre hsp => ?_
  cases optSt with
  | none =>
    exact drop_opt_proto_inner_state_none.mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | some st =>
    cases st with
    | keysUnsampled s =>
      exact (drop_opt_proto_inner_state_keysUnsampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | keysSampled s =>
      exact (drop_opt_proto_inner_state_keysSampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerSent s =>
      exact (drop_opt_proto_inner_state_headerSent hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Received s =>
      exact (drop_opt_proto_inner_state_ct1Received hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekSentCt1Received s =>
      exact (drop_opt_proto_inner_state_ekSentCt1Received hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | noHeaderReceived s =>
      exact (drop_opt_proto_inner_state_noHeaderReceived hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerReceived s =>
      exact (drop_opt_proto_inner_state_headerReceived hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Sampled s =>
      exact (drop_opt_proto_inner_state_ct1Sampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekReceivedCt1Sampled s =>
      exact (drop_opt_proto_inner_state_ekReceivedCt1Sampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Acknowledged s =>
      exact (drop_opt_proto_inner_state_ct1Acknowledged hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct2Sampled s =>
      exact (drop_opt_proto_inner_state_ct2Sampled hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout

theorem drop_opt_proto_inner_state_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly_enc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 271) (dropProtoPolyEncoderSpec A))
    (hct1_sent : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 286) (dropProtoUnchunkedCt1SentEkReceivedSpec A))
    (hhdr_sent : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 281) (dropProtoChunkedHeaderSentSpec A))
    (hct1_recv : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 282) (dropProtoChunkedCt1ReceivedSpec A))
    (hhdr_recv : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 283) (dropProtoChunkedHeaderReceivedSpec A))
    (hno_hdr_recv : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 284) (dropProtoChunkedNoHeaderReceivedSpec A))
    (hek_sent_ct1_recv : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (lsmpl.base 285) (dropProtoChunkedEkSentCt1ReceivedSpec A)) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base H) (blkPl_267).base
      (dropOptProtoInnerStatePlacedSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, optSt⟩ R s0 hpc hrun hpre hsp => ?_
  cases optSt with
  | none =>
    exact drop_opt_proto_inner_state_none_placed.mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | some st =>
    cases st with
    | keysUnsampled s =>
      exact (drop_opt_proto_inner_state_keysUnsampled_placed hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | keysSampled s =>
      exact (drop_opt_proto_inner_state_keysSampled_placed hct1_recv s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerSent s =>
      exact (drop_opt_proto_inner_state_headerSent_placed hhdr_sent s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Received s =>
      exact (drop_opt_proto_inner_state_ct1Received_placed hct1_recv s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekSentCt1Received s =>
      exact (drop_opt_proto_inner_state_ekSentCt1Received_placed hek_sent_ct1_recv s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | noHeaderReceived s =>
      exact (drop_opt_proto_inner_state_noHeaderReceived_placed hno_hdr_recv s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerReceived s =>
      exact (drop_opt_proto_inner_state_headerReceived_placed hhdr_recv s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Sampled s =>
      exact (drop_opt_proto_inner_state_ct1Sampled_placed hdealloc hct1_sent hpoly_enc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekReceivedCt1Sampled s =>
      exact (drop_opt_proto_inner_state_ekReceivedCt1Sampled_placed hct1_sent hpoly_enc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Acknowledged s =>
      exact (drop_opt_proto_inner_state_ct1Acknowledged_placed hdealloc hct1_sent s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct2Sampled s =>
      exact (drop_opt_proto_inner_state_ct2Sampled_placed hdealloc hpoly_enc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout

/-! ## `drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` (`0x4c460`) -/

theorem cap_add_three_beq_zero_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    ¬((cap + 3#64 == 0#64) = true) := by
  rw [beq_iff_eq]; intro h
  have h1 : (cap + 3#64).toNat = (cap.toNat + 3) % 2 ^ 64 := BitVec.toNat_add cap 3#64
  rw [h, BitVec.toNat_zero] at h1; omega

theorem cap_ne_zero_slt_one_false {cap : BitVec 64}
    (hlt : cap.toNat < 2 ^ 63) (hne0 : ¬((cap == 0#64) = true)) :
    BitVec.slt cap 1#64 = false := by
  have hne : cap.toNat ≠ 0 := by
    intro h0; apply hne0; rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq h0
  unfold BitVec.slt BitVec.toInt
  simp only [Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceMul, ↓reduceIte,
    decide_eq_false_iff_not]
  split <;> omega

theorem cap_ne_zero_lt_one_false {cap : BitVec 64}
    (hlt : cap.toNat < 2 ^ 63) (hne0 : ¬((cap == 0#64) = true)) :
    ¬(ConditionHolds .LT (subsPState64 cap 1#64) = true) := by
  rw [conditionHolds_lt_subsPState64, cap_ne_zero_slt_one_false hlt hne0]; decide

def optProtoInnerStateTaggedRest (A : RustAlloc) (d w : BitVec 64)
    (optSt : Option V1State.InnerState) : SepProp :=
  ∃∗ P : SepProp, ⌜(d ↦₆₄ w) ∗ P ⊢ optProtoInnerStateAt A d optSt⌝ ∗ P

private theorem expose_word_of_eq {A : RustAlloc} {d w : BitVec 64} {R : SepProp}
    {optSt : Option V1State.InnerState}
    (heq : optProtoInnerStateAt A d optSt = (d ↦₆₄ w) ∗ R)
    (hne3 : ¬((w + 3#64 == 0#64) = true)) :
    optProtoInnerStateAt A d optSt ⊢
      ∃∗ w' : BitVec 64,
        ⌜¬((w' + 3#64 == 0#64) = true)⌝ ∗
        (d ↦₆₄ w') ∗
        optProtoInnerStateTaggedRest A d w' optSt := by
  rw [heq]; refine Entails.sepExists_right w (Entails.pure_right hne3 (sepConj_mono_right ?_))
  unfold optProtoInnerStateTaggedRest
  exact Entails.sepExists_right R (Entails.pure_right (Entails.of_eq heq.symm) (Entails.refl R))

theorem optProtoInnerStateAt_expose_word (A : RustAlloc) (d : BitVec 64)
    (optSt : Option V1State.InnerState) :
    optProtoInnerStateAt A d optSt ⊢
      ∃∗ w : BitVec 64,
        ⌜¬((w + 3#64 == 0#64) = true)⌝ ∗
        (d ↦₆₄ w) ∗
        optProtoInnerStateTaggedRest A d w optSt := by
  cases optSt with
  | none => exact expose_word_of_eq rfl (by decide)
  | some st =>
    cases st with
    | keysUnsampled s => exact expose_word_of_eq rfl (by decide)
    | keysSampled s => exact expose_word_of_eq rfl (by decide)
    | headerSent s => exact expose_word_of_eq rfl (by decide)
    | ct1Received s => exact expose_word_of_eq rfl (by decide)
    | ekSentCt1Received s => exact expose_word_of_eq rfl (by decide)
    | noHeaderReceived s => exact expose_word_of_eq rfl (by decide)
    | headerReceived s => exact expose_word_of_eq rfl (by decide)
    | ekReceivedCt1Sampled s => exact expose_word_of_eq rfl (by decide)
    | ct1Acknowledged s => exact expose_word_of_eq rfl (by decide)
    | ct2Sampled s => exact expose_word_of_eq rfl (by decide)
    | ct1Sampled s =>
      cases huc : s.uc with
      | none =>
        have heq : optProtoInnerStateAt A d (some (.ct1Sampled s)) =
            (d ↦₆₄ noneCap) ∗ (memRegion (d + 8#64) 120 ∗
              optProtoPolynomialEncoderAt A (d + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
              optProtoPolynomialDecoderAt A (d + 184#64) (s.receivingEk.map pbToProtoPolyDecoder)) := by
          dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt]
          rw [huc, optProtoUnchunkedCt1SentAt_none]; ac_rfl
        exact expose_word_of_eq heq (by decide)
      | some u =>
        dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt]
        rw [huc, optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
        refine Entails.trans
          (sepConj_mono_left (protoUnchunkedCt1SentEkReceivedAt_expose_cap A d (ct1SentToCt1SentEkReceived u))) ?_
        rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro cap
        rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro ptr
        rw [sepConj_assoc, sepConj_assoc]; apply Entails.pure_left; intro hcap_lt
        refine Entails.sepExists_right cap (Entails.pure_right (cap_add_three_beq_zero_false hcap_lt) (sepConj_mono_right ?_))
        let P := protoUnchunkedCt1SentEkReceivedRestAt A d cap ptr (ct1SentToCt1SentEkReceived u) ∗
          optProtoPolynomialEncoderAt A (d + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
          optProtoPolynomialDecoderAt A (d + 184#64) (s.receivingEk.map pbToProtoPolyDecoder)
        have hun : (d ↦₆₄ cap) ∗ P ⊢ optProtoInnerStateAt A d (some (.ct1Sampled s)) := by
          dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt, P]
          rw [huc, optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
          refine Entails.trans (Entails.of_eq (by ac_rfl))
            (sepConj_mono_left (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A d cap ptr
              (ct1SentToCt1SentEkReceived u)))
        unfold optProtoInnerStateTaggedRest
        exact Entails.sepExists_right P (Entails.pure_right hun (Entails.refl P))

theorem optProtoInnerStateAt_unexpose_word (A : RustAlloc) (d w : BitVec 64)
    (optSt : Option V1State.InnerState) :
    (d ↦₆₄ w) ∗ optProtoInnerStateTaggedRest A d w optSt ⊢
      optProtoInnerStateAt A d optSt := by
  unfold optProtoInnerStateTaggedRest
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro P
  rw [sepConj_left_comm]; apply Entails.pure_left; intro hun; exact hun

theorem versionNegotiationPBTail_entails_memRegion_24 (a : BitVec 64) (vn : VersionNegotiationPB) :
    optChainParamsPBAt (a + 0x18#64) vn.chainParams ∗
      ((a + 0x24#64) ↦₃₂ vn.direction) ∗
      ((a + 0x28#64) ↦₃₂ vn.minVersion) ∗
      memRegion (a + 0x2c#64) 4 ⊢
    memRegion (a + 24#64) 24 := by
  rw [show (24#64 : BitVec 64) = 0x18#64 from rfl,
      ProofLib.memRegion_split' (b := a + 0x18#64) (n := 12) (k := 12)
        (b' := a + 0x24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x24#64) (n := 4) (k := 8)
        (b' := a + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 0x28#64) (n := 4) (k := 4)
        (b' := a + 0x2c#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (optChainParamsPBAt_entails_memRegion_12 _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono_left (pointsTo32_entails_memRegion _ _)))

theorem versionNegotiationPBAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (vn : VersionNegotiationPB) :
    versionNegotiationPBAt A a vn ⊢
      ∃∗ g : VecPin,
        ⌜g.cap.toNat < 2 ^ 63⌝ ∗
        (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ memRegion (a + 16#64) 32 ∗
        vecCapPtrDealloc A g.cap g.ptr := by
  unfold versionNegotiationPBAt rustBytesVecAt vecU8
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_lt A a cap ptr vn.authKey
  have h2 := versionNegotiationPBTail_entails_memRegion_24 a vn
  have hjoin32 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 = memRegion (a + 16#64) 32 := by
    rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24)
          (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show _ =
      vecU8At A a cap ptr vn.authKey ∗
      (optChainParamsPBAt (a + 0x18#64) vn.chainParams ∗
       ((a + 0x24#64) ↦₃₂ vn.direction) ∗
       ((a + 0x28#64) ↦₃₂ vn.minVersion) ∗
       memRegion (a + 0x2c#64) 4) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h1 h2) ?_
  rw [sepConj_assoc]; apply Entails.pure_left; intro hcap_lt
  refine Entails.pure_right hcap_lt ?_
  dsimp only; rw [← hjoin32]; exact Entails.of_eq (by ac_rfl)

theorem vnHeader_entails_memRegion_48 (a cap ptr : BitVec 64) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a cap)
    (sepConj_mono_left (pointsTo64_entails_memRegion (a + 8#64) ptr))

theorem optVersionNegotiationPBAt_none_entails_memRegion_48 (a : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40 ⊢ memRegion a 48 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

theorem optProtoPqRatchetInnerAt_none_entails_memRegion_224 (d : BitVec 64) :
    (d ↦₆₄ none3Cap') ∗ memRegion (d + 8#64) 216 ⊢ memRegion d 224 := by
  rw [ProofLib.memRegion_split' (b := d) (n := 8) (k := 216) (b' := d + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion d none3Cap')

local macro "proto_pq_ratchet_state_steps " entry:term:max jtTerm:term:max : tactic => `(tactic| (
  rcases x with ⟨a, st⟩
  dsimp only [DropProtoPqRatchetStateGhost.a, DropProtoPqRatchetStateGhost.st] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 44#64)
    (P_mid := (memRegion a 48 ∗ optChainPBAt A (a + 48#64) st.chain ∗
      optProtoPqRatchetInnerAt A (a + 128#64) st.inner) ∗ $jtTerm ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
  · cases hvn : st.versionNegotiation with
    | none =>
      dsimp only [optVersionNegotiationPBAt]; wp_steps
      refine SepWP.focus_weaken (optVersionNegotiationPBAt_none_entails_memRegion_48 a) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21]; try ac_rfl) ?_; wp_done
    | some vn =>
      dsimp only [optVersionNegotiationPBAt]
      refine SepWP.focus_weaken (versionNegotiationPBAt_entails_dealloc A a vn) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩; wp_focus_pure; intro hcap_lt
      dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      by_cases hc0 : (cap == 0#64) = true <;>
        simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
        subst hc_eq; wp_steps
        refine SepWP.focus_weaken (vnHeader_entails_memRegion_48 a 0#64 ptr) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21]; try ac_rfl) ?_; wp_done
      · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
        have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
        wp_steps; wp_apply
        refine SepWP.focus_weaken (vnHeader_entails_memRegion_48 a cap ptr) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx22_1, hx19_1⟩
    refine seq_clean (mid := $entry + 112#64)
      (P_mid := (memRegion a 128 ∗ optProtoPqRatchetInnerAt A (a + 128#64) st.inner) ∗ $jtTerm ∗
        A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hjoin128 : memRegion a 48 ∗ memRegion (a + 48#64) 80 ⊢ memRegion a 128 := by
        rw [ProofLib.memRegion_split a 48 80 (by decide)]; exact Entails.refl _
      cases hch : st.chain with
      | none =>
        have h56 : (a + 48#64) + 8#64 = a + 56#64 := BitVec.add_assoc a 48#64 8#64
        dsimp only [optChainPBAt]; rw [h56]; wp_steps
        have hnone80 : ((a + 48#64) ↦₆₄ noneCap) ∗ memRegion (a + 56#64) 72 ⊢ memRegion (a + 48#64) 80 := by
          rw [← h56]; exact optChainPBAt_none_entails_memRegion_80 (a + 48#64)
        refine SepWP.focus_weaken hnone80 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
        refine align_pre (by ac_rfl) ?_; wp_done
      | some ch =>
        dsimp only [optChainPBAt]
        refine SepWP.focus_weaken (chainPBAt_entails_dealloc A (a + 48#64) ch) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
        have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
        have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
          have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
          omega
        have hne_none := cap_add_one_beq_zero_false hcap_lt_pow
        have h56 : (a + 48#64) + 8#64 = a + 56#64 := BitVec.add_assoc a 48#64 8#64
        have h64 : (a + 48#64) + 16#64 = a + 64#64 := BitVec.add_assoc a 48#64 16#64
        have h72 : (a + 48#64) + 24#64 = a + 72#64 := BitVec.add_assoc a 48#64 24#64
        have h80 : (a + 48#64) + 32#64 = a + 80#64 := BitVec.add_assoc a 48#64 32#64
        have h88 : (a + 48#64) + 40#64 = a + 88#64 := BitVec.add_assoc a 48#64 40#64
        refine seq_clean (mid := $entry + 92#64)
          (P_mid := (memRegion a 48 ∗
            ((a + 48#64) ↦₆₄ g.links.cap) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
            ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
            ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
            memRegion (a + 88#64) 40 ∗ vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
            optProtoPqRatchetInnerAt A (a + 128#64) st.inner) ∗ $jtTerm ∗
            A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
        · by_cases hc : g.links.cap = 0
          · have hnil : ch.links = [] := by rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
            have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            have h0 : arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr [] = emp := rfl
            simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte, emp_sepConj, sepConj_emp]
            wp_steps; rw [← sepConj_emp ((a + 48#64) ↦₆₄ 0#64), ← h0]
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
            wp_call hslice_raw ⟨g.links.ptr, []⟩
            have hsp_eq : stackAt s1.sp dropStack32 = stackAt (s0.sp - 48#64) dropStack32 := by rw [hsp_1]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
            wp_steps; refine align_pre (by simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]; ac_rfl) ?_; wp_done
          · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_lsl7_sub_lsl4 hcap_lt
            have hsplit : g.links.cap.toNat * 112 = ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 ≤ 2 ^ 64 := by rw [← hsplit]; omega
            have hrejoin : memRegion g.links.ptr (ch.links.length * 112) ∗
                memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112)) ((g.links.cap.toNat - ch.links.length) * 112) ⊢
                memRegion g.links.ptr (g.links.cap.toNat * 112) := by
              rw [hsplit, ProofLib.memRegion_split g.links.ptr (ch.links.length * 112) ((g.links.cap.toNat - ch.links.length) * 112) hbound]
              exact Entails.refl _
            simp only [hc, ↓reduceIte]; wp_steps
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
            wp_call hslice_raw ⟨g.links.ptr, ch.links⟩
            have hsp_eq : stackAt s1.sp dropStack32 = stackAt (s0.sp - 48#64) dropStack32 := by rw [hsp_1]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
            refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
            wp_steps; wp_apply
            refine align_pre (by rw [hsp_sf, hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21]; ac_rfl) ?_; wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx22_2, hx19_2⟩
          have hhdr80 : ((a + 48#64) ↦₆₄ g.links.cap) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
              ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
              memRegion (a + 88#64) 40 ⊢ memRegion (a + 48#64) 80 := by
            rw [← h56, ← h64, ← h72, ← h80, ← h88]
            exact chainPBHeaders_entails_memRegion_80 (a + 48#64) g.links.cap g.links.ptr
              (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr
          dsimp only [vecCapPtrDealloc]
          by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
            simp only [hnr, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · wp_steps
            refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
            refine align_pre (by ac_rfl) ?_; wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
            refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx22_3, hx19_3⟩
      have hjoin352 : memRegion a 128 ∗ memRegion (a + 128#64) 224 ⊢ memRegion a 352 := by
        rw [ProofLib.memRegion_split a 128 224 (by decide)]; exact Entails.refl _
      cases hinner : st.inner with
      | none =>
        have h136 : (a + 128#64) + 8#64 = a + 136#64 := BitVec.add_assoc a 128#64 8#64
        dsimp only [optProtoPqRatchetInnerAt, none3Cap']; rw [h136]; wp_steps
        have hnone224 : ((a + 128#64) ↦₆₄ 0xfffffffffffffffd#64) ∗ memRegion (a + 136#64) 216 ⊢
            memRegion (a + 128#64) 224 := by
          rw [← h136]; exact optProtoPqRatchetInnerAt_none_entails_memRegion_224 (a + 128#64)
        refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        wp_done
      | some innerVal =>
        cases innerVal with
        | v1 v1 =>
          dsimp only [optProtoPqRatchetInnerAt]
          refine SepWP.focus_weaken (optProtoInnerStateAt_expose_word A (a + 128#64) v1.innerState) (by sep_focus) ?_
          wp_pull_exists; rename_i w; wp_focus_pure; intro hne3; wp_steps
          refine SepWP.focus_weaken (optProtoInnerStateAt_unexpose_word A (a + 128#64) w v1.innerState) (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_call hinner_raw ⟨a + 128#64, v1.innerState⟩
          refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
          wp_done))

theorem drop_proto_pq_ratchet_state_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPqRatchetStateName)
      (dropProtoPqRatchetStateSpec A b) := by
  simp only [dropProtoPqRatchetStateSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPqRatchetStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext) dropProtoPqRatchetState_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hslice_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPqRatchetStateName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>"))
      (dropProtoEpochSliceSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>"))
      (b := b) (X := Rust.withPanics ext) dropProtoPqRatchetState_fnOff
      (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>") (by decide))
    (drop_proto_epoch_slice_ok_ext hdealloc)
  have hinner_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoPqRatchetStateName +
        bv% (2 ^ 64 - (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>")))
      (dropOptProtoInnerStateSpec A b) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropProtoPqRatchetStateName =
        (dropProgAtExt b ext).fnAddr dropOptProtoInnerStateName +
          BitVec.ofNat 64 (num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>")) :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>"))
        (b := b) (X := Rust.withPanics ext) dropOptProtoInnerState_fnOff dropProtoPqRatchetState_fnOff (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_opt_proto_inner_state_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  simp only [rustDeallocSpec] at hdealloc_raw
  code_fetches_sym_top libsignalSessionCode spqrDropTopBin b (Rust.withPanics ext)
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" 160
  dsimp only [dropProgAtExt, dropProtoPqRatchetStateName, dropProtoEpochSliceSpec,
    dropOptProtoInnerStateSpec, protoPqRatchetStateAt,
    protoPqRatchetStateSize, optProtoInnerStateSize, chainEpochPBSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hslice_raw hinner_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>" = entry
  examples_hide_fetches; wp_init x s0
  proto_pq_ratchet_state_steps entry (optProtoInnerStateJumpTableAt b)

theorem drop_proto_pq_ratchet_state_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_270).rebase (blkPl_270).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hslice_raw : subroutine_ok ((blkPC_270).rebase (blkPl_270).base H) (lsmpl.base 288) (dropProtoEpochSliceSpec A))
    (hinner_raw : subroutine_ok ((blkPC_270).rebase (blkPl_270).base H) (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec A)) :
    subroutine_ok ((blkPC_270).rebase (blkPl_270).base H) (blkPl_270).base
      (dropProtoPqRatchetStatePlacedSpec A) := by
  simp only [dropProtoPqRatchetStatePlacedSpec]
  have hdealloc_raw := hdealloc; simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [dropProtoEpochSliceSpec, dropOptProtoInnerStatePlacedSpec, protoPqRatchetStateAt,
    protoPqRatchetStateSize, optProtoInnerStateSize, chainEpochPBSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hslice_raw hinner_raw ⊢
  wp_init x s0
  proto_pq_ratchet_state_steps (blkPl_270).base optProtoInnerStateJumpTablePlacedAt

end CryptoVerification.SpqrV1.Drop
