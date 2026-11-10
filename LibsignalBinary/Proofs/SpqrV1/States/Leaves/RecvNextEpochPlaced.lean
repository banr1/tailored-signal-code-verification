/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import ProofLib.SepLogic.WPp

/-!
# `<Ct2Sampled>::recv_next_epoch` (Relocatable, Block `355`)

Relocatable `[LibsignalPlacement]` proofs on `lsProg_355 (Rust.withPanics ext)` (`31` instructions):
`ct2_sampled_recv_next_epoch_placed_ok_ext`, `ct2_sampled_recv_next_epoch_placed_cl_ext`, and
`ct2_sampled_recv_next_epoch_placed_ok_x`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-- Framed relocatable call rule for `withLsCodeLoaded lsmpl (dropGluePoly16Spec A)` (Block `265`). -/
theorem call_dropGluePoly16_cl [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)))
    (arrA : BitVec 64) (vecs : List (List GF16))
    {s0 s : State} {sp_call : BitVec 64} {P F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = arrA)
    (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecGF16ListOf A arrA vecs ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ F) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog (s0.readReg64 Reg.lr) sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine SepWP.call_subroutine_frame hcall (x := ⟨arrA, vecs⟩) (F := F)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit, sepConj_assoc] at hm
    dsimp only [withLsCodeLoaded, dropGluePoly16Spec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hlen⟩, hm⟩
  · dsimp only [withLsCodeLoaded, dropGluePoly16Spec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Relocatable `<Ct2Sampled>::recv_next_epoch` (Block `355`, 31 insns) given a plain `subroutine_ok`
    hypothesis for `drop_glue::<[Poly; 16]>` at `lsmpl.base 265`. -/
theorem ct2_sampled_recv_next_epoch_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (lsmpl.base 265) (dropGluePoly16Spec A)) :
    subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (blkPl_355).base
      (ct2SampledRecvNextEpochSpec A F) := by
  simp only [ct2SampledRecvNextEpochSpec, lsProg_355] at hdrop ⊢
  wp_init x s0
  rcases x with ⟨outA, stA, st, epoch, out⟩
  dsimp only at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 2#5) = epoch›
  obtain ⟨hep_ne, hep_add, hout_eq⟩ := ct2Sampled_recv_next_epoch_ok (by assumption)
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hz2 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false :=
    hep_add ▸ ep_add_one_beq_zero_false hep_ne
  refine SepWP.fold (memRegion_56_unfold (s0.readReg64 (Reg.gpr 0#5))) (by sep_focus) ?_
  refine SepWP.fold (stackAt_4160_top_unfold s0.sp) (by sep_focus) ?_
  wp_pull_exists
  unfold chunkedCt2SampledAt unchunkedCt2SentAt
  rw [BitVec.add_assoc (s0.readReg64 (Reg.gpr 1#5)) 400#64 48#64,
      show (400#64 + 48#64 : BitVec 64) = 448#64 from rfl]
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct2) (by sep_focus) ?_
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth) (by sep_focus) ?_
  wp_pull_exists
  rename_i tag vecs g
  refine pure_elim_focus (φ := vecs.length = NUM_POLYS) (by sep_focus) fun hvecs_len => ?_
  have hauth_words : wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]
    simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
      show (400#64 + 8#64 : BitVec 64) = 408#64 from rfl,
      show (408#64 + 8#64 : BitVec 64) = 416#64 from rfl,
      show (416#64 + 8#64 : BitVec 64) = 424#64 from rfl,
      show (424#64 + 8#64 : BitVec 64) = 432#64 from rfl,
      show (432#64 + 8#64 : BitVec 64) = 440#64 from rfl]
  rw [hauth_words]
  wp_steps
  refine SepWP.fold (cells4_restore_4160_bottom s0.sp _ _ _ _) (by sep_focus) ?_
  refine call_dropGluePoly16 hdrop (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm])
    (by assumption)
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm])
    hvecs_len
    (by sep_focus)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf => ?_)
  refine SepWP.fold (Entails.of_eq hauth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (ct2Sampled_stA_post_combine (s0.readReg64 (Reg.gpr 1#5)) tag st.uc.epoch g) (by sep_focus) ?_
  refine SepWP.fold (ct2Sampled_outA_recompose A (s0.readReg64 (Reg.gpr 0#5)) st.uc.auth
    (s0.readReg64 (Reg.gpr 2#5)) out hout_eq g) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_4160_bottom s0.sp).symm) (by sep_focus) ?_
  wp_done

/-- Relocatable `<Ct2Sampled>::recv_next_epoch` (Block `355`, 31 insns) given a `withLsCodeLoaded`
    `subroutine_ok` hypothesis for `drop_glue::<[Poly; 16]>` at `lsmpl.base 265`. -/
theorem ct2_sampled_recv_next_epoch_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_355 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A))) :
    Ct2SampledRecvNextEpochPlacedOkX A F ext := by
  unfold Ct2SampledRecvNextEpochPlacedOkX
  apply subroutine_ok_withLsCodeLoaded_of_left
  simp only [ct2SampledRecvNextEpochSpec, lsProg_355] at hdrop ⊢
  wp_init x s0
  rcases x with ⟨outA, stA, st, epoch, out⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA›
    ‹s0.readReg64 (Reg.gpr 2#5) = epoch›
  obtain ⟨hep_ne, hep_add, hout_eq⟩ := ct2Sampled_recv_next_epoch_ok (by assumption)
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hz2 : (s0.readReg64 (Reg.gpr 2#5) == 0#64) = false :=
    hep_add ▸ ep_add_one_beq_zero_false hep_ne
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 265)
  refine SepWP.fold (memRegion_56_unfold (s0.readReg64 (Reg.gpr 0#5))) (by sep_focus) ?_
  refine SepWP.fold (stackAt_4160_top_unfold s0.sp) (by sep_focus) ?_
  wp_pull_exists
  unfold chunkedCt2SampledAt unchunkedCt2SentAt
  rw [BitVec.add_assoc (s0.readReg64 (Reg.gpr 1#5)) 400#64 48#64,
      show (400#64 + 48#64 : BitVec 64) = 448#64 from rfl]
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A (s0.readReg64 (Reg.gpr 1#5)) st.sending_ct2) (by sep_focus) ?_
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth) (by sep_focus) ?_
  wp_pull_exists
  rename_i tag vecs g
  refine pure_elim_focus (φ := vecs.length = NUM_POLYS) (by sep_focus) fun hvecs_len => ?_
  have hauth_words : wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]
    simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
      show (400#64 + 8#64 : BitVec 64) = 408#64 from rfl,
      show (408#64 + 8#64 : BitVec 64) = 416#64 from rfl,
      show (416#64 + 8#64 : BitVec 64) = 424#64 from rfl,
      show (424#64 + 8#64 : BitVec 64) = 432#64 from rfl,
      show (432#64 + 8#64 : BitVec 64) = 440#64 from rfl]
  rw [hauth_words]
  wp_steps
  refine SepWP.fold (cells4_restore_4160_bottom s0.sp _ _ _ _) (by sep_focus) ?_
  refine call_dropGluePoly16_cl hdrop (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs
    (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
    (by simp only [arm64_norm])
    (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm])
    (by simpa only [State.spAligned] using ‹s0.spAligned = true›)
    (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm])
    (by simp only [Reg.x0, arm64_norm])
    hvecs_len
    (by sep_focus)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf htrace_sf => ?_)
  refine SepWP.fold (Entails.of_eq hauth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (ct2Sampled_stA_post_combine (s0.readReg64 (Reg.gpr 1#5)) tag st.uc.epoch g) (by sep_focus) ?_
  refine SepWP.fold (ct2Sampled_outA_recompose A (s0.readReg64 (Reg.gpr 0#5)) st.uc.auth
    (s0.readReg64 (Reg.gpr 2#5)) out hout_eq g) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_4160_bottom s0.sp).symm) (by sep_focus) ?_
  wp_done

/-- Closed `[LibsignalPlacement]` contract for `<Ct2Sampled>::recv_next_epoch` (Block `355`)
    discharging `drop_glue::<[Poly; 16]>` (Block `265`) via `drop_glue_poly16_placed_ok`. -/
theorem ct2_sampled_recv_next_epoch_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A)) :
    Ct2SampledRecvNextEpochPlacedOkX A F ext :=
  ct2_sampled_recv_next_epoch_placed_cl_ext
    (ls_subroutine_ok_of_block (i := 355) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

end CryptoVerification.SpqrV1.States.Leaves
