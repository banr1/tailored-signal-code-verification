/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`, `31` instructions)

**Checked by Lean.** Verifies `ct2_sampled_recv_next_epoch_ok_ext` against
`Chunked.SendCt.Ct2Sampled.recv_next_epoch`.
-/

@[expose] public section

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
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

noncomputable abbrev leavesProgAtExt (b : BitVec 64) (ext : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics ext)

abbrev dropGluePoly16Name : String :=
  "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>"

/-- `subroutine_ok` transfer across equal entry addresses. -/
theorem sub_ok_of_addr_eq {prog : Program} {a1 a2 : BitVec 64} {α : Type} {spec : Spec α}
    (heq : a1 = a2) (h : subroutine_ok prog a1 spec) : subroutine_ok prog a2 spec :=
  heq ▸ h

/-- Specialized framed call rule for `dropGluePoly16Spec A`. -/
theorem call_dropGluePoly16 {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hcall : subroutine_ok prog entry (dropGluePoly16Spec A))
    (arrA : BitVec 64) (vecs : List (List GF16))
    {s0 s : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp)
    (hsp_align : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = s0.readReg64 Reg.lr)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = arrA)
    (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecGF16ListOf A arrA vecs ∗ A.pool ∗ stackAt s0.sp dropGluePoly16Stack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = s0.readReg64 Reg.lr → sf.status = .Running →
      sf.sp = s0.sp → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt s0.sp dropGluePoly16Stack) ∗ F) post) :
    SepWP prog (s0.readReg64 Reg.lr) s P post := by
  refine SepWP.call_subroutine_frame hcall (x := ⟨arrA, vecs⟩) (F := F)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit, sepConj_assoc] at hm
    dsimp only [dropGluePoly16Spec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hlen⟩, hm⟩
  · dsimp only [dropGluePoly16Spec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 1. Arithmetic & Spatial Helpers for `Ct2Sampled::recv_next_epoch` -/

theorem ep_add_one_beq_zero_false {ep : BitVec 64} (hne : ep ≠ BitVec.allOnes 64) :
    (ep + 1#64 == 0#64) = false := by
  cases h : (ep + 1#64 == 0#64)
  · rfl
  · exfalso
    have h0 : ep + 1#64 = 0#64 := beq_iff_eq.mp h
    apply hne
    change ep = 0xffffffffffffffff#64
    bv_omega

theorem stackAt_4160_top (sp : BitVec 64) :
    stackAt sp (dropGluePoly16Stack + 32) =
      stackAt (sp - 32#64) dropGluePoly16Stack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp dropGluePoly16Stack 4 (by decide)

theorem stackAt_4160_bottom (sp : BitVec 64) :
    stackAt sp (dropGluePoly16Stack + 32) =
      memRegion (sp - 4160#64) 32 ∗ stackAt sp dropGluePoly16Stack :=
  stackAt_split_bottom sp dropGluePoly16Stack 32 (by decide)

theorem cells4_restore_4160_bottom (sp w0 w1 w2 w3 : BitVec 64) :
    stackAt (sp - 32#64) dropGluePoly16Stack ∗
      (((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
       ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) ⊢
    memRegion (sp - 4160#64) 32 ∗ stackAt sp dropGluePoly16Stack := by
  rw [← stackAt_4160_bottom sp, stackAt_4160_top sp]
  refine sepConj_mono_right ?_
  cells_unfold
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

theorem stackAt_4160_top_unfold (sp : BitVec 64) :
    stackAt sp (dropGluePoly16Stack + 32) ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3,
        stackAt (sp - 32#64) dropGluePoly16Stack ∗
        (((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
         ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  rw [stackAt_4160_top sp]
  cells_unfold
  exact Entails.refl _

theorem cells_succ_off (a off : BitVec 64) (k : Nat) :
    cells (a + off) (k + 1) = ∃∗ v : BitVec 64, ((a + off) ↦₆₄ v) ∗ cells (a + (off + 8#64)) k := by
  rw [cells_succ, BitVec.add_assoc]

theorem memRegion_56_unfold (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗
        ((a + 48#64) ↦₆₄ v6) := by
  rw [ProofLib.memRegion_cells a 7 (by decide), cells_succ]
  simp only [cells_succ_off, cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
    show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
    show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl]
  exact Entails.refl _

theorem ct2Sampled_stA_post_combine (stA : BitVec 64) (tag ep : BitVec 64) (g : AuthWords) :
    (stA ↦₆₄ tag) ∗
      memRegion (stA + 8#64) polyArrayBytes ∗
      memRegion (stA + 392#64) 8 ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      ((stA + 448#64) ↦₆₄ ep) ⊢
    memRegion stA 456 := by
  have h0 : (stA ↦₆₄ tag) ⊢ memRegion stA 8 := by
    rw [pointsTo64_eq_pointsToBytes, ← unpack64_length tag]
    exact pointsToBytes_entails_memRegion _ _
  have h400 : wordsAt (stA + 400#64) (authWordsList g) ⊢ memRegion (stA + 400#64) 48 :=
    wordsAt_entails_memRegion (authWordsList g) (stA + 400#64) 48 rfl
  have h448 : ((stA + 448#64) ↦₆₄ ep) ⊢ memRegion (stA + 448#64) 8 := by
    rw [pointsTo64_eq_pointsToBytes, ← unpack64_length ep]
    exact pointsToBytes_entails_memRegion _ _
  refine Entails.trans (sepConj_mono h0 (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono h400 h448)))) ?_
  rw [show polyArrayBytes = 384 from rfl,
      ProofLib.memRegion_split' (b := stA) (n := 8) (k := 448) (b' := stA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 8#64) (n := 384) (k := 64) (b' := stA + 392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := stA + 392#64) (n := 8) (k := 56) (b' := stA + 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := stA + 400#64) (n := 48) (k := 8) (b' := stA + 448#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem ct2Sampled_outA_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (auth : Authenticator) (epoch : Epoch)
    (out : Chunked.SendEk.KeysUnsampled (spqrAuthApi F))
    (hout : out = { uc := { epoch := epoch, auth := auth } }) (g : AuthWords) :
    ((outA ↦₆₄ g.v1.w0) ∗ ((outA + 8#64) ↦₆₄ g.v1.w1) ∗ ((outA + 16#64) ↦₆₄ g.v1.w2) ∗
     ((outA + 24#64) ↦₆₄ g.v2.w0) ∗ ((outA + 32#64) ↦₆₄ g.v2.w1) ∗ ((outA + 40#64) ↦₆₄ g.v2.w2)) ∗
    relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) ∗
    ((outA + 48#64) ↦₆₄ epoch) ⊢
    chunkedKeysUnsampledAt A outA out := by
  subst hout
  unfold chunkedKeysUnsampledAt unchunkedKeysUnsampledAt
  rw [← sepConj_assoc]
  refine sepConj_mono_left ?_
  have hwords :
      ((outA ↦₆₄ g.v1.w0) ∗ ((outA + 8#64) ↦₆₄ g.v1.w1) ∗ ((outA + 16#64) ↦₆₄ g.v1.w2) ∗
       ((outA + 24#64) ↦₆₄ g.v2.w0) ∗ ((outA + 32#64) ↦₆₄ g.v2.w1) ∗ ((outA + 40#64) ↦₆₄ g.v2.w2)) =
      wordsAt outA (authWordsList g) := by
    dsimp only [authWordsList]
    conv_rhs => rw [wordsAt]
    simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
      show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl,
      show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
      show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl,
      show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl]
  rw [hwords, wordsAt_eq_pointsToBytes]
  exact relocatedHeap_recompose (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) outA

theorem pure_elim_focus {prog : Program} {pc : BitVec 64} {s : State} {φ : Prop} {P F : SepProp}
    {post : State → SepProp → Prop} (hf : P = ⌜φ⌝ ∗ F)
    (h : φ → SepWP prog pc s F post) : SepWP prog pc s P post :=
  hf ▸ SepWP.pure_elim h

/-! ## 2. Main Proof: `<Ct2Sampled>::recv_next_epoch` (`0x5fa5c`, 31 insns) -/

theorem ct2_sampled_recv_next_epoch_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr dropGluePoly16Name) (dropGluePoly16Spec A)) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct2SampledRecvNextEpochName)
      (ct2SampledRecvNextEpochSpec A F) := by
  simp only [ct2SampledRecvNextEpochSpec]
  have hdrop_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr ct2SampledRecvNextEpochName - 80800#64)
      (dropGluePoly16Spec A) := sub_ok_of_addr_eq
    (Program.fnAddr_back (d := 80800) (b := b) (X := Rust.withPanics ext)
      libsignalSessionCode_fnOff_0x5a664 libsignalSessionCode_fnOff_0x46ac4 (by decide))
    hdrop
  code_fetches libsignalSessionCode spqrStatesLeavesBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x5a664 370276 124
  dsimp only [leavesProgAtExt, ct2SampledRecvNextEpochName,
    BitVec.ofNat_eq_ofNat] at hdrop_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ct::Ct2Sampled>::recv_next_epoch" = entry
  examples_hide_fetches
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
  refine call_dropGluePoly16 hdrop_raw (s0.readReg64 (Reg.gpr 1#5) + 8#64) vecs
    (by simp only [arm64_norm]; bv_omega)
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

end CryptoVerification.SpqrV1.States.Leaves
