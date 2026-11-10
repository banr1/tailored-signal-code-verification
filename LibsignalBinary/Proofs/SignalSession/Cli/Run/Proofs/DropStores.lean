/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropStores.Helpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Drop Glue Contracts for CLI `Stores` and `IdentityFiles`

Proves separation-logic drop contracts for `core::ptr::drop_glue::<IdentityFiles>` (two `Dir`
fields, stack `48 + extHookStack`) and `core::ptr::drop_glue::<Stores>` (eight `Dir` fields across
320 bytes, stack `96 + extHookStack`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli.RunProofs.Helpers

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] exists_two_pow_one exists_two_pow_eight
attribute [local wp_norm, local arm64_norm]
  sub_32_of_add_32 sub_24_of_add_32 sub_8_of_add_32
  add_32_sub_32 add_32_sub_32_assoc add_32_sub_24 add_32_sub_24_assoc
  add_32_sub_8 add_32_sub_8_assoc
  add_32_neg_32 add_32_neg_32_assoc add_32_neg_24 add_32_neg_24_assoc
  add_32_neg_8 add_32_neg_8_assoc add_one_sub_one
attribute [local simp, local wp_norm, local arm64_norm]
  reg_x0_eq reg_x1_eq reg_x2_eq reg_x19_eq reg_x20_eq reg_x21_eq reg_x22_eq
  reg_x23_eq reg_x24_eq reg_x25_eq reg_x26_eq reg_x27_eq reg_x28_eq
  reg_fp_eq reg_lr_eq

/-- Symbol name of `core::ptr::drop_glue::<signal_session::stores::Stores>`. -/
abbrev cliDropStoresName : String := "core::ptr::drop_glue::<libsignal_cli::stores::Stores>"

/-- Symbol name of `core::ptr::drop_glue::<signal_session::stores::IdentityFiles>` (shared with `KyberFiles` at `+0x78`). -/
abbrev cliDropIdentityFilesName : String :=
  "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>"

structure DropStoresGhost where
  a : BitVec 64
  g : StoresGhost

def dropStoresSpec (A : RustAlloc) (stk : Nat) : Spec DropStoresGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ storesAt A x.a x.g ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 320 ∗ A.pool ∗ stackAt s0.sp stk

structure DropDirPairGhost where
  a : BitVec 64
  d0 : DirGhost
  d1 : DirGhost

def dropDirPairSpec (A : RustAlloc) (stk : Nat) : Spec DropDirPairGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ dirAt A x.a x.d0 ∗ dirAt A (x.a + 0x28#64) x.d1 ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗ A.pool ∗ stackAt s0.sp stk

/-! ## Exact-stack proofs (`48 + extHookStack` and `96 + extHookStack`) -/

private def dropDirPairRawSpec (A : RustAlloc) : Spec DropDirPairGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗ dirRawAt A x.a x.d0.changed ∗
      dirRawAt A (x.a + 0x28#64) x.d1.changed ∗ A.pool ∗ stackAt s.sp idExactStk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 80 ∗ A.pool ∗ stackAt s0.sp idExactStk

private def dropStoresRawSpec (A : RustAlloc) : Spec DropStoresGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      dirAt A x.a x.g.identity.own ∗ dirAt A (x.a + 0x28#64) x.g.identity.peers ∗
      dirRawAt A (x.a + 0x50#64) x.g.signed.changed ∗
      dirAt A (x.a + 0x78#64) x.g.kyber.oneTime ∗ dirAt A (x.a + 0xa0#64) x.g.kyber.lastResort ∗
      dirRawAt A (x.a + 0xc8#64) x.g.oneTime.changed ∗
      dirRawAt A (x.a + 0xf0#64) x.g.sessions.changed ∗
      dirRawAt A (x.a + 0x118#64) x.g.pub.changed ∗
      A.pool ∗ stackAt s.sp storesExactStk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.a 320 ∗ A.pool ∗ stackAt s0.sp storesExactStk

set_option maxHeartbeats 1600000 in
private theorem cliDropIdentityFiles_ok_exact {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropIdentityFilesName)
      ((dropDirPairRawSpec A).inImage img) := by
  simp only [Spec.inImage, dropDirPairRawSpec]
  have hdealloc_raw := hA.dealloc_ok_at cliDropIdentityFilesName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>")];
        simp only [arm64_norm])
  have hdealloc := hdealloc_raw
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  have hloop0 := id_loop0 (img := img) (ext := ext) hdealloc_raw
  have hloop1 := id_loop1 (img := img) (ext := ext) hdealloc_raw
  code_fetches libsignalSessionCode cliDropIdentityFilesBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>")
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>")) 248
  dsimp only [tripleRatchetProgAtExt, cliDropIdentityFilesName, BitVec.ofNat_eq_ofNat]
    at hdealloc hloop0 hloop1 ⊢
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, d0, d1⟩ := x
  dsimp only at *
  subst h
  set a0 := s0.readReg64 (Reg.gpr 0#5)
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_id_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre (sepConj_mono_left (dirRawAt_expose A a0 d0.changed)) ?_
  wp_pull_exists
  rename_i cap0 ptr0
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜d0.changed.length ≤ cap0.toNat ∧ cap0.toNat * 48 < 2 ^ 63 ∧
      d0.changed.length * 48 < 2 ^ 63 ∧ ptr0 ≠ 0⌝ ∗
    ((a0 ↦₆₄ cap0) ∗ ((a0 + 8#64) ↦₆₄ ptr0) ∗
      ((a0 + 16#64) ↦₆₄ BitVec.ofNat 64 d0.changed.length) ∗
      arrayAt (dirEntryAt A) 48 ptr0 d0.changed ∗
      (if cap0 = 0 then emp
       else A.live ptr0 (cap0.toNat * 48) 8 ∗
         memRegion (ptr0 + BitVec.ofNat 64 (d0.changed.length * 48))
           ((cap0.toNat - d0.changed.length) * 48)) ∗
      memRegion (a0 + 24#64) 16 ∗ dirRawAt A (a0 + 0x28#64) d1.changed ∗
      A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ _) ∗ ((s0.sp - 40#64) ↦₆₄ _) ∗
      ((s0.sp - 32#64) ↦₆₄ _) ∗ ((s0.sp - 24#64) ↦₆₄ _) ∗
      ((s0.sp - 16#64) ↦₆₄ _) ∗ ((s0.sp - 8#64) ↦₆₄ _)) by ac_rfl)) ?_
  refine SepWP.pure_elim ?_
  rintro ⟨hlen0_le, hcap0_lt, hlen0_lt, hptr0_ne⟩
  refine seq_cleanX (mid := entry + bv% (120))
    (P_mid := memRegion a0 40 ∗ dirRawAt A (a0 + 0x28#64) d1.changed ∗
      A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = a0)
    h_2 h_1 ?_ ?_
  · refine seq_cleanX (mid := entry + bv% (92))
      (P_mid := (a0 ↦₆₄ cap0) ∗ ((a0 + 8#64) ↦₆₄ ptr0) ∗
        ((a0 + 16#64) ↦₆₄ BitVec.ofNat 64 d0.changed.length) ∗
        memRegion ptr0 (d0.changed.length * 48) ∗
        (if cap0 = 0 then emp
         else A.live ptr0 (cap0.toNat * 48) 8 ∗
           memRegion (ptr0 + BitVec.ofNat 64 (d0.changed.length * 48))
             ((cap0.toNat - d0.changed.length) * 48)) ∗
        memRegion (a0 + 24#64) 16 ∗ dirRawAt A (a0 + 0x28#64) d1.changed ∗
        A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = a0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr0)
      h_2 h_1 ?_ ?_
    · cases hc0 : d0.changed with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        wp_steps
        try wp_done
      | cons hd tl =>
        rw [hc0] at hlen0_lt
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        refine seq_callInvX (mid_pc := entry + bv% (48)) h_2 h_1 ?_
        wp_steps
        refine SepWP.done rfl (by assumption) fun hfrozen_p hsym_p => ?_
        have hpre_eq :
            ((a0 ↦₆₄ cap0) ∗ ((a0 + 8#64) ↦₆₄ ptr0) ∗
              ((a0 + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A) 48 ptr0 (hd :: tl) ∗
              (if cap0 = 0 then emp
               else A.live ptr0 (cap0.toNat * 48) 8 ∗
                 memRegion (ptr0 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap0.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (a0 + 24#64) 16 ∗ dirRawAt A (a0 + 0x28#64) d1.changed ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
            (arrayAt (dirEntryAt A) 48 ptr0 (hd :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              ((a0 ↦₆₄ cap0) ∗ ((a0 + 8#64) ↦₆₄ ptr0) ∗
                ((a0 + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap0 = 0 then emp
                 else A.live ptr0 (cap0.toNat * 48) 8 ∗
                   memRegion (ptr0 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap0.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (a0 + 24#64) 16 ∗ dirRawAt A (a0 + 0x28#64) d1.changed ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) := by
          ac_rfl
        rw [hpre_eq]
        refine SepWP.mono
          (hloop0 s0 (s0.sp - 48#64) a0 ptr0 hfsp_align (hd :: tl) ptr0 _ _
            (List.cons_ne_nil _ _) hlen0_lt rfl (by assumption) hfrozen_p hsym_p
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            rfl rfl rfl rfl) ?_
        intro sm Pm _ _ hh
        exact ⟨Entails.trans hh.1 (Entails.of_eq (by ac_rfl)), hh.2⟩
    · intro sm hpcm hrunm hfrozenm hsymm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken A a0 cap0 ptr0 d0.changed.length hlen0_le hcap0_lt _) ?_
      by_cases hcap0 : (cap0 == 0#64) = true <;>
        simp only [hcap0, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40 a0 cap0
              (dirRawAt A (a0 + 0x28#64) d1.changed ∗ A.pool ∗
                stackAt (s0.sp - 48#64) extHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
            (by ac_rfl)) ?_
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap0
        have hsz_pos : 0 < cap0.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        wp_steps
        rw [mul_48_reg hcap0_lt]
        wp_call hdealloc (ptr0, cap0.toNat * 48, 8)
        refine SepWP.weaken_pre
          (weaken_perm
            (word_and_32_rest_entails_40 a0 cap0
              (dirRawAt A (a0 + 0x28#64) d1.changed ∗ A.pool ∗
                stackAt (s0.sp - 48#64) extHookStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
            (by try rw [hsp_m]; ac_rfl)) ?_
        try wp_done
  ·
    intro s1 hpc1 hrun1 hfrozen1 hsym1
      ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    have ho1_8 : (a0 + 0x28#64) + 8#64 = a0 + 48#64 := by bv_omega
    have ho1_16 : (a0 + 0x28#64) + 16#64 = a0 + 56#64 := by bv_omega
    have ho1_24 : (a0 + 0x28#64) + 24#64 = a0 + 64#64 := by bv_omega
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left
        (dirRawAt_expose_off A a0 0x28#64 48#64 56#64 64#64
          ho1_8 ho1_16 ho1_24 d1.changed))) ?_
    wp_pull_exists
    rename_i cap1 ptr1
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜d1.changed.length ≤ cap1.toNat ∧ cap1.toNat * 48 < 2 ^ 63 ∧
        d1.changed.length * 48 < 2 ^ 63 ∧ ptr1 ≠ 0⌝ ∗
      (((a0 + 40#64) ↦₆₄ cap1) ∗ ((a0 + 48#64) ↦₆₄ ptr1) ∗
        ((a0 + 56#64) ↦₆₄ BitVec.ofNat 64 d1.changed.length) ∗
        arrayAt (dirEntryAt A) 48 ptr1 d1.changed ∗
        (if cap1 = 0 then emp
         else A.live ptr1 (cap1.toNat * 48) 8 ∗
           memRegion (ptr1 + BitVec.ofNat 64 (d1.changed.length * 48))
             ((cap1.toNat - d1.changed.length) * 48)) ∗
        memRegion (a0 + 64#64) 16 ∗ memRegion a0 40 ∗
        A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
    refine SepWP.pure_elim ?_
    rintro ⟨hlen1_le, hcap1_lt, hlen1_lt, hptr1_ne⟩
    refine seq_cleanX (mid := entry + bv% (192))
      (P_mid := ((a0 + 40#64) ↦₆₄ cap1) ∗ ((a0 + 48#64) ↦₆₄ ptr1) ∗
        ((a0 + 56#64) ↦₆₄ BitVec.ofNat 64 d1.changed.length) ∗
        memRegion ptr1 (d1.changed.length * 48) ∗
        (if cap1 = 0 then emp
         else A.live ptr1 (cap1.toNat * 48) 8 ∗
           memRegion (ptr1 + BitVec.ofNat 64 (d1.changed.length * 48))
             ((cap1.toNat - d1.changed.length) * 48)) ∗
        memRegion (a0 + 64#64) 16 ∗ memRegion a0 40 ∗
        A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = a0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr1)
      hfrozen1 hsym1 ?_ ?_
    · cases hc1 : d1.changed with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
        wp_steps
        try wp_done
      | cons hd tl =>
        rw [hc1] at hlen1_lt
        have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
        refine seq_callInvX (mid_pc := entry + bv% (148)) hfrozen1 hsym1 ?_
        wp_steps
        refine SepWP.done rfl (by assumption) fun hfrozen_p hsym_p => ?_
        have hpre_eq :
            (((a0 + 40#64) ↦₆₄ cap1) ∗ ((a0 + 48#64) ↦₆₄ ptr1) ∗
              ((a0 + 56#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
              arrayAt (dirEntryAt A) 48 ptr1 (hd :: tl) ∗
              (if cap1 = 0 then emp
               else A.live ptr1 (cap1.toNat * 48) 8 ∗
                 memRegion (ptr1 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                   ((cap1.toNat - (hd :: tl).length) * 48)) ∗
              memRegion (a0 + 64#64) 16 ∗ memRegion a0 40 ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
              ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
              ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
              ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) =
            (arrayAt (dirEntryAt A) 48 ptr1 (hd :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
              (((a0 + 40#64) ↦₆₄ cap1) ∗ ((a0 + 48#64) ↦₆₄ ptr1) ∗
                ((a0 + 56#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if cap1 = 0 then emp
                 else A.live ptr1 (cap1.toNat * 48) 8 ∗
                   memRegion (ptr1 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap1.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (a0 + 64#64) 16 ∗ memRegion a0 40 ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) := by
          ac_rfl
        rw [hpre_eq]
        refine SepWP.mono
          (hloop1 s0 (s0.sp - 48#64) a0 ptr1 hfsp_align (hd :: tl) ptr1 _ _
            (List.cons_ne_nil _ _) hlen1_lt rfl (by assumption) hfrozen_p hsym_p
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
            hx19_1 rfl rfl rfl) ?_
        intro sm Pm _ _ hh
        exact ⟨Entails.trans hh.1 (Entails.of_eq (by ac_rfl)), hh.2⟩
    · intro sm hpcm hrunm hfrozenm hsymm
        ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
      refine SepWP.weaken_pre
        (post_dir_loop_weaken_off A a0 0x28#64 48#64 56#64 64#64 cap1 ptr1
          ho1_8 ho1_16 ho1_24 d1.changed.length hlen1_le hcap1_lt _) ?_
      by_cases hcap1 : (cap1 == 0#64) = true <;>
        simp only [hcap1, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre
          (weaken_perm
            (id_cap0_ret_weaken a0 cap1 A.pool s0.sp
              (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
              (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
              (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
            (by ac_rfl)) ?_
        try wp_done
      · have hcap_pos := pos_of_beq_zero_false hcap1
        have hsz_pos : 0 < cap1.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
        wp_steps
        rw [mul_48_reg hcap1_lt]
        refine SepWP.weaken_pre
          (weaken_perm
            (id_tail_dealloc_pre_weaken a0 cap1
              (A.live ptr1 (cap1.toNat * 48) 8 ∗ memRegion ptr1 (cap1.toNat * 48))
              A.pool s0.sp
              (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
              (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
              (s0.readReg64 (Reg.gpr 20#5))
              (s0.readReg64 (Reg.gpr 19#5)))
            (by ac_rfl)) ?_
        wp_call hdealloc (ptr1, cap1.toNat * 48, 8)
        refine SepWP.weaken_pre (weaken_perm (id_tail_dealloc_post a0 A.pool s0.sp) (by ac_rfl)) ?_
        try wp_done

theorem cliDropIdentityFiles_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 48 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropIdentityFilesName)
      ((dropDirPairSpec A stk).inImage img) := by
  have hexact := cliDropIdentityFiles_ok_exact hA
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - idExactStk)
  have hsplit : stackAt s0.sp stk = stackAt s0.sp idExactStk ∗ F :=
    Put.Helpers.stackAt_sub_split hstk hstk64 s0.sp
  have hpre1 : s0.mem ⊨
      ((dropDirPairRawSpec A).inImage img).pre x s0 ∗
        ((roPathAt x.d0.path ∗ roPathAt x.d1.path) ∗ (F ∗ R)) := by
    simp only [Spec.inImage, dropDirPairSpec, dropDirPairRawSpec] at hpre ⊢
    rw [hsplit] at hpre
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (Entails.of_eq (show _ =
        (dirAt A x.a x.d0 ∗ dirAt A (x.a + 0x28#64) x.d1) ∗
          (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗ ⌜s0.readReg64 .x0 = x.a⌝ ∗
            A.pool ∗ stackAt s0.sp idExactStk ∗ F ∗ R) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (id_entry_raw_ro A x.a x.d0 x.d1)) ?_
    exact Entails.of_eq (by ac_rfl)
  have hpre2 : s0.mem ⊨ ((dropDirPairRawSpec A).inImage img).pre x s0 ∗ (F ∗ R) :=
    Satisfies.drop_mid hpre1
  refine reaches_pc_mono
    (subroutine_ok_apply_full hexact x (F ∗ R) hpc hrun hpre2 hsp) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  simp only [Spec.inImage, dropDirPairSpec, dropDirPairRawSpec] at hpost ⊢
  rw [hsplit]
  convert hpost using 1
  ac_rfl

set_option maxHeartbeats 1600000 in
private theorem cliDropStores_ok_exact {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropStoresName)
      ((dropStoresRawSpec A).inImage img) := by
  simp only [Spec.inImage, dropStoresRawSpec]
  have hdealloc_raw := hA.dealloc_ok_at cliDropStoresName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "core::ptr::drop_glue::<libsignal_cli::stores::Stores>"))
    (by rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_cli::stores::Stores>")];
        simp only [arm64_norm])
  have hdealloc := hdealloc_raw
  simp only [Spec.inImage, rustDeallocExternSpecWithStack, LayoutOk] at hdealloc
  have hid_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropStoresName +
        (0#64 - BitVec.ofNat 64
          (ls_rel% "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>"
            "core::ptr::drop_glue::<libsignal_cli::stores::Stores>")))
      ((dropDirPairSpec A idExactStk).inImage img) := by
    rw [fnAddr_identity_from_stores]
    exact cliDropIdentityFiles_ok hA idExactStk (le_refl _) (by decide)
  have hid := hid_raw
  simp only [Spec.inImage, dropDirPairSpec] at hid
  have hsigned := stores_dir_signed (img := img) (ext := ext) hdealloc_raw
  have honetime := stores_dir_onetime (img := img) (ext := ext) hdealloc_raw
  have hsessions := stores_dir_sessions (img := img) (ext := ext) hdealloc_raw
  have hloop3 := stores_loop3 (img := img) (ext := ext) hdealloc_raw
  code_fetches libsignalSessionCode cliDropStoresBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_cli::stores::Stores>")
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_cli::stores::Stores>")) 460
  dsimp only [tripleRatchetProgAtExt, cliDropStoresName, BitVec.ofNat_eq_ofNat]
    at hdealloc hid hsigned honetime hsessions hloop3 ⊢
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_cli::stores::Stores>" = entry
  simp only [arm64_norm] at hid
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, g⟩ := x
  dsimp only at *
  subst h
  set a0 := s0.readReg64 (Reg.gpr 0#5)
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_stores_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine seq_cleanX (mid := entry + bv% (24))
    (P_mid := memRegion a0 80 ∗
      dirRawAt A (a0 + 0x50#64) g.signed.changed ∗
      dirAt A (a0 + 0x78#64) g.kyber.oneTime ∗ dirAt A (a0 + 0xa0#64) g.kyber.lastResort ∗
      dirRawAt A (a0 + 0xc8#64) g.oneTime.changed ∗
      dirRawAt A (a0 + 0xf0#64) g.sessions.changed ∗
      dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
      A.pool ∗ stackAt (s0.sp - 48#64) idExactStk ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = a0)
    h_2 h_1 ?_ ?_
  · refine seq_cleanX (mid := entry + bv% (20))
      (P_mid := dirAt A a0 g.identity.own ∗ dirAt A (a0 + 0x28#64) g.identity.peers ∗
        dirRawAt A (a0 + 0x50#64) g.signed.changed ∗
        dirAt A (a0 + 0x78#64) g.kyber.oneTime ∗ dirAt A (a0 + 0xa0#64) g.kyber.lastResort ∗
        dirRawAt A (a0 + 0xc8#64) g.oneTime.changed ∗
        dirRawAt A (a0 + 0xf0#64) g.sessions.changed ∗
        dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
        A.pool ∗ stackAt (s0.sp - 48#64) idExactStk ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = a0 ∧ sm.readReg64 (Reg.gpr 0#5) = a0)
      h_2 h_1 ?_ ?_
    · wp_steps
      try wp_done
    · intro sc hpcc hrunc hfrozenc hsymc
        ⟨⟨hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩,
          hx19_c, hx0_c⟩
      wp_call hid (DropDirPairGhost.mk a0 g.identity.own g.identity.peers)
      try rw [hsp_c]
      try wp_done
  ·
    intro s1 hpc1 hrun1 hfrozen1 hsym1 hq1
    rw [stackAt_id_split_bottom (s0.sp - 48#64)]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      dirRawAt A (a0 + bv% (80)) g.signed.changed ∗ A.pool ∗
      stackAt (s0.sp - 48#64) extHookStack ∗
      (memRegion a0 80 ∗
        dirAt A (a0 + 0x78#64) g.kyber.oneTime ∗ dirAt A (a0 + 0xa0#64) g.kyber.lastResort ∗
        dirRawAt A (a0 + 0xc8#64) g.oneTime.changed ∗
        dirRawAt A (a0 + 0xf0#64) g.sessions.changed ∗
        dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
        memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
    refine seq_cleanX (mid := entry + bv% (124))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = a0)
      hfrozen1 hsym1
      (hsigned s0 (s0.sp - 48#64) a0 hfsp_align g.signed.changed s1 _
        hpc1 hrun1 hfrozen1 hsym1 hq1.1 hq1.2) ?_
    intro s2 hpc2 hrun2 hfrozen2 hsym2
      ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    have ha0_a0 : a0 + 0xa0#64 = (a0 + 0x78#64) + 0x28#64 := by bv_omega
    rw [ha0_a0]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      dirAt A (a0 + 0x78#64) g.kyber.oneTime ∗
      dirAt A ((a0 + 0x78#64) + 0x28#64) g.kyber.lastResort ∗
      A.pool ∗ (memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗ stackAt (s0.sp - 48#64) extHookStack) ∗
      (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗
        dirRawAt A (a0 + 0xc8#64) g.oneTime.changed ∗
        dirRawAt A (a0 + 0xf0#64) g.sessions.changed ∗
        dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
    rw [← stackAt_id_split_bottom (s0.sp - 48#64)]
    refine seq_cleanX (mid := entry + bv% (132))
      (P_mid := memRegion (a0 + 0x78#64) 80 ∗ A.pool ∗ stackAt (s0.sp - 48#64) idExactStk ∗
        (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗
          dirRawAt A (a0 + 0xc8#64) g.oneTime.changed ∗
          dirRawAt A (a0 + 0xf0#64) g.sessions.changed ∗
          dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = a0)
      hfrozen2 hsym2 ?_ ?_
    · wp_steps
      wp_call hid (DropDirPairGhost.mk (a0 + 0x78#64) g.kyber.oneTime g.kyber.lastResort)
      try rw [hsp_2]
      try wp_done
    ·
      intro s3 hpc3 hrun3 hfrozen3 hsym3 hq3
      rw [stackAt_id_split_bottom (s0.sp - 48#64)]
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A (a0 + bv% (200)) g.oneTime.changed ∗ A.pool ∗
        stackAt (s0.sp - 48#64) extHookStack ∗
        (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗ memRegion (a0 + 0x78#64) 80 ∗
          dirRawAt A (a0 + 0xf0#64) g.sessions.changed ∗
          dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
          memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
      refine seq_cleanX (mid := entry + bv% (232))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = a0)
        hfrozen3 hsym3
        (honetime s0 (s0.sp - 48#64) a0 hfsp_align g.oneTime.changed s3 _
          hpc3 hrun3 hfrozen3 hsym3 hq3.1 hq3.2) ?_
      intro s4 hpc4 hrun4 hfrozen4 hsym4 hq4
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A (a0 + bv% (240)) g.sessions.changed ∗ A.pool ∗
        stackAt (s0.sp - 48#64) extHookStack ∗
        (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗ memRegion (a0 + 0x78#64) 80 ∗
          memRegion (a0 + 0xc8#64) 40 ∗
          dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
          memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
      refine seq_cleanX (mid := entry + bv% (332))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 (Reg.gpr 19#5) = a0)
        hfrozen4 hsym4
        (hsessions s0 (s0.sp - 48#64) a0 hfsp_align g.sessions.changed s4 _
          hpc4 hrun4 hfrozen4 hsym4 hq4.1 hq4.2) ?_
      intro s5 hpc5 hrun5 hfrozen5 hsym5
        ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
      have ho7_8 : (a0 + 0x118#64) + 8#64 = a0 + 288#64 := by bv_omega
      have ho7_16 : (a0 + 0x118#64) + 16#64 = a0 + 296#64 := by bv_omega
      have ho7_24 : (a0 + 0x118#64) + 24#64 = a0 + 304#64 := by bv_omega
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        dirRawAt A (a0 + 0x118#64) g.pub.changed ∗
        (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗ memRegion (a0 + 0x78#64) 80 ∗
          memRegion (a0 + 0xc8#64) 40 ∗ memRegion (a0 + 0xf0#64) 40 ∗
          A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
          stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) by ac_rfl)) ?_
      refine SepWP.weaken_pre
        (sepConj_mono_left
          (dirRawAt_expose_off A a0 0x118#64 288#64 296#64 304#64
            ho7_8 ho7_16 ho7_24 g.pub.changed)) ?_
      wp_pull_exists
      rename_i cap7 ptr7
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ⌜g.pub.changed.length ≤ cap7.toNat ∧ cap7.toNat * 48 < 2 ^ 63 ∧
          g.pub.changed.length * 48 < 2 ^ 63 ∧ ptr7 ≠ 0⌝ ∗
        (((a0 + 280#64) ↦₆₄ cap7) ∗ ((a0 + 288#64) ↦₆₄ ptr7) ∗
          ((a0 + 296#64) ↦₆₄ BitVec.ofNat 64 g.pub.changed.length) ∗
          arrayAt (dirEntryAt A) 48 ptr7 g.pub.changed ∗
          (if cap7 = 0 then emp
           else A.live ptr7 (cap7.toNat * 48) 8 ∗
             memRegion (ptr7 + BitVec.ofNat 64 (g.pub.changed.length * 48))
               ((cap7.toNat - g.pub.changed.length) * 48)) ∗
          memRegion (a0 + 304#64) 16 ∗
          (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗ memRegion (a0 + 0x78#64) 80 ∗
            memRegion (a0 + 0xc8#64) 40 ∗ memRegion (a0 + 0xf0#64) 40 ∗
            A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) by ac_rfl)) ?_
      refine SepWP.pure_elim ?_
      rintro ⟨hlen7_le, hcap7_lt, hlen7_lt, hptr7_ne⟩
      refine seq_cleanX (mid := entry + bv% (404))
        (P_mid := ((a0 + 280#64) ↦₆₄ cap7) ∗ ((a0 + 288#64) ↦₆₄ ptr7) ∗
          ((a0 + 296#64) ↦₆₄ BitVec.ofNat 64 g.pub.changed.length) ∗
          memRegion ptr7 (g.pub.changed.length * 48) ∗
          (if cap7 = 0 then emp
           else A.live ptr7 (cap7.toNat * 48) 8 ∗
             memRegion (ptr7 + BitVec.ofNat 64 (g.pub.changed.length * 48))
               ((cap7.toNat - g.pub.changed.length) * 48)) ∗
          memRegion (a0 + 304#64) 16 ∗
          (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗ memRegion (a0 + 0x78#64) 80 ∗
            memRegion (a0 + 0xc8#64) 40 ∗ memRegion (a0 + 0xf0#64) 40 ∗
            A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
            stackAt (s0.sp - 48#64) extHookStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 (Reg.gpr 19#5) = a0 ∧ sm.readReg64 (Reg.gpr 20#5) = ptr7)
        hfrozen5 hsym5 ?_ ?_
      · cases hc7 : g.pub.changed with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
          wp_steps
          try wp_done
        | cons hd tl =>
          rw [hc7] at hlen7_lt
          have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) (by omega)
          refine seq_callInvX (mid_pc := entry + bv% (360)) hfrozen5 hsym5 ?_
          wp_steps
          refine SepWP.done rfl (by assumption) fun hfrozen_p hsym_p => ?_
          have hpre_eq :
              (((a0 + 280#64) ↦₆₄ cap7) ∗ ((a0 + 288#64) ↦₆₄ ptr7) ∗
                ((a0 + 296#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                arrayAt (dirEntryAt A) 48 ptr7 (hd :: tl) ∗
                (if cap7 = 0 then emp
                 else A.live ptr7 (cap7.toNat * 48) 8 ∗
                   memRegion (ptr7 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                     ((cap7.toNat - (hd :: tl).length) * 48)) ∗
                memRegion (a0 + 304#64) 16 ∗
                (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗ memRegion (a0 + 0x78#64) 80 ∗
                  memRegion (a0 + 0xc8#64) 40 ∗ memRegion (a0 + 0xf0#64) 40 ∗
                  A.pool ∗ memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
                  stackAt (s0.sp - 48#64) extHookStack ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) =
              (arrayAt (dirEntryAt A) 48 ptr7 (hd :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) extHookStack ∗
                (((a0 + 280#64) ↦₆₄ cap7) ∗ ((a0 + 288#64) ↦₆₄ ptr7) ∗
                  ((a0 + 296#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                  (if cap7 = 0 then emp
                   else A.live ptr7 (cap7.toNat * 48) 8 ∗
                     memRegion (ptr7 + BitVec.ofNat 64 ((hd :: tl).length * 48))
                       ((cap7.toNat - (hd :: tl).length) * 48)) ∗
                  memRegion (a0 + 304#64) 16 ∗
                  (memRegion a0 80 ∗ memRegion (a0 + 0x50#64) 40 ∗ memRegion (a0 + 0x78#64) 80 ∗
                    memRegion (a0 + 0xc8#64) 40 ∗ memRegion (a0 + 0xf0#64) 40 ∗
                    memRegion ((s0.sp - 48#64) - 16432#64) 48 ∗
                    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
                    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
                    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
                    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
                    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))) := by
            ac_rfl
          rw [hpre_eq]
          refine SepWP.mono
            (hloop3 s0 (s0.sp - 48#64) a0 ptr7 hfsp_align (hd :: tl) ptr7 _ _
              (List.cons_ne_nil _ _) hlen7_lt rfl (by assumption) hfrozen_p hsym_p
              ⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩
              hx19_5 rfl rfl rfl) ?_
          intro sm Pm _ _ hh
          exact ⟨Entails.trans hh.1 (Entails.of_eq (by ac_rfl)), hh.2⟩
      · intro sm hpcm hrunm hfrozenm hsymm
          ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
            hx19_m, hx20_m⟩
        refine SepWP.weaken_pre
          (post_dir_loop_weaken_off A a0 0x118#64 288#64 296#64 304#64 cap7 ptr7
            ho7_8 ho7_16 ho7_24 g.pub.changed.length hlen7_le hcap7_lt _) ?_
        by_cases hcap7 : (cap7 == 0#64) = true <;>
          simp only [hcap7, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre
            (weaken_perm
              (stores_cap0_ret_weaken a0 cap7 A.pool s0.sp
                (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
                (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
                (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
              (by ac_rfl)) ?_
          try wp_done
        · have hcap_pos := pos_of_beq_zero_false hcap7
          have hsz_pos : 0 < cap7.toNat * 48 := Nat.mul_pos hcap_pos (by decide)
          wp_steps
          rw [mul_48_reg hcap7_lt]
          refine SepWP.weaken_pre
            (weaken_perm
              (stores_tail_dealloc_pre_weaken a0 cap7
                (A.live ptr7 (cap7.toNat * 48) 8 ∗ memRegion ptr7 (cap7.toNat * 48))
                A.pool s0.sp
                (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
                (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
                (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
              (by ac_rfl)) ?_
          wp_call hdealloc (ptr7, cap7.toNat * 48, 8)
          refine SepWP.weaken_pre (weaken_perm (stores_tail_dealloc_post a0 A.pool s0.sp) (by ac_rfl)) ?_
          try wp_done

/-! ## Parameterized-stack contract -/

theorem cliDropStores_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropStoresName)
      ((dropStoresSpec A stk).inImage img) := by
  have hexact := cliDropStores_ok_exact hA
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  let F : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - storesExactStk)
  have hsplit : stackAt s0.sp stk = stackAt s0.sp storesExactStk ∗ F :=
    Put.Helpers.stackAt_sub_split hstk hstk64 s0.sp
  have hpre1 : s0.mem ⊨
      ((dropStoresRawSpec A).inImage img).pre x s0 ∗
        ((roPathAt x.g.signed.path ∗ roPathAt x.g.oneTime.path ∗
          roPathAt x.g.sessions.path ∗ roPathAt x.g.pub.path) ∗ (F ∗ R)) := by
    simp only [Spec.inImage, dropStoresSpec, dropStoresRawSpec] at hpre ⊢
    rw [hsplit] at hpre
    refine Satisfies.mono ?_ hpre
    refine Entails.trans (Entails.of_eq (show _ =
        storesAt A x.a x.g ∗
          (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗ ⌜s0.readReg64 .x0 = x.a⌝ ∗
            A.pool ∗ stackAt s0.sp storesExactStk ∗ F ∗ R) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (stores_entry_raw_ro A x.a x.g)) ?_
    exact Entails.of_eq (by ac_rfl)
  have hpre2 : s0.mem ⊨ ((dropStoresRawSpec A).inImage img).pre x s0 ∗ (F ∗ R) :=
    Satisfies.drop_mid hpre1
  refine reaches_pc_mono
    (subroutine_ok_apply_full hexact x (F ∗ R) hpc hrun hpre2 hsp) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  simp only [Spec.inImage, dropStoresSpec, dropStoresRawSpec] at hpost ⊢
  rw [hsplit]
  convert hpost using 1
  ac_rfl

example : libsignalSessionCode.fnOff cliDropStoresName =
    num% (ls_off% "core::ptr::drop_glue::<libsignal_cli::stores::Stores>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_cli::stores::Stores>"
example : libsignalSessionCode.fnOff cliDropIdentityFilesName =
    num% (ls_off% "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>") :=
  ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_cli::stores::IdentityFiles>"

end CryptoVerification.SignalSession.Cli.RunProofs
