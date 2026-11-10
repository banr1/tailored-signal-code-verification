/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.DecodeErrorFrom
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.From
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Slow
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre' sp_setMem_setPC_pre'
  readReg64_setPC_pre' readReg64_setMem_setPC_pre'
  readReg32_setPC_pre' readReg32_setMem_setPC_pre'
  readReg_setPC_pre' readReg_setMem_setPC_pre'
  calleeSavedVRegs_setPC_pre' calleeSavedVRegs_setMem_setPC_pre'

theorem stackAt_varintSlowX (sp : BitVec 64) :
    stackAt sp (64 + 2 * extHookStack) =
      stackAt (sp - 64#64) (2 * extHookStack) ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v8) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := ProofLib.stackAt_split_cells sp (2 * extHookStack) 8 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 8)) 8 (by decide)] at h0
  change stackAt sp (64 + 2 * extHookStack) =
    stackAt (sp - 64#64) (2 * extHookStack) ∗ memRegion (sp - 64#64) 64 at h0
  have s1 := ProofLib.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s1
  have s2 := ProofLib.memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [bv_sub_add_lit sp 56 40] at s2
  have s3 := ProofLib.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s3
  rw [h0, s1, s2, s3,
    ProofLib.memRegion_eight (sp - 64#64),
    ProofLib.memRegion_eight (sp - 16#64),
    ProofLib.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem decodeVarintSlow_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img) := by
  have hFrom := decodeErrorFrom_ok_ext_x hA
  clear hA
  unfold Spec.inImage decodeVarintSlowSpecWithStack
  simp only [stackAt_varintSlowX, sepExists_sepConj_left, sepExists_sepConj_right]
  dsimp only [tripleRatchetProgAtExt] at hFrom ⊢
  have hfn : libsignalSessionCode.fnOff varintSlowName =
      num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") :=
    varintSlow_fnOff
  have hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr varintSlowName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
          (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")))
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) := by
    have heq : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr varintSlowName +
        bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
          (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")) =
        (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr decodeErrorFromName := by
      simp only [Program.fnAddr_rebase, varintSlow_fnOff, decodeErrorFrom_fnOff]
      bv_lin
    rw [heq]
    exact hFrom
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow.varintSlowBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")) 448
  clear hfn hFrom
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr varintSlowName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨slotA, slot, ptr, bs⟩ := x
  dsimp only at *
  have hinv : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have h : bs.length < 2 ^ 64 := by assumption
  have herr : ∀ {s : State} (k : Nat),
      varintSlow bs = none →
      min 10 bs.length = k →
      StateAt s0 s (entry + bv% (76)) →
      ImgCallInv img s →
      SepWPp prog (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) (2 * extHookStack) ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) (2 * extHookStack) ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s k hnone hk ⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ hinv_s
    subst hk
    simp only [hnone]
    apply SepWPp.of_sepWP_inImage
      (mid := entry + bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
        (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>"))) hinv_s
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
    rintro ⟨hF_call, -⟩
    refine SepWPp.call_frame (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := entry + bv% (92)) hFromCall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
      (by simp only [State.spAligned, arm64_norm, hsps]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hsps]; rfl)
      (And.intro (And.intro hF_call hinv_s.2) (by decide : KindNoHeap 0x8000000000000001#64))
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm, htrs])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    apply SepWPp.of_sepWP_ret
    simp only [memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, hsps]
    apply SepWP.exists_elim; intro v_err
    wp_steps
    wp_done
  have hok : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s (entry + bv% (52)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp prog (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) (2 * extHookStack) ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) (2 * extHookStack) ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    simp only [hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  have hok9 : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s (entry + bv% (432)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp prog (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) (2 * extHookStack) ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) (2 * extHookStack) ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    simp only [hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  apply SepWPp.of_sepWP_inImage (mid := entry + bv% (20)) hinv
  wp_steps
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  intro hinv
  by_cases hbs0 : bs = []
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hbs0]
    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
    wp_steps
    conv => arg 4; rw [show (slot ↦₆₄ ptr) = (slot ↦₆₄ (ptr + BitVec.ofNat 64 0)) by simp,
      show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) =
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - 0)) by simp]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    intro hinv
    apply herr 0 (by simp [hbs0, varintSlow, varintSlowAux]) (by simp [hbs0])
    · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [CalleeSaved19_28, arm64_norm]⟩
    · exact hinv
  · obtain ⟨b0, bs1, hcons0'⟩ := List.exists_cons_of_ne_nil hbs0
    have hcons0 : ([] : List (BitVec 8)) ++ b0 :: bs1 = bs := hcons0'.symm
    clear hcons0' hbs0
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_ofNat (by rw [← hcons0]; simp) h (by decide)
    have hpts0 : (ptr ↦ₛ bs) = (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ bs1) := by
      rw [← hcons0, List.nil_append, pointsToBytes_cons]
    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (48)) hinv
    conv => arg 4; rw [hpts0]
    wp_steps
    conv => arg 4; rw [← hpts0, ofNat_sub_ofNat_of_le (k := 1) (by rw [← hcons0]; simp) h]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    intro hinv
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := getLsbD_7_of_le hb0
      apply SepWPp.of_sepWP (mid := entry + bv% (52))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      apply hok (vAcc1 b0) 1 (by rw [← hcons0]; exact varintSlow_1 b0 bs1 hb0)
      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [CalleeSaved19_28, arm64_norm]⟩,
        by simp only [arm64_norm, ← vAcc1_eq]⟩
    · have hbit0 := getLsbD_7_of_gt hb0
      apply SepWPp.of_sepWP_inImage (mid := entry + bv% (68)) hinv
      wp_steps
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      intro hinv
      by_cases hbs1 : bs1 = []
      · have hlen1 : BitVec.ofNat 64 bs.length = 1#64 := by
          rw [← hcons0, hbs1]; rfl
        apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
        wp_steps
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        intro hinv
        apply herr 1
          (by rw [← hcons0, hbs1]; exact varintSlow_none_1 b0 hb0)
          (by rw [← hcons0, hbs1]; rfl)
        · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
            by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [CalleeSaved19_28, arm64_norm]⟩
        · exact hinv
      · obtain ⟨b1, bs2, hcons1'⟩ := List.exists_cons_of_ne_nil hbs1
        have hcons1 : [b0] ++ b1 :: bs2 = bs := by rw [← hcons0, hcons1']; rfl
        clear hcons1' hbs1 hcons0
        have hlen_ne1 : BitVec.ofNat 64 bs.length ≠ 1#64 :=
          ofNat_ne_ofNat (by rw [← hcons1]; simp) h (by decide)
        have hpts1 := pointsToBytes_extract_at ptr bs [b0] bs2 b1 1 hcons1 rfl
        apply SepWPp.of_sepWP_inImage (mid := entry + bv% (136)) hinv
        conv => arg 4; rw [hpts1]
        wp_steps
        conv => arg 4; rw [← hpts1, ofNat_sub_ofNat_of_le (k := 2) (by rw [← hcons1]; simp) h]
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        intro hinv
        by_cases hb1 : b1 ≤ 0x7f#8
        · have hbit1 := getLsbD_7_of_le hb1
          apply SepWPp.of_sepWP (mid := entry + bv% (52))
          wp_steps
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          apply hok (vAcc2 b0 b1) 2 (by rw [← hcons1]; exact varintSlow_2 b0 b1 bs2 hb0 hb1)
          exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
            by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [CalleeSaved19_28, arm64_norm]⟩,
            by simp only [arm64_norm, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
        · have hbit1 := getLsbD_7_of_gt hb1
          apply SepWPp.of_sepWP_inImage (mid := entry + bv% (140)) hinv
          wp_steps
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          intro hinv
          by_cases hbs2 : bs2 = []
          · have hlen2 : BitVec.ofNat 64 bs.length = 2#64 := by
              rw [← hcons1, hbs2]; rfl
            apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
            wp_steps
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            intro hinv
            apply herr 2
              (by rw [← hcons1, hbs2]; exact varintSlow_none_2 b0 b1 hb0 hb1)
              (by rw [← hcons1, hbs2]; rfl)
            · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [CalleeSaved19_28, arm64_norm]⟩
            · exact hinv
          · obtain ⟨b2, bs3, hcons2'⟩ := List.exists_cons_of_ne_nil hbs2
            have hcons2 : [b0, b1] ++ b2 :: bs3 = bs := by rw [← hcons1, hcons2']; rfl
            clear hcons2' hbs2 hcons1
            have hlen_ne2 : BitVec.ofNat 64 bs.length ≠ 2#64 :=
              ofNat_ne_ofNat (by rw [← hcons2]; simp) h (by decide)
            have hpts2 := pointsToBytes_extract_at ptr bs [b0, b1] bs3 b2 2 hcons2 rfl
            apply SepWPp.of_sepWP_inImage (mid := entry + bv% (172)) hinv
            conv => arg 4; rw [hpts2]
            wp_steps
            conv => arg 4; rw [← hpts2, ofNat_sub_ofNat_of_le (k := 3) (by rw [← hcons2]; simp) h]
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            intro hinv
            by_cases hb2 : b2 ≤ 0x7f#8
            · have hbit2 := getLsbD_7_of_le hb2
              apply SepWPp.of_sepWP (mid := entry + bv% (52))
              wp_steps
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              apply hok (vAcc3 b0 b1 b2) 3 (by rw [← hcons2]; exact varintSlow_3 b0 b1 b2 bs3 hb0 hb1 hb2)
              exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [CalleeSaved19_28, arm64_norm]⟩,
                by simp only [arm64_norm, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
            · have hbit2 := getLsbD_7_of_gt hb2
              apply SepWPp.of_sepWP_inImage (mid := entry + bv% (176)) hinv
              wp_steps
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              intro hinv
              by_cases hbs3 : bs3 = []
              · have hlen3 : BitVec.ofNat 64 bs.length = 3#64 := by
                  rw [← hcons2, hbs3]; rfl
                apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                wp_steps
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                intro hinv
                apply herr 3
                  (by rw [← hcons2, hbs3]; exact varintSlow_none_3 b0 b1 b2 hb0 hb1 hb2)
                  (by rw [← hcons2, hbs3]; rfl)
                · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                    by simp only [arm64_norm], by simp only [arm64_norm],
                    by simp only [CalleeSaved19_28, arm64_norm]⟩
                · exact hinv
              · obtain ⟨b3, bs4, hcons3'⟩ := List.exists_cons_of_ne_nil hbs3
                have hcons3 : [b0, b1, b2] ++ b3 :: bs4 = bs := by rw [← hcons2, hcons3']; rfl
                clear hcons3' hbs3 hcons2
                have hlen_ne3 : BitVec.ofNat 64 bs.length ≠ 3#64 :=
                  ofNat_ne_ofNat (by rw [← hcons3]; simp) h (by decide)
                have hpts3 := pointsToBytes_extract_at ptr bs [b0, b1, b2] bs4 b3 3 hcons3 rfl
                apply SepWPp.of_sepWP_inImage (mid := entry + bv% (208)) hinv
                conv => arg 4; rw [hpts3]
                wp_steps
                conv => arg 4; rw [← hpts3, ofNat_sub_ofNat_of_le (k := 4) (by rw [← hcons3]; simp) h]
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                intro hinv
                by_cases hb3 : b3 ≤ 0x7f#8
                · have hbit3 := getLsbD_7_of_le hb3
                  apply SepWPp.of_sepWP (mid := entry + bv% (52))
                  wp_steps
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  apply hok (vAcc4 b0 b1 b2 b3) 4 (by rw [← hcons3]; exact varintSlow_4 b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3)
                  exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                    by simp only [arm64_norm], by simp only [arm64_norm],
                    by simp only [CalleeSaved19_28, arm64_norm]⟩,
                    by simp only [arm64_norm, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                · have hbit3 := getLsbD_7_of_gt hb3
                  apply SepWPp.of_sepWP_inImage (mid := entry + bv% (212)) hinv
                  wp_steps
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  intro hinv
                  by_cases hbs4 : bs4 = []
                  · have hlen4 : BitVec.ofNat 64 bs.length = 4#64 := by
                      rw [← hcons3, hbs4]; rfl
                    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                    wp_steps
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    intro hinv
                    apply herr 4
                      (by rw [← hcons3, hbs4]; exact varintSlow_none_4 b0 b1 b2 b3 hb0 hb1 hb2 hb3)
                      (by rw [← hcons3, hbs4]; rfl)
                    · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                        by simp only [arm64_norm], by simp only [arm64_norm],
                        by simp only [CalleeSaved19_28, arm64_norm]⟩
                    · exact hinv
                  · obtain ⟨b4, bs5, hcons4'⟩ := List.exists_cons_of_ne_nil hbs4
                    have hcons4 : [b0, b1, b2, b3] ++ b4 :: bs5 = bs := by rw [← hcons3, hcons4']; rfl
                    clear hcons4' hbs4 hcons3
                    have hlen_ne4 : BitVec.ofNat 64 bs.length ≠ 4#64 :=
                      ofNat_ne_ofNat (by rw [← hcons4]; simp) h (by decide)
                    have hpts4 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3] bs5 b4 4 hcons4 rfl
                    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (244)) hinv
                    conv => arg 4; rw [hpts4]
                    wp_steps
                    conv => arg 4; rw [← hpts4, ofNat_sub_ofNat_of_le (k := 5) (by rw [← hcons4]; simp) h]
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    intro hinv
                    by_cases hb4 : b4 ≤ 0x7f#8
                    · have hbit4 := getLsbD_7_of_le hb4
                      apply SepWPp.of_sepWP (mid := entry + bv% (52))
                      wp_steps
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      apply hok (vAcc5 b0 b1 b2 b3 b4) 5 (by rw [← hcons4]; exact varintSlow_5 b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4)
                      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                        by simp only [arm64_norm], by simp only [arm64_norm],
                        by simp only [CalleeSaved19_28, arm64_norm]⟩,
                        by simp only [arm64_norm, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                    · have hbit4 := getLsbD_7_of_gt hb4
                      apply SepWPp.of_sepWP_inImage (mid := entry + bv% (248)) hinv
                      wp_steps
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      intro hinv
                      by_cases hbs5 : bs5 = []
                      · have hlen5 : BitVec.ofNat 64 bs.length = 5#64 := by
                          rw [← hcons4, hbs5]; rfl
                        apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                        wp_steps
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        intro hinv
                        apply herr 5
                          (by rw [← hcons4, hbs5]; exact varintSlow_none_5 b0 b1 b2 b3 b4 hb0 hb1 hb2 hb3 hb4)
                          (by rw [← hcons4, hbs5]; rfl)
                        · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                            by simp only [arm64_norm], by simp only [arm64_norm],
                            by simp only [CalleeSaved19_28, arm64_norm]⟩
                        · exact hinv
                      · obtain ⟨b5, bs6, hcons5'⟩ := List.exists_cons_of_ne_nil hbs5
                        have hcons5 : [b0, b1, b2, b3, b4] ++ b5 :: bs6 = bs := by rw [← hcons4, hcons5']; rfl
                        clear hcons5' hbs5 hcons4
                        have hlen_ne5 : BitVec.ofNat 64 bs.length ≠ 5#64 :=
                          ofNat_ne_ofNat (by rw [← hcons5]; simp) h (by decide)
                        have hpts5 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4] bs6 b5 5 hcons5 rfl
                        apply SepWPp.of_sepWP_inImage (mid := entry + bv% (280)) hinv
                        conv => arg 4; rw [hpts5]
                        wp_steps
                        conv => arg 4; rw [← hpts5, ofNat_sub_ofNat_of_le (k := 6) (by rw [← hcons5]; simp) h]
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        intro hinv
                        by_cases hb5 : b5 ≤ 0x7f#8
                        · have hbit5 := getLsbD_7_of_le hb5
                          apply SepWPp.of_sepWP (mid := entry + bv% (52))
                          wp_steps
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          apply hok (vAcc6 b0 b1 b2 b3 b4 b5) 6 (by rw [← hcons5]; exact varintSlow_6 b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5)
                          exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                            by simp only [arm64_norm], by simp only [arm64_norm],
                            by simp only [CalleeSaved19_28, arm64_norm]⟩,
                            by simp only [arm64_norm, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                        · have hbit5 := getLsbD_7_of_gt hb5
                          apply SepWPp.of_sepWP_inImage (mid := entry + bv% (284)) hinv
                          wp_steps
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          intro hinv
                          by_cases hbs6 : bs6 = []
                          · have hlen6 : BitVec.ofNat 64 bs.length = 6#64 := by
                              rw [← hcons5, hbs6]; rfl
                            apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                            wp_steps
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            intro hinv
                            apply herr 6
                              (by rw [← hcons5, hbs6]; exact varintSlow_none_6 b0 b1 b2 b3 b4 b5 hb0 hb1 hb2 hb3 hb4 hb5)
                              (by rw [← hcons5, hbs6]; rfl)
                            · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                by simp only [arm64_norm], by simp only [arm64_norm],
                                by simp only [CalleeSaved19_28, arm64_norm]⟩
                            · exact hinv
                          · obtain ⟨b6, bs7, hcons6'⟩ := List.exists_cons_of_ne_nil hbs6
                            have hcons6 : [b0, b1, b2, b3, b4, b5] ++ b6 :: bs7 = bs := by rw [← hcons5, hcons6']; rfl
                            clear hcons6' hbs6 hcons5
                            have hlen_ne6 : BitVec.ofNat 64 bs.length ≠ 6#64 :=
                              ofNat_ne_ofNat (by rw [← hcons6]; simp) h (by decide)
                            have hpts6 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5] bs7 b6 6 hcons6 rfl
                            apply SepWPp.of_sepWP_inImage (mid := entry + bv% (316)) hinv
                            conv => arg 4; rw [hpts6]
                            wp_steps
                            conv => arg 4; rw [← hpts6, ofNat_sub_ofNat_of_le (k := 7) (by rw [← hcons6]; simp) h]
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            intro hinv
                            by_cases hb6 : b6 ≤ 0x7f#8
                            · have hbit6 := getLsbD_7_of_le hb6
                              apply SepWPp.of_sepWP (mid := entry + bv% (52))
                              wp_steps
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              apply hok (vAcc7 b0 b1 b2 b3 b4 b5 b6) 7 (by rw [← hcons6]; exact varintSlow_7 b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                              exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                by simp only [arm64_norm], by simp only [arm64_norm],
                                by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                by simp only [arm64_norm, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                            · have hbit6 := getLsbD_7_of_gt hb6
                              apply SepWPp.of_sepWP_inImage (mid := entry + bv% (320)) hinv
                              wp_steps
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              intro hinv
                              by_cases hbs7 : bs7 = []
                              · have hlen7 : BitVec.ofNat 64 bs.length = 7#64 := by
                                  rw [← hcons6, hbs7]; rfl
                                apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                                wp_steps
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                intro hinv
                                apply herr 7
                                  (by rw [← hcons6, hbs7]; exact varintSlow_none_7 b0 b1 b2 b3 b4 b5 b6 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                                  (by rw [← hcons6, hbs7]; rfl)
                                · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                    by simp only [arm64_norm], by simp only [arm64_norm],
                                    by simp only [CalleeSaved19_28, arm64_norm]⟩
                                · exact hinv
                              · obtain ⟨b7, bs8, hcons7'⟩ := List.exists_cons_of_ne_nil hbs7
                                have hcons7 : [b0, b1, b2, b3, b4, b5, b6] ++ b7 :: bs8 = bs := by rw [← hcons6, hcons7']; rfl
                                clear hcons7' hbs7 hcons6
                                have hlen_ne7 : BitVec.ofNat 64 bs.length ≠ 7#64 :=
                                  ofNat_ne_ofNat (by rw [← hcons7]; simp) h (by decide)
                                have hpts7 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6] bs8 b7 7 hcons7 rfl
                                apply SepWPp.of_sepWP_inImage (mid := entry + bv% (352)) hinv
                                conv => arg 4; rw [hpts7]
                                wp_steps
                                conv => arg 4; rw [← hpts7, ofNat_sub_ofNat_of_le (k := 8) (by rw [← hcons7]; simp) h]
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                intro hinv
                                by_cases hb7 : b7 ≤ 0x7f#8
                                · have hbit7 := getLsbD_7_of_le hb7
                                  apply SepWPp.of_sepWP (mid := entry + bv% (52))
                                  wp_steps
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  apply hok (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7) 8 (by rw [← hcons7]; exact varintSlow_8 b0 b1 b2 b3 b4 b5 b6 b7 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                                  exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                    by simp only [arm64_norm], by simp only [arm64_norm],
                                    by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                    by simp only [arm64_norm, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                                · have hbit7 := getLsbD_7_of_gt hb7
                                  apply SepWPp.of_sepWP_inImage (mid := entry + bv% (356)) hinv
                                  wp_steps
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  intro hinv
                                  by_cases hbs8 : bs8 = []
                                  · have hlen8 : BitVec.ofNat 64 bs.length = 8#64 := by
                                      rw [← hcons7, hbs8]; rfl
                                    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                                    wp_steps
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    intro hinv
                                    apply herr 8
                                      (by rw [← hcons7, hbs8]; exact varintSlow_none_8 b0 b1 b2 b3 b4 b5 b6 b7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                                      (by rw [← hcons7, hbs8]; rfl)
                                    · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                        by simp only [arm64_norm], by simp only [arm64_norm],
                                        by simp only [CalleeSaved19_28, arm64_norm]⟩
                                    · exact hinv
                                  · obtain ⟨b8, bs9, hcons8'⟩ := List.exists_cons_of_ne_nil hbs8
                                    have hcons8 : [b0, b1, b2, b3, b4, b5, b6, b7] ++ b8 :: bs9 = bs := by rw [← hcons7, hcons8']; rfl
                                    clear hcons8' hbs8 hcons7
                                    have hlen_ne8 : BitVec.ofNat 64 bs.length ≠ 8#64 :=
                                      ofNat_ne_ofNat (by rw [← hcons8]; simp) h (by decide)
                                    have hpts8 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7] bs9 b8 8 hcons8 rfl
                                    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (388)) hinv
                                    conv => arg 4; rw [hpts8]
                                    wp_steps
                                    conv => arg 4; rw [← hpts8, ofNat_sub_ofNat_of_le (k := 9) (by rw [← hcons8]; simp) h]
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    intro hinv
                                    by_cases hb8 : b8 ≤ 0x7f#8
                                    · have hbit8 := getLsbD_7_of_le hb8
                                      apply SepWPp.of_sepWP (mid := entry + bv% (52))
                                      wp_steps
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      apply hok (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8) 9 (by rw [← hcons8]; exact varintSlow_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                                      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                        by simp only [arm64_norm], by simp only [arm64_norm],
                                        by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                        by simp only [arm64_norm, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                                    · have hbit8 := getLsbD_7_of_gt hb8
                                      apply SepWPp.of_sepWP_inImage (mid := entry + bv% (392)) hinv
                                      wp_steps
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      intro hinv
                                      by_cases hbs9 : bs9 = []
                                      · have hlen9 : BitVec.ofNat 64 bs.length = 9#64 := by
                                          rw [← hcons8, hbs9]; rfl
                                        apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                                        wp_steps
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        intro hinv
                                        apply herr 9
                                          (by rw [← hcons8, hbs9]; exact varintSlow_none_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                                          (by rw [← hcons8, hbs9]; rfl)
                                        · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                            by simp only [arm64_norm], by simp only [arm64_norm],
                                            by simp only [CalleeSaved19_28, arm64_norm]⟩
                                        · exact hinv
                                      · obtain ⟨b9, bs10, hcons9'⟩ := List.exists_cons_of_ne_nil hbs9
                                        have hcons9 : [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ b9 :: bs10 = bs := by rw [← hcons8, hcons9']; rfl
                                        clear hcons9' hbs9 hcons8
                                        have hlen_ne9 : BitVec.ofNat 64 bs.length ≠ 9#64 :=
                                          ofNat_ne_ofNat (by rw [← hcons9]; simp) h (by decide)
                                        have hpts9 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7, b8] bs10 b9 9 hcons9 rfl
                                        apply SepWPp.of_sepWP_inImage (mid := entry + bv% (416)) hinv
                                        conv => arg 4; rw [hpts9]
                                        wp_steps
                                        conv => arg 4; rw [← hpts9, ofNat_sub_ofNat_of_le (k := 10) (by rw [← hcons9]; simp) h]
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        intro hinv
                                        by_cases hb9 : b9 ≤ 0x7f#8
                                        · have hbit9 := signExtend64_getLsbD_63_of_le hb9
                                          apply SepWPp.of_sepWP_inImage (mid := entry + bv% (424)) hinv
                                          wp_steps
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          intro hinv
                                          by_cases hb9_ovf : 2#8 ≤ b9
                                          · have hovf := byte9_hi_of_ge hb9_ovf
                                            apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                                            wp_steps
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            intro hinv
                                            apply herr 10
                                              (by rw [← hcons9]; exact varintSlow_none_10_ovf b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                                              (by rw [← hcons9]; simp)
                                            · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                                by simp only [arm64_norm], by simp only [arm64_norm],
                                                by simp only [CalleeSaved19_28, arm64_norm]⟩
                                            · exact hinv
                                          · have hovf := byte9_hi_of_lt hb9 hb9_ovf
                                            apply SepWPp.of_sepWP (mid := entry + bv% (432))
                                            wp_steps
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            apply hok9 (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 10
                                              (by rw [← hcons9]; exact varintSlow_10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                                            exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                              by simp only [arm64_norm], by simp only [arm64_norm],
                                              by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                              by simp only [arm64_norm, vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127, signExtend64_shiftLeft_63]⟩
                                        · have hbit9 := signExtend64_getLsbD_63_of_gt hb9
                                          apply SepWPp.of_sepWP_inImage (mid := entry + bv% (76)) hinv
                                          wp_steps
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          intro hinv
                                          apply herr 10
                                            (by rw [← hcons9]; exact varintSlow_none_10_gt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9)
                                            (by rw [← hcons9]; simp)
                                          · exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                              by simp only [arm64_norm], by simp only [arm64_norm],
                                              by simp only [CalleeSaved19_28, arm64_norm]⟩
                                          · exact hinv

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
