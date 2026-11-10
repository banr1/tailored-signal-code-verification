/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Steps
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Relocatable `[LibsignalPlacement]` Loops and Prologue

**Checked by Lean.**

Defines `unchunkedCt1SentEkReceivedSendCt2PlacedSpec` and proves `[LibsignalPlacement]`
Issue-1275 loops and Segment 1 prologue (`+0x00 → +0x88`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open DoReserveNorm

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_logFilterSym (pl : Arm64.Obj.MultiPlacement) :
    libsignalSessionLib.resolve pl lsLogFilterSym = pl.ρ lsLogFilterSym :=
  ls_resolve_data (by decide +kernel)

/-- Read-only `.rodata` + `MAX_LOG_LEVEL_FILTER` bundle required by
    `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (Block `347`) under `[LibsignalPlacement]`. -/
def unchunkedSendCt2PlacedRoAt [LibsignalPlacement] : SepProp :=
  (lsLogFilterAddr ↦₆₄ 0#64) ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)

/-- Relocatable specification of `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`
    (Block `347`) under `[LibsignalPlacement]`. -/
def unchunkedCt1SentEkReceivedSendCt2PlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) :
    Spec (UnchunkedSendCt2Ghost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧
      x.st.send_ct2 K = .ok (x.outUc, x.ct2, x.mac)⌝ ∗
      memRegion x.outA 104 ∗
      unchunkedCt1SentEkReceivedAt A x.stA x.st ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool ∗ stackAt s.sp unchunkedSendCt2Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      unchunkedCt2SentAt A x.outA x.outUc ∗
      vecU8 A (x.outA + 56#64) x.ct2 ∗
      vecU8 A (x.outA + 80#64) x.mac ∗
      memRegion x.stA 128 ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool ∗ stackAt s0.sp unchunkedSendCt2Stack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev sendCt2PlacedPostQ [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (x : UnchunkedSendCt2Ghost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev sendCt2PlacedPostQp
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (x : UnchunkedSendCt2Ghost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  sendCt2PostQp A F K 0 x s0 R

/-! ## Issue-1275 Loops under `[LibsignalPlacement]` -/

theorem swap_loop_step_last_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (basePtr : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_347).base + 0x204#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = 2046#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x228#64)
      s (((basePtr + 2046#64) ↦ₛ [b0, b1]) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + 2046#64) ↦ₛ [b1, b0]) ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf) := by
  rw [pointsToBytes_pair_split (basePtr + 2046#64) b0 b1 [], pointsToBytes_nil, sepConj_emp]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨?_, by simp only [Reg.x21, arm64_norm], ?_⟩
  · rw [pointsToBytes_pair_split (basePtr + 2046#64) b1 b0 [], pointsToBytes_nil, sepConj_emp]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx22]

theorem swap_loop_step_more_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (basePtr off : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hoff : off.toNat < 2046)
    (hpc : s.pc = (blkPl_347).base + 0x204#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x204#64)
      s (((basePtr + off) ↦₈ b0) ∗ ((basePtr + off + 1#64) ↦₈ b1) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame) ∧
        sf.readReg64 .x8 = off + 2#64 ∧
        SwapLoopSaved s sf) := by
  have hne : off + 2#64 ≠ 2048#64 := by bv_omega
  have hne_bne : (off + 2#64 != 2048#64) = true := bne_iff_ne.mpr hne
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hne_bne]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by ac_rfl, by simp only [Reg.x8, arm64_norm, hx8], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx22]

theorem swap_loop_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (basePtr : BitVec 64)
    (bs : Bytes) (off : BitVec 64) (s : State) (Frame : SepProp)
    (hne : bs ≠ [])
    (hmod : bs.length % 2 = 0)
    (hsum : off.toNat + bs.length = 2048)
    (hpc : s.pc = (blkPl_347).base + 0x204#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x228#64)
      s (((basePtr + off) ↦ₛ bs) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + off) ↦ₛ swapAdjacentPairs bs) ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf) := by
  match bs with
  | [] => exact (hne rfl).elim
  | [_] => simp at hmod
  | [b0, b1] =>
    have hoff : off = 2046#64 := by
      simp only [List.length_cons, List.length_nil] at hsum
      bv_omega
    subst hoff
    exact swap_loop_step_last_placed basePtr b0 b1 s Frame hpc hrun hx22 hx8
  | b0 :: b1 :: b2 :: rest =>
    have hlen_ge : 3 ≤ (b0 :: b1 :: b2 :: rest).length := by simp
    have hoff_lt : off.toNat < 2046 := by omega
    have hrest_ne : (b2 :: rest) ≠ [] := List.cons_ne_nil b2 rest
    have hrest_mod : (b2 :: rest).length % 2 = 0 := by
      simp only [List.length_cons] at hmod ⊢
      omega
    have hoff2_sum : (off + 2#64).toNat + (b2 :: rest).length = 2048 := by
      simp only [List.length_cons] at hsum ⊢
      have h1 : (off + 2#64).toNat = off.toNat + 2 := by bv_omega
      omega
    have hpre_eq : ((basePtr + off) ↦ₛ (b0 :: b1 :: b2 :: rest)) ∗ Frame =
        ((basePtr + off) ↦₈ b0) ∗ ((basePtr + off + 1#64) ↦₈ b1) ∗
          (((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗ Frame) := by
      rw [pointsToBytes_pair_split (basePtr + off) b0 b1 (b2 :: rest)]
      have hadd : basePtr + off + 2#64 = basePtr + (off + 2#64) := by bv_omega
      rw [hadd]
      ac_rfl
    rw [hpre_eq]
    refine Drop.seq_clean
      (mid := (blkPl_347).base + 0x204#64)
      (P_mid := ((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗
        (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame))
      (Q := fun sm => sm.readReg64 .x8 = off + 2#64 ∧ SwapLoopSaved s sm)
      ?_ ?_
    · refine SepWP.mono
        (swap_loop_step_more_placed basePtr off b0 b1 s
          (((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗ Frame)
          hoff_lt hpc hrun hx22 hx8) ?_
      rintro sm Pm _ _ ⟨hPm, hx8_sm, hsaved1⟩
      rw [hPm]
      exact ⟨Entails.of_eq (by ac_rfl), hx8_sm, hsaved1⟩
    · rintro sm hpcm hrunm ⟨hx8_sm, hsaved1⟩
      refine SepWP.mono
        (swap_loop_placed_ok basePtr (b2 :: rest) (off + 2#64) sm
          (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame)
          hrest_ne hrest_mod hoff2_sum hpcm hrunm (hsaved1.x22.trans hx22) hx8_sm) ?_
      rintro sf Pf _ _ ⟨hPf, hx21_sf, hsaved2⟩
      refine ⟨?_, hx21_sf, hsaved1.trans hsaved2⟩
      rw [hPf]
      dsimp only [swapAdjacentPairs]
      rw [pointsToBytes_pair_split (basePtr + off) b1 b0 (swapAdjacentPairs (b2 :: rest))]
      have hadd : basePtr + off + 2#64 = basePtr + (off + 2#64) := by bv_omega
      rw [hadd]
      ac_rfl

theorem scan_exit_500_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_347).base + 0x100#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x228#64)
      s ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
    by simp only [Reg.x22, Reg.x19, arm64_norm],
    by simp only [Reg.x28, arm64_norm], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

theorem scan_exit_574_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_347).base + 0x174#64)
    (hrun : s.status = .Running) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x1d8#64)
      s ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_head_step_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (ptr rem : BitVec 64) (w : BitVec 16) (s : State) (Frame : SepProp)
    (hrem_lo : 2 ≤ rem.toNat)
    (hpc : s.pc = (blkPl_347).base + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x9c#64)
      s ((ptr ↦₁₆ w) ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦₁₆ w) ∗ Frame) ∧
        sf.readReg64 .x8 = ptr ∧
        sf.readReg64 .x9 = rem ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = w.zeroExtend 64 ∧
        sf.readReg64 .x13 = s.readReg64 .x13 ∧
        sf.readReg64 .x14 = 2#64 ∧
        ScanLoopSaved s sf) := by
  have hult2 : rem.ult 2#64 = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not]
    omega
  have hne1 : (rem == 1#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  wp_step; wp_step; wp_step; wp_step
  have hpc98 : ((if (rem == 1#64) = true then (blkPl_347).base + 1064#64 else (blkPl_347).base + 152#64) : BitVec 64) =
      (blkPl_347).base + 152#64 := by simp only [hne1, Bool.false_eq_true, ↓reduceIte]
  wp_step
  refine SepWP.done (by simp only [arm64_norm, hne1]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl,
    by simp only [Reg.x8, arm64_norm, hx8],
    by simp only [Reg.x9, arm64_norm, hx9],
    by simp only [Reg.x10, arm64_norm, hx10],
    by simp only [Reg.x11, arm64_norm],
    by simp only [Reg.x12, arm64_norm],
    by simp only [Reg.x13, arm64_norm],
    by simp only [Reg.x14, arm64_norm, hx9, hx10, hult2, Bool.false_eq_true, ↓reduceIte],
    ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_continue_to_7c_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0000#16 ∨ w = 0xFFFF#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x7c#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = s.readReg64 .x9 ∧
        sf.readReg64 .x10 = s.readReg64 .x10 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x14 = s.readReg64 .x14 ∧
        ScanLoopSaved s sf) := by
  rcases hw with rfl | rfl
  · wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨rfl, by simp only [Reg.x8, arm64_norm], by simp only [Reg.x9, arm64_norm],
      by simp only [Reg.x10, arm64_norm], by simp only [Reg.x11, arm64_norm, hx11],
      by simp only [Reg.x13, arm64_norm, hx13], by simp only [Reg.x14, arm64_norm], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨rfl, by simp only [Reg.x8, arm64_norm], by simp only [Reg.x9, arm64_norm],
      by simp only [Reg.x10, arm64_norm], by simp only [Reg.x11, arm64_norm, hx11],
      by simp only [Reg.x13, arm64_norm, hx13], by simp only [Reg.x14, arm64_norm], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_7c_last_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (blkPl_347).base + 0x7c#64)
    (hrun : s.status = .Running)
    (hx9 : s.readReg64 .x9 = 2#64)
    (hx14 : s.readReg64 .x14 = 2#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x228#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
    by simp only [Reg.x22, Reg.x19, arm64_norm],
    by simp only [Reg.x28, arm64_norm], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

theorem scan_7c_more_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (ptr rem : BitVec 64) (s : State) (P : SepProp)
    (hrem_gt : 2 < rem.toNat) (hrem_hi : rem.toNat ≤ 512)
    (hpc : s.pc = (blkPl_347).base + 0x7c#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx14 : s.readReg64 .x14 = 2#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x88#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        sf.readReg64 .x8 = ptr + 2#64 ∧
        sf.readReg64 .x9 = rem - 2#64 ∧
        sf.readReg64 .x10 = s.readReg64 .x10 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x13 = s.readReg64 .x13 ∧
        ScanLoopSaved s sf) := by
  have hsub_ne : (rem - 2#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hsub_ne]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl,
    by simp only [Reg.x8, arm64_norm, hx8, hx14],
    by simp only [Reg.x9, arm64_norm, hx9, hx14],
    by simp only [Reg.x10, arm64_norm],
    by simp only [Reg.x11, arm64_norm],
    by simp only [Reg.x13, arm64_norm],
    ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_true_to_574_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x174#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        ScanLoopSaved s sf) := by
  rcases hw with rfl | rfl | rfl
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ⟨rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ⟨rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ⟨rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_false_12_fffe_to_228_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0001#16 ∨ w = 0x0002#16 ∨ w = 0xFFFE#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x228#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  rcases hw with rfl | rfl | rfl
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
      by simp only [Reg.x22, Reg.x19, arm64_norm],
      by simp only [Reg.x28, arm64_norm, hx28], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
      by simp only [Reg.x22, Reg.x19, arm64_norm],
      by simp only [Reg.x28, arm64_norm, hx28], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
      by simp only [Reg.x22, Reg.x19, arm64_norm],
      by simp only [Reg.x28, arm64_norm, hx28], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

theorem scan_weird_le511_to_500_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hle511 : w.toNat ≤ 511)
    (hw0 : w ≠ 0x0000#16) (hw1 : w ≠ 0x0001#16) (hw2 : w ≠ 0x0002#16) (hw256 : w ≠ 0x0100#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x100#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        ScanLoopSaved s sf) := by
  have hc1 : (w.zeroExtend 32).sle 511#32 = true := by
    revert hle511; bv_kernel
  have hc2 : (w.zeroExtend 32 != 0#32) = true := by
    revert hw0; bv_kernel
  have hc3 : (w.zeroExtend 32 - 1#32).ult 2#32 = false := by
    revert hw0 hw1 hw2; bv_kernel
  have hc4 : (w.zeroExtend 32 == 256#32) = false := by
    revert hw256; bv_kernel
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hc1, hc2, hc3, hc4]) (by simpa only [arm64_norm] using hrun) ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_weird_gt511_to_500_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hgt511 : ¬(w.toNat ≤ 511))
    (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16) (hwfffe : w ≠ 0xFFFE#16) (hwffff : w ≠ 0xFFFF#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x100#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        ScanLoopSaved s sf) := by
  have hc1 : (w.zeroExtend 32).sle 511#32 = false := by
    revert hgt511; bv_kernel
  have hc2 : (w.zeroExtend 32).sle 65534#32 = true := by
    revert hwffff; bv_kernel
  have hc3 : (w.zeroExtend 32 == 512#32) = false := by
    revert hw512; bv_kernel
  have hc4 : (w.zeroExtend 32 == 65279#32) = false := by
    revert hwfeff; bv_kernel
  have hc5 : (w.zeroExtend 32 == 65534#32) = false := by
    revert hwfffe; bv_kernel
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hc1, hc2, hc3, hc4, hc5]) (by simpa only [arm64_norm] using hrun) ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_weird_to_500_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw0 : w ≠ 0x0000#16) (hwffff : w ≠ 0xFFFF#16)
    (hw1 : w ≠ 0x0001#16) (hw2 : w ≠ 0x0002#16) (hwfffe : w ≠ 0xFFFE#16)
    (hw256 : w ≠ 0x0100#16) (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x100#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        ScanLoopSaved s sf) := by
  by_cases hle511 : w.toNat ≤ 511
  · exact scan_weird_le511_to_500_placed w s P hle511 hw0 hw1 hw2 hw256 hpc hrun hx12
  · exact scan_weird_gt511_to_500_placed w s P hle511 hw512 hwfeff hwfffe hwffff hpc hrun hx11 hx12

theorem scan_9c_false_exit_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (Frame : SepProp)
    (hw0 : w ≠ 0x0000#16) (hwffff : w ≠ 0xFFFF#16)
    (hw256 : w ≠ 0x0100#16) (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x228#64)
      s ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  by_cases hw_le : w = 0x0001#16 ∨ w = 0x0002#16 ∨ w = 0xFFFE#16
  · exact scan_false_12_fffe_to_228_placed w s ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      hw_le hpc hrun hx11 hx12 hx28
  · push Not at hw_le
    rcases hw_le with ⟨hw1, hw2, hwfffe⟩
    refine Drop.seq_clean
      (mid := (blkPl_347).base + 0x100#64)
      (P_mid := (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (Q := fun sm => ScanLoopSaved s sm)
      ?_ ?_
    · refine SepWP.mono
        (scan_weird_to_500_placed w s ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
          hw0 hwffff hw1 hw2 hwfffe hw256 hw512 hwfeff hpc hrun hx11 hx12) ?_
      rintro sm Pm _ _ ⟨hPm, hsaved1⟩
      rw [hPm]
      exact ⟨Entails.refl _, hsaved1⟩
    · rintro sm hpcm hrunm hsaved1
      refine SepWP.mono
        (scan_exit_500_placed sm Frame hpcm hrunm (hsaved1.x28.trans hx28)) ?_
      rintro sf Pf _ _ ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved2⟩
      exact ⟨hPf, hx21_sf, hx22_sf.trans hsaved1.x19, hx28_sf, hsaved1.trans hsaved2⟩

theorem scan_9c_true_exit_placed [LibsignalPlacement] {H : String → Option (State → State)}
    (w : BitVec 16) (s : State) (Frame : SepProp)
    (hw : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16)
    (hpc : s.pc = (blkPl_347).base + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x1d8#64)
      s ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  refine Drop.seq_clean
    (mid := (blkPl_347).base + 0x174#64)
    (P_mid := (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
    (Q := fun sm => ScanLoopSaved s sm)
    ?_ ?_
  · refine SepWP.mono
      (scan_true_to_574_placed w s ((lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) hw hpc hrun hx11 hx12) ?_
    rintro sm Pm _ _ ⟨hPm, hsaved1⟩
    rw [hPm]
    exact ⟨Entails.refl _, hsaved1⟩
  · rintro sm hpcm hrunm hsaved1
    refine SepWP.mono (scan_exit_574_placed sm Frame hpcm hrunm) ?_
    rintro sf Pf _ _ ⟨hPf, hsaved2⟩
    exact ⟨hPf, hsaved1.trans hsaved2⟩

theorem scan_loop_false_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = false)
    (hpc : s.pc = (blkPl_347).base + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x228#64)
      s ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  match bs with
  | [] => exact absurd rfl hbs_ne
  | [_] => simp at hbs_mod
  | b0 :: b1 :: rest =>
    have hrem_lo : 2 ≤ rem.toNat := by
      subst hrem
      simp only [List.length_cons] at hbs_le ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    let w : BitVec 16 := (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16
    have hw_eq : w = b1 ++ b0 := issue1275_word_eq b0 b1
    rw [pointsToBytes_pair_pointsTo16 ptr b0 b1 rest, ← hw_eq, sepConj_assoc]
    refine Drop.seq_clean
      (mid := (blkPl_347).base + 0x9c#64)
      (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
      (Q := fun sm =>
        sm.readReg64 .x8 = ptr ∧
        sm.readReg64 .x9 = rem ∧
        sm.readReg64 .x10 = 2#64 ∧
        sm.readReg64 .x11 = 65534#64 ∧
        sm.readReg64 .x12 = w.zeroExtend 64 ∧
        sm.readReg64 .x13 = 65535#64 ∧
        sm.readReg64 .x14 = 2#64 ∧
        ScanLoopSaved s sm)
      ?_ ?_
    · refine SepWP.mono
        (scan_head_step_placed ptr rem w s
          (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
          hrem_lo hpc hrun hx8 hx9 hx10) ?_
      rintro sm Pm _ _ ⟨hPm, hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hsaved_m⟩
      rw [hPm]
      exact ⟨Entails.refl _, hx8_m, hx9_m, hx10_m, hx11_m.trans hx11, hx12_m, hx13_m.trans hx13, hx14_m, hsaved_m⟩
    · rintro sm hpcm hrunm ⟨hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hsaved_m⟩
      by_cases hw_cont : w = 0x0000#16 ∨ w = 0xFFFF#16
      · have hflip_rest : issue1275NeedsFlip rest = false := by
          rwa [issue1275NeedsFlip_cons_cont b0 b1 rest hw_cont] at hflip
        refine Drop.seq_clean
          (mid := (blkPl_347).base + 0x7c#64)
          (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
          (Q := fun s7c =>
            s7c.readReg64 .x8 = ptr ∧
            s7c.readReg64 .x9 = rem ∧
            s7c.readReg64 .x10 = 2#64 ∧
            s7c.readReg64 .x11 = 65534#64 ∧
            s7c.readReg64 .x13 = 65535#64 ∧
            s7c.readReg64 .x14 = 2#64 ∧
            ScanLoopSaved s s7c)
          ?_ ?_
        · refine SepWP.mono
            (scan_continue_to_7c_placed w sm
              ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
              hw_cont hpcm hrunm hx11_m hx12_m hx13_m) ?_
          rintro s7c P7c _ _ ⟨hP7c, hx8_7, hx9_7, hx10_7, hx11_7, hx13_7, hx14_7, hsaved_7⟩
          rw [hP7c]
          exact ⟨Entails.refl _, hx8_7.trans hx8_m, hx9_7.trans hx9_m, hx10_7.trans hx10_m,
            hx11_7, hx13_7, hx14_7.trans hx14_m, hsaved_m.trans hsaved_7⟩
        · rintro s7c hpc7c hrun7c ⟨hx8_7, hx9_7, hx10_7, hx11_7, hx13_7, hx14_7, hsaved_7⟩
          match rest with
          | [] =>
            have hrem2 : rem = 2#64 := by
              subst hrem; rfl
            refine SepWP.mono
              (scan_7c_last_placed s7c
                ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ []) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
                hpc7c hrun7c (hx9_7.trans hrem2) hx14_7 (hsaved_7.x28.trans hx28)) ?_
            rintro sf Pf _ _ ⟨hPf, hx21_f, hx22_f, hx28_f, hsaved_f⟩
            exact ⟨hPf, hx21_f, hx22_f.trans hsaved_7.x19, hx28_f, hsaved_7.trans hsaved_f⟩
          | [_] => simp at hbs_mod
          | b2 :: b3 :: rest' =>
            have hrest_ne : (b2 :: b3 :: rest') ≠ [] := List.cons_ne_nil _ _
            have hrest_mod : (b2 :: b3 :: rest').length % 2 = 0 := by
              simp only [List.length_cons] at hbs_mod ⊢; omega
            have hrest_le : (b2 :: b3 :: rest').length ≤ 512 := by
              simp only [List.length_cons] at hbs_le ⊢; omega
            have hrem_gt : 2 < rem.toNat := by
              subst hrem
              simp only [List.length_cons] at hbs_le ⊢
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              omega
            have hrem_hi : rem.toNat ≤ 512 := by
              subst hrem
              simp only [List.length_cons] at hbs_le ⊢
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              omega
            have hrem_sub : rem - 2#64 = BitVec.ofNat 64 (b2 :: b3 :: rest').length := by
              subst hrem
              simp only [List.length_cons] at hbs_le ⊢
              bv_omega
            refine Drop.seq_clean
              (mid := (blkPl_347).base + 0x88#64)
              (P_mid := ((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ Frame))
              (Q := fun s88 =>
                s88.readReg64 .x8 = ptr + 2#64 ∧
                s88.readReg64 .x9 = rem - 2#64 ∧
                s88.readReg64 .x10 = 2#64 ∧
                s88.readReg64 .x11 = 65534#64 ∧
                s88.readReg64 .x13 = 65535#64 ∧
                ScanLoopSaved s s88)
              ?_ ?_
            · refine SepWP.mono
                (scan_7c_more_placed ptr rem s7c
                  ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
                  hrem_gt hrem_hi hpc7c hrun7c hx8_7 hx9_7 hx14_7) ?_
              rintro s88 P88 _ _ ⟨hP88, hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              rw [hP88]
              exact ⟨Entails.of_eq (by ac_rfl), hx8_8, hx9_8, hx10_8.trans hx10_7,
                hx11_8.trans hx11_7, hx13_8.trans hx13_7, hsaved_7.trans hsaved_8⟩
            · rintro s88 hpc88 hrun88 ⟨hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              refine SepWP.mono
                (scan_loop_false_placed_ok (ptr + 2#64) (b2 :: b3 :: rest') (rem - 2#64) s88
                  ((ptr ↦₁₆ w) ∗ Frame)
                  hrest_ne hrest_mod hrest_le hrem_sub hflip_rest hpc88 hrun88
                  hx8_8 hx9_8 hx10_8 hx11_8 hx13_8 (hsaved_8.x28.trans hx28)) ?_
              rintro sf Pf _ _ ⟨hPf, hx21_f, hx22_f, hx28_f, hsaved_f⟩
              refine ⟨?_, hx21_f, hx22_f.trans hsaved_8.x19, hx28_f, hsaved_8.trans hsaved_f⟩
              rw [hPf]
              ac_rfl
      · push Not at hw_cont
        rcases hw_cont with ⟨hw0, hwffff⟩
        have hw_not_be : ¬(w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16) :=
          issue1275NeedsFlip_cons_false_not_be b0 b1 rest hflip
        push Not at hw_not_be
        rcases hw_not_be with ⟨hw256, hw512, hwfeff⟩
        have hpre_eq : ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)) =
            ((lsLogFilterAddr ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)) := by
          ac_rfl
        conv => arg 4; rw [hpre_eq]
        refine SepWP.mono
          (scan_9c_false_exit_placed w sm ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)
            hw0 hwffff hw256 hw512 hwfeff hpcm hrunm hx11_m hx12_m (hsaved_m.x28.trans hx28)) ?_
        rintro sf Pf _ _ ⟨hPf, hx21_f, hx22_f, hx28_f, hsaved_f⟩
        refine ⟨?_, hx21_f, hx22_f.trans hsaved_m.x19, hx28_f, hsaved_m.trans hsaved_f⟩
        rw [hPf]
        ac_rfl

theorem scan_loop_true_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = true)
    (hpc : s.pc = (blkPl_347).base + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x1d8#64)
      s ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  match bs with
  | [] => exact absurd rfl hbs_ne
  | [_] => simp at hbs_mod
  | b0 :: b1 :: rest =>
    have hrem_lo : 2 ≤ rem.toNat := by
      subst hrem
      simp only [List.length_cons] at hbs_le ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    let w : BitVec 16 := (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16
    have hw_eq : w = b1 ++ b0 := issue1275_word_eq b0 b1
    rw [pointsToBytes_pair_pointsTo16 ptr b0 b1 rest, ← hw_eq, sepConj_assoc]
    refine Drop.seq_clean
      (mid := (blkPl_347).base + 0x9c#64)
      (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
      (Q := fun sm =>
        sm.readReg64 .x8 = ptr ∧
        sm.readReg64 .x9 = rem ∧
        sm.readReg64 .x10 = 2#64 ∧
        sm.readReg64 .x11 = 65534#64 ∧
        sm.readReg64 .x12 = w.zeroExtend 64 ∧
        sm.readReg64 .x13 = 65535#64 ∧
        sm.readReg64 .x14 = 2#64 ∧
        ScanLoopSaved s sm)
      ?_ ?_
    · refine SepWP.mono
        (scan_head_step_placed ptr rem w s
          (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
          hrem_lo hpc hrun hx8 hx9 hx10) ?_
      rintro sm Pm _ _ ⟨hPm, hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hsaved_m⟩
      rw [hPm]
      exact ⟨Entails.refl _, hx8_m, hx9_m, hx10_m, hx11_m.trans hx11, hx12_m, hx13_m.trans hx13, hx14_m, hsaved_m⟩
    · rintro sm hpcm hrunm ⟨hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hsaved_m⟩
      by_cases hw_cont : w = 0x0000#16 ∨ w = 0xFFFF#16
      · have hflip_rest : issue1275NeedsFlip rest = true := by
          rwa [issue1275NeedsFlip_cons_cont b0 b1 rest hw_cont] at hflip
        match rest with
        | [] =>
          dsimp only [issue1275NeedsFlip] at hflip_rest
          contradiction
        | [_] => simp at hbs_mod
        | b2 :: b3 :: rest' =>
          have hrest_ne : (b2 :: b3 :: rest') ≠ [] := List.cons_ne_nil _ _
          have hrest_mod : (b2 :: b3 :: rest').length % 2 = 0 := by
            simp only [List.length_cons] at hbs_mod ⊢; omega
          have hrest_le : (b2 :: b3 :: rest').length ≤ 512 := by
            simp only [List.length_cons] at hbs_le ⊢; omega
          have hrem_gt : 2 < rem.toNat := by
            subst hrem
            simp only [List.length_cons] at hbs_le ⊢
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            omega
          have hrem_hi : rem.toNat ≤ 512 := by
            subst hrem
            simp only [List.length_cons] at hbs_le ⊢
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            omega
          have hrem_sub : rem - 2#64 = BitVec.ofNat 64 (b2 :: b3 :: rest').length := by
            subst hrem
            simp only [List.length_cons] at hbs_le ⊢
            bv_omega
          refine Drop.seq_clean
            (mid := (blkPl_347).base + 0x7c#64)
            (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
            (Q := fun s7c =>
              s7c.readReg64 .x8 = ptr ∧
              s7c.readReg64 .x9 = rem ∧
              s7c.readReg64 .x10 = 2#64 ∧
              s7c.readReg64 .x11 = 65534#64 ∧
              s7c.readReg64 .x13 = 65535#64 ∧
              s7c.readReg64 .x14 = 2#64 ∧
              ScanLoopSaved s s7c)
            ?_ ?_
          · refine SepWP.mono
              (scan_continue_to_7c_placed w sm
                ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
                hw_cont hpcm hrunm hx11_m hx12_m hx13_m) ?_
            rintro s7c P7c _ _ ⟨hP7c, hx8_7, hx9_7, hx10_7, hx11_7, hx13_7, hx14_7, hsaved_7⟩
            rw [hP7c]
            exact ⟨Entails.refl _, hx8_7.trans hx8_m, hx9_7.trans hx9_m, hx10_7.trans hx10_m,
              hx11_7, hx13_7, hx14_7.trans hx14_m, hsaved_m.trans hsaved_7⟩
          · rintro s7c hpc7c hrun7c ⟨hx8_7, hx9_7, hx10_7, hx11_7, hx13_7, hx14_7, hsaved_7⟩
            refine Drop.seq_clean
              (mid := (blkPl_347).base + 0x88#64)
              (P_mid := ((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ Frame))
              (Q := fun s88 =>
                s88.readReg64 .x8 = ptr + 2#64 ∧
                s88.readReg64 .x9 = rem - 2#64 ∧
                s88.readReg64 .x10 = 2#64 ∧
                s88.readReg64 .x11 = 65534#64 ∧
                s88.readReg64 .x13 = 65535#64 ∧
                ScanLoopSaved s s88)
              ?_ ?_
            · refine SepWP.mono
                (scan_7c_more_placed ptr rem s7c
                  ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame))
                  hrem_gt hrem_hi hpc7c hrun7c hx8_7 hx9_7 hx14_7) ?_
              rintro s88 P88 _ _ ⟨hP88, hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              rw [hP88]
              exact ⟨Entails.of_eq (by ac_rfl), hx8_8, hx9_8, hx10_8.trans hx10_7,
                hx11_8.trans hx11_7, hx13_8.trans hx13_7, hsaved_7.trans hsaved_8⟩
            · rintro s88 hpc88 hrun88 ⟨hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              refine SepWP.mono
                (scan_loop_true_placed_ok (ptr + 2#64) (b2 :: b3 :: rest') (rem - 2#64) s88
                  ((ptr ↦₁₆ w) ∗ Frame)
                  hrest_ne hrest_mod hrest_le hrem_sub hflip_rest hpc88 hrun88
                  hx8_8 hx9_8 hx10_8 hx11_8 hx13_8) ?_
              rintro sf Pf _ _ ⟨hPf, hsaved_f⟩
              refine ⟨?_, hsaved_8.trans hsaved_f⟩
              rw [hPf]
              ac_rfl
      · have hw_be : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16 :=
          issue1275NeedsFlip_cons_true_be b0 b1 rest hflip hw_cont
        have hpre_eq : ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)) =
            ((lsLogFilterAddr ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)) := by
          ac_rfl
        conv => arg 4; rw [hpre_eq]
        refine SepWP.mono
          (scan_9c_true_exit_placed w sm ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)
            hw_be hpcm hrunm hx11_m hx12_m) ?_
        rintro sf Pf _ _ ⟨hPf, hsaved_f⟩
        refine ⟨?_, hsaved_m.trans hsaved_f⟩
        rw [hPf]
        ac_rfl

/-! ## Segment 1: Prologue (`+0x00 → +0x88`) -/

set_option maxHeartbeats 800000 in
theorem send_ct2_prologue_to_scan_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {F : ShaCompress} (A : RustAlloc)
    (outA stA : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr : BitVec 64)
    (l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hes_len : st.es.length = 2080)
    (hek_len : st.ek.length = 1152)
    (hpc : s0.pc = (blkPl_347).base)
    (hrun : s0.status = .Running)
    (hsp : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = outA)
    (hx1 : s0.readReg64 .x1 = stA) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 0x88#64)
      s0
      ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
        ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
        ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
        ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
        ((stA + 48#64) ↦₆₄ esCap) ∗ ((stA + 56#64) ↦₆₄ esPtr) ∗
        ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
        ((stA + 72#64) ↦₆₄ ekCap) ∗ ((stA + 80#64) ↦₆₄ ekPtr) ∗
        ((stA + 88#64) ↦₆₄ BitVec.ofNat 64 st.ek.length) ∗
        ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗
        ((stA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((stA + 120#64) ↦₆₄ st.epoch) ∗
        vecU8HeapAt A ct1Cap ct1Ptr st.ct1 ∗
        ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ∗
        ((s0.sp - 272#64) ↦₆₄ s64) ∗ memRegion (s0.sp - 264#64) 120 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
        Frame)
      (fun sf Pf =>
        Pf = ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
          ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
          ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
          ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
          memRegion (stA + 48#64) 80 ∗
          ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
          ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
          vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr st.ct1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          ((s0.sp - 120#64) ↦₆₄ e0) ∗
          sendCt2CalleeSavedAt s0 ∗
          Frame) ∧
        sf.sp = s0.sp - 336#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        sf.readReg64 .x8 = esPtr + 1536#64 ∧
        sf.readReg64 .x9 = 512#64 ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x19 = esPtr ∧
        sf.readReg64 .x20 = ekPtr ∧
        sf.readReg64 .x23 = outA ∧
        sf.readReg64 .x24 = stA ∧
        sf.readReg64 .x25 = mkPtr ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 st.auth.macKey.length ∧
        sf.readReg64 .x27 = 1152#64 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  simp only [wp_norm, arm64_norm] at hx0 hx1
  rw [hes_len, hek_len]
  wp_steps
  refine SepWP.fold (fold_stA_48_80 stA esCap esPtr 2080#64 ekCap ekPtr 1152#64
    ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) st.epoch) (by sep_focus) ?_
  refine SepWP.fold (fold_vecU8At_sp_304 A s0.sp ct1Cap ct1Ptr st.ct1) (by sep_focus) ?_
  refine SepWP.fold (fold_sp_272_128 s0.sp 2080#64) (by sep_focus) ?_
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  unfold sendCt2CalleeSavedAt
  refine ⟨by ac_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [State.sp, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x13, Reg.x19, Reg.x20,
      Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29,
      arm64_norm, hx0, hx1]

end CryptoVerification.SpqrV1.Unchunked
