/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Libcrux Issue-1275 Loops

**Checked by Lean.**

Verifies the `swapAdjacentPairs` byte-swap loop and `issue1275NeedsFlip` halfword scan loop
inlined into `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L29b

open Lean Elab Tactic Arm64 ProofLib

/-- Layout-independent instruction-fetch helper for `[0, count)` of `send_ct2`. -/
elab "send_ct2_fetches " b:term:max ext:term:max count:num : tactic => do
  let eOff ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches CryptoVerification.libsignalSessionCode
      CryptoVerification.SpqrV1.Unchunked.unchunkedSendCt2Bin $b $ext $hfn $offLit $count))

/-- Layout-independent instruction-fetch helper for `[start, start + count)` of `send_ct2`. -/
elab "send_ct2_fetches_range " b:term:max ext:term:max start:num count:num : tactic => do
  let eOff ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"
  let hfn := mkCIdent eOff.decl
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SpqrV1.Unchunked.unchunkedSendCt2Bin $b $ext $hfn $offLit $start $count))

end CryptoVerification.SpqrV1.Layout.L29b

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L29b
open DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Registers preserved across the `swapAdjacentPairs` loop (`0x5e604..0x5e628`). -/
structure SwapLoopSaved (s0 s : State) : Prop where
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  x29 : s.readReg64 .x29 = s0.readReg64 .x29
  x30 : s.readReg64 .x30 = s0.readReg64 .x30
  sp : s.sp = s0.sp
  trace : s.trace = s0.trace
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0

theorem SwapLoopSaved.refl (s : State) : SwapLoopSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SwapLoopSaved.trans {s0 s1 s2 : State}
    (h01 : SwapLoopSaved s0 s1) (h12 : SwapLoopSaved s1 s2) : SwapLoopSaved s0 s2 :=
  ⟨h12.x19.trans h01.x19, h12.x20.trans h01.x20, h12.x22.trans h01.x22,
   h12.x23.trans h01.x23, h12.x24.trans h01.x24, h12.x25.trans h01.x25,
   h12.x26.trans h01.x26, h12.x27.trans h01.x27, h12.x28.trans h01.x28,
   h12.x29.trans h01.x29, h12.x30.trans h01.x30, h12.sp.trans h01.sp,
   h12.trace.trans h01.trace, h12.vregs.trans h01.vregs⟩

theorem pointsToBytes_pair_split (p : BitVec 64) (b0 b1 : BitVec 8) (rest : Bytes) :
    (p ↦ₛ (b0 :: b1 :: rest)) =
      (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦ₛ rest) := by
  rw [pointsToBytes_cons, pointsToBytes_cons]
  have h2 : (p + 1#64) + 1#64 = p + 2#64 := by bv_omega
  rw [h2]

/-- Single iteration of the `swapAdjacentPairs` loop (`0x5e604..0x5e624`) when `rest = []`
(`off = 2046#64`, so `off + 2#64 = 2048#64` and `0x5e620: b.ne` falls through to `0x5e624..0x5e628`). -/
theorem swap_loop_step_last {b : BitVec 64} {ext : String → Option (State → State)}
    (basePtr : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = 2046#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s (((basePtr + 2046#64) ↦ₛ [b0, b1]) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + 2046#64) ↦ₛ [b1, b0]) ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf) := by
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  rw [pointsToBytes_pair_split (basePtr + 2046#64) b0 b1 [], pointsToBytes_nil, sepConj_emp]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨?_, by simp only [Reg.x21, arm64_norm], ?_⟩
  · rw [pointsToBytes_pair_split (basePtr + 2046#64) b1 b0 [], pointsToBytes_nil, sepConj_emp]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx22]

/-- Single iteration of the `swapAdjacentPairs` loop (`0x5e604..0x5e620`) when `off.toNat < 2046`
(`off + 2#64 ≠ 2048#64`, so `0x5e620: b.ne` branches back to `0x5e604`). -/
theorem swap_loop_step_more {b : BitVec 64} {ext : String → Option (State → State)}
    (basePtr off : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hoff : off.toNat < 2046)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64)
      s (((basePtr + off) ↦₈ b0) ∗ ((basePtr + off + 1#64) ↦₈ b1) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame) ∧
        sf.readReg64 .x8 = off + 2#64 ∧
        SwapLoopSaved s sf) := by
  have hne : off + 2#64 ≠ 2048#64 := by bv_omega
  have hne_bne : (off + 2#64 != 2048#64) = true := bne_iff_ne.mpr hne
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hne_bne]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by ac_rfl, by simp only [Reg.x8, arm64_norm, hx8], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx22]

/-- Full `swapAdjacentPairs` loop (`0x5e604..0x5e628`) over any non-empty even-length suffix `bs`
at `basePtr + off` with `off.toNat + bs.length = 2048`. -/
theorem swap_loop_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (basePtr : BitVec 64) :
    ∀ (bs : Bytes) (off : BitVec 64) (s : State) (Frame : SepProp),
      bs ≠ [] →
      bs.length % 2 = 0 →
      off.toNat + bs.length = 2048 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64 →
      s.status = .Running →
      s.readReg64 .x22 = basePtr →
      s.readReg64 .x8 = off →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
        s (((basePtr + off) ↦ₛ bs) ∗ Frame)
        (fun sf Pf =>
          Pf = (((basePtr + off) ↦ₛ swapAdjacentPairs bs) ∗ Frame) ∧
          sf.readReg64 .x21 = 1#64 ∧
          SwapLoopSaved s sf)
  | [], _, _, _, hne, _, _, _, _, _, _ => (hne rfl).elim
  | [_], _, _, _, _, hmod, _, _, _, _, _ => by simp at hmod
  | [b0, b1], off, s, Frame, _, _, hsum, hpc, hrun, hx22, hx8 => by
    have hoff : off = 2046#64 := by
      simp only [List.length_cons, List.length_nil] at hsum
      bv_omega
    subst hoff
    exact swap_loop_step_last basePtr b0 b1 s Frame hpc hrun hx22 hx8
  | b0 :: b1 :: b2 :: rest, off, s, Frame, _, hmod, hsum, hpc, hrun, hx22, hx8 => by
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
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64)
      (P_mid := ((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗
        (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame))
      (Q := fun sm => sm.readReg64 .x8 = off + 2#64 ∧ SwapLoopSaved s sm)
      ?_ ?_
    · refine SepWP.mono
        (swap_loop_step_more basePtr off b0 b1 s
          (((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗ Frame)
          hoff_lt hpc hrun hx22 hx8) ?_
      rintro sm Pm _ _ ⟨hPm, hx8_sm, hsaved1⟩
      rw [hPm]
      exact ⟨Entails.of_eq (by ac_rfl), hx8_sm, hsaved1⟩
    · rintro sm hpcm hrunm ⟨hx8_sm, hsaved1⟩
      refine SepWP.mono
        (swap_loop_ok basePtr (b2 :: rest) (off + 2#64) sm
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

/-! ## `issue1275NeedsFlip` Halfword Scan Loop -/

/-- Registers preserved across the `issue1275NeedsFlip` scan loop (`0x5e478..0x5e588`). -/
structure ScanLoopSaved (s0 s : State) : Prop where
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  x29 : s.readReg64 .x29 = s0.readReg64 .x29
  x30 : s.readReg64 .x30 = s0.readReg64 .x30
  sp : s.sp = s0.sp
  trace : s.trace = s0.trace
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0

theorem ScanLoopSaved.refl (s : State) : ScanLoopSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ScanLoopSaved.trans {s0 s1 s2 : State}
    (h01 : ScanLoopSaved s0 s1) (h12 : ScanLoopSaved s1 s2) : ScanLoopSaved s0 s2 :=
  ⟨h12.x19.trans h01.x19, h12.x20.trans h01.x20,
   h12.x23.trans h01.x23, h12.x24.trans h01.x24, h12.x25.trans h01.x25,
   h12.x26.trans h01.x26, h12.x27.trans h01.x27, h12.x28.trans h01.x28,
   h12.x29.trans h01.x29, h12.x30.trans h01.x30, h12.sp.trans h01.sp,
   h12.trace.trans h01.trace, h12.vregs.trans h01.vregs⟩

theorem issue1275_word_eq (b0 b1 : BitVec 8) :
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = b1 ++ b0 := by
  bv_kernel

theorem adrp_500_eq (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    (((b + bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") + 256#64) &&& 18446744073709547520#64) + bv% (ls_xref% 0x59108 - 0x59000) + bv% ((ls_xref% 0x59108 0x5910c) % 4096)) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  bv_kernel

theorem adrp_574_eq (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) :
    (((b + bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") + 372#64) &&& 18446744073709547520#64) + bv% (ls_xref% 0x5917c - 0x59000) + bv% ((ls_xref% 0x5917c 0x59180) % 4096)) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  bv_kernel

theorem scan_exit_564 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x164#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
    by simp only [Reg.x22, Reg.x19, arm64_norm],
    by simp only [Reg.x28, arm64_norm], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

theorem scan_exit_500 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  have hadrp : (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      unchunkedCt1SentEkReceivedSendCt2Name + 256#64 &&&
      18446744073709547520#64) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - 0x59000)) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    rw [Program.fnAddr_rebase, unchunkedCt1SentEkReceivedSendCt2_fnOff]
    revert hb; bv_kernel
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
    by simp only [Reg.x22, Reg.x19, arm64_norm],
    by simp only [Reg.x28, arm64_norm], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

theorem scan_exit_574 {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x174#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  have hadrp : (((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      unchunkedCt1SentEkReceivedSendCt2Name + 372#64 &&&
      18446744073709547520#64) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - 0x59000)) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    rw [Program.fnAddr_rebase, unchunkedCt1SentEkReceivedSendCt2_fnOff]
    revert hb; bv_kernel
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

/-- Loop header step `0x5e488 → 0x5e49c` (`entry + 0x88#64 → entry + 0x9c#64`, 5 instructions):
checks `rem ≥ 2#64` (setting `x14 = 2#64` and not branching on `rem == 1#64`) and loads the 16-bit
halfword `w = b1 ++ b0` from `ptr` into `w12`. -/
theorem scan_head_step {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr rem : BitVec 64) (w : BitVec 16) (s : State) (Frame : SepProp)
    (hrem_lo : 2 ≤ rem.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
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
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step
  have hpc98 : ((if (rem == 1#64) = true then entry + 1064#64 else entry + 152#64) : BitVec 64) =
      entry + 152#64 := by simp only [hne1, Bool.false_eq_true, ↓reduceIte]
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

theorem scan_continue_to_7c {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0000#16 ∨ w = 0xFFFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
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
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
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

theorem scan_7c_last {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
    (hrun : s.status = .Running)
    (hx9 : s.readReg64 .x9 = 2#64)
    (hx14 : s.readReg64 .x14 = 2#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨rfl, by simp only [Reg.x21, arm64_norm],
    by simp only [Reg.x22, Reg.x19, arm64_norm],
    by simp only [Reg.x28, arm64_norm], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

theorem scan_7c_more {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr rem : BitVec 64) (s : State) (P : SepProp)
    (hrem_gt : 2 < rem.toNat) (hrem_hi : rem.toNat ≤ 512)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx14 : s.readReg64 .x14 = 2#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
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
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
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

theorem scan_true_to_574 {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x174#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
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

theorem scan_false_12_fffe_to_228 {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0001#16 ∨ w = 0x0002#16 ∨ w = 0xFFFE#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
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

theorem scan_weird_le511_to_500 {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hle511 : w.toNat ≤ 511)
    (hw0 : w ≠ 0x0000#16) (hw1 : w ≠ 0x0001#16) (hw2 : w ≠ 0x0002#16) (hw256 : w ≠ 0x0100#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
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
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hc1, hc2, hc3, hc4]) (by simpa only [arm64_norm] using hrun) ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_weird_gt511_to_500 {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hgt511 : ¬(w.toNat ≤ 511))
    (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16) (hwfffe : w ≠ 0xFFFE#16) (hwffff : w ≠ 0xFFFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
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
  send_ct2_fetches b (Rust.withPanics ext) 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" = entry
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hc1, hc2, hc3, hc4, hc5]) (by simpa only [arm64_norm] using hrun) ⟨rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

theorem scan_weird_to_500 {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw0 : w ≠ 0x0000#16) (hwffff : w ≠ 0xFFFF#16)
    (hw1 : w ≠ 0x0001#16) (hw2 : w ≠ 0x0002#16) (hwfffe : w ≠ 0xFFFE#16)
    (hw256 : w ≠ 0x0100#16) (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
      s P
      (fun sf Pf =>
        Pf = P ∧
        ScanLoopSaved s sf) := by
  by_cases hle511 : w.toNat ≤ 511
  · exact scan_weird_le511_to_500 w s P hle511 hw0 hw1 hw2 hw256 hpc hrun hx12
  · exact scan_weird_gt511_to_500 w s P hle511 hw512 hwfeff hwfffe hwffff hpc hrun hx11 hx12

theorem pointsToBytes_pair_pointsTo16 (a : BitVec 64) (b0 b1 : BitVec 8) (rest : Bytes) :
    (a ↦ₛ (b0 :: b1 :: rest)) = (a ↦₁₆ (b1 ++ b0)) ∗ ((a + 2#64) ↦ₛ rest) := by
  rw [pointsToBytes_pair_split a b0 b1 rest, ← pointsTo8_pair a b0 b1]
  ac_rfl

theorem scan_9c_false_exit {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hw0 : w ≠ 0x0000#16) (hwffff : w ≠ 0xFFFF#16)
    (hw256 : w ≠ 0x0100#16) (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  by_cases hw_le : w = 0x0001#16 ∨ w = 0x0002#16 ∨ w = 0xFFFE#16
  · exact scan_false_12_fffe_to_228 w s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      hw_le hpc hrun hx11 hx12 hx28
  · push Not at hw_le
    rcases hw_le with ⟨hw1, hw2, hwfffe⟩
    refine Drop.seq_clean
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
      (P_mid := ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (Q := fun sm => ScanLoopSaved s sm)
      ?_ ?_
    · refine SepWP.mono
        (scan_weird_to_500 w s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
          hw0 hwffff hw1 hw2 hwfffe hw256 hw512 hwfeff hpc hrun hx11 hx12) ?_
      rintro sm Pm _ _ ⟨hPm, hsaved1⟩
      rw [hPm]
      exact ⟨Entails.refl _, hsaved1⟩
    · rintro sm hpcm hrunm hsaved1
      refine SepWP.mono
        (scan_exit_500 sm Frame hb hpcm hrunm (hsaved1.x28.trans hx28)) ?_
      rintro sf Pf _ _ ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved2⟩
      exact ⟨hPf, hx21_sf, hx22_sf.trans hsaved1.x19, hx28_sf, hsaved1.trans hsaved2⟩

theorem scan_9c_true_exit {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hw : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  refine Drop.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x174#64)
    (P_mid := ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
    (Q := fun sm => ScanLoopSaved s sm)
    ?_ ?_
  · refine SepWP.mono
      (scan_true_to_574 w s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) hw hpc hrun hx11 hx12) ?_
    rintro sm Pm _ _ ⟨hPm, hsaved1⟩
    rw [hPm]
    exact ⟨Entails.refl _, hsaved1⟩
  · rintro sm hpcm hrunm hsaved1
    refine SepWP.mono (scan_exit_574 sm Frame hb hpcm hrunm) ?_
    rintro sf Pf _ _ ⟨hPf, hsaved2⟩
    exact ⟨hPf, hsaved1.trans hsaved2⟩

theorem issue1275NeedsFlip_cons_cont (b0 b1 : BitVec 8) (rest : Bytes)
    (hw : ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0000#16 ∨
          ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFFFF#16) :
    issue1275NeedsFlip (b0 :: b1 :: rest) = issue1275NeedsFlip rest := by
  dsimp only [issue1275NeedsFlip]
  rcases hw with h | h <;> simp [h]

theorem issue1275NeedsFlip_cons_false_not_be (b0 b1 : BitVec 8) (rest : Bytes)
    (hflip : issue1275NeedsFlip (b0 :: b1 :: rest) = false) :
    ¬(((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0100#16 ∨
      ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0200#16 ∨
      ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFEFF#16) := by
  dsimp only [issue1275NeedsFlip] at hflip
  rintro (h | h | h) <;> simp [h] at hflip

theorem issue1275NeedsFlip_cons_true_be (b0 b1 : BitVec 8) (rest : Bytes)
    (hflip : issue1275NeedsFlip (b0 :: b1 :: rest) = true)
    (hnot_cont : ¬(((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0000#16 ∨
                   ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFFFF#16)) :
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0100#16 ∨
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0x0200#16 ∨
    ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = 0xFEFF#16 := by
  dsimp only [issue1275NeedsFlip] at hflip
  generalize ((b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16) = w at hflip hnot_cont ⊢
  push Not at hnot_cont
  rcases hnot_cont with ⟨hw0, hwffff⟩
  have hc0 : (w == 0x0000#16 || w == 0xFFFF#16) = false := by
    revert hw0 hwffff; bv_kernel
  rw [hc0] at hflip
  by_cases hc1 : (w == 0x0001#16 || w == 0x0002#16 || w == 0xFFFE#16) = true
  · rw [hc1] at hflip; contradiction
  · rw [Bool.not_eq_true] at hc1
    rw [hc1] at hflip
    by_cases hc2 : (w == 0x0100#16 || w == 0x0200#16 || w == 0xFEFF#16) = true
    · simp only [Bool.or_eq_true, beq_iff_eq] at hc2
      rcases hc2 with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [Bool.not_eq_true] at hc2
      rw [hc2] at hflip; contradiction

/-- Complete inductive proof of the `issue1275NeedsFlip` scan loop (`0x5e488 → 0x5e628`)
when `issue1275NeedsFlip bs = false`. -/
theorem scan_loop_false_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
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
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
      (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
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
        (scan_head_step ptr rem w s
          (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
          hrem_lo hpc hrun hx8 hx9 hx10) ?_
      rintro sm Pm _ _ ⟨hPm, hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hsaved_m⟩
      rw [hPm]
      exact ⟨Entails.refl _, hx8_m, hx9_m, hx10_m, hx11_m.trans hx11, hx12_m, hx13_m.trans hx13, hx14_m, hsaved_m⟩
    · rintro sm hpcm hrunm ⟨hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hsaved_m⟩
      by_cases hw_cont : w = 0x0000#16 ∨ w = 0xFFFF#16
      · have hflip_rest : issue1275NeedsFlip rest = false := by
          rwa [issue1275NeedsFlip_cons_cont b0 b1 rest hw_cont] at hflip
        refine Drop.seq_clean
          (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
          (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
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
            (scan_continue_to_7c w sm
              ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
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
              (scan_7c_last s7c
                ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ []) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
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
              (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
              (P_mid := ((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ Frame))
              (Q := fun s88 =>
                s88.readReg64 .x8 = ptr + 2#64 ∧
                s88.readReg64 .x9 = rem - 2#64 ∧
                s88.readReg64 .x10 = 2#64 ∧
                s88.readReg64 .x11 = 65534#64 ∧
                s88.readReg64 .x13 = 65535#64 ∧
                ScanLoopSaved s s88)
              ?_ ?_
            · refine SepWP.mono
                (scan_7c_more ptr rem s7c
                  ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
                  hrem_gt hrem_hi hpc7c hrun7c hx8_7 hx9_7 hx14_7) ?_
              rintro s88 P88 _ _ ⟨hP88, hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              rw [hP88]
              exact ⟨Entails.of_eq (by ac_rfl), hx8_8, hx9_8, hx10_8.trans hx10_7,
                hx11_8.trans hx11_7, hx13_8.trans hx13_7, hsaved_7.trans hsaved_8⟩
            · rintro s88 hpc88 hrun88 ⟨hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              refine SepWP.mono
                (scan_loop_false_ok (ptr + 2#64) (b2 :: b3 :: rest') (rem - 2#64) s88
                  ((ptr ↦₁₆ w) ∗ Frame)
                  hb hrest_ne hrest_mod hrest_le hrem_sub hflip_rest hpc88 hrun88
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
        have hpre_eq : ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)) =
            (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)) := by
          ac_rfl
        conv => arg 4; rw [hpre_eq]
        refine SepWP.mono
          (scan_9c_false_exit w sm ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)
            hb hw0 hwffff hw256 hw512 hwfeff hpcm hrunm hx11_m hx12_m (hsaved_m.x28.trans hx28)) ?_
        rintro sf Pf _ _ ⟨hPf, hx21_f, hx22_f, hx28_f, hsaved_f⟩
        refine ⟨?_, hx21_f, hx22_f.trans hsaved_m.x19, hx28_f, hsaved_m.trans hsaved_f⟩
        rw [hPf]
        ac_rfl

/-- Complete inductive proof of the `issue1275NeedsFlip` scan loop (`0x5e488 → 0x5e5d8`)
when `issue1275NeedsFlip bs = true`. -/
theorem scan_loop_true_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64)
      s ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
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
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
      (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
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
        (scan_head_step ptr rem w s
          (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
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
            (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
            (P_mid := (ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
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
              (scan_continue_to_7c w sm
                ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
                hw_cont hpcm hrunm hx11_m hx12_m hx13_m) ?_
            rintro s7c P7c _ _ ⟨hP7c, hx8_7, hx9_7, hx10_7, hx11_7, hx13_7, hx14_7, hsaved_7⟩
            rw [hP7c]
            exact ⟨Entails.refl _, hx8_7.trans hx8_m, hx9_7.trans hx9_m, hx10_7.trans hx10_m,
              hx11_7, hx13_7, hx14_7.trans hx14_m, hsaved_m.trans hsaved_7⟩
          · rintro s7c hpc7c hrun7c ⟨hx8_7, hx9_7, hx10_7, hx11_7, hx13_7, hx14_7, hsaved_7⟩
            refine Drop.seq_clean
              (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
              (P_mid := ((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ Frame))
              (Q := fun s88 =>
                s88.readReg64 .x8 = ptr + 2#64 ∧
                s88.readReg64 .x9 = rem - 2#64 ∧
                s88.readReg64 .x10 = 2#64 ∧
                s88.readReg64 .x11 = 65534#64 ∧
                s88.readReg64 .x13 = 65535#64 ∧
                ScanLoopSaved s s88)
              ?_ ?_
            · refine SepWP.mono
                (scan_7c_more ptr rem s7c
                  ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame))
                  hrem_gt hrem_hi hpc7c hrun7c hx8_7 hx9_7 hx14_7) ?_
              rintro s88 P88 _ _ ⟨hP88, hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              rw [hP88]
              exact ⟨Entails.of_eq (by ac_rfl), hx8_8, hx9_8, hx10_8.trans hx10_7,
                hx11_8.trans hx11_7, hx13_8.trans hx13_7, hsaved_7.trans hsaved_8⟩
            · rintro s88 hpc88 hrun88 ⟨hx8_8, hx9_8, hx10_8, hx11_8, hx13_8, hsaved_8⟩
              refine SepWP.mono
                (scan_loop_true_ok (ptr + 2#64) (b2 :: b3 :: rest') (rem - 2#64) s88
                  ((ptr ↦₁₆ w) ∗ Frame)
                  hb hrest_ne hrest_mod hrest_le hrem_sub hflip_rest hpc88 hrun88
                  hx8_8 hx9_8 hx10_8 hx11_8 hx13_8) ?_
              rintro sf Pf _ _ ⟨hPf, hsaved_f⟩
              refine ⟨?_, hsaved_8.trans hsaved_f⟩
              rw [hPf]
              ac_rfl
      · have hw_be : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16 :=
          issue1275NeedsFlip_cons_true_be b0 b1 rest hflip hw_cont
        have hpre_eq : ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)) =
            (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)) := by
          ac_rfl
        conv => arg 4; rw [hpre_eq]
        refine SepWP.mono
          (scan_9c_true_exit w sm ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)
            hb hw_be hpcm hrunm hx11_m hx12_m) ?_
        rintro sf Pf _ _ ⟨hPf, hsaved_f⟩
        refine ⟨?_, hsaved_m.trans hsaved_f⟩
        rw [hPf]
        ac_rfl

end CryptoVerification.SpqrV1.Unchunked
