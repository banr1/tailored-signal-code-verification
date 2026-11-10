/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Companion for Shared `Ok` Epilogue

Lifts `epilogue_step_8468_64` (`Epilogue.lean`) and `epilogue_step_8468_64_region`,
`states_from_pb_epilogue_8180`, `states_from_pb_epilogue_8176` (`Variant1.lean`) from
`AllocContracts` to `AllocContracts4K` inside `CryptoVerification.SpqrV1.States.FromPb.Ext4K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::from_pb")
  (ls_stub% "memcpy")

@[local arm64_norm, local wp_norm]
private theorem bv328_toNat_ext : (328#64 : BitVec 64).toNat = 328 := rfl

/-- Step C of the shared `Ok` epilogue (`+8468 -> +64`, 8 instructions including `BL memcpy`),
parameterized directly by `subroutine_ok` for `sessionMemcpySpec allocHookStack` at `memcpyName`. -/
theorem epilogue_step_8468_64_of_memcpy
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (sessionMemcpySpec allocHookStack))
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 560#64) 328 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗
       ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 560#64) ↦ₛ bs240) ∗
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗
          ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗
          ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        BitVec.ofNat 64 (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy")))
      (sessionMemcpySpec allocHookStack) :=
    sub_ok_at_of_fnAddr hmemcpy_fn statesFromPbName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
      (by simp only [statesFromPbName, memcpyName, arm64_norm])
  simp only [sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  rw [← hbs240]
  states_from_pb_fetches_range b (Rust.withPanics ext) 8468 32
  dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre [pointsTo128, sepConj_assoc]
  wp_steps
  wp_call hmemcpy (s.readReg64 .x19 + 560#64, s.sp + 240#64, bs240)
  wp_steps
  simp only [pointsTo128, sepConj_assoc]
  wp_done

/-- Minimal allocator & `session_memcpy` contract bundle used across `<States>::from_pb` variants,
satisfied by both `AllocContracts` and `AllocContracts4K`. -/
structure StatesFromPbAlloc (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr LibsignalTripleRatchet.deallocName) (rustDeallocSpec A)
  shim : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  session_memcpy_16 : subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack)

namespace StatesFromPbAlloc

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

theorem of_allocContracts (hA : AllocContracts b A ext) : StatesFromPbAlloc b A ext :=
  ⟨hA.alloc, hA.dealloc, hA.shim, hA.session_memcpy allocHookStack⟩

theorem of_4k (hA : AllocContracts4K b A ext) : StatesFromPbAlloc b A ext :=
  ⟨hA.alloc, hA.dealloc, hA.shim, hA.session_memcpy allocHookStack (by decide) (by decide)⟩

theorem alloc_ok_at (hA : StatesFromPbAlloc b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem shim_ok_at (hA : StatesFromPbAlloc b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem session_memcpy_ok_at (hA : StatesFromPbAlloc b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpySpec allocHookStack) :=
  sub_ok_at_of_fnAddr hA.session_memcpy_16 name k hk

end StatesFromPbAlloc

/-- Goal type of `states_from_pb_keysUnsampled_156` (`Variant1b.lean`). -/
abbrev StatesFromPbKeysUnsampled156Goal (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (ext : String → Option (State → State)) (s0 s1 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.KeysUnsampled) (R : SepProp) : Prop :=
  SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      optProtoInnerStateAt A pbA (some (.keysUnsampled s)) ∗ statesFromPbJumpTableAt b ∗ A.pool)
    (fun sf Pf =>
      (Pf ⊢ resultChunkedStatesAt A (F := F) out
          (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.keysUnsampled s) }) ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗
        stackAt s0.sp statesFromPbStack) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
    (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))

/-- Step C of the shared `Ok` epilogue (`+8468 -> +64`, 8 instructions including `BL memcpy`)
under `StatesFromPbAlloc`. -/
theorem epilogue_step_8468_64_sfa
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext)
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 560#64) 328 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗
       ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 560#64) ↦ₛ bs240) ∗
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗
          ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗
          ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) :=
  epilogue_step_8468_64_of_memcpy hA.session_memcpy_16
    s fsp out bs240 hbs240 uq888 uq904 q1888 q1904 u920 w1920 Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19

theorem epilogue_step_8468_64_region_sfa
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64) (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64) s
      (stackAt fsp allocHookStack ∗ memRegion (out + 560#64) 368 ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          (((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q1888) ∗
           ((out + 904#64) ↦₁₂₈ q1904) ∗ ((out + 920#64) ↦₆₄ w1920)) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_partC_split out))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u920
  apply ProofLib.SepWP.exists_left; intro uq904
  apply ProofLib.SepWP.exists_left; intro uq888
  have hstep := epilogue_step_8468_64_sfa hA s fsp out bs240 hbs240
    uq888 uq904 q1888 q1904 u920 w1920 Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
  intro sm Pm _ _ ⟨hPm, hregs⟩
  exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hregs⟩

/-- Complete shared `Ok` epilogue from `+8180` to `s0.x30` under `StatesFromPbAlloc`. -/
theorem states_from_pb_epilogue_8180_sfa
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx6 : s.readReg64 .x6 = (s0.sp - 2400#64) + 576#64) (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp halign
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_928_split_8 out))) ?_
  unfold epilogueStackSlots
  refine SepWP.seq (epilogue_step_8180_8284_region s (s0.sp - 2400#64) out w208 w880
    q704 q720 q736 q752 q768 q784 q800 q816 q848
    (((s0.sp - 2400#64 + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
     ((s0.sp - 2400#64 + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
     memRegion (out + 103#64) 42 ∗ memRegion (out + 161#64) 7 ∗
     memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168 ∗ memRegion (out + 560#64) 368 ∗
     ((s0.sp - 2400#64 + 92#64) ↦₃₂ d92) ∗
     ((s0.sp - 2400#64 + 104#64) ↦₆₄ w104) ∗ ((s0.sp - 2400#64 + 112#64) ↦₆₄ w112) ∗
     ((s0.sp - 2400#64 + 120#64) ↦₆₄ w120) ∗ ((s0.sp - 2400#64 + 160#64) ↦₆₄ w160) ∗
     ((s0.sp - 2400#64 + 172#64) ↦₃₂ d172) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
     ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
     ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240) ∗
     ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ q576) ∗ ((s0.sp - 2400#64 + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
     ((s0.sp - 2400#64 + 608#64) ↦₁₂₈ q608) ∗ ((s0.sp - 2400#64 + 624#64) ↦₁₂₈ q624) ∗
     ((s0.sp - 2400#64 + 640#64) ↦₁₂₈ q640) ∗ ((s0.sp - 2400#64 + 656#64) ↦₁₂₈ q656) ∗
     ((s0.sp - 2400#64 + 672#64) ↦₁₂₈ q672) ∗ ((s0.sp - 2400#64 + 688#64) ↦₁₂₈ q688) ∗
     ((s0.sp - 2400#64 + 832#64) ↦₆₄ w832) ∗
     ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ q1888) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ q1904) ∗
     ((s0.sp - 2400#64 + 1920#64) ↦₆₄ w1920) ∗
     memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
     epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
    hfsp_align hpc hrun hsp hx19 |>
    SepWP.weaken_pre (by unfold epilogueStackPartA; exact Entails.of_eq (by ac_rfl))) ?_
  intro sA PA hpcA hrunA ⟨hPA, hspA, hx0A, hx1A, hx2A, hx4A, hx5A, hx6A, hx7A, hx8A, hx9A,
    hx10A, hx11A, hx12A, hx16A, hx19A, hx21A, hx22A, hx23A, hx24A, hx26A, hx28A, _, htrA⟩
  have hPA' : PA ⊢
      ((memRegion (out + 103#64) 42 ∗ (((out + 145#64) ↦₁₂₈ q848) ∗ memRegion (out + 161#64) 7) ∗
        memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168) ∗
       epilogueStackPartBPre (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 w224 w232 w592
         w832 (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
         q576 q608 q624 q640 q656 q672 q688 ∗
       (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
        memRegion (out + 560#64) 368 ∗ ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240) ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ q1888) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ q1904) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ w1920) ∗
        epilogueOutPartANo145 out
          (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
          (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
          (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
          ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
          (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
          q704 q720 q736 q752 q768 q784 q800 q816 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
        ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
        ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
        ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
        ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
        ((s0.sp - 2400#64 + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
        ((s0.sp - 2400#64 + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
        ((s0.sp - 2400#64 + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
        epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)) := by
    refine Entails.trans hPA ?_
    rw [sepConj_assoc, sepConj_assoc, ← sepConj_assoc (epilogueStackPartA _ _ _ _ _ _ _ _ _ _ _ _),
        ← sepConj_assoc (epilogueStackPartA _ _ _ _ _ _ _ _ _ _ _ _ ∗ _),
        epilogueStackPartA_realign_eq]
    unfold epilogueStackPartBPre
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.seq (SepWP.weaken_pre hPA' (epilogue_step_8284_8468_region sA (s0.sp - 2400#64) out q848
    d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832
    (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
    q576 q608 q624 q640 q656 q672 q688 _
    hfsp_align hpcA hrunA hspA hx0A (hx6A.trans hx6) hx19A (hx23A.trans hx23))) ?_
  intro sB PB hpcB hrunB ⟨hPB, hspB, hx0B, hx1B, hx2B, hx19B, _, htrB⟩
  rw [hx8A, hx4A, hx5A, hx21A, hx9A, hx7A, hx2A, hx11A, hx22A, hx24A, hx10A, hx26A, hx12A, hx1A, hx28A, hx16A] at hPB
  refine SepWP.seq (SepWP.weaken_pre (Entails.trans hPB (Entails.of_eq (by ac_rfl)))
    (epilogue_step_8468_64_region_sfa hA sB (s0.sp - 2400#64) out bs240 hbs240 q1888 q1904 w1920
      (((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
       epilogueOutPartBPost out
         (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
         (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
         w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
         (d172.setWidth 8) (overlapWord7 (q848.extractLsb' 64 64) w864)
         q608 q624 q640 q656 q672 q688
         w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
         (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
         (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
         (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
         w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) ∗
       epilogueStackPartBPost (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 w224 w232 w592
         w832 (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
         q576 q608 q624 q640 q656 q672 q688 ∗
       memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       epilogueOutPartANo145 out
         (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
         (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
         (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
         ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
         (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
         q704 q720 q736 q752 q768 q784 q800 q816 ∗
       ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
       ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
       ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
       ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
       ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
       ((s0.sp - 2400#64 + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
       ((s0.sp - 2400#64 + 856#64) ↦ₛ EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
       ((s0.sp - 2400#64 + 880#64) ↦ₛ EncoderFromPb.loBytes7 w880) ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      hfsp_align hpcB hrunB hspB hx0B hx1B hx2B hx19B)) ?_
  intro sC PC hpcC hrunC ⟨hPC, hspC, htrC⟩
  have hPC' : PC ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (epilogueOutFull out
        (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
        (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
        (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
        ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
        (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
        (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
        (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
        w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
        (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
        (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
        (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
        (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
        w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240 q1888 q1904 w1920 ∗
       Frame) := by
    refine Entails.trans hPC ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    have hstk := epilogueStackPost_entails_2304 (s0.sp - 2400#64)
      d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240 hbs240
      q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 q1888 q1904 w1920
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hstk))
    unfold epilogueStackPartBPost epilogueStackGaps
      epilogueOutPartANo145 epilogueOutPartBPost epilogueOutFull
    exact Entails.of_eq (by ac_rfl)
  have hep := states_from_pb_epilogue_64 s0 sC
    (epilogueOutFull out
      (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
      (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
      (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
      ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
      (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
      (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
      (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
      w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
      (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
      (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
      (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
      (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
      w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240 q1888 q1904 w1920 ∗
     Frame)
    halign hpcC hrunC hspC (htrC.trans (htrB.trans (htrA.trans htr)))
  refine SepWP.weaken_pre hPC' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f⟩

/-- Complete shared `Ok` epilogue from `+8176` (`add x6, sp, #576`) to `s0.x30` under `StatesFromPbAlloc`. -/
theorem states_from_pb_epilogue_8176_sfa
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : StatesFromPbAlloc b A ext) (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8176#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hstep : ∀ (P_pre : SepProp),
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64) s P_pre
        (fun s1 P1 =>
          (P1 ⊢ P_pre) ∧ s1.sp = s.sp ∧ s1.readReg64 .x6 = s.sp + 576#64 ∧
          s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
          s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg32 .x3 = s.readReg32 .x3 ∧
          s1.readReg64 .x4 = s.readReg64 .x4 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
          s1.readReg64 .x7 = s.readReg64 .x7 ∧ s1.readReg64 .x8 = s.readReg64 .x8 ∧
          s1.readReg64 .x9 = s.readReg64 .x9 ∧ s1.readReg64 .x10 = s.readReg64 .x10 ∧
          s1.readReg64 .x11 = s.readReg64 .x11 ∧ s1.readReg64 .x12 = s.readReg64 .x12 ∧
          s1.readReg64 .x13 = s.readReg64 .x13 ∧ s1.readReg64 .x14 = s.readReg64 .x14 ∧
          s1.readReg64 .x15 = s.readReg64 .x15 ∧ s1.readReg64 .x16 = s.readReg64 .x16 ∧
          s1.readReg64 .x17 = s.readReg64 .x17 ∧ s1.readReg64 .x18 = s.readReg64 .x18 ∧
          s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
          s1.readReg32 .x21 = s.readReg32 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg32 .x27 = s.readReg32 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x30 = s.readReg64 .x30 ∧
          TraceCalleeSaved s1 s) := by
    intro P_pre
    states_from_pb_fetches_range b (Rust.withPanics ext) 8176 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps; wp_done
  refine SepWP.seq (hstep _) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx6_1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx7_1,
    hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
    hx28_1, hx30_1, htr1⟩
  have hep := states_from_pb_epilogue_8180_sfa hA s0 s1 out
    d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240 hbs240
    q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame
    halign hpc1 hrun1 (hsp1.trans hsp) (hx6_1.trans (congrArg (· + 576#64) hsp))
    (hx19_1.trans hx19) (hx23_1.trans hx23) (htr1.trans htr)
  rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
      hx3_1, hx27_32_1, hx27_1, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1,
      hx10_1, hx26_1, hx12_1, hx1_1, hx28_1, hx16_1] at hep
  exact SepWP.weaken_pre hP1 hep

namespace Ext4K

theorem epilogue_step_8468_64
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64) (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64) s
      (stackAt fsp allocHookStack ∗ memRegion (out + 560#64) 328 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗ ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt fsp allocHookStack ∗ ((out + 560#64) ↦ₛ bs240) ∗
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗ ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) :=
  epilogue_step_8468_64_sfa (.of_4k hA) s fsp out bs240 hbs240 uq888 uq904 q1888 q1904 u920 w1920
    Frame hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19

theorem epilogue_step_8468_64_region
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64) (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64) s
      (stackAt fsp allocHookStack ∗ memRegion (out + 560#64) 368 ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt fsp allocHookStack ∗
          (((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q1888) ∗
           ((out + 904#64) ↦₁₂₈ q1904) ∗ ((out + 920#64) ↦₆₄ w1920)) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) :=
  epilogue_step_8468_64_region_sfa (.of_4k hA) s fsp out bs240 hbs240 q1888 q1904 w1920 Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19

theorem states_from_pb_epilogue_8180
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx6 : s.readReg64 .x6 = (s0.sp - 2400#64) + 576#64) (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) :=
  states_from_pb_epilogue_8180_sfa (.of_4k hA) s0 s out d92 d172 w104 w112 w120 w160 w192 w208
    w224 w232 bs240 hbs240 q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784
    q800 q816 w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame halign hpc hrun hsp hx6 hx19 hx23 htr

theorem states_from_pb_epilogue_8176
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8176#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) :=
  states_from_pb_epilogue_8176_sfa (.of_4k hA) s0 s out d92 d172 w104 w112 w120 w160 w192 w208
    w224 w232 bs240 hbs240 q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784
    q800 q816 w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame halign hpc hrun hsp hx19 hx23 htr

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
