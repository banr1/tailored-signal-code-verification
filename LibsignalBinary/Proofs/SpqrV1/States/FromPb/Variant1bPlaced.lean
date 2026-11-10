/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DecodesPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 0 (`KeysUnsampled`, `+156`)

Relocatable Block-`333` error and success paths for `InnerState.keysUnsampled`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## External Alloc / Memcpy Hook Bundle for `States::from_pb` (Block `333`) -/

/-- External hook satisfaction bundle replacing `AllocContracts b A ext` for relocatable
    `States::from_pb` (Block `333`). -/
structure FromPbAllocHooks (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  panic_ok : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked
  shim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimSpec
  alloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A)
  dealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)
  memcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec

theorem fromPb_externAt?_handleError [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
  Eq.trans spqr_externAt?_of_mem hA.panic_ok

/-! ## Variant 0 (`KeysUnsampled`, `+156`) Error Paths (`uc = none` and `auth = none`) -/

/-- `KeysUnsampled` error path when `s.uc = none` (`+156 -> +2044 -> s0.x30`). -/
theorem states_from_pb_keysUnsampled_uc_none_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ none2Cap) ∗
        memRegion (pbA + 16#64) 48 ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := none }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 2044#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [none2Cap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 156#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 2044#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hpb := pbA_keysUnsampled_uc_none_entails_224 pbA
      dsimp only [none2Cap] at hpb
      refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpb)))))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have hep := states_from_pb_err_2044_placed (A := A) (F := F) (ext := ext) s0 s2 out
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩
    change resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) ∗
        stackAt s0.sp statesFromPbStack ⊢
      resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool ∗ stackAt s0.sp statesFromPbStack
    exact Entails.of_eq (by ac_rfl)

/-- `KeysUnsampled` error path when `s.uc = some { auth := none, epoch := ep }` (`+156 -> +2044 -> s0.x30`). -/
theorem states_from_pb_keysUnsampled_auth_none_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA ep : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
        memRegion (pbA + 16#64) 40 ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := none, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 2044#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool))
    (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 156#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 2044#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hpb := pbA_keysUnsampled_auth_none_entails_224 pbA ep
      dsimp only [noneCap] at hpb
      refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpb)))))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have hep := states_from_pb_err_2044_placed (A := A) (F := F) (ext := ext) s0 s2 out
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2
    refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩
    change resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) ∗
        stackAt s0.sp statesFromPbStack ⊢
      resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗
        A.pool ∗ stackAt s0.sp statesFromPbStack
    exact Entails.of_eq (by ac_rfl)

/-! ## Specialized Placed Epilogue Wrapper for `KeysUnsampled` (`+8176 -> ret`) -/

theorem states_from_pb_epilogue_8176_keysUnsampled_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (out pa1 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8176#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 208 ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗
       memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (out ↦₆₄ s.readReg64 .x8) ∗ ((out + 8#64) ↦₆₄ s.readReg64 .x15) ∗
          ((out + 16#64) ↦₆₄ pa1) ∗ ((out + 24#64) ↦₆₄ s.readReg64 .x20) ∗
          ((out + 32#64) ↦₆₄ s.readReg64 .x13) ∗ ((out + 40#64) ↦₆₄ s.readReg64 .x25) ∗
          ((out + 48#64) ↦₆₄ s.readReg64 .x30) ∗ ((out + 56#64) ↦₆₄ s.readReg64 .x9) ∗
          memRegion (out + 64#64) 864 ∗ stackAt s0.sp statesFromPbStack ∗ Frame) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (memRegion_208_entails_epilogue_lo (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_left (memRegion_2088_entails_epilogue_hi (s0.sp - 2400#64))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun w1920 => ProofLib.SepWP.exists_left fun q1904 =>
    ProofLib.SepWP.exists_left fun q1888 => ProofLib.SepWP.exists_left fun w888 =>
    ProofLib.SepWP.exists_left fun w880 => ProofLib.SepWP.exists_left fun w864 =>
    ProofLib.SepWP.exists_left fun q848 => ProofLib.SepWP.exists_left fun w832 =>
    ProofLib.SepWP.exists_left fun q816 => ProofLib.SepWP.exists_left fun q800 =>
    ProofLib.SepWP.exists_left fun q784 => ProofLib.SepWP.exists_left fun q768 =>
    ProofLib.SepWP.exists_left fun q752 => ProofLib.SepWP.exists_left fun q736 =>
    ProofLib.SepWP.exists_left fun q720 => ProofLib.SepWP.exists_left fun q704 =>
    ProofLib.SepWP.exists_left fun q688 => ProofLib.SepWP.exists_left fun q672 =>
    ProofLib.SepWP.exists_left fun q656 => ProofLib.SepWP.exists_left fun q640 =>
    ProofLib.SepWP.exists_left fun q624 => ProofLib.SepWP.exists_left fun q608 =>
    ProofLib.SepWP.exists_left fun w592 => ProofLib.SepWP.exists_left fun q576 =>
    ProofLib.SepWP.exists_left fun bs240 => ProofLib.SepWP.exists_left fun w232 =>
    ProofLib.SepWP.exists_left fun w224 => ProofLib.SepWP.exists_left fun w192 =>
    ProofLib.SepWP.exists_left fun d172 => ProofLib.SepWP.exists_left fun w160 =>
    ProofLib.SepWP.exists_left fun w120 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d92 => ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
    epilogueStackSlots (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 pa1 w224 w232 bs240.val
      q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
    epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame by
      unfold epilogueStackSlots epilogueStackGaps; ac_rfl)) ?_
  refine SepWP.mono (states_from_pb_epilogue_8176_placed hmemcpy_sat s0 s out
    d92 d172 w104 w112 w120 w160 w192 pa1 w224 w232 bs240.val bs240.property
    q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame halign hpc hrun hsp hx19 hx23 htr) ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m⟩
  refine ⟨Entails.trans hPm (Entails.trans (sepConj_mono_left (epilogueOutFull_entails_64_864 out
    (s.readReg64 .x8) (s.readReg64 .x15) pa1 (s.readReg64 .x20)
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
    bs240.val bs240.property q1888 q1904 w1920)) (Entails.of_eq (by ac_rfl))), hsp_m, hcc_m, htr_m⟩

/-! ## Variant 0 (`KeysUnsampled`, `+156`) Success Path (`uc = some { epoch, auth := some auth }`) -/

theorem states_from_pb_keysUnsampled_step0_156_200_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ep w152 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Frame : SepProp)
    (hcap0 : ga.rootKey.cap.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 200#64) s
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗
        authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗
        memRegion (pbA + 64#64) 160 ∗
        ((fsp + 152#64) ↦₆₄ w152) ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 152#64) ↦₆₄ ep) ∗
          vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
          vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗
          memRegion pbA optProtoInnerStateSize ∗ Frame) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧
        s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧
        s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
        TraceCalleeSaved s1 s) := by
  have hcmn2 : (ga.rootKey.cap + 2#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_two_beq_zero_false hcap0)
  have hcmn1 : (ga.rootKey.cap + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hcap0)
  rw [authenticatorPBPinnedAt_8_eq_full]
  change s.pc = (blkPl_333).base + 156#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 200#64) s _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := pbA_keysUnsampled_some_entails_224 pbA ga.rootKey.cap ga.rootKey.ptr
      (BitVec.ofNat 64 auth.rootKey.length) ga.macKey.cap ga.macKey.ptr
      (BitVec.ofNat 64 auth.macKey.length) ep
    refine Entails.trans (Entails.of_eq (show _ =
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗
        ((pbA + 8#64) ↦₆₄ ga.rootKey.cap) ∗ ((pbA + 16#64) ↦₆₄ ga.rootKey.ptr) ∗
        ((pbA + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((pbA + 32#64) ↦₆₄ ga.macKey.cap) ∗ ((pbA + 40#64) ↦₆₄ ga.macKey.ptr) ∗
        ((pbA + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160) ∗
      ((fsp + 152#64) ↦₆₄ ep) ∗
      vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
      vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ Frame by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_step1_200_5476_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (target_pc fsp out w208 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 200#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (pa1 : BitVec 64) (s1 : State),
      s1.pc = lsmpl.base 333 + 5476#64 →
      s1.status = .Running →
      (s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
       s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
       s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
       s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
       s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
       s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s1
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗
         vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
         vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
       vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗ A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hr_cases : auth.rootKey = [] ∨ 0 < auth.rootKey.length := by cases auth.rootKey <;> simp
  rcases hr_cases with hr_nil | hr_pos
  · refine sepWPp_seq_clean
      (mid := lsmpl.base 333 + 5476#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ 1#64) ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
        vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) 1#64 auth.rootKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0)
      ?_ (hnext 1#64)
    clear hnext; rw [hr_nil] at hx26 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx26 ⊢
    change s.pc = (blkPl_333).base + 200#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5476#64) s _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A ga.rootKey.cap ga.rootKey.ptr []
      have hn := vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A ga.rootKey.cap ga.rootKey.ptr [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ 1#64) ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A ga.rootKey.cap ga.rootKey.ptr auth.rootKey hr_pos)))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
          (⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧ ga.rootKey.cap.toNat < 2 ^ 63 ∧
            ga.rootKey.ptr ≠ 0#64 ∧ ga.rootKey.cap ≠ 0#64⌝ ∗
           (A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
            memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (ga.rootKey.cap.toNat - auth.rootKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧ ga.rootKey.cap.toNat < 2 ^ 63 ∧
          ga.rootKey.ptr ≠ 0#64 ∧ ga.rootKey.cap ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
         A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
         memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (ga.rootKey.cap.toNat - auth.rootKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hr_le, hr_cap, hptr0, hcap0_ne⟩ => ?_
    have hr_lt63 : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
    have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
    have hr_ne0 : (BitVec.ofNat 64 auth.rootKey.length == 0#64) = false := ofNat_beq_zero_false hr_pos hr_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hr_lay3 : auth.rootKey.length + 1 ≤ 2 ^ 63 := hr_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
      spqr_hook_ok_of_mem hA.shim
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
      spqr_hook_ok_of_mem hA.alloc
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrMemcpySym) sessionMemcpySpec :=
      spqr_hook_ok_of_mem hA.memcpy
    simp only [sessionMemcpySpec] at hmc
    have hpanic : ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
      fromPb_externAt?_handleError hA
    dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hA
    change s.pc = (blkPl_333).base + 200#64 at hpc
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s _ _ _
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 220#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.rootKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom0 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom0, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom0_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom0
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := (blkPl_333).base + 5476#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ ((fsp + 208#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗
          vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
          vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) (sf_1.readReg64 Reg.x0) auth.rootKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
          s1.readReg64 .x22 = ga.rootKey.cap ∧ s1.readReg64 .x24 = ga.rootKey.ptr ∧
          s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
          s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
          s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
          s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0)
        ?_ (hnext (sf_1.readReg64 Reg.x0))
      clear hnext; wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp]
        have hd := vecU8Payload_pos_dealloc A ga.rootKey.cap ga.rootKey.ptr auth.rootKey hr_le hr_cap hptr0 hcap0_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.rootKey hr_pos hr_lt63 hoom0
        have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
        rw [hsp_sf1]
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
           memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length) (ga.rootKey.cap.toNat - auth.rootKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.rootKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.rootKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
          ((fsp + 208#64) ↦₆₄ sf_1.readReg64 Reg.x0) ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_step2_5476_5600_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (target_pc fsp out : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator) (Frame R : SepProp)
    (post : State → SepProp → Prop) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 5476#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length) (htr : TraceCalleeSaved s s0)
    (hnext : ∀ (s2 : State),
      s2.pc = lsmpl.base 333 + 5600#64 →
      s2.status = .Running →
      (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
       s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
       s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
       s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
       s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
       s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0) →
      SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s2
        (stackAt fsp encoderFromPbStack ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
         vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s2.readReg64 .x25) auth.macKey ∗
         A.pool ∗ Frame)
        post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s
      (stackAt fsp encoderFromPbStack ∗ vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗ Frame)
      post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hm_cases : auth.macKey = [] ∨ 0 < auth.macKey.length := by cases auth.macKey <;> simp
  rcases hm_cases with hm_nil | hm_pos
  · refine sepWPp_seq_clean
      (mid := lsmpl.base 333 + 5600#64)
      (P_mid := stackAt fsp encoderFromPbStack ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) 1#64 auth.macKey ∗ A.pool ∗ Frame)
      (Q_regs := fun s2 => s2.readReg64 .x25 = 1#64 ∧
        (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
         s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
         s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
         s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
         s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
         s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0))
      ?_ (fun s2 hpc2 hrun2 ⟨hx25, hregs⟩ => by rw [← hx25]; exact hnext s2 hpc2 hrun2 hregs)
    clear hnext; rw [hm_nil] at hx13 hx27 ⊢
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx13 hx27 ⊢
    change s.pc = (blkPl_333).base + 5476#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5600#64) s _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hd := vecU8Payload_entails_dealloc A ga.macKey.cap ga.macKey.ptr []
      have hn := vecU8Payload_of_nil A
      dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hn
      refine Entails.trans (Entails.of_eq (show _ =
        vecU8Payload A ga.macKey.cap ga.macKey.ptr [] ∗ emp ∗
        stackAt fsp encoderFromPbStack ∗ A.pool ∗ Frame by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hd (sepConj_mono_left hn)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · refine SepWPp.weaken_pre (sepConj_mono_right
      (sepConj_mono_left (vecU8Payload_pos_unpack A ga.macKey.cap ga.macKey.ptr auth.macKey hm_pos))) ?_
    rw [show stackAt fsp encoderFromPbStack ∗
          (⌜auth.macKey.length ≤ ga.macKey.cap.toNat ∧ ga.macKey.cap.toNat < 2 ^ 63 ∧
            ga.macKey.ptr ≠ 0#64 ∧ ga.macKey.cap ≠ 0#64⌝ ∗
           (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
            memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (ga.macKey.cap.toNat - auth.macKey.length))) ∗
          A.pool ∗ Frame =
        ⌜auth.macKey.length ≤ ga.macKey.cap.toNat ∧ ga.macKey.cap.toNat < 2 ^ 63 ∧
          ga.macKey.ptr ≠ 0#64 ∧ ga.macKey.cap ≠ 0#64⌝ ∗
        (stackAt fsp encoderFromPbStack ∗
         A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
         memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (ga.macKey.cap.toNat - auth.macKey.length) ∗
         A.pool ∗ Frame) by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hm_le, hm_cap, hptr1, hcap1_ne⟩ => ?_
    have hm_lt63 : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hm_lt64 : auth.macKey.length < 2 ^ 64 := by omega
    have hm_toNat : (BitVec.ofNat 64 auth.macKey.length).toNat = auth.macKey.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm_lt64]
    have hm_ne0 : (BitVec.ofNat 64 auth.macKey.length == 0#64) = false := ofNat_beq_zero_false hm_pos hm_lt64
    have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hm_lay3 : auth.macKey.length + 1 ≤ 2 ^ 63 := hm_lt63
    have h1_toNat : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [stackAt_encoderFromPb_split_allocHook fsp]; wp_simp_pre [sepConj_assoc]
    have hshim : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustNoAllocShimSym) sessionShimSpec :=
      spqr_hook_ok_of_mem hA.shim
    simp only [sessionShimSpec] at hshim
    have halloc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
      spqr_hook_ok_of_mem hA.alloc
    simp only [rustAllocSpec] at halloc
    have hmc : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ spqrMemcpySym) sessionMemcpySpec :=
      spqr_hook_ok_of_mem hA.memcpy
    simp only [sessionMemcpySpec] at hmc
    have hpanic : ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
      fromPb_externAt?_handleError hA
    dsimp only [BitVec.ofNat_eq_ofNat] at hshim halloc hmc hpanic hpc hnext ⊢
    clear hA
    change s.pc = (blkPl_333).base + 5476#64 at hpc
    change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s _ _ _
    apply SepWPp.of_sepWP (mid := (blkPl_333).base + 5504#64)
    wp_steps; wp_apply; wp_steps; wp_call halloc (auth.macKey.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [statesFromPbOnPanic, sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom1, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_assoc]
      have hoom1_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom1
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      refine sepWPp_seq_clean (mid := (blkPl_333).base + 5600#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
          vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (sf_1.readReg64 Reg.x0) auth.macKey ∗
          A.pool ∗ Frame)
        (Q_regs := fun s2 => s2.readReg64 .x25 = sf_1.readReg64 Reg.x0 ∧
          (s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
           s2.readReg64 .x22 = ga.rootKey.cap ∧ s2.readReg64 .x24 = ga.rootKey.ptr ∧
           s2.readReg64 .x20 = ga.macKey.cap ∧ s2.readReg64 .x21 = ga.macKey.ptr ∧
           s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
           s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
           s2.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0))
        ?_ (fun s2 hpc2 hrun2 ⟨hx25, hregs⟩ => by rw [← hx25]; exact hnext s2 hpc2 hrun2 hregs)
      clear hnext; wp_steps; wp_apply; wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [stackAt_encoderFromPb_split_allocHook fsp]
        have hd := vecU8Payload_pos_dealloc A ga.macKey.cap ga.macKey.ptr auth.macKey hm_le hm_cap hptr1 hcap1_ne
        have hp := vecU8Payload_pos A (sf_1.readReg64 Reg.x0) auth.macKey hm_pos hm_lt63 hoom1
        have hsp_sf1 : sf_1.sp = fsp := by simp only [wp_norm, arm64_norm, *]
        rw [hsp_sf1]
        refine Entails.trans (Entails.of_eq (show _ =
          (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ (ga.macKey.ptr ↦ₛ auth.macKey) ∗
           memRegion (ga.macKey.ptr + BitVec.ofNat 64 auth.macKey.length) (ga.macKey.cap.toNat - auth.macKey.length)) ∗
          (A.live (sf_1.readReg64 Reg.x0) auth.macKey.length 1 ∗ (sf_1.readReg64 Reg.x0 ↦ₛ auth.macKey)) ∗
          memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗ A.pool ∗ Frame by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hd (sepConj_mono_left hp)) (Entails.of_eq (by ac_rfl))
      · wp_done

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_step3_5600_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s : State) (fsp out pbA ep pa1 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator) (hr_lt63 : auth.rootKey.length < 2 ^ 63)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5600#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx22 : s.readReg64 .x22 = ga.rootKey.cap) (hx24 : s.readReg64 .x24 = ga.rootKey.ptr)
    (hx20 : s.readReg64 .x20 = ga.macKey.cap) (hx21 : s.readReg64 .x21 = ga.macKey.ptr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗ memRegion (fsp + 160#64) 48 ∗
       ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
       vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
       vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
       vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
       vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  have hdealloc_raw : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem hA.dealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hr_lt64 : auth.rootKey.length < 2 ^ 64 := by omega
  have hr_toNat : (BitVec.ofNat 64 auth.rootKey.length).toNat = auth.rootKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt64]
  have hcmn_false : (BitVec.ofNat 64 auth.rootKey.length + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false (by rw [hr_toNat]; exact hr_lt63))
  rw [stackAt_encoderFromPb_split_allocHook fsp]
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 5624#64)
    (P_mid := memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
      memRegion out chunkedStatesSize ∗ memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗
      memRegion (fsp + 160#64) 48 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
      statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
      vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
      vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
      memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
    (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
      s1.readReg64 .x20 = ga.macKey.cap ∧ s1.readReg64 .x21 = ga.macKey.ptr ∧
      s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
      s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
      s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s1 s0) ?_ ?_
  · clear hfsp
    dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
    change s.pc = (blkPl_333).base + 5600#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5624#64) s _ _
    by_cases hc1 : (ga.rootKey.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
    · wp_steps; wp_apply; wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by rw [hsp]; ac_rfl)) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx23_1, hx20_1, hx21_1, hx25_1, hx26_1, hx13_1, hx27_1, htr1⟩
    refine EncoderFromPb.seq_clean
      (mid := lsmpl.base 333 + 5648#64)
      (P_mid := memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
        memRegion out chunkedStatesSize ∗ memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗
        memRegion (fsp + 160#64) 48 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
        vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x23 = fsp + 848#64 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧ s2.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s2.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧ TraceCalleeSaved s2 s0) ?_ ?_
    · clear hfsp
      dsimp only [vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc1 ⊢
      change s1.pc = (blkPl_333).base + 5624#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5648#64) s1 _ _
      by_cases hc2 : (ga.macKey.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
      · wp_steps; wp_apply; wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by rw [hsp1]; ac_rfl)) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx25_2, hx26_2, hx13_2, htr2⟩
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 8176#64)
        (P_mid := stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
          memRegion fsp 208 ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗ memRegion (fsp + 216#64) 2088 ∗
          statesFromPbSavedCells s0 ∗
          (vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool))
        (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = out ∧ s3.readReg64 .x23 = fsp + 848#64 ∧
          s3.readReg64 .x8 = 2#64 ∧ s3.readReg64 .x15 = BitVec.ofNat 64 auth.rootKey.length ∧
          s3.readReg64 .x20 = BitVec.ofNat 64 auth.rootKey.length ∧
          s3.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
          s3.readReg64 .x25 = s.readReg64 .x25 ∧ s3.readReg64 .x30 = BitVec.ofNat 64 auth.macKey.length ∧
          s3.readReg64 .x9 = ep ∧ TraceCalleeSaved s3 s0) ?_ ?_
      · clear hfsp
        change s2.pc = (blkPl_333).base + 5648#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 8176#64) s2 _ _
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · rw [stackAt_encoderFromPb_split_allocHook fsp]
          have h208 := memRegion_152_8_48_entails_208 fsp ep
          refine Entails.trans (Entails.of_eq (show _ =
            (memRegion fsp 152 ∗ ((fsp + 152#64) ↦₆₄ ep) ∗ memRegion (fsp + 160#64) 48) ∗
            memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack ∗
            memRegion out chunkedStatesSize ∗ ((fsp + 208#64) ↦₆₄ pa1) ∗
            memRegion (fsp + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
            vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
            vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
            memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left h208) (Entails.of_eq (by ac_rfl))
        · wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx8_3, hx15_3, hx20_3, hx13_3, hx25_3, hx30_3, hx9_3, htr3⟩
        subst hfsp
        have hep := states_from_pb_epilogue_8176_keysUnsampled_placed hA.memcpy s0 s3 out pa1
          (vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
          halign hpc3 hrun3 hsp3 hx19_3 hx23_3 htr3
        rw [hx8_3, hx15_3, hx20_3, hx13_3, hx25_3, hx30_3, hx9_3] at hep
        refine SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
          ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩
        rw [states_from_pb_keysUnsampled_some_eq]
        dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedKeysUnsampledAt,
          unchunkedKeysUnsampledAt, Authenticator.fromPb]
        have hauth := authenticatorAt_8_pack A out
          (BitVec.ofNat 64 auth.rootKey.length) pa1
          (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25)
          { rootKey := auth.rootKey, macKey := auth.macKey }
        dsimp only at hauth
        have h56 : (out + 8#64) + 48#64 = out + 56#64 := by bv_omega
        rw [h56]
        refine Entails.trans (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((out + 16#64) ↦₆₄ pa1) ∗
           ((out + 24#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((out + 32#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
           ((out + 40#64) ↦₆₄ s.readReg64 .x25) ∗ ((out + 48#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
           vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
           vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s.readReg64 .x25) auth.macKey) ∗
          (out ↦₆₄ 2#64) ∗ ((out + 56#64) ↦₆₄ ep) ∗ memRegion (out + 64#64) 864 ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hauth) (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
theorem states_from_pb_keysUnsampled_some_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State) (out pbA ep : BitVec 64)
    (auth : ProtoAuthenticator) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ optProtoAuthenticatorAt A (pbA + 8#64) (some auth) ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := some auth, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  rw [show optProtoAuthenticatorAt A (pbA + 8#64) (some auth) =
    ∃∗ ga : AuthenticatorPBGhost, authenticatorPBPinnedAt A ga (pbA + 8#64) auth from
    authenticatorPBAt_eq_exists_pinned A (pbA + 8#64) auth]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (memRegion_2304_split_152_208 (s0.sp - 2400#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ga => SepWPp.exists_elim fun w208 => SepWPp.exists_elim fun w152 => ?_
  have hcap_ext : authenticatorPBPinnedAt A ga (pbA + 8#64) auth ⊢
      ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ authenticatorPBPinnedAt A ga (pbA + 8#64) auth := by
    rw [authenticatorPBPinnedAt_8_eq_cap_tail]
    have h1 : vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ⊢
        ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey := by
      unfold vecU8Payload; apply Entails.pure_left; intro ⟨hle, hlt, hne⟩
      exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h1))))
      (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 152 ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000000#64) ∗
        authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool =
      authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
       ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl))
    (Entails.trans (sepConj_mono_left hcap_ext) (Entails.of_eq (show _ =
      ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗ authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
       ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
        memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
        statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)) by ac_rfl)))) ?_
  refine SepWPp.pure_elim fun hcap0 => ?_
  refine EncoderFromPb.sepWPp_seq_clean
    (states_from_pb_keysUnsampled_step0_156_200_placed (ext := ext) s1 (s0.sp - 2400#64) out pbA ep w152 ga auth
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
       ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
       statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
      hcap0 hfsp_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx22_2, hx24_2, hx20_2, hx21_2, hx26_2, hx13_2, hx27_2, htr2⟩
  have htr2 := htr2.trans htr1
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (vecU8Payload_extract_len_lt63 A ga.rootKey.cap ga.rootKey.ptr auth.rootKey))) ?_
  rw [show ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗
        (⌜auth.rootKey.length < 2 ^ 63⌝ ∗ vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey) ∗
        vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ memRegion pbA optProtoInnerStateSize ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
         memRegion (s0.sp - 2400#64) 152 ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
         ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
         statesFromPbSavedCells s0 ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) =
      ⌜auth.rootKey.length < 2 ^ 63⌝ ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
       vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗ A.pool ∗
       (vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗
        memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
        memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)) by ac_rfl]
  refine SepWPp.pure_elim fun hr_lt63 => ?_
  refine states_from_pb_keysUnsampled_step1_200_5476_placed hA s0 s2 (s0.readReg64 .x30)
    (s0.sp - 2400#64) out w208 ga auth
    (vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗
     memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
     memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) R _
    hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx22_2 hx24_2 hx20_2 hx21_2 hx26_2 hx13_2 hx27_2 htr2 ?_
  intro pa1 s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx23_3, hx22_3, hx24_3, hx20_3, hx21_3, hx26_3, hx13_3, hx27_3, htr3⟩
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗ A.pool ∗
    (memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
     ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
     statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) by ac_rfl)) ?_
  refine states_from_pb_keysUnsampled_step2_5476_5600_placed hA s0 s3 (s0.readReg64 .x30)
    (s0.sp - 2400#64) out ga auth
    (memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 152 ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗ memRegion (s0.sp - 2400#64 + 160#64) 48 ∗
     ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗ memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗
     statesFromPbSavedCells s0 ∗ vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
     vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt) R _
    hfsp_align hpc3 hrun3 hsp3 hx19_3 hx23_3 hx22_3 hx24_3 hx20_3 hx21_3 hx26_3 hx13_3 hx27_3 htr3 ?_
  intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx23_4, hx22_4, hx24_4, hx20_4, hx21_4, hx26_4, hx13_4, hx27_4, htr4⟩
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
    memRegion (s0.sp - 2400#64) 152 ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ ep) ∗
    memRegion (s0.sp - 2400#64 + 160#64) 48 ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗
    memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
    vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr ∗
    vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
    vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) (s4.readReg64 .x25) auth.macKey ∗
    memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool by ac_rfl)) ?_
  exact SepWPp.of_sepWP_ret (states_from_pb_keysUnsampled_step3_5600_ret_placed hA s0 s4
    (s0.sp - 2400#64) out pbA ep pa1 ga auth hr_lt63 hsp0_align rfl
    hpc4 hrun4 hsp4 hx19_4 hx23_4 hx22_4 hx24_4 hx20_4 hx21_4 hx26_4 hx13_4 hx27_4 htr4)

theorem states_from_pb_keysUnsampled_156_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s1 : State) (out pbA : BitVec 64)
    (s : V1State.Chunked.KeysUnsampled) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.keysUnsampled s)) ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.keysUnsampled s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  cases s with | mk uc =>
  cases uc with
  | none =>
    dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt, optProtoUnchunkedKeysUnsampledAt]
    have h16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
    rw [h16]; simp only [sepConj_assoc]
    exact SepWPp.of_sepWP_ret (states_from_pb_keysUnsampled_uc_none_placed (ext := ext) s0 s1 out pbA hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  | some uc =>
    cases uc with | mk ep auth =>
    cases auth with
    | none =>
      dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedKeysUnsampledAt,
        optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt, optProtoAuthenticatorAt]
      have h16 : (pbA + 8#64) + 8#64 = pbA + 16#64 := by bv_omega
      have h56 : (pbA + 8#64) + 48#64 = pbA + 56#64 := by bv_omega
      rw [h16, h56]; simp only [sepConj_assoc]
      exact SepWPp.of_sepWP_ret (states_from_pb_keysUnsampled_auth_none_placed (ext := ext) s0 s1 out pbA ep hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
    | some auth =>
      rw [optProtoInnerStateAt_keysUnsampled_some_eq]; simp only [sepConj_assoc]
      exact states_from_pb_keysUnsampled_some_placed hA s0 s1 out pbA ep auth R hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx27_1 htr1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced (
  FromPbAllocHooks
  fromPb_externAt?_handleError
  states_from_pb_keysUnsampled_uc_none_placed
  states_from_pb_keysUnsampled_auth_none_placed
  states_from_pb_epilogue_8176_keysUnsampled_placed
  states_from_pb_keysUnsampled_step0_156_200_placed
  states_from_pb_keysUnsampled_step1_200_5476_placed
  states_from_pb_keysUnsampled_step2_5476_5600_placed
  states_from_pb_keysUnsampled_step3_5600_ret_placed
  states_from_pb_keysUnsampled_some_placed
  states_from_pb_keysUnsampled_156_placed
)
end CryptoVerification.SpqrV1.States.FromPb
