/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledUc
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded Placed Inner `Unchunked.Ct1SentEkReceived` Lemmas for `Chunked.EkReceivedCt1Sampled::merge` (Block `310`)

Proves the cross-block error exits and inlined `Unchunked.Ct1SentEkReceived` field-merge loop of
`Chunked.EkReceivedCt1Sampled::merge` on Block `310` with `withLsCodeRoLoaded lsmpl` callee contracts.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

@[local simp, local arm64_norm]
private theorem bv64_add72_add8 (a : BitVec 64) : a + 72#64 + 8#64 = a + 80#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add72_add16 (a : BitVec 64) : a + 72#64 + 16#64 = a + 88#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add72_add24 (a : BitVec 64) : a + 72#64 + 24#64 = a + 96#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add72_add32 (a : BitVec 64) : a + 72#64 + 32#64 = a + 104#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add72_add40 (a : BitVec 64) : a + 72#64 + 40#64 = a + 112#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add88_add8 (a : BitVec 64) : a + 88#64 + 8#64 = a + 96#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add104_add8 (a : BitVec 64) : a + 104#64 + 8#64 = a + 112#64 := by bv_omega

private def vecU8CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr bs

private theorem unchunked5CapAt_eq (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5CapAt A a bsLen epoch auth v3 v4 v5 =
      vecU8CapAt A a bsLen v3 ∗ vecU8CapAt A (a + 0x18#64) bsLen v4 ∗
      vecU8CapAt A (a + 0x30#64) bsLen v5 ∗
      optAuthenticatorPBCapAt A (a + 0x48#64) bsLen auth ∗ ((a + 0x78#64) ↦₆₄ epoch) := rfl

private theorem unchunked5CapAt_eq_ek (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5CapAt A a bsLen epoch auth v3 v4 v5 =
      vecU8CapAt A (a + 0x18#64) bsLen v4 ∗ vecU8CapAt A a bsLen v3 ∗
      vecU8CapAt A (a + 0x30#64) bsLen v5 ∗
      optAuthenticatorPBCapAt A (a + 0x48#64) bsLen auth ∗ ((a + 0x78#64) ↦₆₄ epoch) := by
  rw [unchunked5CapAt_eq]; ac_rfl

private theorem unchunked5CapAt_eq_ct1 (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5CapAt A a bsLen epoch auth v3 v4 v5 =
      vecU8CapAt A (a + 0x30#64) bsLen v5 ∗ vecU8CapAt A a bsLen v3 ∗
      vecU8CapAt A (a + 0x18#64) bsLen v4 ∗
      optAuthenticatorPBCapAt A (a + 0x48#64) bsLen auth ∗ ((a + 0x78#64) ↦₆₄ epoch) := by
  rw [unchunked5CapAt_eq]; ac_rfl

private theorem unchunked5CapAt_eq_auth (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5CapAt A a bsLen epoch auth v3 v4 v5 =
      optAuthenticatorPBCapAt A (a + 0x48#64) bsLen auth ∗
      vecU8CapAt A a bsLen v3 ∗ vecU8CapAt A (a + 0x18#64) bsLen v4 ∗
      vecU8CapAt A (a + 0x30#64) bsLen v5 ∗ ((a + 0x78#64) ↦₆₄ epoch) := by
  rw [unchunked5CapAt_eq]; ac_rfl

private theorem vecU8CapAt_mono' (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    {m n : Nat} (hle : m ≤ n) :
    vecU8CapAt A a n bs ⊢ vecU8CapAt A a m bs :=
  vecU8CapAt_mono A a bs hle

private theorem vecU8CapAt_entails_vecU8' (A : RustAlloc) (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) :
    vecU8CapAt A a n bs ⊢ rustBytesVecAt A a bs :=
  vecU8CapAt_entails_vecU8 A a n bs

private theorem vecU8At_entails_vecU8CapAt (A : RustAlloc) (a cap ptr : BitVec 64) (n : Nat)
    (bs : List (BitVec 8)) (hcap : BytesMergeCapOk cap n) :
    vecU8At A a cap ptr bs ⊢ vecU8CapAt A a n bs := by
  unfold vecU8CapAt
  refine Entails.trans (Entails.pure_right hcap (Entails.refl _)) ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

/-- Shared exit from `+0x078` (`(blkPl_310).base + 120#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)` and returns. -/
theorem chunkedEkReceivedCt1Sampled_from_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.EkReceivedCt1Sampled} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_310).base + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedEkReceivedCt1SampledErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := (s0.sp - 128#64, w))
    (ret_pc := (blkPl_310).base + 128#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorFromSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedEkReceivedCt1SampledMergeSpec
  simp only [decodeErrorFromSpec, hnone, chunkedInlSavedRegs10,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le3_inl A _) (by sep_focus)
  apply SepWP.fold (chunkedEkReceivedCt1SampledPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
  wp_done
/-- Inner error exit at `+0x328` (`(blkPl_310).base + 808#64`): pushes `("EkReceivedCt1Sampled", "uc")` onto `x1 = err` (`n ≤ 2`) and returns. -/
theorem chunkedEkReceivedCt1Sampled_uc_push_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.EkReceivedCt1Sampled} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_310).base + 808#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err n ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        memRegion (s0.sp - 128#64) 48 ∗
        chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hret := @chunkedEkReceivedCt1Sampled_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_cells1_160 s0.sp, chunkedEkReceivedCt1SampledErrFrame]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := (s0.sp - 128#64, err, n))
    (ret_pc := (blkPl_310).base + 844#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx1]; rfl)
    (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeErrorPushSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 128#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps; apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Inner error exit at `+0x31c` (`(blkPl_310).base + 796#64`): calls `DecodeError::from` on `(s0.sp - 128#64, w)` and chains into `uc_push_exit`. -/
theorem chunkedEkReceivedCt1Sampled_uc_from_push_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.EkReceivedCt1Sampled} {s : State} {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_310).base + 796#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedEkReceivedCt1Sampled_uc_push_exit_cl_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedEkReceivedCt1SampledErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := (s0.sp - 128#64, w))
    (ret_pc := (blkPl_310).base + 804#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorFromSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 808#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
  exact hpush hnone (by decide : 0 ≤ 2) hsm0 hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Inner field error exit at `+0x470` (`(blkPl_310).base + 1136#64`): calls `DecodeError::push` on `(s0.sp - 128#64, err, n)` (`n ≤ 1`),
loads `x1` from `[sp]`, and jumps to `uc_push_exit` (`+0x328`). -/
theorem chunkedEkReceivedCt1Sampled_uc_field_push_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.EkReceivedCt1Sampled} {s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hn : n ≤ 1) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_310).base + 1136#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
        memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
        chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hpush := @chunkedEkReceivedCt1Sampled_uc_push_exit_cl_placed _ A H hPushCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedEkReceivedCt1SampledErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := (s0.sp - 128#64, err, n))
    (ret_pc := (blkPl_310).base + 1140#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeErrorPushSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 808#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps; apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
  exact hpush hnone (by omega : n + 1 ≤ 2) herr hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-! ## 1. Inner `Unchunked.Ct1SentEkReceived` Field Steps -/
/-- Step lemma for unknown field tags in `Unchunked.Ct1SentEkReceived` (`tag ∉ {1, 2, 3, 4, 5}`) at `+0x284` (`(blkPl_310).base + 644#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_skip_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hSkipCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest')
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedEkReceivedCt1Sampled_uc_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField97 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_310).base + 656#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [skipField3Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 808#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr rest.length uc sendingCt1) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 404#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (unchunked5CapAt_mono A x.msgPtr uc.epoch uc.auth uc.es uc.ek uc.ct1 hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Step lemma for tag 1 (`epoch : u64`) in `Unchunked.Ct1SentEkReceived` when `iwt = .varint` at `+0x260` (`(blkPl_310).base + 608#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_tag1_varint_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.Ct1SentEkReceived}
    {sendingCt1 : Option PolynomialEncoder} {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with epoch := v } sendingCt1 x.bs rest')
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 608#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedEkReceivedCt1Sampled_uc_field_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨x.bufRef, x.slot, restPtr, rest⟩) (ret_pc := (blkPl_310).base + 620#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl) hrest_lt (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 1136#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr rest.length uc sendingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 404#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hdv, unchunked5CapAt_eq, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.es hrest'_le) (by sep_focus); apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x18#64) uc.ek hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x30#64) uc.ct1 hrest'_le) (by sep_focus); apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x48#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with epoch := v } sendingCt1 x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre]; rw [unchunked5CapAt_eq]; sep_entail)
    exact hcont v rest' _ hdv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Step lemma for tag 1 (`epoch : u64`) wire-type error (`iwt ≠ .varint`) at `+0x260` (`(blkPl_310).base + 608#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_tag1_wt_err_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hpc : s.pc = (blkPl_310).base + 608#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hcbnz_wt : (BitVec.ofNat 64 iwt.toNat == 0#64) = false := iwt_cbnz_true_of_ne_varint hiwt
  have hfpush := @chunkedEkReceivedCt1Sampled_uc_field_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 261)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, chunkedInlBelow_decodeErrorHook s0.sp, memRegion_48_wtErr160 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
  apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr rest.length uc sendingCt1) (by sep_focus); wp_reach
  refine SepWPpLscro.call_frame_lscro (x := (s0.sp - 128#64, 0x8000000000000006#64)) (ret_pc := (blkPl_310).base + 1064#64) hFromCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeErrorFromSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 1136#64)
  (conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm⟩
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0; wp_steps; wp_reach
  apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
    (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
  exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
private theorem chunkedEkReceivedCt1Sampled_uc_auth_init_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 548#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      s'.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) → s'.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (vecU8CapAt A x.msgPtr rest.length uc.es ∗ vecU8CapAt A (x.msgPtr + 0x18#64) rest.length uc.ek ∗
          vecU8CapAt A (x.msgPtr + 0x30#64) rest.length uc.ct1 ∗ authenticatorPBCapAt A (x.msgPtr + 0x48#64) rest.length (uc.auth.getD default) ∗
          ((x.msgPtr + 0x78#64) ↦₆₄ uc.epoch) ∗ optPolynomialEncoderPBAt A (x.msgPtr + 128#64) sendingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 524#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs;
  rcases hauth : uc.auth with _ | auth
  · rw [hauth] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 548#64)
    conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, unchunked5CapAt_eq_auth, hauth, optAuthenticatorPBCapAt, memRegion_40_cells (x.msgPtr + 0x48#64)]
    simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; wp_steps
    have hdef := default_cells_entails_authenticatorPBCapAt A (x.msgPtr + 0x48#64) rest.length
    simp only [arm64_norm] at hdef; apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := vecU8CapAt A x.msgPtr rest.length uc.es ∗ vecU8CapAt A (x.msgPtr + 0x18#64) rest.length uc.ek ∗ vecU8CapAt A (x.msgPtr + 0x30#64) rest.length uc.ct1 ∗ authenticatorPBCapAt A (x.msgPtr + 0x48#64) rest.length default ∗ ((x.msgPtr + 0x78#64) ↦₆₄ uc.epoch) ∗ optPolynomialEncoderPBAt A (x.msgPtr + 128#64) sendingCt1 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (by sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
  · rw [hauth] at hcont; dsimp only [Option.getD] at hcont
    let macCap : SepProp := ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x48#64 + 0x18#64) cap ptr auth.macKey
    have hcmn_in : authenticatorPBCapAt A (x.msgPtr + 0x48#64) rest.length auth ⊢
        ∃∗ cap_ik : BitVec 64, ∃∗ ptr_ik : BitVec 64, ⌜cap_ik.toNat < 2 ^ 63 ∧ BytesMergeCapOk cap_ik rest.length⌝ ∗
          ((x.msgPtr + 72#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 80#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 88#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap := by
      have hlt_buf : ∀ (cap ptr : BitVec 64) (bs : List (BitVec 8)), vecU8Buf A cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A cap ptr bs := by
        intro cap ptr bs; unfold vecU8Buf; refine Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))
      have hlt_at : ∀ (a cap ptr : BitVec 64) (bs : List (BitVec 8)),
          vecU8At A a cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
        intro a cap ptr bs; rw [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.trans (sepConj_mono_right (hlt_buf cap ptr bs)) (by sep_entail)
      change (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x48#64) cap ptr auth.rootKey) ∗ macCap ⊢ _
      rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun cap_ik => ?_
      rw [sepExists_sepConj_left]; refine ProofLib.Entails.sepExists_elim fun ptr_ik => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
      rw [sepConj_assoc]; refine Entails.pure_left fun hcap => ?_
      refine Entails.trans (sepConj_mono_left (hlt_at (x.msgPtr + 0x48#64) cap_ik ptr_ik auth.rootKey)) ?_
      simp only [sepConj_assoc, bv64_add72_add8, bv64_add72_add16]
      exact Entails.pure_left fun hlt => Entails.pure_right ⟨hlt, hcap⟩ (Entails.refl _)
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 548#64)
    conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, unchunked5CapAt_eq_auth, hauth, optAuthenticatorPBCapAt]
    simp only [sepConj_assoc]; apply SepWP.fold hcmn_in (by sep_focus); wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik; apply SepWP.pure_elim; rintro ⟨hcap_lt, hcap_ik⟩
    have hcmn1 := cap_add_one_beq_zero_false hcap_lt; have hcmn2 := cap_add_one_bne_zero_true hcap_lt; wp_steps
    have hcmn_out : ((x.msgPtr + 72#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 80#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 88#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap ⊢
        authenticatorPBCapAt A (x.msgPtr + 0x48#64) rest.length auth := by
      change ((x.msgPtr + 72#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 80#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 88#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey ∗ macCap ⊢
        (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x48#64) cap ptr auth.rootKey) ∗ macCap
      refine Entails.trans (Entails.of_eq (show _ = (((x.msgPtr + 72#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 80#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 88#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey) ∗ macCap by ac_rfl)) ?_
      refine sepConj_mono_left ?_
      have hhdr : ((x.msgPtr + 72#64) ↦₆₄ cap_ik) ∗ ((x.msgPtr + 80#64) ↦₆₄ ptr_ik) ∗ ((x.msgPtr + 88#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ vecU8Buf A cap_ik ptr_ik auth.rootKey ⊢
          vecU8At A (x.msgPtr + 0x48#64) cap_ik ptr_ik auth.rootKey := by
        rw [vecU8At_eq_header_sep_buf, vecHeader]; simp only [bv64_add72_add8, bv64_add72_add16]; sep_entail
      refine Entails.trans hhdr ?_; refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
      exact Entails.pure_right hcap_ik (Entails.refl _)
    apply SepWP.fold hcmn_out (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := vecU8CapAt A x.msgPtr rest.length uc.es ∗ vecU8CapAt A (x.msgPtr + 0x18#64) rest.length uc.ek ∗ vecU8CapAt A (x.msgPtr + 0x30#64) rest.length uc.ct1 ∗ authenticatorPBCapAt A (x.msgPtr + 0x48#64) rest.length auth ∗ ((x.msgPtr + 0x78#64) ↦₆₄ uc.epoch) ∗ optPolynomialEncoderPBAt A (x.msgPtr + 128#64) sendingCt1 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool)
      (by sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm]) (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
/-- Step lemma for tag 2 (`auth : Option<Authenticator>`) in `Unchunked.Ct1SentEkReceived` at `+0x20c` (`(blkPl_310).base + 524#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_tag2_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.Ct1SentEkReceived}
    {sendingCt1 : Option PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_auth : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (auth' : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption = some (auth', rest') →
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with auth := some auth' } sendingCt1 x.bs rest')
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 524#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  refine chunkedEkReceivedCt1Sampled_uc_auth_init_placed ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := fun (auth' : ProtoAuthenticator) => @chunkedEkReceivedCt1Sampled_uc_field_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some { uc with auth := some auth' }, sendingCt1 := sendingCt1 }
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 295)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_authMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x48#64, uc.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_310).base + 560#64) hAuthCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [authMergeSpec]; simp only [arm64_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; rfl)
    hrest_lt (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [authMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hauth_res : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (uc.auth.getD default) rest 97).toOption with
  | none =>
    have hnone := hnone_of_auth hauth_res
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 1136#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro auth'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A x.msgPtr rest.length uc.es) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A (x.msgPtr + 0x18#64) rest.length uc.ek) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A (x.msgPtr + 0x30#64) rest.length uc.ct1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some { uc with auth := some auth' }, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame, chunkedEkReceivedCt1SampledPBAt, optCt1SentEkReceivedPBAt, ct1SentEkReceivedPBAt, unchunked5At, optAuthenticatorPBAt]; sep_entail)
    exact hfpush auth' hnone hn_err hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨auth', rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 404#64)
    (conv => arg 4; simp only [authMergeSpec, hauth_res, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.es hrest'_le) (by sep_focus); apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x18#64) uc.ek hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x30#64) uc.ct1 hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with auth := some auth' } sendingCt1 x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre]; rw [unchunked5CapAt_eq]; dsimp only [optAuthenticatorPBCapAt]; sep_entail)
    exact hcont auth' rest' _ hauth_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Step lemma for tag 3 (`es : Vec<u8>` at `x.msgPtr`) in `Unchunked.Ct1SentEkReceived` at `+0x238` (`(blkPl_310).base + 568#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_tag3_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State} {uc : V1State.Unchunked.Ct1SentEkReceived}
    {sendingCt1 : Option PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with es := v } sendingCt1 x.bs rest')
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 568#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedEkReceivedCt1Sampled_uc_field_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }

  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 290)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, unchunked5CapAt_eq, vecU8CapAt,
    sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro cap1; apply SepWP.exists_elim; intro ptr1; apply SepWP.pure_elim; intro hcap1; wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr, cap1, ptr1, uc.es, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_310).base + 580#64) hBytesCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap1⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap1 rest.length) (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 1136#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A x.msgPtr cap1 ptr1 uc.es) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A (x.msgPtr + 0x18#64) rest.length uc.ek) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A (x.msgPtr + 0x30#64) rest.length uc.ct1) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (x.msgPtr + 0x48#64) rest.length uc.auth) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame, chunkedEkReceivedCt1SampledPBAt, optCt1SentEkReceivedPBAt, ct1SentEkReceivedPBAt, unchunked5At]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 404#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap1'; apply SepWP.exists_elim; intro ptr1'; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap1'⟩
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapAt A x.msgPtr cap1' ptr1' rest'.length v hcap1') (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x18#64) uc.ek hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x30#64) uc.ct1 hrest'_le) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x48#64) uc.auth hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with es := v } sendingCt1 x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre]; rw [unchunked5CapAt_eq]; sep_entail)
    exact hcont v rest' _ hmb (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Step lemma for tag 4 (`ek : Vec<u8>` at `x.msgPtr + 0x18#64`) in `Unchunked.Ct1SentEkReceived` at `+0x24c` (`(blkPl_310).base + 588#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_tag4_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with ek := v } sendingCt1 x.bs rest')
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 588#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedEkReceivedCt1Sampled_uc_field_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }

  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 290)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, unchunked5CapAt_eq_ek, vecU8CapAt,
    sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro cap2; apply SepWP.exists_elim; intro ptr2; apply SepWP.pure_elim; intro hcap2; wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, uc.ek, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_310).base + 600#64) hBytesCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap2⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap2 rest.length) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 1136#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A x.msgPtr rest.length uc.es) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A (x.msgPtr + 0x18#64) cap2 ptr2 uc.ek) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A (x.msgPtr + 0x30#64) rest.length uc.ct1) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (x.msgPtr + 0x48#64) rest.length uc.auth) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame, chunkedEkReceivedCt1SampledPBAt, optCt1SentEkReceivedPBAt, ct1SentEkReceivedPBAt, unchunked5At]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 404#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap2'; apply SepWP.exists_elim; intro ptr2'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap2'⟩
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.es hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapAt A (x.msgPtr + 0x18#64) cap2' ptr2' rest'.length v hcap2') (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x30#64) uc.ct1 hrest'_le) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x48#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with ek := v } sendingCt1 x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre]; rw [unchunked5CapAt_eq]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Step lemma for tag 5 (`ct1 : Vec<u8>` at `x.msgPtr + 0x30#64`) in `Unchunked.Ct1SentEkReceived` at `+0x1e8` (`(blkPl_310).base + 488#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_tag5_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with ct1 := v } sendingCt1 x.bs rest')
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 488#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedEkReceivedCt1Sampled_uc_field_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }

  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 290)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, unchunked5CapAt_eq_ct1, vecU8CapAt,
    sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro cap3; apply SepWP.exists_elim; intro ptr3; apply SepWP.pure_elim; intro hcap3; wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x30#64, cap3, ptr3, uc.ct1, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_310).base + 500#64) hBytesCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap3⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap3 rest.length) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 1136#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_cells1_160 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A x.msgPtr rest.length uc.es) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8' A (x.msgPtr + 0x18#64) rest.length uc.ek) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A (x.msgPtr + 0x30#64) cap3 ptr3 uc.ct1) (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (x.msgPtr + 0x48#64) rest.length uc.auth) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame, chunkedEkReceivedCt1SampledPBAt, optCt1SentEkReceivedPBAt, ct1SentEkReceivedPBAt, unchunked5At]; sep_entail)
    exact hfpush hnone (by decide : 0 ≤ 1) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 404#64)
    (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro cap3'; apply SepWP.exists_elim; intro ptr3'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap3'⟩
    apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A x.msgPtr uc.es hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono' A (x.msgPtr + 0x18#64) uc.ek hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapAt A (x.msgPtr + 0x30#64) cap3' ptr3' rest'.length v hcap3') (by sep_focus)
    apply SepWP.fold (optAuthenticatorPBCapAt_mono A (x.msgPtr + 0x48#64) uc.auth hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc with ct1 := v } sendingCt1 x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre]; rw [unchunked5CapAt_eq]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
      ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-! ## 2. Inner Loop Exit Lemma -/
/-- Inner loop exit at `+0x194` (`(blkPl_310).base + 404#64`) when `cur.length ≤ innerLimit`. -/
theorem chunkedEkReceivedCt1Sampled_uc_loop_le_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hle_lim : cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : innerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < innerLimit →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (s' : State),
      cur.length = innerLimit →
      s'.pc = (blkPl_310).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs cur)
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs cur)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = innerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 168#64)
    conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
    simp only [sepConj_assoc]; wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs cur)
      (by dsimp only [chunkedEkReceivedCt1SampledLoopPre, chunkedEkReceivedCt1SampledPBCapAt, optCt1SentEkReceivedPBCapAt, sliceCursorAfter]; simp only [arm64_norm]; sep_entail)
    exact hcont _ heq_lim (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24]) (by simp only [arm64_norm, hx25])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · have hlt_lim : cur.length < innerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_push := @chunkedEkReceivedCt1Sampled_uc_from_push_exit_cl_placed _ A H hFromCall hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }

    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 796#64)
    conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr cur.length uc sendingCt1) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

end CryptoVerification.SpqrV1.Prost.MessageMerge
