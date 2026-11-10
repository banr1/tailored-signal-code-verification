/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>` Phase 1b: Inner-State Unpack (`+156..+224`)

**Checked by Lean.**

Verifies `spqr_send_inner_none_step` (`+156 -> s0.lr` when `pq.inner = none`, returning
`Ok(Send { state: [], msg: [], key: None })`) and `spqr_send_inner_some_to_224`
(`+156 -> +224` when `pq.inner = some (.v1 v1)`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_add_add_lit1 bv_add_add_lit2

/-! ## `pq.inner = none` Return Path (`+156 -> s0.lr`) -/

/-- Reassemble `(a30 ↦₆₄ w0) ∗ ((a30 + 8#64) ↦₆₄ w1) ∗ DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) vn`
    after writing `w0, w1, w2, w3` to `[a30 .. a30 + 32)`. -/
theorem reassemble_optVersionNegotiationPBTail_raw (A : RustAlloc) (a30 : BitVec 64)
    (w0 w1 w2 w3 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB)
    (hlen16 : bs16.length = 16) :
    (a30 ↦₆₄ w0) ∗
      ((a30 + 8#64) ↦₆₄ w1) ∗
      ((a30 + 16#64) ↦₆₄ w2) ∗
      ((a30 + 24#64) ↦₆₄ w3) ∗
      ((a30 + 32#64) ↦ₛ bs16) ∗
      (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
        ((unpack64 w2 ++ unpack64 w3) ++ bs16) ⊢
      (a30 ↦₆₄ w0) ∗
      ((a30 + 8#64) ↦₆₄ w1) ∗
      DecodeState.optVersionNegotiationPBTailAt A w0 w1 (a30 + 16#64) vn :=
  sepConj_mono_right (reassemble_optVersionNegotiationPBTail A a30 w0 w1 w2 w3 bs16 vn hlen16)

theorem memRegion_sendResult_split_56 (ret : BitVec 64) :
    memRegion ret 72 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r8 : BitVec 64, ∃∗ r16 : BitVec 64, ∃∗ r24 : BitVec 64,
      ∃∗ r32 : BitVec 64, ∃∗ r40 : BitVec 64, ∃∗ r48 : BitVec 64,
        (ret ↦₆₄ r0) ∗
        ((ret + 8#64) ↦₆₄ r8) ∗
        ((ret + 16#64) ↦₆₄ r16) ∗
        ((ret + 24#64) ↦₆₄ r24) ∗
        ((ret + 32#64) ↦₆₄ r32) ∗
        ((ret + 40#64) ↦₆₄ r40) ∗
        ((ret + 48#64) ↦₆₄ r48) ∗
        memRegion (ret + 56#64) 16 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 64)
        (b' := ret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 8) (k := 56)
        (b' := ret + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 16#64) (n := 8) (k := 48)
        (b' := ret + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 24#64) (n := 8) (k := 40)
        (b' := ret + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 32)
        (b' := ret + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 40#64) (n := 8) (k := 24)
        (b' := ret + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 48#64) (n := 8) (k := 16)
        (b' := ret + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret,
      ProofLib.memRegion_eight (ret + 8#64),
      ProofLib.memRegion_eight (ret + 16#64),
      ProofLib.memRegion_eight (ret + 24#64),
      ProofLib.memRegion_eight (ret + 32#64),
      ProofLib.memRegion_eight (ret + 40#64),
      ProofLib.memRegion_eight (ret + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro r48
  apply Entails.sepExists_elim; intro r40
  apply Entails.sepExists_elim; intro r32
  apply Entails.sepExists_elim; intro r24
  apply Entails.sepExists_elim; intro r16
  apply Entails.sepExists_elim; intro r8
  apply Entails.sepExists_elim; intro r0
  refine Entails.sepExists_right r0
    (Entails.sepExists_right r8
      (Entails.sepExists_right r16
        (Entails.sepExists_right r24
          (Entails.sepExists_right r32
            (Entails.sepExists_right r40
              (Entails.sepExists_right r48 ?_))))))
  exact Entails.of_eq (by ac_rfl)

theorem empty_vecU8_entails (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A a [] := by
  unfold vecU8
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  unfold vecU8At vecHeader
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 := by decide
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [h0, ↓reduceIte, sepConj_emp]
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem empty_ok_sendResult_entails (A : RustAlloc) (ret : BitVec 64) :
    (ret ↦₆₄ 0#64) ∗
      ((ret + 8#64) ↦₆₄ 1#64) ∗
      ((ret + 16#64) ↦₆₄ 0#64) ∗
      ((ret + 24#64) ↦₆₄ 0#64) ∗
      ((ret + 32#64) ↦₆₄ 1#64) ∗
      ((ret + 40#64) ↦₆₄ 0#64) ∗
      ((ret + 48#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
      memRegion (ret + 56#64) 16 ⊢
      spqrSendResultAt A ret (some ([], none, [])) := by
  unfold spqrSendResultAt spqrSendKeyAt
  dsimp only
  have hlen : ([] : List (BitVec 8)).length < 2 ^ 32 := by decide
  have hv1 := empty_vecU8_entails A ret
  have hv2 := empty_vecU8_entails A (ret + 24#64)
  have ha32 : (ret + 24#64) + 8#64 = ret + 32#64 := by bv_omega
  have ha40 : (ret + 24#64) + 16#64 = ret + 40#64 := by bv_omega
  rw [ha32, ha40] at hv2
  have ha56 : (ret + 48#64) + 8#64 = ret + 56#64 := by bv_omega
  rw [ha56]
  refine Entails.pure_right hlen ?_
  refine Entails.trans
    (Entails.of_eq (show _ =
      ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64)) ∗
      (((ret + 24#64) ↦₆₄ 0#64) ∗ ((ret + 32#64) ↦₆₄ 1#64) ∗ ((ret + 40#64) ↦₆₄ 0#64)) ∗
      (((ret + 48#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗ memRegion (ret + 56#64) 16) by ac_rfl)) ?_
  exact sepConj_mono hv1 (sepConj_mono_left hv2)

theorem inner_none_b0_rejoin (fsp : BitVec 64) (w1 w2 w3 : BitVec 64) :
    ((fsp + 0xb0#64) ↦₆₄ DecodeState.none3Cap) ∗
      memRegion (fsp + 0xb8#64) 216 ∗
      ((fsp + 0x190#64) ↦₆₄ w1) ∗
      ((fsp + 0x198#64) ↦₆₄ w2) ∗
      ((fsp + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1a8#64) (0x1f20 - 0x1a8) ⊢
      memRegion (fsp + 0xb0#64) (0x1f20 - 0xb0) := by
  have hinner : ((fsp + 0xb0#64) ↦₆₄ DecodeState.none3Cap) ∗ memRegion (fsp + 0xb8#64) 216 ⊢
      memRegion (fsp + 0xb0#64) 224 := by
    rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 8) (k := 216)
          (b' := fsp + 0xb8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0xb0#64) DecodeState.none3Cap)
  rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 224) (k := 0x1f20 - 0x190)
        (b' := fsp + 0x190#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x190#64) (n := 8) (k := 0x1f20 - 0x198)
        (b' := fsp + 0x198#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x198#64) (n := 8) (k := 0x1f20 - 0x1a0)
        (b' := fsp + 0x1a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1a0#64) (n := 8) (k := 0x1f20 - 0x1a8)
        (b' := fsp + 0x1a8#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((fsp + 0xb0#64) ↦₆₄ DecodeState.none3Cap) ∗ memRegion (fsp + 0xb8#64) 216) ∗
      ((fsp + 0x190#64) ↦₆₄ w1) ∗
      ((fsp + 0x198#64) ↦₆₄ w2) ∗
      ((fsp + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1a8#64) (0x1f20 - 0x1a8) by ac_rfl)) ?_
  exact sepConj_mono hinner
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x190#64) w1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x198#64) w2)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1a0#64) w3))))

@[local simp, local arm64_norm, local wp_norm]
theorem none3Cap_add_three_beq_zero :
    (DecodeState.none3Cap + 3#64 == 0#64) = true ∧
    (DecodeState.none3Cap + 3#64 != 0#64) = false := by decide

theorem slt_one_false_iff {w0 : BitVec 64} (h : BitVec.slt w0 1#64 = false) :
    BitVec.sle 1#64 w0 = true := by
  revert h; bv_bits

theorem slt_one_true_iff {w0 : BitVec 64} (h : BitVec.slt w0 1#64 = true) :
    (!BitVec.slt w0 1#64) = false := by
  rw [h]; rfl

/-- `pq.inner = none` path from `+156` to `s0.lr` (`0x308f8..0x30938`):
    loads `[sp + 0xb0] = none3Cap`, finishes relocating `pq.versionNegotiation` to `sp + 0x30`,
    writes `Ok(Send { state: [], msg: [], key: None })` to `*ret`, and drops
    `pq.versionNegotiation` and `pq.chain` before returning. -/
theorem spqr_send_inner_none_step {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hdropChain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    (s0 s : State) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hlen16 : bs16.length = 16)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) none ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          spqrSendResultAt A ret (some ([], none, [])) ∗
          A.pool ∗
          stackAt s0.sp spqrSendStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  by_cases hslt : BitVec.slt w0 1#64 = true
  · have hge_false := slt_one_true_iff hslt
    refine EncoderFromPb.seq_clean
      (mid := spqrSendEntry b + 4608#64)
      (P_mid :=
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool ∗
        (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest))
      (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
      spqr_send_fetches_range b (Rust.withPanics ext) 156 68
      dsimp only [tripleRatchetProgAtExt, spqrSendName, DecodeState.optProtoPqRatchetInnerAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_session::HookRng>" = entry
      examples_hide_fetches
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 ⊢
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left (memRegion_sendResult_split_56 ret)))))))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro r8
      apply ProofLib.SepWP.exists_left; intro r16
      apply ProofLib.SepWP.exists_left; intro r24
      apply ProofLib.SepWP.exists_left; intro r32
      apply ProofLib.SepWP.exists_left; intro r40
      apply ProofLib.SepWP.exists_left; intro r48
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hvn_raw := reassemble_optVersionNegotiationPBTail_raw A (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
        have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
        have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
        have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
        have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
        rw [ha56, ha64, ha72, ha80] at hvn_raw
        have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
        rw [ha56, ha64, hslt] at hvn_drop
        simp only [↓reduceIte] at hvn_drop
        have hvn48 := Entails.trans hvn_raw hvn_drop
        have h60 : memRegion fsp 48 ∗ memRegion (fsp + 48#64) 48 ⊢ memRegion fsp 96 := by
          rw [memRegion_rejoin_30_48 fsp]
          exact Entails.refl _
        have hb0 := inner_none_b0_rejoin fsp w1 w2 w3
        have hret := empty_ok_sendResult_entails A ret
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion fsp 48 ∗
             (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
              ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
              ((fsp + 80#64) ↦ₛ bs16) ∗
              (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
                ((unpack64 w2 ++ unpack64 w3) ++ bs16))) ∗
            (((fsp + 176#64) ↦₆₄ DecodeState.none3Cap) ∗
             memRegion (fsp + 184#64) 216 ∗
             ((fsp + 400#64) ↦₆₄ w1) ∗
             ((fsp + 408#64) ↦₆₄ w2) ∗
             ((fsp + 416#64) ↦₆₄ w3) ∗
             memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
            ((ret ↦₆₄ 0#64) ∗
             ((ret + 8#64) ↦₆₄ 1#64) ∗
             ((ret + 16#64) ↦₆₄ 0#64) ∗
             ((ret + 24#64) ↦₆₄ 0#64) ∗
             ((ret + 32#64) ↦₆₄ 1#64) ∗
             ((ret + 40#64) ↦₆₄ 0#64) ∗
             ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion (ret + 56#64) 16) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hvn48) h60)
            (sepConj_mono hb0 (sepConj_mono_left hret))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2⟩
      have hep := spqr_send_chain_drop_epilogue_4608 hdropChain s0 s2 chain
        (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩
  · have hslt_f : BitVec.slt w0 1#64 = false := Bool.eq_false_iff.mpr hslt
    have hge_true := slt_one_false_iff hslt_f
    refine SepWP.seq (mid := spqrSendEntry b + 904#64)
      (Mid := fun s1 P1 =>
        0 < w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
          A.live w1 w0.toNat 1 ∗
          memRegion w1 w0.toNat ∗
          ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool ∗
          (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest)) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x23 = w0 ∧
        s1.trace = s.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0)
      ?_ ?_
    · rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
      spqr_send_fetches_range b (Rust.withPanics ext) 156 68
      dsimp only [tripleRatchetProgAtExt, spqrSendName, DecodeState.optProtoPqRatchetInnerAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_session::HookRng>" = entry
      examples_hide_fetches
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 ⊢
      have hvn_raw := reassemble_optVersionNegotiationPBTail_raw A (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
      have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
      have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
      have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
      have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
      rw [ha56, ha64, ha72, ha80] at hvn_raw
      have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
      rw [ha56, ha64, hslt_f] at hvn_drop
      simp only [Bool.false_eq_true, ↓reduceIte] at hvn_drop
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left (memRegion_sendResult_split_56 ret)))))))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro r8
      apply ProofLib.SepWP.exists_left; intro r16
      apply ProofLib.SepWP.exists_left; intro r24
      apply ProofLib.SepWP.exists_left; intro r32
      apply ProofLib.SepWP.exists_left; intro r40
      apply ProofLib.SepWP.exists_left; intro r48
      wp_steps
      have hvn_all := Entails.trans hvn_raw hvn_drop
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
             ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
             ((fsp + 80#64) ↦ₛ bs16) ∗
             (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
               ((unpack64 w2 ++ unpack64 w3) ++ bs16)) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 48 ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             ((fsp + 176#64) ↦₆₄ DecodeState.none3Cap) ∗
             memRegion (fsp + 184#64) 216 ∗
             ((fsp + 400#64) ↦₆₄ w1) ∗
             ((fsp + 408#64) ↦₆₄ w2) ∗
             ((fsp + 416#64) ↦₆₄ w3) ∗
             memRegion (fsp + 424#64) (0x1f20 - 0x1a8) ∗
             (ret ↦₆₄ 0#64) ∗
             ((ret + 8#64) ↦₆₄ 1#64) ∗
             ((ret + 16#64) ↦₆₄ 0#64) ∗
             ((ret + 24#64) ↦₆₄ 0#64) ∗
             ((ret + 32#64) ↦₆₄ 1#64) ∗
             ((ret + 40#64) ↦₆₄ 0#64) ∗
             ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion (ret + 56#64) 16 ∗
             A.pool ∗
             spqrSendSavedRegs fsp s0 ∗
             Rest) by ac_rfl))
          (sepConj_mono_left hvn_all)) ?_
      wp_focus_pure; rintro ⟨hw0_pos, hw0_lt, hw1_ne⟩
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
      refine ⟨hw0_pos, hw0_lt, hw1_ne, ?_,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
      have hb0 := inner_none_b0_rejoin fsp w1 w2 w3
      have hret := empty_ok_sendResult_entails A ret
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((fsp + 176#64) ↦₆₄ DecodeState.none3Cap) ∗
           memRegion (fsp + 184#64) 216 ∗
           ((fsp + 400#64) ↦₆₄ w1) ∗
           ((fsp + 408#64) ↦₆₄ w2) ∗
           ((fsp + 416#64) ↦₆₄ w3) ∗
           memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
          ((ret ↦₆₄ 0#64) ∗
           ((ret + 8#64) ↦₆₄ 1#64) ∗
           ((ret + 16#64) ↦₆₄ 0#64) ∗
           ((ret + 24#64) ↦₆₄ 0#64) ∗
           ((ret + 32#64) ↦₆₄ 1#64) ∗
           ((ret + 40#64) ↦₆₄ 0#64) ∗
           ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion (ret + 56#64) 16) ∗
          (stackAt fsp spqrSendCalleeStack ∗
           memRegion fsp 48 ∗
           memRegion (fsp + 48#64) 8 ∗
           ((fsp + 56#64) ↦₆₄ w1) ∗
           memRegion (fsp + 64#64) 32 ∗
           A.live w1 w0.toNat 1 ∗
           memRegion w1 w0.toNat ∗
           ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
           spqrSendSavedRegs fsp s0 ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hb0 (sepConj_mono_left hret)) ?_
      exact Entails.of_eq (by ac_rfl)
    · intro s1 P1 hpc1 hrun1 ⟨hw0_pos, hw0_lt, hw1_ne, hP1, hsp1, hx23_1, htr1, hvregs1⟩
      refine SepWP.weaken_pre hP1 ?_
      have hep := spqr_send_vn_chain_drop_epilogue_904 hA.dealloc hdropChain s0 s1 w0 w1 chain
        (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest)
        hsp0_align hpc1 hrun1 hsp1 hx23_1 hw0_pos hw0_lt hw1_ne
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr1⟩

/-! ## `pq.inner = some (.v1 v1)` Step (`+156 -> +224`) -/

/-- Remainder of `Drop.optProtoInnerStateAt A a optSt` when its first 8-byte word `a ↦₆₄ w` is exposed. -/
def optProtoInnerStateHeadRest (A : RustAlloc) (a w : BitVec 64)
    (optSt : Option V1State.InnerState) : SepProp :=
  ∃∗ P : SepProp, ⌜(a ↦₆₄ w) ∗ P ⊢ Drop.optProtoInnerStateAt A a optSt⌝ ∗ P

theorem optProtoInnerStateAt_unexpose_head (A : RustAlloc) (a w : BitVec 64)
    (optSt : Option V1State.InnerState) :
    (a ↦₆₄ w) ∗ optProtoInnerStateHeadRest A a w optSt ⊢
      Drop.optProtoInnerStateAt A a optSt := by
  unfold optProtoInnerStateHeadRest
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro P
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hun
  exact hun

private theorem expose_head_of_tag {A : RustAlloc} {a : BitVec 64}
    (tag : BitVec 64) {optSt : Option V1State.InnerState} (P : SepProp)
    (hne : tag ≠ DecodeState.none3Cap)
    (heq : Drop.optProtoInnerStateAt A a optSt = (a ↦₆₄ tag) ∗ P) :
    Drop.optProtoInnerStateAt A a optSt ⊢
      ∃∗ w : BitVec 64,
        ⌜w ≠ DecodeState.none3Cap⌝ ∗
        (a ↦₆₄ w) ∗
        optProtoInnerStateHeadRest A a w optSt := by
  rw [heq]
  refine Entails.sepExists_right tag (Entails.pure_right hne (sepConj_mono_right ?_))
  unfold optProtoInnerStateHeadRest
  exact Entails.sepExists_right P (Entails.pure_right (Entails.of_eq heq.symm) (Entails.refl P))

theorem vecU8_expose_head_ne_none3Cap (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ w : BitVec 64, ∃∗ Q : SepProp,
        ⌜w ≠ DecodeState.none3Cap⌝ ∗ (a ↦₆₄ w) ∗ ⌜(a ↦₆₄ w) ∗ Q ⊢ vecU8 A a bs⌝ ∗ Q := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  let H : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  have heq : vecU8At A a cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗
      (((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H) := by
    unfold vecU8At vecHeader H
    ac_rfl
  rw [heq]
  apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr_ne⟩
  have hne : cap ≠ DecodeState.none3Cap := by
    intro h; rw [h] at hcap_lt
    change 0xfffffffffffffffd < 2 ^ 63 at hcap_lt
    omega
  let Q : SepProp :=
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ H
  have hun : (a ↦₆₄ cap) ∗ Q ⊢ vecU8 A a bs := by
    unfold vecU8
    refine Entails.trans ?_ (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _)))
    rw [heq]
    unfold Q
    exact Entails.of_eq (by ac_rfl)
  refine Entails.sepExists_right cap (Entails.sepExists_right Q ?_)
  refine Entails.pure_right hne (sepConj_mono_right (Entails.pure_right hun ?_))
  unfold Q
  exact Entails.pure_right ⟨hlen, hcap_lt, hptr_ne⟩ (Entails.refl _)

theorem optProtoInnerStateAt_expose_head (A : RustAlloc) (a : BitVec 64)
    (optSt : Option V1State.InnerState) :
    Drop.optProtoInnerStateAt A a optSt ⊢
      ∃∗ w : BitVec 64,
        ⌜w ≠ DecodeState.none3Cap⌝ ∗
        (a ↦₆₄ w) ∗
        optProtoInnerStateHeadRest A a w optSt := by
  cases optSt with
  | none =>
    exact expose_head_of_tag Drop.none2Cap (memRegion (a + 8#64) 216) (by decide) rfl
  | some st =>
    cases st with
    | keysUnsampled s =>
      exact expose_head_of_tag 0x8000000000000000#64
        (Drop.protoChunkedKeysUnsampledAt A (a + 8#64) s ∗ memRegion (a + 64#64) 160)
        (by decide) rfl
    | keysSampled s =>
      exact expose_head_of_tag 0x8000000000000001#64
        (Drop.protoChunkedKeysSampledAt A (a + 8#64) s ∗ memRegion (a + 168#64) 56)
        (by decide) rfl
    | headerSent s =>
      exact expose_head_of_tag 0x8000000000000002#64
        (Drop.protoChunkedHeaderSentAt A (a + 8#64) s ∗ memRegion (a + 184#64) 40)
        (by decide) rfl
    | ct1Received s =>
      exact expose_head_of_tag 0x8000000000000003#64
        (Drop.protoChunkedCt1ReceivedAt A (a + 8#64) s ∗ memRegion (a + 168#64) 56)
        (by decide) rfl
    | ekSentCt1Received s =>
      exact expose_head_of_tag 0x8000000000000004#64
        (Drop.protoChunkedEkSentCt1ReceivedAt A (a + 8#64) s ∗ memRegion (a + 152#64) 72)
        (by decide) rfl
    | noHeaderReceived s =>
      exact expose_head_of_tag 0x8000000000000005#64
        (Drop.protoChunkedNoHeaderReceivedAt A (a + 8#64) s ∗ memRegion (a + 104#64) 120)
        (by decide) rfl
    | headerReceived s =>
      exact expose_head_of_tag 0x8000000000000006#64
        (Drop.protoChunkedHeaderReceivedAt A (a + 8#64) s ∗ memRegion (a + 128#64) 96)
        (by decide) rfl
    | ekReceivedCt1Sampled s =>
      exact expose_head_of_tag 0x8000000000000008#64
        (Drop.protoChunkedEkReceivedCt1SampledAt A (a + 8#64) s ∗ memRegion (a + 192#64) 32)
        (by decide) rfl
    | ct1Acknowledged s =>
      exact expose_head_of_tag 0x8000000000000009#64
        (Drop.protoChunkedCt1AcknowledgedAt A (a + 8#64) s ∗ memRegion (a + 176#64) 48)
        (by decide) rfl
    | ct2Sampled s =>
      exact expose_head_of_tag 0x800000000000000a#64
        (Drop.protoChunkedCt2SampledAt A (a + 8#64) s ∗ memRegion (a + 120#64) 104)
        (by decide) rfl
    | ct1Sampled s =>
      rcases hsuc : s.uc with _ | uc
      · exact expose_head_of_tag noneCap
          (memRegion (a + 8#64) 120 ∗
           Poly.optProtoPolynomialEncoderAt A (a + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
           Poly.optProtoPolynomialDecoderAt A (a + 184#64) (s.receivingEk.map pbToProtoPolyDecoder))
          (by decide) (by
            unfold Drop.optProtoInnerStateAt Drop.protoInnerStateAt
              Drop.protoChunkedCt1SampledAt Drop.optProtoUnchunkedCt1SentAt
            dsimp only; rw [hsuc]; dsimp only; ac_rfl)
      · let R : SepProp :=
          vecU8 A (a + 24#64) uc.es ∗
          vecU8 A (a + 48#64) uc.ct1 ∗
          optProtoAuthenticatorAt A (a + 72#64) uc.auth ∗
          ((a + 120#64) ↦₆₄ uc.epoch) ∗
          Poly.optProtoPolynomialEncoderAt A (a + 128#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
          Poly.optProtoPolynomialDecoderAt A (a + 184#64) (s.receivingEk.map pbToProtoPolyDecoder)
        have heq : Drop.optProtoInnerStateAt A a (some (.ct1Sampled s)) =
            vecU8 A a uc.hdr ∗ R := by
          unfold Drop.optProtoInnerStateAt Drop.protoInnerStateAt
            Drop.protoChunkedCt1SampledAt Drop.optProtoUnchunkedCt1SentAt
            Drop.protoUnchunkedCt1SentAt R
          dsimp only; rw [hsuc]; dsimp only; ac_rfl
        rw [heq]
        refine Entails.trans (sepConj_mono_left (vecU8_expose_head_ne_none3Cap A a uc.hdr)) ?_
        simp only [sepExists_sepConj_left]
        apply Entails.sepExists_elim; intro w
        apply Entails.sepExists_elim; intro Q
        have hpull :
            ((⌜w ≠ DecodeState.none3Cap⌝ ∗ (a ↦₆₄ w) ∗ ⌜(a ↦₆₄ w) ∗ Q ⊢ vecU8 A a uc.hdr⌝ ∗ Q) ∗ R) =
            ⌜w ≠ DecodeState.none3Cap⌝ ∗ ⌜(a ↦₆₄ w) ∗ Q ⊢ vecU8 A a uc.hdr⌝ ∗
              ((a ↦₆₄ w) ∗ (Q ∗ R)) := by ac_rfl
        rw [hpull]
        apply Entails.pure_left; intro hne
        apply Entails.pure_left; intro hunQ
        refine Entails.sepExists_right w (Entails.pure_right hne (sepConj_mono_right ?_))
        unfold optProtoInnerStateHeadRest
        refine Entails.sepExists_right (Q ∗ R) (Entails.pure_right ?_ (Entails.refl _))
        rw [heq, ← sepConj_assoc]
        exact sepConj_mono_left hunQ

theorem rejoin_190_to_1f20 (fsp w1 w2 w3 : BitVec 64) :
    ((fsp + 0x190#64) ↦₆₄ w1) ∗
      ((fsp + 0x198#64) ↦₆₄ w2) ∗
      ((fsp + 0x1a0#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1a8#64) (0x1f20 - 0x1a8) ⊢
      memRegion (fsp + 0x190#64) (0x1f20 - 0x190) := by
  rw [ProofLib.memRegion_split' (b := fsp + 0x190#64) (n := 8) (k := 0x1f20 - 0x198)
        (b' := fsp + 0x198#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x198#64) (n := 8) (k := 0x1f20 - 0x1a0)
        (b' := fsp + 0x1a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1a0#64) (n := 8) (k := 0x1f20 - 0x1a8)
        (b' := fsp + 0x1a8#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x190#64) w1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 0x198#64) w2)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 0x1a0#64) w3)))

theorem ne_none3Cap_add_three_bne_zero_true {w : BitVec 64} (h : w ≠ DecodeState.none3Cap) :
    (w + 3#64 != 0#64) = true := by
  have h1 := ne_none3Cap_add_three_beq_zero_false h
  simpa [bne] using h1

/-- When `pq.inner = some (.v1 v1)`, `+156 -> +224` (`0x308f8..0x30914 -> 0x3093c`) loads `w_in ≠ none3Cap`
    from `[sp + 0xb0]`, completes the 32-byte relocation of `pq.versionNegotiation` into
    `[sp + 0x30..0x50)` (`reassemble_optVersionNegotiationPBTail_raw`), and branches to `+224` (`0x3093c`). -/
theorem spqr_send_inner_some_to_224 {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (s0 s : State) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16) :
    SepWP (tripleRatchetProgAtExt b ext) (spqrSendEntry b + 224#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          Drop.optProtoInnerStateAt A ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          Rest) ∧
        sm.sp = s0.sp - 0x1f80#64 ∧
        sm.readReg64 .x19 = ret ∧
        sm.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64 ∧
        sm.readReg64 .x23 = w0 ∧
        sm.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
  spqr_send_fetches_range b (Rust.withPanics ext) 156 32
  dsimp only [tripleRatchetProgAtExt, spqrSendName, DecodeState.optProtoPqRatchetInnerAt,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [h_inner_eq]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 hx26 ⊢
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (optProtoInnerStateAt_expose_head A (fsp + 176#64) v1.innerState)))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro win
  wp_focus_pure; intro hwin_ne
  have hwin_br := ne_none3Cap_add_three_beq_zero_false hwin_ne
  have hwin_bne := ne_none3Cap_add_three_bne_zero_true hwin_ne
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine ⟨?_,
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *]⟩
  have hvn := reassemble_optVersionNegotiationPBTail_raw A (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
  have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
  have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
  have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
  have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
  rw [ha56, ha64, ha72, ha80] at hvn
  have hin := optProtoInnerStateAt_unexpose_head A (fsp + 176#64) win v1.innerState
  have h190 := rejoin_190_to_1f20 fsp w1 w2 w3
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
       ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
       ((fsp + 80#64) ↦ₛ bs16) ∗
       (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
         ((unpack64 w2 ++ unpack64 w3) ++ bs16)) ∗
      (((fsp + 176#64) ↦₆₄ win) ∗ optProtoInnerStateHeadRest A (fsp + 176#64) win v1.innerState) ∗
      (((fsp + 400#64) ↦₆₄ w1) ∗ ((fsp + 408#64) ↦₆₄ w2) ∗
       ((fsp + 416#64) ↦₆₄ w3) ∗ memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
      (stackAt fsp spqrSendCalleeStack ∗
       memRegion fsp 48 ∗
       ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
       spqrSendSavedRegs fsp s0 ∗
       Rest) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hvn (sepConj_mono hin (sepConj_mono_left h190))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
