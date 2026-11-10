/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: `Ordering::Greater` (`V0ChainTail`)

**Checked by Lean.** Symbolic execution of the `Ordering::Greater` V0 chain-ratchet branch
(`+496..+740`, `+2108..+2420`, `+2920..+2948`) of `spqr::recv` (`0x5462c`), discharging
`V0ChainTail`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

@[simp] private theorem except_bind_ok_iff {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by cases m <;> simp [Bind.bind, Except.bind]
@[simp] private theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] private theorem decoderFromPbStateDecode_none :
    decoderFromPbStateDecode spqrPolyApi none = .error (.err .stateDecode) := rfl
@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (pure x >>= f) = f x := rfl
@[simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl
@[simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'} {m : Except ε α} {a : α} :
    m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]
@[simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]
@[simp] private theorem liftM_spqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    (liftM r : Except StatesPanic α) = .ok v ↔ r = .ok v := by
  cases r <;> simp [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
@[simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε] {r : Except ε α} {v : α} :
    StatesResult.ofPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [StatesResult.ofPanic]

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

@[local simp, local arm64_norm, local wp_norm]
theorem fp_sub_32_add_eq (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551584#64 = sp0 - 128#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_560_eq' (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  change (s0.sp - 688#64) + 560#64 = s0.sp - 128#64
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem fp_sub_48_add_eq (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551568#64 = sp0 - 144#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_544_eq' (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  change (s0.sp - 688#64) + 544#64 = s0.sp - 144#64
  bv_omega

/-! ## 1. `recvKeyErrAt` Exposure and `onPanic` Bridge for `Chain::recv_key` -/

theorem recvKeyErrAt_entails_code_memRegion23 (out : BitVec 64) (e : Error) :
    recvKeyErrAt out e ⊢
      (out ↦₆₄ 1#64) ∗
      ((out + 8#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
      memRegion (out + 9#64) 23 := by
  unfold recvKeyErrAt
  split
  · rename_i epoch
    have h23 :
        memRegion (out + 0x09#64) 7 ∗ ((out + 0x10#64) ↦₆₄ epoch) ∗ memRegion (out + 0x18#64) 8 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 8)
            (b' := out + 0x18#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rename_i ctr atIdx
    have h23 :
        memRegion (out + 0x09#64) 3 ∗ ((out + 0x0c#64) ↦₃₂ ctr) ∗
          ((out + 0x10#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x14#64) 12 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20)
            (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x10#64) (n := 4) (k := 12)
            (b' := out + 0x14#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo32_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _)))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rename_i atIdx
    have h23 :
        memRegion (out + 0x09#64) 3 ∗ ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20)
            (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rename_i atIdx
    have h23 :
        memRegion (out + 0x09#64) 3 ∗ ((out + 0x0c#64) ↦₃₂ atIdx) ∗ memRegion (out + 0x10#64) 16 ⊢
          memRegion (out + 9#64) 23 := by
      rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20)
            (b' := out + 0x0c#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := out + 0x0c#64) (n := 4) (k := 16)
            (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono_right h23)
  · rw [← sepConj_emp ⌜False⌝]; exact Entails.pure_left False.elim

theorem onPanic_of_chainRecvKey {F : ShaCompress} {K : MlKem}
    {st msg : VecArg} {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {chain0 : Chain}
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (s sm : State) :
    (⌜((Chain.recvKey (spqrHkdfWith F) chain0 0#64 pre.index).isPanic = true ∧ sm.trace = s.trace) ∨
        (allocFailedIn s sm ∧ s.trace <+: sm.trace)⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(allocFailedIn s sm ∨ (spqrV1Recv F K).recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left
  rintro (⟨hpan, htr⟩ | ⟨haf, hsub⟩)
  · have hpan_recv := spqrV1Recv_gt_recvKey_panic (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf hpan
    exact Entails.pure_right ⟨Or.inr hpan_recv, htr ▸ List.prefix_refl _⟩ (Entails.refl _)
  · exact Entails.pure_right ⟨Or.inl haf, hsub⟩ (Entails.refl _)

theorem memRegion_88_sub3056_split_32_56 (sp0 : BitVec 64) :
    memRegion (sp0 - 3056#64) 88 =
      memRegion (sp0 - 3056#64) 32 ∗ memRegion (sp0 - 3024#64) 56 :=
  ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 32) (k := 56)
    (b' := sp0 - 3024#64) rfl (by bv_omega) (by decide)

theorem memRegion_872_sub2968_split_ok_680 (sp0 : BitVec 64) :
    memRegion (sp0 - 3024#64) 56 ∗ memRegion (sp0 - 2968#64) 872 =
      (∃∗ u4 : BitVec 64, (sp0 - 3024#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (sp0 - 3016#64) ↦₆₄ u5) ∗
      memRegion (sp0 - 3008#64) 80 ∗
      memRegion (sp0 - 2928#64) 224 ∗
      memRegion (sp0 - 2704#64) 608 := by
  rw [← ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 56) (k := 872)
        (b' := sp0 - 2968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3024#64) (n := 16) (k := 912)
        (b' := sp0 - 3008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3008#64) (n := 80) (k := 832)
        (b' := sp0 - 2928#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2928#64) (n := 224) (k := 608)
        (b' := sp0 - 2704#64) rfl (by bv_omega) (by decide),
      memRegion_16_split (sp0 - 3024#64),
      bv_sub_add_lit sp0 3024 8]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]

theorem tail680_join_1952 (sp0 d48 d40 d32 : BitVec 64) (d : Words11) :
    ((sp0 - 2048#64) ↦₆₄ d.w6) ∗
      ((sp0 - 2040#64) ↦₆₄ d.w7) ∗
      ((sp0 - 2032#64) ↦₆₄ d.w8) ∗
      ((sp0 - 2024#64) ↦₆₄ d.w9) ∗
      ((sp0 - 2016#64) ↦₆₄ d.w10) ∗
      memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₆₄ d48) ∗
      ((sp0 - 136#64) ↦₆₄ d40) ∗
      ((sp0 - 128#64) ↦₆₄ d32) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 2048#64) 1952 := by
  have hsplit (m n k m' : Nat)
      (hmn : m' = m - n) (hm : n < m) (hnk : m < 2 ^ 64) (hr : n + k ≤ 2 ^ 64) :
      memRegion (sp0 - BitVec.ofNat 64 m) (n + k) =
        memRegion (sp0 - BitVec.ofNat 64 m) n ∗
        memRegion (sp0 - BitVec.ofNat 64 m') k := by
    subst hmn
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 m) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 (m - n)) rfl (bv_sub_add_lit sp0 m n hm hnk).symm hr
  rw [show (1952 : Nat) = 8 + (8 + (8 + (8 + (8 + (1864 + (8 + (8 + (8 + 24)))))))) by decide,
      hsplit 2048 8 1944 2040 rfl (by decide) (by decide) (by decide),
      hsplit 2040 8 1936 2032 rfl (by decide) (by decide) (by decide),
      hsplit 2032 8 1928 2024 rfl (by decide) (by decide) (by decide),
      hsplit 2024 8 1920 2016 rfl (by decide) (by decide) (by decide),
      hsplit 2016 8 1912 2008 rfl (by decide) (by decide) (by decide),
      hsplit 2008 1864 48 144 rfl (by decide) (by decide) (by decide),
      hsplit 144 8 40 136 rfl (by decide) (by decide) (by decide),
      hsplit 136 8 32 128 rfl (by decide) (by decide) (by decide),
      hsplit 128 8 24 120 rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

theorem frame4544_join_err_740 (sp0 : BitVec 64)
    (d880 d888 d896 u0 u1 u2 u3 e0 e1 e2 e3 e4 e5 : BitVec 64) :
    memRegion (sp0 - 4640#64) 352 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      ((sp0 - 4112#64) ↦₆₄ d880) ∗
      ((sp0 - 4104#64) ↦₆₄ d888) ∗
      ((sp0 - 4096#64) ↦₆₄ d896) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      ((sp0 - 3056#64) ↦₆₄ u0) ∗
      ((sp0 - 3048#64) ↦₆₄ u1) ∗
      ((sp0 - 3040#64) ↦₆₄ u2) ∗
      ((sp0 - 3032#64) ↦₆₄ u3) ∗
      memRegion (sp0 - 3024#64) 56 ∗
      memRegion (sp0 - 2968#64) 872 ∗
      ((sp0 - 2096#64) ↦₆₄ e0) ∗
      ((sp0 - 2088#64) ↦₆₄ e1) ∗
      ((sp0 - 2080#64) ↦₆₄ e2) ∗
      ((sp0 - 2072#64) ↦₆₄ e3) ∗
      ((sp0 - 2064#64) ↦₆₄ e4) ∗
      ((sp0 - 2056#64) ↦₆₄ e5) ∗
      memRegion (sp0 - 2048#64) 1952 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  have hsplit (m n k m' : Nat)
      (hmn : m' = m - n) (hm : n < m) (hnk : m < 2 ^ 64) (hr : n + k ≤ 2 ^ 64) :
      memRegion (sp0 - BitVec.ofNat 64 m) (n + k) =
        memRegion (sp0 - BitVec.ofNat 64 m) n ∗
        memRegion (sp0 - BitVec.ofNat 64 m') k := by
    subst hmn
    exact ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 m) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 (m - n)) rfl (bv_sub_add_lit sp0 m n hm hnk).symm hr
  rw [show (4544 : Nat) = 352 + (88 + (88 + (8 + (8 + (8 + (1032 + (8 + (8 + (8 + (8 +
        (56 + (872 + (8 + (8 + (8 + (8 + (8 + (8 + 1952)))))))))))))))))) by decide,
      hsplit 4640 352 4192 4288 rfl (by decide) (by decide) (by decide),
      hsplit 4288 88 4104 4200 rfl (by decide) (by decide) (by decide),
      hsplit 4200 88 4016 4112 rfl (by decide) (by decide) (by decide),
      hsplit 4112 8 4008 4104 rfl (by decide) (by decide) (by decide),
      hsplit 4104 8 4000 4096 rfl (by decide) (by decide) (by decide),
      hsplit 4096 8 3992 4088 rfl (by decide) (by decide) (by decide),
      hsplit 4088 1032 2960 3056 rfl (by decide) (by decide) (by decide),
      hsplit 3056 8 2952 3048 rfl (by decide) (by decide) (by decide),
      hsplit 3048 8 2944 3040 rfl (by decide) (by decide) (by decide),
      hsplit 3040 8 2936 3032 rfl (by decide) (by decide) (by decide),
      hsplit 3032 8 2928 3024 rfl (by decide) (by decide) (by decide),
      hsplit 3024 56 2872 2968 rfl (by decide) (by decide) (by decide),
      hsplit 2968 872 2000 2096 rfl (by decide) (by decide) (by decide),
      hsplit 2096 8 1992 2088 rfl (by decide) (by decide) (by decide),
      hsplit 2088 8 1984 2080 rfl (by decide) (by decide) (by decide),
      hsplit 2080 8 1976 2072 rfl (by decide) (by decide) (by decide),
      hsplit 2072 8 1968 2064 rfl (by decide) (by decide) (by decide),
      hsplit 2064 8 1960 2056 rfl (by decide) (by decide) (by decide),
      hsplit 2056 8 1952 2048 rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

/-! ## 2. `step_v0_after_chainFrom_604` (`+604 .. +740 -> +2184 / +2540`) -/

/-- Shared continuation after `chain_from` succeeds in `Ordering::Greater` (`+604 .. +740`):
    moves `chain0 : Chain` (`88`B) into `s0.sp - 4288#64`, calls `Chain::recv_key(0, pre.index)`
    (`0x608d0`), and branches to `step_v0_recvKey_ok_2184` (`+2184`) on `Ok` or drops `chain1`
    (`0x4c3a0`) and jumps to `step_drop_pre_2540` (`+2540`) on `Err`. -/
theorem step_v0_after_chainFrom_604 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (G_c0 : ChainProofs.ChainGhost) (chain0 : Chain) (pad_c0 : BitVec 32)
    (w0 w1 d880 d888 d896 d2896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 604#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = G_c0.linksCap)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      words11SubAt s0.sp 2096 { chainWords11 G_c0 chain0 pad_c0 with w0 := d2896 } ∗
      chainAtHeap A G_c0 chain0 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hb : img.base &&& 0xfff#64 = 0#64 := hC.base_aligned
  have hrk_ok := spqrRecv_chainRecvKey_ok hC
  have hdrop_chain := spqrRecv_dropChain_ok hC.hA.dealloc
  simp only [Drop.dropSpqrChainSpec] at hdrop_chain
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfits : ChainProofs.RecvPrevFits chain0 :=
    recvPrevFits_of_chainFrom (F := F) (K := K) hst_len hdec hcf
  subst hP
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 49828#64)
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdrop_chain hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 604 76
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 680 64
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 4288) (by sep_focus) ?_
  wp_pull_exists; rename_i u4288
  rw [memRegion_88_sub3056_split_32_56 s0.sp, frame1912_split_err_2388 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d48 d40 d32
  have hchainAt := words11SubAt_entails_chainAt A s0.sp 4288 G_c0 chain0 pad_c0
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hchainAt ⊢
  simp only [sepConj_assoc]
  wp_steps 19
  refine SepWP.focus_weaken hchainAt (by sep_focus) ?_
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hrk_ok
    (⟨s0.sp - 3056#64, s0.sp - 4288#64, 0#64, pre.index, G_c0, chain0⟩ : ChainRecvKeyGhost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = entry + 680#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun sm => by
      dsimp only [chainRecvKeySpecX]
      have hpan := onPanic_of_chainRecvKey (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf s0 sm
      simpa only [State.trace_setPC, State.trace_setMem, State.trace_writeReg64,
        State.trace_writeVReg128, State.trace_setPState, allocFailedIn, htr] using hpan)
    (fun _ _ => rfl)
    (by
      dsimp only [chainRecvKeySpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *],
          hfits⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
  dsimp only [chainRecvKeySpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = s0.sp - 3056#64 := by
    rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by
    rw [hx22_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by
    rw [hx27_c]; simp only [arm64_norm, *]
  have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by
    rw [hx28_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainRecvKeyStackX (by decide)).symm)
    (by sep_focus) ?_
  cases hrk : chain0.recvKey (spqrHkdfWith F) 0#64 pre.index with
  | error ce =>
    cases ce with
    | panic p =>
      dsimp only [recvKeyPostAt]
      exact SepWPpI.focus_pure (by sep_focus) False.elim
    | err e =>
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode) ∧
          ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_recvKey_err hpre hdec hvn hinner hmin hver_gt hcf hrk
      apply SepWPpI.of_sepWP_ret
      dsimp only [recvKeyPostAt]
      refine SepWP.focus_weaken (recvKeyErrAt_entails_code_memRegion23 (s0.sp - 3056#64) e) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (err_payload_expose (s0.sp - 3056#64) (Top.ChainFromVersionNegotiation.spqrErrorTag e) 23 (by decide) (by decide))
        (by sep_focus) ?_
      wp_pull_exists; rename_i w3_err w2_err w1_err
      wp_focus_pure; intro hret8_err
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      rw [memRegion_zero, emp_sepConj]
      unfold chainRepr
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i G_c1
      rw [ret_48_split ret]
      wp_pull_exists; rename_i r3 r2 r1 r0
      wp_steps 15
      have hret_fold :
          ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
            ((ret + 8#64) ↦₆₄ w3_err) ∗
            ((ret + 16#64) ↦₆₄ w2_err) ∗
            ((ret + 24#64) ↦₆₄ w1_err) ∗
            memRegion (ret + 32#64) 16) ⊢
          recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
        rw [herr_recv]
        exact recv_err_words_foldX A ret w3_err w2_err w1_err
          (Top.ChainFromVersionNegotiation.spqrErrorTag e) (e == .stateDecode)
          (spqrErrorTag_eq_zero_iff e).to_iff hret8_err
      refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) Drop.dropSpqrChainStack (by decide)))
        (by sep_focus) ?_
      wp_call hdrop_chain (⟨s0.sp - 4288#64, G_c1, chain0⟩ : Drop.DropSpqrChainGhost)
      simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
        sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) Drop.dropSpqrChainStack (by decide)).symm)
        (by sep_focus) ?_
      wp_steps 1
      refine SepWP.focus_weaken
        (tail680_join_1952 s0.sp G_c0.linksPtr G_c0.linksHead d48 (chainWords11 G_c0 chain0 pad_c0))
        (by dsimp only [chainWords11]; sep_focus) ?_
      refine SepWP.focus_weaken
        (frame4544_join_err_740 s0.sp d880 d888 d896 1#64 w3_err w2_err w1_err
          w3_err w2_err w1_err (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length)
          G_c0.nextRoot.cap G_c0.nextRoot.ptr)
        (by sep_focus) ?_
      refine sepWP_spqrRecvPost_of_post0 hnp ?_
      exact step_drop_pre_2540 img.base A (spqrV1Recv F K) ext hb hC.hA.dealloc st msg ret vn pb w0 w1
        s0 _ _ R _ rfl hs0_align
        (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl)
  | ok res =>
    rcases res with ⟨chain1, rawKey⟩
    have hok_recv := spqrV1Recv_gt_recvKey_ok (F := F) (K := K) hpre hdec hvn hinner hmin hver_gt hcf hrk
    have henc_len := encodeRaw_v0_state_len_lt (F := F) (K := K) hst_len hpre hdec hvn hinner hmin hver_gt hcf hrk
    apply SepWPpI.of_sepWP (mid := entry + 2184#64)
    dsimp only [recvKeyPostAt, recvKeyOkAt]
    rw [bv_sub_add_lit s0.sp 3056 8 (by decide) (by decide)]
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
    refine SepWP.focus_weaken (vecU8_sub_entails_header_buf A s0.sp 3048 rawKey) (by sep_focus) ?_
    wp_pull_exists; rename_i cap_rk ptr_rk
    dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
    wp_steps 7
    refine SepWP.focus_weaken
      (tail680_join_1952 s0.sp G_c0.linksPtr G_c0.linksHead d48 (chainWords11 G_c0 chain0 pad_c0))
      (by dsimp only [chainWords11]; sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_872_sub2968_split_ok_680 s0.sp))
      (by sep_focus) ?_
    wp_pull_exists; rename_i u5 u4
    apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_recvKey_ok_2184 hC st msg ret vn pb chain1 rawKey w0 w1 cap_rk ptr_rk
      d880 d888 d896 0#64 cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length) u4 u5
      (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length) G_c0.nextRoot.cap G_c0.nextRoot.ptr
      henc_len hok_recv s0 _ _ R hs0_align
      (by rw [← hentry, ← spqrRecvEntry_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 3. Frame Helpers for `step_v0_chain_none_2108` and `step_ordering_greater` -/

theorem frame4544_split_v0 (sp0 : BitVec 64) :
    memRegion (sp0 - 4640#64) 4544 =
      memRegion (sp0 - 4640#64) 352 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      (∃∗ d880 : BitVec 64, (sp0 - 4112#64) ↦₆₄ d880) ∗
      (∃∗ d888 : BitVec 64, (sp0 - 4104#64) ↦₆₄ d888) ∗
      (∃∗ d896 : BitVec 64, (sp0 - 4096#64) ↦₆₄ d896) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      memRegion (sp0 - 3056#64) 88 ∗
      memRegion (sp0 - 2968#64) 872 ∗
      memRegion (sp0 - 2096#64) 88 ∗
      memRegion (sp0 - 2008#64) 1912 := by
  have hsplit (a n k b : Nat) (h1 : a - 96 = n + k) (h2 : a - n = b)
      (ha : a < 2 ^ 64) (hn : n < a) :
      memRegion (sp0 - BitVec.ofNat 64 a) (a - 96) =
        memRegion (sp0 - BitVec.ofNat 64 a) n ∗
        memRegion (sp0 - BitVec.ofNat 64 b) k := by
    refine ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 a) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 b) h1 ?_ (by omega)
    rw [bv_sub_add_lit sp0 a n hn ha, h2]
  rw [show (4544 : Nat) = 4640 - 96 from rfl,
      hsplit 4640 352 4192 4288 rfl (by decide) (by decide) (by decide),
      hsplit 4288 88 4104 4200 rfl (by decide) (by decide) (by decide),
      hsplit 4200 88 4016 4112 rfl (by decide) (by decide) (by decide),
      hsplit 4112 8 4008 4104 rfl (by decide) (by decide) (by decide),
      hsplit 4104 8 4000 4096 rfl (by decide) (by decide) (by decide),
      hsplit 4096 8 3992 4088 rfl (by decide) (by decide) (by decide),
      hsplit 4088 1032 2960 3056 rfl (by decide) (by decide) (by decide),
      hsplit 3056 88 2872 2968 rfl (by decide) (by decide) (by decide),
      hsplit 2968 872 2000 2096 rfl (by decide) (by decide) (by decide),
      hsplit 2096 88 1912 2008 rfl (by decide) (by decide) (by decide),
      ProofLib.memRegion_eight (sp0 - 4112#64),
      ProofLib.memRegion_eight (sp0 - 4104#64),
      ProofLib.memRegion_eight (sp0 - 4096#64)]

theorem frame2544_join_v0 (sp0 d880 d888 d896 : BitVec 64) :
    memRegion (sp0 - 4640#64) 352 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      ((sp0 - 4112#64) ↦₆₄ d880) ∗
      ((sp0 - 4104#64) ↦₆₄ d888) ∗
      ((sp0 - 4096#64) ↦₆₄ d896) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      memRegion (sp0 - 3056#64) 88 ∗
      memRegion (sp0 - 2968#64) 872 ⊢
      memRegion (sp0 - 4640#64) 2544 := by
  have hsplit (a n k b : Nat) (h1 : a - 2096 = n + k) (h2 : a - n = b)
      (ha : a < 2 ^ 64) (hn : n < a) :
      memRegion (sp0 - BitVec.ofNat 64 a) (a - 2096) =
        memRegion (sp0 - BitVec.ofNat 64 a) n ∗
        memRegion (sp0 - BitVec.ofNat 64 b) k := by
    refine ProofLib.memRegion_split' (b := sp0 - BitVec.ofNat 64 a) (n := n) (k := k)
      (b' := sp0 - BitVec.ofNat 64 b) h1 ?_ (by omega)
    rw [bv_sub_add_lit sp0 a n hn ha, h2]
  rw [show (2544 : Nat) = 4640 - 2096 from rfl,
      hsplit 4640 352 2192 4288 rfl (by decide) (by decide) (by decide),
      hsplit 4288 88 2104 4200 rfl (by decide) (by decide) (by decide),
      hsplit 4200 88 2016 4112 rfl (by decide) (by decide) (by decide),
      hsplit 4112 8 2008 4104 rfl (by decide) (by decide) (by decide),
      hsplit 4104 8 2000 4096 rfl (by decide) (by decide) (by decide),
      hsplit 4096 8 1992 4088 rfl (by decide) (by decide) (by decide),
      hsplit 4088 1032 960 3056 rfl (by decide) (by decide) (by decide),
      hsplit 3056 88 872 2968 rfl (by decide) (by decide) (by decide)]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

theorem memRegion_88_sub2096_split_byte8 (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 88 =
      (∃∗ d2896 : BitVec 64, (sp0 - 2096#64) ↦₆₄ d2896) ∗
      (∃∗ b0 : BitVec 8, (sp0 - 2088#64) ↦₈ b0) ∗
      memRegion (sp0 - 2087#64) 79 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 8) (k := 80)
        (b' := sp0 - 2088#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2088#64) (n := 1) (k := 79)
        (b' := sp0 - 2087#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp0 - 2096#64),
      ProofLib.memRegion_one (sp0 - 2088#64)]

theorem vn_some_unpack_sub4992 (A : RustAlloc) (sp0 w0 w1 : BitVec 64) (vn : VersionNegotiationPB) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) =
      vecU8At A (sp0 - 4992#64) w0 w1 vn.authKey ∗
      Top.ChainFromVersionNegotiation.optChainParamsPBAt (sp0 - 4968#64) vn.chainParams ∗
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
      ((sp0 - 4952#64) ↦₃₂ vn.minVersion) ∗
      memRegion (sp0 - 4948#64) 4 := by
  unfold optVersionNegotiationPBTailAt versionNegotiationPBTailAt vecU8Heap vecU8At vecHeader
  dsimp only []
  rw [← optChainParamsPBAt_eq_protoRepr,
      bv_sub_add_lit sp0 4992 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4992 16 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 20 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 24 (by decide) (by decide),
      bv_sub_add_lit sp0 4976 28 (by decide) (by decide)]
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  ac_rfl

theorem vecU8At_sub4992_unpack (A : RustAlloc) (sp0 w0 w1 : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp0 - 4992#64) w0 w1 bs ⊢
      ⌜bs.length < 2 ^ 63⌝ ∗
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false w1 bs ∗
      vecU8BufRest A w0 w1 bs.length := by
  have h := vecU8At_entails_header_bytesAt_rest A (sp0 - 4992#64) w0 w1 bs
  rw [bv_sub_add_lit sp0 4992 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4992 16 (by decide) (by decide)] at h
  exact h

theorem vecU8At_sub4992_repack (A : RustAlloc) (sp0 w0 w1 : BitVec 64) (bs : List (BitVec 8)) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bytesAt false w1 bs ∗
      vecU8BufRest A w0 w1 bs.length ⊢
      vecU8At A (sp0 - 4992#64) w0 w1 bs := by
  have h := header_bytesAt_rest_entails_vecU8At A (sp0 - 4992#64) w0 w1 bs
  rw [bv_sub_add_lit sp0 4992 8 (by decide) (by decide),
      bv_sub_add_lit sp0 4992 16 (by decide) (by decide)] at h
  exact h

theorem byte_memRegion79_sub2096_to_v0_err (sp0 : BitVec 64) (e : Error) :
    ((sp0 - 2088#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
      memRegion (sp0 - 2087#64) 79 ⊢
    (∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
      ⌜BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e⌝ ∗
      ((sp0 - 2088#64) ↦₆₄ q0.extractLsb' 0 64) ∗
      ((sp0 - 2080#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp0 - 2072#64) ↦₆₄ w3)) ∗
    memRegion (sp0 - 2064#64) 56 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 2087#64) (n := 7) (k := 72)
        (b' := sp0 - 2080#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2080#64) (n := 8) (k := 64)
        (b' := sp0 - 2072#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2072#64) (n := 8) (k := 56)
        (b' := sp0 - 2064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eq_exists_bytes (sp0 - 2087#64) 7 (by decide),
      ProofLib.memRegion_eight (sp0 - 2080#64),
      ProofLib.memRegion_eight (sp0 - 2072#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepExists_left_entails; intro w2
  apply sepExists_left_entails; intro w1
  apply sepExists_left_entails; intro bs7
  rw [show
    ((sp0 - 2088#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
      ((⌜bs7.length = 7⌝ ∗ ((sp0 - 2087#64) ↦ₛ bs7)) ∗
        ((sp0 - 2080#64) ↦₆₄ w1) ∗ ((sp0 - 2072#64) ↦₆₄ w2) ∗ memRegion (sp0 - 2064#64) 56) =
    ⌜bs7.length = 7⌝ ∗
      (((sp0 - 2088#64) ↦₈ Top.ChainFromVersionNegotiation.spqrErrorTag e) ∗
        ((sp0 - 2087#64) ↦ₛ bs7) ∗
        ((sp0 - 2080#64) ↦₆₄ w1)) ∗
      ((sp0 - 2072#64) ↦₆₄ w2) ∗
      memRegion (sp0 - 2064#64) 56 by ac_rfl]
  refine Entails.pure_left fun hbs7 => ?_
  have h1 := byte_bs7_word_to_pointsTo128 (sp0 - 2088#64) (Top.ChainFromVersionNegotiation.spqrErrorTag e) hbs7 w1
  rw [bv_sub_add_lit sp0 2088 1 (by decide) (by decide),
      bv_sub_add_lit sp0 2088 8 (by decide) (by decide)] at h1
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h1
  refine Entails.trans (sepConj_mono_left h1) ?_
  simp only [sepExists_sepConj_left]
  apply sepExists_left_entails; intro q0
  refine Entails.trans ?_ (Entails.sepExists_intro q0)
  refine Entails.trans ?_ (Entails.sepExists_intro w2)
  unfold pointsTo128
  rw [bv_sub_add_lit sp0 2088 8 (by decide) (by decide)]
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  exact Entails.of_eq (by ac_rfl)

theorem pack_v0_err_sub2088 (sp0 : BitVec 64) (e : Error) (q0 : BitVec 128) (w3 : BitVec 64)
    (htag : BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e) :
    ((sp0 - 2088#64) ↦₆₄ q0.extractLsb' 0 64) ∗
      ((sp0 - 2080#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((sp0 - 2072#64) ↦₆₄ w3) ⊢
    ∃∗ q0' : BitVec 128, ∃∗ w3' : BitVec 64,
      ⌜BitVec.truncate 8 q0' = Top.ChainFromVersionNegotiation.spqrErrorTag e⌝ ∗
      ((sp0 - 2088#64) ↦₆₄ q0'.extractLsb' 0 64) ∗
      ((sp0 - 2080#64) ↦₆₄ q0'.extractLsb' 64 64) ∗
      ((sp0 - 2072#64) ↦₆₄ w3') :=
  Entails.sepExists_right q0 (Entails.sepExists_right w3 (Entails.pure_right htag (Entails.refl _)))

theorem chainErrorAt_sub3056_unpack (sp0 : BitVec 64) (e : Error) :
    chainErrorAt (sp0 - 3056#64) e =
      ∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e⌝ ∗
        ((sp0 - 3056#64) ↦₆₄ Top.ChainFromVersionNegotiation.noneCap) ∗
        ((sp0 - 3048#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp0 - 3040#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((sp0 - 3032#64) ↦₆₄ w3) ∗
        memRegion (sp0 - 3024#64) 56 := by
  have h := chainErrorAt_unpack_words4 (sp0 - 3056#64) e
  rw [bv_sub_add_lit sp0 3056 8 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 16 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 24 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 32 (by decide) (by decide)] at h
  exact h

theorem words4_rest_sub3056_to_memRegion_88 (sp0 w0 w1 w2 w3 : BitVec 64) :
    ((sp0 - 3056#64) ↦₆₄ w0) ∗
      ((sp0 - 3048#64) ↦₆₄ w1) ∗
      ((sp0 - 3040#64) ↦₆₄ w2) ∗
      ((sp0 - 3032#64) ↦₆₄ w3) ∗
      memRegion (sp0 - 3024#64) 56 ⊢
      memRegion (sp0 - 3056#64) 88 := by
  have h := words4_rest_to_memRegion_88 (sp0 - 3056#64) w0 w1 w2 w3
  rw [bv_sub_add_lit sp0 3056 8 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 16 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 24 (by decide) (by decide),
      bv_sub_add_lit sp0 3056 32 (by decide) (by decide)] at h
  exact h

theorem memRegion_88_sub2096_words4_rest (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 88 =
      (∃∗ d0 : BitVec 64, (sp0 - 2096#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp0 - 2088#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp0 - 2080#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp0 - 2072#64) ↦₆₄ d3) ∗
      memRegion (sp0 - 2064#64) 56 := by
  have h := ChainFromNorm.memRegion_88_words4_rest (sp0 - 2096#64)
  rw [bv_sub_add_lit sp0 2096 8 (by decide) (by decide),
      bv_sub_add_lit sp0 2096 16 (by decide) (by decide),
      bv_sub_add_lit sp0 2096 24 (by decide) (by decide),
      bv_sub_add_lit sp0 2096 32 (by decide) (by decide)] at h
  exact h

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  ult_one_toI32

/-! ## 4. `step_v0_chain_none_2108` (`+2108 .. +2140`, `+2384 .. +2388`, `+2920 .. +2948`) -/

/-- When `pre_pb.chain = none` in `Ordering::Greater`, `+2108` checks `vn.direction` and `vn.chainParams`:
    - Invalid `vn.direction` (`> 1`): jumps to `+2384` (`Error::StateDecode`) -> `step_v0_err_2388`.
    - `vn.chainParams = none`: writes `15#8` (`Error::ChainNotAvailable`) at `+2132..+2140` -> `step_v0_err_2388`.
    - `vn.chainParams = some cp`: jumps to `+2920`, calls `Chain::new` (`0x5fea4`), and jumps to `+604` (`step_v0_after_chainFrom_604`). -/
theorem step_v0_chain_none_2108 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 d880 d888 d896 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hchain : pre_pb.chain = none)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_gt : pre.version > 1#8)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      memRegion (s0.sp - 3056#64) 88 ∗
      memRegion (s0.sp - 2968#64) 872 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hb : img.base &&& 0xfff#64 = 0#64 := hC.base_aligned
  have hnew_ok := spqrRecv_chainNew_ok hC
  subst hP
  refine SepWPpI.focus_weaken
    (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn))
    (by sep_focus) ?_
  rcases direction_fromI32_or vn.direction with
    ⟨dir, hdir_val, hdir_opt, hcond_hi⟩ | ⟨hdir_opt, hcond_hi⟩
  · cases hcp : vn.chainParams with
    | none =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error .chainNotAvailable := by
        simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt, hcp]
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
          .error (Error.chainNotAvailable == .stateDecode) ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
      apply SepWPpI.of_sepWP
        (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2388#64)
      dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      spqr_recv_fetches_range img.base (Rust.withPanics ext) 2108 36
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
      examples_hide_fetches
      dsimp only [Top.ChainFromVersionNegotiation.optChainParamsPBAt]
      rw [memRegion_88_sub2096_split_byte8 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i b0_err d2896
      wp_steps 9
      have hcp_fold :
          ((s0.sp - 4968#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 4968#64 + 4#64) 8 =
            Top.ChainFromVersionNegotiation.optChainParamsPBAt (s0.sp - 4968#64) vn.chainParams := by
        rw [hcp]; rfl
      refine SepWP.focus_weaken (Entails.of_eq hcp_fold) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn).symm)
        (by sep_focus) ?_
      have htag_cna : (15#8 : BitVec 8) = Top.ChainFromVersionNegotiation.spqrErrorTag .chainNotAvailable := rfl
      rw [htag_cna]
      refine SepWP.focus_weaken
        (byte_memRegion79_sub2096_to_v0_err s0.sp .chainNotAvailable)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (frame2544_join_v0 s0.sp d880 d888 d896) (by sep_focus) ?_
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_err_2388 A F K ext hb hC.hA.dealloc st msg ret vn pb .chainNotAvailable
        w0 w1 d2896 herr_recv hnp s0 _ _ R hs0_align
        (by rw [← hentry, ← spqrRecvEntry_eq]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
    | some cp =>
      let chain0 := chainNewVal (spqrHkdfWith F) vn.authKey dir cp
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 := by
        simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt, hcp]; rfl
      apply SepWPpI.of_sepWP
        (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 47224#64)
      dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      spqr_recv_fetches_range img.base (Rust.withPanics ext) 2108 24
      spqr_recv_fetches_range img.base (Rust.withPanics ext) 2920 32
      generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
      examples_hide_fetches
      refine SepWP.focus_weaken (vecU8At_sub4992_unpack A s0.sp w0 w1 vn.authKey) (by sep_focus) ?_
      wp_focus_pure; intro hlen64
      dsimp only [Top.ChainFromVersionNegotiation.optChainParamsPBAt]
      rw [bv_sub_add_lit s0.sp 4968 4 (by decide) (by decide),
          bv_sub_add_lit s0.sp 4968 8 (by decide) (by decide)]
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      wp_steps 10
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpI.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainNewStackX (by decide)))
        (by sep_focus) ?_
      refine SepWPpI.call_inImage hnew_ok
        (⟨s0.sp - 2096#64, false, w1, vn.authKey, dir, cp⟩ : ChainNewGhost)
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
        (rfl : _ = entry + 2936#64)
        (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
        (fun sm => by
          dsimp only [chainNewSpecX]
          simpa only [State.trace_setPC, State.trace_setMem, State.trace_writeReg64,
            State.trace_writeVReg128, State.trace_setPState, allocFailedIn, htr] using onPanic_of_allocFailed)
        (fun _ _ => rfl)
        (by
          dsimp only [chainNewSpecX]
          refine frame_pure_pre
            ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              by simp only [arm64_norm, *],
              hlen64⟩
            (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
                sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
        ?_
      intro sm hpcm hrunm hspm hcsm
      have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
      rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
      dsimp only [chainNewSpecX]
      refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
      have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
      have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
      have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
      have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
      have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
      have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by rw [hx22_c]; simp only [arm64_norm, *]
      have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
      have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
      have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
        change sm.readReg64 Reg.fp = s0.sp - 96#64
        rw [hxfp_c]; simp only [arm64_norm, *]
      simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
        sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
      refine SepWPpI.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainNewStackX (by decide)).symm)
        (by sep_focus) ?_
      refine SepWPpI.focus_weaken (vecU8At_sub4992_repack A s0.sp w0 w1 vn.authKey) (by sep_focus) ?_
      have hcp_fold :
          ((s0.sp - 4968#64) ↦₃₂ 1#32) ∗
            ((s0.sp - 4964#64) ↦₃₂ cp.maxJump) ∗
            ((s0.sp - 4960#64) ↦₃₂ cp.maxOooKeys) =
          Top.ChainFromVersionNegotiation.optChainParamsPBAt (s0.sp - 4968#64) vn.chainParams := by
        rw [hcp]
        dsimp only [Top.ChainFromVersionNegotiation.optChainParamsPBAt]
        rw [bv_sub_add_lit s0.sp 4968 4 (by decide) (by decide),
            bv_sub_add_lit s0.sp 4968 8 (by decide) (by decide)]
      refine SepWPpI.focus_weaken (Entails.of_eq hcp_fold) (by sep_focus) ?_
      refine SepWPpI.focus_weaken
        (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn).symm)
        (by sep_focus) ?_
      refine SepWPpI.focus_weaken
        (Entails.trans (chainNew_post_entails_chainRepr A (s0.sp - 2096#64) chain0)
          (chainRepr_sub_entails_words11 A s0.sp 2096 chain0))
        (by sep_focus) ?_
      apply SepWPpI.of_sepWP (mid := entry + 604#64)
      wp_pull_exists; rename_i G_c0 pad_c0
      wp_focus_pure; intro hcap_c0_ne
      have hz_c0 : (G_c0.linksCap + 1#64 == 0#64) = false :=
        add_one_beq_zero_of_ne_noneCap hcap_c0_ne
      have hnz_c0 : (G_c0.linksCap + 1#64 != 0#64) = true := by
        simp [bne, hz_c0]
      dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      simp only [sepConj_assoc]
      wp_steps 4
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, bne, *]) (by simp only [arm64_norm, *])
      exact step_v0_after_chainFrom_604 hC st msg ret pre pre_pb vn pb G_c0 chain0 pad_c0
        w0 w1 d880 d888 d896 G_c0.linksCap
        hst_len hpre hdec hvn hinner hmin hver_gt hcf s0 _ _ R hs0_align
        (by rw [← hentry, ← spqrRecvEntry_eq]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]; ac_rfl)
  · have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error .stateDecode := by
      simp [chainFrom, chainFromVersionNegotiation, hchain, hdir_opt]
    obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
        .error (Error.stateDecode == .stateDecode) ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
      spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
    apply SepWPpI.of_sepWP
      (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2388#64)
    dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 2108 16
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 2384 4
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    rw [memRegion_88_sub2096_split_byte8 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i b0_err d2896
    wp_steps 5
    refine SepWP.focus_weaken
      (Entails.of_eq (vn_some_unpack_sub4992 A s0.sp w0 w1 vn).symm)
      (by sep_focus) ?_
    have htag_sd : (0#8 : BitVec 8) = Top.ChainFromVersionNegotiation.spqrErrorTag .stateDecode := rfl
    rw [htag_sd]
    refine SepWP.focus_weaken
      (byte_memRegion79_sub2096_to_v0_err s0.sp .stateDecode)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (frame2544_join_v0 s0.sp d880 d888 d896) (by sep_focus) ?_
    apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_err_2388 A F K ext hb hC.hA.dealloc st msg ret vn pb .stateDecode
      w0 w1 d2896 herr_recv hnp s0 _ _ R hs0_align
      (by rw [← hentry, ← spqrRecvEntry_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 5. `step_ordering_greater : V0ChainTail` (`+496 .. +600` and `+2164 .. +2180`) -/

/-- `Ordering::Greater` branch (`+496`): dispatches on `pre_pb.chain`:
    - `pre_pb.chain = none`: jumps to `+2108` (`step_v0_chain_none_2108`).
    - `pre_pb.chain = some chPb`: calls `Chain::from_pb` (`0x60074`) and branches to `+604`
    (`step_v0_after_chainFrom_604`) on `Ok` or `+2164 -> +2388` (`step_v0_err_2388`) on `Err`. -/
theorem step_ordering_greater {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (s0 : State) (R : SepProp)
    (hs0_align : s0.spAligned = true) :
    V0ChainTail img A F K ext st msg ret s0 R := by
  intro pre remPtr pre_pb vn pb w0 w1 w26 s P
    hpre _hrem hdec hvn hinner _hw0 _hw26 hmin hver_gt
    hpc hrun hsp htr hx19 hx20 hx21 _hx22 _hx23 _hx24 _hx26 hx27 hx28 hx29 hP
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hb : img.base &&& 0xfff#64 = 0#64 := hC.base_aligned
  have hfrom_pb_ok := spqrRecv_chainFromPb_ok hC
  subst hP
  refine SepWPpI.focus_weaken (Entails.of_eq (frame4544_split_v0 s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPpI.exists_elim; intro d896
  apply SepWPpI.exists_elim; intro d888
  apply SepWPpI.exists_elim; intro d880
  cases hchain : pre_pb.chain with
  | none =>
    apply SepWPpI.of_sepWP
      (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2108#64)
    dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 496 12
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    dsimp only [ProtoRepr.optChainPBAt, LibsignalTripleRatchetRepr.noneCap]
    wp_steps 3
    refine SepWP.focus_weaken
      (word_rest72_to_memRegion_80 (s0.sp - 4944#64) 0xFFFFFFFFFFFFFFFF#64)
      (by rw [bv_sub_add_lit s0.sp 4944 8 (by decide) (by decide)]; sep_focus) ?_
    apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_v0_chain_none_2108 hC st msg ret pre pre_pb vn pb w0 w1 d880 d888 d896
      hst_len hpre hdec hvn hinner hchain hmin hver_gt s0 _ _ R hs0_align
      (by rw [← hentry, ← spqrRecvEntry_eq]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl)
  | some chPb =>
    apply SepWPpI.of_sepWP
      (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 47688#64)
    dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 496 28
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 524 80
    spqr_recv_fetches_range img.base (Rust.withPanics ext) 2164 20
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
    examples_hide_fetches
    dsimp only [ProtoRepr.optChainPBAt]
    rw [chainPBAt_protoRepr_eq_exists A (s0.sp - 4944#64) chPb]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists; rename_i gPb
    refine SepWP.focus_weaken
      (chainPBAt_expose_cap A gPb (s0.sp - 4944#64) chPb)
      (by sep_focus) ?_
    wp_focus_pure; intro hcap_pb_ne
    have hz_pb : (gPb.linksCap + 1#64 == 0#64) = false :=
      add_one_beq_zero_of_ne_noneCap hcap_pb_ne
    wp_steps 7
    refine SepWP.focus_weaken
      (chainPBAt_unexpose_cap A gPb (s0.sp - 4944#64) chPb)
      (by sep_focus) ?_
    apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpI.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromPbStackX (by decide)))
      (by sep_focus) ?_
    refine SepWPpI.call_inImage hfrom_pb_ok
      (⟨s0.sp - 3056#64, s0.sp - 4944#64, gPb, chPb⟩ : ChainFromPbCall)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
      (rfl : _ = entry + 524#64)
      (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
      (fun sm => by
        dsimp only [chainFromPbSpecX]
        simpa only [State.trace_setPC, State.trace_setMem, State.trace_writeReg64,
          State.trace_writeVReg128, State.trace_setPState, allocFailedIn, htr] using onPanic_of_allocFailed)
      (fun _ _ => rfl)
      (by
        dsimp only [chainFromPbSpecX]
        refine frame_pure_pre
          ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
          (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
              sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
    rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, _, _, _, _, _, hx27_c, hx28_c, hxfp_c, _⟩
    dsimp only [chainFromPbSpecX]
    refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
    have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c]; simp only [arm64_norm, *]
    have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c]; simp only [arm64_norm, *]
    have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c]; simp only [arm64_norm, *]
    have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c]; simp only [arm64_norm, *]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64
      rw [hxfp_c]; simp only [arm64_norm, *]
    simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
      sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
    refine SepWPpI.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromPbStackX (by decide)).symm)
      (by sep_focus) ?_
    cases hfpb : Chain.fromPb chPb with
    | error e =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error e := by
        simp [chainFrom, hchain, hfpb]
      obtain ⟨herr_recv, hnp⟩ : (spqrV1Recv F K).recv st.bytes msg.bytes =
          .error (e == .stateDecode) ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_gt_chainFrom_err hpre hdec hvn hinner hmin hver_gt hcf
      apply SepWPpI.of_sepWP (mid := entry + 2388#64)
      dsimp only [chainResultAt]
      rw [chainErrorAt_sub3056_unpack s0.sp e, memRegion_88_sub2096_words4_rest s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      wp_pull_exists; rename_i u2096_3 u2096_2 u2096_1 d2896 q0_err w3_err
      wp_focus_pure; intro htag_q0
      dsimp only [Top.ChainFromVersionNegotiation.noneCap]
      wp_steps 13
      refine SepWP.focus_weaken
        (words4_rest_sub3056_to_memRegion_88 s0.sp 0xFFFFFFFFFFFFFFFF#64
          (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (frame2544_join_v0 s0.sp (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (pack_v0_err_sub2088 s0.sp e q0_err w3_err htag_q0)
        (by sep_focus) ?_
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_err_2388 A F K ext hb hC.hA.dealloc st msg ret vn pb e w0 w1 d2896
        herr_recv hnp s0 _ _ R hs0_align
        (by rw [← hentry, ← spqrRecvEntry_eq]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl)
    | ok chain0 =>
      have hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok chain0 := by
        simp [chainFrom, hchain, hfpb]
      apply SepWPpI.of_sepWP (mid := entry + 604#64)
      dsimp only [chainResultAt]
      refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A s0.sp 3056 chain0) (by sep_focus) ?_
      refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 2096) (by sep_focus) ?_
      wp_pull_exists; rename_i G_c0 pad_c0 u2096
      wp_focus_pure; intro hcap_c0_ne
      have hz_c0 : (G_c0.linksCap + 1#64 == 0#64) = false :=
        add_one_beq_zero_of_ne_noneCap hcap_c0_ne
      have hto88 := words11SubAt_to_memRegion_88 s0.sp 3056 (chainWords11 G_c0 chain0 pad_c0)
      dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hto88 ⊢
      simp only [sepConj_assoc]
      wp_steps 20
      refine SepWP.focus_weaken hto88 (by sep_focus) ?_
      apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      exact step_v0_after_chainFrom_604 hC st msg ret pre pre_pb vn pb G_c0 chain0 pad_c0
        w0 w1 G_c0.linksPtr G_c0.linksHead (BitVec.ofNat 64 (G_c0.epochs.zip chain0.links).length) u2096.w0
        hst_len hpre hdec hvn hinner hmin hver_gt hcf s0 _ _ R hs0_align
        (by rw [← hentry, ← spqrRecvEntry_eq]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]; ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv

