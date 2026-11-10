/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: `Ordering::Less` `chain_from` Error & Post-`into_pb` Continuation

**Checked by Lean.** `VersionNegotiationPB` representation bridges and the error (`+1320..+1348 -> +2424`)
and post-`Chain::into_pb` (`+1424..+1528 -> +824`) continuations of `Ordering::Less` in
`spqr::recv` (`0x5462c`).
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

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Representation Bridges for `VersionNegotiationPB` and `init_inner` / `chain_from` -/

theorem pointsTo32_minVersion_entails_pointsTo8_memRegion3 (a : BitVec 64) (v : BitVec 32) :
    (a ↦₃₂ v) ⊢ ((a ↦₈ v.truncate 8) ∗ memRegion (a + 1#64) 3) := by
  have hsplit (k r : Nat) (off off' : BitVec 64)
      (hkr : k = 1 + r) (hoff : (a + off) + 1#64 = a + off') (hr : k ≤ 2 ^ 64) :
      memRegion (a + off) k = memRegion (a + off) 1 ∗ memRegion (a + off') r :=
    ProofLib.memRegion_split' (b := a + off) (n := 1) (k := r) (b' := a + off') hkr hoff.symm hr
  rw [hsplit 3 2 1#64 2#64 rfl (by bv_omega) (by decide),
      hsplit 2 1 2#64 3#64 rfl (by bv_omega) (by decide),
      pointsTo32_eq_pointsToBytes]
  dsimp only [unpack32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have hb0 : v.extractLsb' 0 8 = BitVec.truncate 8 v := by bv_kernel
  rw [hb0]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (pointsTo8_entails_memRegion _ _)))

theorem vnTail_some_eq_versionNegotiationPBAt (A : RustAlloc) (a w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) (some vn)) =
    Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ a vn := by
  dsimp only [optVersionNegotiationPBTailAt, versionNegotiationPBTailAt,
    Top.ChainFromVersionNegotiation.versionNegotiationPBAt]
  rw [RustHeap.vecU8At_eq_header_sep_buf A a w0 w1 vn.authKey,
      optChainParamsPBAt_eq_protoRepr (a + 24#64) vn.chainParams]
  dsimp only [RustHeap.vecHeader]
  have hbuf : DecodeState.vecU8Heap A w0 w1 vn.authKey = RustHeap.vecU8Buf A w0 w1 vn.authKey := rfl
  have h24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  have h36 : (a + 16#64) + 20#64 = a + 36#64 := by bv_omega
  have h40 : (a + 16#64) + 24#64 = a + 40#64 := by bv_omega
  have h44 : (a + 16#64) + 28#64 = a + 44#64 := by bv_omega
  rw [hbuf, h24, h36, h40, h44]
  ac_rfl

theorem vnTail_some_entails_versionNegotiationPBAt (A : RustAlloc) (a w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) (some vn) ⊢
    Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ a vn :=
  Entails.of_eq (vnTail_some_eq_versionNegotiationPBAt A a w0 w1 vn)

theorem vecU8BufRest_expose_ptr_ne_zero (A : RustAlloc) (w0 w1 : BitVec 64) (len : Nat) :
    vecU8BufRest A w0 w1 len ⊢ ⌜w1 ≠ 0#64⌝ ∗ vecU8BufRest A w0 w1 len := by
  unfold vecU8BufRest
  exact Entails.pure_left fun ⟨hle, hlt, hptr⟩ =>
    Entails.pure_right hptr (Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _))

theorem vn_some_expose_for_initInner (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) ⊢
    ⌜w1 ≠ 0#64⌝ ∗
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
      (w1 ↦ₛ vn.authKey) ∗
      (∃∗ P_vn : SepProp,
        ⌜((sp0 - 4992#64) ↦₆₄ w0) ∗
          ((sp0 - 4984#64) ↦₆₄ w1) ∗
          ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (w1 ↦ₛ vn.authKey) ∗ P_vn ⊢
          Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn⌝ ∗ P_vn) := by
  have h8 : (sp0 - 4992#64) + 8#64 = sp0 - 4984#64 := bv_sub_add_lit sp0 4992 8
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  have hvn_eq :
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) =
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn := by
    rw [← h8, ← h16]
    exact vnTail_some_eq_versionNegotiationPBAt A (sp0 - 4992#64) w0 w1 vn
  have hvn_def : Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn =
      vecU8At A (sp0 - 4992#64) w0 w1 vn.authKey ∗
      Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
      (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
      (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
      memRegion ((sp0 - 4992#64) + 44#64) 4 := rfl
  have hunpack := vecU8At_entails_header_bytesAt_rest A (sp0 - 4992#64) w0 w1 vn.authKey
  have hbytes : ChainProofs.bytesAt false w1 vn.authKey = (w1 ↦ₛ vn.authKey) := rfl
  rw [hbytes, h8, h16] at hunpack
  refine Entails.trans (Entails.of_eq (hvn_eq.trans hvn_def)) ?_
  refine Entails.trans (sepConj_mono_left hunpack) ?_
  refine Entails.trans
    (Entails.of_eq (show
      (⌜vn.authKey.length < 2 ^ 63⌝ ∗
        ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        vecU8BufRest A w0 w1 vn.authKey.length) ∗
        Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
        (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
        (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion ((sp0 - 4992#64) + 44#64) 4 =
      ⌜vn.authKey.length < 2 ^ 63⌝ ∗
        (vecU8BufRest A w0 w1 vn.authKey.length ∗
          (((sp0 - 4992#64) ↦₆₄ w0) ∗
            ((sp0 - 4984#64) ↦₆₄ w1) ∗
            ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
            (w1 ↦ₛ vn.authKey) ∗
            (Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
              (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
              (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
              memRegion ((sp0 - 4992#64) + 44#64) 4))) by ac_rfl)) ?_
  refine Entails.pure_left fun _ => ?_
  refine Entails.trans (sepConj_mono_left (vecU8BufRest_expose_ptr_ne_zero A w0 w1 vn.authKey.length)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right ?_
  refine Entails.trans
    (Entails.of_eq (show
      vecU8BufRest A w0 w1 vn.authKey.length ∗
        (((sp0 - 4992#64) ↦₆₄ w0) ∗
          ((sp0 - 4984#64) ↦₆₄ w1) ∗
          ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (w1 ↦ₛ vn.authKey) ∗
          (Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
            (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
            (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
            memRegion ((sp0 - 4992#64) + 44#64) 4)) =
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        (vecU8BufRest A w0 w1 vn.authKey.length ∗
          Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
          (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
          (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
          memRegion ((sp0 - 4992#64) + 44#64) 4) by ac_rfl)) ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  have hpack := header_bytesAt_rest_entails_vecU8At A (sp0 - 4992#64) w0 w1 vn.authKey
  rw [hbytes, h8, h16] at hpack
  rw [hvn_def]
  refine Entails.trans
    (Entails.of_eq (show
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        (vecU8BufRest A w0 w1 vn.authKey.length ∗
          Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
          (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
          (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
          memRegion ((sp0 - 4992#64) + 44#64) 4) =
      (((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        vecU8BufRest A w0 w1 vn.authKey.length) ∗
        Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
        (((sp0 - 4992#64) + 36#64) ↦₃₂ vn.direction) ∗
        (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion ((sp0 - 4992#64) + 44#64) 4 by ac_rfl)) ?_
  exact sepConj_mono_left hpack

theorem vn_authKey_len_bound_of_spqrDecodeState {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {st : PqRatchetState} {vn : VersionNegotiationPB}
    (hlen : stateBytes.length < 2 ^ 32)
    (hdec : Proto.spqrDecodeState stateBytes = .ok st)
    (hvn : st.versionNegotiation = some vn) :
    32 + vn.authKey.length < 2 ^ 63 := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hraw := decodeState_spqrDeps_raw_le hd
  rw [pbToPqRatchetState_pqRatchetStateToPb] at hraw
  unfold rawPqState at hraw
  rw [hvn] at hraw
  simp only [optRaw_some, rawVN] at hraw
  omega

theorem spqrRecvRoAt_expose_logOff (b : BitVec 64) :
    spqrRecvRoAt b ⊢
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      (∃∗ P_ro : SepProp, ⌜((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ P_ro ⊢ spqrRecvRoAt b⌝ ∗ P_ro) := by
  have h1 : ∀ P Q R S T U : SepProp,
      P ∗ Q ∗ (R ∗ (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ S) ∗ T ∗ U) ∗ statesIntoPbJumpTableAt b =
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ (P ∗ Q ∗ (R ∗ S ∗ T ∗ U) ∗ statesIntoPbJumpTableAt b) := by
    intro P Q R S T U; ac_rfl
  refine Entails.trans (Entails.of_eq (h1 _ _ _ _ _ _)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (h1 _ _ _ _ _ _).symm

theorem zeroExtend64_eq_zero_of_lt_one {v : BitVec 8} (hlt : v < 1#8) :
    v.zeroExtend 64 = 0#64 := by
  have hv0 : v = 0#8 := by bv_omega
  subst hv0; rfl

@[simp, arm64_norm]
theorem direction_ult_two (dir : Direction) :
    (dir.toI32).ult 2#32 = true := by
  cases dir <;> decide

@[simp, arm64_norm]
theorem direction_two_ule_false (dir : Direction) :
    (2#32).ule dir.toI32 = false := by
  cases dir <;> decide

theorem direction_fromI32_of_ult_two {v : BitVec 32} (h : v.ult 2#32 = true) :
    ∃ dir : Direction, v = dir.toI32 ∧ Direction.fromI32? v = some dir := by
  rcases direction_fromI32_or v with ⟨dir, hval, hopt, _⟩ | ⟨_, hhi⟩
  · exact ⟨dir, hval, hopt⟩
  · exfalso
    have h1 : (1#32).toNat = 1 := rfl
    have h2 : (2#32).toNat = 2 := rfl
    have : v.ult 2#32 = false := by
      unfold BitVec.ult at hhi ⊢
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, h1, h2] at hhi ⊢
      omega
    rw [h] at this
    contradiction

theorem direction_fromI32_of_two_ule {v : BitVec 32} (h : (2#32).ule v = true) :
    Direction.fromI32? v = none := by
  rcases direction_fromI32_or v with ⟨dir, hval, _, _⟩ | ⟨hopt, _⟩
  · subst hval
    rw [direction_two_ule_false] at h
    contradiction
  · exact hopt

theorem optVersionNegotiationPBTailAt_some_expose_direction (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) ⊢
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
      (∃∗ P_vn : SepProp,
        ⌜((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn ⊢
          optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn)⌝ ∗ P_vn) := by
  dsimp only [optVersionNegotiationPBTailAt, versionNegotiationPBTailAt]
  have h20 : (sp0 - 4976#64) + 20#64 = sp0 - 4956#64 := bv_sub_add_lit sp0 4976 20
  rw [h20]
  refine Entails.trans
    (Entails.of_eq (show
      (((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        ProtoRepr.optChainParamsPBAt ((sp0 - 4976#64) + 8#64) vn.chainParams ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        (((sp0 - 4976#64) + 24#64) ↦₃₂ vn.minVersion) ∗
        memRegion ((sp0 - 4976#64) + 28#64) 4) ∗
        vecU8Heap A w0 w1 vn.authKey =
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        ((((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          ProtoRepr.optChainParamsPBAt ((sp0 - 4976#64) + 8#64) vn.chainParams ∗
          (((sp0 - 4976#64) + 24#64) ↦₃₂ vn.minVersion) ∗
          memRegion ((sp0 - 4976#64) + 28#64) 4) ∗
          vecU8Heap A w0 w1 vn.authKey) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right
    ((((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
      ProtoRepr.optChainParamsPBAt ((sp0 - 4976#64) + 8#64) vn.chainParams ∗
      (((sp0 - 4976#64) + 24#64) ↦₃₂ vn.minVersion) ∗
      memRegion ((sp0 - 4976#64) + 28#64) 4) ∗
      vecU8Heap A w0 w1 vn.authKey) ?_
  refine Entails.pure_right ?_ (Entails.refl _)
  exact Entails.of_eq (by ac_rfl)

@[simp, arm64_norm]
theorem spqrErrorTag_eq_zero_iff (e : Error) :
    (Top.ChainFromVersionNegotiation.spqrErrorTag e = 0#8) = ((e == .stateDecode) = true) := by
  cases e <;> simp [Top.ChainFromVersionNegotiation.spqrErrorTag, BEq.beq]

theorem truncate8_extractLsb64 (q0 : BitVec 128) :
    BitVec.truncate 8 (q0.extractLsb' 0 64) = BitVec.truncate 8 q0 := by
  bv_kernel

theorem pointsTo64_entails_pointsTo8_memRegion7 (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ⊢ ((a ↦₈ BitVec.truncate 8 w) ∗ memRegion (a + 1#64) 7) := by
  have hsplit (k r : Nat) (off off' : BitVec 64)
      (hkr : k = 1 + r) (hoff : (a + off) + 1#64 = a + off') (hr : k ≤ 2 ^ 64) :
      memRegion (a + off) k = memRegion (a + off) 1 ∗ memRegion (a + off') r :=
    ProofLib.memRegion_split' (b := a + off) (n := 1) (k := r) (b' := a + off') hkr hoff.symm hr
  rw [hsplit 7 6 1#64 2#64 rfl (by bv_omega) (by decide),
      hsplit 6 5 2#64 3#64 rfl (by bv_omega) (by decide),
      hsplit 5 4 3#64 4#64 rfl (by bv_omega) (by decide),
      hsplit 4 3 4#64 5#64 rfl (by bv_omega) (by decide),
      hsplit 3 2 5#64 6#64 rfl (by bv_omega) (by decide),
      hsplit 2 1 6#64 7#64 rfl (by bv_omega) (by decide),
      pointsTo64_eq_pointsToBytes]
  dsimp only [unpack64]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have hb0 : w.extractLsb' 0 8 = BitVec.truncate 8 w := by bv_kernel
  rw [hb0]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (pointsTo8_entails_memRegion _ _)))))))

theorem recv_err_q0_foldX (A : RustAlloc) (r r2 r3 : BitVec 64) (q0 : BitVec 128) (e : Error)
    (hq0 : BitVec.truncate 8 q0 = Top.ChainFromVersionNegotiation.spqrErrorTag e) :
    ((r ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((r + 8#64) ↦₆₄ q0.extractLsb' 0 64) ∗
      ((r + 16#64) ↦₆₄ r2) ∗
      ((r + 24#64) ↦₆₄ r3) ∗
      memRegion (r + 32#64) 16) ⊢
    recvResultExactKeyAt A r (.error (e == .stateDecode)) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_pointsTo8_memRegion7 (r + 8#64) (q0.extractLsb' 0 64)))) ?_
  have haddr : (r + 8#64) + 1#64 = r + 9#64 := by bv_omega
  rw [haddr, truncate8_extractLsb64 q0, hq0]
  simp only [sepConj_assoc]
  exact recv_err_byte_foldX A r r2 r3
    (Top.ChainFromVersionNegotiation.spqrErrorTag e) (e == .stateDecode)
    (Eq.to_iff (spqrErrorTag_eq_zero_iff e))

theorem spqrRecvRoAt_expose_statesIntoPb (b : BitVec 64) :
    spqrRecvRoAt b ⊢
      statesIntoPbJumpTableAt b ∗
      (∃∗ P_ro : SepProp, ⌜statesIntoPbJumpTableAt b ∗ P_ro ⊢ spqrRecvRoAt b⌝ ∗ P_ro) := by
  unfold spqrRecvRoAt
  refine Entails.trans
    (Entails.of_eq (show
      Prost.MessageMerge.v1StateJumpTablesAt b ∗
        statesFromPbJumpTableAt b ∗
        States.Recv.statesRecvRoAt b ∗
        statesIntoPbJumpTableAt b =
      statesIntoPbJumpTableAt b ∗
        (Prost.MessageMerge.v1StateJumpTablesAt b ∗
          statesFromPbJumpTableAt b ∗
          States.Recv.statesRecvRoAt b) by ac_rfl)) ?_
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right _ (Entails.pure_right ?_ (Entails.refl _))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_24_words3 (out : BitVec 64) :
    memRegion out 24 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 16)
        (b' := out + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 8)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out,
      ProofLib.memRegion_eight (out + 8#64),
      ProofLib.memRegion_eight (out + 16#64)]

theorem words3_to_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_words3 a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

theorem memRegion_32_words4 (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 24)
        (b' := out + 8#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 (out + 8#64),
      ProofLib.memRegion_eight out]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words4_to_memRegion_32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [memRegion_32_words4 a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
        (Entails.sepExists_right w3 (Entails.refl _))))

theorem memRegion_64_words8 (out : BitVec 64) :
    memRegion out 64 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (out + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (out + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (out + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (out + 56#64) ↦₆₄ d7) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 32) (k := 32)
        (b' := out + 32#64) rfl (by bv_omega) (by decide),
      memRegion_32_words4 out,
      memRegion_32_words4 (out + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words8_to_memRegion_64 (a w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ⊢
    memRegion a 64 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 32)
        (b' := a + 32#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans
    (Entails.of_eq (show
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ∗
        (((a + 32#64) ↦₆₄ w4) ∗ (((a + 32#64) + 8#64) ↦₆₄ w5) ∗
          (((a + 32#64) + 16#64) ↦₆₄ w6) ∗ (((a + 32#64) + 24#64) ↦₆₄ w7)) by
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])) ?_
  exact sepConj_mono (words4_to_memRegion_32 a w0 w1 w2 w3)
    (words4_to_memRegion_32 (a + 32#64) w4 w5 w6 w7)

theorem spqrV1Recv_lt_one_dir_none (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hlt : pre.version < 1#8)
    (hdir : Direction.fromI32? vn.direction = none) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error true := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_vn_some_inner_some_lt F K (spqrHkdfWith F) hpre hd_ok hvn
    (pqRatchetStateToPb_inner_some hinner) hge hlt
  rw [hdir] at heq
  exact spqrV1Recv_recv_of_err heq

theorem spqrV1Recv_lt_one_chainFrom_err (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {dir : Direction} {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hlt : pre.version < 1#8)
    (hdir : Direction.fromI32? vn.direction = some dir)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .error e) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_vn_some_inner_some_lt F K (spqrHkdfWith F) hpre hd_ok hvn
    (pqRatchetStateToPb_inner_some hinner) hge hlt
  have hch : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  rw [hdir, hch, hcf] at heq
  have his : e.isStateDecode = (e == .stateDecode) := by cases e <;> rfl
  rw [← his]
  exact spqrV1Recv_recv_noPanic_of_err heq

theorem spqrV1Recv_lt_one_chainFrom_ok (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState}
    {vn : VersionNegotiationPB} {pb : V1State} {dir : Direction} {ch : Chain}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hge : ¬ (pre.version < vn.minVersion.truncate 8))
    (hlt : pre.version < 1#8)
    (hdir : Direction.fromI32? vn.direction = some dir)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok ch) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .ok ([], none) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_vn_some_inner_some_lt F K (spqrHkdfWith F) hpre hd_ok hvn
    (pqRatchetStateToPb_inner_some hinner) hge hlt
  have hch : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  rw [hdir, hch, hcf] at heq
  exact spqrV1Recv_recv_of_ok heq

theorem frame4544_split_1076 (sp0 : BitVec 64) :
    memRegion (sp0 - 4640#64) 4544 =
      memRegion (sp0 - 4640#64) 528 ∗
      (∃∗ b0 : BitVec 8, (sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 3967 ∗
      (∃∗ w30 : BitVec 32, (sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 528) (k := 4016)
        (b' := sp0 - 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 1) (k := 4015)
        (b' := sp0 - 4111#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4111#64) (n := 3967) (k := 48)
        (b' := sp0 - 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 144#64) (n := 4) (k := 44)
        (b' := sp0 - 140#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (sp0 - 4112#64),
      ProofLib.memRegion_four (sp0 - 144#64)]

theorem frame4544_join_1076 (sp0 : BitVec 64) (b0 : BitVec 8) (w30 : BitVec 32) :
    memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 3967 ∗
      ((sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  rw [frame4544_split_1076 sp0]
  exact sepConj_mono_right
    (sepConj_mono (Entails.sepExists_right b0 (Entails.refl _))
      (sepConj_mono_right
        (sepConj_mono_left (Entails.sepExists_right w30 (Entails.refl _)))))

theorem frame4544_split_1296 (sp0 : BitVec 64) :
    memRegion (sp0 - 4640#64) 4544 =
      memRegion (sp0 - 4640#64) 1584 ∗
      memRegion (sp0 - 3056#64) Drop.optProtoInnerStateSize ∗
      memRegion (sp0 - 2832#64) 736 ∗
      memRegion (sp0 - 2096#64) 88 ∗
      memRegion (sp0 - 2008#64) 1912 := by
  unfold Drop.optProtoInnerStateSize
  rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 1584) (k := 2960)
        (b' := sp0 - 3056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 224) (k := 2736)
        (b' := sp0 - 2832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2832#64) (n := 736) (k := 2000)
        (b' := sp0 - 2096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 2096#64) (n := 88) (k := 1912)
        (b' := sp0 - 2008#64) rfl (by bv_omega) (by decide)]

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

theorem frame1584_split_err (sp0 : BitVec 64) :
    memRegion (sp0 - 4640#64) 1584 =
      memRegion (sp0 - 4640#64) 528 ∗
      (∃∗ d0 : BitVec 64, (sp0 - 4112#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp0 - 4104#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp0 - 4096#64) ↦₆₄ d2) ∗
      memRegion (sp0 - 4088#64) 1032 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 528) (k := 1056)
        (b' := sp0 - 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 24) (k := 1032)
        (b' := sp0 - 4088#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 (sp0 - 4112#64),
      bv_sub_add_lit sp0 4112 8,
      bv_sub_add_lit sp0 4112 16]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]

theorem frame4544_join_err_2424 (sp0 : BitVec 64) (w0 w1 w2 w790 : BitVec 64) :
    memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₆₄ w0) ∗
      ((sp0 - 4104#64) ↦₆₄ w1) ∗
      ((sp0 - 4096#64) ↦₆₄ w2) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      ((sp0 - 3056#64) ↦₆₄ w790) ∗
      memRegion (sp0 - 3048#64) 216 ∗
      memRegion (sp0 - 2832#64) 736 ∗
      memRegion (sp0 - 2096#64) 88 ∗
      memRegion (sp0 - 2008#64) 1912 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  have h24 := words3_to_memRegion_24 (sp0 - 4112#64) w0 w1 w2
  rw [bv_sub_add_lit sp0 4112 8, bv_sub_add_lit sp0 4112 16] at h24
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24
  have h224 : ((sp0 - 3056#64) ↦₆₄ w790) ∗ memRegion (sp0 - 3048#64) 216 ⊢
      memRegion (sp0 - 3056#64) Drop.optProtoInnerStateSize := by
    unfold Drop.optProtoInnerStateSize
    rw [ProofLib.memRegion_split' (b := sp0 - 3056#64) (n := 8) (k := 216)
          (b' := sp0 - 3048#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4640#64) 528 ∗
        ((sp0 - 4112#64) ↦₆₄ w0) ∗
        ((sp0 - 4104#64) ↦₆₄ w1) ∗
        ((sp0 - 4096#64) ↦₆₄ w2) ∗
        memRegion (sp0 - 4088#64) 1032 ∗
        ((sp0 - 3056#64) ↦₆₄ w790) ∗
        memRegion (sp0 - 3048#64) 216 ∗
        memRegion (sp0 - 2832#64) 736 ∗
        memRegion (sp0 - 2096#64) 88 ∗
        memRegion (sp0 - 2008#64) 1912 =
      (memRegion (sp0 - 4640#64) 528 ∗
        (((sp0 - 4112#64) ↦₆₄ w0) ∗ ((sp0 - 4104#64) ↦₆₄ w1) ∗ ((sp0 - 4096#64) ↦₆₄ w2)) ∗
        memRegion (sp0 - 4088#64) 1032) ∗
        (((sp0 - 3056#64) ↦₆₄ w790) ∗ memRegion (sp0 - 3048#64) 216) ∗
        memRegion (sp0 - 2832#64) 736 ∗
        memRegion (sp0 - 2096#64) 88 ∗
        memRegion (sp0 - 2008#64) 1912 by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_left h24))
      (sepConj_mono_left h224)) ?_
  have h1584 :
      memRegion (sp0 - 4640#64) 528 ∗ memRegion (sp0 - 4112#64) 24 ∗ memRegion (sp0 - 4088#64) 1032 =
      memRegion (sp0 - 4640#64) 1584 := by
    rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 528) (k := 1056)
          (b' := sp0 - 4112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 24) (k := 1032)
          (b' := sp0 - 4088#64) rfl (by bv_omega) (by decide)]
  rw [h1584, ← frame4544_split_1296 sp0]
  exact Entails.refl _

/-- Error path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1348 -> +2424 .. +2456 ->
    +2540`). -/
theorem step_initInner_chainFrom_err_1320 {img : Obj.Image} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State)
    (e : Error) (w0 w1 : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (s0.sp - 4992#64) vn ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      chainErrorAt (s0.sp - 2096#64) e ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hnone3 : (Drop.none3Cap' + 3#64 == 0#64) = true := rfl
  have hnone1 : (Top.ChainFromVersionNegotiation.noneCap + 1#64 == 0#64) = true := rfl
  apply SepWPpI.of_sepWP_ret
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1320 32
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2424 36
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [← vnTail_some_eq_versionNegotiationPBAt A (s0.sp - 4992#64) w0 w1 vn,
      bv_sub_add_lit s0.sp 4992 8,
      bv_sub_add_lit s0.sp 4992 16]
  dsimp only [Drop.optProtoPqRatchetInnerAt]
  rw [bv_sub_add_lit s0.sp 3056 8,
      chainErrorAt_unpack_words4 (s0.sp - 2096#64) e,
      bv_sub_add_lit s0.sp 2096 8,
      bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24,
      bv_sub_add_lit s0.sp 2096 32,
      frame1584_split_err s0.sp,
      ret_48_split ret]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i q0_err w3_err d0 d1 d2 r0 r1 r2 r3
  wp_focus_pure; intro htag_q0
  have htag_eq : BitVec.truncate 8 ((q0_err.extractLsb' 64 64) ++ (q0_err.extractLsb' 0 64)) =
      Top.ChainFromVersionNegotiation.spqrErrorTag e := by
    have hq : (q0_err.extractLsb' 64 64) ++ (q0_err.extractLsb' 0 64) = q0_err := by bv_kernel
    rw [hq, htag_q0]
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_q0_foldX A ret (q0_err.extractLsb' 64 64) w3_err q0_err e htag_q0
  have hw4_join := words4_rest_to_memRegion_88 (s0.sp - 2096#64)
    Top.ChainFromVersionNegotiation.noneCap (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err
  rw [bv_sub_add_lit s0.sp 2096 8,
      bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24,
      bv_sub_add_lit s0.sp 2096 32] at hw4_join
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hw4_join
  wp_steps 17
  refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
  refine SepWP.focus_weaken hw4_join (by sep_focus) ?_
  refine SepWP.focus_weaken
    (frame4544_join_err_2424 s0.sp (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err Drop.none3Cap')
    (by sep_focus) ?_
  refine sepWP_spqrRecvPost_of_post0 hnp ?_
  exact step_drop_pre_2540 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret vn pb w0 w1
    s0 _ _ R _ rfl hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl)

theorem frame1584_split_ok_1320 (sp0 : BitVec 64) :
    memRegion (sp0 - 4640#64) 1584 =
      (∃∗ w160 : BitVec 64, (sp0 - 4640#64) ↦₆₄ w160) ∗
      memRegion (sp0 - 4632#64) 40 ∗
      memRegion (sp0 - 4592#64) 80 ∗
      memRegion (sp0 - 4512#64) 224 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      (∃∗ d0 : BitVec 64, (sp0 - 4112#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp0 - 4104#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp0 - 4096#64) ↦₆₄ d2) ∗
      memRegion (sp0 - 4088#64) 1032 := by
  rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 8) (k := 1576)
        (b' := sp0 - 4632#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4632#64) (n := 40) (k := 1536)
        (b' := sp0 - 4592#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4592#64) (n := 80) (k := 1456)
        (b' := sp0 - 4512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4512#64) (n := 224) (k := 1232)
        (b' := sp0 - 4288#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4288#64) (n := 88) (k := 1144)
        (b' := sp0 - 4200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4200#64) (n := 88) (k := 1056)
        (b' := sp0 - 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 24) (k := 1032)
        (b' := sp0 - 4088#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp0 - 4640#64),
      memRegion_24_words3 (sp0 - 4112#64),
      bv_sub_add_lit sp0 4112 8,
      bv_sub_add_lit sp0 4112 16]
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat, sepConj_assoc]

theorem memRegion_216_words27 (out : BitVec 64) :
    memRegion out 216 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (out + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (out + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (out + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (out + 56#64) ↦₆₄ d7) ∗
      (∃∗ d8 : BitVec 64, (out + 64#64) ↦₆₄ d8) ∗
      (∃∗ d9 : BitVec 64, (out + 72#64) ↦₆₄ d9) ∗
      (∃∗ d10 : BitVec 64, (out + 80#64) ↦₆₄ d10) ∗
      (∃∗ d11 : BitVec 64, (out + 88#64) ↦₆₄ d11) ∗
      (∃∗ d12 : BitVec 64, (out + 96#64) ↦₆₄ d12) ∗
      (∃∗ d13 : BitVec 64, (out + 104#64) ↦₆₄ d13) ∗
      (∃∗ d14 : BitVec 64, (out + 112#64) ↦₆₄ d14) ∗
      (∃∗ d15 : BitVec 64, (out + 120#64) ↦₆₄ d15) ∗
      (∃∗ d16 : BitVec 64, (out + 128#64) ↦₆₄ d16) ∗
      (∃∗ d17 : BitVec 64, (out + 136#64) ↦₆₄ d17) ∗
      (∃∗ d18 : BitVec 64, (out + 144#64) ↦₆₄ d18) ∗
      (∃∗ d19 : BitVec 64, (out + 152#64) ↦₆₄ d19) ∗
      (∃∗ d20 : BitVec 64, (out + 160#64) ↦₆₄ d20) ∗
      (∃∗ d21 : BitVec 64, (out + 168#64) ↦₆₄ d21) ∗
      (∃∗ d22 : BitVec 64, (out + 176#64) ↦₆₄ d22) ∗
      (∃∗ d23 : BitVec 64, (out + 184#64) ↦₆₄ d23) ∗
      (∃∗ d24 : BitVec 64, (out + 192#64) ↦₆₄ d24) ∗
      (∃∗ d25 : BitVec 64, (out + 200#64) ↦₆₄ d25) ∗
      (∃∗ d26 : BitVec 64, (out + 208#64) ↦₆₄ d26) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 24) (k := 192)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 64) (k := 128)
        (b' := out + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 88#64) (n := 64) (k := 64)
        (b' := out + 152#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 out,
      memRegion_64_words8 (out + 24#64),
      memRegion_64_words8 (out + 88#64),
      memRegion_64_words8 (out + 152#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words27_to_memRegion_216 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗
      ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗
      ((a + 88#64) ↦₆₄ w11) ∗ ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗
      ((a + 120#64) ↦₆₄ w15) ∗ ((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17) ∗ ((a + 144#64) ↦₆₄ w18) ∗
      ((a + 152#64) ↦₆₄ w19) ∗ ((a + 160#64) ↦₆₄ w20) ∗ ((a + 168#64) ↦₆₄ w21) ∗ ((a + 176#64) ↦₆₄ w22) ∗
      ((a + 184#64) ↦₆₄ w23) ∗ ((a + 192#64) ↦₆₄ w24) ∗ ((a + 200#64) ↦₆₄ w25) ∗ ((a + 208#64) ↦₆₄ w26) ⊢
    memRegion a 216 := by
  rw [memRegion_216_words27 a]
  refine sepConj_mono (Entails.sepExists_right w0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w1 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w2 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w3 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w4 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w5 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w6 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w7 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w8 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w9 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w10 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w11 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w12 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w13 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w14 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w15 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w16 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w17 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w18 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w19 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w20 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w21 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w22 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w23 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right w24 (Entails.refl _)) ?_
  exact sepConj_mono (Entails.sepExists_right w25 (Entails.refl _))
    (Entails.sepExists_right w26 (Entails.refl _))

theorem memRegion_224_words28 (out : BitVec 64) :
    memRegion out 224 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗
      memRegion (out + 8#64) 216 :=
  Eq.trans
    (ProofLib.memRegion_split' (b := out) (n := 8) (k := 216)
      (b' := out + 8#64) rfl (by bv_omega) (by decide))
    (congrArg (· ∗ memRegion (out + 8#64) 216) (ProofLib.memRegion_eight out))

theorem word_memRegion216_to_memRegion_224 (out w0 : BitVec 64) :
    (out ↦₆₄ w0) ∗ memRegion (out + 8#64) 216 ⊢ memRegion out 224 := by
  rw [memRegion_224_words28 out]
  exact sepConj_mono_left (Entails.sepExists_right w0 (Entails.refl _))

theorem frame4544_join_ok_880 (sp0 : BitVec 64) (w160 d0 d1 d2 : BitVec 64) :
    ((sp0 - 4640#64) ↦₆₄ w160) ∗
      memRegion (sp0 - 4632#64) 40 ∗
      memRegion (sp0 - 4592#64) 80 ∗
      memRegion (sp0 - 4512#64) 224 ∗
      memRegion (sp0 - 4288#64) 88 ∗
      memRegion (sp0 - 4200#64) 88 ∗
      ((sp0 - 4112#64) ↦₆₄ d0) ∗
      ((sp0 - 4104#64) ↦₆₄ d1) ∗
      ((sp0 - 4096#64) ↦₆₄ d2) ∗
      memRegion (sp0 - 4088#64) 1032 ∗
      memRegion (sp0 - 3056#64) 224 ∗
      memRegion (sp0 - 2832#64) 736 ∗
      memRegion (sp0 - 2096#64) 88 ∗
      memRegion (sp0 - 2008#64) 1912 ⊢
    memRegion (sp0 - 4640#64) 4544 := by
  have h1584 :
      ((sp0 - 4640#64) ↦₆₄ w160) ∗
        memRegion (sp0 - 4632#64) 40 ∗
        memRegion (sp0 - 4592#64) 80 ∗
        memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 88 ∗
        memRegion (sp0 - 4200#64) 88 ∗
        ((sp0 - 4112#64) ↦₆₄ d0) ∗
        ((sp0 - 4104#64) ↦₆₄ d1) ∗
        ((sp0 - 4096#64) ↦₆₄ d2) ∗
        memRegion (sp0 - 4088#64) 1032 ⊢
      memRegion (sp0 - 4640#64) 1584 := by
    rw [frame1584_split_ok_1320 sp0]
    refine sepConj_mono (Entails.sepExists_right w160 (Entails.refl _)) ?_
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))))
    refine sepConj_mono (Entails.sepExists_right d0 (Entails.refl _)) ?_
    refine sepConj_mono (Entails.sepExists_right d1 (Entails.refl _)) ?_
    exact sepConj_mono_left (Entails.sepExists_right d2 (Entails.refl _))
  have h224 : memRegion (sp0 - 3056#64) 224 = memRegion (sp0 - 3056#64) Drop.optProtoInnerStateSize := rfl
  rw [h224, frame4544_split_1296 sp0]
  refine Entails.trans
    (Entails.of_eq (show
      ((sp0 - 4640#64) ↦₆₄ w160) ∗
        memRegion (sp0 - 4632#64) 40 ∗
        memRegion (sp0 - 4592#64) 80 ∗
        memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 88 ∗
        memRegion (sp0 - 4200#64) 88 ∗
        ((sp0 - 4112#64) ↦₆₄ d0) ∗
        ((sp0 - 4104#64) ↦₆₄ d1) ∗
        ((sp0 - 4096#64) ↦₆₄ d2) ∗
        memRegion (sp0 - 4088#64) 1032 ∗
        memRegion (sp0 - 3056#64) Drop.optProtoInnerStateSize ∗
        memRegion (sp0 - 2832#64) 736 ∗
        memRegion (sp0 - 2096#64) 88 ∗
        memRegion (sp0 - 2008#64) 1912 =
      (((sp0 - 4640#64) ↦₆₄ w160) ∗
        memRegion (sp0 - 4632#64) 40 ∗
        memRegion (sp0 - 4592#64) 80 ∗
        memRegion (sp0 - 4512#64) 224 ∗
        memRegion (sp0 - 4288#64) 88 ∗
        memRegion (sp0 - 4200#64) 88 ∗
        ((sp0 - 4112#64) ↦₆₄ d0) ∗
        ((sp0 - 4104#64) ↦₆₄ d1) ∗
        ((sp0 - 4096#64) ↦₆₄ d2) ∗
        memRegion (sp0 - 4088#64) 1032) ∗
        (memRegion (sp0 - 3056#64) Drop.optProtoInnerStateSize ∗
          memRegion (sp0 - 2832#64) 736 ∗
          memRegion (sp0 - 2096#64) 88 ∗
          memRegion (sp0 - 2008#64) 1912) by ac_rfl)) ?_
  exact sepConj_mono_left h1584

theorem sepExists_left_entails {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ x, P x ⊢ Q) : (∃∗ x, P x) ⊢ Q := by
  exact Entails.sepExists_elim h

structure Words8 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64

def words8At (out : BitVec 64) (d : Words8) : SepProp :=
  (out ↦₆₄ d.w0) ∗ ((out + 8#64) ↦₆₄ d.w1) ∗ ((out + 16#64) ↦₆₄ d.w2) ∗ ((out + 24#64) ↦₆₄ d.w3) ∗
  ((out + 32#64) ↦₆₄ d.w4) ∗ ((out + 40#64) ↦₆₄ d.w5) ∗ ((out + 48#64) ↦₆₄ d.w6) ∗ ((out + 56#64) ↦₆₄ d.w7)

theorem memRegion_64_entails_words8 (out : BitVec 64) :
    memRegion out 64 ⊢ ∃∗ d : Words8, words8At out d := by
  rw [memRegion_64_words8 out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepExists_left_entails; intro w7
  apply sepExists_left_entails; intro w6
  apply sepExists_left_entails; intro w5
  apply sepExists_left_entails; intro w4
  apply sepExists_left_entails; intro w3
  apply sepExists_left_entails; intro w2
  apply sepExists_left_entails; intro w1
  apply sepExists_left_entails; intro w0
  exact Entails.sepExists_right ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩ (Entails.refl _)

structure Words27 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64
  w10 : BitVec 64
  w11 : BitVec 64
  w12 : BitVec 64
  w13 : BitVec 64
  w14 : BitVec 64
  w15 : BitVec 64
  w16 : BitVec 64
  w17 : BitVec 64
  w18 : BitVec 64
  w19 : BitVec 64
  w20 : BitVec 64
  w21 : BitVec 64
  w22 : BitVec 64
  w23 : BitVec 64
  w24 : BitVec 64
  w25 : BitVec 64
  w26 : BitVec 64

def words27At (out : BitVec 64) (d : Words27) : SepProp :=
  (out ↦₆₄ d.w0) ∗ ((out + 8#64) ↦₆₄ d.w1) ∗ ((out + 16#64) ↦₆₄ d.w2) ∗
  ((out + 24#64) ↦₆₄ d.w3) ∗ ((out + 32#64) ↦₆₄ d.w4) ∗ ((out + 40#64) ↦₆₄ d.w5) ∗
  ((out + 48#64) ↦₆₄ d.w6) ∗ ((out + 56#64) ↦₆₄ d.w7) ∗ ((out + 64#64) ↦₆₄ d.w8) ∗
  ((out + 72#64) ↦₆₄ d.w9) ∗ ((out + 80#64) ↦₆₄ d.w10) ∗ ((out + 88#64) ↦₆₄ d.w11) ∗
  ((out + 96#64) ↦₆₄ d.w12) ∗ ((out + 104#64) ↦₆₄ d.w13) ∗ ((out + 112#64) ↦₆₄ d.w14) ∗
  ((out + 120#64) ↦₆₄ d.w15) ∗ ((out + 128#64) ↦₆₄ d.w16) ∗ ((out + 136#64) ↦₆₄ d.w17) ∗
  ((out + 144#64) ↦₆₄ d.w18) ∗ ((out + 152#64) ↦₆₄ d.w19) ∗ ((out + 160#64) ↦₆₄ d.w20) ∗
  ((out + 168#64) ↦₆₄ d.w21) ∗ ((out + 176#64) ↦₆₄ d.w22) ∗ ((out + 184#64) ↦₆₄ d.w23) ∗
  ((out + 192#64) ↦₆₄ d.w24) ∗ ((out + 200#64) ↦₆₄ d.w25) ∗ ((out + 208#64) ↦₆₄ d.w26)

def words27SubAt (sp0 : BitVec 64) (m : Nat) (d : Words27) : SepProp :=
  ((sp0 - BitVec.ofNat 64 (m - 8)) ↦₆₄ d.w0) ∗ ((sp0 - BitVec.ofNat 64 (m - 16)) ↦₆₄ d.w1) ∗ ((sp0 - BitVec.ofNat 64 (m - 24)) ↦₆₄ d.w2) ∗
  ((sp0 - BitVec.ofNat 64 (m - 32)) ↦₆₄ d.w3) ∗ ((sp0 - BitVec.ofNat 64 (m - 40)) ↦₆₄ d.w4) ∗ ((sp0 - BitVec.ofNat 64 (m - 48)) ↦₆₄ d.w5) ∗
  ((sp0 - BitVec.ofNat 64 (m - 56)) ↦₆₄ d.w6) ∗ ((sp0 - BitVec.ofNat 64 (m - 64)) ↦₆₄ d.w7) ∗ ((sp0 - BitVec.ofNat 64 (m - 72)) ↦₆₄ d.w8) ∗
  ((sp0 - BitVec.ofNat 64 (m - 80)) ↦₆₄ d.w9) ∗ ((sp0 - BitVec.ofNat 64 (m - 88)) ↦₆₄ d.w10) ∗ ((sp0 - BitVec.ofNat 64 (m - 96)) ↦₆₄ d.w11) ∗
  ((sp0 - BitVec.ofNat 64 (m - 104)) ↦₆₄ d.w12) ∗ ((sp0 - BitVec.ofNat 64 (m - 112)) ↦₆₄ d.w13) ∗ ((sp0 - BitVec.ofNat 64 (m - 120)) ↦₆₄ d.w14) ∗
  ((sp0 - BitVec.ofNat 64 (m - 128)) ↦₆₄ d.w15) ∗ ((sp0 - BitVec.ofNat 64 (m - 136)) ↦₆₄ d.w16) ∗ ((sp0 - BitVec.ofNat 64 (m - 144)) ↦₆₄ d.w17) ∗
  ((sp0 - BitVec.ofNat 64 (m - 152)) ↦₆₄ d.w18) ∗ ((sp0 - BitVec.ofNat 64 (m - 160)) ↦₆₄ d.w19) ∗ ((sp0 - BitVec.ofNat 64 (m - 168)) ↦₆₄ d.w20) ∗
  ((sp0 - BitVec.ofNat 64 (m - 176)) ↦₆₄ d.w21) ∗ ((sp0 - BitVec.ofNat 64 (m - 184)) ↦₆₄ d.w22) ∗ ((sp0 - BitVec.ofNat 64 (m - 192)) ↦₆₄ d.w23) ∗
  ((sp0 - BitVec.ofNat 64 (m - 200)) ↦₆₄ d.w24) ∗ ((sp0 - BitVec.ofNat 64 (m - 208)) ↦₆₄ d.w25) ∗ ((sp0 - BitVec.ofNat 64 (m - 216)) ↦₆₄ d.w26)

theorem memRegion_216_entails_words27 (out : BitVec 64) :
    memRegion out 216 ⊢ ∃∗ d : Words27, words27At out d := by
  rw [ProofLib.memRegion_split' (b := out) (n := 24) (k := 192)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 64) (k := 128)
        (b' := out + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 88#64) (n := 64) (k := 64)
        (b' := out + 152#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 out]
  refine Entails.trans (sepConj_mono_right (sepConj_mono (memRegion_64_entails_words8 (out + 24#64))
    (sepConj_mono (memRegion_64_entails_words8 (out + 88#64)) (memRegion_64_entails_words8 (out + 152#64))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepExists_left_entails; intro c
  apply sepExists_left_entails; intro b
  apply sepExists_left_entails; intro a
  apply sepExists_left_entails; intro w2
  apply sepExists_left_entails; intro w1
  apply sepExists_left_entails; intro w0
  refine Entails.sepExists_right
    ⟨w0, w1, w2, a.w0, a.w1, a.w2, a.w3, a.w4, a.w5, a.w6, a.w7,
     b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7,
     c.w0, c.w1, c.w2, c.w3, c.w4, c.w5, c.w6, c.w7⟩ ?_
  dsimp only [words8At, words27At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem words27At_sub_eq (sp0 : BitVec 64) (m : Nat) (d : Words27)
    (h0 : m < 2 ^ 64 := by decide) (h216 : 216 < m := by decide) :
    words27At ((sp0 - BitVec.ofNat 64 m) + 8#64) d = words27SubAt sp0 m d := by
  have hadd (k : Nat) (hk : k < m) :
      (sp0 - BitVec.ofNat 64 m) + BitVec.ofNat 64 k = sp0 - BitVec.ofNat 64 (m - k) :=
    bv_sub_add_lit sp0 m k hk h0
  dsimp only [words27At, words27SubAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hadd 8 (by omega), hadd 16 (by omega), hadd 24 (by omega), hadd 32 (by omega),
      hadd 40 (by omega), hadd 48 (by omega), hadd 56 (by omega), hadd 64 (by omega),
      hadd 72 (by omega), hadd 80 (by omega), hadd 88 (by omega), hadd 96 (by omega),
      hadd 104 (by omega), hadd 112 (by omega), hadd 120 (by omega), hadd 128 (by omega),
      hadd 136 (by omega), hadd 144 (by omega), hadd 152 (by omega), hadd 160 (by omega),
      hadd 168 (by omega), hadd 176 (by omega), hadd 184 (by omega), hadd 192 (by omega),
      hadd 200 (by omega), hadd 208 (by omega), hadd 216 (by omega)]

theorem memRegion_224_sub_entails_words28 (sp0 : BitVec 64) (m : Nat)
    (h0 : m < 2 ^ 64 := by decide) (h216 : 216 < m := by decide) :
    memRegion (sp0 - BitVec.ofNat 64 m) 224 ⊢
      ∃∗ (d0 : BitVec 64), ∃∗ (d : Words27),
        ((sp0 - BitVec.ofNat 64 m) ↦₆₄ d0) ∗ words27SubAt sp0 m d := by
  rw [memRegion_224_words28 (sp0 - BitVec.ofNat 64 m)]
  refine Entails.trans (sepConj_mono_right (memRegion_216_entails_words27 ((sp0 - BitVec.ofNat 64 m) + 8#64))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepExists_left_entails; intro d
  apply sepExists_left_entails; intro d0
  rw [words27At_sub_eq sp0 m d h0 h216]
  exact Entails.sepExists_right d0 (Entails.sepExists_right d (Entails.refl _))

theorem optProtoPqRatchetInnerAt_none_sub_entails_words27 (A : RustAlloc) (sp0 : BitVec 64) (m : Nat)
    (h0 : m < 2 ^ 64 := by decide) (h216 : 216 < m := by decide) :
    Drop.optProtoPqRatchetInnerAt A (sp0 - BitVec.ofNat 64 m) none ⊢
      ∃∗ d : Words27,
        ((sp0 - BitVec.ofNat 64 m) ↦₆₄ Drop.none3Cap') ∗ words27SubAt sp0 m d := by
  dsimp only [Drop.optProtoPqRatchetInnerAt]
  refine Entails.trans (sepConj_mono_right (memRegion_216_entails_words27 ((sp0 - BitVec.ofNat 64 m) + 8#64))) ?_
  simp only [sepExists_sepConj_right]
  apply sepExists_left_entails; intro d
  rw [words27At_sub_eq sp0 m d h0 h216]
  exact Entails.sepExists_right d (Entails.refl _)

theorem words27SubAt_to_memRegion_224 (sp0 : BitVec 64) (m : Nat) (w0 : BitVec 64) (d : Words27)
    (h0 : m < 2 ^ 64 := by decide) (h216 : 216 < m := by decide) :
    ((sp0 - BitVec.ofNat 64 m) ↦₆₄ w0) ∗ words27SubAt sp0 m d ⊢
      memRegion (sp0 - BitVec.ofNat 64 m) 224 := by
  rw [← words27At_sub_eq sp0 m d h0 h216]
  refine Entails.trans (sepConj_mono_right ?_) (word_memRegion216_to_memRegion_224 (sp0 - BitVec.ofNat 64 m) w0)
  exact words27_to_memRegion_216 ((sp0 - BitVec.ofNat 64 m) + 8#64)
    d.w0 d.w1 d.w2 d.w3 d.w4 d.w5 d.w6 d.w7 d.w8 d.w9 d.w10 d.w11 d.w12 d.w13
    d.w14 d.w15 d.w16 d.w17 d.w18 d.w19 d.w20 d.w21 d.w22 d.w23 d.w24 d.w25 d.w26

/-- Continuation after `Chain::into_pb` in `Ordering::Less` (`+1424 .. +1528 -> +824 .. +880 ->
    +2540`). -/
theorem step_initInner_chainFrom_ok_1424 {img : Obj.Image} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 w160 d0 d1 d2 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1424#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoAt img.base ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (s0.sp - 4992#64) vn ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      ((s0.sp - 4640#64) ↦₆₄ w160) ∗
      memRegion (s0.sp - 4632#64) 40 ∗
      ProtoRepr.chainPBAt A (s0.sp - 4592#64) ch.intoPb ∗
      memRegion (s0.sp - 4512#64) 224 ∗
      memRegion (s0.sp - 4288#64) 88 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d0) ∗
      ((s0.sp - 4104#64) ↦₆₄ d1) ∗
      ((s0.sp - 4096#64) ↦₆₄ d2) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 3056#64) none ∗
      memRegion (s0.sp - 2832#64) 736 ∗
      memRegion (s0.sp - 2096#64) 88 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hdrop_chain := spqrRecv_dropOptProtoChain_ok hdealloc
  simp only [Drop.dropOptProtoSpqrChainSpec] at hdrop_chain
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hnone3 : (Drop.none3Cap' + 3#64 == 0#64) = true := rfl
  have hslt_m1 : BitVec.slt 0xFFFFFFFFFFFFFFFF#64 1#64 = true := rfl
  apply SepWPpI.of_sepWP_ret
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdrop_chain hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1424 108
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 824 60
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  have hopt_some : ProtoRepr.chainPBAt A (s0.sp - 4592#64) ch.intoPb =
      ProtoRepr.optChainPBAt A (s0.sp - 4592#64) (some ch.intoPb) := rfl
  rw [← vnTail_some_eq_versionNegotiationPBAt A (s0.sp - 4992#64) w0 w1 vn,
      bv_sub_add_lit s0.sp 4992 8,
      bv_sub_add_lit s0.sp 4992 16,
      hopt_some]
  refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 4512) (by sep_focus) ?_
  wp_pull_exists; rename_i u0 uDst
  refine SepWP.focus_weaken (optProtoPqRatchetInnerAt_none_sub_entails_words27 A s0.sp 3056) (by sep_focus) ?_
  wp_pull_exists; rename_i uSrc
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r0 r1 r2 r3
  have hret_fold :
      ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 1#64) ∗ ((ret + 16#64) ↦₆₄ 0#64) ∗
        ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [hok]
    exact recv_ok_empty_foldX A ret
  have hjoin_dst := words27SubAt_to_memRegion_224 s0.sp 4512 Drop.none3Cap' uSrc
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_dst
  have hjoin_src := words27SubAt_to_memRegion_224 s0.sp 3056 Drop.none3Cap' uSrc
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_src
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_assoc]
  wp_steps 37
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)))
    (by sep_focus) ?_
  wp_call hdrop_chain ⟨s0.sp - 4592#64, some ch.intoPb⟩
  have hsp_eq : stackAt s.sp dropStack80 = stackAt (s0.sp - 4992#64) dropStack80 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack80 (by decide)).symm)
    (by sep_focus) ?_
  wp_steps 2
  refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
  refine SepWP.focus_weaken hjoin_dst (by sep_focus) ?_
  refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
  refine SepWP.focus_weaken (frame4544_join_ok_880 s0.sp 0xFFFFFFFFFFFFFFFF#64 d0 d1 d2) (by sep_focus) ?_
  refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
  exact step_drop_pre_2540 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret vn pb w0 w1
    s0 _ _ R _ rfl hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv

