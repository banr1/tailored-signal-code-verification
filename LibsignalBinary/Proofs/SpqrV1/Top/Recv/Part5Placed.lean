/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp

/-!
# Relocatable Version Dispatch for `spqr::recv`

Relocatable version-branch continuation contracts (`V0ChainPlacedTail`, `InitInnerPlacedTail`,
`V1RatchetPlacedTailLS`) and `spqr::decode_state` + version dispatch (`+312..+496`, `+744..+952`)
for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

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
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Continuation Contracts for the Three Version Branches (`+496`, `+1076`, `+1532`) -/

/-- Continuation contract at `+496` for the V0 chain-ratchet path (`Ordering::Greater`:
    `pre_pb.versionNegotiation = some vn`, `pre_pb.inner = some (.v1 pb)`, `pre.version ≥
    vn.minVersion.truncate 8`, and `pre.version > 1#8`). -/
def V0ChainPlacedTail (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (R : SepProp) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    Proto.spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ DecodeState.none2Cap →
    InnerWordInv pre_pb.inner w26 →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version > 1#8 →
    s.pc = spqrRecvPlacedEntry + 496#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x26 = w26 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)

/-- Continuation contract at `+1076` for the `init_inner` path (`Ordering::Less`:
    `pre_pb.versionNegotiation = some vn`, `pre_pb.inner = some (.v1 pb)`, `pre.version ≥
    vn.minVersion.truncate 8`, and `pre.version < 1#8`, i.e., `pre.version = 0#8` and
    `vn.minVersion.truncate 8 = 0#8`). -/
def InitInnerPlacedTail (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (R : SepProp) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    Proto.spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.versionNegotiation = some vn →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ DecodeState.none2Cap →
    InnerWordInv pre_pb.inner w26 →
    ¬(pre.version < vn.minVersion.truncate 8) →
    pre.version < 1#8 →
    s.pc = spqrRecvPlacedEntry + 1076#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x25 = pre.version.zeroExtend 64 →
    s.readReg64 .x26 = w26 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)

/-- `SepWPpLS` continuation contract at `+1532` for the V1 ratchet path (`Ordering::Equal`). -/
def V1RatchetPlacedTailLS (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (R : SepProp) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    Proto.spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ DecodeState.none2Cap →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    s.pc = spqrRecvPlacedEntry + 1532#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x26 = 0#64 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R)

theorem SepWPpLS.of_sepWP_ret {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog ret s P Q) :
    SepWPpLS prog ret s P Q Qp :=
  SepWPpLS.of_sepWPp (SepWPp.of_sepWP_ret h)

theorem SepWPpLS.pre_mono {prog : Program} {ret : BitVec 64}
    {s : State} {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPpLS prog ret s P' Q Qp) :
    SepWPpLS prog ret s P Q Qp :=
  fun hinv R hm hL => hwp hinv R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem SepWPpLS.focus_weaken {prog : Program} {ret : BitVec 64}
    {s : State} {P P₁ P₁' P_rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hw : P₁ ⊢ P₁') (hfocus : P = P₁ ∗ P_rest)
    (hwp : SepWPpLS prog ret s (P₁' ∗ P_rest) Q Qp) :
    SepWPpLS prog ret s P Q Qp :=
  SepWPpLS.pre_mono (Entails.trans (Entails.of_eq hfocus) (sepConj_mono_left hw)) hwp

theorem SepWPpLS.focus_pure {prog : Program} {ret : BitVec 64}
    {s : State} {P P_rest : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (hfocus : P = ⌜φ⌝ ∗ P_rest)
    (hwp : φ → SepWPpLS prog ret s P_rest Q Qp) :
    SepWPpLS prog ret s P Q Qp := by
  intro hinv R hm hL
  rw [hfocus, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hwp hm.1 hinv R hm.2 hL

/-- Lift `step_equal_792_placed` (`+792 .. +820 -> +1532`) to `SepWPpLS` using
    `V1RatchetPlacedTailLS`. -/
theorem step_equal_792_pLS (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw0_ne : w0 ≠ DecodeState.none2Cap)
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (htail : V1RatchetPlacedTailLS A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 792#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hmemcpy := hC.memcpy_ok
  simp only [framelessMemcpySpec] at hmemcpy
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  have hto :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ⊢
      ∃∗ bs352 : List (BitVec 8),
        ⌜bs352.length = 352⌝ ∗
        ((s0.sp - 4992#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).1 bs352 := by
    have h := (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).2.to_bytes (s0.sp - 4992#64)
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    rw [bv_sub_add_lit s0.sp 4992 8, bv_sub_add_lit s0.sp 4992 16,
        bv_sub_add_lit s0.sp 4992 48, bv_sub_add_lit s0.sp 4992 128] at h
    exact h
  have hsplit_4544 :
      memRegion (s0.sp - 4640#64) 4544 =
        memRegion (s0.sp - 4640#64) 352 ∗ memRegion (s0.sp - 4288#64) 4192 :=
    ProofLib.memRegion_split' (b := s0.sp - 4640#64) (n := 352) (k := 4192)
      (b' := s0.sp - 4288#64) rfl (by bv_omega) (by decide)
  apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 1532#64)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy hpc ⊢
  refine SepWP.focus_weaken hto (by sep_focus) ?_
  wp_pull_exists; rename_i bs352
  wp_focus_pure; intro hlen352
  rw [hsplit_4544]
  have hof :
      ((s0.sp - 4640#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).1 bs352 ⊢
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4512#64) pre_pb.inner := by
    have h := (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).2.of_bytes (s0.sp - 4640#64) bs352 hlen352
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    rw [bv_sub_add_lit s0.sp 4640 8, bv_sub_add_lit s0.sp 4640 16,
        bv_sub_add_lit s0.sp 4640 48, bv_sub_add_lit s0.sp 4640 128] at h
    exact h
  have hsrc_mem : ((s0.sp - 4992#64) ↦ₛ bs352) ⊢ memRegion (s0.sp - 4992#64) 352 := by
    rw [← hlen352]
    exact ProofLib.pointsToBytes_entails_memRegion (s0.sp - 4992#64) bs352
  wp_steps 4
  have hdst_mem : memRegion (s0.sp - 4640#64) 352 = memRegion (s0.sp - 4640#64) bs352.length := by
    rw [hlen352]
  have hlen_lt : bs352.length < 2 ^ 64 := by rw [hlen352]; decide
  have hlen_eq : (352#64 : BitVec 64).toNat = bs352.length := hlen352.symm
  rw [hdst_mem]
  wp_call hmemcpy ⟨s0.sp - 4640#64, s0.sp - 4992#64, bs352⟩
  refine SepWP.focus_weaken hsrc_mem (by sep_focus) ?_
  refine SepWP.focus_weaken hof (by sep_focus) ?_
  refine SepWP.focus_weaken
    (optProtoPqRatchetInnerAt_expose_word A (s0.sp - 4512#64) pre_pb.inner) (by sep_focus) ?_
  wp_pull_exists; rename_i w8 P_inner
  wp_focus_pure; intro hw8
  wp_focus_pure; intro hunexp
  have hw8_bne3 : (w8 + 3#64 != 0#64) = true := by
    rw [hinner] at hw8
    dsimp [InnerWordInv] at hw8
    simp [bne, hw8]
  wp_steps 4
  refine SepWP.focus_weaken hunexp (by sep_focus) ?_
  have hinner_eq : Drop.optProtoPqRatchetInnerAt A (s0.sp - 4512#64) pre_pb.inner =
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState := by
    rw [hinner]; rfl
  rw [hinner_eq]
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact htail pre remPtr pre_pb pb w0 w1 _ _ hpre hvalid hdec hinner hw0_ne hmv hmin
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)

/-- Dispatch at `+744` when `pre_pb.versionNegotiation = none` (`w0 = noneCap`). -/
theorem step_vn_none_744_placed (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = none)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_eq : V1RatchetPlacedTailLS A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 744#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = if (w26 + 3#64 != 0#64) = true then 1#64 else 0#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = noneCap)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ noneCap) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A noneCap w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  subst hP
  cases hinner : pre_pb.inner with
  | none =>
    have hw26_eq : w26 = none3Cap' := by
      rw [hinner] at hw26; exact hw26
    subst hw26_eq
    have hx8_0 : s.readReg64 .x8 = 0#64 := by
      rw [hx8]; rfl
    have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
      spqrV1Recv_recv_of_ok
        (recv_vn_none_inner_none (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
          (pqRatchetStateToPb_inner_none hinner))
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    by_cases hv0 : pre.version = 0#8
    · rw [hv0] at hx25
      wp_steps 5
      refine sepWP_spqrRecvPlacedPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb noneCap w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hinner]) hcl
    · have hne0 := zeroExtend32_bne_zero_of_ne hv0
      wp_steps 5
      refine sepWP_spqrRecvPlacedPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb noneCap w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hinner]) hcl
  | some inn =>
    cases inn with
    | v1 pb =>
      have hw26_ne : ¬((w26 + 3#64 == 0#64) = true) := by
        rw [hinner] at hw26; exact hw26
      have hw26_bne : (w26 + 3#64 != 0#64) = true := by
        simp [bne, hw26_ne]
      have hx8_1 : s.readReg64 .x8 = 1#64 := by
        rw [hx8, hw26_bne]; rfl
      rcases version_trichotomy pre.version with hlt | heq | hgt
      · have hv0 : pre.version = 0#8 := version_eq_zero_of_lt_one hlt
        have hrust : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) st.bytes msg.bytes =
            .error (.err .minimumVersion) := by
          refine recv_vn_none_lt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn ?_
          simp [stateVersion, pqRatchetStateToPb_inner_some hinner, Version.toU8, hlt]
        have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
          spqrV1Recv_recv_of_err hrust
        have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
          spqrV1Recv_noPanic_of_err hrust
        apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
        dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [hv0] at hx25
        wp_steps 2
        refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
        exact step_err_minVersion_752_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb noneCap w1 w26
          hw26 herr s0 _ _ R _ rfl hs0_align
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hinner]) hcl
      · apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 792#64)
        dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [heq] at hx25
        wp_steps 5
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        exact step_equal_792_pLS H_inner A F K ext hC h_inner_eq st msg ret pre remPtr pre_pb pb noneCap w1
          hpre hvalid hdec hinner (by decide) heq (by intro vn hvn'; rw [hvn] at hvn'; cases hvn')
          s0 _ _ R htail_eq hs0_align
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by rw [← hinner])
      · have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
          spqrV1Recv_recv_of_err
            (recv_vn_none_inner_some_gt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
              (pqRatchetStateToPb_inner_some hinner) hgt)
        have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
          spqrV1Recv_noPanic_of_err
            (recv_vn_none_inner_some_gt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
              (pqRatchetStateToPb_inner_some hinner) hgt)
        have hule1 := one_ule_zeroExtend64_of_gt hgt
        have hbne1 := zeroExtend32_bne_one_of_gt hgt
        apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
        dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
        rw [hvn]
        dsimp only [optVersionNegotiationPBTailAt]
        wp_focus_pure; intro _
        wp_steps 5
        refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
        refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
        exact step_err_versionMismatch_892_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w26
          hw26 herr s0 _ _ R _ rfl hs0_align
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by rw [← hinner]; ac_rfl) hcl

/-- Dispatch at `+448` when `pre_pb.versionNegotiation = some vn`. -/
theorem step_vn_some_448_placed (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hw0_ne : w0 ≠ DecodeState.none2Cap)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainPlacedTail A F K ext st msg ret s0 R)
    (htail_lt : InitInnerPlacedTail A F K ext st msg ret s0 R)
    (htail_eq : V1RatchetPlacedTailLS A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 448#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx8 : s.readReg64 .x8 = if (w26 + 3#64 != 0#64) = true then 1#64 else 0#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  subst hP
  by_cases hlt_min : pre.version < vn.minVersion.truncate 8
  · have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
      spqrV1Recv_recv_of_err
        (recv_vn_some_lt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn hlt_min)
    have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
      spqrV1Recv_noPanic_of_err
        (recv_vn_some_lt (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn hlt_min)
    have hult := ult_zeroExtend64_true_of_lt hlt_min
    have hule := ule_zeroExtend64_false_of_lt hlt_min
    apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    rw [hvn]
    refine SepWP.focus_weaken
      (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_pull_exists; rename_i P_vn
    wp_focus_pure; intro hunexp
    wp_steps 3
    refine SepWP.focus_weaken hunexp (by sep_focus) ?_
    refine sepWP_spqrRecvPlacedPost_of_post0 hnp ?_
    exact step_err_minVersion_752_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 w26
      hw26 herr s0 _ _ R _ rfl hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [← hvn]; ac_rfl) hcl
  · have hult := ult_zeroExtend64_false_of_ge hlt_min
    have hule := ule_zeroExtend64_true_of_ge hlt_min
    cases hinner : pre_pb.inner with
    | none =>
      have hw26_eq : w26 = none3Cap' := by
        rw [hinner] at hw26; exact hw26
      subst hw26_eq
      have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
        spqrV1Recv_recv_of_ok
          (recv_vn_some_inner_none (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok hvn
            (pqRatchetStateToPb_inner_none hinner) hlt_min)
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
      rw [hvn]
      refine SepWP.focus_weaken
        (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
      wp_pull_exists; rename_i P_vn
      wp_focus_pure; intro hunexp
      wp_steps 5
      refine SepWP.focus_weaken hunexp (by sep_focus) ?_
      refine sepWP_spqrRecvPlacedPost_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_ok_none_912_placed A (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 none3Cap'
        hw26 hok s0 _ _ R _ rfl hs0_align
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [← hvn, ← hinner]; ac_rfl) hcl
    | some inn =>
      cases inn with
      | v1 pb =>
        have hw26_ne : ¬((w26 + 3#64 == 0#64) = true) := by
          rw [hinner] at hw26; exact hw26
        have hw26_bne : (w26 + 3#64 != 0#64) = true := by
          simp [bne, hw26_ne]
        have hx8_1 : s.readReg64 .x8 = 1#64 := by
          rw [hx8, hw26_bne]; rfl
        rcases version_trichotomy pre.version with hlt | heq | hgt
        · have hv0 : pre.version = 0#8 := version_eq_zero_of_lt_one hlt
          apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 1076#64)
          dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          rw [hv0] at hx25 hult hule
          dsimp at hx25 hult hule
          wp_steps 12
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact htail_lt pre remPtr pre_pb vn pb w0 w1 w26 _ _
            hpre hvalid hdec hvn hinner hw0_ne hw26 hlt_min hlt
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [hv0]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by rw [← hinner]; ac_rfl)
        · apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 792#64)
          dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          rw [heq] at hx25 hult hule
          dsimp at hx25 hult hule
          wp_steps 10
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact step_equal_792_pLS H_inner A F K ext hC h_inner_eq st msg ret pre remPtr pre_pb pb w0 w1
            hpre hvalid hdec hinner hw0_ne heq
            (by intro vn' hvn'; rw [hvn] at hvn'; cases hvn'; exact heq ▸ hlt_min)
            s0 _ _ R htail_eq hs0_align
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by rw [← hvn, ← hinner]; ac_rfl)
        · have hule1 := one_ule_zeroExtend64_of_gt hgt
          have hule1_false := ule_one_zeroExtend64_false_of_gt hgt
          have hbne1 := zeroExtend32_bne_one_of_gt hgt
          have hugt1 := ugt_zeroExtend32_one_of_gt hgt
          apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 496#64)
          dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
          rw [hvn]
          refine SepWP.focus_weaken
            (optVersionNegotiationPBTailAt_some_expose_minVersion A s0.sp w0 w1 vn) (by sep_focus) ?_
          wp_pull_exists; rename_i P_vn
          wp_focus_pure; intro hunexp
          wp_steps 12
          refine SepWP.focus_weaken hunexp (by sep_focus) ?_
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          exact htail_gt pre remPtr pre_pb vn pb w0 w1 w26 _ _
            hpre hvalid hdec hvn hinner hw0_ne hw26 hlt_min hgt
            (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by rw [← hinner]; ac_rfl)

/-- Steps `+408 .. +444`, reassembling `pre_pb` at `s0.sp - 4992#64` and `memRegion (s0.sp -
    4640#64) 4544`, and dispatches via `step_vn_none_744_placed` (`+744`) or
    `step_vn_some_448_placed` (`+448`). -/
theorem step_dispatch_408_placed (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8))
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hw0_ne : w0 ≠ DecodeState.none2Cap)
    (hbs96 : bs96.length = 96)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainPlacedTail A F K ext st msg ret s0 R)
    (htail_lt : InitInnerPlacedTail A F K ext st msg ret s0 R)
    (htail_eq : V1RatchetPlacedTailLS A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 408#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      ((s0.sp - 4960#64) ↦ₛ bs96) ∗
      (relocVnTailAndChainAt A w0 w1 pre_pb).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗
      (∃∗ P_tail : SepProp,
        ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
          memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_tail) ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hreassemble := head16_bs96_entails_vnTailAndChainAt A (s0.sp - 4992#64) w0 w1 w2 w3 bs96 pre_pb hbs96
  rw [bv_sub_add_lit s0.sp 4992 16, bv_sub_add_lit s0.sp 4992 24,
      bv_sub_add_lit s0.sp 4992 32, bv_sub_add_lit s0.sp 4992 48] at hreassemble
  subst hP
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 744#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    wp_pull_exists; rename_i P_tail
    wp_focus_pure; intro hP_tail_join
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A (s0.sp - 4864#64) pre_pb.inner) (by sep_focus) ?_
    wp_pull_exists; rename_i w26 P_inner
    wp_focus_pure; intro hw26
    wp_focus_pure; intro hunexp_inner
    wp_steps 9
    refine SepWP.focus_weaken hreassemble (by sep_focus) ?_
    refine SepWP.focus_weaken hunexp_inner (by sep_focus) ?_
    refine SepWP.focus_weaken hP_tail_join (by sep_focus) ?_
    rw [hvn]
    refine SepWP.focus_weaken (optVersionNegotiationPBTailAt_none_eq A w0 w1 (s0.sp - 4976#64)) (by sep_focus) ?_
    wp_focus_pure; intro hw0; subst hw0
    wp_steps 1
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_vn_none_744_placed H_inner A F K ext hC h_inner_eq st msg ret pre remPtr pre_pb w1 w26
      hpre hvalid hdec hvn hw26 s0 _ _ R htail_eq hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, bne, cset_ne_eq, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [← hvn]; ac_rfl)
  | some vn =>
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 448#64)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
    wp_pull_exists; rename_i P_tail
    wp_focus_pure; intro hP_tail_join
    refine SepWP.focus_weaken
      (optProtoPqRatchetInnerAt_expose_word A (s0.sp - 4864#64) pre_pb.inner) (by sep_focus) ?_
    wp_pull_exists; rename_i w26 P_inner
    wp_focus_pure; intro hw26
    wp_focus_pure; intro hunexp_inner
    wp_steps 9
    refine SepWP.focus_weaken hreassemble (by sep_focus) ?_
    refine SepWP.focus_weaken hunexp_inner (by sep_focus) ?_
    refine SepWP.focus_weaken hP_tail_join (by sep_focus) ?_
    rw [hvn]
    refine SepWP.focus_weaken
      (optVersionNegotiationPBTailAt_some_cap_lt A w0 w1 (s0.sp - 4976#64) vn) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    have hne_none := Drop.cap_add_one_beq_zero_false hcap_lt
    wp_steps 1
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    exact step_vn_some_448_placed H_inner A F K ext hC h_inner_eq st msg ret pre remPtr pre_pb vn w0 w1 w26
      hpre hvalid hdec hvn hw0_ne hw26 s0 _ _ R htail_gt htail_lt htail_eq hs0_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, bne, cset_ne_eq, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [← hvn]; ac_rfl)

/-- Steps from `+312` through `bl spqr::decode_state`, error/success handling at `+328..+408`,
    and version dispatch at `+408..+496` / `+744..+952`, continuing via `V0ChainPlacedTail`
    (`+496`), `InitInnerPlacedTail` (`+1076`), or `V1RatchetPlacedTailLS` (`+1532`). -/
theorem step_decode_and_dispatch_placed (H_inner : V1InnerHeapPred) {A : RustAlloc}
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (s0 s : State) (P R : SepProp)
    (htail_gt : V0ChainPlacedTail A F K ext st msg ret s0 R)
    (htail_lt : InitInnerPlacedTail A F K ext st msg ret s0 R)
    (htail_eq : V1RatchetPlacedTailLS A F K ext st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPlacedPreambleFrame A st msg ret s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hdec_call := hC.decodeState_ok
  subst hP
  unfold spqrRecvPlacedPreambleFrame
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 325)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine SepWP.focus_weaken (ownFrame_split_for_decode s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2 d3 b0 b1 b2
  wp_steps 4
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  unfold spqrRecvRoPlacedAt
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) decodeStateStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpLS.call_lscro hdec_call ⟨st, s0.sp - 3056#64⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    (rfl : _ = spqrRecvPlacedEntry + 328#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [decodeStatePlacedSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hst_len⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, _, hxfp_c, _⟩
  dsimp only [decodeStatePlacedSpecX]
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by
    rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = pre.epoch := by
    rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length := by
    rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = remPtr := by
    rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = pre.version.zeroExtend 64 := by
    rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = s0.sp - 3056#64 := by
    rw [hx26_c]; simp only [arm64_norm, *]
  have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by
    rw [hx27_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64
    rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpLS.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) decodeStateStackX (by decide)).symm)
    (by sep_focus) ?_
  have hro_fold :
      Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
        statesFromPbJumpTablePlacedAt ∗
        statesRecvRoPlacedAt ∗
        statesIntoPbJumpTablePlacedAt ⊢
      spqrRecvRoPlacedAt := Entails.refl _
  refine SepWPpLS.focus_weaken hro_fold (by sep_focus) ?_
  cases hdec : spqrDecodeState st.bytes with
  | error e =>
    apply SepWPpLS.of_sepWP_ret
    exact step_decode_err_328_placed H_inner A F K ext st msg ret pre e d0 d1 d2 d3 b0 b1 b2
      hpre hdec s0 sm _ R _ rfl hs0_align
      hpcm hrunm hspm' htr_sm' hx19_sm hx27_sm
      (by ac_rfl)
  | ok pre_pb =>
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 408#64)
    refine step_decode_ok_328_to_408_placed H_inner A ext hC hC.h_inner_eq st msg ret pre_pb
      d0 d1 d2 d3 b0 b1 b2 s0 sm _ _ hs0_align
      hpcm hrunm hspm' htr_sm' hx19_sm hx26_sm hx27_sm
      (by ac_rfl)
      ?_
    intro w0 w1 w2 w3 bs96 sm2 Pm2 hw0_ne hbs96 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2 hx29_2 hPm2
    apply SepWP.done hpc2 hrun2
    exact step_dispatch_408_placed H_inner A F K ext hC hC.h_inner_eq st msg ret pre remPtr pre_pb
      d0 d1 d2 d3 w0 w1 w2 w3 bs96 hpre hvalid hdec hw0_ne hbs96 s0 sm2 Pm2 R
      htail_gt htail_lt htail_eq hs0_align hpc2 hrun2 hsp2 htr2
      hx19_2 hx20_2
      (by rw [hx21_2, hx21_sm])
      (by rw [hx22_2, hx22_sm])
      (by rw [hx23_2, hx23_sm])
      (by rw [hx24_2, hx24_sm])
      (by rw [hx25_2, hx25_sm])
      hx27_2 hx28_2
      (by rw [hx29_2, hx29_sm])
      hPm2

end CryptoVerification.SpqrV1.Top.Recv
