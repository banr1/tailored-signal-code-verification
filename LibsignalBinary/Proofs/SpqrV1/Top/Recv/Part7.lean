/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Proof
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: `Ordering::Less` (`InitInnerTail`)

**Checked by Lean.** 88-byte (`Words11`) `Chain` relocation helpers and full symbolic execution
of the `Ordering::Less` (`pre.version < 1#8`, `+1076..+1420`) branch of `spqr::recv` (`0x5462c`),
discharging `InitInnerTail`.
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
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. 88-Byte (`11`-Word) Stack Slot Helpers (`Words11`) for `Chain` Moves -/

structure Words11 where
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

def words11At (out : BitVec 64) (d : Words11) : SepProp :=
  (out ↦₆₄ d.w0) ∗ ((out + 8#64) ↦₆₄ d.w1) ∗ ((out + 16#64) ↦₆₄ d.w2) ∗
  ((out + 24#64) ↦₆₄ d.w3) ∗ ((out + 32#64) ↦₆₄ d.w4) ∗ ((out + 40#64) ↦₆₄ d.w5) ∗
  ((out + 48#64) ↦₆₄ d.w6) ∗ ((out + 56#64) ↦₆₄ d.w7) ∗ ((out + 64#64) ↦₆₄ d.w8) ∗
  ((out + 72#64) ↦₆₄ d.w9) ∗ ((out + 80#64) ↦₆₄ d.w10)

def words11SubAt (sp0 : BitVec 64) (m : Nat) (d : Words11) : SepProp :=
  ((sp0 - BitVec.ofNat 64 m) ↦₆₄ d.w0) ∗
  ((sp0 - BitVec.ofNat 64 (m - 8)) ↦₆₄ d.w1) ∗
  ((sp0 - BitVec.ofNat 64 (m - 16)) ↦₆₄ d.w2) ∗
  ((sp0 - BitVec.ofNat 64 (m - 24)) ↦₆₄ d.w3) ∗
  ((sp0 - BitVec.ofNat 64 (m - 32)) ↦₆₄ d.w4) ∗
  ((sp0 - BitVec.ofNat 64 (m - 40)) ↦₆₄ d.w5) ∗
  ((sp0 - BitVec.ofNat 64 (m - 48)) ↦₆₄ d.w6) ∗
  ((sp0 - BitVec.ofNat 64 (m - 56)) ↦₆₄ d.w7) ∗
  ((sp0 - BitVec.ofNat 64 (m - 64)) ↦₆₄ d.w8) ∗
  ((sp0 - BitVec.ofNat 64 (m - 72)) ↦₆₄ d.w9) ∗
  ((sp0 - BitVec.ofNat 64 (m - 80)) ↦₆₄ d.w10)

theorem memRegion_88_entails_words11 (out : BitVec 64) :
    memRegion out 88 ⊢ ∃∗ d : Words11, words11At out d := by
  rw [ProofLib.memRegion_split' (b := out) (n := 24) (k := 64)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      memRegion_24_words3 out]
  refine Entails.trans (sepConj_mono_right (memRegion_64_entails_words8 (out + 24#64))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply sepExists_left_entails; intro a
  apply sepExists_left_entails; intro w2
  apply sepExists_left_entails; intro w1
  apply sepExists_left_entails; intro w0
  refine Entails.sepExists_right
    ⟨w0, w1, w2, a.w0, a.w1, a.w2, a.w3, a.w4, a.w5, a.w6, a.w7⟩ ?_
  dsimp only [words8At, words11At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem words11At_sub_eq (sp0 : BitVec 64) (m : Nat) (d : Words11)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    words11At (sp0 - BitVec.ofNat 64 m) d = words11SubAt sp0 m d := by
  have hadd (k : Nat) (hk : k < m) :
      (sp0 - BitVec.ofNat 64 m) + BitVec.ofNat 64 k = sp0 - BitVec.ofNat 64 (m - k) :=
    bv_sub_add_lit sp0 m k hk h0
  dsimp only [words11At, words11SubAt]
  rw [hadd 8 (by omega), hadd 16 (by omega), hadd 24 (by omega), hadd 32 (by omega),
      hadd 40 (by omega), hadd 48 (by omega), hadd 56 (by omega), hadd 64 (by omega),
      hadd 72 (by omega), hadd 80 (by omega)]

theorem memRegion_88_sub_entails_words11 (sp0 : BitVec 64) (m : Nat)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    memRegion (sp0 - BitVec.ofNat 64 m) 88 ⊢
      ∃∗ d : Words11, words11SubAt sp0 m d := by
  refine Entails.trans (memRegion_88_entails_words11 (sp0 - BitVec.ofNat 64 m)) ?_
  apply sepExists_left_entails; intro d
  rw [words11At_sub_eq sp0 m d h0 h80]
  exact Entails.sepExists_right d (Entails.refl _)

theorem words11SubAt_to_memRegion_88 (sp0 : BitVec 64) (m : Nat) (d : Words11)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    words11SubAt sp0 m d ⊢ memRegion (sp0 - BitVec.ofNat 64 m) 88 := by
  rw [← words11At_sub_eq sp0 m d h0 h80]
  exact words11_to_memRegion_88 (sp0 - BitVec.ofNat 64 m)
    d.w0 d.w1 d.w2 d.w3 d.w4 d.w5 d.w6 d.w7 d.w8 d.w9 d.w10

def chainWords11 (G : ChainProofs.ChainGhost) (c : Chain) (pad : BitVec 32) : Words11 :=
  { w0 := G.linksCap
    w1 := G.linksPtr
    w2 := G.linksHead
    w3 := BitVec.ofNat 64 (G.epochs.zip c.links).length
    w4 := G.nextRoot.cap
    w5 := G.nextRoot.ptr
    w6 := BitVec.ofNat 64 c.nextRoot.length
    w7 := c.currentEpoch
    w8 := c.sendEpoch
    w9 := c.params.maxOooKeys ++ c.params.maxJump
    w10 := pad ++ c.dir.toI32 }

theorem chainRepr_sub_entails_words11 (A : RustAlloc) (sp0 : BitVec 64) (m : Nat) (c : Chain)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    chainRepr A (sp0 - BitVec.ofNat 64 m) c ⊢
      ∃∗ (G : ChainProofs.ChainGhost), ∃∗ (pad : BitVec 32),
        ⌜G.linksCap ≠ Top.ChainFromVersionNegotiation.noneCap⌝ ∗
        words11SubAt sp0 m (chainWords11 G c pad) ∗
        chainAtHeap A G c := by
  refine Entails.trans (chainRepr_entails_words11 A (sp0 - BitVec.ofNat 64 m) c) ?_
  apply sepExists_left_entails; intro G
  apply sepExists_left_entails; intro pad
  refine Entails.sepExists_right G (Entails.sepExists_right pad ?_)
  rw [← words11At_sub_eq sp0 m (chainWords11 G c pad) h0 h80]
  dsimp only [words11At, chainWords11]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem words11_entails_chainAt (A : RustAlloc) (out : BitVec 64) (G : ChainProofs.ChainGhost) (c : Chain)
    (pad : BitVec 32) :
    words11At out (chainWords11 G c pad) ∗ chainAtHeap A G c ⊢
      ChainProofs.chainAt A out G c := by
  dsimp only [words11At, chainWords11]
  unfold ChainProofs.chainAt vecDequeAt vecDequeHeader vecU8At vecHeader chainParamsAt directionAt chainAtHeap
  have hp72 :
      ((out + 72#64) ↦₆₄ (c.params.maxOooKeys ++ c.params.maxJump)) =
        ((out + 0x48#64) ↦₃₂ c.params.maxJump) ∗ ((out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (out + 72#64) c.params.maxJump c.params.maxOooKeys).symm
  have hp80 :
      ((out + 80#64) ↦₆₄ (pad ++ c.dir.toI32)) =
        ((out + 0x50#64) ↦₃₂ c.dir.toI32) ∗ ((out + 0x54#64) ↦₃₂ pad) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      (ChainFromNorm.pointsTo32_pair_eq_pointsTo64 (out + 80#64) c.dir.toI32 pad).symm
  rw [hp72, hp80]
  have hpad : ((out + 0x54#64) ↦₃₂ pad) ⊢ memRegion (out + 0x54#64) 4 := by
    rw [ProofLib.memRegion_four (out + 0x54#64)]
    exact Entails.sepExists_right pad (Entails.refl _)
  rw [show
    ((out ↦₆₄ G.linksCap) ∗
      ((out + 8#64) ↦₆₄ G.linksPtr) ∗
      ((out + 16#64) ↦₆₄ G.linksHead) ∗
      ((out + 24#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
      ((out + 32#64) ↦₆₄ G.nextRoot.cap) ∗
      ((out + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      ((out + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ((out + 56#64) ↦₆₄ c.currentEpoch) ∗
      ((out + 64#64) ↦₆₄ c.sendEpoch) ∗
      (((out + 0x48#64) ↦₃₂ c.params.maxJump) ∗ ((out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys)) ∗
      (((out + 0x50#64) ↦₃₂ c.dir.toI32) ∗ ((out + 0x54#64) ↦₃₂ pad))) ∗
      (⌜G.epochs.length = c.links.length⌝ ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
          G.linksHead (G.epochs.zip c.links) ∗
        ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
            G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
        if G.nextRoot.cap = 0 then emp
        else
          A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
            memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
              (G.nextRoot.cap.toNat - c.nextRoot.length)) =
    ⌜G.epochs.length = c.links.length⌝ ∗
      ((out ↦₆₄ G.linksCap ∗ (out + 0x08#64) ↦₆₄ G.linksPtr ∗ (out + 0x10#64) ↦₆₄ G.linksHead ∗
          (out + 0x18#64) ↦₆₄ BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        vecDequeRingBuf A chainEpochSize chainEpochAlign (chainEpochAt A) G.linksCap G.linksPtr
          G.linksHead (G.epochs.zip c.links)) ∗
      (((out + 0x20#64) ↦₆₄ G.nextRoot.cap ∗ (out + 0x20#64 + 8#64) ↦₆₄ G.nextRoot.ptr ∗
          (out + 0x20#64 + 16#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
        ⌜c.nextRoot.length ≤ G.nextRoot.cap.toNat ∧
            G.nextRoot.cap.toNat < 2 ^ 63 ∧ G.nextRoot.ptr ≠ 0⌝ ∗
          if G.nextRoot.cap = 0 then emp
          else
            A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗ G.nextRoot.ptr ↦ₛ c.nextRoot ∗
              memRegion (G.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
                (G.nextRoot.cap.toNat - c.nextRoot.length)) ∗
      (out + 0x38#64) ↦₆₄ c.currentEpoch ∗ (out + 0x40#64) ↦₆₄ c.sendEpoch ∗
      ((out + 0x48#64) ↦₃₂ c.params.maxJump ∗ (out + 0x48#64 + 0x04#64) ↦₃₂ c.params.maxOooKeys) ∗
      (out + 0x50#64) ↦₃₂ c.dir.toI32 ∗ ((out + 0x54#64) ↦₃₂ pad) by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right hpad))))))

theorem words11SubAt_entails_chainAt (A : RustAlloc) (sp0 : BitVec 64) (m : Nat)
    (G : ChainProofs.ChainGhost) (c : Chain) (pad : BitVec 32)
    (h0 : m < 2 ^ 64 := by decide) (h80 : 80 < m := by decide) :
    words11SubAt sp0 m (chainWords11 G c pad) ∗ chainAtHeap A G c ⊢
      ChainProofs.chainAt A (sp0 - BitVec.ofNat 64 m) G c := by
  rw [← words11At_sub_eq sp0 m (chainWords11 G c pad) h0 h80]
  exact words11_entails_chainAt A (sp0 - BitVec.ofNat 64 m) G c pad

/-! ## 2. Success Path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1420 -> +1424`) -/

theorem sp_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl

theorem sp_setPState (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := rfl

/-- Success path of `spqr::chain_from` in `Ordering::Less` (`+1320 .. +1420 -> +1424`): copies
    `ch : Chain` (`88`B) from `s0.sp - 2096#64` (`sp + 0xb50`) to `s0.sp - 4200#64` (`sp +
    0x318`), calls `Chain::into_pb` (`0x60514`) writing to `s0.sp - 4592#64` (`sp + 0x190`), and
    continues to `step_initInner_chainFrom_ok_1424`. -/
theorem step_initInner_chainFrom_ok_1320 {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (ch : Chain)
    (w0 w1 : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none))
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
      chainRepr A (s0.sp - 2096#64) ch ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hinto_pb := spqrRecv_chainIntoPb_ok hC
  subst hP
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
      bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1320 104
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [frame1584_split_ok_1320 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d2 d1 d0 w160
  refine SepWP.focus_weaken (chainRepr_sub_entails_words11 A s0.sp 2096 ch) (by sep_focus) ?_
  wp_pull_exists; rename_i G pad
  wp_focus_pure; intro hcap_ne
  have hz_ch : (G.linksCap + 1#64 == 0#64) = false := add_one_beq_zero_of_ne_noneCap hcap_ne
  refine SepWP.focus_weaken (memRegion_88_sub_entails_words11 s0.sp 4200) (by sep_focus) ?_
  wp_pull_exists; rename_i dDst
  have hjoin_src := words11SubAt_to_memRegion_88 s0.sp 2096 (chainWords11 G ch pad)
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin_src
  have hpack_dst := words11SubAt_entails_chainAt A s0.sp 4200 G ch pad
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hpack_dst
  dsimp only [words11SubAt, chainWords11, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  simp only [sepConj_assoc]
  wp_steps 26
  refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
  refine SepWP.focus_weaken hpack_dst (by sep_focus) ?_
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hinto_pb ⟨s0.sp - 4592#64, s0.sp - 4200#64, G, ch⟩
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = entry + 1424#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [chainIntoPbSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, _⟩
  dsimp only [chainIntoPbSpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [arm64_norm, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
    (by sep_focus) ?_
  exact step_initInner_chainFrom_ok_1424 A F K ext hC.base_aligned hC.hA.dealloc
    st msg ret vn pb ch w0 w1 w160
    G.linksPtr G.linksHead (BitVec.ofNat 64 (G.epochs.zip ch.links).length)
    hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx20_sm (by ac_rfl)

/-! ## 3. `Ordering::Less` (`InitInnerTail`, `+1076 .. +1320`) -/

@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_48 (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551568#64 = sp0 - 144#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_544 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  unfold Kdf.HkdfToSliceProof.hsp
  bv_omega

theorem adrp_1152_ldr_ed0 {b entry : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hentry : spqrRecvEntry b ext = entry) :
    ((entry + 1152#64 &&& 18446744073709547520#64) +
        bv% (page% (ls_sym% "log::MAX_LOG_LEVEL_FILTER") - page% (ls_off% "spqr::recv" + 1152))) +
        bv% (ls_sym% "log::MAX_LOG_LEVEL_FILTER" % 4096) =
      b + bv% (ls_sym% "log::MAX_LOG_LEVEL_FILTER") := by
  subst hentry
  rw [← spqrRecvEntry_eq]
  dsimp only [tripleRatchetProgAtExt, spqrRecvName]
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "spqr::recv")]
  revert b hb; bv_kernel

theorem not_ult_two_imp_two_ule {v : BitVec 32} (h : ¬(v.ult 2#32 = true)) :
    (2#32).ule v = true := by
  revert v h; bv_kernel

theorem ult_two_imp_two_ule_false {v : BitVec 32} (h : v.ult 2#32 = true) :
    (2#32).ule v = false := by
  revert v h; bv_kernel

/-- When `¬(vn.direction.ult 2#32 = true)` (`Direction.fromI32? vn.direction = none`),
    `Ordering::Less` (`+1076 .. +1280`) stores `Err(InvalidStateEncoding)` (`tag = 0#8`) at
    `ret` and drops `pre_pb` via `step_drop_vn_936` / `step_drop_pre_952`. -/
theorem step_ordering_less_dir_none {img : Obj.Image} (A : RustAlloc)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_ge : ¬(vn.direction.ult 2#32 = true))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hx25' : s.readReg64 .x25 = 0#64 := by
    rw [hx25, zeroExtend64_eq_zero_of_lt_one hver_lt]
  clear hx25
  have hule : (2#32).ule vn.direction = true := not_ult_two_imp_two_ule hdir_ge
  have hdir_none : Direction.fromI32? vn.direction = none := direction_fromI32_of_two_ule hule
  have herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error true :=
    spqrV1Recv_lt_one_dir_none F K hpre hdec hvn hinner hmin hver_lt hdir_none
  apply SepWPpI.of_sepWP_ret
  subst hP
  rw [← hinner]
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1076 8
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1148 20
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1252 32
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  have hadrp_1152 := adrp_1152_ldr_ed0 hb hentry
  examples_hide_fetches
  rw [frame4544_split_1076 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i w30_slot b0_slot
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_logOff img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro
  wp_focus_pure; intro hP_ro
  refine SepWP.focus_weaken
    (optVersionNegotiationPBTailAt_some_expose_direction A s0.sp w0 w1 vn) (by sep_focus) ?_
  wp_pull_exists; rename_i P_dir
  wp_focus_pure; intro hP_dir
  refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 b8 r2 r3
  have hfold := recv_err_byte_foldX A ret r2 r3 0#8 true (by decide)
  rw [← herr] at hfold
  wp_steps 13
  refine SepWP.focus_weaken hP_ro (by sep_focus) ?_
  refine SepWP.focus_weaken hP_dir (by sep_focus) ?_
  refine SepWP.focus_weaken (frame4544_join_1076 s0.sp 0#8 0#32) (by sep_focus) ?_
  refine SepWP.fold hfold (by sep_focus) ?_
  have hvn_dealloc :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ⊢
      ⌜w0.toNat < 2 ^ 63⌝ ∗
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
        vecCapPtrDealloc A w0 w1 := by
    have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
    have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
    rw [← h8, ← h16]
    exact vnTail_some_entails_dealloc A (s0.sp - 4992#64) w0 w1 vn
  refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
  wp_focus_pure; intro hcap_lt
  dsimp only [vecCapPtrDealloc]
  by_cases hc0 : (w0 == 0#64) = true <;>
    simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
  · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
    subst hw0
    wp_steps 2
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
    refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_err_true herr) ?_
    exact step_drop_pre_952 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb w26 hw26
      s0 _ _ R _ rfl hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl)
  · wp_steps 1
    refine sepWP_spqrRecvPost_of_post0 (spqrV1Recv_noPanic_of_recv_err_true herr) ?_
    exact step_drop_vn_936 img.base A (spqrV1Recv F K) ext hb hdealloc st msg ret pre_pb w0 w1 w26 hw26
      s0 _ _ R _ rfl hs0_align
      (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl)

/-- Expose `w0, w1, vn.authKey.length, w1 ↦ₛ vn.authKey, vn.direction` for `+1252 .. +1296`
    (`init_inner`). -/
theorem vn_some_expose_dir_and_initInner (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) ⊢
    ⌜w1 ≠ 0#64⌝ ∗
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
      (w1 ↦ₛ vn.authKey) ∗
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
      (∃∗ P_vn : SepProp,
        ⌜((sp0 - 4992#64) ↦₆₄ w0) ∗
          ((sp0 - 4984#64) ↦₆₄ w1) ∗
          ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
          (w1 ↦ₛ vn.authKey) ∗
          ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn ⊢
          Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn⌝ ∗ P_vn) := by
  have h8 : (sp0 - 4992#64) + 8#64 = sp0 - 4984#64 := bv_sub_add_lit sp0 4992 8
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  have h36 : (sp0 - 4992#64) + 36#64 = sp0 - 4956#64 := bv_sub_add_lit sp0 4992 36
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
  rw [h36]
  refine Entails.trans
    (Entails.of_eq (show
      (⌜vn.authKey.length < 2 ^ 63⌝ ∗
        ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        vecU8BufRest A w0 w1 vn.authKey.length) ∗
        Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion ((sp0 - 4992#64) + 44#64) 4 =
      ⌜vn.authKey.length < 2 ^ 63⌝ ∗
        (vecU8BufRest A w0 w1 vn.authKey.length ∗
          (((sp0 - 4992#64) ↦₆₄ w0) ∗
            ((sp0 - 4984#64) ↦₆₄ w1) ∗
            ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
            (w1 ↦ₛ vn.authKey) ∗
            ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
            (Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
              (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
              memRegion ((sp0 - 4992#64) + 44#64) 4))) by ac_rfl)) ?_
  refine Entails.pure_left fun _ => ?_
  refine Entails.trans (sepConj_mono_left (vecU8BufRest_expose_ptr_ne_zero A w0 w1 vn.authKey.length)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hptr => Entails.pure_right hptr ?_
  let P_vn : SepProp :=
    vecU8BufRest A w0 w1 vn.authKey.length ∗
      Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
      (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
      memRegion ((sp0 - 4992#64) + 44#64) 4
  have hjoin :
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn ⊢
        Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn := by
    have hpack := header_bytesAt_rest_entails_vecU8At A (sp0 - 4992#64) w0 w1 vn.authKey
    rw [hbytes, h8, h16] at hpack
    rw [hvn_def, h36]
    refine Entails.trans (Entails.of_eq (show
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn =
      (((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        vecU8BufRest A w0 w1 vn.authKey.length) ∗
        Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
        memRegion ((sp0 - 4992#64) + 44#64) 4 by
      unfold P_vn; ac_rfl)) ?_
    exact sepConj_mono_left hpack
  refine Entails.trans (Entails.of_eq (show
    vecU8BufRest A w0 w1 vn.authKey.length ∗
      (((sp0 - 4992#64) ↦₆₄ w0) ∗
        ((sp0 - 4984#64) ↦₆₄ w1) ∗
        ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
        (w1 ↦ₛ vn.authKey) ∗
        ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗
        (Top.ChainFromVersionNegotiation.optChainParamsPBAt ((sp0 - 4992#64) + 24#64) vn.chainParams ∗
          (((sp0 - 4992#64) + 40#64) ↦₃₂ vn.minVersion) ∗
          memRegion ((sp0 - 4992#64) + 44#64) 4)) =
    ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      ((sp0 - 4976#64) ↦₆₄ BitVec.ofNat 64 vn.authKey.length) ∗
      (w1 ↦ₛ vn.authKey) ∗
      ((sp0 - 4956#64) ↦₃₂ vn.direction) ∗ P_vn by
    unfold P_vn; ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (Entails.sepExists_right P_vn (Entails.pure_right hjoin (Entails.refl _)))))))

theorem versionNegotiationPBAt_entails_vnTail_some (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (sp0 - 4992#64) vn ⊢
      ((sp0 - 4992#64) ↦₆₄ w0) ∗
      ((sp0 - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4976#64) (some vn) := by
  have h8 : (sp0 - 4992#64) + 8#64 = sp0 - 4984#64 := bv_sub_add_lit sp0 4992 8
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  rw [← h8, ← h16, ← vnTail_some_eq_versionNegotiationPBAt A (sp0 - 4992#64) w0 w1 vn]
  exact Entails.refl _

theorem optProtoPqRatchetInnerAt_none_entails_memRegion_224 (A : RustAlloc) (a : BitVec 64) :
    Drop.optProtoPqRatchetInnerAt A a none ⊢ memRegion a 224 := by
  dsimp only [Drop.optProtoPqRatchetInnerAt]
  rw [show (224 : Nat) = 8 + 216 by decide, memRegion_split a 8 216 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion a Drop.none3Cap')

theorem frame4544_join_1320 (sp0 : BitVec 64) (b0 : BitVec 8) (w30 : BitVec 32) :
    memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 1055 ∗
      memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44 ⊢
      memRegion (sp0 - 4640#64) 1584 ∗ memRegion (sp0 - 2008#64) 1912 := by
  have hlow :
      memRegion (sp0 - 4640#64) 528 ∗
        ((sp0 - 4112#64) ↦₈ b0) ∗
        memRegion (sp0 - 4111#64) 1055 ⊢
      memRegion (sp0 - 4640#64) 1584 := by
    conv_rhs =>
      rw [ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 528) (k := 1056)
          (b' := sp0 - 4112#64) (by decide) (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 4112#64) (n := 1) (k := 1055)
          (b' := sp0 - 4111#64) (by decide) (by bv_omega) (by decide),
        ProofLib.memRegion_one (sp0 - 4112#64)]
    exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right b0 (Entails.refl _)))
  have hhigh :
      memRegion (sp0 - 2008#64) 1864 ∗
        ((sp0 - 144#64) ↦₃₂ w30) ∗
        memRegion (sp0 - 140#64) 44 ⊢
      memRegion (sp0 - 2008#64) 1912 := by
    conv_rhs =>
      rw [ProofLib.memRegion_split' (b := sp0 - 2008#64) (n := 1864) (k := 48)
          (b' := sp0 - 144#64) (by decide) (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp0 - 144#64) (n := 4) (k := 44)
          (b' := sp0 - 140#64) (by decide) (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo32_entails_memRegion (sp0 - 144#64) w30))
  refine Entails.trans (Entails.of_eq (show
    memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 1055 ∗
      memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44 =
    (memRegion (sp0 - 4640#64) 528 ∗
      ((sp0 - 4112#64) ↦₈ b0) ∗
      memRegion (sp0 - 4111#64) 1055) ∗
    (memRegion (sp0 - 2008#64) 1864 ∗
      ((sp0 - 144#64) ↦₃₂ w30) ∗
      memRegion (sp0 - 140#64) 44) by ac_rfl)) ?_
  exact sepConj_mono hlow hhigh

/-- When `vn.direction.ult 2#32 = true` (`Direction.fromI32? vn.direction = some dir`),
    `Ordering::Less` (`+1076 .. +1320`) calls `spqr::init_inner` (`+1296`) with `v = .v0`, calls
    `spqr::chain_from` (`+1316`), and continues to `step_initInner_chainFrom_err_1320` or
    `step_initInner_chainFrom_ok_1320`. -/
theorem step_ordering_less_dir_some {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (hdir_lt : vn.direction.ult 2#32 = true)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
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
      ProtoRepr.optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hx25' : s.readReg64 .x25 = 0#64 := by
    rw [hx25, zeroExtend64_eq_zero_of_lt_one hver_lt]
  clear hx25
  obtain ⟨dir, hdir_some, hdir_eq⟩ := direction_fromI32_of_ult_two hdir_lt
  have hule : (2#32).ule vn.direction = false := ult_two_imp_two_ule_false hdir_lt
  have hak_len : 32 + vn.authKey.length < 2 ^ 63 :=
    vn_authKey_len_bound_of_spqrDecodeState (F := F) (K := K) hst_len hdec hvn
  have hinit_ok := spqrRecv_initInner_ok hC
  have hcf_ok := spqrRecv_chainFrom_ok hC
  subst hP
  apply SepWPpI.of_sepWP
    (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
      bv% (2 ^ 64 - ls_rel% "spqr::init_inner" "spqr::recv"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1076 8
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1148 20
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1252 12
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1284 16
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 1300 20
  generalize hentry : (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry at *
  have hadrp_1152 := adrp_1152_ldr_ed0 hC.base_aligned hentry
  examples_hide_fetches
  rw [frame4544_split_1076 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i w30_slot b0_slot
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_logOff img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_log
  wp_focus_pure; intro hP_ro_log
  refine SepWP.focus_weaken (vn_some_expose_dir_and_initInner A s0.sp w0 w1 vn) (by sep_focus) ?_
  wp_pull_exists; rename_i P_vn
  wp_focus_pure; intro hw1_ne
  wp_focus_pure; intro hP_vn
  wp_steps 14
  refine SepWP.focus_weaken hP_ro_log (by sep_focus) ?_
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_statesIntoPb img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_into
  wp_focus_pure; intro hP_ro_into
  have hsplit3967 :
      memRegion (s0.sp - 4111#64) 3967 =
        memRegion (s0.sp - 4111#64) 1055 ∗
        memRegion (s0.sp - 3056#64) Drop.optProtoInnerStateSize ∗
        memRegion (s0.sp - 2832#64) 736 ∗
        memRegion (s0.sp - 2096#64) 88 ∗
        memRegion (s0.sp - 2008#64) 1864 := by
    unfold Drop.optProtoInnerStateSize
    rw [ProofLib.memRegion_split' (b := s0.sp - 4111#64) (n := 1055) (k := 2912)
        (b' := s0.sp - 3056#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 3056#64) (n := 224) (k := 2688)
        (b' := s0.sp - 2832#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 2832#64) (n := 736) (k := 1952)
        (b' := s0.sp - 2096#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := s0.sp - 2096#64) (n := 88) (k := 1864)
        (b' := s0.sp - 2008#64) (by decide) (by bv_omega) (by decide)]
  rw [hsplit3967]
  simp only [sepConj_assoc]
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStack (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hinit_ok
    (⟨s0.sp - 3056#64, .v0, dir, w1, vn.authKey⟩ : InitInnerGhost)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hsp]; exact hs0_align)
    (rfl : _ = entry + 1300#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => by
      dsimp only [initInnerSpecX, initInnerSpec, initInnerOnPanic]
      exact onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [initInnerSpecX, initInnerSpec]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]; rfl,
          by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          hw1_ne, hak_len, hC.base_aligned⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsm with ⟨hx19_c, hx20_c, _⟩
  dsimp only [initInnerSpecX, initInnerSpec, initInnerResultAt_v0]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by
    rw [hx19_c]; simp only [arm64_norm, *]
  have hx20_sm : sm.readReg64 .x20 = w0 := by
    rw [hx20_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) initInnerStack (by decide)).symm)
    (by sep_focus) ?_
  refine SepWPpI.focus_weaken hP_vn (by sep_focus) ?_
  refine SepWPpI.focus_weaken hP_ro_into (by sep_focus) ?_
  refine SepWPpI.focus_weaken (frame4544_join_1320 s0.sp 0#8 0#32) (by sep_focus) ?_
  apply SepWPpI.of_sepWP
    (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::chain_from" "spqr::recv"))
  rw [optChainPBAt_protoRepr_eq_exists A (s0.sp - 4944#64) pre_pb.chain]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i gPb
  have hvn_ref :
      Top.ChainFromVersionNegotiation.versionNegotiationPBAt A ⟨w0, w1⟩ (s0.sp - 4992#64) vn ⊢
      ChainFrom.optVersionNegotiationRefAt A ⟨w0, w1⟩ (s0.sp - 4992#64) (some vn) :=
    Entails.pure_right hsp_ne (Entails.refl _)
  refine SepWP.focus_weaken hvn_ref (by sep_focus) ?_
  wp_steps 5
  apply Prost.EncodeToVec.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)))
    (by sep_focus) ?_
  refine SepWPpI.call_inImage hcf_ok
    (⟨s0.sp - 2096#64, s0.sp - 4944#64, s0.sp - 4992#64, gPb, ⟨w0, w1⟩, pre_pb.chain, some vn⟩ : ChainFromCall)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, hspm']; exact hs0_align)
    (rfl : _ = entry + 1320#64)
    (by simp only [arm64_norm, htr_sm']; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed)
    (fun _ _ => rfl)
    (by
      dsimp only [chainFromSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']; sep_focus))
    ?_
  intro sn hpcn hrunn hspn hcsn
  have hvregs_cn := hcsn.2.2.2.2.2.2.2.2.2.2.2
  rcases hcsn with ⟨hx19_cn, hx20_cn, _⟩
  dsimp only [chainFromSpecX, ChainFrom.optVersionNegotiationRefAt]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sn
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro _
  have htr_sn' : TraceVRegs sn s0 := ⟨by rw [htr_sn]; simp only [arm64_norm, *], by rw [hvregs_cn]; simp only [arm64_norm, *]⟩
  have hspn' : sn.sp = s0.sp - 4992#64 := by
    rw [hspn]; simp only [arm64_norm, *]
  have hx19_sn : sn.readReg64 .x19 = ret := by
    rw [hx19_cn]; simp only [arm64_norm, *]
  have hx20_sn : sn.readReg64 .x20 = w0 := by
    rw [hx20_cn]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128, sp_setPState, reduceCtorEq, ↓reduceIte, hspm']
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainFromStackX (by decide)).symm)
    (by sep_focus) ?_
  cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) with
  | error err =>
    obtain ⟨herr, hnp⟩ := spqrV1Recv_lt_one_chainFrom_err F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_err_1320 A F K ext hC.base_aligned hC.hA.dealloc
      st msg ret vn pb err w0 w1 herr hnp s0 sn _ R hs0_align
      (by dsimp only [tripleRatchetProgAtExt, spqrRecvName]; rw [hentry]; exact hpcn)
      hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; ac_rfl)
  | ok ch =>
    have hok : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok ([], none) :=
      spqrV1Recv_lt_one_chainFrom_ok F K hpre hdec hvn hinner hmin hver_lt hdir_eq hcf
    exact step_initInner_chainFrom_ok_1320 hC st msg ret vn pb ch w0 w1 hok
      s0 sn _ R hs0_align
      (by dsimp only [tripleRatchetProgAtExt, spqrRecvName]; rw [hentry]; exact hpcn)
      hrunn hspn' htr_sn' hx19_sn hx20_sn (by dsimp only [chainResultAt]; ac_rfl)

/-- Combined `Ordering::Less` (`+1076 .. +1420`) tail contract when `s0.sp - 4992#64 ≠ 0#64`. -/
theorem step_ordering_less {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContracts H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState)
    (vn : VersionNegotiationPB) (pb : V1State)
    (w0 w1 w26 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hvn : pre_pb.versionNegotiation = some vn)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hmin : ¬(pre.version < vn.minVersion.truncate 8))
    (hver_lt : pre.version < 1#8)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hsp_ne : s0.sp - 4992#64 ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 1076#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx25 : s.readReg64 .x25 = pre.version.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = w26)
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
      ProtoRepr.optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  by_cases hdir_lt : vn.direction.ult 2#32 = true
  · exact step_ordering_less_dir_some hC st msg ret pre pre_pb vn pb w0 w1
      hst_len hpre hdec hvn hinner hmin hver_lt hdir_lt
      s0 s P R hs0_align hsp_ne hpc hrun hsp htr hx19 hx20 hx25 hx29 hP
  · exact step_ordering_less_dir_none A F K ext hC.base_aligned hC.hA.dealloc
      st msg ret pre pre_pb vn pb w0 w1 w26
      hpre hdec hvn hinner hw26 hmin hver_lt hdir_lt
      s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx25 hx26 hx29 hP

end CryptoVerification.SpqrV1.Top.Recv
