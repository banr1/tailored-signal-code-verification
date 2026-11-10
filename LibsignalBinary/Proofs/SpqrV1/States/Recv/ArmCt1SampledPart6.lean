/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 6 (Path 5c)

**Checked by Lean.** Verifies `Split928` reconstruction of `States.ct2Sampled` (`tag = 12#64`) and
Path 5c (`outMsg = some decoded`, `recv_ek = .ok uc_ek`, `ack = true`: `<Ct1SentEkReceived>::send_ct2`,
`send_ct2_encoder`, deallocations, and epilogue convergence `+16596 -> +18996`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible]
  libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  polyDecoderAt polyEncoderAt unchunkedCt1SentAt chunkAt
  statesRecvSavedCells statesRecvJumpTableAt

attribute [-simp, -arm64_norm]
  statesRecv_fnOff

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

theorem fnAddr_adrp_59890 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 17468#64) &&&
      0xfffffffffffff000#64) = b + 0x54000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

/-! ## 1. `Split928` Assembly and Reconstruction for `States.ct2Sampled` (Path 5c) -/

/-- Builds the `Split928` for `States.ct2Sampled` (`tag = 12#64`) from:
    - `c_enc : Words50` (`400`B `PolyEncoder` at `+8..+408`),
    - `g : AuthWords` and `epoch : BitVec 64` (`56`B `Unchunked.SendCt.Ct2Sent` at `+408..+464`),
    - trailing padding words `w10, w11, w13, w14, w15`, `mid : List (BitVec 8)` (`376`B), and `tail : Words5` (`40`B). -/
def mkSplit928Ct2Sampled (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (w10 w11 w13 w14 w15 : BitVec 64) (mid : List (BitVec 8)) (tail : Words5) : Split928 where
  c0 := {
    w0 := 12#64
    w1 := c_enc.c0.w0
    w2 := c_enc.c0.w1
    w3 := c_enc.c0.w2
    w4 := c_enc.c0.w3
    w5 := c_enc.c0.w4
    w6 := c_enc.c0.w5
    w7 := c_enc.c0.w6
    w8 := c_enc.c0.w7
    w9 := c_enc.c0.w8
    w10 := c_enc.c0.w9
    w11 := c_enc.c0.w10
    w12 := c_enc.c0.w11
    w13 := c_enc.c0.w12
    w14 := c_enc.c0.w13
    w15 := c_enc.c0.w14
  }
  c1 := {
    w0 := c_enc.c0.w15
    w1 := c_enc.c1.w0
    w2 := c_enc.c1.w1
    w3 := c_enc.c1.w2
    w4 := c_enc.c1.w3
    w5 := c_enc.c1.w4
    w6 := c_enc.c1.w5
    w7 := c_enc.c1.w6
    w8 := c_enc.c1.w7
    w9 := c_enc.c1.w8
    w10 := c_enc.c1.w9
    w11 := c_enc.c1.w10
    w12 := c_enc.c1.w11
    w13 := c_enc.c1.w12
    w14 := c_enc.c1.w13
    w15 := c_enc.c1.w14
  }
  c2 := {
    w0 := c_enc.c1.w15
    w1 := c_enc.c2.w0
    w2 := c_enc.c2.w1
    w3 := c_enc.c2.w2
    w4 := c_enc.c2.w3
    w5 := c_enc.c2.w4
    w6 := c_enc.c2.w5
    w7 := c_enc.c2.w6
    w8 := c_enc.c2.w7
    w9 := c_enc.c2.w8
    w10 := c_enc.c2.w9
    w11 := c_enc.c2.w10
    w12 := c_enc.c2.w11
    w13 := c_enc.c2.w12
    w14 := c_enc.c2.w13
    w15 := c_enc.c2.w14
  }
  c3 := {
    w0 := c_enc.c2.w15
    w1 := c_enc.w48
    w2 := c_enc.w49
    w3 := g.v1.w0
    w4 := g.v1.w1
    w5 := g.v1.w2
    w6 := g.v2.w0
    w7 := g.v2.w1
    w8 := g.v2.w2
    w9 := epoch
    w10 := w10
    w11 := w11
    w12 := c_enc.c2.w2
    w13 := w13
    w14 := w14
    w15 := w15
  }
  mid := mid
  tail := tail

theorem mkSplit928Ct2Sampled_mid_length (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (w10 w11 w13 w14 w15 : BitVec 64) {mid : List (BitVec 8)} (tail : Words5)
    (h : mid.length = 376) :
    (mkSplit928Ct2Sampled c_enc g epoch w10 w11 w13 w14 w15 mid tail).mid.length = 376 := h

theorem split928At_mkSplit928Ct2Sampled_eq (outA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (w10 w11 w13 w14 w15 : BitVec 64) (mid : List (BitVec 8)) (tail : Words5) :
    split928At outA (mkSplit928Ct2Sampled c_enc g epoch w10 w11 w13 w14 w15 mid tail) =
      ((outA ↦₆₄ 12#64) ∗
        words50At (outA + 8#64) c_enc ∗
        wordsAt (outA + 408#64) (ct2SentWordsList g epoch) ∗
        wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList) := by
  dsimp only [split928At, mkSplit928Ct2Sampled, words50At, ct2SentWordsList, authWordsList,
    vecWordsList, Words16.toList, Words5.toList]
  simp only [List.cons_append, List.nil_append,
    wordsAt_16, wordsAt_7, wordsAt_6, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem split928At_reconstruct_ct2Sampled (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64)
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (outEnc : PolyEncoder)
    (c_enc : Words50) (g : AuthWords)
    (w10 w11 w13 w14 w15 : BitVec 64) {mid : List (BitVec 8)} (tail : Words5)
    (hmid : mid.length = 376) :
    split928At outA (mkSplit928Ct2Sampled c_enc g outUc.epoch w10 w11 w13 w14 w15 mid tail) ∗
      relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
    chunkedStatesAt A outA (.ct2Sampled { uc := outUc, sending_ct2 := outEnc }) := by
  rw [split928At_mkSplit928Ct2Sampled_eq]
  have henc :
      words50At (outA + 8#64) c_enc ∗
        relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes ⊢
      polyEncoderAt A (outA + 8#64) outEnc := by
    rw [words50At_eq_pointsToBytes]
    exact relocatedHeap_recompose (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes (outA + 8#64)
  have huc :
      wordsAt (outA + 408#64) (ct2SentWordsList g outUc.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
      unchunkedCt2SentAt A (outA + 408#64) outUc := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose (fun dst => unchunkedCt2SentAt A dst outUc)
      (wordsBytes (ct2SentWordsList g outUc.epoch)) (outA + 408#64)
  have h48 :
      wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ⊢
      memRegion (outA + 464#64) 48 :=
    wordsAt_entails_memRegion [w10, w11, c_enc.c2.w2, w13, w14, w15] (outA + 464#64) 48 rfl
  have h376 :
      ((outA + 512#64) ↦ₛ mid) ⊢ memRegion (outA + 512#64) 376 := by
    rw [← hmid]
    exact ProofLib.pointsToBytes_entails_memRegion (outA + 512#64) mid
  have h40 :
      wordsAt (outA + 888#64) tail.toList ⊢ memRegion (outA + 888#64) 40 :=
    wordsAt_entails_memRegion tail.toList (outA + 888#64) 40 rfl
  have h464 :
      wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList ⊢
      memRegion (outA + 464#64) 464 := by
    refine Entails.trans (sepConj_mono h48 (sepConj_mono h376 h40)) ?_
    rw [← ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
          (b' := outA + 888#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := outA + 464#64) (n := 48) (k := 416)
          (b' := outA + 512#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hrearr :
      ((outA ↦₆₄ 12#64) ∗
        words50At (outA + 8#64) c_enc ∗
        wordsAt (outA + 408#64) (ct2SentWordsList g outUc.epoch) ∗
        wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList) ∗
      relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) =
      (outA ↦₆₄ 12#64) ∗
      ((words50At (outA + 8#64) c_enc ∗
        relocatedHeap (fun dst => polyEncoderAt A dst outEnc) c_enc.toBytes) ∗
       (wordsAt (outA + 408#64) (ct2SentWordsList g outUc.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
          (wordsBytes (ct2SentWordsList g outUc.epoch)))) ∗
      (wordsAt (outA + 464#64) [w10, w11, c_enc.c2.w2, w13, w14, w15] ∗
        ((outA + 512#64) ↦ₛ mid) ∗
        wordsAt (outA + 888#64) tail.toList) := by ac_rfl
  rw [hrearr]
  have hdest :
      chunkedStatesAt A outA (.ct2Sampled { uc := outUc, sending_ct2 := outEnc }) =
      (outA ↦₆₄ 12#64) ∗
        (polyEncoderAt A (outA + 8#64) outEnc ∗
          unchunkedCt2SentAt A (outA + 408#64) outUc) ∗
        memRegion (outA + 464#64) 464 := by
    dsimp only [chunkedStatesAt, chunkedCt2SampledAt]
    have h408 : (outA + 8#64) + 400#64 = outA + 408#64 := by bv_omega
    rw [h408]
  rw [hdest]
  exact sepConj_mono_right (sepConj_mono (sepConj_mono henc huc) h464)

/-- Scratch staging layout for Path 5c (`States.ct2Sampled`), where `c0.w11` (`fsp + 88`) and
    `w90` (`fsp + 144`) retain their prior values from `sc`. -/
def copyFullScratchCt2 (sc : CopyScratchStack) (d : Split928) : CopyScratchStack :=
  { (copyFullScratch sc d) with
    c0 := { (copyFullScratch sc d).c0 with w11 := sc.c0.w11 }
    w90 := sc.w90 }

set_option maxHeartbeats 1200000 in
/-- Bridge step between `send_ct2` return (`+11636`, `0x581c8`) and `send_ct2_encoder` call
    (`+11692 -> +59092`, `0x58200`): copies `7` words of `outUc` (`ct2SentWordsList g_uc outUc.epoch`)
    from `fsp + 3992..4048` to `fsp + 2256..2312` (`sp + 0x8d0..0x908`), collapses `fsp + 3992..4096`
    into `memRegion (fsp + 3992#64) 104`, loads `(ct2Ptr, ct2.length, macPtr, mac.length)` into
    `(x1, x2, x3, x4)` and `(macCap, ct2Cap, ct2Ptr, macPtr)` into `(x20, x25, x26, x27)`, and
    executes `bl 0x63b28` to reach `entry + 59092#64`. -/
theorem ct1Sampled_send_ct2_mid_step
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64)
    (g_uc : AuthWords) (epoch : BitVec 64)
    (ct2Cap ct2Ptr ct2Len macCap macPtr macLen : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11636#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 59092#64) s_in
      (wordsAt (fsp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((fsp + 4048#64) ↦₆₄ ct2Cap) ∗
        ((fsp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((fsp + 4064#64) ↦₆₄ ct2Len) ∗
        ((fsp + 4072#64) ↦₆₄ macCap) ∗
        ((fsp + 4080#64) ↦₆₄ macPtr) ∗
        ((fsp + 4088#64) ↦₆₄ macLen) ∗
        memRegion (fsp + 2256#64) 56 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          memRegion (fsp + 3992#64) 104 ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc epoch) ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x0 = fsp + 1856#64 ∧
        sf.readReg64 .x1 = ct2Ptr ∧
        sf.readReg64 .x2 = ct2Len ∧
        sf.readReg64 .x3 = macPtr ∧
        sf.readReg64 .x4 = macLen ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = macCap ∧
        sf.readReg64 .x21 = fsp + 3856#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = ct2Cap ∧
        sf.readReg64 .x26 = ct2Ptr ∧
        sf.readReg64 .x27 = macPtr ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hpre :
      wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((s_in.sp + 4048#64) ↦₆₄ ct2Cap) ∗
        ((s_in.sp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((s_in.sp + 4064#64) ↦₆₄ ct2Len) ∗
        ((s_in.sp + 4072#64) ↦₆₄ macCap) ∗
        ((s_in.sp + 4080#64) ↦₆₄ macPtr) ∗
        ((s_in.sp + 4088#64) ↦₆₄ macLen) ∗
        memRegion (s_in.sp + 2256#64) 56 ∗
        Rest ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6,
        wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((s_in.sp + 4048#64) ↦₆₄ ct2Cap) ∗
        ((s_in.sp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((s_in.sp + 4064#64) ↦₆₄ ct2Len) ∗
        ((s_in.sp + 4072#64) ↦₆₄ macCap) ∗
        ((s_in.sp + 4080#64) ↦₆₄ macPtr) ∗
        ((s_in.sp + 4088#64) ↦₆₄ macLen) ∗
        (((s_in.sp + 2256#64) ↦₆₄ v0) ∗
          ((s_in.sp + 2264#64) ↦₆₄ v1) ∗
          ((s_in.sp + 2272#64) ↦₆₄ v2) ∗
          ((s_in.sp + 2280#64) ↦₆₄ v3) ∗
          ((s_in.sp + 2288#64) ↦₆₄ v4) ∗
          ((s_in.sp + 2296#64) ↦₆₄ v5) ∗
          ((s_in.sp + 2304#64) ↦₆₄ v6)) ∗
        Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (cells_7_unfold (s_in.sp + 2256#64)))))))))) ?_
    simp only [wordsAt_7, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v2
    apply Entails.sepExists_elim; intro v3
    apply Entails.sepExists_elim; intro v4
    apply Entails.sepExists_elim; intro v5
    apply Entails.sepExists_elim; intro v6
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.sepExists_right v6 (Entails.of_eq (by ac_rfl))))))))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro v1
  apply ProofLib.SepWP.exists_left; intro v2
  apply ProofLib.SepWP.exists_left; intro v3
  apply ProofLib.SepWP.exists_left; intro v4
  apply ProofLib.SepWP.exists_left; intro v5
  apply ProofLib.SepWP.exists_left; intro v6
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        (wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
          wordsAt (s_in.sp + 4048#64) [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen]) ∗
        wordsAt (s_in.sp + 2256#64) (ct2SentWordsList g_uc epoch) ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x0 = s_in.sp + 1856#64 ∧
      sf.readReg64 .x1 = ct2Ptr ∧
      sf.readReg64 .x2 = ct2Len ∧
      sf.readReg64 .x3 = macPtr ∧
      sf.readReg64 .x4 = macLen ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x20 = macCap ∧
      sf.readReg64 .x21 = s_in.sp + 3856#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x25 = ct2Cap ∧
      sf.readReg64 .x26 = ct2Ptr ∧
      sf.readReg64 .x27 = macPtr ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
      sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range b (Rust.withPanics ext) 11636 60
    dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    dsimp only [ct2SentWordsList, authWordsList, vecWordsList]
    simp only [List.cons_append, List.nil_append,
      wordsAt_7, wordsAt_6, BitVec.add_assoc, BitVec.reduceAdd, hx21, hx29]
    wp_steps
    wp_done
  · have h56 := wordsAt_entails_memRegion (ct2SentWordsList g_uc epoch) (s_in.sp + 3992#64) 56 rfl
    have h48 := wordsAt_entails_memRegion [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen]
      (s_in.sp + 4048#64) 48 rfl
    have h104 :
        wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
          wordsAt (s_in.sp + 4048#64) [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen] ⊢
        memRegion (s_in.sp + 3992#64) 104 := by
      refine Entails.trans (sepConj_mono h56 h48) ?_
      rw [← ProofLib.memRegion_split' (b := s_in.sp + 3992#64) (n := 56) (k := 48)
            (b' := s_in.sp + 4048#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact sepConj_mono_left h104

section SendCt2AndEncode

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi

@[local arm64_norm] private theorem mem_writeReg64_ct1s6 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases s; cases r <;> rfl
@[local arm64_norm] private theorem symtab_writeReg64_ct1s6 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl
@[local arm64_norm] private theorem mem_setPC_ct1s6 (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem = s.mem := by cases s; rfl
@[local arm64_norm] private theorem symtab_setPC_ct1s6 (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

private theorem imgCallInv_of_mem_symtab_ct1s6 (img : Obj.Image) {s s' : State}
    (hm : s'.mem = s.mem) (hs : s'.symtab = s.symtab) (h : ImgCallInv img s) :
    ImgCallInv img s' :=
  ⟨by rw [Obj.Image.frozenLoaded_iff, hm, ← Obj.Image.frozenLoaded_iff]; exact h.1,
   by rw [hs]; exact h.2⟩

private theorem unchunkedSendCt2_addr_ok_ext {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name) spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36780#64) spec := by
  refine Drop.sub_ok_of_addr_eq ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, unchunkedCt1SentEkReceivedSendCt2Name]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"]
  bv_omega

private theorem sendCt2Encoder_addr_ok_ext {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName) spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 59092#64) spec := by
  refine Drop.sub_ok_of_addr_eq ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, sendCt2EncoderName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "spqr::v1::chunked::send_ct::send_ct2_encoder"]
  bv_omega

abbrev ct1SampledSendCt2Cont (prog : Program) (s0 : State) (P_pan : Prop) (R : SepProp)
    (post : State → SepProp → Prop) : State → SepProp → Prop :=
  fun sm Pm =>
    SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))

private theorem call_growToCalleeExt_statesRecv {α : Type} {img : Obj.Image} {P_pan : Prop}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    {oldStack : Nat} {spec : Spec α} (x : α) (BodyPre BodyPost : SepProp)
    (hcall : subroutine_ok prog entry ((growToCalleeExt oldStack spec).inImage img))
    (hle : oldStack + (statesRecvCalleeStackXExt - oldStack) = statesRecvCalleeStackXExt)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {PureCond : Prop} {post : State → SepProp → Prop} (hpure : PureCond)
    (hpre_eq : spec.pre x s = ⌜PureCond⌝ ∗ BodyPre ∗ stackAt sp_call oldStack)
    (hpost_eq : ∀ sf, spec.post x s sf = ⌜sf.trace = s.trace⌝ ∗ BodyPost ∗ stackAt sp_call oldStack)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hinv : ImgCallInv img s) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hsplit : P = (BodyPre ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → ImgCallInv img sf → TraceCalleeSaved sf s0 →
      SepWP prog next_pc sf ((BodyPost ∗ stackAt sp_call statesRecvCalleeStackXExt) ∗ Frame)
        (ct1SampledSendCt2Cont prog s0 P_pan R post)) :
    SepWP prog entry s P (ct1SampledSendCt2Cont prog s0 P_pan R post) := by
  have hstk : stackAt sp_call statesRecvCalleeStackXExt =
      memRegion (sp_call - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack) ∗ stackAt sp_call oldStack := by
    have hbd : oldStack + (statesRecvCalleeStackXExt - oldStack) ≤ 2 ^ 64 := by rw [hle]; decide
    simpa only [hle] using
      ProofLib.stackAt_split_bottom sp_call oldStack (statesRecvCalleeStackXExt - oldStack) hbd
  apply SepWP.done hpc hrun
  refine CryptoVerification.LibsignalTripleRatchet.SepWPp.call_inImage hcall hinv (x := x) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_) (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hinv_sf => ?_)
  · intro R' hm; rw [hsplit, hstk] at hm
    dsimp only [growToCalleeExt]; rw [hsp, hpre_eq]
    have hm' : s.mem ⊨
        (BodyPre ∗ stackAt sp_call oldStack ∗
          memRegion (sp_call - BitVec.ofNat 64 statesRecvCalleeStackXExt)
            (statesRecvCalleeStackXExt - oldStack)) ∗ (Frame ∗ R') :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
    exact ⟨hpure, hm'⟩
  · dsimp only [growToCalleeExt] at hmem; rw [hpan_eq] at hmem
    exact Satisfies.mono (sepConj_mono_left (onPanic_alloc_entails_statesRecv htrace.1)) hmem
  · dsimp only [growToCalleeExt]; rw [hsp, hpost_eq sf, sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    refine SepWP.weaken_pre ?_ (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hinv_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩)
    rw [hstk]; exact Entails.of_eq (by ac_rfl)

private theorem ct1Sampled_send_ct2_and_encode_core
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {P_pan : Prop}
    {ext : String → Option (State → State)} {Inv : State → Prop} {StackP : BitVec 64 → SepProp}
    (hinv_mem : ∀ {s s' : State}, s'.mem = s.mem → s'.symtab = s.symtab → Inv s → Inv s')
    (hseq : ∀ {prog : Program} {mid target : BitVec 64} {s : State} {P P' : SepProp}
      {φ : State → Prop} {post' : State → SepProp → Prop},
      Inv s → SepWP prog mid s P (fun sm Pm => (Pm ⊢ P') ∧ φ sm) →
      (∀ sm, sm.pc = mid → sm.status = .Running → Inv sm → φ sm → SepWP prog target sm P' post') →
      SepWP prog target s P post')
    (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (outEnc : PolyEncoder) (Frame R : SepProp) {post : State → SepProp → Prop}
    (hcall_sc : ∀ {s : State} {P Frame' : SepProp}, Inv s →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36780#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 Reg.lr = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11636#64 →
      TraceCalleeSaved s s0 → s.readReg64 Reg.x0 = fsp + 3992#64 → s.readReg64 Reg.x1 = fsp + 3856#64 →
      P = (memRegion (fsp + 3992#64) 104 ∗ unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗
        unchunkedSendCt2RoAt b ∗ A.pool ∗ StackP fsp) ∗ Frame' →
      (∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11636#64 →
        sf.status = .Running → sf.sp = fsp → CalleeSavedPreserved s sf → Inv sf → TraceCalleeSaved sf s0 →
        SepWP (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 59092#64) sf
          ((unchunkedCt2SentAt A (fsp + 3992#64) outUc ∗ vecU8 A ((fsp + 3992#64) + 56#64) ct2 ∗
            vecU8 A ((fsp + 3992#64) + 80#64) mac ∗ memRegion (fsp + 3856#64) 128 ∗
            unchunkedSendCt2RoAt b ∗ A.pool ∗ StackP fsp) ∗ Frame')
          (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post)) →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36780#64) s P
        (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post))
    (hcall_enc : ∀ (ct2Ptr macPtr : BitVec 64) {s : State} {P Frame' : SepProp},
      ct2Ptr ≠ 0#64 → macPtr ≠ 0#64 → Inv s →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 59092#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 Reg.lr = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64 →
      TraceCalleeSaved s s0 → s.readReg64 Reg.x0 = fsp + 1856#64 → s.readReg64 Reg.x1 = ct2Ptr →
      s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length →
      s.readReg64 Reg.x3 = macPtr → s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length →
      P = (memRegion (fsp + 1856#64) 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗ A.pool ∗ StackP fsp) ∗ Frame' →
      (∀ sf : State, sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64 →
        sf.status = .Running → sf.sp = fsp → CalleeSavedPreserved s sf → Inv sf → TraceCalleeSaved sf s0 →
        SepWP (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64) sf
          ((polyEncoderAt A (fsp + 1856#64) outEnc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
            A.pool ∗ StackP fsp) ∗ Frame')
          (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post)) →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 59092#64) s P
        (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post))
    (hinv : Inv s_in) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11624#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (hnext : ∀ (sf : State) (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64 →
      sf.status = .Running → sf.sp = fsp → Inv sf →
      sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = macCap →
      sf.readReg64 .x21 = fsp + 3856#64 → sf.readReg64 .x24 = s_in.readReg64 .x24 →
      sf.readReg64 .x25 = ct2Cap → sf.readReg64 .x26 = ct2Ptr →
      sf.readReg64 .x27 = macPtr → sf.readReg64 .x28 = s_in.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 4144#64 → TraceCalleeSaved sf s0 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64) sf
        ((polyEncoderAt A (fsp + 1856#64) outEnc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          vecCapPtrDealloc A ct2Cap ct2Ptr ∗ vecCapPtrDealloc A macCap macPtr ∗
          memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
          unchunkedSendCt2RoAt b ∗ A.pool ∗ StackP fsp) ∗ Frame)
        (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36780#64) s_in
      ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗ memRegion (fsp + 3992#64) 104 ∗
        unchunkedSendCt2RoAt b ∗ A.pool ∗ StackP fsp) ∗ Frame)
      (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post) := by
  subst hsp
  have hmid_lem := @ct1Sampled_send_ct2_mid_step b ext
  states_recv_fetches_range b (Rust.withPanics ext) 11624 12
  dsimp only [ct1SampledSendCt2Cont, tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hcall_sc hcall_enc hmid_lem hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  refine hcall_sc
    (hinv_mem (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm])
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr.1, htr.2])
    (by simp only [Reg.x0, arm64_norm, hx29]) (by simp only [Reg.x1, arm64_norm, hx21]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 hinv1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  simp only [arm64_norm, hx21, hx29] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have h56_eq : (s_in.sp + 3992#64) + 56#64 = s_in.sp + 4048#64 := by bv_omega
  have h80_eq : (s_in.sp + 3992#64) + 80#64 = s_in.sp + 4072#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (unchunkedCt2SentAt_extract A (s_in.sp + 3992#64) outUc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s_in.sp + 4048#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr
  wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s_in.sp + 4072#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr
  wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  have hmid := hmid_lem sf1 s_in.sp g_uc outUc.epoch
    ct2Cap ct2Ptr (BitVec.ofNat 64 ct2.length) macCap macPtr (BitVec.ofNat 64 mac.length)
    (relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc) (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
      (ct2Ptr ↦ₛ ct2) ∗ vecU8Tail A ct2Cap ct2Ptr ct2 ∗ (macPtr ↦ₛ mac) ∗ vecU8Tail A macCap macPtr mac ∗
      memRegion (s_in.sp + 1856#64) 400 ∗ memRegion (s_in.sp + 3856#64) 128 ∗
      unchunkedSendCt2RoAt b ∗ A.pool ∗ StackP s_in.sp ∗ Frame)
    hfsp_align hpc1 hrun1 hsp1 hx21_1 hx29_1
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hseq hinv1 hmid (fun sf2 hpc2 hrun2 hinv2 ⟨hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2,
      hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hx30_2, htr2⟩ => ?_))
  refine hcall_enc ct2Ptr macPtr hct2_ne hmac_ne hinv2 hpc2 hrun2 hsp2 hx30_2 (htr2.trans htr1)
    hx0_2 hx1_2 hx2_2 hx3_2 hx4_2 (by sep_focus) (fun sf3 hpc3 hrun3 hsp3 hcs3 hinv3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2,
    hx19_1, hx24_1, hx28_1] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ct2Cap ct2Ptr ct2 hct2_le hct2_lt) (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A macCap macPtr mac hmac_le hmac_lt) (by sep_focus) ?_
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sf3 g_uc ct2Cap ct2Ptr macCap macPtr
      hpc3 hrun3 hsp3 hinv3 hx19_3 hx20_3 hx21_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 htr3)

/-- Calls `<Ct1SentEkReceived>::send_ct2` (`0x5e400`) and `send_ct2_encoder` (`0x63b28`) across
    `+11624 -> +11696` (`0x581bc..0x58204`), producing `polyEncoderAt A (fsp + 1856) outEnc`,
    `wordsAt (fsp + 2256) (ct2SentWordsList g_uc outUc.epoch)`, and `vecCapPtrDealloc` for `ct2` and `mac`. -/
theorem ct1Sampled_send_ct2_and_encode
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64} {P_pan : Prop}
    {ext : String → Option (State → State)} (hb : b &&& 0xfff#64 = 0#64)
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName) (sendCt2EncoderSpec A))
    (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac) (outEnc : PolyEncoder)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (Frame R : SepProp) {post : State → SepProp → Prop} (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11624#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (hnext : ∀ (sf : State) (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64 →
      sf.status = .Running → sf.sp = fsp →
      sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = macCap →
      sf.readReg64 .x21 = fsp + 3856#64 → sf.readReg64 .x24 = s_in.readReg64 .x24 →
      sf.readReg64 .x25 = ct2Cap → sf.readReg64 .x26 = ct2Ptr →
      sf.readReg64 .x27 = macPtr → sf.readReg64 .x28 = s_in.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 4144#64 → TraceCalleeSaved sf s0 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64) sf
        ((polyEncoderAt A (fsp + 1856#64) outEnc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          vecCapPtrDealloc A ct2Cap ct2Ptr ∗ vecCapPtrDealloc A macCap macPtr ∗
          memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
          unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗ Frame)
        (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36780#64) s_in
      ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗ memRegion (fsp + 3992#64) 104 ∗
        unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗ Frame)
      (ct1SampledSendCt2Cont (tripleRatchetProgAtExt b ext) s0 P_pan R post) := by
  have hsplit_sc := stackAt_statesRecvCallee_eq_unchunkedSendCt2' fsp
  have hsplit_enc := stackAt_statesRecvCallee_eq_sendCt2Encoder' fsp
  exact ct1Sampled_send_ct2_and_encode_core (Inv := fun _ => True)
    (StackP := fun sp => stackAt sp statesRecvCalleeStackX)
    (fun _ _ _ => trivial)
    (fun _ h1 h2 => seq_clean h1 (fun sm hpc_m hrun_m hφ => h2 sm hpc_m hrun_m trivial hφ))
    s0 s_in fsp uc_ek outUc ct2 mac outEnc Frame R
    (fun {_ _ Frame'} _ hpc_s hrun_s hsp_s hlr_s htr_s hx0_s hx1_s hP hcont =>
      call_sendCt2_statesRecv (P_pan := P_pan) (unchunkedSendCt2_ok_at_statesRecv hsendCt2) hb
        (fsp + 3992#64) (fsp + 3856#64) uc_ek outUc ct2 mac hsc
        (Frame := memRegion (fsp - 19552#64) 2832 ∗ Frame')
        hpc_s hrun_s hsp_s hfsp_align hlr_s htr_s hx0_s hx1_s (by rw [hP, hsplit_sc]; ac_rfl)
        (fun sf hpc_f hrun_f hsp_f hcs_f htr_f =>
          SepWP.weaken_pre (Entails.of_eq (by rw [hsplit_sc]; ac_rfl))
            (hcont sf hpc_f hrun_f hsp_f hcs_f trivial htr_f)))
    (fun ct2Ptr macPtr {_ _ Frame'} hct2_ne hmac_ne _ hpc_s hrun_s hsp_s hlr_s htr_s hx0_s hx1_s hx2_s hx3_s hx4_s hP hcont =>
      call_sendCt2Encoder_statesRecv (P_pan := P_pan) (sendCt2Encoder_ok_at_statesRecv hsendCt2Enc)
        (fsp + 1856#64) ct2Ptr macPtr ct2 mac outEnc hct2_ne hmac_ne henc
        (Frame := memRegion (fsp - 19552#64) 2096 ∗ Frame')
        hpc_s hrun_s hsp_s hfsp_align hlr_s htr_s hx0_s hx1_s hx2_s hx3_s hx4_s (by rw [hP, hsplit_enc]; ac_rfl)
        (fun sf hpc_f hrun_f hsp_f hcs_f htr_f =>
          SepWP.weaken_pre (Entails.of_eq (by rw [hsplit_enc]; ac_rfl))
            (hcont sf hpc_f hrun_f hsp_f hcs_f trivial htr_f)))
    trivial hfsp_align hpc hrun hsp htr hx21 hx29
    (fun sf g_uc ct2Cap ct2Ptr macCap macPtr hpc_f hrun_f hsp_f _ =>
      hnext sf g_uc ct2Cap ct2Ptr macCap macPtr hpc_f hrun_f hsp_f)

/-- Calls `<Ct1SentEkReceived>::send_ct2` and `send_ct2_encoder` across
    `+11624 -> +11696` (`0x581bc..0x58204`) under `.inImage img` + `statesRecvCalleeStackXExt`. -/
theorem ct1Sampled_send_ct2_and_encode_ext
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {K : MlKem} {P_pan : Prop}
    {ext : String → Option (State → State)} (hb : img.base &&& 0xfff#64 = 0#64)
    (hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      ((growToCalleeExt unchunkedSendCt2Stack
        (unchunkedCt1SentEkReceivedSendCt2Spec A F K img.base)).inImage img))
    (hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName)
      ((growToCalleeExt sendCt2EncoderStack (sendCt2EncoderSpec A)).inImage img))
    (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac) (outEnc : PolyEncoder)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (Frame R : SepProp) {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s_in) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11624#64)
    (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (hnext : ∀ (sf : State) (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11696#64 →
      sf.status = .Running → sf.sp = fsp → ImgCallInv img sf →
      sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = macCap →
      sf.readReg64 .x21 = fsp + 3856#64 → sf.readReg64 .x24 = s_in.readReg64 .x24 →
      sf.readReg64 .x25 = ct2Cap → sf.readReg64 .x26 = ct2Ptr →
      sf.readReg64 .x27 = macPtr → sf.readReg64 .x28 = s_in.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 4144#64 → TraceCalleeSaved sf s0 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 11696#64) sf
        ((polyEncoderAt A (fsp + 1856#64) outEnc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          vecCapPtrDealloc A ct2Cap ct2Ptr ∗ vecCapPtrDealloc A macCap macPtr ∗
          memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
          unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗ Frame)
        (ct1SampledSendCt2Cont (tripleRatchetProgAtExt img.base ext) s0 P_pan R post)) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr statesRecvName + 36780#64) s_in
      ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗ memRegion (fsp + 3992#64) 104 ∗
        unchunkedSendCt2RoAt img.base ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackXExt) ∗ Frame)
      (ct1SampledSendCt2Cont (tripleRatchetProgAtExt img.base ext) s0 P_pan R post) :=
  ct1Sampled_send_ct2_and_encode_core (Inv := ImgCallInv img)
    (StackP := fun sp => stackAt sp statesRecvCalleeStackXExt)
    (imgCallInv_of_mem_symtab_ct1s6 img)
    (fun hinv_m h1 h2 => seq_clean_inImage_ax hinv_m h1 h2)
    s0 s_in fsp uc_ek outUc ct2 mac outEnc Frame R
    (fun {_ _ Frame'} hinv_s hpc_s hrun_s hsp_s hlr_s htr_s hx0_s hx1_s hP hcont =>
      call_growToCalleeExt_statesRecv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩
        (memRegion (fsp + 3992#64) 104 ∗ unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗
          unchunkedSendCt2RoAt img.base ∗ A.pool)
        (unchunkedCt2SentAt A (fsp + 3992#64) outUc ∗ vecU8 A ((fsp + 3992#64) + 56#64) ct2 ∗
          vecU8 A ((fsp + 3992#64) + 80#64) mac ∗ memRegion (fsp + 3856#64) 128 ∗
          unchunkedSendCt2RoAt img.base ∗ A.pool)
        (unchunkedSendCt2_addr_ok_ext hsendCt2) (by decide) (Frame := Frame')
        (And.intro hb (And.intro hx0_s (And.intro hx1_s hsc)))
        (by dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]; rw [hsp_s]; ac_rfl)
        (fun _ => by dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]; rw [hsp_s]; ac_rfl)
        (fun _ => rfl) hinv_s hpc_s hrun_s hsp_s hfsp_align hlr_s htr_s (by rw [hP]; ac_rfl)
        (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f htr_f =>
          SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (hcont sf hpc_f hrun_f hsp_f hcs_f hinv_f htr_f)))
    (fun ct2Ptr macPtr {_ _ Frame'} hct2_ne hmac_ne hinv_s hpc_s hrun_s hsp_s hlr_s htr_s hx0_s hx1_s hx2_s hx3_s hx4_s hP hcont =>
      call_growToCalleeExt_statesRecv ⟨fsp + 1856#64, ct2Ptr, ct2, macPtr, mac, outEnc⟩
        (memRegion (fsp + 1856#64) 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗ A.pool)
        (polyEncoderAt A (fsp + 1856#64) outEnc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗ A.pool)
        (sendCt2Encoder_addr_ok_ext hsendCt2Enc) (by decide) (Frame := Frame')
        (And.intro hx0_s (And.intro hx1_s (And.intro hx2_s (And.intro hx3_s
          (And.intro hx4_s (And.intro hct2_ne (And.intro hmac_ne henc)))))))
        (by dsimp only [sendCt2EncoderSpec]; rw [hsp_s]; ac_rfl)
        (fun _ => by dsimp only [sendCt2EncoderSpec]; rw [hsp_s]; ac_rfl)
        (fun _ => rfl) hinv_s hpc_s hrun_s hsp_s hfsp_align hlr_s htr_s (by rw [hP]; ac_rfl)
        (fun sf hpc_f hrun_f hsp_f hcs_f hinv_f htr_f =>
          SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (hcont sf hpc_f hrun_f hsp_f hcs_f hinv_f htr_f)))
    hinv hfsp_align hpc hrun hsp htr hx21 hx29 hnext

end SendCt2AndEncode

set_option maxHeartbeats 1600000 in
/-- Staging block of Path 5c (`+11696 -> +12072`, `0x58204..0x5837c`):
    loads the `50` words of `c_enc` (`outEnc` at `fsp + 1856`) and `7` words of `outUc`
    (`ct2SentWordsList g epoch` at `fsp + 2256`) into `copyScratchStackAt` and
    `epilogueStoreStackPart1At`, keeping `c_enc.c1.w11` in `x20`, `g.v2.w2` in `x21`,
    `g.v2.w1` in `x22`, `c_enc.c0.w0` in `x23`, and moving old `x20` (`macCap`) to `x1`. -/
theorem ct1Sampled_copy_some_ack_stage
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (fsp stA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11696#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928Ct2Sampled c_enc g epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12072#64) s_in
      (words50At (fsp + 1856#64) c_enc ∗
        wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          words50At (fsp + 1856#64) c_enc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
          copyScratchStackAt fsp
            { (copyFullScratchCt2 sc d) with
              c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }
              w88 := sc.w88 } ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = c_enc.c1.w11 ∧
        sf.readReg64 .x21 = g.v2.w2 ∧
        sf.readReg64 .x22 = g.v2.w1 ∧
        sf.readReg64 .x23 = c_enc.c0.w0 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x26 = s_in.readReg64 .x26 ∧
        sf.readReg64 .x27 = s_in.readReg64 .x27 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  states_recv_fetches_range b (Rust.withPanics ext) 11696 376
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At,
    ct2SentWordsList, authWordsList, vecWordsList, Words16.toList]
  simp only [List.cons_append, List.nil_append,
    wordsAt_16, wordsAt_7, BitVec.add_assoc, BitVec.reduceAdd, hx29]
  wp_steps
  wp_done

/-- Deallocate `mac : Vec<u8>` at `+12072 -> +12088` (`0x5837c..0x5838c`):
    `cbz x1, 0x5838c; mov x0, x27; mov w2, #1; bl __rust_dealloc`. -/
theorem ct1Sampled_dealloc_mac_12072
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s_in : State) (fsp macCap macPtr : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12072#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = macCap)
    (hx27 : s_in.readReg64 .x27 = macPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12088#64) s_in
      (vecCapPtrDealloc A macCap macPtr ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x26 = s_in.readReg64 .x26 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx27
  have hdealloc_raw := dealloc_raw_ok_at_statesRecv hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  states_recv_fetches_range b (Rust.withPanics ext) 12072 16
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hdealloc_raw hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit]
  dsimp only [vecCapPtrDealloc]
  by_cases hmac : (s_in.readReg64 .x1 == 0#64) = true <;>
    simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    rw [← hsplit]
    wp_done
  · wp_steps
    wp_apply
    rw [← hsplit]
    wp_done

/-- Deallocate `ct2 : Vec<u8>` at `+12088 -> +12108` (`0x5838c..0x583a0`):
    `cbz x25, 0x583a0; mov x0, x26; mov x1, x25; mov w2, #1; bl __rust_dealloc`. -/
theorem ct1Sampled_dealloc_ct2_12088
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s_in : State) (fsp ct2Cap ct2Ptr : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12088#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx25 : s_in.readReg64 .x25 = ct2Cap)
    (hx26 : s_in.readReg64 .x26 = ct2Ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12108#64) s_in
      (vecCapPtrDealloc A ct2Cap ct2Ptr ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx25 hx26
  have hdealloc_raw := dealloc_raw_ok_at_statesRecv hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  states_recv_fetches_range b (Rust.withPanics ext) 12088 20
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat]
    at hpc hdealloc_raw hsplit ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rw [hsplit]
  dsimp only [vecCapPtrDealloc]
  by_cases hct2 : (s_in.readReg64 .x25 == 0#64) = true <;>
    simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    rw [← hsplit]
    wp_done
  · wp_steps
    wp_apply
    rw [← hsplit]
    wp_done

set_option maxHeartbeats 1600000 in
/-- Drop `sending_ct1 : [Poly; 16]` at `stA + 8` and `dec' : [SortedSet<Pt>; 16]` at `fsp + 2752`,
    and finish staging `w118, w60, w1e0, w88` (`+12108 -> +16160 -> +16596`,
    `0x583a0..0x583c0` and `0x59374..0x59388`). -/
theorem ct1Sampled_drop_and_finish_stage_12108
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s_in : State) (fsp stA : BitVec 64)
    (vecs_enc : List (List GF16)) (hvecs_enc_len : vecs_enc.length = NUM_POLYS)
    (vecs_dec : List (List Pt)) (hvecs_dec_len : vecs_dec.length = NUM_POLYS)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12108#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = c_enc.c1.w11)
    (hx21 : s_in.readReg64 .x21 = g.v2.w2)
    (hx22 : s_in.readReg64 .x22 = g.v2.w1)
    (hx23 : s_in.readReg64 .x23 = c_enc.c0.w0) :
    let d := mkSplit928Ct2Sampled c_enc g epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64) s_in
      (((fsp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A (stA + 8#64) vecs_enc ∗
        vecPtListOf A (fsp + 2752#64) vecs_dec ∗
        memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp
          { (copyFullScratchCt2 sc d) with
            c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }
            w88 := sc.w88 } ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 8#64) 384 ∗
          memRegion (fsp + 2752#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = 4#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hdrop_poly := dropPoly16_ok_at_statesRecv hdealloc
  have hdrop_ss := dropSortedSetPt16_ok_at_statesRecv hdealloc
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        memRegion (stA + 8#64) 384 ∗
        (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
        copyScratchStackAt s_in.sp (copyFullScratchCt2 sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = 4#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · states_recv_fetches_range b (Rust.withPanics ext) 12108 36
    states_recv_fetches_range b (Rust.withPanics ext) 16160 24
    dsimp only [tripleRatchetProgAtExt, statesRecvName, polyArrayBytes, BitVec.ofNat_eq_ofNat]
      at hpc hdrop_poly hdrop_ss hsplit ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::recv" = entry
    examples_hide_fetches
    rw [hsplit]
    dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
      epilogueStoreStackPart1At, epilogueStackOfSplit928, Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd, hx20, hx21, hx22, hx23]
    wp_steps
    wp_call hdrop_poly ⟨stA + 8#64, vecs_enc⟩
    wp_steps
    wp_call hdrop_ss ⟨s_in.sp + 2752#64, vecs_dec⟩
    wp_steps
    wp_done
  · have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2752_mr))

/-! ## 2. Path 5c Epilogue Convergence (`+16596 -> +16800 -> +17464 -> +18892 -> +18996`) -/

/-- Part 2a of Path 5c (`+16596 -> +16800`, `0x59528..0x59568`):
    copies `376`B from `fsp + 976` to `fsp + 3272` (`x28`), copies `fsp + 1352..1392` to `fsp + 3232..3272`,
    and branches on `x23 = 4#64` (`x8 = 3#64 > 1`) to `+16800` (`0x595f4`). -/
theorem ct1Sampled_copy_some_ack_part2a
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 4#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = 3#64 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw := memcpy_region_ok_at_statesRecv hmemcpy
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976]
  states_recv_fetches_range b (Rust.withPanics ext) 16596 64
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [Words5.toList]
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  wp_steps
  wp_call hmemcpy_raw ⟨s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976⟩
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
/-- Part 2b of Path 5c (`+16800 -> +17464 -> +18892 -> +18996`,
    `0x595f4..0x5961c`, `0x5988c..0x598ac`, `0x59e20..0x59e88`):
    checks `x8 = 3#64 ≠ 2#64`, checks `MAX_LOG_LEVEL_FILTER` (`0 <= 2`), writes `we0 = 12#64`
    and `we8 = noneCap`, loads registers from `copyScratchStackAt`, and falls through to `+18996`. -/
theorem ct1Sampled_copy_some_ack_part2b
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s_in : State) (fsp stA outA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (v576 v584 v592 : BitVec 64) (bs352_576 : List (BitVec 8))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 16800#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = 3#64)
    (hx19 : s_in.readReg64 .x19 = outA) :
    let d := mkSplit928Ct2Sampled c_enc g epoch (s_in.readReg64 .x2)
      k.wf8 k.w3c0 k.w3c8 k.w100 (mid376Bytes v576 v584 v592 bs352_576) k.tail
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        statesRecvRoAt b ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          statesRecvRoAt b ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  have hadrp := fnAddr_adrp_59890 (b := b) (H := Rust.withPanics ext) hb
  states_recv_fetches_range b (Rust.withPanics ext) 16800 44
  states_recv_fetches_range b (Rust.withPanics ext) 17464 36
  states_recv_fetches_range b (Rust.withPanics ext) 18892 104
  dsimp only [tripleRatchetProgAtExt, statesRecvName, statesRecvRoAt, unchunkedSendCt2RoAt,
    logOff, BitVec.ofNat_eq_ofNat] at hpc hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes v576 v584 v592 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) v576 v584 v592 bs352_576]
  dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx8]
  wp_steps
  wp_done

end CryptoVerification.SpqrV1.States.Recv
