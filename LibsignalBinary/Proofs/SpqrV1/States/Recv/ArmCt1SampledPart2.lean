/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledDefs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 2: Shared Store & Unchanged Paths

Shared `Ok(V1Recv)` store block (`0x59e88..0x59fd0`, `+18996 -> +19324`), scratch stack-frame
helpers (`fsp + 0..976`), and state-copy blocks for `msg.epoch < st.uc.epoch` (`+10500`) and
non-`ek` payloads (`+12144`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

/-! ## 1. Stack Bundle `[fsp + 224 .. fsp + 976]` for `0x59e88..0x59fd0` (`+18996 -> +19324`) -/

/-- The 47 8-byte words and 376-byte middle slice at `fsp + 224 .. fsp + 976` (`0xe0 .. 0x3d0`, 752B)
    read by the shared `.ct1Sampled` `Ok` return store block at `0x59e88..0x59fd0` (`+18996 -> +19324`). -/
structure EpilogueStoreStack where
  we0 : BitVec 64
  we8 : BitVec 64
  wf0 : BitVec 64
  wf8 : BitVec 64
  w100 : BitVec 64
  w108 : BitVec 64
  w110 : BitVec 64
  w118 : BitVec 64
  w120 : BitVec 64
  w128 : BitVec 64
  w130 : BitVec 64
  w138 : BitVec 64
  w140 : BitVec 64
  w148 : BitVec 64
  w150 : BitVec 64
  w158 : BitVec 64
  w160 : BitVec 64
  w168 : BitVec 64
  w170 : BitVec 64
  w178 : BitVec 64
  w180 : BitVec 64
  w188 : BitVec 64
  w190 : BitVec 64
  w198 : BitVec 64
  w1a0 : BitVec 64
  w1a8 : BitVec 64
  w1b0 : BitVec 64
  w1b8 : BitVec 64
  w1c0 : BitVec 64
  w1c8 : BitVec 64
  w1d0 : BitVec 64
  w1d8 : BitVec 64
  w1e0 : BitVec 64
  w1e8 : BitVec 64
  w1f0 : BitVec 64
  w1f8 : BitVec 64
  w200 : BitVec 64
  w208 : BitVec 64
  w210 : BitVec 64
  w218 : BitVec 64
  w220 : BitVec 64
  w228 : BitVec 64
  w230 : BitVec 64
  w238 : BitVec 64
  mid : List (BitVec 8)
  w3b8 : BitVec 64
  w3c0 : BitVec 64
  w3c8 : BitVec 64

/-- Part 1 stack words read in `0x59e88..0x59fa4` (`+18996 -> +19280`, 36 words). -/
def epilogueStoreStackPart1At (fsp : BitVec 64) (k : EpilogueStoreStack) : SepProp :=
  ((fsp + 224#64) ↦₆₄ k.we0) ∗
  ((fsp + 248#64) ↦₆₄ k.wf8) ∗ ((fsp + 256#64) ↦₆₄ k.w100) ∗
  ((fsp + 264#64) ↦₆₄ k.w108) ∗ ((fsp + 272#64) ↦₆₄ k.w110) ∗
  ((fsp + 280#64) ↦₆₄ k.w118) ∗ ((fsp + 288#64) ↦₆₄ k.w120) ∗
  ((fsp + 296#64) ↦₆₄ k.w128) ∗ ((fsp + 304#64) ↦₆₄ k.w130) ∗
  ((fsp + 312#64) ↦₆₄ k.w138) ∗ ((fsp + 320#64) ↦₆₄ k.w140) ∗
  ((fsp + 328#64) ↦₆₄ k.w148) ∗ ((fsp + 336#64) ↦₆₄ k.w150) ∗
  ((fsp + 344#64) ↦₆₄ k.w158) ∗ ((fsp + 352#64) ↦₆₄ k.w160) ∗
  ((fsp + 360#64) ↦₆₄ k.w168) ∗ ((fsp + 368#64) ↦₆₄ k.w170) ∗
  ((fsp + 376#64) ↦₆₄ k.w178) ∗ ((fsp + 384#64) ↦₆₄ k.w180) ∗
  ((fsp + 392#64) ↦₆₄ k.w188) ∗ ((fsp + 400#64) ↦₆₄ k.w190) ∗
  ((fsp + 408#64) ↦₆₄ k.w198) ∗ ((fsp + 416#64) ↦₆₄ k.w1a0) ∗
  ((fsp + 424#64) ↦₆₄ k.w1a8) ∗ ((fsp + 432#64) ↦₆₄ k.w1b0) ∗
  ((fsp + 440#64) ↦₆₄ k.w1b8) ∗ ((fsp + 448#64) ↦₆₄ k.w1c0) ∗
  ((fsp + 456#64) ↦₆₄ k.w1c8) ∗ ((fsp + 464#64) ↦₆₄ k.w1d0) ∗
  ((fsp + 472#64) ↦₆₄ k.w1d8) ∗ ((fsp + 480#64) ↦₆₄ k.w1e0) ∗
  ((fsp + 488#64) ↦₆₄ k.w1e8) ∗ ((fsp + 496#64) ↦₆₄ k.w1f0) ∗
  ((fsp + 504#64) ↦₆₄ k.w1f8) ∗
  ((fsp + 960#64) ↦₆₄ k.w3c0) ∗ ((fsp + 968#64) ↦₆₄ k.w3c8)

/-- Part 2 stack words and `mid` slice read in `0x59fa4..0x59fd0` (`+19280 -> +19324`). -/
def epilogueStoreStackPart2At (fsp : BitVec 64) (k : EpilogueStoreStack) : SepProp :=
  ((fsp + 232#64) ↦₆₄ k.we8) ∗
  ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
  ((fsp + 528#64) ↦₆₄ k.w210) ∗ ((fsp + 536#64) ↦₆₄ k.w218) ∗
  ((fsp + 544#64) ↦₆₄ k.w220) ∗ ((fsp + 552#64) ↦₆₄ k.w228) ∗
  ((fsp + 560#64) ↦₆₄ k.w230) ∗
  ((fsp + 576#64) ↦ₛ k.mid)

/-- The `Split928` value written to `outA + 0..928` by `0x59e88..0x59fd0` (`+18996 -> +19324`)
    when entered in state `s` with stack contents `k : EpilogueStoreStack`. -/
def epilogueSplit928 (s : State) (k : EpilogueStoreStack) : Split928 where
  c0 := {
    w0 := k.we0
    w1 := s.readReg64 .x1
    w2 := s.readReg64 .x8
    w3 := k.w1f0
    w4 := k.w1c8
    w5 := k.w178
    w6 := k.w170
    w7 := k.w1f8
    w8 := k.w120
    w9 := k.w1b0
    w10 := k.w198
    w11 := k.w160
    w12 := k.w180
    w13 := k.w150
    w14 := k.w128
    w15 := k.w1a8
  }
  c1 := {
    w0 := s.readReg64 .x23
    w1 := s.readReg64 .x27
    w2 := k.w1b8
    w3 := k.w108
    w4 := k.w158
    w5 := k.w188
    w6 := k.w110
    w7 := k.w168
    w8 := k.w190
    w9 := k.w1d0
    w10 := k.w130
    w11 := k.w148
    w12 := k.w118
    w13 := k.w140
    w14 := s.readReg64 .x3
    w15 := k.w138
  }
  c2 := {
    w0 := s.readReg64 .x24
    w1 := s.readReg64 .x25
    w2 := s.readReg64 .x12
    w3 := s.readReg64 .x11
    w4 := s.readReg64 .x10
    w5 := s.readReg64 .x15
    w6 := s.readReg64 .x28
    w7 := s.readReg64 .x7
    w8 := s.readReg64 .x0
    w9 := s.readReg64 .x6
    w10 := s.readReg64 .x30
    w11 := s.readReg64 .x21
    w12 := s.readReg64 .x9
    w13 := k.w1a0
    w14 := s.readReg64 .x17
    w15 := k.w1d8
  }
  c3 := {
    w0 := s.readReg64 .x26
    w1 := s.readReg64 .x5
    w2 := s.readReg64 .x4
    w3 := k.w1c0
    w4 := s.readReg64 .x22
    w5 := s.readReg64 .x13
    w6 := s.readReg64 .x14
    w7 := k.w1e0
    w8 := s.readReg64 .x16
    w9 := k.w1e8
    w10 := s.readReg64 .x2
    w11 := k.wf8
    w12 := s.readReg64 .x20
    w13 := k.w3c0
    w14 := k.w3c8
    w15 := k.w100
  }
  mid := k.mid
  tail := {
    w0 := k.w210
    w1 := k.w218
    w2 := k.w220
    w3 := k.w228
    w4 := k.w230
  }

/-- Inverse of `epilogueSplit928`: builds the `EpilogueStoreStack` corresponding to `d : Split928`
    and `Option<EpochSecret>` stack words `we8, w200, w208`. -/
def epilogueStackOfSplit928 (d : Split928) (we8 w200 w208 : BitVec 64) : EpilogueStoreStack where
  we0 := d.c0.w0
  we8 := we8
  wf0 := 0#64
  wf8 := d.c3.w11
  w100 := d.c3.w15
  w108 := d.c1.w3
  w110 := d.c1.w6
  w118 := d.c1.w12
  w120 := d.c0.w8
  w128 := d.c0.w14
  w130 := d.c1.w10
  w138 := d.c1.w15
  w140 := d.c1.w13
  w148 := d.c1.w11
  w150 := d.c0.w13
  w158 := d.c1.w4
  w160 := d.c0.w11
  w168 := d.c1.w7
  w170 := d.c0.w6
  w178 := d.c0.w5
  w180 := d.c0.w12
  w188 := d.c1.w5
  w190 := d.c1.w8
  w198 := d.c0.w10
  w1a0 := d.c2.w13
  w1a8 := d.c0.w15
  w1b0 := d.c0.w9
  w1b8 := d.c1.w2
  w1c0 := d.c3.w3
  w1c8 := d.c0.w4
  w1d0 := d.c1.w9
  w1d8 := d.c2.w15
  w1e0 := d.c3.w7
  w1e8 := d.c3.w9
  w1f0 := d.c0.w3
  w1f8 := d.c0.w7
  w200 := w200
  w208 := w208
  w210 := d.tail.w0
  w218 := d.tail.w1
  w220 := d.tail.w2
  w228 := d.tail.w3
  w230 := d.tail.w4
  w238 := 0#64
  mid := d.mid
  w3b8 := 0#64
  w3c0 := d.c3.w13
  w3c8 := d.c3.w14

/-- Register equality condition at `+18996` (`0x59e88`) ensuring `epilogueSplit928 s k = d`. -/
def epilogueRegsEqSplit928 (s : State) (d : Split928) : Prop :=
  s.readReg64 .x1 = d.c0.w1 ∧
  s.readReg64 .x8 = d.c0.w2 ∧
  s.readReg64 .x23 = d.c1.w0 ∧
  s.readReg64 .x27 = d.c1.w1 ∧
  s.readReg64 .x3 = d.c1.w14 ∧
  s.readReg64 .x24 = d.c2.w0 ∧
  s.readReg64 .x25 = d.c2.w1 ∧
  s.readReg64 .x12 = d.c2.w2 ∧
  s.readReg64 .x11 = d.c2.w3 ∧
  s.readReg64 .x10 = d.c2.w4 ∧
  s.readReg64 .x15 = d.c2.w5 ∧
  s.readReg64 .x28 = d.c2.w6 ∧
  s.readReg64 .x7 = d.c2.w7 ∧
  s.readReg64 .x0 = d.c2.w8 ∧
  s.readReg64 .x6 = d.c2.w9 ∧
  s.readReg64 .x30 = d.c2.w10 ∧
  s.readReg64 .x21 = d.c2.w11 ∧
  s.readReg64 .x9 = d.c2.w12 ∧
  s.readReg64 .x17 = d.c2.w14 ∧
  s.readReg64 .x26 = d.c3.w0 ∧
  s.readReg64 .x5 = d.c3.w1 ∧
  s.readReg64 .x4 = d.c3.w2 ∧
  s.readReg64 .x22 = d.c3.w4 ∧
  s.readReg64 .x13 = d.c3.w5 ∧
  s.readReg64 .x14 = d.c3.w6 ∧
  s.readReg64 .x16 = d.c3.w8 ∧
  s.readReg64 .x2 = d.c3.w10 ∧
  s.readReg64 .x20 = d.c3.w12

theorem epilogueSplit928_of_eq (s : State) (d : Split928) (we8 w200 w208 : BitVec 64)
    (hregs : epilogueRegsEqSplit928 s d) :
    epilogueSplit928 s (epilogueStackOfSplit928 d we8 w200 w208) = d := by
  rcases d with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, mid, ⟨⟩⟩
  rcases hregs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  dsimp only [epilogueSplit928, epilogueStackOfSplit928] at *
  subst_vars
  rfl

theorem memRegion_928_entails_split928 (outA : BitVec 64) :
    memRegion outA chunkedStatesSize ⊢
    ∃∗ d_out : Split928, ⌜d_out.mid.length = 376⌝ ∗ split928At outA d_out := by
  rw [memRegion_eq_exists_bytes outA chunkedStatesSize (by decide)]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hbs_len
  obtain ⟨d_out, hmid, rfl⟩ := exists_split928_of_length_928 hbs_len
  refine Entails.sepExists_right d_out ?_
  refine Entails.pure_right hmid ?_
  rw [split928At_eq_pointsToBytes outA d_out hmid]
  exact Entails.refl _

theorem memRegion_32_entails_words4 (a : BitVec 64) :
    memRegion a 32 ⊢
    (∃∗ v0 : BitVec 64, (a ↦₆₄ v0)) ∗
    (∃∗ v1 : BitVec 64, ((a + 8#64) ↦₆₄ v1)) ∗
    (∃∗ v2 : BitVec 64, ((a + 16#64) ↦₆₄ v2)) ∗
    (∃∗ v3 : BitVec 64, ((a + 24#64) ↦₆₄ v3)) := by
  rw [ProofLib.memRegion_split a 8 24 (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64)]
  exact Entails.of_eq (by ac_rfl)

theorem memcpy_region_ok_at_statesRecv {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        (bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy")))
      sessionMemcpyRegionSpec := by
  refine Drop.sub_ok_of_addr_eq ?_ hmemcpy
  exact (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "memcpy"))) (b := b) (X := Rust.withPanics ext)
    (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv") (ls_stub% "memcpy") (by decide)).symm

set_option maxHeartbeats 800000 in
/-- Part 1 of shared `Ok` return store block (`+18996 -> +19280`, `0x59e88 -> 0x59fa4`):
    writes `c0, c1, c2, c3` (`64` words = `512`B) to `outA + 0..512` and sets up
    `x0 = outA + 512#64`, `x1 = fsp + 576#64`, `x2 = 376#64` for `memcpy`. -/
theorem ct1Sampled_epilogue_store_part1
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack)
    (c0_out c1_out c2_out c3_out : Words16)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19280#64) s_in
      (epilogueStoreStackPart1At fsp k ∗
        wordsAt outA c0_out.toList ∗
        wordsAt (outA + 128#64) c1_out.toList ∗
        wordsAt (outA + 256#64) c2_out.toList ∗
        wordsAt (outA + 384#64) c3_out.toList ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueStoreStackPart1At fsp k ∗
          wordsAt outA (epilogueSplit928 s_in k).c0.toList ∗
          wordsAt (outA + 128#64) (epilogueSplit928 s_in k).c1.toList ∗
          wordsAt (outA + 256#64) (epilogueSplit928 s_in k).c2.toList ∗
          wordsAt (outA + 384#64) (epilogueSplit928 s_in k).c3.toList ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x0 = outA + 512#64 ∧
        sf.readReg64 .x1 = fsp + 576#64 ∧
        sf.readReg64 .x2 = 376#64 ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx19
  states_recv_fetches_range b (Rust.withPanics ext) 18996 284
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [epilogueStoreStackPart1At, epilogueSplit928, Words16.toList]
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_done

/-- Part 2 of shared `Ok` return store block (`+19280 -> +19324`, `0x59fa4 -> 0x59fd0`):
    calls `memcpy(outA + 512, fsp + 576, 376)` and writes `tail` (`5` words = `40`B at `outA + 888..928`)
    and the 4 `Option<EpochSecret>` words at `outA + 928..960`. -/
theorem ct1Sampled_epilogue_store_part2
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_mid : State) (fsp outA v20 : BitVec 64)
    (k : EpilogueStoreStack)
    (tail_out : Words5) (v928 v936 v944 v952 : BitVec 64)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_mid.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19280#64)
    (hrun : s_mid.status = .Running)
    (hsp : s_mid.sp = fsp)
    (hx0 : s_mid.readReg64 .x0 = outA + 512#64)
    (hx1 : s_mid.readReg64 .x1 = fsp + 576#64)
    (hx2 : s_mid.readReg64 .x2 = 376#64)
    (hx19 : s_mid.readReg64 .x19 = outA)
    (hx20 : s_mid.readReg64 .x20 = v20) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64) s_mid
      (epilogueStoreStackPart2At fsp k ∗
        memRegion (outA + 512#64) 376 ∗
        wordsAt (outA + 888#64) tail_out.toList ∗
        ((outA + 928#64) ↦₆₄ v928) ∗
        ((outA + 936#64) ↦₆₄ v936) ∗
        ((outA + 944#64) ↦₆₄ v944) ∗
        ((outA + 952#64) ↦₆₄ v952) ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueStoreStackPart2At fsp k ∗
          ((outA + 512#64) ↦ₛ k.mid) ∗
          wordsAt (outA + 888#64) [k.w210, k.w218, k.w220, k.w228, k.w230] ∗
          ((outA + 928#64) ↦₆₄ k.we8) ∗
          ((outA + 936#64) ↦₆₄ v20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗
          ((outA + 952#64) ↦₆₄ k.w208) ∗
          Rest) ∧
        sf.sp = fsp ∧
        TraceCalleeSaved sf s_mid) := by
  subst hsp hx19 hx20
  have hmemcpy_raw := memcpy_region_ok_at_statesRecv hmemcpy
  states_recv_fetches_range b (Rust.withPanics ext) 19280 44
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [epilogueStoreStackPart2At, Words5.toList]
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call hmemcpy_raw ⟨s_mid.readReg64 .x19 + 512#64, s_mid.sp + 576#64, k.mid⟩
  wp_steps
  wp_done

theorem pointsToBytes_entails_memRegion_376 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 376) :
    (a ↦ₛ bs) ⊢ memRegion a 376 := by
  rw [memRegion_eq_exists_bytes a 376 (by decide)]
  refine Entails.sepExists_right bs ?_
  exact Entails.pure_right h (Entails.refl _)

/-- Full shared `Ok` return store block (`+18996 -> +19324`, `0x59e88 -> 0x59fd0`):
    combines `ct1Sampled_epilogue_store_part1` and `ct1Sampled_epilogue_store_part2` to write
    `split928At outA (epilogueSplit928 s_in k)` (`928`B) and the 4 `Option<EpochSecret>` words
    at `outA + 928..960` (`32`B). -/
theorem ct1Sampled_epilogue_store
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64) s_in
      (epilogueStoreStackPart1At fsp k ∗
        epilogueStoreStackPart2At fsp k ∗
        memRegion outA chunkedStatesSize ∗
        memRegion (outA + 928#64) 32 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueStoreStackPart1At fsp k ∗
          epilogueStoreStackPart2At fsp k ∗
          split928At outA (epilogueSplit928 s_in k) ∗
          ((outA + 928#64) ↦₆₄ k.we8) ∗
          ((outA + 936#64) ↦₆₄ (s_in.readReg64 .x20)) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗
          ((outA + 952#64) ↦₆₄ k.w208) ∗
          Rest) ∧
        sf.sp = fsp ∧
        TraceCalleeSaved sf s_in) := by
  have hpre :
      epilogueStoreStackPart1At fsp k ∗
      epilogueStoreStackPart2At fsp k ∗
      memRegion outA chunkedStatesSize ∗
      memRegion (outA + 928#64) 32 ∗
      Rest ⊢
      ∃∗ d_out : Split928, ∃∗ v928 : BitVec 64, ∃∗ v936 : BitVec 64,
      ∃∗ v944 : BitVec 64, ∃∗ v952 : BitVec 64,
        epilogueStoreStackPart1At fsp k ∗
        wordsAt outA d_out.c0.toList ∗
        wordsAt (outA + 128#64) d_out.c1.toList ∗
        wordsAt (outA + 256#64) d_out.c2.toList ∗
        wordsAt (outA + 384#64) d_out.c3.toList ∗
        (epilogueStoreStackPart2At fsp k ∗
          memRegion (outA + 512#64) 376 ∗
          wordsAt (outA + 888#64) d_out.tail.toList ∗
          ((outA + 928#64) ↦₆₄ v928) ∗
          ((outA + 936#64) ↦₆₄ v936) ∗
          ((outA + 944#64) ↦₆₄ v944) ∗
          ((outA + 952#64) ↦₆₄ v952) ∗
          Rest) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_928_entails_split928 outA)
        (sepConj_mono_left (memRegion_32_entails_words4 (outA + 928#64)))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro v952
    apply Entails.sepExists_elim; intro v944
    apply Entails.sepExists_elim; intro v936
    apply Entails.sepExists_elim; intro v928
    apply Entails.sepExists_elim; intro d_out
    refine Entails.sepExists_right d_out (Entails.sepExists_right v928
      (Entails.sepExists_right v936 (Entails.sepExists_right v944
        (Entails.sepExists_right v952 ?_))))
    rw [show epilogueStoreStackPart1At fsp k ∗
        (epilogueStoreStackPart2At fsp k ∗
          ((⌜d_out.mid.length = 376⌝ ∗ split928At outA d_out) ∗
            ((((outA + 928#64) ↦₆₄ v928) ∗ ((outA + 936#64) ↦₆₄ v936) ∗
              ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952)) ∗
            Rest))) =
        ⌜d_out.mid.length = 376⌝ ∗
        ((outA + 512#64) ↦ₛ d_out.mid) ∗
        (epilogueStoreStackPart1At fsp k ∗
          wordsAt outA d_out.c0.toList ∗
          wordsAt (outA + 128#64) d_out.c1.toList ∗
          wordsAt (outA + 256#64) d_out.c2.toList ∗
          wordsAt (outA + 384#64) d_out.c3.toList ∗
          (epilogueStoreStackPart2At fsp k ∗
            wordsAt (outA + 888#64) d_out.tail.toList ∗
            ((outA + 928#64) ↦₆₄ v928) ∗
            ((outA + 936#64) ↦₆₄ v936) ∗
            ((outA + 944#64) ↦₆₄ v944) ∗
            ((outA + 952#64) ↦₆₄ v952) ∗
            Rest)) by
      dsimp only [split928At]; ac_rfl]
    apply Entails.pure_left; intro hd_mid
    refine Entails.trans (sepConj_mono_left
      (pointsToBytes_entails_memRegion_376 (outA + 512#64) d_out.mid hd_mid)) ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro d_out
  apply ProofLib.SepWP.exists_left; intro v928
  apply ProofLib.SepWP.exists_left; intro v936
  apply ProofLib.SepWP.exists_left; intro v944
  apply ProofLib.SepWP.exists_left; intro v952
  refine SepWP.seq (ct1Sampled_epilogue_store_part1 s_in fsp outA k
    d_out.c0 d_out.c1 d_out.c2 d_out.c3 _ hfsp_align hpc hrun hsp hx19) ?_
  intro s_mid P_mid hpc_mid hrun_mid ⟨hP_mid, hsp_mid, hx0_mid, hx1_mid, hx2_mid, hx19_mid, hx20_mid, htr_mid⟩
  have hP_mid' : P_mid ⊢
      epilogueStoreStackPart2At fsp k ∗
      memRegion (outA + 512#64) 376 ∗
      wordsAt (outA + 888#64) d_out.tail.toList ∗
      ((outA + 928#64) ↦₆₄ v928) ∗
      ((outA + 936#64) ↦₆₄ v936) ∗
      ((outA + 944#64) ↦₆₄ v944) ∗
      ((outA + 952#64) ↦₆₄ v952) ∗
      (epilogueStoreStackPart1At fsp k ∗
        wordsAt outA (epilogueSplit928 s_in k).c0.toList ∗
        wordsAt (outA + 128#64) (epilogueSplit928 s_in k).c1.toList ∗
        wordsAt (outA + 256#64) (epilogueSplit928 s_in k).c2.toList ∗
        wordsAt (outA + 384#64) (epilogueSplit928 s_in k).c3.toList ∗
        Rest) :=
    Entails.trans hP_mid (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP_mid' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_store_part2 hmemcpy s_mid fsp outA (s_in.readReg64 .x20) k
      d_out.tail v928 v936 v944 v952 _ hmid hfsp_align hpc_mid hrun_mid
      hsp_mid hx0_mid hx1_mid hx2_mid hx19_mid hx20_mid) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, htr_f⟩
  refine ⟨?_, hsp_f, htr_f.trans htr_mid⟩
  refine Entails.trans hPf ?_
  dsimp only [split928At, epilogueSplit928, Words5.toList]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Scratch Stack Frame (`fsp + 0..976`) for State-Copy Paths -/

/-- The 29 scratch 64-bit words in `fsp + 0..248` (all words in `0..256` except `we0`, `we8`, `wf8`). -/
structure CopyScratchStack where
  c0 : Words16
  w80 : BitVec 64
  w88 : BitVec 64
  w90 : BitVec 64
  w98 : BitVec 64
  wa0 : BitVec 64
  wa8 : BitVec 64
  wb0 : BitVec 64
  wb8 : BitVec 64
  wc0 : BitVec 64
  wc8 : BitVec 64
  wd0 : BitVec 64
  wd8 : BitVec 64
  wf0 : BitVec 64

def CopyScratchStack.c1 (sc : CopyScratchStack) (we0 we8 wf8 : BitVec 64) : Words16 :=
  ⟨sc.w80, sc.w88, sc.w90, sc.w98, sc.wa0, sc.wa8, sc.wb0, sc.wb8,
   sc.wc0, sc.wc8, sc.wd0, sc.wd8, we0, we8, sc.wf0, wf8⟩

def EpilogueStoreStack.c2 (k : EpilogueStoreStack) : Words16 :=
  ⟨k.w100, k.w108, k.w110, k.w118, k.w120, k.w128, k.w130, k.w138,
   k.w140, k.w148, k.w150, k.w158, k.w160, k.w168, k.w170, k.w178⟩

def EpilogueStoreStack.c3 (k : EpilogueStoreStack) : Words16 :=
  ⟨k.w180, k.w188, k.w190, k.w198, k.w1a0, k.w1a8, k.w1b0, k.w1b8,
   k.w1c0, k.w1c8, k.w1d0, k.w1d8, k.w1e0, k.w1e8, k.w1f0, k.w1f8⟩

def EpilogueStoreStack.tail (k : EpilogueStoreStack) : Words5 :=
  ⟨k.w210, k.w218, k.w220, k.w228, k.w230⟩

def copyScratchStackAt (fsp : BitVec 64) (sc : CopyScratchStack) : SepProp :=
  wordsAt fsp sc.c0.toList ∗
  ((fsp + 128#64) ↦₆₄ sc.w80) ∗ ((fsp + 136#64) ↦₆₄ sc.w88) ∗
  ((fsp + 144#64) ↦₆₄ sc.w90) ∗ ((fsp + 152#64) ↦₆₄ sc.w98) ∗
  ((fsp + 160#64) ↦₆₄ sc.wa0) ∗ ((fsp + 168#64) ↦₆₄ sc.wa8) ∗
  ((fsp + 176#64) ↦₆₄ sc.wb0) ∗ ((fsp + 184#64) ↦₆₄ sc.wb8) ∗
  ((fsp + 192#64) ↦₆₄ sc.wc0) ∗ ((fsp + 200#64) ↦₆₄ sc.wc8) ∗
  ((fsp + 208#64) ↦₆₄ sc.wd0) ∗ ((fsp + 216#64) ↦₆₄ sc.wd8) ∗
  ((fsp + 240#64) ↦₆₄ sc.wf0)

theorem memRegion_128_entails_words16 (a : BitVec 64) :
    memRegion a 128 ⊢ ∃∗ c : Words16, wordsAt a c.toList := by
  rw [memRegion_eq_exists_bytes a 128 (by decide)]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨c, rfl⟩ := exists_words16_of_length_128 hlen
  refine Entails.sepExists_right c ?_
  rw [wordsAt_eq_pointsToBytes]
  exact Entails.refl _

theorem memRegion_40_entails_words5 (a : BitVec 64) :
    memRegion a 40 ⊢ ∃∗ c : Words5, wordsAt a c.toList := by
  rw [memRegion_eq_exists_bytes a 40 (by decide)]
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨c, rfl⟩ := exists_words5_of_length_40 hlen
  refine Entails.sepExists_right c ?_
  rw [wordsAt_eq_pointsToBytes]
  exact Entails.refl _

theorem memRegion_16_entails_words2 (a : BitVec 64) :
    memRegion a 16 ⊢
    (∃∗ v0 : BitVec 64, (a ↦₆₄ v0)) ∗ (∃∗ v1 : BitVec 64, ((a + 8#64) ↦₆₄ v1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 8#64)]
  exact Entails.refl _

theorem copyScratch_and_epilogueStack_eq_chunks (fsp : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    copyScratchStackAt fsp sc ∗
      epilogueStoreStackPart1At fsp k ∗
      epilogueStoreStackPart2At fsp k =
    wordsAt fsp sc.c0.toList ∗
      wordsAt (fsp + 128#64) (sc.c1 k.we0 k.we8 k.wf8).toList ∗
      wordsAt (fsp + 256#64) k.c2.toList ∗
      wordsAt (fsp + 384#64) k.c3.toList ∗
      ((fsp + 512#64) ↦₆₄ k.w200) ∗
      ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗
      ((fsp + 576#64) ↦ₛ k.mid) ∗
      ((fsp + 960#64) ↦₆₄ k.w3c0) ∗
      ((fsp + 968#64) ↦₆₄ k.w3c8) := by
  dsimp only [copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    CopyScratchStack.c1, EpilogueStoreStack.c2, EpilogueStoreStack.c3, EpilogueStoreStack.tail,
    Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem copyScratch_and_epilogueStack_entails_memRegion_4144 (fsp : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) (hmid : k.mid.length = 376) :
    copyScratchStackAt fsp sc ∗
      epilogueStoreStackPart1At fsp k ∗
      epilogueStoreStackPart2At fsp k ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 3168 ⊢
    memRegion fsp 4144 := by
  have heq :
      copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        epilogueStoreStackPart2At fsp k ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 =
      (copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        epilogueStoreStackPart2At fsp k) ∗
      (memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168) := by ac_rfl
  rw [heq, copyScratch_and_epilogueStack_eq_chunks fsp sc k]
  have hc0 := wordsAt_entails_memRegion sc.c0.toList fsp 128 rfl
  have hc1 := wordsAt_entails_memRegion (sc.c1 k.we0 k.we8 k.wf8).toList (fsp + 128#64) 128 rfl
  have hc2 := wordsAt_entails_memRegion k.c2.toList (fsp + 256#64) 128 rfl
  have hc3 := wordsAt_entails_memRegion k.c3.toList (fsp + 384#64) 128 rfl
  have hw200 := ProofLib.pointsTo64_entails_memRegion (fsp + 512#64) k.w200
  have hw208 := ProofLib.pointsTo64_entails_memRegion (fsp + 520#64) k.w208
  have htail := wordsAt_entails_memRegion k.tail.toList (fsp + 528#64) 40 rfl
  have hmid_r := pointsToBytes_entails_memRegion_376 (fsp + 576#64) k.mid hmid
  have hw3c0 := ProofLib.pointsTo64_entails_memRegion (fsp + 960#64) k.w3c0
  have hw3c8 := ProofLib.pointsTo64_entails_memRegion (fsp + 968#64) k.w3c8
  refine Entails.trans (sepConj_mono_left
    (sepConj_mono hc0 (sepConj_mono hc1 (sepConj_mono hc2 (sepConj_mono hc3
      (sepConj_mono hw200 (sepConj_mono hw208 (sepConj_mono htail
        (sepConj_mono hmid_r (sepConj_mono hw3c0 hw3c8)))))))))) ?_
  rw [ProofLib.memRegion_split fsp 128 4016 (by decide),
      ProofLib.memRegion_split' (b := fsp + 128#64) (n := 128) (k := 3888) (b' := fsp + 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 256#64) (n := 128) (k := 3760) (b' := fsp + 384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 384#64) (n := 128) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 512#64) (n := 8) (k := 3624) (b' := fsp + 520#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 520#64) (n := 8) (k := 3616) (b' := fsp + 528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 528#64) (n := 40) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 8) (k := 3176) (b' := fsp + 968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 968#64) (n := 8) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

def copyLtScratch (sc : CopyScratchStack) (d : Split928) : CopyScratchStack where
  c0 := { sc.c0 with
    w2 := d.c2.w4
    w3 := d.c2.w0
    w4 := d.c1.w14
    w7 := d.c2.w9
    w8 := d.c2.w7
    w9 := d.c2.w3
    w10 := d.c2.w2
    w12 := d.c3.w8
    w13 := d.c2.w8
    w14 := d.c2.w5
  }
  w80 := d.c2.w6
  w88 := sc.w88
  w90 := sc.w90
  w98 := d.c1.w0
  wa0 := d.c1.w1
  wa8 := d.c3.w0
  wb0 := d.c3.w4
  wb8 := d.c3.w2
  wc0 := d.c2.w12
  wc8 := d.c2.w14
  wd0 := sc.wd0
  wd8 := d.c3.w1
  wf0 := d.c2.w11

def copyOtherScratch (sc : CopyScratchStack) (d : Split928) : CopyScratchStack where
  c0 := { sc.c0 with
    w1 := d.c3.w5
    w2 := d.c2.w4
    w3 := d.c2.w0
    w4 := d.c1.w14
    w6 := d.c2.w10
    w7 := d.c2.w9
    w8 := d.c2.w7
    w9 := d.c2.w3
    w10 := d.c2.w2
    w11 := d.c3.w10
    w13 := d.c2.w8
    w14 := d.c2.w5
  }
  w80 := d.c2.w6
  w88 := sc.w88
  w90 := sc.w90
  w98 := d.c1.w0
  wa0 := sc.wa0
  wa8 := d.c3.w0
  wb0 := d.c3.w4
  wb8 := d.c3.w2
  wc0 := d.c2.w12
  wc8 := d.c2.w14
  wd0 := sc.wd0
  wd8 := d.c3.w1
  wf0 := d.c2.w11

set_option maxHeartbeats 1200000 in
/-- Path 2 (`msg.epoch < st.uc.epoch`) state-copy block (`+10500 -> +18996`,
    `0x57d58..0x57f00 -> 0x5857c..0x58594`). -/
theorem ct1Sampled_copy_lt
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10500#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          split928At stA d ∗
          copyScratchStackAt fsp (copyLtScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx19
  have hmemcpy_raw := memcpy_region_ok_at_statesRecv hmemcpy
  states_recv_fetches_range b (Rust.withPanics ext) 10500 428
  states_recv_fetches_range b (Rust.withPanics ext) 12584 28
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyLtScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call hmemcpy_raw ⟨s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid⟩
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
/-- Path 3 (`msg.epoch == st.uc.epoch`, non-`ek`/`ekCt1Ack`) state-copy block (`+12144 -> +18996`,
    `0x583c4..0x58594`). -/
theorem ct1Sampled_copy_other
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 12144#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s_in
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          split928At stA d ∗
          copyScratchStackAt fsp (copyOtherScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx19
  have hmemcpy_raw := memcpy_region_ok_at_statesRecv hmemcpy
  states_recv_fetches_range b (Rust.withPanics ext) 12144 468
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyOtherScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_call hmemcpy_raw ⟨s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid⟩
  wp_steps
  wp_done

theorem optEpochSecretAt_none_of_words4 (A : RustAlloc) (a w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
    optEpochSecretAt A a none := by
  rw [optEpochSecretAt_none]
  refine sepConj_mono_right ?_
  rw [ProofLib.memRegion_split (a + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split' (b := (a + 8#64) + 8#64) (n := 8) (k := 8)
        (b' := a + 24#64) rfl (by bv_omega) (by decide)]
  have h16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [h16]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 16#64) w2)
      (ProofLib.pointsTo64_entails_memRegion (a + 24#64) w3))

def epilogueStackOfChunks (c1 c2 c3 : Words16) (w200 w208 : BitVec 64) (tail : Words5)
    (w3c0 w3c8 : BitVec 64) : EpilogueStoreStack where
  we0 := c1.w12
  we8 := c1.w13
  wf0 := c1.w14
  wf8 := c1.w15
  w100 := c2.w0
  w108 := c2.w1
  w110 := c2.w2
  w118 := c2.w3
  w120 := c2.w4
  w128 := c2.w5
  w130 := c2.w6
  w138 := c2.w7
  w140 := c2.w8
  w148 := c2.w9
  w150 := c2.w10
  w158 := c2.w11
  w160 := c2.w12
  w168 := c2.w13
  w170 := c2.w14
  w178 := c2.w15
  w180 := c3.w0
  w188 := c3.w1
  w190 := c3.w2
  w198 := c3.w3
  w1a0 := c3.w4
  w1a8 := c3.w5
  w1b0 := c3.w6
  w1b8 := c3.w7
  w1c0 := c3.w8
  w1c8 := c3.w9
  w1d0 := c3.w10
  w1d8 := c3.w11
  w1e0 := c3.w12
  w1e8 := c3.w13
  w1f0 := c3.w14
  w1f8 := c3.w15
  w200 := w200
  w208 := w208
  w210 := tail.w0
  w218 := tail.w1
  w220 := tail.w2
  w228 := tail.w3
  w230 := tail.w4
  w238 := 0#64
  mid := []
  w3b8 := 0#64
  w3c0 := w3c0
  w3c8 := w3c8

def copyScratchOfChunks (c0 c1 : Words16) : CopyScratchStack where
  c0 := c0
  w80 := c1.w0
  w88 := c1.w1
  w90 := c1.w2
  w98 := c1.w3
  wa0 := c1.w4
  wa8 := c1.w5
  wb0 := c1.w6
  wb8 := c1.w7
  wc0 := c1.w8
  wc8 := c1.w9
  wd0 := c1.w10
  wd8 := c1.w11
  wf0 := c1.w14

theorem memRegion_4144_entails_copyScratch_and_epilogueStack (fsp : BitVec 64) :
    memRegion fsp 4144 ⊢
    ∃∗ sc : CopyScratchStack, ∃∗ k : EpilogueStoreStack,
      copyScratchStackAt fsp sc ∗
      epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ k.we8) ∗
      ((fsp + 512#64) ↦₆₄ k.w200) ∗
      ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗
      memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 3168 := by
  rw [ProofLib.memRegion_split fsp 128 4016 (by decide),
      ProofLib.memRegion_split' (b := fsp + 128#64) (n := 128) (k := 3888) (b' := fsp + 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 256#64) (n := 128) (k := 3760) (b' := fsp + 384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 384#64) (n := 128) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 512#64) (n := 8) (k := 3624) (b' := fsp + 520#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 520#64) (n := 8) (k := 3616) (b' := fsp + 528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 528#64) (n := 40) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 8) (k := 3176) (b' := fsp + 968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 968#64) (n := 8) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 512#64),
      ProofLib.memRegion_eight (fsp + 520#64),
      ProofLib.memRegion_eight (fsp + 960#64),
      ProofLib.memRegion_eight (fsp + 968#64)]
  refine Entails.trans (sepConj_mono (memRegion_128_entails_words16 fsp)
    (sepConj_mono (memRegion_128_entails_words16 (fsp + 128#64))
      (sepConj_mono (memRegion_128_entails_words16 (fsp + 256#64))
        (sepConj_mono (memRegion_128_entails_words16 (fsp + 384#64))
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 528#64))))))))) ?_
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1
  apply Entails.sepExists_elim; intro c2
  apply Entails.sepExists_elim; intro c3
  apply Entails.sepExists_elim; intro w200
  apply Entails.sepExists_elim; intro w208
  apply Entails.sepExists_elim; intro tail
  apply Entails.sepExists_elim; intro w3c0
  apply Entails.sepExists_elim; intro w3c8
  refine Entails.sepExists_right (copyScratchOfChunks c0 c1)
    (Entails.sepExists_right (epilogueStackOfChunks c1 c2 c3 w200 w208 tail w3c0 w3c8) ?_)
  dsimp only [copyScratchStackAt, epilogueStoreStackPart1At, copyScratchOfChunks,
    epilogueStackOfChunks, EpilogueStoreStack.tail, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.States.Recv

