/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberc
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Missing-Kyber v4 Error and Full Kyber `Ok` Dispatch

Proves `kyber_neither_v4_err_placed_wpE` (`+0x6c8 → +0xa24` / `+0xa80`) and
`w5b_kyber_ok_placed_wpW` (`+0x684 → +0x830`) on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 Arm64.Obj ProofLib ProofLib.GenPlacedFetches ProofLib.ProgramReflection
open CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open RunProofs.Pksm

abbrev w5bc_SepWPp := @Wire.SepWPp
private abbrev w5bc_done := @Wire.SepWP.done
private abbrev w5bc_panic := @Wire.SepWPp.panic
private abbrev w5bc_frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev w5bc_bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom
private abbrev w5bc_pure_pre := @Wire.SepWPp.pure_pre
private abbrev w5bc_exists_pre := @Wire.SepWPp.exists_pre
private abbrev w5bc_mono_pre := @Wire.SepWPp.mono_pre
private abbrev w5bc_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev w5bc_of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev w5bc_call_noPanic_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_noPanic_pk

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## 1. ``kyber_neither_v4_err_placed_wpE``: (`+0x6c8 → +0xa24` / `+0xa80`) -/

/-- (``+0x6c8 → +0xa24` / `+0xa80`, dec `1736 → 2596``):
When `kpkTag = 0#32`, `kyberOpt = none` (`kyberCap = noneCap`), and `0x40 ≤ vb.toNat`,
branches `+0x6c8` (`1736`) → `+0x718` (`1816`) → `+0x818` (`2072`) → `+0x998` (`2456`),
allocates the 54-byte `.rodata` error string, panics via `+0xa80` (`handle_error`) on OOM,
otherwise writes `pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext)` and reaches `+0xa24` (`2596`). -/
theorem kyber_neither_v4_err_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : CodecHooksPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8}
    (hvb_ge : 0x40 ≤ vb.toNat)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (_hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    w5bc_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      (optVecU8Buf A kyberCap kyberPtr kyberLen none ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  dsimp only [optVecU8Buf]
  refine w5bc_pure_pre fun hcap => ?_
  subst hcap
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hshim := w5bw_shim_ok hH.shim
  have halloc := w5bw_alloc_ok hH.alloc
  have hpan := raw_vec_panic_at_prekey_placed hH.panic_raw
  clear hH
  have hvb_ule := ule_64_vb_eq_true hvb_ge
  have hstack := stackAt_sub_split sp' allocHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine w5bc_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := lsρ lsRustNoAllocShimSym) ?_
  wp_steps
  refine w5bc_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine w5bc_call_noPanic_pk keepsFrozenInv_codeRoLoaded () hshim
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 2460#64) (by simp [arm64_norm])
    (T := emp)
    (F := memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
    (φ := True)
    (by simp [noAllocShimSpec])
    trivial
    (by rw [emp_sepConj])
    ?_
  clear hshim
  intro s1 hpc1 hrun1 hsp1 hsp1_align hcl1' hcs1
  dsimp only [noAllocShimSpec]
  refine w5bc_pure_pre fun htr1 => ?_
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  have hsp1_eq : s1.sp = sp' := by tryFromPost_sp [hsp1, hsp_eq]
  refine w5bc_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl1'
    (mid := lsρ lsRustAllocSym) ?_
  wp_steps
  refine w5bc_done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) fun hcl2 => ?_
  have hlay54 : LayoutOk 54 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine w5bc_call_noPanic_pk keepsFrozenInv_codeRoLoaded (54, 1) halloc
    (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    (by tryFromPost_sp_align hsp1_align) hcl2
    (ret_pc := (blkPl_111).base + 2472#64) (by simp [arm64_norm])
    (T := A.pool ∗ stackAt sp' allocHookStack)
    (φ := (54#64 : BitVec 64).toNat = 54 ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk 54 1)
    (by simp [rustAllocSpec, hsp1_eq, arm64_norm])
    ⟨rfl, rfl, hlay54⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear halloc
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2' hcs2
  dsimp only [rustAllocSpec]
  rw [w5bw_rot_alloc]
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp1_eq]
  by_cases hoom : s2.readReg64 .x0 = 0
  · simp only [hoom, ite_true]
    refine w5bc_pure_pre fun htr2 => ?_
    refine w5bc_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl2'
      (mid := lsρ lsRawVecHandleErrorSym) ?_
    wp_steps
    refine w5bc_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun _ => ?_
    refine w5bc_panic (by simp [hrun2, arm64_norm])
      (by simpa [arm64_norm] using hpan)
      (tryFromQp_of_panicked (by simp [Rust.panicked, htr2, htr1, htr, arm64_norm]))
  · clear hpan
    simp only [hoom, ite_false, sepConj_assoc]
    refine w5bc_pure_pre fun ⟨_, htr2⟩ => ?_
    have hbeq : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    rw [memRegion54_unpack (s2.readReg64 .x0), memRegion248_split_err sret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine w5bc_exists_pre fun s0_6 => w5bc_exists_pre fun s0_5 =>
      w5bc_exists_pre fun s0_4 => w5bc_exists_pre fun s0_3 =>
      w5bc_exists_pre fun s0_2 => w5bc_exists_pre fun s0_1 =>
      w5bc_exists_pre fun s0_0 =>
      w5bc_exists_pre fun w5 => w5bc_exists_pre fun w4 =>
      w5bc_exists_pre fun w3 => w5bc_exists_pre fun w2 =>
      w5bc_exists_pre fun w1 => w5bc_exists_pre fun w0 => ?_
    let roBase := lsmpl.ρ "libsignal_protocol:.rodata..Lanon.565"
    refine w5bc_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl2' (mid := (blkPl_111).base + 2504#64) ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at0 hcl2' "libsignal_protocol:.rodata..Lanon.565" 54) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 8) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 16) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 24) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 32) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 40) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 46) rfl ?_
    wp_steps
    refine w5bc_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
    have hshift := shift_window_40_to_46 (s2.readReg64 .x0) (s2.mem.read64 (roBase + 40#64))
    refine w5bc_mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right
              (Entails.trans (by apply entails_of_eq; rw [← sepConj_assoc])
                (Entails.trans (sepConj_mono_left hshift)
                  (by apply entails_of_eq; rw [sepConj_assoc])))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine w5bc_exists_pre fun w46 => ?_
    refine w5bc_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl3 ?_
    wp_steps
    refine w5bc_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl4 => ?_
    refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2_align, hcl4,
          by simp [htr2, htr1, htr, arm64_norm]⟩,
        by simp [hx29_2, hx29_1, hx29, arm64_norm],
        by simp [hx26_2, hx26_1, hx26, arm64_norm],
        by simp [hx23_2, hx23_1, hx23, arm64_norm],
        by simp [hx22_2, hx22_1, hx22, arm64_norm],
        by simp [hx21_2, hx21_1, hx21, arm64_norm],
        by simp [hx20_2, hx20_1, hx20, arm64_norm],
        by simp [hx19_2, hx19_1, hx19, arm64_norm]⟩, ?_⟩
    have hpack54 := memRegion54_pack (s2.readReg64 .x0)
      (s2.mem.read64 roBase)
      (s2.mem.read64 (roBase + 8#64))
      (s2.mem.read64 (roBase + 16#64))
      (s2.mem.read64 (roBase + 24#64))
      (s2.mem.read64 (roBase + 32#64))
      (s2.mem.read64 (roBase + 46#64))
    have herr := freshString_entails_pksmErrE A sret (s2.readReg64 .x0)
      (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64) s0_6 54
      ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
        ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
        ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
        ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
        ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
        ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
        ((roBase + 46#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 46#64)))
      (by decide) (by decide) hoom (bf_low8_eq_3 s0_5)
    have herr' :
        (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
          ((sret + 16#64) ↦₆₄ 54#64) ∗ ((sret + 24#64) ↦₆₄ s2.readReg64 .x0) ∗
          ((sret + 32#64) ↦₆₄ 54#64) ∗
          ((sret + 40#64) ↦₆₄ (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64)) ∗
          ((sret + 48#64) ↦₆₄ s0_6) ∗ memRegion (sret + 56#64) 192 ∗
          A.live (s2.readReg64 .x0) 54 1 ∗
          (((s2.readReg64 .x0) ↦₆₄ s2.mem.read64 roBase) ∗
            ((s2.readReg64 .x0 + 8#64) ↦₆₄ s2.mem.read64 (roBase + 8#64)) ∗
            ((s2.readReg64 .x0 + 16#64) ↦₆₄ s2.mem.read64 (roBase + 16#64)) ∗
            ((s2.readReg64 .x0 + 24#64) ↦₆₄ s2.mem.read64 (roBase + 24#64)) ∗
            ((s2.readReg64 .x0 + 32#64) ↦₆₄ s2.mem.read64 (roBase + 32#64)) ∗
            memRegion (s2.readReg64 .x0 + 40#64) 6 ∗
            ((s2.readReg64 .x0 + 46#64) ↦₆₄ s2.mem.read64 (roBase + 46#64))) ∗
          ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
            ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
            ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
            ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
            ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
            ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
            ((roBase + 46#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 46#64))) ⊢
          pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left hpack54))))))))))
        herr
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) herr')
        (by apply entails_of_eq; ac_rfl))
    dsimp only [roBase]
    simp only [hstack, hsp1_eq, errTag, speWord, arm64_norm]
    apply entails_of_eq; ac_rfl

/-! ## 2. ``w5b_kyber_ok_placed_wpW``: Full Kyber `Ok` Dispatch (`+0x684 → +0x830`) -/

/-- (``+0x684 → +0x830`, dec `1668 → 2096``):
Composes `pk_scatter_head_placed_wp` with `kyber_both_ok_placed_wp` and `kyber_neither_v3_ok_placed_wp`
from `BaseKeyOkStatePlaced` at `+0x684` (`1668`) to `KyberOkStatePlaced` at `+0x830` (`2096`)
with `kyberSpillsAtW` and `kyberStageOut`. -/
theorem w5b_kyber_ok_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64}
    {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hkpk : match kpkOpt with | some id => kpkTag = 1#32 ∧ kpkVal = id | none => kpkTag = 0#32)
    (hok : (kpkOpt.isSome && kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ vb.toNat < 0x40))
    (hst : BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk s)
    (hpc : s.pc = (blkPl_111).base + 1668#64)
    (hrun : s.status = .Running) :
    w5bc_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ (kyberBoxPtr kyberBoxLen : BitVec 64)
          (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
          (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64),
          (bk.take 33).drop 1 = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∧
          KyberOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf ∧
          (Pf ⊢ kyberSpillsAtW sp' bkCap bkPtr kyberLen ikPtr ikLen msgPtr msgLen
              regTag regVal opkTag opkVal spkVal kpkVal
              b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23 ∗
            memRegion (sp' + 312#64) 48 ∗
            kyberStageOut A kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hst_ep, hbk_ok, hpk_eq, hpk_bytes,
    hx29, hx28, hx27, hx26, hx25, _, hx23, hx22, hx21, hx20, hx19⟩
  have hlen32 : ((bk.take 33).drop 1).length = 32 := by
    rw [← hpk_bytes]; exact (pkOf bk).bytes.toList_length
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk_of⟩ :=
    exists_pkBytesOf ((bk.take 33).drop 1) hlen32
  have hpre_split :
      memRegion (sp' + 12#64) 4 ∗
        seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ⊢
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15) ∗
      (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion (sp' + 12#64) 4 ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
        ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
        ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 72#64) ↦₆₄ bkLen) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) := by
    dsimp only [seg1SpillsAtW]
    apply entails_of_eq; ac_rfl
  refine w5bc_mono_pre hpre_split ?_
  refine w5bc_bind_frame_tryFrom
    (pk_scatter_head_placed_wp hpk_of hst_ep hpc hrun hx29 hx28 hx27 hx26 hx25 hx23 hx22 hx21 hx20 hx19) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hpstate1, hx8_1, hx11_1, hx12_1,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx24_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
  refine w5bc_mono_pre (sepConj_mono_left hent1) ?_
  rcases hok with hboth | ⟨rfl, rfl, hvb_lt⟩
  · cases kpkOpt with
    | none => simp at hboth
    | some kpkId =>
      cases kyberOpt with
      | none => simp at hboth
      | some kyberCt =>
        rcases hkpk with ⟨rfl, rfl⟩
        have hvec_lt :
            optVecU8Buf A kyberCap kyberPtr kyberLen (some kyberCt) ⊢
              ⌜kyberLen = BitVec.ofNat 64 kyberCt.length ∧ kyberCap.toNat < 2 ^ 63⌝ ∗
                Wire.vecU8Buf A kyberCap kyberPtr kyberCt := by
          dsimp only [optVecU8Buf, Wire.vecU8Buf]
          refine Entails.pure_left fun hlen => Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
          rw [pure_true_emp ⟨hlen, hlt⟩, emp_sepConj, pure_true_emp ⟨hle, hlt, hne⟩, emp_sepConj]
          exact Entails.refl _
        refine w5bc_mono_pre (P' :=
            ⌜kyberLen = BitVec.ofNat 64 kyberCt.length ∧ kyberCap.toNat < 2 ^ 63⌝ ∗
            ((memRegion (sp' + 12#64) 4 ∗
              ((sp' + 40#64) ↦₆₄ kyberLen) ∗
              ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
              memRegion (sp' + 312#64) 48 ∗
              Wire.vecU8Buf A kyberCap kyberPtr kyberCt ∗
              A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
             (((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
              ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
              ((sp' + 32#64) ↦₆₄ msgLen) ∗
              ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
              ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
              ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
              ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
              spUnused112 sp' ∗
              ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
              ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
              sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6)))
          (by
            refine Entails.trans (sepConj_mono_right (sepConj_mono_left hvec_lt)) ?_
            apply entails_of_eq; ac_rfl) ?_
        refine w5bc_pure_pre fun ⟨hky_len, hky_lt⟩ => ?_
        subst hky_len
        refine w5bc_frame_tryFrom
          (kyber_both_ok_placed_wp hC hbk_ok hpk_eq hpk_bytes hky_lt hst1 hpc1 hrun1 hpstate1
            hx8_1 hx11_1 hx12_1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
          fun sf Pf ⟨kyberBoxPtr, hstf, hptr_nz, hentf⟩ => ?_
        refine ⟨kyberBoxPtr, BitVec.ofNat 64 kyberCt.length,
          b0, b1, b2, b3, b4, b5, b6, b7, b8, b31, w9, w13, w15, w23,
          hpk_of, hstf, ?_⟩
        refine Entails.trans (sepConj_mono_left hentf) ?_
        dsimp only [kyberSpillsAtW, kyberStageOut]
        rw [pure_true_emp ⟨hptr_nz, rfl, rfl⟩, emp_sepConj]
        apply entails_of_eq; ac_rfl
  · subst hkpk
    refine w5bc_mono_pre (P' :=
        optVecU8Buf A kyberCap kyberPtr kyberLen none ∗
        ((memRegion (sp' + 12#64) 4 ∗
          ((sp' + 68#64) ↦₃₂ 0#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen)) ∗
         (((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
          ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
          ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ spUnused112 sp' ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗ ((sp' + 128#64) ↦₃₂ w9) ∗
          ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (sp' + 312#64) 48 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))))
      (by apply entails_of_eq; ac_rfl) ?_
    dsimp only [optVecU8Buf]
    refine w5bc_pure_pre fun hcap => ?_
    subst hcap
    refine w5bc_frame_tryFrom
      (kyber_neither_v3_ok_placed_wp hbk_ok hpk_eq hpk_bytes hvb_lt hst1 hpc1 hrun1 hpstate1
        hx8_1 hx11_1 hx12_1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ?_
    refine ⟨0#64, kyberPtr, b0, b1, b2, b3, b4, b5, b6, b7, b8, b31, w9, w13, w15, w23, hpk_of, hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    dsimp only [kyberSpillsAtW, kyberStageOut]
    rw [pure_true_emp ⟨rfl, hvb_lt⟩]; apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
