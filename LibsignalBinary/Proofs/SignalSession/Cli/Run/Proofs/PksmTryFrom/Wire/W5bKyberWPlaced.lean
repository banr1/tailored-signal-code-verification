/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberbPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Kyber Scatter, `Ok` Branches, and Mismatched-Field Error

Proves the `[LibsignalPlacement]` `PublicKey` scatter (`+0x684 → +0x6c8`), `both` and v3
`neither` `Ok` branches (`+0x6c8 → +0x830`), panic/dealloc tails (`+0xa80`, `+0xa1c → +0xa24`),
and the 68-byte mismatched-Kyber error branch (`kyber_half_err_placed_wpE`) on
`preKeyPlacedProg H`.
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

abbrev w5bw_SepWPp := @Wire.SepWPp
private abbrev w5bw_done := @Wire.SepWP.done
private abbrev w5bw_panic := @Wire.SepWPp.panic
private abbrev w5bw_frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev w5bw_bind := @Wire.SepWPp.bind
private abbrev w5bw_bind_frame_tryFrom := @Wire.SepWPp.bind_frame_tryFrom
private abbrev w5bw_pure_pre := @Wire.SepWPp.pure_pre
private abbrev w5bw_exists_pre := @Wire.SepWPp.exists_pre
private abbrev w5bw_mono_pre := @Wire.SepWPp.mono_pre
private abbrev w5bw_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev w5bw_of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
private abbrev w5bw_call_noPanic_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_noPanic_pk
private abbrev w5bw_call_tryFrom_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.call_tryFrom_pk

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

private theorem w5bw_ule_64_vb_eq_false {vb : BitVec 8} (hvb_lt : vb.toNat < 0x40) :
    (64#64).ule (vb.zeroExtend 64) = false := by
  rw [BitVec.ule_eq_decide]
  exact decide_eq_false (by rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)

/-! ## 1. `pk_scatter_head_placed_wp`, `kyber_both_ok_placed_wp`, `kyber_neither_v3_ok_placed_wp` -/

/-- (``+0x684 .. +0x6c8`, `+1668 .. +1736``, `[LibsignalPlacement]`):
Loads the 32-byte `PublicKey` from `sp' + 313..345`, scatters `w23, b31, w9, w13, b0..b6`
into `sp' + 112..144`, keeps `b8`, `w15`, `b7` in `x8`, `x11`, `x12`, sets `x24 = sp' + 312#64`,
and sets `pstate = subsPState32 kpkTag 1#32` at `+0x6c8` (`1736`, `b.ne +0x718`). -/
theorem pk_scatter_head_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {kpkTag : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {pkBytes : List (BitVec 8)}
    (hpk : pkBytes = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1668#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    w5bw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 1736#64) s
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ pkBytes) ∗ memRegion (sp' + 345#64) 15)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pstate = subsPState32 kpkTag 1#32 ∧
        sf.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x11 = w15 ∧
        sf.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = sp' + 312#64 ∧
        sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
        sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret ∧
        (Pf ⊢ ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (sp' + 312#64) 48))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  rw [hpk, ← pkLayoutAt_eq_pointsToBytes]
  refine w5bw_mono_pre
    (sepConj_mono_right (sepConj_mono_left (memRegion32_112_unpack sp'))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine w5bw_exists_pre fun w112 => w5bw_exists_pre fun b120 =>
    w5bw_exists_pre fun w128 => w5bw_exists_pre fun w132 =>
    w5bw_exists_pre fun c0 => w5bw_exists_pre fun c1 =>
    w5bw_exists_pre fun c2 => w5bw_exists_pre fun c3 =>
    w5bw_exists_pre fun c4 => w5bw_exists_pre fun c5 =>
    w5bw_exists_pre fun c6 => ?_
  dsimp only [pkLayoutAt]
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1680#64) ?_
  conv => arg 4; dsimp only [sevenBytesHeadAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have h313_tail := sevenBytesHeadAt_eq_tailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6
  refine w5bw_mono_pre (P' :=
      ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗
      ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15)
    (by
      rw [← h313_tail]
      dsimp only [sevenBytesHeadAt, pkRestAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := (blkPl_111).base + 1704#64) ?_
  conv => arg 4; dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl2 => ?_
  have h136_tail := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6
  refine w5bw_mono_pre (P' :=
      ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesTailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6 ∗
      ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 313#64), ← h136_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  conv => arg 4; dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl3 => ?_
  refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl3,
      by simp [htr, arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm], ?_⟩
  have h136_head := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6
  have hcollapse := deser_ok_entails_memRegion48 sp' b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  rw [h136_head]
  dsimp only [sevenBytesTailAt]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hcollapse)))))))
  dsimp only [sevenBytesHeadAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_of_eq; ac_rfl

/-- (``+0x6c8 .. +0x6fc → +0x830`, `1736 .. 1788 → 2096``, `[LibsignalPlacement]`):
When `kpkTag = 1#32` (`m.kyberPreKeyId = some kpkId`) and `m.kyberCiphertext = some kyberCt`
(`kyberCap.toNat < 2 ^ 63`), stores `b8`, `b7`, `w15` to stack slots `sp' + 68`, `sp' + 12`,
`sp' + 72`, converts `kyberCt` via `into_boxed_slice`, and branches to `+0x830` (`2096`). -/
theorem kyber_both_ok_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {b7 b8 : BitVec 8} {w15 : BitVec 64}
    {kyberCt : List (BitVec 8)}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hky_lt : kyberCap.toNat < 2 ^ 63)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 1#32 1#32)
    (hx8 : s.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = w15)
    (hx12 : s.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    w5bw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
        ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
        memRegion (sp' + 312#64) 48 ∗
        Wire.vecU8Buf A kyberCap kyberPtr kyberCt ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ kyberBoxPtr : BitVec 64,
          KyberOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr (BitVec.ofNat 64 kyberCt.length)
            ikCap msgCap vb bk pk sf ∧
          kyberBoxPtr ≠ 0#64 ∧
          (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
            memRegion (sp' + 312#64) 48 ∗
            boxU8Buf A kyberBoxPtr kyberCt ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hky_eq := cap_add1_eq_of_lt hky_lt
  have hstackBox := stackAt_sub_split sp' LibsignalTripleRatchet.intoBoxedSliceStackX
    (Prost.skipFieldStackX 100) (by decide)
  conv => arg 4; rw [memRegion48_312_split24 sp']
  refine w5bw_mono_pre (sepConj_mono_left (memRegion_four_entails (sp' + 12#64))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine w5bw_exists_pre fun w328 => w5bw_exists_pre fun w320 =>
    w5bw_exists_pre fun w312 => w5bw_exists_pre fun w12 => ?_
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 56) ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm])
    (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have hvec_ky : vecU8At A (sp' + 312#64) kyberCap kyberPtr kyberCt =
      ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
      ((sp' + 328#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
      Wire.vecU8Buf A kyberCap kyberPtr kyberCt := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine w5bw_call_tryFrom_pk keepsFrozenInv_codeRoLoaded
    (⟨sp' + 312#64, kyberCap, kyberPtr, kyberCt⟩ : VecArg) hC.intoBoxedX
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 1780#64) (by simp [arm64_norm])
    (by simp [htr, arm64_norm])
    (T := vecU8At A (sp' + 312#64) kyberCap kyberPtr kyberCt ∗ A.pool ∗
      stackAt s.sp LibsignalTripleRatchet.intoBoxedSliceStackX)
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp [LibsignalTripleRatchet.intoBoxedSliceSpecX, VecArg.at, hsp_eq, arm64_norm])
    rfl
    (by rw [hvec_ky, hstackBox, hsp_eq]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [LibsignalTripleRatchet.intoBoxedSliceSpecX]
  rw [sepConj_assoc]
  refine w5bw_pure_pre fun ⟨hx1_2, htr2⟩ => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, _, hx26_2, hx27_2, _, hx29_2, _⟩
  have hbox_nz : boxU8Buf A (s2.readReg64 .x0) kyberCt ⊢
      ⌜s2.readReg64 .x0 ≠ 0#64⌝ ∗ boxU8Buf A (s2.readReg64 .x0) kyberCt := by
    refine Entails.trans (by dsimp only [boxU8Buf]; exact Entails.refl _) ?_
    refine Entails.pure_left fun ⟨hptr, hlen⟩ => ?_
    have hptr' : s2.readReg64 .x0 ≠ 0#64 := hptr
    rw [pure_true_emp hptr', emp_sepConj]
    dsimp only [boxU8Buf]
    rw [pure_true_emp ⟨hptr, hlen⟩, emp_sepConj]
    exact Entails.refl _
  have h48 : vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 kyberCt.length) ∗
      memRegion (sp' + 336#64) 24 ⊢ memRegion (sp' + 312#64) 48 := by
    rw [show (48 : Nat) = 24 + 24 by decide, Prost.memRegion_split (sp' + 312#64) 24 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (vecHeader_entails_memRegion24 (sp' + 312#64) kyberCap kyberPtr _)
  refine w5bw_mono_pre
    (P' := ⌜s2.readReg64 .x0 ≠ 0#64⌝ ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        memRegion (sp' + 312#64) 48 ∗
        boxU8Buf A (s2.readReg64 .x0) kyberCt ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by
      refine Entails.trans
        (Q := boxU8Buf A (s2.readReg64 .x0) kyberCt ∗
          ((vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 kyberCt.length) ∗
            memRegion (sp' + 336#64) 24) ∗
            ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
            A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
        (by simp only [hstackBox, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hbox_nz (sepConj_mono_left h48)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine w5bw_pure_pre fun hptr_nz => ?_
  refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
  refine ⟨s2.readReg64 .x0,
    ⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hcl3,
        by simp [htr2, htr, arm64_norm]⟩,
      hbk_ok, hpk_eq, hpk_bytes,
      by simp [hx29_2, hx29, arm64_norm], by simp [arm64_norm],
      by simp [hx27_2, hx27, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
      by simp [arm64_norm], by simp [hx24_2, hx24, arm64_norm],
      by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
      by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
      by simp [hx19_2, hx19, arm64_norm]⟩,
    hptr_nz, by apply entails_of_eq; ac_rfl⟩

/-- (``1736 → 1816 → 2072 → 2096``, `[LibsignalPlacement]`):
When `kpkTag = 0#32`, `kyberCap = noneCap`, and `vb.toNat < 0x40`, branches `1736 → 1816 → 2072`,
checks `cmp w22, #64`, sets `x28 = 0#64`, stores `b7`, `b8`, `w15` to stack slots `sp' + 12`,
`sp' + 68`, `sp' + 72`, and falls through to `+0x830` (`2096`). -/
theorem kyber_neither_v3_ok_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret len ptr0 kyberPtr bkLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {b7 b8 : BitVec 8} {w15 : BitVec 64}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hvb_lt : vb.toNat < 0x40)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx8 : s.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = w15)
    (hx12 : s.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = noneCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    w5bw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        ((sp' + 68#64) ↦₃₂ 0#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen))
      (fun sf Pf =>
        KyberOkStatePlaced s0 sp' sret len ptr0 0#64 kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcs_vb := w5bw_ule_64_vb_eq_false hvb_lt
  refine w5bw_mono_pre (sepConj_mono_left (memRegion_four_entails (sp' + 12#64))) ?_
  simp only [sepExists_sepConj_left]
  refine w5bw_exists_pre fun w12 => ?_
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2080#64) ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl1 ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl2 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl2,
        by simp [htr, arm64_norm]⟩,
      hbk_ok, hpk_eq, hpk_bytes,
      by simp [hx29, arm64_norm], by simp [arm64_norm],
      by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
      by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm],
      by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
      by simp [hx19, arm64_norm]⟩,
    by apply entails_of_eq; ac_rfl⟩

/-! ## 2. Panic Tail (`kyber_a80_panic_placed_wp`) & Dealloc (`kyber_a1c_to_a24_placed_wp`) -/

/-- Panic tail at `+0xa80` (`2688`) under `[LibsignalPlacement]`:
`mov w0, #1; mov w1, #54; bl handle_error`. -/
theorem kyber_a80_panic_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    {s0 s : State} {sp' target_pc : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hst : KyberExitA80StatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2688#64)
    (hrun : s.status = .Running) :
    w5bw_SepWPp (preKeyPlacedProg H) target_pc s P Q (tryFromQp s0) := by
  rcases hst with ⟨_hsp_eq, _hsp, hcl, hallocF, htr⟩
  have hpan := raw_vec_panic_at_prekey_placed h_panic
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsRawVecHandleErrorSym) ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun _ => ?_
  refine w5bw_panic (by simp [hrun, arm64_norm])
    (by simpa [arm64_norm] using hpan)
    fun _ hm => ?_
  have hφ : allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                ((blkPl_111).base + 2700#64)).setPC
            ((blkPl_111).ρ lsRawVecHandleErrorSym))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                  ((blkPl_111).base + 2700#64)).setPC
              ((blkPl_111).ρ lsRawVecHandleErrorSym))).trace :=
    ⟨by simpa [allocFailedIn, Rust.panicked, arm64_norm] using hallocF,
     by simpa [Rust.panicked, arm64_norm] using htr⟩
  have hent : P ⊢ ⌜allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                ((blkPl_111).base + 2700#64)).setPC
            ((blkPl_111).ρ lsRawVecHandleErrorSym))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 54#64).writeReg64 (Reg.gpr 30#5)
                  ((blkPl_111).base + 2700#64)).setPC
              ((blkPl_111).ρ lsRawVecHandleErrorSym))).trace⌝ ∗ anyHeap := by
    rw [pure_true_emp hφ, emp_sepConj]; exact entails_anyHeap P
  exact Satisfies.mono (sepConj_mono_left hent) hm

/-- Step `+0xa1c .. +0xa20 → +0xa24` (`2588 → 2596`) under `[LibsignalPlacement]`:
deallocates `kyberPtr` (`kyberCap > 0`) and transitions from `KyberExitA1cStatePlaced` at `+0xa1c`
(`2588`) to `KyberExitA24StatePlaced` at `+0xa24` (`2596`). -/
theorem kyber_a1c_to_a24_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : KyberExitA1cStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 2588#64)
    (hrun : s.status = .Running) :
    w5bw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hpos, hlt, _hne,
    hx0, hx1, hx29, hx26, hx23, hx22, hx21, hx20, hx19⟩
  have hstack := stackAt_skipFieldStackX_ext sp'
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine w5bw_call_noPanic_pk keepsFrozenInv_codeRoLoaded (kyberPtr, kyberCap.toNat, 1) hC.deallocX
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 2596#64) (by simp [arm64_norm])
    (T := A.pool ∗ A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
      stackAt s.sp extHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = kyberPtr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = kyberCap.toNat ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk kyberCap.toNat 1)
    (by simp [rustDeallocExternSpecWithStack, arm64_norm])
    ⟨hx0, by simp [hx1], rfl, layoutOk_align1 hpos hlt⟩
    (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack]
  rw [sepConj_assoc]
  refine w5bw_pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, hx26_2, _, _, hx29_2, _⟩
  refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  refine w5bw_done hpc2 hrun2 fun hcl3 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp2, hsp_eq], by tryFromPost_sp_align hsp2_align, hcl3,
        by simp [htr2, htr, arm64_norm]⟩,
      by simp [hx29_2, hx29, arm64_norm],
      by simp [hx26_2, hx26, arm64_norm],
      by simp [hx23_2, hx23, arm64_norm],
      by simp [hx22_2, hx22, arm64_norm],
      by simp [hx21_2, hx21, arm64_norm],
      by simp [hx20_2, hx20, arm64_norm],
      by simp [hx19_2, hx19, arm64_norm]⟩,
    by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl⟩

/-! ## 3. Placed Shim / Alloc / `.rodata` Helpers & `kyber_err_alloc68_head_placed_wpE` -/

theorem w5bw_shim_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec) :
    subroutine_ok (preKeyPlacedProg H) (lsρ lsRustNoAllocShimSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) noAllocShimSpec) :=
  subroutine_ok_withPreKeyInv_of_plain (ls_hook_ok_of_mem hshim)

theorem w5bw_alloc_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok (preKeyPlacedProg H) (lsρ lsRustAllocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (rustAllocSpec A)) :=
  subroutine_ok_withPreKeyInv_of_plain (ls_hook_ok_of_mem halloc)

theorem w5bw_rot_alloc (P1 P2 P3 F : SepProp) :
    (P1 ∗ P2 ∗ P3) ∗ F = P3 ∗ P1 ∗ P2 ∗ F := by ac_rfl

theorem w5bw_rodata_ro8_at [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeRoLoaded lsmpl m) (sym : String) (n off : Nat)
    (hro_sym : lsroRO sym n = true := by decide +kernel)
    (hoff : off + 8 ≤ n := by decide) (hn_lt : n < 2 ^ 32 := by decide) :
    m.RO (lsmpl.ρ sym + BitVec.ofNat 64 off) 8 := by
  have hbase : m.RO (lsmpl.ρ sym) n := lsro_perm hcl.2 hro_sym
  intro a ha
  unfold Arm64.InRegion at ha
  apply hbase a
  unfold Arm64.InRegion
  have hk : (a - (lsmpl.ρ sym + BitVec.ofNat 64 off)).toNat < 8 := ha
  have heq : a - lsmpl.ρ sym =
      (a - (lsmpl.ρ sym + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off := by bv_omega
  rw [heq, BitVec.toNat_add_of_lt]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem w5bw_rodata_ro8_at0 [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeRoLoaded lsmpl m) (sym : String) (n : Nat)
    (hro_sym : lsroRO sym n = true := by decide +kernel)
    (hn : 8 ≤ n := by decide) (hn_lt : n < 2 ^ 32 := by decide) :
    m.RO (lsmpl.ρ sym) 8 := by
  simpa [BitVec.add_zero] using w5bw_rodata_ro8_at hcl sym n 0 hro_sym (by omega) hn_lt

/-- Shared `.rodata` symbol for the 68-byte half-Kyber error message in Block 111 (`+0x734`). -/
abbrev lsPksmKyberHalfErrRoSym : String := "libsignal_protocol:.rodata..Lanon.566"

/-- Shared `.rodata` symbol for the 54-byte missing-Kyber v4 error message in Block 111 (`+0x9ac`). -/
abbrev lsPksmKyberV4ErrRoSym : String := "libsignal_protocol:.rodata..Lanon.565"

/-- Shared error-allocation head `+0x720 .. +0x780` (`1824 .. 1920`) under `[LibsignalPlacement]`:
calls `__rust_no_alloc_shim_is_unstable_v2` and `__rust_alloc(68, 1)`, panics via
`handle_error` (`tryFromQp s0`) if `x0 = 0`, otherwise copies the 68-byte `.rodata` error string
into the heap buffer, writes `pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext)`, and
reaches `+0x780` (`1920`) with `pstate = addsPState64 (kyberCap - 1#64) 2#64`. -/
theorem kyber_err_alloc68_head_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : CodecHooksPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1824#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    w5bw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 1920#64) s
      (memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pstate = addsPState64 (kyberCap - 1#64) 2#64 ∧
        sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
        sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret ∧
        (Pf ⊢ (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hshim := w5bw_shim_ok hH.shim
  have halloc := w5bw_alloc_ok hH.alloc
  have hpan := raw_vec_panic_at_prekey_placed hH.panic_raw
  clear hH
  have hstack := stackAt_sub_split sp' allocHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := lsρ lsRustNoAllocShimSym) ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  refine w5bw_call_noPanic_pk keepsFrozenInv_codeRoLoaded () hshim
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by tryFromPost_sp_align hsp) hcl1
    (ret_pc := (blkPl_111).base + 1828#64) (by simp [arm64_norm])
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
  refine w5bw_pure_pre fun htr1 => ?_
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  have hsp1_eq : s1.sp = sp' := by tryFromPost_sp [hsp1, hsp_eq]
  refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl1'
    (mid := lsρ lsRustAllocSym) ?_
  wp_steps
  refine w5bw_done (by simp [arm64_norm]) (by simp [hrun1, arm64_norm]) fun hcl2 => ?_
  have hlay68 : LayoutOk 68 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine w5bw_call_noPanic_pk keepsFrozenInv_codeRoLoaded (68, 1) halloc
    (by simp [arm64_norm]) (by simp [hrun1, arm64_norm])
    (by tryFromPost_sp_align hsp1_align) hcl2
    (ret_pc := (blkPl_111).base + 1840#64) (by simp [arm64_norm])
    (T := A.pool ∗ stackAt sp' allocHookStack)
    (φ := (68#64 : BitVec 64).toNat = 68 ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk 68 1)
    (by simp [rustAllocSpec, hsp1_eq, arm64_norm])
    ⟨rfl, rfl, hlay68⟩
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
    refine w5bw_pure_pre fun htr2 => ?_
    refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl2'
      (mid := lsρ lsRawVecHandleErrorSym) ?_
    wp_steps
    refine w5bw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun _ => ?_
    refine w5bw_panic (by simp [hrun2, arm64_norm])
      (by simpa [arm64_norm] using hpan)
      (tryFromQp_of_panicked (by simp [Rust.panicked, htr2, htr1, htr, arm64_norm]))
  · clear hpan
    simp only [hoom, ite_false, sepConj_assoc]
    refine w5bw_pure_pre fun ⟨_, htr2⟩ => ?_
    have hbeq : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    refine w5bw_mono_pre
      (sepConj_mono_right (sepConj_mono_left (memRegion68_unpack (s2.readReg64 .x0)))) ?_
    rw [memRegion248_split_err sret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine w5bw_exists_pre fun s0_6 => w5bw_exists_pre fun s0_5 =>
      w5bw_exists_pre fun s0_4 => w5bw_exists_pre fun s0_3 =>
      w5bw_exists_pre fun s0_2 => w5bw_exists_pre fun s0_1 =>
      w5bw_exists_pre fun s0_0 =>
      w5bw_exists_pre fun w8 => w5bw_exists_pre fun w7 =>
      w5bw_exists_pre fun w6 => w5bw_exists_pre fun w5 =>
      w5bw_exists_pre fun w4 => w5bw_exists_pre fun w3 =>
      w5bw_exists_pre fun w2 => w5bw_exists_pre fun w1 =>
      w5bw_exists_pre fun w0 => ?_
    let roBase := lsmpl.ρ "libsignal_protocol:.rodata..Lanon.566"
    refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2' ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at0 hcl2' "libsignal_protocol:.rodata..Lanon.566" 68) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 8) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 16) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 24) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 32) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 40) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 48) rfl ?_
    refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 56) rfl ?_
    wp_steps
    refine w5bw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
    refine ⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2_align, hcl3,
        by simp [htr2, htr1, htr, arm64_norm]⟩,
      by simp [arm64_norm],
      by simp [hx29_2, hx29_1, hx29, arm64_norm],
      by simp [hx28_2, hx28_1, hx28, arm64_norm],
      by simp [hx26_2, hx26_1, hx26, arm64_norm],
      by simp [hx25_2, hx25_1, hx25, arm64_norm],
      by simp [hx23_2, hx23_1, hx23, arm64_norm],
      by simp [hx22_2, hx22_1, hx22, arm64_norm],
      by simp [hx21_2, hx21_1, hx21, arm64_norm],
      by simp [hx20_2, hx20_1, hx20, arm64_norm],
      by simp [hx19_2, hx19_1, hx19, arm64_norm], ?_⟩
    have hpack68 := memRegion68_pack (s2.readReg64 .x0)
      (s2.mem.read64 roBase)
      (s2.mem.read64 (roBase + 8#64))
      (s2.mem.read64 (roBase + 16#64))
      (s2.mem.read64 (roBase + 24#64))
      (s2.mem.read64 (roBase + 32#64))
      (s2.mem.read64 (roBase + 40#64))
      (s2.mem.read64 (roBase + 48#64))
      (s2.mem.read64 (roBase + 56#64))
      1953391987#32
    have herr := freshString_entails_pksmErrE A sret (s2.readReg64 .x0)
      (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64) s0_6 68
      ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
        ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
        ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
        ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
        ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
        ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
        ((roBase + 48#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 48#64)) ∗
        ((roBase + 56#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 56#64)))
      (by decide) (by decide) hoom (bf_low8_eq_3 s0_5)
    have herr' :
        (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
          ((sret + 16#64) ↦₆₄ 68#64) ∗ ((sret + 24#64) ↦₆₄ s2.readReg64 .x0) ∗
          ((sret + 32#64) ↦₆₄ 68#64) ∗
          ((sret + 40#64) ↦₆₄ (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64)) ∗
          ((sret + 48#64) ↦₆₄ s0_6) ∗ memRegion (sret + 56#64) 192 ∗
          A.live (s2.readReg64 .x0) 68 1 ∗
          (((s2.readReg64 .x0) ↦₆₄ s2.mem.read64 roBase) ∗
            ((s2.readReg64 .x0 + 8#64) ↦₆₄ s2.mem.read64 (roBase + 8#64)) ∗
            ((s2.readReg64 .x0 + 16#64) ↦₆₄ s2.mem.read64 (roBase + 16#64)) ∗
            ((s2.readReg64 .x0 + 24#64) ↦₆₄ s2.mem.read64 (roBase + 24#64)) ∗
            ((s2.readReg64 .x0 + 32#64) ↦₆₄ s2.mem.read64 (roBase + 32#64)) ∗
            ((s2.readReg64 .x0 + 40#64) ↦₆₄ s2.mem.read64 (roBase + 40#64)) ∗
            ((s2.readReg64 .x0 + 48#64) ↦₆₄ s2.mem.read64 (roBase + 48#64)) ∗
            ((s2.readReg64 .x0 + 56#64) ↦₆₄ s2.mem.read64 (roBase + 56#64)) ∗
            ((s2.readReg64 .x0 + 64#64) ↦₃₂ 1953391987#32)) ∗
          ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
            ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
            ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
            ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
            ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
            ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
            ((roBase + 48#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 48#64)) ∗
            ((roBase + 56#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 56#64))) ⊢
          pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left hpack68))))))))))
        herr
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) herr')
        (by apply entails_of_eq; ac_rfl))
    dsimp only [roBase]
    simp only [hstack, hsp1_eq, errTag, speWord, arm64_norm]
    apply entails_of_eq; ac_rfl

/-- (``+0x6c8 → +0xa24` / `+0xa74`, dec `1736 → 2596``):
When `(kpkOpt.isSome != kyberOpt.isSome) = true`, branches `+0x6c8` (`1736`) → `+0x720` (`1824`),
allocates the 68-byte error string, writes `pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext)`,
deallocates `kyberPtr` via `+0xa1c` when `kyberCap > 0`, and reaches `+0xa24` (`2596`). -/
theorem kyber_half_err_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : CodecHooksPlaced A H) (hC : PksmCalleesPlaced A H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {kpkTag : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    (htag : kpkTag = if kpkOpt.isSome then 1#32 else 0#32)
    (hhalf : (kpkOpt.isSome != kyberOpt.isSome) = true)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 kpkTag 1#32)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    w5bw_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      (optVecU8Buf A kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      (tryFromQp s0) := by
  subst htag
  cases kpkOpt with
  | some _kpkId =>
    cases kyberOpt with
    | some _ => simp at hhalf
    | none =>
      dsimp only [optVecU8Buf]
      refine w5bw_pure_pre fun hcap => ?_
      subst hcap
      rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
      have h1 : w5bw_SepWPp (preKeyPlacedProg H)
          ((blkPl_111).base + 1824#64) s
          (memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
          (fun s1 P1 =>
            PostEpilogueStatePlaced s0 sp' s1 ∧
            s1.readReg64 .x29 = sp' + 512#64 ∧ s1.readReg64 .x28 = noneCap ∧
            s1.readReg64 .x27 = 0x8000000000000002#64 ∧ s1.readReg64 .x26 = msgCap ∧
            s1.readReg64 .x25 = kyberPtr ∧ s1.readReg64 .x23 = ikCap ∧
            s1.readReg64 .x22 = vb.zeroExtend 64 ∧ s1.readReg64 .x21 = ptr0 ∧
            s1.readReg64 .x20 = len ∧ s1.readReg64 .x19 = sret ∧
            (P1 ⊢ memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
          (tryFromQp s0) := by
        refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
        wp_steps
        refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
        exact ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
            by simp [htr, arm64_norm]⟩,
          by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
          by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
          by simp [hx25, arm64_norm], by simp [hx23, arm64_norm],
          by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
          by simp [hx20, arm64_norm], by simp [hx19, arm64_norm],
          Entails.refl _⟩
      refine w5bw_bind h1 ?_; clear h1
      rintro s1 P1 hpc1 hrun1 ⟨hst1, hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
      refine w5bw_mono_pre hent1 ?_
      refine w5bw_bind
        (kyber_err_alloc68_head_placed_wpE hH hst1 hpc1 hrun1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hst2, hpstate2, hx29_2, hx28_2, hx26_2, _hx25_2, hx23_2, hx22_2, hx21_2, hx20_2, hx19_2, hent2⟩
      rcases hst2 with ⟨hsp2_eq, hsp2, hcl2, htr2⟩
      refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
      wp_steps
      refine w5bw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
      exact ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hcl3,
            by simp [htr2, arm64_norm]⟩,
          by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
          by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
          by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
          by simp [hx19_2, arm64_norm]⟩, hent2⟩
  | none =>
    cases kyberOpt with
    | none => simp at hhalf
    | some kyberCt =>
      have hcap_lt :
          optVecU8Buf A kyberCap kyberPtr kyberLen (some kyberCt) ⊢
            ⌜kyberCap.toNat < 2 ^ 63⌝ ∗
              ∃∗ active : Bool, deallocSlot A kyberCap kyberPtr active := by
        dsimp only [optVecU8Buf, Wire.vecU8Buf]
        refine Entails.pure_left fun hlen => Entails.pure_left fun ⟨_, hlt, _⟩ => ?_
        have hlt' : kyberCap.toNat < 2 ^ 63 := hlt
        rw [pure_true_emp hlt', emp_sepConj]
        refine Entails.trans ?_ (optVecU8Buf_entails_deallocSlot A kyberCap kyberPtr kyberLen (some kyberCt))
        dsimp only [optVecU8Buf, Wire.vecU8Buf]
        rw [pure_true_emp hlen, emp_sepConj, pure_true_emp ⟨‹_›, hlt, ‹_›⟩, emp_sepConj]
        exact Entails.refl _
      refine w5bw_mono_pre (sepConj_mono_left hcap_lt) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine w5bw_exists_pre fun active => ?_
      refine w5bw_pure_pre fun hky_lt => ?_
      have hky_eq := cap_add1_eq_of_lt hky_lt
      rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
      have h1 : w5bw_SepWPp (preKeyPlacedProg H)
          ((blkPl_111).base + 1824#64) s
          (deallocSlot A kyberCap kyberPtr active ∗
            memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
          (fun s1 P1 =>
            PostEpilogueStatePlaced s0 sp' s1 ∧
            s1.readReg64 .x29 = sp' + 512#64 ∧ s1.readReg64 .x28 = kyberCap ∧
            s1.readReg64 .x27 = 0x8000000000000002#64 ∧ s1.readReg64 .x26 = msgCap ∧
            s1.readReg64 .x25 = kyberPtr ∧ s1.readReg64 .x23 = ikCap ∧
            s1.readReg64 .x22 = vb.zeroExtend 64 ∧ s1.readReg64 .x21 = ptr0 ∧
            s1.readReg64 .x20 = len ∧ s1.readReg64 .x19 = sret ∧
            (P1 ⊢ (memRegion sret 248 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
              deallocSlot A kyberCap kyberPtr active))
          (tryFromQp s0) := by
        refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
        wp_steps
        refine w5bw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
        refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
            by simp [htr, arm64_norm]⟩,
          by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
          by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
          by simp [hx25, arm64_norm], by simp [hx23, arm64_norm],
          by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
          by simp [hx20, arm64_norm], by simp [hx19, arm64_norm],
          by apply entails_of_eq; ac_rfl⟩
      refine w5bw_bind h1 ?_; clear h1
      rintro s1 P1 hpc1 hrun1 ⟨hst1, hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
      refine w5bw_mono_pre hent1 ?_
      refine w5bw_bind_frame_tryFrom
        (kyber_err_alloc68_head_placed_wpE hH hst1 hpc1 hrun1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hst2, hpstate2, hx29_2, hx28_2, hx26_2, hx25_2, hx23_2, hx22_2, hx21_2, hx20_2, hx19_2, hent2⟩
      refine w5bw_mono_pre (P' := deallocSlot A kyberCap kyberPtr active ∗
          (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
        (Entails.trans (sepConj_mono_left hent2) (by apply entails_of_eq; ac_rfl)) ?_
      cases active with
      | false =>
        have hdealloc : deallocSlot A kyberCap kyberPtr false = ⌜kyberCap = noneCap ∨ kyberCap = 0#64⌝ := rfl
        rw [hdealloc]
        refine w5bw_pure_pre fun hcap0 => ?_
        rcases hst2 with ⟨hsp2_eq, hsp2, hcl2, htr2⟩
        rcases hcap0 with rfl | rfl
        all_goals
          refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
          wp_steps
          refine w5bw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
          exact ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hcl3,
                by simp [htr2, arm64_norm]⟩,
              by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
              by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
              by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
              by simp [hx19_2, arm64_norm]⟩,
            by apply entails_of_eq; ac_rfl⟩
      | true =>
        have hdealloc : deallocSlot A kyberCap kyberPtr true =
            (⌜0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64⌝ ∗
              A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat) := rfl
        rw [hdealloc]
        simp only [sepConj_assoc]
        refine w5bw_pure_pre fun ⟨hpos, hlt, hne_ptr⟩ => ?_
        have hhi := cap_sub1_add2_hi_of_pos_lt hpos hlt
        rcases hst2 with ⟨hsp2_eq, hsp2, hcl2, htr2⟩
        have h3 : w5bw_SepWPp (preKeyPlacedProg H)
            ((blkPl_111).base + 2588#64) s2
            (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
              pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap ∗
              A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
            (fun s3 P3 =>
              KyberExitA1cStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s3 ∧
              (P3 ⊢ (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
                  A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
                (pksmErrE A [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap)))
            (tryFromQp s0) := by
          refine w5bw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 1924#64) ?_
          wp_steps
          refine w5bw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl2' => ?_
          refine w5bw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2' ?_
          wp_steps
          refine w5bw_done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcl3 => ?_
          refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hcl3,
                by simp [htr2, arm64_norm]⟩,
              hpos, hlt, hne_ptr,
              by simp [arm64_norm], by simp [arm64_norm],
              by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
              by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
              by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
              by simp [hx19_2, arm64_norm]⟩,
            by apply entails_of_eq; ac_rfl⟩
        refine w5bw_bind h3 ?_; clear h3
        rintro s3 P3 hpc3 hrun3 ⟨hst3, hent3⟩
        refine w5bw_mono_pre hent3 ?_
        refine w5bw_frame_tryFrom (kyber_a1c_to_a24_placed_wp hC hst3 hpc3 hrun3)
          fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
        refine Entails.trans (sepConj_mono_left hentf) ?_
        apply entails_of_eq; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
