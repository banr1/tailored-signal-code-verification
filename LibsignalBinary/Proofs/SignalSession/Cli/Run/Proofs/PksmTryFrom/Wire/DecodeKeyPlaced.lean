/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PrologueBPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Loop-Exit State and 8-Way Tag Dispatch

Defines `PreKeyLoopExitStatePlaced` at `+0x460` (`1120`) and proves the 8-way protobuf tag
dispatch `dispatchPK_placed_cps` (`+0x170..+0x234`) on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
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
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open RunProofs.Pksm

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk

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

/-- State invariant at the `+0x460` loop exit under `[LibsignalPlacement]`. -/
structure PreKeyLoopExitStatePlaced [LibsignalPlacement]
    (s0 : State) (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (sf : State) : Prop where
  regs : PreKeyLoopRegs sp' sret len ptr0 vb sf
  spAligned : sf.spAligned = true
  codeRoLoaded : LibsignalCodeRoLoaded lsmpl sf.mem
  trace : sf.trace = s0.trace

set_option maxHeartbeats 800000 in
/-- `[LibsignalPlacement]` 8-way tag dispatch at `+0x170` (`368`) on `preKeyPlacedProg H`. -/
theorem dispatchPK_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {tag : Nat}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x170#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag) (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x260#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x190#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x2a0#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h4 : tag = 4 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x200#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h5 : tag = 5 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x280#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h6 : tag = 6 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x1d0#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h7 : tag = 7 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x2c8#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h8 : tag = 8 → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x238#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp)
    (h9 : 9 ≤ tag → ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x2d8#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 P Q Qp) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 0x460#64) s P Q Qp := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 608#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h1 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 400#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h2 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 672#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h3 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 4#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 512#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h4 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 5#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 640#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h5 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 6#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 464#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h6 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 7#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 712#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h7 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 8#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
      (mid := (blkPl_111).base + 568#64) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
    exact h8 rfl _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 9) := hx1
    obtain ⟨hc1, hc2, hc2_ne, hc3, hc3_ne, hc4, hc4_ne, hc5, hc6, hc6_ne, hc7, hc7_ne, hc8, hc8_ne⟩ :=
      tag_ge9_conds (n + 9) (by omega) htag_lt
    cases hgt4 : BitVec.slt 4#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32)
    · cases hgt2 : BitVec.slt 2#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32)
      · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
          (mid := (blkPl_111).base + 728#64) ?_
        wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
      · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
          (mid := (blkPl_111).base + 728#64) ?_
        wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
    · cases hgt6 : BitVec.slt 6#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32)
      · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
          (mid := (blkPl_111).base + 728#64) ?_
        wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr
      · refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
          (mid := (blkPl_111).base + 728#64) ?_
        wp_steps
        refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hcl1 => ?_
        exact h9 (by omega) _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
           by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
           by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19⟩
          (by simp only [arm64_norm]) (by simpa [arm64_norm] using hx1')
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
