/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Missing-Field Entry Blocks (`+0x66c`, `+0x678`)

Re-exports `speWordsOf` packing lemmas and placed cleanup tails, and proves the `+0x678 → +0x7b8`
and `+0x66c → +0x7d0` error entry blocks on `preKeyPlacedProg H`.
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
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open RunProofs.Pksm

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done

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

abbrev cleanup_33c_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.cleanup_33c_placed_wp

abbrev cleanup_57c_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.cleanup_57c_placed_wp

abbrev cleanup_568_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.cleanup_568_placed_wp

abbrev cleanup_558_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.cleanup_558_placed_wp

abbrev cleanup_554_placed_wp :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.cleanup_554_placed_wp

/-- `+0x678 .. +0x680` (`1656` → `+0x7b8` / `1976`) on `preKeyPlacedProg H`:
`mov x8, #-1; str x27, [x19, #8]; b +0x7b8`. -/
theorem entry_678_to_7b8_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' sret w1 x27v : BitVec 64}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1656#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = sret)
    (hx27 : s.readReg64 .x27 = x27v) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1976#64) s
      ((sret + 8#64) ↦₆₄ w1)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.readReg64 .x8 = errTag ∧
        sf.readReg64 .x19 = sret ∧
        (Pf ⊢ (sret + 8#64) ↦₆₄ x27v))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk
    keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  exact ⟨⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
    hcl1, by simp [htr, arm64_norm]⟩,
    by simp [errTag, arm64_norm], by simp [hx19, arm64_norm], Entails.refl _⟩

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
