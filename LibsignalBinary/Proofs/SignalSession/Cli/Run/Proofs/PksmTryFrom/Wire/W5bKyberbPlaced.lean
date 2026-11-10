/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberb
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Kyber OOM Panic Tails (`+0xa74`, `+0xa80`)

Proves `kyber_a74_panic_placed_wp` and re-exports `kyber_a80_panic_placed_wp`,
`pksmParse_eq_none_of_kyber_half`, and `sepConj_rot3_kyber` on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 Arm64.Obj ProofLib.GenPlacedFetches ProofLib.ProgramReflection
open ProofLib hiding SepWPp
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
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open RunProofs.Pksm

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWP.done := @Wire.SepWP.done
private abbrev SepWPp.panic := @Wire.SepWPp.panic

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

/-- Raw-vec `handle_error` symbol in Block 111 (`alloc::raw_vec::handle_error`). -/
abbrev lsRawVecHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem raw_vec_panic_at_prekey_placed [LibsignalPlacement] {H : LibsignalHooks}
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked) :
    (preKeyPlacedProg H).externAt? ((blkPl_111).ρ lsRawVecHandleErrorSym) =
      some Rust.panicked :=
  (ls_externAt?_of_mem).trans h_panic

/-- Panic tail at `+0xa74` (`2676`) under `[LibsignalPlacement]`:
`mov w0, #1; mov w1, #68; bl handle_error`. -/
theorem kyber_a74_panic_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    {s0 s : State} {sp' target_pc : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hst : KyberExitA74StatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2676#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) target_pc s P Q (tryFromQp s0) := by
  rcases hst with ⟨_hsp_eq, _hsp, hcl, hallocF, htr⟩
  have hpan := raw_vec_panic_at_prekey_placed h_panic
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
    keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsRawVecHandleErrorSym) ?_
  wp_steps
  refine SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun _ => ?_
  refine SepWPp.panic (by simp [hrun, arm64_norm])
    (by simpa [arm64_norm] using hpan)
    fun _ hm => ?_
  have hφ : allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                ((blkPl_111).base + 2688#64)).setPC
            ((blkPl_111).ρ lsRawVecHandleErrorSym))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                  ((blkPl_111).base + 2688#64)).setPC
              ((blkPl_111).ρ lsRawVecHandleErrorSym))).trace :=
    ⟨by simpa [allocFailedIn, Rust.panicked, arm64_norm] using hallocF,
     by simpa [Rust.panicked, arm64_norm] using htr⟩
  have hent : P ⊢ ⌜allocFailedIn s0
        (Rust.panicked
          ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                ((blkPl_111).base + 2688#64)).setPC
            ((blkPl_111).ρ lsRawVecHandleErrorSym))) ∧
      s0.trace <+:
        (Rust.panicked
            ((((s.writeReg64 (Reg.gpr 0#5) 1#64).writeReg64 (Reg.gpr 1#5) 68#64).writeReg64 (Reg.gpr 30#5)
                  ((blkPl_111).base + 2688#64)).setPC
              ((blkPl_111).ρ lsRawVecHandleErrorSym))).trace⌝ ∗ anyHeap := by
    rw [pure_true_emp hφ, emp_sepConj]; exact entails_anyHeap P
  exact Satisfies.mono (sepConj_mono_left hent) hm

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
