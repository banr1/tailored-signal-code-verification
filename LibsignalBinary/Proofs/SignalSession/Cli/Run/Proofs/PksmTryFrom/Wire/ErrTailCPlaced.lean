/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailC
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.OkBridgePlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Shared Epilogue (`+0x504..+0x520`)

Proves the shared error/success epilogue (`+0x504..+0x520 → ret`) on `preKeyPlacedProg H`,
restoring callee-saved registers `x19..x30` and reassembling `stackAt s0.sp preKeyTryFromStack`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack SepWPp
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev SepWPp := Wire.SepWPp
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

private theorem stackAt_preKeyTryFrom_unsplit_etc (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 608#64) smallRootStack ∗
      memRegion (sp - 608#64) 296 ∗
      memRegion (sp - 608#64 + 296#64) 152 ∗
      memRegion (sp - 608#64 + 448#64) 64 ∗
      preKeyCalleeSavedAt (sp - 608#64) s0 ⊢
      stackAt sp preKeyTryFromStack := by
  rw [CryptoVerification.E2E.Pqxdh.ResponderWire.stackAt_preKeyTryFrom_split sp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (preKeyCalleeSavedAt_entails_memRegion96 (sp - 608#64) s0))))

/-- Shared epilogue (``+0x504 .. +0x520`, dec `1284 .. 1312``) under `[LibsignalPlacement]`:
restores `x29, x30, x28..x19` from `sp' + 512 .. sp' + 600`, adds `0x260` (`608`) to `sp`,
and returns to `s0.readReg64 .x30` with `sretOut` (arbitrary `SepProp` at `x.ret`, e.g.
`pksmErrE A fn x.ret e`, `pksmErrAt A fn x.ret`, or `RunCompose.pksmResAt A x.ret res`)
and the reassembled `stackAt s0.sp preKeyTryFromStack`. -/
theorem err_epilogue_504_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {sretOut : SepProp} {s0 s : State}
    (_hsp0 : s0.spAligned = true)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 0x504#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        sretOut ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗ sretOut ∗ (x.ptr ↦ₛ x.bytes) ∗
          lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗ A.pool))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  unfold preKeyCalleeSavedAt
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  refine SepWPp.of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro _hcl1
  refine ⟨by simp_all [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := stackAt_preKeyTryFrom_unsplit_etc s0.sp s0
    unfold preKeyCalleeSavedAt at hstk
    simp only [bv_sub_add_lit', BitVec.reduceSub] at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq; ac_rfl

/-- Exact-`pksmErrE` specialization of `err_epilogue_504_placed_wp`. -/
theorem err_epilogue_504_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {x : RunCompose.PksmGhost} {fn : List (BitVec 8)} {e : SignalProtocolError} {s0 s : State}
    (hsp0 : s0.spAligned = true)
    (hst : PostEpilogueStatePlaced s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 0x504#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        pksmErrE A fn x.ret e ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗ pksmErrE A fn x.ret e ∗ (x.ptr ↦ₛ x.bytes) ∗
          lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗ A.pool))
      (tryFromQp s0) :=
  err_epilogue_504_placed_wp hsp0 hst hpc hrun

abbrev tail_a4c_placed_wp := @cleanup_57c_placed_wp

abbrev tail_a38_placed_wp := @cleanup_568_placed_wp

abbrev tail_a28_placed_wp := @cleanup_558_placed_wp

abbrev tail_a24_placed_wp := @cleanup_554_placed_wp

abbrev deallocChain_970_placed_wp := @cleanup_4a0_placed_wp

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
