/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssembly
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTail
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresence

/-!
# `PreKeySignalMessage::try_from`: Shared `+0x504` Error-Epilogue Closing and Stack Reassembly

Proves `w8b_errTail_close` (`+0x504 → ret` via `epilogue_504_err_wpE` and `w8b_errPost`)
and stack-frame reassembly helpers shared across the post-loop error continuations.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs

/-- `SepWPp.exists_pre` lifted under a right-hand frame `(∃∗ a, P a) ∗ F`. -/
theorem w8bErrW_exists_pre_frame {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ a, Wire.SepWPp prog ret s (P a ∗ F) Q Qp) :
    Wire.SepWPp prog ret s ((∃∗ a, P a) ∗ F) Q Qp := by
  rw [sepExists_sepConj_left]
  exact Wire.SepWPp.exists_pre h

/-- Shared `+0x504` (`1284`) error-epilogue closing: absorbs any residual heap
garbage `R` into `anyHeap`, steps `epilogue_504_err_wpE`, and closes `(pksmTryFromSpec A img).post`
via `w8b_errPost`. -/
theorem w8b_errTail_close {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {x : RunCompose.PksmGhost}
    {s0 s : State} {R : SepProp} {fn : List (BitVec 8)} {e : SignalProtocolError}
    (hparse : Pksm.pksmParse x.bytes = none)
    (hst : PostEpilogueState img s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 1284#64)
    (hrun : s.status = .Running) :
    Wire.SepWPp (contractProg img.base ext) (s0.readReg64 .x30) s
      (pksmErrE A fn x.ret e ∗ R ∗
        stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧
        (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (pksmTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  refine SepWPp.mono_post
    (Wire.SepWPp.mono_pre
      (P' := stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (pksmErrE A fn x.ret e ∗ anyHeap) ∗
        (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
      (by
        refine Entails.trans
          (Q := stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
            memRegion (s0.sp - 608#64) 296 ∗
            memRegion (s0.sp - 608#64 + 296#64) 152 ∗
            memRegion (s0.sp - 608#64 + 448#64) 64 ∗
            preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
            (pksmErrE A fn x.ret e ∗ R) ∗
            (x.ptr ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
          (by apply entails_of_eq; ac_rfl) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (entails_anyHeap R))))))))
      (epilogue_504_err_wpE (x := x) fn e hst hpc hrun)) ?_
  intro sf Pf _ _ hq
  exact w8b_errPost hparse hq

/-! ### Stack-Frame Re-Assembly Helpers -/

theorem w8bSeg1Cells_entails_memRegion96 (sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen :
    BitVec 64) (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32) :
    ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
      ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
      ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
      ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
      ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
      ((sp' + 68#64) ↦₃₂ kpkTag) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ⊢
      memRegion (sp' + 16#64) 96 := by
  have h : seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
      regTag regVal opkTag opkVal spkVal kpkTag kpkVal ⊢ memRegion (sp' + 16#64) 96 := by
    dsimp only [seg1SpillsAtW]
    rw [ProofLib.memRegion_split (sp' + 16#64) 4 92 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64) 4 88 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64) 4 84 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 72 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 64 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 4 60 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 48 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 44 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 4#64) 4 40 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 4#64 + 4#64) 8 32 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 4#64 + 4#64 + 8#64) 8 24 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64) 8 16 (by decide),
      ProofLib.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))))))))))))))
  exact Entails.trans (by dsimp only [seg1SpillsAtW]; apply entails_of_eq; ac_rfl) h

theorem w8bMemRegion248_eq_words2 (sret : BitVec 64) :
    memRegion sret 248 = ∃∗ w8 : BitVec 64, ∃∗ w0 : BitVec 64,
      (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ memRegion (sret + 16#64) 232 := by
  rw [ProofLib.memRegion_split sret 8 240 (by decide),
    ProofLib.memRegion_split (sret + 8#64) 8 232 (by decide),
    ProofLib.memRegion_eight sret, ProofLib.memRegion_eight (sret + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

theorem w8bWords2_entails_memRegion248 (sret w0 w8 : BitVec 64) :
    (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w8) ∗ memRegion (sret + 16#64) 232 ⊢
      memRegion sret 248 := by
  rw [ProofLib.memRegion_split sret 8 240 (by decide),
    ProofLib.memRegion_split (sret + 8#64) 8 232 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem w8bMemRegion296_split_16_96 (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 16 ∗ memRegion (sp' + 16#64) 96 ∗ memRegion (sp' + 112#64) 184 := by
  rw [ProofLib.memRegion_split sp' 16 280 (by decide),
    ProofLib.memRegion_split (sp' + 16#64) 96 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem w8bMemRegion152_split (sp' : BitVec 64) :
    memRegion (sp' + 296#64) 152 =
      memRegion (sp' + 296#64) 16 ∗ memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 88 := by
  rw [ProofLib.memRegion_split (sp' + 296#64) 16 136 (by decide),
    ProofLib.memRegion_split (sp' + 296#64 + 16#64) 48 88 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
