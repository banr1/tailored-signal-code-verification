/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureEntry -- shake: keep

/-!
# Poll Stage P2/P3/P4 Spatial Folding and Account-Distinctness Helpers

Coroutine and 3280-byte stack frame folding lemmas reducing Stage P2 error exits, Stage P3 error /
version-mismatch exits, and Stage P4 exits back into `dpFutDoneAt` and `memRegion sp 3280`,
together with `distinctSid_of_decPkOk`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Universal Coroutine Region Folding into `dpFutDoneAt` -/

/-- Coroutine sub-regions outside Stage P1 that remain untouched after Stage P2 splits
`memRegion (fut + 0x280#64) 64` and `memRegion (fut + 0x468#64) 40`. -/
def coroPostP2UnusedAt (fut : BitVec 64) : SepProp :=
  memRegion (fut + 0x2c1#64) 7 ∗
  memRegion (fut + 0x391#64) 7 ∗
  memRegion (fut + 0x3a8#64) 128 ∗
  memRegion (fut + 0x4b0#64) 66 ∗
  memRegion (fut + 0x4f3#64) 5 ∗
  memRegion (fut + 0x4f8#64) 736

theorem coroUnusedP1At_eq_postP2 (fut : BitVec 64) :
    coroUnusedP1At fut =
      memRegion (fut + 0x280#64) 64 ∗
      memRegion (fut + 0x468#64) 40 ∗
      coroPostP2UnusedAt fut := by
  unfold coroUnusedP1At coroPostP2UnusedAt
  ac_rfl

/-- Fold fine-grained coroutine sub-regions (`[0..704)`, `[+0x2c0] = 1#8`, and the active sub-regions
complementing `coroPostP2UnusedAt fut` on `[0x2c1..2008)`) back into `dpFutDoneAt fut`. -/
theorem coro_regions_entails_dpFutDoneAt (fut : BitVec 64) :
    memRegion fut 112 ∗
    memRegion (fut + 0x70#64) 112 ∗
    memRegion (fut + 0xe0#64) 24 ∗
    memRegion (fut + 0xf8#64) 344 ∗
    memRegion (fut + 0x250#64) 48 ∗
    memRegion (fut + 0x280#64) 24 ∗
    memRegion (fut + 0x298#64) 8 ∗
    memRegion (fut + 0x2a0#64) 8 ∗
    memRegion (fut + 0x2a8#64) 4 ∗
    memRegion (fut + 0x2ac#64) 20 ∗
    ((fut + 0x2c0#64) ↦₈ 1#8) ∗
    memRegion (fut + 0x2c8#64) 200 ∗
    memRegion (fut + 0x390#64) 1 ∗
    memRegion (fut + 0x398#64) 16 ∗
    memRegion (fut + 0x428#64) 64 ∗
    memRegion (fut + 0x468#64) 40 ∗
    memRegion (fut + 0x490#64) 32 ∗
    memRegion (fut + 0x4f2#64) 1 ∗
    coroPostP2UnusedAt fut ⊢ dpFutDoneAt fut := by
  unfold coroPostP2UnusedAt dpFutDoneAt
  dsimp only [dpFutStateOff, dpFutSize]
  simp only [Nat.reduceAdd, Nat.reduceSub]
  have h64 : memRegion (fut + 0x280#64) 64 =
      memRegion (fut + 0x280#64) 24 ∗
      memRegion (fut + 0x298#64) 8 ∗
      memRegion (fut + 0x2a0#64) 8 ∗
      memRegion (fut + 0x2a8#64) 4 ∗
      memRegion (fut + 0x2ac#64) 20 := by
    rw [memRegion_split (fut + 0x280#64) 24 40 (by decide),
        memRegion_split (fut + 0x280#64 + 24#64) 8 32 (by decide),
        memRegion_split (fut + 0x280#64 + 24#64 + 8#64) 8 24 (by decide),
        memRegion_split (fut + 0x280#64 + 24#64 + 8#64 + 8#64) 4 20 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h368 : memRegion (fut + 0xe0#64) 368 =
      memRegion (fut + 0xe0#64) 24 ∗ memRegion (fut + 0xf8#64) 344 := by
    rw [memRegion_split (fut + 0xe0#64) 24 344 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h704 : memRegion fut 704 =
      memRegion fut 112 ∗ memRegion (fut + 0x70#64) 112 ∗
      memRegion (fut + 0xe0#64) 368 ∗
      memRegion (fut + 0x250#64) 48 ∗ memRegion (fut + 0x280#64) 64 := by
    rw [memRegion_split fut 112 592 (by decide),
        memRegion_split (fut + 112#64) 112 480 (by decide),
        memRegion_split (fut + 112#64 + 112#64) 368 112 (by decide),
        memRegion_split (fut + 112#64 + 112#64 + 368#64) 48 64 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1303 : memRegion (fut + 0x2c1#64) 1303 =
      memRegion (fut + 0x2c1#64) 7 ∗ memRegion (fut + 0x2c8#64) 200 ∗
      memRegion (fut + 0x390#64) 1 ∗ memRegion (fut + 0x391#64) 7 ∗
      memRegion (fut + 0x398#64) 16 ∗ memRegion (fut + 0x3a8#64) 128 ∗
      memRegion (fut + 0x428#64) 64 ∗ memRegion (fut + 0x468#64) 40 ∗
      memRegion (fut + 0x490#64) 32 ∗ memRegion (fut + 0x4b0#64) 66 ∗
      memRegion (fut + 0x4f2#64) 1 ∗ memRegion (fut + 0x4f3#64) 5 ∗
      memRegion (fut + 0x4f8#64) 736 := by
    rw [memRegion_split (fut + 0x2c1#64) 7 1296 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64) 200 1096 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64) 1 1095 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64) 7 1088 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64) 16 1072 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64) 128 944 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64) 64 880 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64) 40 840 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64) 32 808 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64 + 32#64) 66 742 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64 + 32#64 + 66#64) 1 741 (by decide),
        memRegion_split (fut + 0x2c1#64 + 7#64 + 200#64 + 1#64 + 7#64 + 16#64 + 128#64 + 64#64 + 40#64 + 32#64 + 66#64 + 1#64) 5 736 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h704, h368, h64, h1303]
  sep_frame

/-- Join `memRegion (fut + 0x2c8#64) 16 ∗ memRegion (fut + 0x2d8#64) 184` into
`memRegion (fut + 0x2c8#64) 200`. -/
theorem coro_2c8_16_184_eq (fut : BitVec 64) :
    memRegion (fut + 0x2c8#64) 200 =
      memRegion (fut + 0x2c8#64) 16 ∗ memRegion (fut + 0x2d8#64) 184 := by
  rw [memRegion_split (fut + 0x2c8#64) 16 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Three adjacent `↦₆₄` cells at `a, a+8, a+16` entail `memRegion a 24`. -/
theorem words3_entails_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 0x8#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_split a 8 16 (by decide),
      memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a w0)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1)
      (ProofLib.pointsTo64_entails_memRegion (a + 16#64) w2))

/-! ## 2. Bidirectional Stack Frame Splits & Folds for Stage P3 (`+0x1778`) -/

/-- Untouched gap bytes inside `[sp + 0x08.. sp + 0x98)` (`[+0x20..0x24)`, `[+0x58..0x5c)`,
`[+0x78..0x7c)`). -/
def spLowGapsAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x20#64) 4 ∗
  memRegion (sp + 0x58#64) 4 ∗
  memRegion (sp + 0x78#64) 4

/-- Untouched gap regions inside `[sp + 0x550.. sp + 0xc70)` around `[+0x930..0x990)` and
`[+0xa90..0xbe8)`. -/
def spHighGapsAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x550#64) 992 ∗
  memRegion (sp + 0x990#64) 256 ∗
  memRegion (sp + 0xbe8#64) 136

/-- Split `memRegion (sp + 0x550#64) 1824` into `memRegion (sp + 0x930#64) 96`,
`memRegion (sp + 0xa90#64) 344`, and `spHighGapsAt sp`. -/
theorem sp_550_1824_split_genP3 (sp : BitVec 64) :
    memRegion (sp + 0x550#64) 1824 =
      memRegion (sp + 0x930#64) 96 ∗
      memRegion (sp + 0xa90#64) 344 ∗
      spHighGapsAt sp := by
  unfold spHighGapsAt
  rw [memRegion_split (sp + 0x550#64) 992 832 (by decide),
      memRegion_split (sp + 0x550#64 + 992#64) 96 736 (by decide),
      memRegion_split (sp + 0x550#64 + 992#64 + 96#64) 256 480 (by decide),
      memRegion_split (sp + 0x550#64 + 992#64 + 96#64 + 256#64) 344 136 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Join `memRegion (sp + 0x930#64) 48 ∗ memRegion (sp + 0x960#64) 48` into
`memRegion (sp + 0x930#64) 96`. -/
theorem sp_930_48_48_eq (sp : BitVec 64) :
    memRegion (sp + 0x930#64) 96 =
      memRegion (sp + 0x930#64) 48 ∗ memRegion (sp + 0x960#64) 48 := by
  rw [memRegion_split (sp + 0x930#64) 48 48 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem pts64_mr {a v : BitVec 64} {P Q : SepProp} (h : P ⊢ Q) :
    (a ↦₆₄ v) ∗ P ⊢ memRegion a 8 ∗ Q :=
  sepConj_mono (ProofLib.pointsTo64_entails_memRegion a v) h

private theorem pts32_mr {a : BitVec 64} {v : BitVec 32} {P Q : SepProp} (h : P ⊢ Q) :
    (a ↦₃₂ v) ∗ P ⊢ memRegion a 4 ∗ Q :=
  sepConj_mono (pointsTo32_entails_memRegion a v) h

/-- Fold `genP3S5SpillRem sp ∗ memRegion (sp + 0x930#64) 48 ∗ spLowGapsAt sp` plus `[+0x80]`,
`[+0x88]`, `[+0x90]` back into `memRegion (sp + 0x8#64) 144`, `((sp + 0x98#64) ↦₆₄ _)`,
`((sp + 0xd0#64) ↦₆₄ _)`, and `memRegion (sp + 0x930#64) 96`. -/
theorem genP3S5SpillRem_fold (sp : BitVec 64) (v80 v88 v90 : BitVec 64) :
    genP3S5SpillRem sp ∗
    memRegion (sp + 0x930#64) 48 ∗
    ((sp + 0x80#64) ↦₆₄ v80) ∗
    ((sp + 0x88#64) ↦₆₄ v88) ∗
    ((sp + 0x90#64) ↦₆₄ v90) ∗
    spLowGapsAt sp ⊢
      memRegion (sp + 0x8#64) 144 ∗
      memRegion (sp + 0x930#64) 96 ∗
      (∃∗ u_98 : BitVec 64, (sp + 0x98#64) ↦₆₄ u_98) ∗
      (∃∗ u_d0 : BitVec 64, (sp + 0xd0#64) ↦₆₄ u_d0) := by
  have hPend : genP3PendSpillScratch sp ⊢
      memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 0x10#64) 8 ∗ memRegion (sp + 0x18#64) 8 ∗
      memRegion (sp + 0x24#64) 4 ∗ memRegion (sp + 0x28#64) 4 ∗ memRegion (sp + 0x2c#64) 4 :=
    Entails.sepExists_elim fun w =>
      pts64_mr (pts64_mr (pts64_mr (pts32_mr (pts32_mr (pointsTo32_entails_memRegion _ _)))))
  have hTail : genP3TailSpillScratch sp ⊢
      memRegion (sp + 0x30#64) 4 ∗ memRegion (sp + 0x34#64) 4 ∗
      memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 :=
    Entails.sepExists_elim fun w =>
      pts32_mr (pts32_mr (pts64_mr (ProofLib.pointsTo64_entails_memRegion _ _)))
  have hChains : genP3ChainsSpillScratch sp ⊢
      memRegion (sp + 0x60#64) 8 ∗ memRegion (sp + 0x68#64) 8 ∗ memRegion (sp + 0x70#64) 8 :=
    Entails.sepExists_elim fun w =>
      pts64_mr (pts64_mr (ProofLib.pointsTo64_entails_memRegion _ _))
  have hFront :
      (∃∗ w : GenP3S5FrontRem,
        ((sp + 0x48#64) ↦₆₄ w.u48) ∗ ((sp + 0x50#64) ↦₆₄ w.u50) ∗
        ((sp + 0x5c#64) ↦₃₂ w.u5c) ∗ ((sp + 0x7c#64) ↦₃₂ w.u7c) ∗
        ((sp + 0x98#64) ↦₆₄ w.u98) ∗ ((sp + 0xd0#64) ↦₆₄ w.ud0)) ⊢
      memRegion (sp + 0x48#64) 8 ∗ memRegion (sp + 0x50#64) 8 ∗
      memRegion (sp + 0x5c#64) 4 ∗ memRegion (sp + 0x7c#64) 4 ∗
      (∃∗ u_98 : BitVec 64, (sp + 0x98#64) ↦₆₄ u_98) ∗
      (∃∗ u_d0 : BitVec 64, (sp + 0xd0#64) ↦₆₄ u_d0) :=
    Entails.sepExists_elim fun w =>
      pts64_mr (pts64_mr (pts32_mr (pts32_mr
        (sepConj_mono (Entails.sepExists_right w.u98 (Entails.refl _))
          (Entails.sepExists_right w.ud0 (Entails.refl _))))))
  have h144 : memRegion (sp + 0x8#64) 144 =
      memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 0x10#64) 8 ∗ memRegion (sp + 0x18#64) 8 ∗
      memRegion (sp + 0x20#64) 4 ∗
      memRegion (sp + 0x24#64) 4 ∗ memRegion (sp + 0x28#64) 4 ∗ memRegion (sp + 0x2c#64) 4 ∗
      memRegion (sp + 0x30#64) 4 ∗ memRegion (sp + 0x34#64) 4 ∗
      memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ∗
      memRegion (sp + 0x48#64) 8 ∗ memRegion (sp + 0x50#64) 8 ∗
      memRegion (sp + 0x58#64) 4 ∗ memRegion (sp + 0x5c#64) 4 ∗
      memRegion (sp + 0x60#64) 8 ∗ memRegion (sp + 0x68#64) 8 ∗ memRegion (sp + 0x70#64) 8 ∗
      memRegion (sp + 0x78#64) 4 ∗ memRegion (sp + 0x7c#64) 4 ∗
      memRegion (sp + 0x80#64) 8 ∗ memRegion (sp + 0x88#64) 8 ∗ memRegion (sp + 0x90#64) 8 := by
    rw [memRegion_split (sp + 0x8#64) 8 136 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64) 8 128 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64) 8 120 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64) 4 116 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64) 4 112 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64) 4 108 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64) 4 104 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64) 4 100 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64) 4 96 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 88 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 80 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 8 72 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64) 4 60 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 48 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 8 40 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64) 8 32 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64) 4 28 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 4#64) 4 24 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 16 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hSpill : genP3S5SpillRem sp ⊢
      (memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 0x10#64) 8 ∗ memRegion (sp + 0x18#64) 8 ∗
        memRegion (sp + 0x24#64) 4 ∗ memRegion (sp + 0x28#64) 4 ∗ memRegion (sp + 0x2c#64) 4) ∗
      (memRegion (sp + 0x30#64) 4 ∗ memRegion (sp + 0x34#64) 4 ∗
        memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8) ∗
      (memRegion (sp + 0x60#64) 8 ∗ memRegion (sp + 0x68#64) 8 ∗ memRegion (sp + 0x70#64) 8) ∗
      (memRegion (sp + 0x48#64) 8 ∗ memRegion (sp + 0x50#64) 8 ∗
        memRegion (sp + 0x5c#64) 4 ∗ memRegion (sp + 0x7c#64) 4 ∗
        (∃∗ u_98 : BitVec 64, (sp + 0x98#64) ↦₆₄ u_98) ∗
        (∃∗ u_d0 : BitVec 64, (sp + 0xd0#64) ↦₆₄ u_d0)) ∗
      memRegion (sp + 0x960#64) 48 := by
    unfold genP3S5SpillRem
    exact sepConj_mono hPend (sepConj_mono hTail (sepConj_mono hChains (sepConj_mono_left hFront)))
  unfold spLowGapsAt
  rw [h144, sp_930_48_48_eq sp]
  refine Entails.trans (sepConj_mono hSpill (sepConj_mono_right
    (pts64_mr (pts64_mr (pts64_mr (Entails.refl _)))))) ?_
  generalize (∃∗ u_98 : BitVec 64, (sp + 0x98#64) ↦₆₄ u_98) = P98
  generalize (∃∗ u_d0 : BitVec 64, (sp + 0xd0#64) ↦₆₄ u_d0) = Pd0
  sep_frame

/-! ## 3. Universal Stack Frame (`memRegion sp 3280`) Splits & Exit Folding -/

/-- Untouched gap sub-regions inside `[sp + 0x234.. sp + 0x3e0)` (`428` bytes). -/
def spMidGapsAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x234#64) 28 ∗
  memRegion (sp + 0x264#64) 12 ∗
  memRegion (sp + 0x2a0#64) 16 ∗
  memRegion (sp + 0x2d4#64) 12 ∗
  memRegion (sp + 0x304#64) 12 ∗
  memRegion (sp + 0x334#64) 12 ∗
  memRegion (sp + 0x364#64) 12 ∗
  memRegion (sp + 0x394#64) 12 ∗
  memRegion (sp + 0x3a8#64) 4 ∗
  memRegion (sp + 0x3ad#64) 3

/-- Bidirectional split of `memRegion (sp + 0x234#64) 428` into active Stage P2/P3/P4 stack slots
and `spMidGapsAt sp`. -/
theorem sp_234_428_split (sp : BitVec 64) :
    memRegion (sp + 0x234#64) 428 =
      memRegion (sp + 0x250#64) 20 ∗
      memRegion (sp + 0x270#64) 48 ∗
      memRegion (sp + 0x2b0#64) 36 ∗
      memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗
      memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      memRegion (sp + 0x3a0#64) 8 ∗
      memRegion (sp + 0x3ac#64) 1 ∗
      memRegion (sp + 0x3b0#64) 24 ∗
      memRegion (sp + 0x3c8#64) 24 ∗
      spMidGapsAt sp := by
  unfold spMidGapsAt
  rw [memRegion_split (sp + 0x234#64) 28 400 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64) 20 380 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64) 12 368 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64) 48 320 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64) 16 304 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64) 36 268 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64) 12 256 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64) 36 220 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64) 12 208 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64) 36 172 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64) 12 160 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64) 36 124 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64) 12 112 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64) 36 76 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64) 12 64 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64) 8 56 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 8#64) 4 52 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 8#64 + 4#64) 1 51 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 8#64 + 4#64 + 1#64) 3 48 (by decide),
      memRegion_split (sp + 0x234#64 + 28#64 + 20#64 + 12#64 + 48#64 + 16#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64 + 8#64 + 4#64 + 1#64 + 3#64) 24 24 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Bidirectional splits for `memRegion (sp + 0x3e0#64) 368` (`= 344 + 24`, with `344 = 104 + 240`
for Stage P3 entry and `344 = 48 + 296` for Stage P4). -/
theorem sp_3e0_368_eq_344_24 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 344 ∗ memRegion (sp + 0x538#64) 24 := by
  rw [memRegion_split (sp + 0x3e0#64) 344 24 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem sp_3e0_344_eq_104_240 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 104 ∗ memRegion (sp + 0x448#64) 240 := by
  rw [memRegion_split (sp + 0x3e0#64) 104 240 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem sp_3e0_344_eq_48_296 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 296 := by
  rw [memRegion_split (sp + 0x3e0#64) 48 296 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem sp_270_48_of_p4_slots (sp v270 ptCap ptPtr ptLen : BitVec 64) :
    ((sp + 0x270#64) ↦₆₄ v270) ∗
    ((sp + 0x278#64) ↦₆₄ ptCap) ∗
    ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
    ((sp + 0x288#64) ↦₆₄ ptLen) ∗
    memRegion (sp + 0x290#64) 16 ⊢
      memRegion (sp + 0x270#64) 48 := by
  rw [memRegion_split (sp + 0x270#64) 8 40 (by decide),
      memRegion_split (sp + 0x270#64 + 8#64) 8 32 (by decide),
      memRegion_split (sp + 0x270#64 + 8#64 + 8#64) 8 24 (by decide),
      memRegion_split (sp + 0x270#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ v270)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptCap)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptPtr)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ ptLen)
          (Entails.refl _))))

/-- Universal closure stack-frame exit folding into `memRegion (sp0 - 0xcd0#64) 3280`. -/
theorem clos_stack_3280_of_regions (sp0 : BitVec 64) (s0 : State) :
    let sp := sp0 - 0xcd0#64
    memRegion sp 8 ∗
    memRegion (sp + 0x8#64) 144 ∗
    memRegion (sp + 0x98#64) 8 ∗
    memRegion (sp + 0xa0#64) 8 ∗
    memRegion (sp + 0xa8#64) 8 ∗
    memRegion (sp + 0xb0#64) 8 ∗
    memRegion (sp + 0xb8#64) 8 ∗
    memRegion (sp + 0xc0#64) 8 ∗
    memRegion (sp + 0xc8#64) 8 ∗
    memRegion (sp + 0xd0#64) 8 ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x234#64) 428 ∗
    memRegion (sp + 0x3e0#64) 368 ∗
    memRegion (sp + 0x550#64) 1824 ∗
    decryptPrekeySavedRegsAt sp0 s0 ⊢ memRegion sp 3280 := by
  dsimp only
  let sp := sp0 - 0xcd0#64
  change _ ⊢ memRegion sp 3280
  have hsaved := savedRegs_entails_memRegion_96' sp0 s0
  have h_c70 : sp + 0xc70#64 = sp0 - 0x60#64 := by dsimp only [sp]; bv_omega
  have h64 : memRegion (sp + 0x98#64) 64 =
      memRegion (sp + 0x98#64) 8 ∗ memRegion (sp + 0xa0#64) 8 ∗
      memRegion (sp + 0xa8#64) 8 ∗ memRegion (sp + 0xb0#64) 8 ∗
      memRegion (sp + 0xb8#64) 8 ∗ memRegion (sp + 0xc0#64) 8 ∗
      memRegion (sp + 0xc8#64) 8 ∗ memRegion (sp + 0xd0#64) 8 := by
    rw [memRegion_split (sp + 0x98#64) 8 56 (by decide),
        memRegion_split (sp + 0x98#64 + 8#64) 8 48 (by decide),
        memRegion_split (sp + 0x98#64 + 8#64 + 8#64) 8 40 (by decide),
        memRegion_split (sp + 0x98#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
        memRegion_split (sp + 0x98#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
        memRegion_split (sp + 0x98#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
        memRegion_split (sp + 0x98#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [memRegion_split sp 8 3272 (by decide),
      memRegion_split (sp + 8#64) 144 3128 (by decide),
      memRegion_split (sp + 8#64 + 144#64) 64 3064 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64) 348 2716 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64) 428 2288 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64 + 428#64) 368 1920 (by decide),
      memRegion_split (sp + 8#64 + 144#64 + 64#64 + 348#64 + 428#64 + 368#64) 1824 96 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h_c70, h64]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right hsaved)))))))))))))) ?_
  dsimp only [sp] at *
  sep_frame

/-! ## 4. Stage P2/P3 Entry Spill & Stack Preparation (`+0x0868` and `+0x1778`) -/

/-- A 4-byte read-write `memRegion` is equivalent to an existential `↦₃₂` cell. -/
theorem memRegion_4_eq_exists_pointsTo32 (a : BitVec 64) :
    memRegion a 4 = ∃∗ u : BitVec 32, a ↦₃₂ u := by
  apply Entails.antisymm
  · rw [memRegion_eq_exists_bytes a 4 (by decide)]
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hlen => ?_
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at hlen; done)
    rw [pointsToBytes4_eq_pointsTo32]
    exact Entails.sepExists_right _ (Entails.refl _)
  · exact Entails.sepExists_elim (pointsTo32_entails_memRegion a)

private theorem step_mr8 {a : BitVec 64} {Rest Acc Q : SepProp}
    (h : ∀ u : BitVec 64, Rest ∗ ((a ↦₆₄ u) ∗ Acc) ⊢ Q) :
    (memRegion a 8 ∗ Rest) ∗ Acc ⊢ Q := by
  rw [ProofLib.memRegion_cells a 1 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left]
  exact Entails.sepExists_elim fun u => Entails.trans (by sep_frame) (h u)

private theorem step_mr4 {a : BitVec 64} {Rest Acc Q : SepProp}
    (h : ∀ u : BitVec 32, Rest ∗ ((a ↦₃₂ u) ∗ Acc) ⊢ Q) :
    (memRegion a 4 ∗ Rest) ∗ Acc ⊢ Q := by
  rw [memRegion_4_eq_exists_pointsTo32 a, sepExists_sepConj_left, sepExists_sepConj_left]
  exact Entails.sepExists_elim fun u => Entails.trans (by sep_frame) (h u)

private theorem elim_mr8 {a : BitVec 64} {Acc Q : SepProp}
    (h : ∀ u : BitVec 64, (a ↦₆₄ u) ∗ Acc ⊢ Q) :
    memRegion a 8 ∗ Acc ⊢ Q := by
  rw [ProofLib.memRegion_cells a 1 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left]
  exact Entails.sepExists_elim h

private theorem elim_mr4 {a : BitVec 64} {Acc Q : SepProp}
    (h : ∀ u : BitVec 32, (a ↦₃₂ u) ∗ Acc ⊢ Q) :
    memRegion a 4 ∗ Acc ⊢ Q := by
  rw [memRegion_4_eq_exists_pointsTo32 a, sepExists_sepConj_left]
  exact Entails.sepExists_elim h

/-- Split `memRegion (sp + 0x8#64) 144` into `memRegion (sp + 0x8#64) 120` (untouched across Stage P2)
and the three 8-byte slots `[+0x80, +0x88, +0x90]` used by Stage P2. -/
theorem sp_8_144_split_120_words3 (sp : BitVec 64) :
    memRegion (sp + 0x8#64) 144 =
      ∃∗ u_80 : BitVec 64, ∃∗ u_88 : BitVec 64, ∃∗ u_90 : BitVec 64,
        memRegion (sp + 0x8#64) 120 ∗
        ((sp + 0x80#64) ↦₆₄ u_80) ∗
        ((sp + 0x88#64) ↦₆₄ u_88) ∗
        ((sp + 0x90#64) ↦₆₄ u_90) := by
  rw [memRegion_split (sp + 0x8#64) 120 24 (by decide),
      memRegion_split (sp + 0x8#64 + 120#64) 8 16 (by decide),
      memRegion_split (sp + 0x8#64 + 120#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.antisymm
  · refine Entails.trans (show _ ⊢
      (memRegion (sp + 0x80#64) 8 ∗ memRegion (sp + 0x88#64) 8 ∗ memRegion (sp + 0x90#64) 8) ∗
        memRegion (sp + 0x8#64) 120 by sep_frame) ?_
    refine step_mr8 fun u_80 => step_mr8 fun u_88 => elim_mr8 fun u_90 => ?_
    exact Entails.sepExists_right u_80 (Entails.sepExists_right u_88
      (Entails.sepExists_right u_90 (by sep_frame)))
  · refine Entails.sepExists_elim fun u_80 => Entails.sepExists_elim fun u_88 =>
      Entails.sepExists_elim fun u_90 => ?_
    exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ u_80)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ u_88)
        (ProofLib.pointsTo64_entails_memRegion _ u_90)))

/-- Assemble `genP3SpillAll sp ∗ spLowGapsAt sp` at `+0x1778` from `memRegion (sp + 0x8#64) 120`,
`((sp + 0x98#64) ↦₆₄ v98)`, `((sp + 0xd0#64) ↦₆₄ vd0)`, and `memRegion (sp + 0x930#64) 96`. -/
theorem sp_8_120_to_genP3SpillAll (sp v98 vd0 : BitVec 64) :
    memRegion (sp + 0x8#64) 120 ∗
    ((sp + 0x98#64) ↦₆₄ v98) ∗
    ((sp + 0xd0#64) ↦₆₄ vd0) ∗
    memRegion (sp + 0x930#64) 96 ⊢
      genP3SpillAll sp ∗ spLowGapsAt sp := by
  have h120 : memRegion (sp + 0x8#64) 120 =
      memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 0x10#64) 8 ∗ memRegion (sp + 0x18#64) 8 ∗
      memRegion (sp + 0x20#64) 4 ∗
      memRegion (sp + 0x24#64) 4 ∗ memRegion (sp + 0x28#64) 4 ∗ memRegion (sp + 0x2c#64) 4 ∗
      memRegion (sp + 0x30#64) 4 ∗ memRegion (sp + 0x34#64) 4 ∗
      memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ∗
      memRegion (sp + 0x48#64) 8 ∗ memRegion (sp + 0x50#64) 8 ∗
      memRegion (sp + 0x58#64) 4 ∗ memRegion (sp + 0x5c#64) 4 ∗
      memRegion (sp + 0x60#64) 8 ∗ memRegion (sp + 0x68#64) 8 ∗ memRegion (sp + 0x70#64) 8 ∗
      memRegion (sp + 0x78#64) 4 ∗ memRegion (sp + 0x7c#64) 4 := by
    rw [memRegion_split (sp + 0x8#64) 8 112 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64) 8 104 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64) 8 96 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64) 4 92 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64) 4 88 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64) 4 84 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64) 4 76 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64) 4 72 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 64 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 56 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 8 48 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64) 4 36 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64) 4 32 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 24 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 8 16 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64) 8 8 (by decide),
        memRegion_split (sp + 0x8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64 + 8#64 + 8#64) 4 4 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h96 : memRegion (sp + 0x930#64) 96 =
      memRegion (sp + 0x930#64) 8 ∗ memRegion (sp + 0x938#64) 8 ∗
      memRegion (sp + 0x940#64) 8 ∗ memRegion (sp + 0x948#64) 8 ∗
      memRegion (sp + 0x950#64) 8 ∗ memRegion (sp + 0x958#64) 8 ∗
      memRegion (sp + 0x960#64) 8 ∗ memRegion (sp + 0x968#64) 8 ∗
      memRegion (sp + 0x970#64) 8 ∗ memRegion (sp + 0x978#64) 8 ∗
      memRegion (sp + 0x980#64) 8 ∗ memRegion (sp + 0x988#64) 8 := by
    rw [memRegion_split (sp + 0x930#64) 8 88 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64) 8 80 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64) 8 72 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64) 8 64 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 56 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
        memRegion_split (sp + 0x930#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hPend :
      memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 0x10#64) 8 ∗ memRegion (sp + 0x18#64) 8 ∗
      memRegion (sp + 0x24#64) 4 ∗ memRegion (sp + 0x28#64) 4 ∗ memRegion (sp + 0x2c#64) 4 ⊢
        genP3PendSpillScratch sp := by
    rw [← sepConj_emp (memRegion (sp + 0x8#64) 8 ∗ _)]
    refine step_mr8 fun v08 => step_mr8 fun v10 => step_mr8 fun v18 =>
      step_mr4 fun v24 => step_mr4 fun v28 => elim_mr4 fun v2c => ?_
    exact Entails.sepExists_right ⟨v08, v10, v18, v24, v28, v2c⟩ (by sep_frame)
  have hTail :
      memRegion (sp + 0x30#64) 4 ∗ memRegion (sp + 0x34#64) 4 ∗
      memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ⊢
        genP3TailSpillScratch sp := by
    rw [← sepConj_emp (memRegion (sp + 0x30#64) 4 ∗ _)]
    refine step_mr4 fun u30 => step_mr4 fun u34 => step_mr8 fun u38 => elim_mr8 fun u40 => ?_
    exact Entails.sepExists_right ⟨u30, u34, u38, u40⟩ (by sep_frame)
  have hChains :
      memRegion (sp + 0x60#64) 8 ∗ memRegion (sp + 0x68#64) 8 ∗ memRegion (sp + 0x70#64) 8 ⊢
        genP3ChainsSpillScratch sp := by
    rw [← sepConj_emp (memRegion (sp + 0x60#64) 8 ∗ _)]
    refine step_mr8 fun u60 => step_mr8 fun u68 => elim_mr8 fun u70 => ?_
    exact Entails.sepExists_right ⟨u60, u68, u70⟩ (by sep_frame)
  have hFront :
      (memRegion (sp + 0x48#64) 8 ∗ memRegion (sp + 0x50#64) 8 ∗
        memRegion (sp + 0x5c#64) 4 ∗ memRegion (sp + 0x7c#64) 4 ∗
        memRegion (sp + 0x930#64) 8 ∗ memRegion (sp + 0x938#64) 8 ∗
        memRegion (sp + 0x940#64) 8 ∗ memRegion (sp + 0x948#64) 8 ∗
        memRegion (sp + 0x950#64) 8 ∗ memRegion (sp + 0x958#64) 8 ∗
        memRegion (sp + 0x960#64) 8 ∗ memRegion (sp + 0x968#64) 8 ∗
        memRegion (sp + 0x970#64) 8 ∗ memRegion (sp + 0x978#64) 8 ∗
        memRegion (sp + 0x980#64) 8 ∗ memRegion (sp + 0x988#64) 8) ∗
      (((sp + 0x98#64) ↦₆₄ v98) ∗ ((sp + 0xd0#64) ↦₆₄ vd0)) ⊢
        ∃∗ w : GenP3FrontSpill,
          ((sp + 0x48#64) ↦₆₄ w.u_48) ∗ ((sp + 0x50#64) ↦₆₄ w.u_50) ∗
          ((sp + 0x5c#64) ↦₃₂ w.u_5c) ∗ ((sp + 0x7c#64) ↦₃₂ w.u_7c) ∗
          ((sp + 0x98#64) ↦₆₄ w.u_98) ∗ ((sp + 0xd0#64) ↦₆₄ w.u_d0) ∗
          ((sp + 0x930#64) ↦₆₄ w.u930) ∗ ((sp + 0x938#64) ↦₆₄ w.u938) ∗
          ((sp + 0x940#64) ↦₆₄ w.u940) ∗ ((sp + 0x948#64) ↦₆₄ w.u948) ∗
          ((sp + 0x950#64) ↦₆₄ w.u950) ∗ ((sp + 0x958#64) ↦₆₄ w.u958) ∗
          ((sp + 0x960#64) ↦₆₄ w.u960) ∗ ((sp + 0x968#64) ↦₆₄ w.u968) ∗
          ((sp + 0x970#64) ↦₆₄ w.u970) ∗ ((sp + 0x978#64) ↦₆₄ w.u978) ∗
          ((sp + 0x980#64) ↦₆₄ w.u980) ∗ ((sp + 0x988#64) ↦₆₄ w.u988) := by
    refine step_mr8 fun u48 => step_mr8 fun u50 => step_mr4 fun u5c => step_mr4 fun u7c =>
      step_mr8 fun u930 => step_mr8 fun u938 => step_mr8 fun u940 => step_mr8 fun u948 =>
      step_mr8 fun u950 => step_mr8 fun u958 => step_mr8 fun u960 => step_mr8 fun u968 =>
      step_mr8 fun u970 => step_mr8 fun u978 => step_mr8 fun u980 => elim_mr8 fun u988 => ?_
    exact Entails.sepExists_right
      ⟨u48, u50, u5c, u7c, v98, vd0, u930, u938, u940, u948, u950, u958,
        u960, u968, u970, u978, u980, u988⟩ (by sep_frame)
  rw [h120, h96]
  unfold genP3SpillAll spLowGapsAt
  refine Entails.trans (show _ ⊢
    (memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 0x10#64) 8 ∗ memRegion (sp + 0x18#64) 8 ∗
      memRegion (sp + 0x24#64) 4 ∗ memRegion (sp + 0x28#64) 4 ∗ memRegion (sp + 0x2c#64) 4) ∗
    (memRegion (sp + 0x30#64) 4 ∗ memRegion (sp + 0x34#64) 4 ∗
      memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8) ∗
    (memRegion (sp + 0x60#64) 8 ∗ memRegion (sp + 0x68#64) 8 ∗ memRegion (sp + 0x70#64) 8) ∗
    ((memRegion (sp + 0x48#64) 8 ∗ memRegion (sp + 0x50#64) 8 ∗
        memRegion (sp + 0x5c#64) 4 ∗ memRegion (sp + 0x7c#64) 4 ∗
        memRegion (sp + 0x930#64) 8 ∗ memRegion (sp + 0x938#64) 8 ∗
        memRegion (sp + 0x940#64) 8 ∗ memRegion (sp + 0x948#64) 8 ∗
        memRegion (sp + 0x950#64) 8 ∗ memRegion (sp + 0x958#64) 8 ∗
        memRegion (sp + 0x960#64) 8 ∗ memRegion (sp + 0x968#64) 8 ∗
        memRegion (sp + 0x970#64) 8 ∗ memRegion (sp + 0x978#64) 8 ∗
        memRegion (sp + 0x980#64) 8 ∗ memRegion (sp + 0x988#64) 8) ∗
      (((sp + 0x98#64) ↦₆₄ v98) ∗ ((sp + 0xd0#64) ↦₆₄ vd0))) ∗
    (memRegion (sp + 0x20#64) 4 ∗ memRegion (sp + 0x58#64) 4 ∗ memRegion (sp + 0x78#64) 4)
    by sep_frame) ?_
  refine Entails.trans (sepConj_mono hPend (sepConj_mono hTail (sepConj_mono hChains
    (sepConj_mono_left hFront)))) ?_
  simp only [sepConj_assoc]
  exact Entails.refl _

/-- Bidirectional split of `stackAt sp rootStack` into `stackAt sp chainCloneStack` + bottom
extension (for Stage P3 entry) and `stackAt sp growOneSpeStack` + bottom extension (for Stage P3 exit). -/
theorem stackAt_root_eq_chainClone (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
      stackAt sp chainCloneStack :=
  ProofLib.stackAt_split_bottom sp chainCloneStack (rootStack - chainCloneStack) (by decide)

theorem stackAt_root_eq_growOneSpe (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      stackAt sp growOneSpeStack :=
  ProofLib.stackAt_split_bottom sp growOneSpeStack (rootStack - growOneSpeStack) (by decide)

/-! ## 5. Account Distinctness for `StageP3GenStmt` -/

/-- Discharges `StageP3GenStmt`'s `Or.inr` account-distinctness hypothesis
`DistinctSid uuidTryParse loc.name.bytes rem.name.bytes` from `DecPkOk₀.distinctAcct`. -/
theorem distinctSid_of_decPkOk {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {rem loc : AddrGhost} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F rem.val loc.val pm) :
    DistinctSid uuidTryParse loc.name.bytes rem.name.bytes := by
  intro sid hloc hrem
  exact hd.distinctAcct ⟨sid, hrem, hloc⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
