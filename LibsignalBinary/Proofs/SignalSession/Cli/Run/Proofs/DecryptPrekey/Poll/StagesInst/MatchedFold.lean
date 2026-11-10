/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPre
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Bridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Poll Path B Stage P2 Exit and Continuation Folds

Proves `matched_mismatch_fold` (folding `stageP2MatchedMismatchPost` into the `hmismatch`
postcondition of `StageP2MatchedFramedCliStmt`) and `matched_match_fold` (folding
`stageP2MatchedMatchPre` into `genP3Pre` and Stage P3 coroutine/stack frames).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSpqrV1
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

set_option linter.unusedSimpArgs false

theorem pts64_mr {a v : BitVec 64} {P Q : SepProp} (h : P ⊢ Q) :
    (a ↦₆₄ v) ∗ P ⊢ memRegion a 8 ∗ Q :=
  sepConj_mono (ProofLib.pointsTo64_entails_memRegion a v) h

theorem pts32_mr {a : BitVec 64} {v : BitVec 32} {P Q : SepProp} (h : P ⊢ Q) :
    (a ↦₃₂ v) ∗ P ⊢ memRegion a 4 ∗ Q :=
  sepConj_mono (pointsTo32_entails_memRegion a v) h

theorem words3_off_mr (sp off a1 a2 w0 w1 w2 : BitVec 64)
    (h1 : off + 0x8#64 = a1 := by rfl) (h2 : off + 0x10#64 = a2 := by rfl) :
    ((sp + off) ↦₆₄ w0) ∗ ((sp + a1) ↦₆₄ w1) ∗ ((sp + a2) ↦₆₄ w2) ⊢ memRegion (sp + off) 24 := by
  subst h1; subst h2
  simpa only [BitVec.add_assoc] using words3_entails_memRegion24 (sp + off) w0 w1 w2

/-! ## 1. Shared Coroutine Fold Helpers -/

theorem active10_3a8_488_fold (fut msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt : BitVec 64) :
    processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt ∗
    memRegion (fut + 0x3a8#64) 80 ∗
    memRegion (fut + 0x488#64) 8 ⊢
    memRegion (fut + 0x3a8#64) 128 ∗ memRegion (fut + 0x468#64) 40 := by
  rw [Matched.processPrekeyActive10At_eq]
  have h48 :
      ((fut + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((fut + 0x400#64) ↦₆₄ kyberStoreVt) ∗
      ((fut + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((fut + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
      ((fut + 0x418#64) ↦₆₄ idStorePtr) ∗ ((fut + 0x420#64) ↦₆₄ idStoreVt) ⊢
      memRegion (fut + 0x3f8#64) 48 := by
    rw [memRegion_split (fut + 0x3f8#64) 8 40 (by decide),
        memRegion_split (fut + 0x3f8#64 + 8#64) 8 32 (by decide),
        memRegion_split (fut + 0x3f8#64 + 8#64 + 8#64) 8 24 (by decide),
        memRegion_split (fut + 0x3f8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
        memRegion_split (fut + 0x3f8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact pts64_mr (pts64_mr (pts64_mr (pts64_mr (pts64_mr
      (ProofLib.pointsTo64_entails_memRegion _ _)))))
  have h32 :
      ((fut + 0x468#64) ↦₆₄ msgPtr) ∗ ((fut + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((fut + 0x480#64) ↦₆₄ (fut + 0xe0#64)) ⊢
      memRegion (fut + 0x468#64) 32 := by
    rw [memRegion_split (fut + 0x468#64) 8 24 (by decide),
        memRegion_split (fut + 0x468#64 + 8#64) 8 16 (by decide),
        memRegion_split (fut + 0x468#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact pts64_mr (pts64_mr (pts64_mr (ProofLib.pointsTo64_entails_memRegion _ _)))
  have h128 : memRegion (fut + 0x3a8#64) 80 ∗ memRegion (fut + 0x3f8#64) 48 =
      memRegion (fut + 0x3a8#64) 128 := by
    rw [memRegion_split (fut + 0x3a8#64) 80 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h40 : memRegion (fut + 0x468#64) 32 ∗ memRegion (fut + 0x488#64) 8 =
      memRegion (fut + 0x468#64) 40 := by
    rw [memRegion_split (fut + 0x468#64) 32 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [← h128, ← h40]
  refine Entails.trans (show _ ⊢
    memRegion (fut + 0x3a8#64) 80 ∗
    (((fut + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((fut + 0x400#64) ↦₆₄ kyberStoreVt) ∗
      ((fut + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((fut + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
      ((fut + 0x418#64) ↦₆₄ idStorePtr) ∗ ((fut + 0x420#64) ↦₆₄ idStoreVt)) ∗
    (((fut + 0x468#64) ↦₆₄ msgPtr) ∗ ((fut + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((fut + 0x480#64) ↦₆₄ (fut + 0xe0#64))) ∗
    memRegion (fut + 0x488#64) 8 by sep_frame) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono h48 (sepConj_mono_left h32))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem innerInit_200_fold (fut msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64) :
    ((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
    ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
    processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ⊢
    memRegion (fut + 0x2c8#64) 200 := by
  rw [ProofLib.memRegion_cells (fut + 0x2c8#64) 25 (by decide),
      ← processPrekeyInnerInitAt_eq_330_388_rem23]
  exact processPrekeyInnerInitAt_entails_cells25
    fut msgPtr remoteAddrPtr localAddrPtr idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt

theorem postTrust_64_32_fold (fut msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64) :
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt ⊢
    memRegion (fut + 0x428#64) 64 ∗ memRegion (fut + 0x490#64) 32 := by
  unfold processPrekeyPostTrustAt
  have h64 :
      ((fut + 0x428#64) ↦₆₄ spkStorePtr) ∗ ((fut + 0x430#64) ↦₆₄ spkStoreVt) ∗
      ((fut + 0x438#64) ↦₆₄ kyberStorePtr) ∗ ((fut + 0x440#64) ↦₆₄ kyberStoreVt) ∗
      ((fut + 0x448#64) ↦₆₄ preKeyStorePtr) ∗ ((fut + 0x450#64) ↦₆₄ preKeyStoreVt) ∗
      ((fut + 0x458#64) ↦₆₄ idStorePtr) ∗ ((fut + 0x460#64) ↦₆₄ idStoreVt) ⊢
      memRegion (fut + 0x428#64) 64 := by
    rw [memRegion_split (fut + 0x428#64) 8 56 (by decide),
        memRegion_split (fut + 0x428#64 + 8#64) 8 48 (by decide),
        memRegion_split (fut + 0x428#64 + 8#64 + 8#64) 8 40 (by decide),
        memRegion_split (fut + 0x428#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
        memRegion_split (fut + 0x428#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
        memRegion_split (fut + 0x428#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
        memRegion_split (fut + 0x428#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact pts64_mr (pts64_mr (pts64_mr (pts64_mr (pts64_mr (pts64_mr (pts64_mr
      (ProofLib.pointsTo64_entails_memRegion _ _)))))))
  have h32 :
      ((fut + 0x490#64) ↦₆₄ msgPtr) ∗ ((fut + 0x498#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x4a0#64) ↦₆₄ localAddrPtr) ∗ ((fut + 0x4a8#64) ↦₆₄ (fut + 0xe0#64)) ⊢
      memRegion (fut + 0x490#64) 32 := by
    rw [memRegion_split (fut + 0x490#64) 8 24 (by decide),
        memRegion_split (fut + 0x490#64 + 8#64) 8 16 (by decide),
        memRegion_split (fut + 0x490#64 + 8#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact pts64_mr (pts64_mr (pts64_mr (ProofLib.pointsTo64_entails_memRegion _ _)))
  refine Entails.trans (show _ ⊢
    (((fut + 0x428#64) ↦₆₄ spkStorePtr) ∗ ((fut + 0x430#64) ↦₆₄ spkStoreVt) ∗
      ((fut + 0x438#64) ↦₆₄ kyberStorePtr) ∗ ((fut + 0x440#64) ↦₆₄ kyberStoreVt) ∗
      ((fut + 0x448#64) ↦₆₄ preKeyStorePtr) ∗ ((fut + 0x450#64) ↦₆₄ preKeyStoreVt) ∗
      ((fut + 0x458#64) ↦₆₄ idStorePtr) ∗ ((fut + 0x460#64) ↦₆₄ idStoreVt)) ∗
    (((fut + 0x490#64) ↦₆₄ msgPtr) ∗ ((fut + 0x498#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x4a0#64) ↦₆₄ localAddrPtr) ∗ ((fut + 0x4a8#64) ↦₆₄ (fut + 0xe0#64)))
    by sep_frame) (sepConj_mono h64 h32)

/-! ## 2. Mismatch Exit Fold (`matched_mismatch_fold`) -/

theorem coro_mismatch_fold (fut msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr u_298 u_2a0 : BitVec 64)
    (u_2a8 : BitVec 32) :
    processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
    decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
    ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
    coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    memRegion (fut + 0xe0#64) 368 ∗ cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x280#64) 24 ∗
    ((fut + 0x298#64) ↦₆₄ u_298) ∗ ((fut + 0x2a0#64) ↦₆₄ u_2a0) ∗ ((fut + 0x2a8#64) ↦₃₂ u_2a8) ∗
    memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
    ((fut + 0x2c0#64) ↦₈ 1#8) ∗
    ((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗ ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
    processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    ((fut + 0x390#64) ↦₈ 1#8) ∗ cells (fut + 0x398#64) 2 ∗
    ((fut + 0x4f1#64) ↦₈ 0#8) ∗ ((fut + 0x4f2#64) ↦₈ 1#8) ∗
    memRegion (fut + 0x2c1#64) 7 ∗ memRegion (fut + 0x391#64) 7 ∗
    memRegion (fut + 0x3a8#64) 80 ∗ memRegion (fut + 0x488#64) 8 ∗
    memRegion (fut + 0x4b0#64) 65 ∗ memRegion (fut + 0x4f3#64) 5 ∗
    memRegion (fut + 0x4f8#64) 736 ⊢ dpFutDoneAt fut := by
  have hcopy :
      ((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
      coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt rngPtr ⊢ memRegion (fut + 0x70#64) 112 := by
    rw [← coroCopyAt_eq_head3_tail11]
    exact coroCopy_entails_memRegion_112 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have h4b0 : memRegion (fut + 0x4b0#64) 65 ∗ ((fut + 0x4f1#64) ↦₈ 0#8) ⊢
      memRegion (fut + 0x4b0#64) 66 := by
    rw [memRegion_split (fut + 0x4b0#64) 65 1 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (ProofLib.pointsTo8_entails_memRegion _ _)
  have he0 : memRegion (fut + 0xe0#64) 368 =
      memRegion (fut + 0xe0#64) 24 ∗ memRegion (fut + 0xf8#64) 344 := by
    rw [memRegion_split (fut + 0xe0#64) 24 344 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [he0]
  have hc := coro_regions_entails_dpFutDoneAt fut
  unfold coroPostP2UnusedAt at hc
  have h250 : memRegion (fut + 0x250#64) 48 = cells (fut + 0x250#64) 6 :=
    ProofLib.memRegion_cells (fut + 0x250#64) 6 (by decide)
  have h398 : memRegion (fut + 0x398#64) 16 = cells (fut + 0x398#64) 2 :=
    ProofLib.memRegion_cells (fut + 0x398#64) 2 (by decide)
  rw [coro_2ac_20_eq_8_12 fut, h250, h398] at hc
  refine Entails.trans ?_ hc
  refine Entails.trans (show _ ⊢
    decryptPrekeyCoroInitAt fut msgPtr remoteAddrPtr localAddrPtr
      sessStorePtr sessStoreVt idStorePtr idStoreVt
      preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr ∗
    (((fut + 0x70#64) ↦₆₄ msgPtr) ∗ ((fut + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
      ((fut + 0x80#64) ↦₆₄ localAddrPtr) ∗
      coroCopyTail11At fut sessStorePtr sessStoreVt idStorePtr idStoreVt
        preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt rngPtr) ∗
    (processPrekeyActive10At fut msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
      memRegion (fut + 0x3a8#64) 80 ∗ memRegion (fut + 0x488#64) 8) ∗
    (((fut + 0x330#64) ↦₆₄ remoteAddrPtr) ∗ ((fut + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64)) ∗
      processPrekeyInnerRem23At fut msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
        kyberStorePtr kyberStoreVt) ∗
    processPrekeyPostTrustAt fut msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
      kyberStorePtr kyberStoreVt ∗
    (memRegion (fut + 0x4b0#64) 65 ∗ ((fut + 0x4f1#64) ↦₈ 0#8)) ∗
    ((fut + 0x298#64) ↦₆₄ u_298) ∗ ((fut + 0x2a0#64) ↦₆₄ u_2a0) ∗
    ((fut + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((fut + 0x390#64) ↦₈ 1#8) ∗ ((fut + 0x4f2#64) ↦₈ 1#8) ∗
    (memRegion (fut + 0xe0#64) 24 ∗ memRegion (fut + 0xf8#64) 344 ∗
      cells (fut + 0x250#64) 6 ∗ memRegion (fut + 0x280#64) 24 ∗
      memRegion (fut + 0x2ac#64) 8 ∗ memRegion (fut + 0x2b4#64) 12 ∗
      ((fut + 0x2c0#64) ↦₈ 1#8) ∗ cells (fut + 0x398#64) 2 ∗
      memRegion (fut + 0x2c1#64) 7 ∗ memRegion (fut + 0x391#64) 7 ∗
      memRegion (fut + 0x4f3#64) 5 ∗ memRegion (fut + 0x4f8#64) 736) by sep_frame) ?_
  refine Entails.trans (sepConj_mono (coroInit_entails_memRegion_112 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (sepConj_mono hcopy (sepConj_mono (active10_3a8_488_fold _ _ _ _ _ _ _ _ _ _)
      (sepConj_mono (innerInit_200_fold _ _ _ _ _ _ _ _ _ _ _ _)
        (sepConj_mono (postTrust_64_32_fold _ _ _ _ _ _ _ _ _ _ _ _)
          (sepConj_mono h4b0 (pts64_mr (pts64_mr (pts32_mr
            (sepConj_mono (ProofLib.pointsTo8_entails_memRegion _ _)
              (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)))))))))))) ?_
  sep_frame

theorem stack_mismatch_fold (s0 : State) (sp fut cx out
    u_80 u_88 u_90 u_b0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_b8 : BitVec 32) (b_3ac : BitVec 8) :
    (sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
    ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x90#64) ↦₆₄ u_90) ∗
    ((sp + 0x98#64) ↦₆₄ (fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (fut + 0x4f2#64)) ∗
    ((sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    ((sp + 0xb8#64) ↦₃₂ u_b8) ∗ memRegion (sp + 0xbc#64) 4 ∗
    ((sp + 0xc0#64) ↦₆₄ cx) ∗ ((sp + 0xc8#64) ↦₆₄ out) ∗ ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
    memRegion (sp + 0xd8#64) 348 ∗
    memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 48 ∗
    memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
    memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
    memRegion (sp + 0x370#64) 36 ∗
    ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
    ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗ ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
    ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
    spMidGapsAt sp ∗
    memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
    memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 ∗
    memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
    memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
    memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 ∗
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ⊢ memRegion sp 3280 := by
  have h144 :
      memRegion (sp + 0x8#64) 120 ∗
      (((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x90#64) ↦₆₄ u_90)) ⊢
      memRegion (sp + 0x8#64) 144 := by
    rw [memRegion_split (sp + 0x8#64) 120 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_right (words3_off_mr sp 0x80#64 0x88#64 0x90#64 _ _ _)
  have hb8 := sp_b8_32_bc_4_entails_memRegion8 sp u_b8
  have h234 :
      memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 48 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
      (((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗ ((sp + 0x3c0#64) ↦₆₄ u_3c0)) ∗
      (((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8)) ∗
      spMidGapsAt sp ⊢ memRegion (sp + 0x234#64) 428 := by
    rw [sp_234_428_split sp]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (pts64_mr (sepConj_mono (ProofLib.pointsTo8_entails_memRegion _ _)
          (sepConj_mono (words3_off_mr sp 0x3b0#64 0x3b8#64 0x3c0#64 _ _ _)
            (sepConj_mono_left (words3_off_mr sp 0x3c8#64 0x3d0#64 0x3d8#64 _ _ _)))))))))))
  have h3e0 :
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 =
      memRegion (sp + 0x3e0#64) 368 := by
    rw [sp_3e0_368_eq_344_24 sp, sp_3e0_344_eq_104_240 sp,
        memRegion_split (sp + 0x3e0#64) 34 70 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have h550 :
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 =
      memRegion (sp + 0x550#64) 1824 := by
    rw [sp_550_1824_split_genP3 sp]
    unfold spHighGapsAt
    rw [memRegion_split (sp + 0xa90#64) 48 296 (by decide),
        memRegion_split (sp + 0x550#64) 976 16 (by decide),
        memRegion_split (sp + 0x550#64 + 976#64) 6 10 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  have hclos := clos_stack_3280_of_regions (sp + 0xcd0#64) s0
  have hsp_sub : sp + 0xcd0#64 - 0xcd0#64 = sp := by bv_omega
  dsimp only at hclos
  rw [hsp_sub] at hclos
  refine Entails.trans ?_ hclos
  rw [← h3e0, ← h550]
  refine Entails.trans (show _ ⊢
    (sp ↦₆₄ 0#64) ∗
    (memRegion (sp + 0x8#64) 120 ∗
      (((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x90#64) ↦₆₄ u_90))) ∗
    ((sp + 0x98#64) ↦₆₄ (fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (fut + 0x4f2#64)) ∗
    ((sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
    (((sp + 0xb8#64) ↦₃₂ u_b8) ∗ memRegion (sp + 0xbc#64) 4) ∗
    ((sp + 0xc0#64) ↦₆₄ cx) ∗ ((sp + 0xc8#64) ↦₆₄ out) ∗ ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
    (memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 48 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
      (((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗ ((sp + 0x3c0#64) ↦₆₄ u_3c0)) ∗
      (((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8)) ∗
      spMidGapsAt sp) ∗
    (memRegion (sp + 0xd8#64) 348 ∗
      (memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
        memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24) ∗
      (memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
        memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
        memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136) ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by sep_frame) ?_
  refine Entails.trans (pts64_mr (sepConj_mono h144
    (pts64_mr (pts64_mr (pts64_mr (pts64_mr
      (sepConj_mono hb8 (pts64_mr (pts64_mr (pts64_mr
        (sepConj_mono_left h234))))))))))) ?_
  sep_frame

theorem matched_mismatch_fold_ext {A : RustAlloc} {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 : State) (sp rngPtr : BitVec 64) (u_b8 : BitVec 32) (w : MatchedEntryWords) :
    stageP2MatchedMismatchPost A img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x78#64) (kyberVt img)
      y.g.peerA (y.g.msgA + 0xc8#64)
      w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
      w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
      w.u_2a8 u_b8 y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
      y.g.msg.baseKey y.g.msg.identityKey
      (matchedInnerFrameExt img y rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      apiDecResultAt A y.out
        (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗
      logOff img ∗
      A.pool ∗
      stackAt sp rootStack := by
  dsimp only [stageP2MatchedMismatchPost, matchedInnerFrameExt]
  have hcoro := coro_mismatch_fold y.fut y.g.msgA y.g.peerA y.g.meA
    (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
    (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
    (y.g.stores + 0x78#64) (kyberVt img) rngPtr w.u_298 w.u_2a0 w.u_2a8
  have hstk := stack_mismatch_fold s0 sp y.fut y.cx y.out
    w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
    w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8 u_b8 w.b_3ac
  rw [preKeyMsgAt_eq_base_idKey_sep, signalMessageAt_eq_ver_sep, preKeyMsgRemBaseIdKeyAt_eq_ver_sep]
  refine Entails.trans (show _ ⊢
    (processPrekeyActive10At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x78#64) (kyberVt img) ∗
      decryptPrekeyCoroInitAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      ((y.fut + 0x70#64) ↦₆₄ y.g.msgA) ∗ ((y.fut + 0x78#64) ↦₆₄ y.g.peerA) ∗
      ((y.fut + 0x80#64) ↦₆₄ y.g.meA) ∗
      coroCopyTail11At y.fut (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr ∗
      memRegion (y.fut + 0xe0#64) 368 ∗ cells (y.fut + 0x250#64) 6 ∗ memRegion (y.fut + 0x280#64) 24 ∗
      ((y.fut + 0x298#64) ↦₆₄ w.u_298) ∗ ((y.fut + 0x2a0#64) ↦₆₄ w.u_2a0) ∗
      ((y.fut + 0x2a8#64) ↦₃₂ w.u_2a8) ∗
      memRegion (y.fut + 0x2ac#64) 8 ∗ memRegion (y.fut + 0x2b4#64) 12 ∗
      ((y.fut + 0x2c0#64) ↦₈ 1#8) ∗
      ((y.fut + 0x330#64) ↦₆₄ y.g.peerA) ∗ ((y.fut + 0x388#64) ↦₆₄ (y.g.msgA + 0xc8#64)) ∗
      processPrekeyInnerRem23At y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      processPrekeyPostTrustAt y.fut y.g.msgA y.g.peerA y.g.meA
        y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
        (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img) ∗
      ((y.fut + 0x390#64) ↦₈ 1#8) ∗ cells (y.fut + 0x398#64) 2 ∗
      ((y.fut + 0x4f1#64) ↦₈ 0#8) ∗ ((y.fut + 0x4f2#64) ↦₈ 1#8) ∗
      memRegion (y.fut + 0x2c1#64) 7 ∗ memRegion (y.fut + 0x391#64) 7 ∗
      memRegion (y.fut + 0x3a8#64) 80 ∗ memRegion (y.fut + 0x488#64) 8 ∗
      memRegion (y.fut + 0x4b0#64) 65 ∗ memRegion (y.fut + 0x4f3#64) 5 ∗
      memRegion (y.fut + 0x4f8#64) 736) ∗
    ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 0x8#64) 120 ∗
      ((sp + 0x80#64) ↦₆₄ w.u_80) ∗ ((sp + 0x88#64) ↦₆₄ w.u_88) ∗ ((sp + 0x90#64) ↦₆₄ w.u_90) ∗
      ((sp + 0x98#64) ↦₆₄ (y.fut + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (y.fut + 0x4f2#64)) ∗
      ((sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((sp + 0xb0#64) ↦₆₄ (y.fut + 0x390#64)) ∗
      ((sp + 0xb8#64) ↦₃₂ u_b8) ∗ memRegion (sp + 0xbc#64) 4 ∗
      ((sp + 0xc0#64) ↦₆₄ y.cx) ∗ ((sp + 0xc8#64) ↦₆₄ y.out) ∗ ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x270#64) 48 ∗
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗
      memRegion (sp + 0x370#64) 36 ∗
      ((sp + 0x3a0#64) ↦₆₄ w.u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ w.b_3ac) ∗
      ((sp + 0x3b0#64) ↦₆₄ w.u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ w.u_3b8) ∗ ((sp + 0x3c0#64) ↦₆₄ w.u_3c0) ∗
      ((sp + 0x3c8#64) ↦₆₄ w.u_3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ w.u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ w.u_3d8) ∗
      spMidGapsAt sp ∗
      memRegion (sp + 0x3e0#64) 34 ∗ memRegion (sp + 0x402#64) 70 ∗
      memRegion (sp + 0x448#64) 240 ∗ memRegion (sp + 0x538#64) 24 ∗
      memRegion (sp + 0x550#64) 976 ∗ memRegion (sp + 0x920#64) 6 ∗ memRegion (sp + 0x926#64) 10 ∗
      memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 256 ∗
      memRegion (sp + 0xa90#64) 48 ∗ memRegion (sp + 0xac0#64) 296 ∗ memRegion (sp + 0xbe8#64) 136 ∗
      decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) ∗
    (apiDecResultAt A y.out
        (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
      ((y.g.msgA + 0x70#64) ↦₈ y.g.msg.message.messageVersion) ∗
      signalMessageRestVerAt A y.g.msgG.msg y.g.msgA y.g.msg.message ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      ((y.g.msgA + 0xf0#64) ↦₈ y.g.msg.messageVersion) ∗
      preKeyMsgRemMatchedAt A y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗
      logOff img ∗
      A.pool ∗
      stackAt sp rootStack) by sep_frame) ?_
  refine Entails.trans (sepConj_mono hcoro (sepConj_mono_left hstk)) ?_
  sep_frame

theorem matched_mismatch_fold {B : RunBudgets} {S : RunSem}
    (img : Obj.Image) (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 : State) (sp rngPtr : BitVec 64) (u_b8 : BitVec 32) (w : MatchedEntryWords) :
    stageP2MatchedMismatchPost E2E.HooksE.A0 img s0 sp y.fut y.out y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x78#64) (kyberVt img)
      y.g.peerA (y.g.msgA + 0xc8#64)
      w.u_80 w.u_88 w.u_90 (y.fut + 0x390#64)
      w.u_298 w.u_2a0 w.u_3a0 w.u_3b0 w.u_3b8 w.u_3c0 w.u_3c8 w.u_3d0 w.u_3d8
      w.u_2a8 u_b8 y.g.msg.messageVersion y.g.msg.message.messageVersion w.b_3ac
      y.g.msg.baseKey y.g.msg.identityKey
      (matchedInnerFrame img y rngPtr sp) ⊢
      dpFutDoneAt y.fut ∗
      memRegion sp 3280 ∗
      apiDecResultAt E2E.HooksE.A0 y.out
        (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      coinsInstalled img y.g.coinsP y.g.coins ∗
      TokenInit img ∗
      logOff img ∗
      E2E.HooksE.A0.pool ∗
      stackAt sp rootStack :=
  matched_mismatch_fold_ext img y s0 sp rngPtr u_b8 w

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
