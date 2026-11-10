/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExitFold
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrace -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2Defs -- shake: keep

/-!
# Poll Stage P3 and Stage P4 Spatial Folds

Spatial bridge lemmas connecting Stage P3 error exits (`stageP3ErrPost` /
`stageP3ErrPostPrevEmpty`), Stage P3 `Ok` mid-states at `+0x34dc`, and Stage P4 exit frames
(`Kits.stageP4ExitAt` and `stageP4MatchedExitAt`) to `dpFutDoneAt` and `memRegion s.sp 3280`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
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

/-- Split `stackAt sp rootStack` into any sub-budget `n ≤ rootStack` plus its bottom gap. -/
theorem stackAt_root_sub_eq (sp : BitVec 64) {n : Nat} (hle : n ≤ rootStack) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - n) ∗
      stackAt sp n :=
  P3P4.stackAt_sub_eq sp rootStack n hle (by unfold rootStack; decide)

/-- `stageP4ErrUnwindStack` fits inside `dpClosSubStack B`. -/
theorem stageP4ErrUnwindStack_le_subStack (B : RunBudgets) :
    stageP4ErrUnwindStack ≤ dpClosSubStack B := by
  have h : stageP4ErrUnwindStack ≤ 1048576 - 3280 := by decide
  exact Nat.le_trans h (Nat.le_add_right _ _)

/-- Path A 4-kit `stageP4CallStack` fits inside `dpClosSubStack B`. -/
theorem cliPollStageP4Stack_le_subStack (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (pid kid ksid : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP4CallStack
      (cliPollSessKit A b F0 Scope peer (cliKitStk B))
      (cliPollIdKit A b F0 peer (cliKitStk B))
      (cliPollPkKit A b F0 pid (cliKitStk B))
      (cliPollKpkKit A b F0 kid ksid kbk (cliKitStk B)) ≤ dpClosSubStack B := by
  have hAll := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hAll
  rcases hAll with ⟨_, _, hsS, hsP, _, _, hiS, hiP, _, _, _, _,
    _, _, hpS, hpP, _, _, _, _, hkS, hkP⟩
  have hErr := stageP4ErrUnwindStack_le_subStack B
  dsimp only [stageP4CallStack, saveIdCallStack, markKyberCallStack,
    removePreKeyCallStack, storeSessionCallStack,
    cliPollSessKit, cliSessionStoreSpec,
    cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec,
    cliPollPkKit, cliPreKeyStoreSpec,
    cliPollKpkKit, cliKpkStoreSpecFull]
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hiS, Nat.max_le.mpr ⟨hiP, hErr⟩⟩,
     Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hkS, Nat.max_le.mpr ⟨hkP, hErr⟩⟩,
       Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨hpS, Nat.max_le.mpr ⟨hpP, hErr⟩⟩,
         Nat.max_le.mpr ⟨hsS, Nat.max_le.mpr ⟨hsP, hErr⟩⟩⟩⟩⟩

/-- Path B 2-kit `max (saveIdCallStack ikit) (storeSessionCallStack kit)` fits inside
`dpClosSubStack B`. -/
theorem cliPollStageP4MatchedStack_le_subStack (A : RustAlloc) (b : BitVec 64) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (B : RunBudgets) :
    max
      (saveIdCallStack (cliPollIdKit A b F0 peer (cliKitStk B)))
      (storeSessionCallStack (cliPollSessKit A b F0 Scope peer (cliKitStk B))) ≤
      dpClosSubStack B := by
  have hAll := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hAll
  rcases hAll with ⟨_, _, hsS, hsP, _, _, hiS, hiP, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _⟩
  have hErr := stageP4ErrUnwindStack_le_subStack B
  dsimp only [saveIdCallStack, storeSessionCallStack,
    cliPollSessKit, cliSessionStoreSpec,
    cliPollIdKit, cliIdStoreSpecFull, cliIdentityStoreSpec]
  exact Nat.max_le.mpr
    ⟨Nat.max_le.mpr ⟨hiS, Nat.max_le.mpr ⟨hiP, hErr⟩⟩,
     Nat.max_le.mpr ⟨hsS, Nat.max_le.mpr ⟨hsP, hErr⟩⟩⟩

/-- Collapse the existential `errs` triple at `sp + 0x3c8..0x3e0` into `memRegion (sp + 0x3c8#64) 24`. -/
theorem sp_3c8_exists_entails_memRegion24 (sp : BitVec 64) :
    (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
      ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗
      ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((sp + 0x3d8#64) ↦₆₄ errsLen)) ⊢
      memRegion (sp + 0x3c8#64) 24 := by
  refine Entails.sepExists_elim fun c =>
    Entails.sepExists_elim fun p =>
    Entails.sepExists_elim fun l => ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    words3_entails_memRegion24 (sp + 0x3c8#64) c p l

/-- Collapse `((coroPtr + 0x2a0#64) ↦₆₄ w) ∗ ((coroPtr + 0x2a8#64) ↦₃₂ s)` into
`memRegion (coroPtr + 0x2a0#64) 8 ∗ memRegion (coroPtr + 0x2a8#64) 4`. -/
theorem coro_2a0_2a8_entails (coroPtr w : BitVec 64) (s : BitVec 32) :
    ((coroPtr + 0x2a0#64) ↦₆₄ w) ∗ ((coroPtr + 0x2a8#64) ↦₃₂ s) ⊢
      memRegion (coroPtr + 0x2a0#64) 8 ∗ memRegion (coroPtr + 0x2a8#64) 4 :=
  sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ w) (pointsTo32_entails_memRegion _ s)

/-- Join the 13 contiguous stack sub-regions covering `[sp + 0xd8.. sp + 0x3e0)` (`776 = 348 + 428`
bytes) into `memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x234#64) 428`. -/
theorem sp_d8_to_3e0_join (sp : BitVec 64) :
    memRegion (sp + 0xd8#64) 376 ∗
    memRegion (sp + 0x250#64) 20 ∗
    memRegion (sp + 0x264#64) 12 ∗
    memRegion (sp + 0x270#64) 48 ∗
    memRegion (sp + 0x2a0#64) 16 ∗
    memRegion (sp + 0x2b0#64) 192 ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x394#64) 12 ∗
    memRegion (sp + 0x3a0#64) 8 ∗
    memRegion (sp + 0x3a8#64) 4 ∗
    memRegion (sp + 0x3ac#64) 1 ∗
    memRegion (sp + 0x3ad#64) 27 ∗
    memRegion (sp + 0x3c8#64) 24 =
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x234#64) 428 := by
  have h376 : memRegion (sp + 0xd8#64) 376 =
      memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x234#64) 28 := by
    rw [memRegion_split (sp + 0xd8#64) 348 28 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h192 : memRegion (sp + 0x2b0#64) 192 =
      memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2d4#64) 12 ∗
      memRegion (sp + 0x2e0#64) 36 ∗ memRegion (sp + 0x304#64) 12 ∗
      memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x334#64) 12 ∗
      memRegion (sp + 0x340#64) 36 ∗ memRegion (sp + 0x364#64) 12 := by
    rw [memRegion_split (sp + 0x2b0#64) 36 156 (by decide),
        memRegion_split (sp + 0x2b0#64 + 36#64) 12 144 (by decide),
        memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64) 36 108 (by decide),
        memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64) 12 96 (by decide),
        memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64 + 12#64) 36 60 (by decide),
        memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64) 12 48 (by decide),
        memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64) 36 12 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h27 : memRegion (sp + 0x3ad#64) 27 =
      memRegion (sp + 0x3ad#64) 3 ∗ memRegion (sp + 0x3b0#64) 24 := by
    rw [memRegion_split (sp + 0x3ad#64) 3 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h376, h192, h27, sp_234_428_split sp]
  unfold spMidGapsAt
  apply Entails.antisymm <;> sep_frame

/-- Split `stackAt sp (dpClosSubStack B)` into any sub-budget `n ≤ dpClosSubStack B` plus its
bottom extension. -/
theorem stackAt_subStack_sub_eq (sp : BitVec 64) (B : RunBudgets) {n : Nat}
    (hle : n ≤ dpClosSubStack B) (hsp : dpClosSubStack B ≤ sp.toNat) :
    stackAt sp (dpClosSubStack B) =
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - n) ∗
      stackAt sp n :=
  P3P4.stackAt_sub_eq sp (dpClosSubStack B) n hle (Nat.le_of_lt (Nat.lt_of_le_of_lt hsp sp.isLt))

/-- Bidirectional split of `decryptPrekeyCoroCopyAt` (`[coroPtr + 0x70.. +0xe0)`) into the 10 words
used by `Kits.stageP4Shared` and the 4 caller-preserved words (`+0x80`, `+0xb8`, `+0xc0`, `+0xd8`). -/
def coroCopyRemP4At (fut meA spkPtr spkVt rng : BitVec 64) : SepProp :=
  ((fut + 0x80#64) ↦₆₄ meA) ∗
  ((fut + 0xb8#64) ↦₆₄ spkPtr) ∗
  ((fut + 0xc0#64) ↦₆₄ spkVt) ∗
  ((fut + 0xd8#64) ↦₆₄ rng)

theorem coroCopy_eq_p4_sep
    (fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng : BitVec 64) :
    decryptPrekeyCoroCopyAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng =
      (((fut + 0x70#64) ↦₆₄ msgA) ∗
       ((fut + 0x78#64) ↦₆₄ peerA) ∗
       ((fut + 0x88#64) ↦₆₄ sPtr) ∗
       ((fut + 0x90#64) ↦₆₄ sVt) ∗
       ((fut + 0x98#64) ↦₆₄ iPtr) ∗
       ((fut + 0xa0#64) ↦₆₄ iVt) ∗
       ((fut + 0xa8#64) ↦₆₄ pkPtr) ∗
       ((fut + 0xb0#64) ↦₆₄ pkVt) ∗
       ((fut + 0xc8#64) ↦₆₄ kPtr) ∗
       ((fut + 0xd0#64) ↦₆₄ kVt)) ∗
      coroCopyRemP4At fut meA spkPtr spkVt rng := by
  unfold decryptPrekeyCoroCopyAt coroCopyRemP4At
  ac_rfl

/-- Remainder of `preKeyMsgAt A g a m` after extracting `signalMessageAt`, `baseKey` (`+0xa8`), and
`identityKey` (`+0xc8`) for Stages P2, P3, and P4. -/
def preKeyMsgRemBaseIdKeyAt (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) : SepProp :=
  optU32At (a + 0x78#64) m.preKeyId ∗
  boxU8At A (a + 0x80#64) g.serPtr m.serialized ∗
  optKyberAt A (a + 0x90#64) g.kyberPtr m.kyberPayload ∗
  ((a + 0xe8#64) ↦₃₂ m.registrationId) ∗
  ((a + 0xec#64) ↦₃₂ m.signedPreKeyId) ∗
  ((a + 0xf0#64) ↦₈ m.messageVersion) ∗
  memRegion (a + 0xf1#64) 7

theorem preKeyMsgAt_eq_base_idKey_sep (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) :
    preKeyMsgAt A g a m =
      signalMessageAt A g.msg a m.message ∗
      ((a + 0xa8#64) ↦ₛ m.baseKey.bytes.toList) ∗
      ((a + 0xc8#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRemBaseIdKeyAt A g a m := by
  unfold preKeyMsgAt preKeyMsgRemBaseIdKeyAt
  ac_rfl

theorem exists_pointsTo64_entails_memRegion8 (a : BitVec 64) :
    (∃∗ u : BitVec 64, a ↦₆₄ u) ⊢ memRegion a 8 :=
  Entails.sepExists_elim fun u => ProofLib.pointsTo64_entails_memRegion a u

theorem sp_b8_32_bc_4_entails_memRegion8 (sp : BitVec 64) (v : BitVec 32) :
    ((sp + 0xb8#64) ↦₃₂ v) ∗ memRegion (sp + 0xbc#64) 4 ⊢ memRegion (sp + 0xb8#64) 8 := by
  rw [memRegion_split (sp + 0xb8#64) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_left (pointsTo32_entails_memRegion (sp + 0xb8#64) v)

/-- Fold all closure stack-frame atoms returned by Stage P3 `Err` / `verNe` (both Path A and Path B)
together with the Stage P3 caller stack gaps back into `memRegion (s0.sp - 0xcd0#64) 3280`. -/
theorem stageP3Err_stack_entails_3280 (s0 : State)
    (v80 v88 v90 va0 va8 vb0 vc0 vc8 v3a0 : BitVec 64) (vb8 : BitVec 32) :
    let sp := s0.sp - 0xcd0#64
    memRegion sp 8 ∗
    genP3S5SpillRem sp ∗
    memRegion (sp + 0x930#64) 48 ∗
    ((sp + 0x80#64) ↦₆₄ v80) ∗
    ((sp + 0x88#64) ↦₆₄ v88) ∗
    ((sp + 0x90#64) ↦₆₄ v90) ∗
    spLowGapsAt sp ∗
    ((sp + 0xa0#64) ↦₆₄ va0) ∗
    ((sp + 0xa8#64) ↦₆₄ va8) ∗
    ((sp + 0xb0#64) ↦₆₄ vb0) ∗
    ((sp + 0xb8#64) ↦₃₂ vb8) ∗
    memRegion (sp + 0xbc#64) 4 ∗
    ((sp + 0xc0#64) ↦₆₄ vc0) ∗
    ((sp + 0xc8#64) ↦₆₄ vc8) ∗
    memRegion (sp + 0xd8#64) 376 ∗
    memRegion (sp + 0x250#64) 20 ∗
    memRegion (sp + 0x264#64) 12 ∗
    memRegion (sp + 0x270#64) 48 ∗
    memRegion (sp + 0x2a0#64) 16 ∗
    memRegion (sp + 0x2b0#64) 192 ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x394#64) 12 ∗
    ((sp + 0x3a0#64) ↦₆₄ v3a0) ∗
    memRegion (sp + 0x3a8#64) 4 ∗
    ((sp + 0x3ac#64) ↦₈ 3#8) ∗
    memRegion (sp + 0x3ad#64) 27 ∗
    (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
      ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗
      ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((sp + 0x3d8#64) ↦₆₄ errsLen)) ∗
    memRegion (sp + 0x3e0#64) 344 ∗
    memRegion (sp + 0x538#64) 24 ∗
    memRegion (sp + 0xa90#64) 344 ∗
    spHighGapsAt sp ∗
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ⊢
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  change _ ⊢ memRegion sp 3280
  have hsp_cd0 : sp + 0xcd0#64 = s0.sp := by dsimp only [sp]; bv_omega
  rw [hsp_cd0]
  have hspill :
      genP3S5SpillRem sp ∗
      memRegion (sp + 0x930#64) 48 ∗
      ((sp + 0x80#64) ↦₆₄ v80) ∗
      ((sp + 0x88#64) ↦₆₄ v88) ∗
      ((sp + 0x90#64) ↦₆₄ v90) ∗
      spLowGapsAt sp ⊢
        memRegion (sp + 0x8#64) 144 ∗
        memRegion (sp + 0x930#64) 96 ∗
        memRegion (sp + 0x98#64) 8 ∗
        memRegion (sp + 0xd0#64) 8 :=
    Entails.trans (genP3S5SpillRem_fold sp v80 v88 v90)
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (exists_pointsTo64_entails_memRegion8 _)
          (exists_pointsTo64_entails_memRegion8 _))))
  have ha0 := ProofLib.pointsTo64_entails_memRegion (sp + 0xa0#64) va0
  have ha8 := ProofLib.pointsTo64_entails_memRegion (sp + 0xa8#64) va8
  have hb0 := ProofLib.pointsTo64_entails_memRegion (sp + 0xb0#64) vb0
  have hb8 := sp_b8_32_bc_4_entails_memRegion8 sp vb8
  have hc0 := ProofLib.pointsTo64_entails_memRegion (sp + 0xc0#64) vc0
  have hc8 := ProofLib.pointsTo64_entails_memRegion (sp + 0xc8#64) vc8
  have h3a0 := ProofLib.pointsTo64_entails_memRegion (sp + 0x3a0#64) v3a0
  have h3ac := pointsTo8_entails_memRegion (sp + 0x3ac#64) 3#8
  have h3c8 := sp_3c8_exists_entails_memRegion24 sp
  refine Entails.trans
    (sepConj_mono_right
      (Entails.trans
        (show _ ⊢
          (genP3S5SpillRem sp ∗ memRegion (sp + 0x930#64) 48 ∗
            ((sp + 0x80#64) ↦₆₄ v80) ∗ ((sp + 0x88#64) ↦₆₄ v88) ∗
            ((sp + 0x90#64) ↦₆₄ v90) ∗ spLowGapsAt sp) ∗
          ((sp + 0xa0#64) ↦₆₄ va0) ∗
          ((sp + 0xa8#64) ↦₆₄ va8) ∗
          ((sp + 0xb0#64) ↦₆₄ vb0) ∗
          (((sp + 0xb8#64) ↦₃₂ vb8) ∗ memRegion (sp + 0xbc#64) 4) ∗
          ((sp + 0xc0#64) ↦₆₄ vc0) ∗
          ((sp + 0xc8#64) ↦₆₄ vc8) ∗
          ((sp + 0x3a0#64) ↦₆₄ v3a0) ∗
          ((sp + 0x3ac#64) ↦₈ 3#8) ∗
          (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
            ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((sp + 0x3d8#64) ↦₆₄ errsLen)) ∗
          (memRegion (sp + 0xd8#64) 376 ∗ memRegion (sp + 0x250#64) 20 ∗
            memRegion (sp + 0x264#64) 12 ∗ memRegion (sp + 0x270#64) 48 ∗
            memRegion (sp + 0x2a0#64) 16 ∗ memRegion (sp + 0x2b0#64) 192 ∗
            memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x394#64) 12 ∗
            memRegion (sp + 0x3a8#64) 4 ∗ memRegion (sp + 0x3ad#64) 27 ∗
            memRegion (sp + 0x3e0#64) 344 ∗ memRegion (sp + 0x538#64) 24 ∗
            memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
            decryptPrekeySavedRegsAt s0.sp s0) by
          generalize
            (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
              ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
              ((sp + 0x3d8#64) ↦₆₄ errsLen)) = Perrs
          dsimp only [sp] at *
          sep_frame)
        (sepConj_mono hspill
          (sepConj_mono ha0 (sepConj_mono ha8 (sepConj_mono hb0
            (sepConj_mono hb8 (sepConj_mono hc0 (sepConj_mono hc8
              (sepConj_mono h3a0 (sepConj_mono h3ac (sepConj_mono_left h3c8)))))))))))) ?_
  have hrhs :
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
      (memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x234#64) 428) ∗
      memRegion (sp + 0x3e0#64) 368 ∗
      memRegion (sp + 0x550#64) 1824 ∗
      decryptPrekeySavedRegsAt s0.sp s0 ⊢ memRegion sp 3280 := by
    dsimp only [sp]
    simpa only [sepConj_assoc] using clos_stack_3280_of_regions s0.sp s0
  refine Entails.trans ?_ hrhs
  rw [← sp_d8_to_3e0_join sp, sp_3e0_368_eq_344_24 sp, sp_550_1824_split_genP3 sp]
  dsimp only [sp] at *
  sep_frame

/-- Bidirectional split of `memRegion (sp + 0x2b0#64) 192` into the four 36-byte Stage P4 slots
and their four 12-byte inter-slot gaps. -/
def sp2b0GapsAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x2d4#64) 12 ∗
  memRegion (sp + 0x304#64) 12 ∗
  memRegion (sp + 0x334#64) 12 ∗
  memRegion (sp + 0x364#64) 12

theorem sp_2b0_192_split (sp : BitVec 64) :
    memRegion (sp + 0x2b0#64) 192 =
      memRegion (sp + 0x2b0#64) 36 ∗
      memRegion (sp + 0x2e0#64) 36 ∗
      memRegion (sp + 0x310#64) 36 ∗
      memRegion (sp + 0x340#64) 36 ∗
      sp2b0GapsAt sp := by
  unfold sp2b0GapsAt
  rw [memRegion_split (sp + 0x2b0#64) 36 156 (by decide),
      memRegion_split (sp + 0x2b0#64 + 36#64) 12 144 (by decide),
      memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64) 36 108 (by decide),
      memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64) 12 96 (by decide),
      memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64 + 12#64) 36 60 (by decide),
      memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64) 12 48 (by decide),
      memRegion_split (sp + 0x2b0#64 + 36#64 + 12#64 + 36#64 + 12#64 + 36#64 + 12#64) 36 12 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-- Fold all closure coroutine atoms returned by Stage P3 `Err` / `verNe` or Stage P4 `ExitAt`
(once `[+0xe0..+0x250)` is `memRegion (fut + 0xe0#64) 368` and `[+0x298..+0x2ac)` are reduced to
`memRegion`s) back into `dpFutDoneAt fut`. -/
theorem stageP3Err_coro_entails_dpFutDoneAt
    (fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng : BitVec 64) :
    decryptPrekeyCoroInitAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng ∗
    decryptPrekeyCoroCopyAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng ∗
    memRegion (fut + 0xe0#64) 368 ∗
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
    coroPostP2UnusedAt fut ⊢
      dpFutDoneAt fut := by
  have hinit := coroInit_entails_memRegion_112 fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng
  have hcopy := coroCopy_entails_memRegion_112 fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng
  have h368 : memRegion (fut + 0xe0#64) 368 =
      memRegion (fut + 0xe0#64) 24 ∗ memRegion (fut + 0xf8#64) 344 := by
    rw [memRegion_split (fut + 0xe0#64) 24 344 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h368]
  refine Entails.trans (sepConj_mono hinit (sepConj_mono_left hcopy)) ?_
  refine Entails.trans (by sep_frame) (coro_regions_entails_dpFutDoneAt fut)

/-- Fold all closure stack-frame atoms returned by Stage P4 `stageP4ExitAt` / `stageP4MatchedExitAt`
together with the Stage P4 caller stack gaps back into `memRegion (s0.sp - 0xcd0#64) 3280`. -/
theorem stageP4Exit_stack_entails_3280 (s0 : State)
    (v80 v88 v90 va0 va8 vb0 vc0 vc8 v3a0 v270 ptCap ptPtr ptLen c3c8 c3d0 c3d8 : BitVec 64)
    (vb8 : BitVec 32) :
    let sp := s0.sp - 0xcd0#64
    memRegion sp 8 ∗
    genP3S5SpillRem sp ∗
    memRegion (sp + 0x930#64) 48 ∗
    ((sp + 0x80#64) ↦₆₄ v80) ∗
    ((sp + 0x88#64) ↦₆₄ v88) ∗
    ((sp + 0x90#64) ↦₆₄ v90) ∗
    spLowGapsAt sp ∗
    ((sp + 0xa0#64) ↦₆₄ va0) ∗
    ((sp + 0xa8#64) ↦₆₄ va8) ∗
    ((sp + 0xb0#64) ↦₆₄ vb0) ∗
    ((sp + 0xb8#64) ↦₃₂ vb8) ∗
    memRegion (sp + 0xbc#64) 4 ∗
    ((sp + 0xc0#64) ↦₆₄ vc0) ∗
    ((sp + 0xc8#64) ↦₆₄ vc8) ∗
    memRegion (sp + 0xd8#64) 376 ∗
    memRegion (sp + 0x250#64) 20 ∗
    memRegion (sp + 0x264#64) 12 ∗
    ((sp + 0x270#64) ↦₆₄ v270) ∗
    ((sp + 0x278#64) ↦₆₄ ptCap) ∗
    ((sp + 0x280#64) ↦₆₄ ptPtr) ∗
    ((sp + 0x288#64) ↦₆₄ ptLen) ∗
    memRegion (sp + 0x290#64) 16 ∗
    memRegion (sp + 0x2a0#64) 16 ∗
    memRegion (sp + 0x2b0#64) 36 ∗
    memRegion (sp + 0x2e0#64) 36 ∗
    memRegion (sp + 0x310#64) 36 ∗
    memRegion (sp + 0x340#64) 36 ∗
    sp2b0GapsAt sp ∗
    memRegion (sp + 0x370#64) 36 ∗
    memRegion (sp + 0x394#64) 12 ∗
    ((sp + 0x3a0#64) ↦₆₄ v3a0) ∗
    memRegion (sp + 0x3a8#64) 4 ∗
    ((sp + 0x3ac#64) ↦₈ 3#8) ∗
    memRegion (sp + 0x3ad#64) 27 ∗
    ((sp + 0x3c8#64) ↦₆₄ c3c8) ∗
    ((sp + 0x3d0#64) ↦₆₄ c3d0) ∗
    ((sp + 0x3d8#64) ↦₆₄ c3d8) ∗
    memRegion (sp + 0x3e0#64) 48 ∗
    memRegion (sp + 0x410#64) 296 ∗
    memRegion (sp + 0x538#64) 24 ∗
    memRegion (sp + 0xa90#64) 344 ∗
    spHighGapsAt sp ∗
    decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ⊢
      memRegion sp 3280 := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  change _ ⊢ memRegion sp 3280
  have h270 := sp_270_48_of_p4_slots sp v270 ptCap ptPtr ptLen
  have h3c8 :
      ((sp + 0x3c8#64) ↦₆₄ c3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ c3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ c3d8) ⊢
      (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
        ((sp + 0x3c8#64) ↦₆₄ errsCap) ∗
        ((sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
        ((sp + 0x3d8#64) ↦₆₄ errsLen)) :=
    Entails.sepExists_right c3c8 (Entails.sepExists_right c3d0
      (Entails.sepExists_right c3d8 (Entails.refl _)))
  refine Entails.trans
    (Entails.trans
      (show _ ⊢
        (((sp + 0x270#64) ↦₆₄ v270) ∗ ((sp + 0x278#64) ↦₆₄ ptCap) ∗
          ((sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((sp + 0x288#64) ↦₆₄ ptLen) ∗
          memRegion (sp + 0x290#64) 16) ∗
        (((sp + 0x3c8#64) ↦₆₄ c3c8) ∗ ((sp + 0x3d0#64) ↦₆₄ c3d0) ∗
          ((sp + 0x3d8#64) ↦₆₄ c3d8)) ∗
        (memRegion (sp + 0x2b0#64) 36 ∗ memRegion (sp + 0x2e0#64) 36 ∗
          memRegion (sp + 0x310#64) 36 ∗ memRegion (sp + 0x340#64) 36 ∗ sp2b0GapsAt sp) ∗
        (memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 296) ∗
        (memRegion sp 8 ∗ genP3S5SpillRem sp ∗ memRegion (sp + 0x930#64) 48 ∗
          ((sp + 0x80#64) ↦₆₄ v80) ∗ ((sp + 0x88#64) ↦₆₄ v88) ∗
          ((sp + 0x90#64) ↦₆₄ v90) ∗ spLowGapsAt sp ∗
          ((sp + 0xa0#64) ↦₆₄ va0) ∗ ((sp + 0xa8#64) ↦₆₄ va8) ∗
          ((sp + 0xb0#64) ↦₆₄ vb0) ∗ ((sp + 0xb8#64) ↦₃₂ vb8) ∗
          memRegion (sp + 0xbc#64) 4 ∗ ((sp + 0xc0#64) ↦₆₄ vc0) ∗
          ((sp + 0xc8#64) ↦₆₄ vc8) ∗ memRegion (sp + 0xd8#64) 376 ∗
          memRegion (sp + 0x250#64) 20 ∗ memRegion (sp + 0x264#64) 12 ∗
          memRegion (sp + 0x2a0#64) 16 ∗ memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x394#64) 12 ∗ ((sp + 0x3a0#64) ↦₆₄ v3a0) ∗
          memRegion (sp + 0x3a8#64) 4 ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
          memRegion (sp + 0x3ad#64) 27 ∗ memRegion (sp + 0x538#64) 24 ∗
          memRegion (sp + 0xa90#64) 344 ∗ spHighGapsAt sp ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0) by sep_frame)
      (sepConj_mono h270 (sepConj_mono_left h3c8))) ?_
  rw [← sp_2b0_192_split sp, ← sp_3e0_344_eq_48_296 sp]
  refine Entails.trans ?_
    (stageP3Err_stack_entails_3280 s0 v80 v88 v90 va0 va8 vb0 vc0 vc8 v3a0 vb8)
  dsimp only [sp] at *
  generalize
    (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
      ((s0.sp - 0xcd0#64 + 0x3c8#64) ↦₆₄ errsCap) ∗
      ((s0.sp - 0xcd0#64 + 0x3d0#64) ↦₆₄ errsPtr) ∗
      ((s0.sp - 0xcd0#64 + 0x3d8#64) ↦₆₄ errsLen)) = Perrs
  sep_frame

/-- Split `memRegion (coroPtr + 0x2a0#64) 8` into two 32-bit words for Path B `M4`. -/
theorem coro_2a0_8_eq_exists_words32 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x2a0#64) 8 =
      ∃∗ u0 : BitVec 32, ∃∗ u1 : BitVec 32,
        ((coroPtr + 0x2a0#64) ↦₃₂ u0) ∗ ((coroPtr + 0x2a4#64) ↦₃₂ u1) := by
  rw [memRegion_split (coroPtr + 0x2a0#64) 4 4 (by decide),
      memRegion_4_eq_exists_pointsTo32 (coroPtr + 0x2a0#64),
      memRegion_4_eq_exists_pointsTo32 (coroPtr + 0x2a0#64 + 4#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]

theorem coro_2a0_words32_entails_memRegion8 (coroPtr : BitVec 64) (u0 u1 : BitVec 32) :
    ((coroPtr + 0x2a0#64) ↦₃₂ u0) ∗ ((coroPtr + 0x2a4#64) ↦₃₂ u1) ⊢
      memRegion (coroPtr + 0x2a0#64) 8 := by
  rw [coro_2a0_8_eq_exists_words32 coroPtr]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.refl _))

/-- Bidirectional split of `memRegion (coroPtr + 0x2ac#64) 20` into `8 + 12` bytes for Path B `M4`. -/
theorem coro_2ac_20_eq_8_12 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x2ac#64) 20 =
      memRegion (coroPtr + 0x2ac#64) 8 ∗ memRegion (coroPtr + 0x2b4#64) 12 := by
  rw [memRegion_split (coroPtr + 0x2ac#64) 8 12 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Bidirectional split of `decryptPrekeyCoroCopyAt` (`[coroPtr + 0x70.. +0xe0)`) into the 8 words
used by `Matched.stageP4MatchedShared` and the 6 caller-preserved words. -/
def coroCopyRemMatchedP4At (fut meA pkPtr pkVt kPtr kVt rng : BitVec 64) : SepProp :=
  ((fut + 0x80#64) ↦₆₄ meA) ∗
  ((fut + 0xa8#64) ↦₆₄ pkPtr) ∗
  ((fut + 0xb0#64) ↦₆₄ pkVt) ∗
  ((fut + 0xc8#64) ↦₆₄ kPtr) ∗
  ((fut + 0xd0#64) ↦₆₄ kVt) ∗
  ((fut + 0xd8#64) ↦₆₄ rng)

theorem coroCopy_eq_matched_p4_sep
    (fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng : BitVec 64) :
    decryptPrekeyCoroCopyAt fut msgA peerA meA sPtr sVt iPtr iVt pkPtr pkVt spkPtr spkVt kPtr kVt rng =
      (((fut + 0x70#64) ↦₆₄ msgA) ∗
       ((fut + 0x78#64) ↦₆₄ peerA) ∗
       ((fut + 0x88#64) ↦₆₄ sPtr) ∗
       ((fut + 0x90#64) ↦₆₄ sVt) ∗
       ((fut + 0x98#64) ↦₆₄ iPtr) ∗
       ((fut + 0xa0#64) ↦₆₄ iVt) ∗
       ((fut + 0xb8#64) ↦₆₄ spkPtr) ∗
       ((fut + 0xc0#64) ↦₆₄ spkVt)) ∗
      coroCopyRemMatchedP4At fut meA pkPtr pkVt kPtr kVt rng := by
  unfold decryptPrekeyCoroCopyAt coroCopyRemMatchedP4At
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
