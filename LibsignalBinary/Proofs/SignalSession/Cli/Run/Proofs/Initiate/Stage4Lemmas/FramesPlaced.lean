/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.PurePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.DecodePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Frames
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 4 Stack Frame Carve/Merge and Session Folding (`[LibsignalPlacement]`)

Re-exports Stage 4 stack carve/merge and `SessionState` folding lemmas alongside `lsLogOff_eq`,
`initArgsAtPlaced_entails_memRegion`, and `stage4FrameRegions_placed_entails_stackAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.TopLevel
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) :=
  rfl

theorem initArgsAtPlaced_entails_memRegion [LibsignalPlacement] (fsp : BitVec 64)
    (x : InitGhost) (s0 : State) :
    initArgsAtPlaced fsp x s0 ⊢ memRegion (fsp + 0xd0#64) 0x58 := by
  unfold initArgsAtPlaced
  rw [ProofLib.memRegion_split' (b := fsp + 0xd0#64) (n := 8) (k := 80)
        (b' := fsp + 0xd8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xd8#64) (n := 8) (k := 72)
        (b' := fsp + 0xe0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xe0#64) (n := 8) (k := 64)
        (b' := fsp + 0xe8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xe8#64) (n := 8) (k := 56)
        (b' := fsp + 0xf0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xf0#64) (n := 8) (k := 48)
        (b' := fsp + 0xf8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0xf8#64) (n := 8) (k := 40)
        (b' := fsp + 0x100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x100#64) (n := 8) (k := 32)
        (b' := fsp + 0x108#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x108#64) (n := 8) (k := 24)
        (b' := fsp + 0x110#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x110#64) (n := 4) (k := 20)
        (b' := fsp + 0x114#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x114#64) (n := 4) (k := 16)
        (b' := fsp + 0x118#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x118#64) (n := 8) (k := 8)
        (b' := fsp + 0x120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))))

theorem stage4FrameRegions_placed_entails_stackAt [LibsignalPlacement] {B : RunBudgets} {stk : Nat}
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (x : InitGhost) (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (b5b8 b5b9 : BitVec 8) (s0 : State)
    (hekA : ekAPk.length = 32) (hekASk : ekASk.length = 32) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    memRegion fsp 0xd0 ∗
      initArgsAtPlaced fsp x s0 ∗
      initFreshRecAt fsp ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      (((fsp + 0x298#64) ↦ₛ ekAPk) ∗
        memRegion (fsp + 0x2b8#64) 0x48 ∗
        ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
        memRegion (fsp + 0x308#64) 0x40 ∗
        ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
        ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
        ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
        ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
        ((fsp + 0x3c8#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((fsp + 0x3e8#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x408#64) ↦ₛ x.bundle.spk.bytes.toList) ∗
        ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
        ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
        (match x.bundle.opk with
         | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
         | none => memRegion (fsp + 0x439#64) 32) ∗
        ((fsp + 0x459#64) ↦₈ 0#8) ∗
        memRegion (fsp + 0x45a#64) 6) ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      ((fsp + 0x5b8#64) ↦₈ b5b8) ∗ ((fsp + 0x5b9#64) ↦₈ b5b9) ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      memRegion (s0.sp - 0x60#64) 0x60 ∗
      stackAt fsp (stk - cliInitiateFrame) ⊢
      stackAt s0.sp stk := by
  intro fsp opkFlag
  have hge := stk_ge_frame hstk
  have hlocals :
      memRegion fsp 0xd0 ∗
      memRegion (fsp + 0xd0#64) 0x58 ∗
      memRegion (fsp + 0x128#64) 0x20 ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      memRegion (fsp + 0x298#64) 0x1c8 ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 ∗
      memRegion (fsp + 0x5b9#64) 1 ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) =
        memRegion fsp initLocalsSize := by
    change memRegion fsp 0xd0 ∗
      memRegion (fsp + 0xd0#64) 0x58 ∗
      memRegion (fsp + 0x128#64) 0x20 ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      memRegion (fsp + 0x298#64) 0x1c8 ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 ∗
      memRegion (fsp + 0x5b9#64) 1 ∗
      memRegion (fsp + 0x5ba#64) 5846 = memRegion fsp 7312
    rw [ProofLib.memRegion_split' (b := fsp) (n := 0xd0) (k := 7104)
          (b' := fsp + 0xd0#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0xd0#64) (n := 0x58) (k := 7016)
          (b' := fsp + 0x128#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x128#64) (n := 0x20) (k := 6984)
          (b' := fsp + 0x148#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x148#64) (n := 0x150) (k := 6648)
          (b' := fsp + 0x298#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x298#64) (n := 0x1c8) (k := 6192)
          (b' := fsp + 0x460#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x460#64) (n := 0x158) (k := 5848)
          (b' := fsp + 0x5b8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x5b8#64) (n := 1) (k := 5847)
          (b' := fsp + 0x5b9#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 0x5b9#64) (n := 1) (k := 5846)
          (b' := fsp + 0x5ba#64) rfl (by bv_omega) (by decide)]
  have hframe :
      memRegion fsp initLocalsSize ∗ memRegion (s0.sp - 0x60#64) 0x60 =
        memRegion fsp cliInitiateFrame :=
    (ProofLib.memRegion_split' (b := fsp) (n := 7312) (k := 96)
      (b' := s0.sp - 0x60#64) rfl (by dsimp [fsp, cliInitiateFrame]; bv_omega) (by decide)).symm
  have hstk_merge :
      stackAt fsp (stk - cliInitiateFrame) ∗ memRegion fsp cliInitiateFrame =
        stackAt s0.sp stk := by
    dsimp only [stackAt]
    have hbase : fsp - BitVec.ofNat 64 (stk - cliInitiateFrame) = s0.sp - BitVec.ofNat 64 stk := by
      dsimp only [fsp]
      have hsub : BitVec.ofNat 64 cliInitiateFrame + BitVec.ofNat 64 (stk - cliInitiateFrame) =
          BitVec.ofNat 64 stk :=
        bv64_ofNat_add_eq_of_mod (by omega)
      bv_omega
    rw [hbase]
    exact (ProofLib.memRegion_split' (b := s0.sp - BitVec.ofNat 64 stk)
      (n := stk - cliInitiateFrame) (k := cliInitiateFrame) (b' := fsp)
      (by omega) (by rw [← hbase]; bv_omega) (by omega)).symm
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (initArgsAtPlaced_entails_memRegion fsp x s0)
    (sepConj_mono (initFreshRecAt_entails_memRegion fsp)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (stage3KeySlotsNoHeap_entails_memRegion fsp x.bundle kp ekASk ekAPk
        pqspkPtr opkId hekA hekASk)
    (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (Entails.refl _))))))))) ?_
  have heq :
      memRegion fsp 0xd0 ∗
      memRegion (fsp + 0xd0#64) 0x58 ∗
      memRegion (fsp + 0x128#64) 0x20 ∗
      memRegion (fsp + 0x148#64) 0x150 ∗
      memRegion (fsp + 0x298#64) 0x1c8 ∗
      memRegion (fsp + 0x460#64) 0x158 ∗
      memRegion (fsp + 0x5b8#64) 1 ∗
      memRegion (fsp + 0x5b9#64) 1 ∗
      memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
      memRegion (s0.sp - 0x60#64) 0x60 ∗
      stackAt fsp (stk - cliInitiateFrame) =
        stackAt s0.sp stk := by
    have h1 :
        memRegion fsp 0xd0 ∗
        memRegion (fsp + 0xd0#64) 0x58 ∗
        memRegion (fsp + 0x128#64) 0x20 ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        memRegion (fsp + 0x298#64) 0x1c8 ∗
        memRegion (fsp + 0x460#64) 0x158 ∗
        memRegion (fsp + 0x5b8#64) 1 ∗
        memRegion (fsp + 0x5b9#64) 1 ∗
        memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
        memRegion (s0.sp - 0x60#64) 0x60 ∗
        stackAt fsp (stk - cliInitiateFrame) =
        stackAt fsp (stk - cliInitiateFrame) ∗
          ((memRegion fsp 0xd0 ∗
            memRegion (fsp + 0xd0#64) 0x58 ∗
            memRegion (fsp + 0x128#64) 0x20 ∗
            memRegion (fsp + 0x148#64) 0x150 ∗
            memRegion (fsp + 0x298#64) 0x1c8 ∗
            memRegion (fsp + 0x460#64) 0x158 ∗
            memRegion (fsp + 0x5b8#64) 1 ∗
            memRegion (fsp + 0x5b9#64) 1 ∗
            memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba)) ∗
           memRegion (s0.sp - 0x60#64) 0x60) := by ac_rfl
    rw [h1, hlocals, hframe, hstk_merge]
  exact Entails.of_eq heq

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
