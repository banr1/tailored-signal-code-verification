/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Memmove -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import ProofLib.SepLogic.WPp

/-!
# `HookSat` Sibling of `StoreLoopProofs.DefsBudget` (`SegS3`, Block `24`)
(`LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudgetSat`)

Weakens `H "memmove" = some hookMemmove` in `InsertKeyPlacedSpec`, `StoreLoopIterPlacedSpec`,
`StoreLoopIterPlacedRoSpec`, `StoreLoopPlacedSpec`, and `StoreLoopPlacedRoSpec` to
`HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096)`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudgetSat

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (chainHmac chainKeySeed)
open CryptoGames.LibsignalSession (
  ChainKey RatchetState ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalPlacement LibsignalRoLoaded
  blkPC_24 blkPl_24 libsignalRoLoaded_of_keepsFrozen lsmpl
)
open CryptoVerification.LibsignalSessionRepr (ChainGhost RatchetGhost)
open CryptoVerification.SessionModel (chainStepN findReceiverChainIndex_set skippedKeys)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkEpiloguePC_placed cmkLoopPC_placed
)
open CryptoVerification.LibsignalSession.StoreLoop (updatedRatchetState)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustAllocEvents
)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (GrowOnePlacedOk)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkEpilogueEvs CmkLoopAdvanceEvs CmkLoopState_placed
  FindIndexPlacedOk HmacPlacedOk HmacPlacedRoOk cmkPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  AdvanceChainKeyPlacedRoSpec AdvanceChainKeyPlacedSpec AdvanceChainKeyState_placed
  CmkAfterGrowEvs CmkAfterSeedEvs CmkGrowOptEvs CmkIterPostEvs CmkPopOptEvs ConcatEnv
  DeriveSeedPlacedRoSpec DeriveSeedPlacedSpec EvictOldestKeyPlacedSpec
  EvictOldestKeyState_placed InsertKeyState_placed
  cmkAfterGrowEvs_nonempty cmkAfterSeedEvs_nonempty cmkLoopAdvanceEvs_of_seed_seq
  cmkLoopAdvanceEvs_zero_iff cmkNextCap cmkNextLen cmkNextLen_eq_take
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (sessionMemmoveBoundedBudgetSpec)

@[expose] def InsertKeyPlacedSpecSat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096) → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init stA : M.σ)
      (remAfterGrow : List AllocEvent → Prop)
      (Gc : RatchetGhost) (stc : RatchetState)
      (ckc : ChainKey) (ci : Nat) (chc : ReceiverChain)
      (seedPtr : BitVec 64) (R : SepProp) (s0 sA : State),
      stc.receiverChains[ci]? = some chc →
      (∃ evs, remAfterGrow evs) →
      InsertKeyState_placed F A lim x st_init stA
        (ConcatEnv (CmkGrowOptEvs ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length)
          remAfterGrow)
        Gc stc ckc ci seedPtr R s0 sA →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sA.mem →
      let cap1 := cmkNextCap ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length
      ∃ sB, Steps ((blkPC_24).rebase (blkPl_24).base H) sA sB ∧
        ((chc.messageKeys.length < maxMessageKeys ∧
          ∃ stB G', Gc.AgreeExcept G' (some ci) ∧
            (G'.chains[ci]?.map (·.mkCap)).getD 0#64 = cap1 ∧
            AdvanceChainKeyState_placed A lim x st_init stB remAfterGrow
              G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB) ∨
         (∃ stB cg,
            EvictOldestKeyState_placed F A lim x st_init stB remAfterGrow
              Gc stc ckc ci chc cg cap1 (sB.readReg64 .x24) seedPtr R s0 sB) ∨
         (sB.status = .Panicked ∧ (sB.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 sB ∗ R)))

@[expose] def StoreLoopIterPlacedSpecSat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096) →
    FindIndexPlacedOk H A → HmacPlacedOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (k : Nat) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((∃ st_next G', Gc.AgreeExcept G' (some ci) ∧
            (G'.chains[ci]?.map (·.mkCap)).getD 0#64 = cmkNextCap cap0 chc.messageKeys.length ∧
            CmkLoopState_placed A lim x st_init st_next
              (CmkIterPostEvs k cap0 chc.messageKeys.length isPanic)
              G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

@[expose] def StoreLoopIterPlacedRoSpecSat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096) →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (k : Nat) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let ck' := chainStepN F 1 ckc
      let st' : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys } }
      let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
      let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((∃ st_next G', Gc.AgreeExcept G' (some ci) ∧
            (G'.chains[ci]?.map (·.mkCap)).getD 0#64 = cmkNextCap cap0 chc.messageKeys.length ∧
            CmkLoopState_placed A lim x st_init st_next
              (CmkIterPostEvs k cap0 chc.messageKeys.length isPanic)
              G' st' ck' R nextPC s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

@[expose] def StoreLoopPlacedSpecSat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096) →
    FindIndexPlacedOk H A → HmacPlacedOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (x.counter - ckc.index).toNat
          ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

@[expose] def StoreLoopPlacedRoSpecSat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A lim H →
    HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096) →
    FindIndexPlacedOk H A → HmacPlacedRoOk H F → GrowOnePlacedOk H A lim →
    ∀ (x : ConsumeMessageKeyGhost) (st_init st : M.σ) (isPanic : Bool)
      (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State),
      ckc.index < x.counter →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (x.counter - ckc.index).toNat
          ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64) chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let n := (x.counter - ckc.index).toNat
      let ck_end := chainStepN F n ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F n ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))

theorem storeLoop_iter_placed_of_parts_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA_part : DeriveSeedPlacedSpec F A lim H)
    (hB_part : InsertKeyPlacedSpecSat F A lim H)
    (hC_part : EvictOldestKeyPlacedSpec F A lim H)
    (hD_part : AdvanceChainKeyPlacedSpec F A lim H) :
    StoreLoopIterPlacedSpecSat F A lim H := by
  unfold StoreLoopIterPlacedSpecSat
  intro hA hmm hfind hhmac hgrow x st_init st k isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
  let len0 := chc.messageKeys.length
  have hstate_seq :
      CmkLoopState_placed A lim x st_init st
        (ConcatEnv (fun evs => evs = rustAllocEvents 32 1) (CmkAfterSeedEvs k cap0 len0 isPanic))
        Gc stc ckc R cmkLoopPC_placed s0 s :=
    ⟨hstate.1.weaken fun _ h => cmkLoopAdvanceEvs_of_seed_seq h, hstate.2⟩
  obtain ⟨sA, hstepsA, ⟨stA, seedPtr, hsA⟩ | hpanA⟩ :=
    hA_part hA hfind hhmac x st_init st (CmkAfterSeedEvs k cap0 len0 isPanic)
      Gc stc ckc ci chc R s0 s hlt hci hchc (cmkAfterSeedEvs_nonempty k cap0 len0 isPanic)
      hstate_seq hL
  · have hLA := hstepsA.codeLoaded hL
    obtain ⟨sB, hstepsB, ⟨hlt_max, stB, G', hG', hcap', hsD⟩ | ⟨stB, cg, hsC⟩ | hpanB⟩ :=
      hB_part hmm hgrow x st_init stA (CmkAfterGrowEvs k cap0 len0 isPanic)
        Gc stc ckc ci chc seedPtr R s0 sA hchc (cmkAfterGrowEvs_nonempty k cap0 len0 isPanic)
        hsA hLA
    · have hLB := hstepsB.codeLoaded hLA
      have hnle : ¬ maxMessageKeys ≤ len0 := Nat.not_le.mpr hlt_max
      have hsD' : AdvanceChainKeyState_placed A lim x st_init stB
          (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB :=
        ⟨hsD.1.weaken fun evs h => ⟨[], evs, rfl, by simp [CmkPopOptEvs, hnle], h⟩, hsD.2⟩
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB hlt hsD' hLB
      exact ⟨s', (hstepsA.trans hstepsB).trans hstepsD, Or.inl ⟨stB, G', hG', hcap', hs'⟩⟩
    · have hLB := hstepsB.codeLoaded hLA
      have hlen2000 : len0 = maxMessageKeys := hsC.2.2.2.2.2.2.1
      have hle_max : maxMessageKeys ≤ len0 := Nat.le_of_eq hlen2000.symm
      have hsC' : EvictOldestKeyState_placed F A lim x st_init stB
          (ConcatEnv FreeOnlyEvs (CmkIterPostEvs k cap0 len0 isPanic))
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB :=
        ⟨hsC.1.weaken fun _ ⟨e1, e2, heq, h1, h2⟩ =>
          ⟨e1, e2, heq, by simp [CmkPopOptEvs, hle_max, h1], h2⟩, hsC.2⟩
      obtain ⟨sC, hstepsC, stC, G', hG', hcap', hsD⟩ :=
        hC_part hA x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB hchc hsC' hLB
      have hLC := hstepsC.codeLoaded hLB
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stC (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC hlt hsD hLC
      exact ⟨s', ((hstepsA.trans hstepsB).trans hstepsC).trans hstepsD,
        Or.inl ⟨stC, G', hG', hcap', hs'⟩⟩
    · exact ⟨sB, hstepsA.trans hstepsB, Or.inr hpanB⟩
  · exact ⟨sA, hstepsA, Or.inr hpanA⟩

theorem storeLoop_iter_placed_ro_of_parts_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA_part : DeriveSeedPlacedRoSpec F A lim H)
    (hB_part : InsertKeyPlacedSpecSat F A lim H)
    (hC_part : EvictOldestKeyPlacedSpec F A lim H)
    (hD_part : AdvanceChainKeyPlacedRoSpec F A lim H) :
    StoreLoopIterPlacedRoSpecSat F A lim H := by
  unfold StoreLoopIterPlacedRoSpecSat
  intro hA hmm hfind hhmac hgrow x st_init st k isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
  let cap0 := (Gc.chains[ci]?.map (·.mkCap)).getD 0#64
  let len0 := chc.messageKeys.length
  have hstate_seq :
      CmkLoopState_placed A lim x st_init st
        (ConcatEnv (fun evs => evs = rustAllocEvents 32 1) (CmkAfterSeedEvs k cap0 len0 isPanic))
        Gc stc ckc R cmkLoopPC_placed s0 s :=
    ⟨hstate.1.weaken fun _ h => cmkLoopAdvanceEvs_of_seed_seq h, hstate.2⟩
  obtain ⟨sA, hstepsA, ⟨stA, seedPtr, hsA⟩ | hpanA⟩ :=
    hA_part hA hfind hhmac x st_init st (CmkAfterSeedEvs k cap0 len0 isPanic)
      Gc stc ckc ci chc R s0 s hlt hci hchc (cmkAfterSeedEvs_nonempty k cap0 len0 isPanic)
      hstate_seq hL hro
  · have hLA := hstepsA.codeLoaded hL
    have hroA := libsignalRoLoaded_of_keepsFrozen hro hstepsA.keepsFrozen
    obtain ⟨sB, hstepsB, ⟨hlt_max, stB, G', hG', hcap', hsD⟩ | ⟨stB, cg, hsC⟩ | hpanB⟩ :=
      hB_part hmm hgrow x st_init stA (CmkAfterGrowEvs k cap0 len0 isPanic)
        Gc stc ckc ci chc seedPtr R s0 sA hchc (cmkAfterGrowEvs_nonempty k cap0 len0 isPanic)
        hsA hLA
    · have hLB := hstepsB.codeLoaded hLA
      have hroB := libsignalRoLoaded_of_keepsFrozen hroA hstepsB.keepsFrozen
      have hnle : ¬ maxMessageKeys ≤ len0 := Nat.not_le.mpr hlt_max
      have hsD' : AdvanceChainKeyState_placed A lim x st_init stB
          (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB :=
        ⟨hsD.1.weaken fun evs h => ⟨[], evs, rfl, by simp [CmkPopOptEvs, hnle], h⟩, hsD.2⟩
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sB hlt hsD' hLB hroB
      exact ⟨s', (hstepsA.trans hstepsB).trans hstepsD, Or.inl ⟨stB, G', hG', hcap', hs'⟩⟩
    · have hLB := hstepsB.codeLoaded hLA
      have hroB := libsignalRoLoaded_of_keepsFrozen hroA hstepsB.keepsFrozen
      have hlen2000 : len0 = maxMessageKeys := hsC.2.2.2.2.2.2.1
      have hle_max : maxMessageKeys ≤ len0 := Nat.le_of_eq hlen2000.symm
      have hsC' : EvictOldestKeyState_placed F A lim x st_init stB
          (ConcatEnv FreeOnlyEvs (CmkIterPostEvs k cap0 len0 isPanic))
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB :=
        ⟨hsC.1.weaken fun _ ⟨e1, e2, heq, h1, h2⟩ =>
          ⟨e1, e2, heq, by simp [CmkPopOptEvs, hle_max, h1], h2⟩, hsC.2⟩
      obtain ⟨sC, hstepsC, stC, G', hG', hcap', hsD⟩ :=
        hC_part hA x st_init stB (CmkIterPostEvs k cap0 len0 isPanic)
          Gc stc ckc ci chc cg (cmkNextCap cap0 len0) (sB.readReg64 .x24) seedPtr R s0 sB hchc hsC' hLB
      have hLC := hstepsC.codeLoaded hLB
      have hroC := libsignalRoLoaded_of_keepsFrozen hroB hstepsC.keepsFrozen
      obtain ⟨s', hstepsD, hs'⟩ :=
        hD_part hhmac x st_init stC (CmkIterPostEvs k cap0 len0 isPanic)
          G' (updatedRatchetState F stc ci chc ckc) ckc R s0 sC hlt hsD hLC hroC
      exact ⟨s', ((hstepsA.trans hstepsB).trans hstepsC).trans hstepsD,
        Or.inl ⟨stC, G', hG', hcap', hs'⟩⟩
    · exact ⟨sB, hstepsA.trans hstepsB, Or.inr hpanB⟩
  · exact ⟨sA, hstepsA, Or.inr hpanA⟩

private theorem take_append_take_of_le_placed {α : Type} :
    ∀ (xs ys : List α) {m k : Nat}, m ≤ k →
      (xs ++ ys.take k).take m = (xs ++ ys).take m
  | [], ys, m, k, hmk => by simp [List.take_take, Nat.min_eq_left hmk]
  | x :: xs, ys, 0, k, _ => rfl
  | x :: xs, ys, m + 1, k, hmk => by
    simp only [List.cons_append, List.take_succ_cons]
    exact congrArg (x :: ·) (take_append_take_of_le_placed xs ys (Nat.le_of_succ_le hmk))

private theorem take_append_take_eq_placed {α : Type} (xs ys : List α) (m : Nat) :
    (xs ++ ys.take m).take m = (xs ++ ys).take m :=
  take_append_take_of_le_placed xs ys (Nat.le_refl m)

private theorem set_set_same_placed {α : Type} (xs : List α) (i : Nat) (a b : α) :
    (xs.set i a).set i b = xs.set i b := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [List.set, ih]

private theorem getElem?_set_self_placed {α : Type} {xs : List α} {i : Nat}
    (hi : i < xs.length) (a : α) :
    (xs.set i a)[i]? = some a := by
  rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem_set_self]

private theorem storeLoop_placed_loop_ind_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hiter : StoreLoopIterPlacedSpecSat F A lim H)
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedOk H F)
    (hgrow : GrowOnePlacedOk H A lim)
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (isPanic : Bool)
    (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (st : M.σ) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter →
      (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))
  | 0, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq
      change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkEpiloguePC_placed := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨st_next, G', hG', _, hst'⟩ | hpan⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st 0 isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst'
      have hst_ep : CmkLoopState_placed A lim x st_init st_next (CmkEpilogueEvs isPanic)
          G' _ ck' R cmkEpiloguePC_placed s0 s' :=
        ⟨hst'.1.weaken fun _ h => cmkLoopAdvanceEvs_zero_iff.mpr h, hst'.2⟩
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, st_next, G', hG', ?_⟩⟩
      simpa [ck', chainStepN, skippedKeys] using hst_ep
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by
      rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkLoopPC_placed := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨st1_b, G1, hG1, hcap1, hst1⟩ | hpan1⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st (k + 1) isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self_placed hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]
        exact hci
      have hlen1 : cmkNextLen chc.messageKeys.length = chc1.messageKeys.length :=
        cmkNextLen_eq_take (ckc.messageKeys F) chc.messageKeys
      have hst1' : CmkLoopState_placed A lim x st_init st1_b
          (CmkLoopAdvanceEvs (k + 1) ((G1.chains[ci]?.map (·.mkCap)).getD 0#64)
            chc1.messageKeys.length isPanic)
          G1 st1 ck' R cmkLoopPC_placed s0 s1 := by
        refine ⟨hst1.1.weaken fun _ h => ?_, hst1.2⟩
        unfold CmkIterPostEvs
        rwa [← hcap1, hlen1]
      obtain ⟨s2, hsteps2, ⟨hck_end, st2_b, G2, hG2, hst2⟩ | hpan2⟩ :=
        storeLoop_placed_loop_ind_sat F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
          k st1_b G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1' (hsteps1.codeLoaded hL)
      · refine ⟨s2, hsteps1.trans hsteps2,
          Or.inl ⟨hck_end, st2_b, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]
          rw [set_set_same_placed]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (chainHmac F ckc.key chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq_placed]
            simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

theorem storeLoop_placed_of_iter_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hiter : StoreLoopIterPlacedSpecSat F A lim H) : StoreLoopPlacedSpecSat F A lim H := by
  unfold StoreLoopPlacedSpecSat
  intro hA hmm hfind hhmac hgrow x st_init st isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 :=
    ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only
  rw [hk] at hstate ⊢
  exact storeLoop_placed_loop_ind_sat F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
    k st Gc stc ckc chc s hlt hk hci hchc hstate hL

private theorem storeLoop_placed_ro_loop_ind_sat [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hiter : StoreLoopIterPlacedRoSpecSat F A lim H)
    (hA : CmkAllocHooks A lim H)
    (hmm : HookSat H "memmove" (sessionMemmoveBoundedBudgetSpec 4096))
    (hfind : FindIndexPlacedOk H A) (hhmac : HmacPlacedRoOk H F)
    (hgrow : GrowOnePlacedOk H A lim)
    (x : ConsumeMessageKeyGhost) (st_init : M.σ) (isPanic : Bool)
    (ci : Nat) (R : SepProp) (s0 : State) :
    ∀ (k : Nat) (st : M.σ) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
      (chc : ReceiverChain) (s : State),
      ckc.index < x.counter →
      (x.counter - ckc.index).toNat = k + 1 →
      stc.findReceiverChainIndex x.their = some ci →
      stc.receiverChains[ci]? = some chc →
      CmkLoopState_placed A lim x st_init st
        (CmkLoopAdvanceEvs (k + 1) ((Gc.chains[ci]?.map (·.mkCap)).getD 0#64)
          chc.messageKeys.length isPanic)
        Gc stc ckc R cmkLoopPC_placed s0 s →
      ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s.mem →
      LibsignalRoLoaded lsmpl s.mem →
      let ck_end := chainStepN F (k + 1) ckc
      let st_end : RatchetState :=
        { stc with
          receiverChains := stc.receiverChains.set ci
            { chc with messageKeys := (skippedKeys F (k + 1) ckc ++ chc.messageKeys).take maxMessageKeys } }
      ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) s s' ∧
        ((ck_end.index = x.counter ∧ ∃ st_end_b G', Gc.AgreeExcept G' (some ci) ∧
            CmkLoopState_placed A lim x st_init st_end_b (CmkEpilogueEvs isPanic)
              G' st_end ck_end R cmkEpiloguePC_placed s0 s') ∨
         (s'.status = .Panicked ∧ (s'.mem ⊨ (cmkPlacedSpec F A lim).onPanic (x, st_init) s0 s' ∗ R)))
  | 0, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL, hro => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_idx : ck'.index = x.counter := by
      apply BitVec.eq_of_toNat_eq
      change (ckc.index + 1#32).toNat = x.counter.toNat
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnlt : ¬ ((chainStepN F 1 ckc).index < x.counter) := by rw [hck'_idx]; exact BitVec.lt_irrefl _
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkEpiloguePC_placed := by simp [hnlt]
    obtain ⟨s', hsteps, ⟨st_next, G', hG', _, hst'⟩ | hpan⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st 0 isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
    · rw [hpc_eq] at hst'
      have hst_ep : CmkLoopState_placed A lim x st_init st_next (CmkEpilogueEvs isPanic)
          G' _ ck' R cmkEpiloguePC_placed s0 s' :=
        ⟨hst'.1.weaken fun _ h => cmkLoopAdvanceEvs_zero_iff.mpr h, hst'.2⟩
      refine ⟨s', hsteps, Or.inl ⟨hck'_idx, st_next, G', hG', ?_⟩⟩
      simpa [ck', chainStepN, skippedKeys] using hst_ep
    · exact ⟨s', hsteps, Or.inr hpan⟩
  | k + 1, st, Gc, stc, ckc, chc, s, hlt, hk, hci, hchc, hstate, hL, hro => by
    have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
    have hsub_nat : (x.counter - ckc.index).toNat = x.counter.toNat - ckc.index.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)
    let ck' := chainStepN F 1 ckc
    have hck'_toNat : ck'.index.toNat = ckc.index.toNat + 1 := by
      change (ckc.index + 1#32).toNat = ckc.index.toNat + 1
      have := x.counter.isLt
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt' : (chainStepN F 1 ckc).index < x.counter := by
      rw [BitVec.lt_def, hck'_toNat]; omega
    have hpc_eq : (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed) =
        cmkLoopPC_placed := by simp [hlt']
    have hk' : (x.counter - ck'.index).toNat = k + 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt'), hck'_toNat]; omega
    obtain ⟨s1, hsteps1, ⟨st1_b, G1, hG1, hcap1, hst1⟩ | hpan1⟩ :=
      hiter hA hmm hfind hhmac hgrow x st_init st (k + 1) isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
    · rw [hpc_eq] at hst1
      let chc1 : ReceiverChain :=
        { chc with messageKeys := (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys }
      let st1 : RatchetState := { stc with receiverChains := stc.receiverChains.set ci chc1 }
      have hci_lt : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc).1
      have hchc1 : st1.receiverChains[ci]? = some chc1 := getElem?_set_self_placed hci_lt chc1
      have hci1 : st1.findReceiverChainIndex x.their = some ci := by
        rw [findReceiverChainIndex_set stc x.their ci chc1 ⟨chc, hchc, rfl⟩]
        exact hci
      have hlen1 : cmkNextLen chc.messageKeys.length = chc1.messageKeys.length :=
        cmkNextLen_eq_take (ckc.messageKeys F) chc.messageKeys
      have hst1' : CmkLoopState_placed A lim x st_init st1_b
          (CmkLoopAdvanceEvs (k + 1) ((G1.chains[ci]?.map (·.mkCap)).getD 0#64)
            chc1.messageKeys.length isPanic)
          G1 st1 ck' R cmkLoopPC_placed s0 s1 := by
        refine ⟨hst1.1.weaken fun _ h => ?_, hst1.2⟩
        unfold CmkIterPostEvs
        rwa [← hcap1, hlen1]
      obtain ⟨s2, hsteps2, ⟨hck_end, st2_b, G2, hG2, hst2⟩ | hpan2⟩ :=
        storeLoop_placed_ro_loop_ind_sat F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
          k st1_b G1 st1 ck' chc1 s1 hlt' hk' hci1 hchc1 hst1' (hsteps1.codeLoaded hL)
          (libsignalRoLoaded_of_keepsFrozen hro hsteps1.keepsFrozen)
      · refine ⟨s2, hsteps1.trans hsteps2,
          Or.inl ⟨hck_end, st2_b, G2, RatchetGhost.AgreeExcept.trans hG1 hG2, ?_⟩⟩
        have hst_eq :
            { st1 with
              receiverChains := st1.receiverChains.set ci
                { chc1 with messageKeys := (skippedKeys F (k + 1) ck' ++ chc1.messageKeys).take maxMessageKeys } } =
            { stc with
              receiverChains := stc.receiverChains.set ci
                { chc with messageKeys := (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys } } := by
          dsimp only [st1, chc1, ck', chainStepN]
          rw [set_set_same_placed]
          have hmk :
              (skippedKeys F (k + 1)
                  ⟨bytesToKey32 (chainHmac F ckc.key chainKeySeed), ckc.index + 1⟩ ++
                (ckc.messageKeys F :: chc.messageKeys).take maxMessageKeys).take maxMessageKeys =
              (skippedKeys F (k + 2) ckc ++ chc.messageKeys).take maxMessageKeys := by
            rw [take_append_take_eq_placed]
            simp [skippedKeys, List.append_assoc]
          rw [hmk]
        rwa [hst_eq] at hst2
      · exact ⟨s2, hsteps1.trans hsteps2, Or.inr hpan2⟩
    · exact ⟨s1, hsteps1, Or.inr hpan1⟩

theorem storeLoop_placed_ro_of_iter_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hiter : StoreLoopIterPlacedRoSpecSat F A lim H) : StoreLoopPlacedRoSpecSat F A lim H := by
  unfold StoreLoopPlacedRoSpecSat
  intro hA hmm hfind hhmac hgrow x st_init st isPanic Gc stc ckc ci chc R s0 s hlt hci hchc hstate hL hro
  have hlt_nat : ckc.index.toNat < x.counter.toNat := BitVec.lt_def.mp hlt
  have hpos : 0 < (x.counter - ckc.index).toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]
    omega
  obtain ⟨k, hk⟩ : ∃ k, (x.counter - ckc.index).toNat = k + 1 :=
    ⟨(x.counter - ckc.index).toNat - 1, by omega⟩
  dsimp only
  rw [hk] at hstate ⊢
  exact storeLoop_placed_ro_loop_ind_sat F A lim H hiter hA hmm hfind hhmac hgrow x st_init isPanic ci R s0
    k st Gc stc ckc chc s hlt hk hci hchc hstate hL hro

end LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudgetSat
