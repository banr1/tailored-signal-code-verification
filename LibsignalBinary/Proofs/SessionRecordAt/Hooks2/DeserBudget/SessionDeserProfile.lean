/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields

/-!
# `DeserBoundedTotalEvs` Allocation Profile for `sessDeserEvents`

Proves tight (`SessDeserSetBEnv`) and coarse (`SessDeserSetAEnv`) `DeserBoundedTotalEvs` allocation
profiles directly on `sessDeserEvents r` from `DeserializeScopeP_Q NonEmptyV1Q r` (`bs := encodeRecord r`),
together with `2 MiB` corollaries and `CliPqxdhInputs` → `FilesOkPeer` domain-chain bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile

open Arm64.Process (bytesOfString)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (IdentityKey MessageKeyGenerator ReceiverChain maxMessageKeys maxReceiverChains)
open CryptoGames.LibsignalSessionApi (PendingPreKey Session SessionRecord)
open CryptoVerification.E2E (PEParams wirePrekey wireWhisper)
open CryptoVerification.E2E.Record (bytesField encMessageKey encodeRecord lenField uint32Field)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainField ChainG GenField chainGAfter chainGAfter_fields genFields recvChainG senderChainG ssgOf)
open CryptoVerification.E2E.Record.L1GX (GenFieldX genFieldsX kyberBody pendingFieldX pendingIdBody pendingSpkBody)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliPqxdhInputs Cmd Inputs bundleDir partyAddress pqInitInputs pqRecvInputs pqSendInputs)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV cliIo parseArgs ratchetScopeCoversPq_scopeIn)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf callPeer runFiles)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer callPeer_of_cmd filesOkPeer_pqInit filesOkPeer_pqRecv filesOkPeer_pqSend partyAddr pqSessBytes_le_fileCapBytes scopeIn scopeKit scopeKit_of_scopeIn)
open LibsignalBinary.Heap (AllocEvent rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (ChainFieldBytesOk chainDoneEvents chainFieldStepEvents chainMergeEvents mem_fields_bytes_le_33)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (basicFieldByteLen mergeFieldQEvents nextCapRecv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (IsPow2Cap4 isPow2Cap4_zero_or_ge_four le_vecCap4Of vec104GrowEvents vecCap4Next vecCap4Of vecCap4Of_le_eight vecCap4Of_le_four_mul_pow vecCap4Of_le_two_mul_sub_two vecCap4Of_mono vecCap4Of_pow2 vecCap4Of_succ vecCap4Push)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (bytesDropEvents bytesMergeAllocEvents bytesMergeEvents doReserveEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget (fieldsEventsAux nextCapRecv_eq_vecCap4Of recvCount sessDeserEvents ssgqAfter_recv_length)
open LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget (DeserBoundedTotalEvs deserSmallStepReq deserSmallTotalReq otherAllocCount otherAllocStep reallocCount reallocStep tinyAllocCount tinyAllocStep totalStepReq)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ encodeRecord_eq_recFieldsQ genFieldsQ pendingFieldQ recFieldsQ recFieldsQ_ok ssgqAfter_recFieldsQ ssgqOf)

/-! ## 1. Named `SessDeserSetBEnv` & `SessDeserSetAEnv` Profiles and Monotonicity -/

/-- Tight Set B `DeserBoundedTotalEvs` profile `(min 20064 (bs.length / 18 + 64), 16, 48, min (12 * bs.length + 4096) 2000000, 14 * bs.length + 4096, 6 * bs.length + 4096)` on wire slice `bs`. -/
abbrev SessDeserSetBEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  DeserBoundedTotalEvs
    (min 20064 (bs.length / 18 + 64))
    16
    48
    (min (12 * bs.length + 4096) 2000000)
    (14 * bs.length + 4096)
    (6 * bs.length + 4096)
    evs

/-- Relaxed Set A `DeserBoundedTotalEvs` profile `(min 20064 (bs.length / 18 + 64), 64, 128, min (12 * bs.length + 4096) 2000000, 14 * bs.length + 4096, 6 * bs.length + 4096)` on wire slice `bs`. -/
abbrev SessDeserSetAEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  DeserBoundedTotalEvs
    (min 20064 (bs.length / 18 + 64))
    64
    128
    (min (12 * bs.length + 4096) 2000000)
    (14 * bs.length + 4096)
    (6 * bs.length + 4096)
    evs

/-- Componentwise monotonicity of `DeserBoundedTotalEvs`. -/
theorem deserBoundedTotalEvs_mono
    {t₁ t₂ o₁ o₂ r₁ r₂ s₁ s₂ tot₁ tot₂ m₁ m₂ : Nat} {evs : List AllocEvent}
    (h : DeserBoundedTotalEvs t₁ o₁ r₁ s₁ tot₁ m₁ evs)
    (ht : t₁ ≤ t₂) (ho : o₁ ≤ o₂) (hr : r₁ ≤ r₂)
    (hs : s₁ ≤ s₂) (htot : tot₁ ≤ tot₂) (hm : m₁ ≤ m₂) :
    DeserBoundedTotalEvs t₂ o₂ r₂ s₂ tot₂ m₂ evs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Nat.le_trans h1 ht, Nat.le_trans h2 ho, Nat.le_trans h3 hr,
    Nat.le_trans h4 hs, Nat.le_trans h5 htot,
    fun ev hev => ⟨Nat.le_trans (h6 ev hev).1 hm, (h6 ev hev).2⟩⟩

/-! ## 2. Additive Event Counter Lemmas & `bytesMergeEvents` Bounds -/

private theorem tinyAllocCount_append (xs ys : List AllocEvent) :
    tinyAllocCount (xs ++ ys) = tinyAllocCount xs + tinyAllocCount ys := by
  induction xs with
  | nil => simp [tinyAllocCount]
  | cons ev xs ih => simp only [List.cons_append, tinyAllocCount, ih]; omega

private theorem otherAllocCount_append (xs ys : List AllocEvent) :
    otherAllocCount (xs ++ ys) = otherAllocCount xs + otherAllocCount ys := by
  induction xs with
  | nil => simp [otherAllocCount]
  | cons ev xs ih => simp only [List.cons_append, otherAllocCount, ih]; omega

private theorem reallocCount_append (xs ys : List AllocEvent) :
    reallocCount (xs ++ ys) = reallocCount xs + reallocCount ys := by
  induction xs with
  | nil => simp [reallocCount]
  | cons ev xs ih => simp only [List.cons_append, reallocCount, ih]; omega

private theorem deserSmallTotalReq_append (xs ys : List AllocEvent) :
    deserSmallTotalReq (xs ++ ys) = deserSmallTotalReq xs + deserSmallTotalReq ys := by
  induction xs with
  | nil => simp [deserSmallTotalReq]
  | cons ev xs ih => simp only [List.cons_append, deserSmallTotalReq, ih]; omega

private theorem totalStepReq_append (xs ys : List AllocEvent) :
    totalStepReq (xs ++ ys) = totalStepReq xs + totalStepReq ys := by
  induction xs with
  | nil => simp [totalStepReq]
  | cons ev xs ih => simp only [List.cons_append, totalStepReq, ih]; omega

private theorem bytesMergeEvents_zero_pos {n : Nat} (hn : 0 < n) :
    bytesMergeEvents 0 n = [.alloc n, .alloc (max n 8), .free 1 n] := by
  have hne : n ≠ 0 := by omega
  have hle1 : 1 ≤ n := hn
  have hle2 : 1 ≤ max n 8 := by omega
  have ha1 : (1 : Nat) ≤ 16 ∧ 1 ≤ n := ⟨by decide, hle1⟩
  have ha2 : (1 : Nat) ≤ 16 ∧ 1 ≤ max n 8 := ⟨by decide, hle2⟩
  simp [bytesMergeEvents, bytesMergeAllocEvents, bytesDropEvents, doReserveEvents,
    rustAllocEvents, rustDeallocEvents, hne, hn, ha1, ha2]

private theorem bytesMergeEvents_tiny_exact {n : Nat} (hpos : 0 < n) (hle33 : n ≤ 33) :
    tinyAllocCount (bytesMergeEvents 0 n) = 2 ∧
    otherAllocCount (bytesMergeEvents 0 n) = 0 ∧
    reallocCount (bytesMergeEvents 0 n) = 0 ∧
    deserSmallTotalReq (bytesMergeEvents 0 n) = 0 ∧
    totalStepReq (bytesMergeEvents 0 n) ≤ 66 ∧
    ∀ ev ∈ bytesMergeEvents 0 n, eventStepReq ev ≤ 33 ∧ eventStepAlign ev ≤ 16 := by
  rw [bytesMergeEvents_zero_pos hpos]
  have h1 : n ≤ 44 := by omega
  have h2 : ¬ (44 < n) := by omega
  have h3 : max n 8 ≤ 44 := by omega
  have h4 : ¬ (44 < max n 8) := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tinyAllocCount, tinyAllocStep, h1, h3]
  · simp [otherAllocCount, otherAllocStep, h2, h4]
  · simp [reallocCount, reallocStep]
  · simp [deserSmallTotalReq, deserSmallStepReq, h2, h4]
  · simp only [totalStepReq, eventStepReq]; omega
  · intro ev hev
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl | rfl <;> simp only [eventStepReq, eventStepAlign] <;> omega

private theorem bytesMergeEvents_1569_exact :
    tinyAllocCount (bytesMergeEvents 0 1569) = 0 ∧
    otherAllocCount (bytesMergeEvents 0 1569) = 2 ∧
    reallocCount (bytesMergeEvents 0 1569) = 0 ∧
    deserSmallTotalReq (bytesMergeEvents 0 1569) = 3138 ∧
    totalStepReq (bytesMergeEvents 0 1569) = 3138 ∧
    ∀ ev ∈ bytesMergeEvents 0 1569, eventStepReq ev ≤ 1569 ∧ eventStepAlign ev ≤ 16 := by
  rw [bytesMergeEvents_zero_pos (by decide : 0 < 1569)]
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro ev hev
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
  rcases hev with rfl | rfl | rfl <;> decide

private theorem bytesMergeEvents_general_bounds (n : Nat) :
    tinyAllocCount (bytesMergeEvents 0 n) ≤ 2 ∧
    otherAllocCount (bytesMergeEvents 0 n) ≤ 2 ∧
    reallocCount (bytesMergeEvents 0 n) = 0 ∧
    deserSmallTotalReq (bytesMergeEvents 0 n) ≤ min (2 * n) 270334 ∧
    totalStepReq (bytesMergeEvents 0 n) ≤ 2 * n + 8 ∧
    ∀ ev ∈ bytesMergeEvents 0 n, eventStepReq ev ≤ n + 8 ∧ eventStepAlign ev ≤ 16 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [tinyAllocCount, otherAllocCount, reallocCount, deserSmallTotalReq, totalStepReq]
  · rw [bytesMergeEvents_zero_pos hpos]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [tinyAllocCount, tinyAllocStep]; split_ifs <;> omega
    · simp only [otherAllocCount, otherAllocStep]; split_ifs <;> omega
    · simp [reallocCount, reallocStep]
    · simp only [deserSmallTotalReq, deserSmallStepReq]
      by_cases h44 : n ≤ 44
      · have h1 : ¬ (44 < n) := by omega
        have h2 : ¬ (44 < max n 8) := by omega
        simp only [h1, h2, false_and, ↓reduceIte]
        omega
      · have hmax : max n 8 = n := by omega
        rw [hmax]
        by_cases h135 : n ≤ 135167
        · have hgt : 44 < n := by omega
          simp only [hgt, h135, and_self, ↓reduceIte]
          omega
        · simp only [h135, and_false, ↓reduceIte]
          omega
    · simp only [totalStepReq, eventStepReq]; omega
    · intro ev hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl | rfl <;> simp only [eventStepReq, eventStepAlign] <;> omega

/-! ## 3. Parametric `Vec<104>` Doubling Telescoping (`vec104CumF`) -/

private def vec104CumF (f : Nat → Nat) (cap : Nat) : Nat :=
  if cap < 4 then 0
  else if cap < 8 then f 0
  else vec104CumF f (cap / 2) + f (cap / 2)
termination_by cap
decreasing_by omega

private theorem vec104CumF_zero (f : Nat → Nat) : vec104CumF f 0 = 0 := by
  unfold vec104CumF
  simp only [Nat.reduceLT, ↓reduceIte]

private theorem vec104CumF_four (f : Nat → Nat) : vec104CumF f 4 = f 0 := by
  unfold vec104CumF
  simp only [Nat.reduceLT, ↓reduceIte]

private theorem vec104CumF_two_mul (f : Nat → Nat) {cap : Nat} (hcap : 4 ≤ cap) :
    vec104CumF f (2 * cap) = vec104CumF f cap + f cap := by
  conv_lhs => unfold vec104CumF
  have h1 : ¬ (2 * cap < 4) := by omega
  have h2 : ¬ (2 * cap < 8) := by omega
  have hdiv : (2 * cap) / 2 = cap := by omega
  simp only [h1, h2, hdiv, ↓reduceIte]

private theorem vec104CumF_next (f : Nat → Nat) {cap : Nat} (hcap : IsPow2Cap4 cap) :
    vec104CumF f (vecCap4Next cap) = vec104CumF f cap + f cap := by
  rcases isPow2Cap4_zero_or_ge_four hcap with rfl | hge
  · simp only [vecCap4Next, ↓reduceIte, vec104CumF_four, vec104CumF_zero, Nat.zero_add]
  · have hne : cap ≠ 0 := by omega
    simp only [vecCap4Next, hne, ↓reduceIte]
    exact vec104CumF_two_mul f hge

private def vec104PowSum (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | j + 1 => vec104PowSum f j + f (4 * 2 ^ j)

private theorem vec104CumF_pow2_eq (f : Nat → Nat) (j : Nat) :
    vec104CumF f (4 * 2 ^ j) = vec104PowSum f j := by
  induction j with
  | zero => exact vec104CumF_four f
  | succ j ih =>
    have hge : 4 ≤ 4 * 2 ^ j := by
      have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    have heq : 4 * 2 ^ (j + 1) = 2 * (4 * 2 ^ j) := by rw [Nat.pow_succ]; omega
    rw [heq, vec104CumF_two_mul f hge, ih, vec104PowSum]

private theorem vec104CumF_pow2_mono (f : Nat → Nat) {i j : Nat} (hij : i ≤ j) :
    vec104CumF f (4 * 2 ^ i) ≤ vec104CumF f (4 * 2 ^ j) := by
  induction hij with
  | refl => omega
  | step _ ih =>
    rename_i m _
    have hge : 4 ≤ 4 * 2 ^ m := by
      have hm : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    have heq : 4 * 2 ^ (m + 1) = 2 * (4 * 2 ^ m) := by rw [Nat.pow_succ]; omega
    rw [heq, vec104CumF_two_mul f hge]
    omega

private theorem vec104CumF_le_of_pow2 (f : Nat → Nat) {cap capMax : Nat}
    (hcap : IsPow2Cap4 cap) (hmax : IsPow2Cap4 capMax) (hle : cap ≤ capMax) :
    vec104CumF f cap ≤ vec104CumF f capMax := by
  rcases hcap with rfl | ⟨i, rfl⟩
  · simp only [vec104CumF_zero, Nat.zero_le]
  · rcases hmax with rfl | ⟨j, rfl⟩
    · have : 1 ≤ 2 ^ i := Nat.one_le_two_pow; omega
    · have hpow_le : 2 ^ i ≤ 2 ^ j := by omega
      have hij : i ≤ j := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 hpow_le
      exact vec104CumF_pow2_mono f hij

private theorem vec104CumF_push (f : Nat → Nat) (n : Nat) :
    vec104CumF f (vecCap4Of (n + 1)) =
      vec104CumF f (vecCap4Of n) + (if n < vecCap4Of n then 0 else f (vecCap4Of n)) := by
  rw [vecCap4Of_succ]
  unfold vecCap4Push
  split
  · omega
  · exact vec104CumF_next f (vecCap4Of_pow2 n)

private def fOther (cap : Nat) : Nat := if cap = 0 then 1 else 0
private def fRealloc (cap : Nat) : Nat := if cap = 0 then 0 else 1
private def fSmall (cap : Nat) : Nat :=
  if cap = 0 then 416 else if 2 * cap * 104 ≤ 135167 then 2 * cap * 104 else 0
private def fTotal (cap : Nat) : Nat :=
  if cap = 0 then 416 else 2 * cap * 104

private theorem vec104GrowEvents_zero_eq : vec104GrowEvents 0 = [.alloc 416] := by
  simp [vec104GrowEvents, rustAllocEvents]

private theorem vec104GrowEvents_pos_eq {cap : Nat} (hge : 4 ≤ cap) :
    vec104GrowEvents cap = [.realloc 8 (cap * 104) (2 * cap * 104)] := by
  have hne : cap ≠ 0 := by omega
  have hal : (8 : Nat) ≤ 16 ∧ 8 ≤ 2 * cap * 104 := ⟨by decide, by omega⟩
  simp [vec104GrowEvents, rustReallocEvents, hne, hal]

private theorem vec104GrowEvents_step_stats {cap : Nat} (hcap : IsPow2Cap4 cap) :
    tinyAllocCount (vec104GrowEvents cap) = 0 ∧
    otherAllocCount (vec104GrowEvents cap) = fOther cap ∧
    reallocCount (vec104GrowEvents cap) = fRealloc cap ∧
    deserSmallTotalReq (vec104GrowEvents cap) = fSmall cap ∧
    totalStepReq (vec104GrowEvents cap) = fTotal cap ∧
    ∀ ev ∈ vec104GrowEvents cap, eventStepReq ev ≤ vecCap4Next cap * 104 ∧ eventStepAlign ev ≤ 16 := by
  rcases isPow2Cap4_zero_or_ge_four hcap with rfl | hge
  · rw [vec104GrowEvents_zero_eq]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    decide
  · rw [vec104GrowEvents_pos_eq hge]
    have hne : cap ≠ 0 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [tinyAllocCount, tinyAllocStep]
    · simp [otherAllocCount, otherAllocStep, fOther, hne]
    · simp [reallocCount, reallocStep, fRealloc, hne]
    · simp [deserSmallTotalReq, deserSmallStepReq, fSmall, hne]
    · simp [totalStepReq, eventStepReq, fTotal, hne]
    · intro ev hev
      simp only [List.mem_singleton] at hev
      subst hev
      simp only [eventStepReq, eventStepAlign, vecCap4Next, hne, ↓reduceIte]
      omega

private theorem vec104CumF_mono_fn {f g : Nat → Nat} (hfg : ∀ c, f c ≤ g c) (cap : Nat) :
    vec104CumF f cap ≤ vec104CumF g cap := by
  induction cap using Nat.strongRecOn with
  | ind n ih =>
    unfold vec104CumF
    split
    · omega
    · split
      · exact hfg 0
      · have h1 := ih (n / 2) (by omega)
        have h2 := hfg (n / 2)
        omega

private theorem vec104CumF_fTotal_pow2_eq (j : Nat) :
    vec104CumF fTotal (4 * 2 ^ j) = (2 * (4 * 2 ^ j) - 4) * 104 := by
  induction j with
  | zero =>
    show vec104CumF fTotal 4 = 416
    rw [vec104CumF_four]
    rfl
  | succ j ih =>
    have hge : 4 ≤ 4 * 2 ^ j := by
      have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega
    have heq : 4 * 2 ^ (j + 1) = 2 * (4 * 2 ^ j) := by rw [Nat.pow_succ]; omega
    rw [heq, vec104CumF_two_mul fTotal hge, ih]
    unfold fTotal
    have hne : 4 * 2 ^ j ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    omega

private theorem vec104CumF_fTotal_le_linear (n : Nat) :
    vec104CumF fTotal (vecCap4Of n) ≤ 416 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [vec104CumF_zero]
  · rcases vecCap4Of_pow2 n with h0 | ⟨j, hj⟩
    · have hle := le_vecCap4Of n
      omega
    · rw [hj, vec104CumF_fTotal_pow2_eq j, ← hj]
      by_cases h5 : 5 ≤ n
      · have hcap := vecCap4Of_le_two_mul_sub_two h5
        omega
      · have hle4 : n ≤ 4 := by omega
        have hcap4 : vecCap4Of n ≤ 4 := vecCap4Of_le_four_mul_pow 0 (by simpa using hle4)
        omega

private theorem vec104CumF_fSmall_le_linear (n : Nat) :
    vec104CumF fSmall (vecCap4Of n) ≤ 416 * n := by
  refine Nat.le_trans (vec104CumF_mono_fn ?_ (vecCap4Of n)) (vec104CumF_fTotal_le_linear n)
  intro c
  unfold fSmall fTotal
  split_ifs <;> omega

private theorem vecCap4Of_le_two_mul_add_four (n : Nat) :
    vecCap4Of n ≤ 2 * n + 4 := by
  by_cases h5 : 5 ≤ n
  · have h := vecCap4Of_le_two_mul_sub_two h5
    omega
  · have hle4 : n ≤ 4 := by omega
    have h := vecCap4Of_le_four_mul_pow 0 (by simpa using hle4)
    omega

private theorem vec104CumF_at_8 :
    vec104CumF fOther 8 = 1 ∧
    vec104CumF fRealloc 8 = 1 ∧
    vec104CumF fSmall 8 = 1248 ∧
    vec104CumF fTotal 8 = 1248 := by
  have h8 : (8 : Nat) = 4 * 2 ^ 1 := rfl
  rw [h8, vec104CumF_pow2_eq, vec104CumF_pow2_eq, vec104CumF_pow2_eq, vec104CumF_pow2_eq]
  decide

private theorem vec104CumF_at_2048 :
    vec104CumF fOther 2048 = 1 ∧
    vec104CumF fRealloc 2048 = 9 ∧
    vec104CumF fSmall 2048 = 212576 := by
  have h2048 : (2048 : Nat) = 4 * 2 ^ 9 := rfl
  rw [h2048, vec104CumF_pow2_eq, vec104CumF_pow2_eq, vec104CumF_pow2_eq]
  decide

private theorem isPow2Cap4_8 : IsPow2Cap4 8 := Or.inr ⟨1, by decide⟩
private theorem isPow2Cap4_2048 : IsPow2Cap4 2048 := Or.inr ⟨9, by decide⟩

/-! ## 4. `chainMergeEvents` Bounds on `ChainG.Ok` -/

private def isKeyChainField : ChainField → Bool
  | .key _ => true
  | _ => false

private def nonKeyCount (xs : List ChainField) : Nat :=
  xs.countP (fun fl => !isKeyChainField fl)

private theorem chainGAfter_succ (c : ChainG) {i : Nat} (hi : i < c.fields.length) :
    chainGAfter c (i + 1) = (chainGAfter c i).apply (c.fields[i]'hi) := by
  unfold chainGAfter
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

private theorem chainDoneEvents_stats {c : ChainG} (hc : c.Ok) (i : Nat)
    (hi : i ≤ c.fields.length) :
    let m := (chainGAfter c i).keys.length
    let nk := nonKeyCount (c.fields.take i)
    tinyAllocCount (chainDoneEvents c i) = 2 * nk + 2 * m ∧
    otherAllocCount (chainDoneEvents c i) = vec104CumF fOther (vecCap4Of m) ∧
    reallocCount (chainDoneEvents c i) = vec104CumF fRealloc (vecCap4Of m) ∧
    deserSmallTotalReq (chainDoneEvents c i) = vec104CumF fSmall (vecCap4Of m) ∧
    totalStepReq (chainDoneEvents c i) ≤ 66 * nk + 64 * m + vec104CumF fTotal (vecCap4Of m) ∧
    ∀ ev ∈ chainDoneEvents c i,
      eventStepReq ev ≤ max 33 (vecCap4Of m * 104) ∧ eventStepAlign ev ≤ 16 := by
  induction i with
  | zero =>
    simp [chainDoneEvents, chainGAfter, ChainG.empty, nonKeyCount, vec104CumF_zero,
      tinyAllocCount, otherAllocCount, reallocCount, deserSmallTotalReq, totalStepReq]
  | succ i ih =>
    have hlt : i < c.fields.length := by omega
    obtain ⟨ihT, ihO, ihR, ihS, ihTot, ihMax⟩ := ih (Nat.le_of_lt hlt)
    have hmem : c.fields[i]'hlt ∈ c.fields := List.getElem_mem hlt
    have hfb : ChainFieldBytesOk (c.fields[i]'hlt) := mem_fields_bytes_le_33 hc hmem
    have hdone : chainDoneEvents c (i + 1) =
        chainDoneEvents c i ++
          chainFieldStepEvents (chainGAfter c i).keys.length (c.fields[i]'hlt) := by
      simp [chainDoneEvents, hlt]
    have htake : c.fields.take (i + 1) = c.fields.take i ++ [c.fields[i]'hlt] :=
      List.take_succ_eq_append_getElem hlt
    rw [hdone, chainGAfter_succ c hlt, htake]
    generalize hfl : c.fields[i]'hlt = fl at hfb ⊢
    cases fl with
    | srk b =>
      have hb : b.length = 33 := hfb
      obtain ⟨bT, bO, bR, bS, bTot, bMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
      have hnk : nonKeyCount (c.fields.take i ++ [.srk b]) = nonKeyCount (c.fields.take i) + 1 := by
        simp [nonKeyCount, List.countP_append, isKeyChainField]
      have hmk : ((chainGAfter c i).apply (.srk b)).keys.length = (chainGAfter c i).keys.length := rfl
      simp only [chainFieldStepEvents, hnk, hmk, tinyAllocCount_append, otherAllocCount_append,
        reallocCount_append, deserSmallTotalReq_append, totalStepReq_append]
      refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
      intro ev hev
      rcases List.mem_append.mp hev with h1 | h2
      · exact ihMax ev h1
      · obtain ⟨hr, ha⟩ := bMax ev h2
        exact ⟨by omega, ha⟩
    | priv b =>
      have hb : b.length = 32 := hfb
      obtain ⟨bT, bO, bR, bS, bTot, bMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
      have hnk : nonKeyCount (c.fields.take i ++ [.priv b]) = nonKeyCount (c.fields.take i) + 1 := by
        simp [nonKeyCount, List.countP_append, isKeyChainField]
      have hmk : ((chainGAfter c i).apply (.priv b)).keys.length = (chainGAfter c i).keys.length := rfl
      simp only [chainFieldStepEvents, hnk, hmk, tinyAllocCount_append, otherAllocCount_append,
        reallocCount_append, deserSmallTotalReq_append, totalStepReq_append]
      refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
      intro ev hev
      rcases List.mem_append.mp hev with h1 | h2
      · exact ihMax ev h1
      · obtain ⟨hr, ha⟩ := bMax ev h2
        exact ⟨by omega, ha⟩
    | ck idx key =>
      have hb : key.length = 32 := hfb
      obtain ⟨bT, bO, bR, bS, bTot, bMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < key.length) (by omega : key.length ≤ 33)
      have hnk : nonKeyCount (c.fields.take i ++ [.ck idx key]) = nonKeyCount (c.fields.take i) + 1 := by
        simp [nonKeyCount, List.countP_append, isKeyChainField]
      have hmk : ((chainGAfter c i).apply (.ck idx key)).keys.length = (chainGAfter c i).keys.length := rfl
      simp only [chainFieldStepEvents, hnk, hmk, tinyAllocCount_append, otherAllocCount_append,
        reallocCount_append, deserSmallTotalReq_append, totalStepReq_append]
      refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
      intro ev hev
      rcases List.mem_append.mp hev with h1 | h2
      · exact ihMax ev h1
      · obtain ⟨hr, ha⟩ := bMax ev h2
        exact ⟨by omega, ha⟩
    | key mkg =>
      have hb : mkg.seed.length = 32 := hfb
      set lenMk := (chainGAfter c i).keys.length
      have hnk : nonKeyCount (c.fields.take i ++ [.key mkg]) = nonKeyCount (c.fields.take i) := by
        simp [nonKeyCount, List.countP_append, isKeyChainField]
      have hmk : ((chainGAfter c i).apply (.key mkg)).keys.length = lenMk + 1 := by
        simp [ChainG.apply, lenMk]
      have hb32 : bytesMergeEvents 0 mkg.seed.length = [.alloc 32, .alloc 32, .free 1 32] := by
        rw [hb, bytesMergeEvents_zero_pos (by decide : 0 < 32)]
        rfl
      have hbT : tinyAllocCount (bytesMergeEvents 0 mkg.seed.length) = 2 := by rw [hb32]; decide
      have hbO : otherAllocCount (bytesMergeEvents 0 mkg.seed.length) = 0 := by rw [hb32]; decide
      have hbR : reallocCount (bytesMergeEvents 0 mkg.seed.length) = 0 := by rw [hb32]; decide
      have hbS : deserSmallTotalReq (bytesMergeEvents 0 mkg.seed.length) = 0 := by rw [hb32]; decide
      have hbTot : totalStepReq (bytesMergeEvents 0 mkg.seed.length) = 64 := by rw [hb32]; decide
      have hbMax : ∀ ev ∈ bytesMergeEvents 0 mkg.seed.length, eventStepReq ev ≤ 33 ∧ eventStepAlign ev ≤ 16 := by
        rw [hb32]
        intro ev hev
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
        rcases hev with rfl | rfl | rfl <;> decide
      have hpushO := vec104CumF_push fOther lenMk
      have hpushR := vec104CumF_push fRealloc lenMk
      have hpushS := vec104CumF_push fSmall lenMk
      have hpushTot := vec104CumF_push fTotal lenMk
      obtain ⟨gT, gO, gR, gS, gTot, gMax⟩ := vec104GrowEvents_step_stats (vecCap4Of_pow2 lenMk)
      have hcapMono : vecCap4Of lenMk ≤ vecCap4Of (lenMk + 1) := vecCap4Of_mono (Nat.le_succ lenMk)
      dsimp only []
      rw [hnk, hmk]
      by_cases hgrow : lenMk < vecCap4Of lenMk
      · have hstep : chainFieldStepEvents lenMk (.key mkg) = bytesMergeEvents 0 mkg.seed.length := by
          simp [chainFieldStepEvents, hgrow]
        simp only [hgrow, ↓reduceIte] at hpushO hpushR hpushS hpushTot
        rw [hstep]
        simp only [tinyAllocCount_append, otherAllocCount_append, reallocCount_append,
          deserSmallTotalReq_append, totalStepReq_append]
        refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
        intro ev hev
        rcases List.mem_append.mp hev with h1 | h2
        · obtain ⟨hr, ha⟩ := ihMax ev h1
          have hmul : vecCap4Of lenMk * 104 ≤ vecCap4Of (lenMk + 1) * 104 :=
            Nat.mul_le_mul_right 104 hcapMono
          exact ⟨by omega, ha⟩
        · obtain ⟨hr, ha⟩ := hbMax ev h2
          exact ⟨by omega, ha⟩
      · have hstep : chainFieldStepEvents lenMk (.key mkg) =
            bytesMergeEvents 0 mkg.seed.length ++ vec104GrowEvents (vecCap4Of lenMk) := by
          simp [chainFieldStepEvents, hgrow]
        simp only [hgrow, ↓reduceIte] at hpushO hpushR hpushS hpushTot
        have hcapEq : vecCap4Of (lenMk + 1) = vecCap4Next (vecCap4Of lenMk) := by
          rw [vecCap4Of_succ, vecCap4Push]
          simp [hgrow]
        rw [hstep]
        simp only [tinyAllocCount_append, otherAllocCount_append, reallocCount_append,
          deserSmallTotalReq_append, totalStepReq_append]
        refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
        intro ev hev
        rcases List.mem_append.mp hev with h1 | h23
        · obtain ⟨hr, ha⟩ := ihMax ev h1
          have hmul : vecCap4Of lenMk * 104 ≤ vecCap4Of (lenMk + 1) * 104 :=
            Nat.mul_le_mul_right 104 hcapMono
          exact ⟨by omega, ha⟩
        · rcases List.mem_append.mp h23 with h2 | h3
          · obtain ⟨hr, ha⟩ := hbMax ev h2
            exact ⟨by omega, ha⟩
          · obtain ⟨hr, ha⟩ := gMax ev h3
            rw [← hcapEq] at hr
            exact ⟨by omega, ha⟩

private theorem nonKeyCount_map_key (ks : List MessageKeyGenerator) :
    nonKeyCount (ks.map ChainField.key) = 0 := by
  unfold nonKeyCount
  simp [isKeyChainField]

private theorem nonKeyCount_fields_le_three (c : ChainG) :
    nonKeyCount c.fields ≤ 3 := by
  have h4 : (c.keys.map ChainField.key).countP (fun fl => !isKeyChainField fl) = 0 :=
    nonKeyCount_map_key c.keys
  unfold ChainG.fields nonKeyCount
  simp only [List.countP_append, h4, Nat.add_zero]
  rcases c.ck with _ | ⟨_, _⟩ <;> split_ifs <;> simp [isKeyChainField]

private theorem chainMergeEvents_bounds {c : ChainG} (hc : c.Ok) :
    tinyAllocCount (chainMergeEvents c) ≤ 6 + 2 * c.keys.length ∧
    otherAllocCount (chainMergeEvents c) ≤ 1 ∧
    reallocCount (chainMergeEvents c) ≤ 9 ∧
    deserSmallTotalReq (chainMergeEvents c) ≤ min (416 * c.keys.length) 212576 ∧
    totalStepReq (chainMergeEvents c) ≤ 198 + 480 * c.keys.length ∧
    ∀ ev ∈ chainMergeEvents c,
      eventStepReq ev ≤ 208 * c.keys.length + 416 ∧ eventStepAlign ev ≤ 16 := by
  unfold chainMergeEvents
  have hstats := chainDoneEvents_stats hc c.fields.length (Nat.le_refl _)
  rw [chainGAfter_fields c, List.take_length] at hstats
  obtain ⟨hT, hO, hR, hS, hTot, hMax⟩ := hstats
  have hnk := nonKeyCount_fields_le_three c
  have hk_le : c.keys.length ≤ 2000 := by
    have hm := hc.2.2.2.2
    have h2000 : maxMessageKeys = 2000 := by decide
    omega
  have hcap2048 : vecCap4Of c.keys.length ≤ 2048 :=
    vecCap4Of_le_four_mul_pow 9 (by omega)
  have hO_le := vec104CumF_le_of_pow2 fOther (vecCap4Of_pow2 c.keys.length) isPow2Cap4_2048 hcap2048
  have hR_le := vec104CumF_le_of_pow2 fRealloc (vecCap4Of_pow2 c.keys.length) isPow2Cap4_2048 hcap2048
  have hS_abs := vec104CumF_le_of_pow2 fSmall (vecCap4Of_pow2 c.keys.length) isPow2Cap4_2048 hcap2048
  have hS_lin := vec104CumF_fSmall_le_linear c.keys.length
  have hTot_lin := vec104CumF_fTotal_le_linear c.keys.length
  have hc2048 := vec104CumF_at_2048
  have hcapLin := vecCap4Of_le_two_mul_add_four c.keys.length
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro ev hev
  obtain ⟨hr, ha⟩ := hMax ev hev
  exact ⟨by omega, ha⟩

private theorem chainMergeEvents_sender_bounds {c : ChainG} (hc : c.Ok) (hk0 : c.keys = []) :
    tinyAllocCount (chainMergeEvents c) ≤ 6 ∧
    otherAllocCount (chainMergeEvents c) = 0 ∧
    reallocCount (chainMergeEvents c) = 0 ∧
    deserSmallTotalReq (chainMergeEvents c) = 0 ∧
    totalStepReq (chainMergeEvents c) ≤ 198 ∧
    ∀ ev ∈ chainMergeEvents c, eventStepReq ev ≤ 33 ∧ eventStepAlign ev ≤ 16 := by
  unfold chainMergeEvents
  have hstats := chainDoneEvents_stats hc c.fields.length (Nat.le_refl _)
  rw [chainGAfter_fields c, List.take_length, hk0] at hstats
  simp only [List.length_nil] at hstats
  obtain ⟨hT, hO, hR, hS, hTot, hMax⟩ := hstats
  have hnk := nonKeyCount_fields_le_three c
  simp only [vecCap4Of, vec104CumF_zero] at hO hR hS hTot hMax
  refine ⟨by omega, hO, hR, hS, by omega, ?_⟩
  intro ev hev
  obtain ⟨hr, ha⟩ := hMax ev hev
  exact ⟨by omega, ha⟩

/-! ## 5. Wire-Length Lower Bounds (`fl.enc.length`) -/

private theorem one_le_encodeVarint_length (v : BitVec 64) :
    1 ≤ (encodeVarint v).length := by
  unfold encodeVarint encodeVarintAux
  split <;> simp

private theorem one_le_encodeKey_length (tag : Nat) (wt : WireType) :
    1 ≤ (encodeKey tag wt).length :=
  one_le_encodeVarint_length _

private theorem lenField_length_ge (tag : Nat) (b : List (BitVec 8)) :
    b.length + 2 ≤ (lenField tag b).length := by
  unfold lenField
  have h1 := one_le_encodeKey_length tag .lengthDelimited
  have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 b.length)
  simp only [List.length_append]
  omega

private theorem bytesField_length_ge_of_pos (tag : Nat) {b : List (BitVec 8)} (hpos : 0 < b.length) :
    b.length + 2 ≤ (bytesField tag b).length := by
  unfold bytesField
  have hne : b ≠ [] := by
    intro h
    rw [h] at hpos
    cases hpos
  simp only [hne, ↓reduceIte]
  exact lenField_length_ge tag b

private theorem lenField_encMessageKey_length_ge {mk : MessageKeyGenerator}
    (hseed : mk.seed.length = 32) :
    36 ≤ (lenField 4 (encMessageKey mk)).length := by
  have h0 := lenField_length_ge 4 (encMessageKey mk)
  have heq : (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
    simp [encMessageKey]
  have h2 := bytesField_length_ge_of_pos 5 (b := mk.seed) (by omega)
  omega

private theorem flatten_encMessageKeys_length_ge (mks : List MessageKeyGenerator)
    (hseeds : ∀ mk ∈ mks, mk.seed.length = 32) :
    36 * mks.length ≤ ((mks.map fun mk => lenField 4 (encMessageKey mk)).flatten).length := by
  induction mks with
  | nil => simp
  | cons mk mks ih =>
    have hmk := lenField_encMessageKey_length_ge (hseeds mk List.mem_cons_self)
    have hmks := ih (fun m hm => hseeds m (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

private theorem chainG_enc_length_ge {c : ChainG} (hc : c.Ok) :
    35 + 36 * c.keys.length ≤ c.enc.length := by
  unfold ChainG.enc
  have hsrk := bytesField_length_ge_of_pos 1 (b := c.srk) (by have := hc.1; omega)
  have h1 := hc.1
  have hkeys := flatten_encMessageKeys_length_ge c.keys hc.2.2.2.1
  simp only [List.length_append]
  omega

private theorem genFieldQ_recv_enc_length_ge {c : ChainG} (hc : c.Ok) :
    37 + 36 * c.keys.length ≤ (GenFieldQ.base (.recv c)).enc.length := by
  have heq : (GenFieldQ.base (.recv c)).enc = lenField 7 c.enc := by
    simp [GenFieldQ.enc, GenFieldQ.tag, GenField.tag,
      GenFieldQ.wt, GenField.wt, GenFieldQ.payload, GenField.payload,
      ChainG.payload, lenField, List.append_assoc]
  rw [heq]
  have h0 := lenField_length_ge 7 c.enc
  have h1 := chainG_enc_length_ge hc
  omega

private theorem genFieldQ_sender_enc_length_ge {c : ChainG} (hc : c.Ok) :
    37 ≤ (GenFieldQ.base (.sender c)).enc.length := by
  have heq : (GenFieldQ.base (.sender c)).enc = lenField 6 c.enc := by
    simp [GenFieldQ.enc, GenFieldQ.tag, GenField.tag,
      GenFieldQ.wt, GenField.wt, GenFieldQ.payload, GenField.payload,
      ChainG.payload, lenField, List.append_assoc]
  rw [heq]
  have h0 := lenField_length_ge 6 c.enc
  have h1 := chainG_enc_length_ge hc
  omega

private theorem genFieldQ_kyber_enc_length_ge (i : BitVec 32) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) :
    1573 ≤ (GenFieldQ.kyber i ct).enc.length := by
  have hbody : 1571 ≤ (kyberBody i ct).length := by
    unfold kyberBody
    have h3 := lenField_length_ge 2 ct
    simp only [List.length_append]
    omega
  unfold GenFieldQ.enc GenFieldQ.tag GenFieldQ.wt GenFieldQ.payload
  have h1 := one_le_encodeKey_length 14 .lengthDelimited
  have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 (kyberBody i ct).length)
  simp only [List.length_append]
  omega

private theorem genFieldQ_pq_enc_length_ge (b : List (BitVec 8)) :
    b.length + 2 ≤ (GenFieldQ.pq b).enc.length := by
  unfold GenFieldQ.enc GenFieldQ.tag GenFieldQ.wt GenFieldQ.payload
  have h1 := one_le_encodeKey_length 15 .lengthDelimited
  have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 b.length)
  simp only [List.length_append]
  omega

private theorem pendingIdBody_length_ge (i : BitVec 32) {b : List (BitVec 8)} (hb : b.length = 33) :
    35 ≤ (pendingIdBody i b).length := by
  unfold pendingIdBody
  have h3 := lenField_length_ge 2 b
  simp only [List.length_append]
  omega

private theorem pendingSpkBody_length_ge (pid : Option (BitVec 32)) {b : List (BitVec 8)}
    (spk : BitVec 32) (hb : b.length = 33) :
    35 ≤ (pendingSpkBody pid b spk).length := by
  unfold pendingSpkBody
  have h3 := lenField_length_ge 2 b
  simp only [List.length_append]
  omega

private theorem genFieldQ_basic32_enc_length_ge {fl : GenFieldQ} (hOk : fl.Ok) :
    (∀ b, fl = .base (.lik b) → 35 ≤ fl.enc.length) ∧
    (∀ b, fl = .base (.rik b) → 35 ≤ fl.enc.length) ∧
    (∀ b, fl = .base (.root b) → 34 ≤ fl.enc.length) ∧
    (∀ b, fl = .base (.pending b) → 37 ≤ fl.enc.length) ∧
    (∀ i b, fl = .pendingId i b → 37 ≤ fl.enc.length) ∧
    (∀ pid b spk, fl = .pendingSpk pid b spk → 37 ≤ fl.enc.length) ∧
    (∀ b, fl = .abk b → 35 ≤ fl.enc.length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro b rfl
    have hb : b.length = 33 := hOk
    have h1 := one_le_encodeKey_length 2 .lengthDelimited
    have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 b.length)
    simp only [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload,
      GenField.tag, GenField.wt, GenField.payload, List.length_append]
    omega
  · rintro b rfl
    have hb : b.length = 33 := hOk
    have h1 := one_le_encodeKey_length 3 .lengthDelimited
    have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 b.length)
    simp only [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload,
      GenField.tag, GenField.wt, GenField.payload, List.length_append]
    omega
  · rintro b rfl
    have hb : b.length = 32 := hOk
    have h1 := one_le_encodeKey_length 4 .lengthDelimited
    have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 b.length)
    simp only [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload,
      GenField.tag, GenField.wt, GenField.payload, List.length_append]
    omega
  · rintro b rfl
    have hb : b.length = 33 := hOk
    have h1 := one_le_encodeKey_length 9 .lengthDelimited
    have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 (lenField 2 b).length)
    have h3 := lenField_length_ge 2 b
    simp only [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload,
      GenField.tag, GenField.wt, GenField.payload, List.length_append]
    omega
  · rintro i b rfl
    have hb : b.length = 33 := hOk
    have h1 := one_le_encodeKey_length 9 .lengthDelimited
    have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 (pendingIdBody i b).length)
    have h3 := pendingIdBody_length_ge i hb
    simp only [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload, List.length_append]
    omega
  · rintro pid b spk rfl
    have hb : b.length = 33 := hOk.1
    have h1 := one_le_encodeKey_length 9 .lengthDelimited
    have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 (pendingSpkBody pid b spk).length)
    have h3 := pendingSpkBody_length_ge pid spk hb
    simp only [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload, List.length_append]
    omega
  · rintro b rfl
    have hb : b.length = 33 := hOk
    have h1 := one_le_encodeKey_length 13 .lengthDelimited
    have h2 := one_le_encodeVarint_length (BitVec.ofNat 64 b.length)
    simp only [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload, List.length_append]
    omega

/-! ## 6. Decomposition of `fieldsEventsAux` into `fieldInnerEvents` + Outer `receiver_chains` -/

private def fieldInnerEvents : GenFieldQ → List AllocEvent
  | .base (.sender c) => chainMergeEvents c
  | .base (.recv c) => chainMergeEvents c
  | fl => bytesMergeEvents 0 (basicFieldByteLen fl)

private theorem fieldInnerEvents_pointwise_linear {fl : GenFieldQ} (hOk : fl.Ok) :
    deserSmallTotalReq (fieldInnerEvents fl) ≤ 12 * fl.enc.length ∧
    totalStepReq (fieldInnerEvents fl) ≤ 14 * fl.enc.length ∧
    ∀ ev ∈ fieldInnerEvents fl,
      eventStepReq ev ≤ 6 * fl.enc.length + 4096 ∧ eventStepAlign ev ≤ 16 := by
  have hb32 := genFieldQ_basic32_enc_length_ge hOk
  cases fl with
  | base f =>
    cases f with
    | version v =>
      simp [fieldInnerEvents, basicFieldByteLen, deserSmallTotalReq, totalStepReq]
    | prevCounter v =>
      simp [fieldInnerEvents, basicFieldByteLen, deserSmallTotalReq, totalStepReq]
    | lik b =>
      have hw := hb32.1 b rfl
      have hb : b.length = 33 := hOk
      obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
      simp only [fieldInnerEvents, basicFieldByteLen]
      refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
    | rik b =>
      have hw := hb32.2.1 b rfl
      have hb : b.length = 33 := hOk
      obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
      simp only [fieldInnerEvents, basicFieldByteLen]
      refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
    | root b =>
      have hw := hb32.2.2.1 b rfl
      have hb : b.length = 32 := hOk
      obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
      simp only [fieldInnerEvents, basicFieldByteLen]
      refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
    | sender c =>
      have hcOk : c.Ok := hOk.1
      have hk0 : c.keys = [] := hOk.2.2.2
      have hw := genFieldQ_sender_enc_length_ge hcOk
      obtain ⟨_, _, _, hS, hTot, hMax⟩ := chainMergeEvents_sender_bounds hcOk hk0
      simp only [fieldInnerEvents]
      refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
    | recv c =>
      have hcOk : c.Ok := hOk.1
      have hw := genFieldQ_recv_enc_length_ge hcOk
      obtain ⟨_, _, _, hS, hTot, hMax⟩ := chainMergeEvents_bounds hcOk
      simp only [fieldInnerEvents]
      refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
    | pending b =>
      have hw := hb32.2.2.2.1 b rfl
      have hb : b.length = 33 := hOk
      obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
      simp only [fieldInnerEvents, basicFieldByteLen]
      refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
  | pendingId i b =>
    have hw := hb32.2.2.2.2.1 i b rfl
    have hb : b.length = 33 := hOk
    obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
    simp only [fieldInnerEvents, basicFieldByteLen]
    refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
  | pendingSpk pid b spk =>
    have hw := hb32.2.2.2.2.2.1 pid b spk rfl
    have hb : b.length = 33 := hOk.1
    obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
    simp only [fieldInnerEvents, basicFieldByteLen]
    refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
  | remReg _ =>
    simp [fieldInnerEvents, basicFieldByteLen, deserSmallTotalReq, totalStepReq]
  | locReg _ =>
    simp [fieldInnerEvents, basicFieldByteLen, deserSmallTotalReq, totalStepReq]
  | abk b =>
    have hw := hb32.2.2.2.2.2.2 b rfl
    have hb : b.length = 33 := hOk
    obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_tiny_exact (by omega : 0 < b.length) (by omega : b.length ≤ 33)
    simp only [fieldInnerEvents, basicFieldByteLen]
    refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
  | kyber i ct =>
    have hct : ct.length = 1569 := hOk
    have hw := genFieldQ_kyber_enc_length_ge i hct
    obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_1569_exact
    simp only [fieldInnerEvents, basicFieldByteLen, hct]
    refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩
  | pq b =>
    have hw := genFieldQ_pq_enc_length_ge b
    obtain ⟨_, _, _, hS, hTot, hMax⟩ := bytesMergeEvents_general_bounds b.length
    simp only [fieldInnerEvents, basicFieldByteLen]
    refine ⟨by omega, by omega, fun ev hev => ⟨by have := (hMax ev hev).1; omega, (hMax ev hev).2⟩⟩

private theorem fieldsEventsAux_stats (n : Nat) (xs : List GenFieldQ) :
    tinyAllocCount (fieldsEventsAux (vecCap4Of n) n xs) =
      (xs.map (fun fl => tinyAllocCount (fieldInnerEvents fl))).sum ∧
    otherAllocCount (fieldsEventsAux (vecCap4Of n) n xs) + vec104CumF fOther (vecCap4Of n) =
      (xs.map (fun fl => otherAllocCount (fieldInnerEvents fl))).sum +
        vec104CumF fOther (vecCap4Of (n + recvCount xs)) ∧
    reallocCount (fieldsEventsAux (vecCap4Of n) n xs) + vec104CumF fRealloc (vecCap4Of n) =
      (xs.map (fun fl => reallocCount (fieldInnerEvents fl))).sum +
        vec104CumF fRealloc (vecCap4Of (n + recvCount xs)) ∧
    deserSmallTotalReq (fieldsEventsAux (vecCap4Of n) n xs) + vec104CumF fSmall (vecCap4Of n) =
      (xs.map (fun fl => deserSmallTotalReq (fieldInnerEvents fl))).sum +
        vec104CumF fSmall (vecCap4Of (n + recvCount xs)) ∧
    totalStepReq (fieldsEventsAux (vecCap4Of n) n xs) + vec104CumF fTotal (vecCap4Of n) =
      (xs.map (fun fl => totalStepReq (fieldInnerEvents fl))).sum +
        vec104CumF fTotal (vecCap4Of (n + recvCount xs)) ∧
    ∀ ev ∈ fieldsEventsAux (vecCap4Of n) n xs,
      (∃ fl ∈ xs, ev ∈ fieldInnerEvents fl) ∨
      (eventStepReq ev ≤ vecCap4Of (n + recvCount xs) * 104 ∧ eventStepAlign ev ≤ 16) := by
  induction xs generalizing n with
  | nil =>
    simp [fieldsEventsAux, recvCount, tinyAllocCount, otherAllocCount, reallocCount,
      deserSmallTotalReq, totalStepReq]
  | cons fl rest ih =>
    by_cases hrecv : ∃ c, fl = .base (.recv c)
    · rcases hrecv with ⟨c, rfl⟩
      have hcap : nextCapRecv (vecCap4Of n) n (.base (.recv c)) = vecCap4Of (n + 1) :=
        nextCapRecv_eq_vecCap4Of n (.base (.recv c))
      have hcnt : n + 1 + recvCount rest = n + recvCount (.base (.recv c) :: rest) := by
        simp only [recvCount]; omega
      obtain ⟨ihT, ihO, ihR, ihS, ihTot, ihMax⟩ := ih (n + 1)
      rw [hcnt] at ihO ihR ihS ihTot ihMax
      have hstepAux : fieldsEventsAux (vecCap4Of n) n (.base (.recv c) :: rest) =
          mergeFieldQEvents (vecCap4Of n) n (.base (.recv c)) ++
            fieldsEventsAux (vecCap4Of (n + 1)) (n + 1) rest := by
        simp only [fieldsEventsAux, hcap]
      rw [hstepAux]
      simp only [List.map_cons, List.sum_cons]
      have hpushO := vec104CumF_push fOther n
      have hpushR := vec104CumF_push fRealloc n
      have hpushS := vec104CumF_push fSmall n
      have hpushTot := vec104CumF_push fTotal n
      obtain ⟨gT, gO, gR, gS, gTot, gMax⟩ := vec104GrowEvents_step_stats (vecCap4Of_pow2 n)
      have hleCap := le_vecCap4Of n
      by_cases heq : n = vecCap4Of n
      · have hnlt : ¬ (n < vecCap4Of n) := by omega
        have hmEq : mergeFieldQEvents (vecCap4Of n) n (.base (.recv c)) =
            fieldInnerEvents (.base (.recv c)) ++ vec104GrowEvents (vecCap4Of n) := by
          dsimp only [mergeFieldQEvents, fieldInnerEvents]
          split_ifs
          rfl
        simp only [hnlt, ↓reduceIte] at hpushO hpushR hpushS hpushTot
        rw [hmEq]
        simp only [tinyAllocCount_append, otherAllocCount_append, reallocCount_append,
          deserSmallTotalReq_append, totalStepReq_append]
        have hcapNext : vecCap4Next (vecCap4Of n) ≤ vecCap4Of (n + recvCount (.base (.recv c) :: rest)) := by
          have h1 : vecCap4Of (n + 1) = vecCap4Next (vecCap4Of n) := by
            rw [vecCap4Of_succ, vecCap4Push]
            simp only [hnlt, ↓reduceIte]
          rw [← h1]
          exact vecCap4Of_mono (by simp only [recvCount]; omega)
        refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
        intro ev hev
        rcases List.mem_append.mp hev with h12 | h3
        · rcases List.mem_append.mp h12 with h1 | h2
          · exact Or.inl ⟨.base (.recv c), List.mem_cons_self, h1⟩
          · obtain ⟨hr, ha⟩ := gMax ev h2
            exact Or.inr ⟨Nat.le_trans hr (Nat.mul_le_mul_right 104 hcapNext), ha⟩
        · rcases ihMax ev h3 with ⟨fl', hfl', hev'⟩ | hcap'
          · exact Or.inl ⟨fl', List.mem_cons_of_mem _ hfl', hev'⟩
          · exact Or.inr hcap'
      · have hlt : n < vecCap4Of n := by omega
        have hmEq : mergeFieldQEvents (vecCap4Of n) n (.base (.recv c)) =
            fieldInnerEvents (.base (.recv c)) := by
          dsimp only [mergeFieldQEvents, fieldInnerEvents]
          split_ifs
          simp only [List.append_nil]
        simp only [hlt, ↓reduceIte] at hpushO hpushR hpushS hpushTot
        rw [hmEq]
        simp only [tinyAllocCount_append, otherAllocCount_append, reallocCount_append,
          deserSmallTotalReq_append, totalStepReq_append]
        refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
        intro ev hev
        rcases List.mem_append.mp hev with h1 | h2
        · exact Or.inl ⟨.base (.recv c), List.mem_cons_self, h1⟩
        · rcases ihMax ev h2 with ⟨fl', hfl', hev'⟩ | hcap'
          · exact Or.inl ⟨fl', List.mem_cons_of_mem _ hfl', hev'⟩
          · exact Or.inr hcap'
    · have hcnt : recvCount (fl :: rest) = recvCount rest := by
        cases fl with
        | base f =>
          cases f with
          | recv c => exact False.elim (hrecv ⟨c, rfl⟩)
          | _ => rfl
        | _ => rfl
      have hstepAux : fieldsEventsAux (vecCap4Of n) n (fl :: rest) =
          fieldInnerEvents fl ++ fieldsEventsAux (vecCap4Of n) n rest := by
        cases fl with
        | base f =>
          cases f with
          | recv c => exact False.elim (hrecv ⟨c, rfl⟩)
          | _ => rfl
        | _ => rfl
      obtain ⟨ihT, ihO, ihR, ihS, ihTot, ihMax⟩ := ih n
      rw [hstepAux, hcnt]
      simp only [List.map_cons, List.sum_cons, tinyAllocCount_append, otherAllocCount_append,
        reallocCount_append, deserSmallTotalReq_append, totalStepReq_append]
      refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
      intro ev hev
      rcases List.mem_append.mp hev with h1 | h2
      · exact Or.inl ⟨fl, List.mem_cons_self, h1⟩
      · rcases ihMax ev h2 with ⟨fl', hfl', hev'⟩ | hcap'
        · exact Or.inl ⟨fl', List.mem_cons_of_mem _ hfl', hev'⟩
        · exact Or.inr hcap'

/-! ## 7. Compositional Piece Bounds Over `genFieldsQ s` -/

private theorem flatMap_enc_length_eq_sum (xs : List GenFieldQ) :
    (xs.flatMap GenFieldQ.enc).length = (xs.map (fun fl => fl.enc.length)).sum := by
  induction xs with
  | nil => rfl
  | cons fl xs ih => simp [List.flatMap_cons, ih]

private theorem sum_linear_small_total {xs : List GenFieldQ} (hOk : ∀ fl ∈ xs, fl.Ok) :
    (xs.map (fun fl => deserSmallTotalReq (fieldInnerEvents fl))).sum ≤
      12 * (xs.map (fun fl => fl.enc.length)).sum ∧
    (xs.map (fun fl => totalStepReq (fieldInnerEvents fl))).sum ≤
      14 * (xs.map (fun fl => fl.enc.length)).sum := by
  induction xs with
  | nil => simp
  | cons fl xs ih =>
    obtain ⟨hS, hTot, _⟩ := fieldInnerEvents_pointwise_linear (hOk fl List.mem_cons_self)
    obtain ⟨ihS, ihTot⟩ := ih (fun f hf => hOk f (List.mem_cons_of_mem _ hf))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem mem_enc_le_sum {xs : List GenFieldQ} {fl : GenFieldQ} (hmem : fl ∈ xs) :
    fl.enc.length ≤ (xs.map (fun f => f.enc.length)).sum := by
  induction xs with
  | nil => cases hmem
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hmem with rfl | htl
    · omega
    · have := ih htl
      omega

private def PieceBounded (tB oB rB sB : Nat) (piece : List GenFieldQ) : Prop :=
  (∀ fl ∈ piece, fl.Ok) →
    (piece.map (fun fl => tinyAllocCount (fieldInnerEvents fl))).sum ≤ tB ∧
    (piece.map (fun fl => otherAllocCount (fieldInnerEvents fl))).sum ≤ oB ∧
    (piece.map (fun fl => reallocCount (fieldInnerEvents fl))).sum ≤ rB ∧
    (piece.map (fun fl => deserSmallTotalReq (fieldInnerEvents fl))).sum ≤ sB

private theorem pieceBounded_nil : PieceBounded 0 0 0 0 [] := fun _ => by simp

private theorem pieceBounded_singleton {tB oB rB sB : Nat} {fl : GenFieldQ}
    (h : fl.Ok →
      tinyAllocCount (fieldInnerEvents fl) ≤ tB ∧
      otherAllocCount (fieldInnerEvents fl) ≤ oB ∧
      reallocCount (fieldInnerEvents fl) ≤ rB ∧
      deserSmallTotalReq (fieldInnerEvents fl) ≤ sB) :
    PieceBounded tB oB rB sB [fl] := by
  intro hOk
  obtain ⟨h1, h2, h3, h4⟩ := h (hOk fl List.mem_cons_self)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact ⟨h1, h2, h3, h4⟩

private theorem pieceBounded_mono {t₁ t₂ o₁ o₂ r₁ r₂ s₁ s₂ : Nat} {piece : List GenFieldQ}
    (hp : PieceBounded t₁ o₁ r₁ s₁ piece)
    (ht : t₁ ≤ t₂) (ho : o₁ ≤ o₂) (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    PieceBounded t₂ o₂ r₂ s₂ piece := by
  intro hOk
  obtain ⟨h1, h2, h3, h4⟩ := hp hOk
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem pieceBounded_append {t₁ t₂ o₁ o₂ r₁ r₂ s₁ s₂ : Nat} {xs ys : List GenFieldQ}
    (hx : PieceBounded t₁ o₁ r₁ s₁ xs) (hy : PieceBounded t₂ o₂ r₂ s₂ ys) :
    PieceBounded (t₁ + t₂) (o₁ + o₂) (r₁ + r₂) (s₁ + s₂) (xs ++ ys) := by
  intro hOk
  obtain ⟨x1, x2, x3, x4⟩ := hx (fun fl h => hOk fl (List.mem_append_left _ h))
  obtain ⟨y1, y2, y3, y4⟩ := hy (fun fl h => hOk fl (List.mem_append_right _ h))
  simp only [List.map_append, List.sum_append]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem pb_varint {fl : GenFieldQ} (h : fieldInnerEvents fl = []) :
    PieceBounded 0 0 0 0 [fl] :=
  pieceBounded_singleton fun _ => by
    rw [h]
    simp [tinyAllocCount, otherAllocCount, reallocCount, deserSmallTotalReq]

private theorem pb_tiny33 {fl : GenFieldQ}
    (h : fl.Ok → ∃ n, fieldInnerEvents fl = bytesMergeEvents 0 n ∧ 0 < n ∧ n ≤ 33) :
    PieceBounded 2 0 0 0 [fl] :=
  pieceBounded_singleton fun hOk => by
    obtain ⟨n, heq, hpos, hle⟩ := h hOk
    obtain ⟨h1, h2, h3, h4, _⟩ := bytesMergeEvents_tiny_exact hpos hle
    rw [heq]
    exact ⟨by omega, by omega, by omega, by omega⟩

private theorem pb_pendingFieldQ (o : Option PendingPreKey) :
    PieceBounded 2 0 0 0 (pendingFieldQ o) := by
  unfold pendingFieldQ pendingFieldX
  rcases o with _ | p
  · dsimp only [List.map]
    exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
  · dsimp only
    split_ifs
    · rcases p.preKeyId with _ | i
      · exact pb_tiny33 fun hOk => by
          have hb : p.baseKey.serialize.length = 33 := hOk
          exact ⟨p.baseKey.serialize.length, rfl, by omega, by omega⟩
      · exact pb_tiny33 fun hOk => by
          have hb : p.baseKey.serialize.length = 33 := hOk
          exact ⟨p.baseKey.serialize.length, rfl, by omega, by omega⟩
    · exact pb_tiny33 fun hOk => by
        have hb : p.baseKey.serialize.length = 33 := hOk.1
        exact ⟨p.baseKey.serialize.length, rfl, by omega, by omega⟩

private theorem recvChains_sum_bounds (cs : List ReceiverChain)
    (hOk : ∀ fl ∈ cs.map (fun c => GenFieldQ.base (.recv (recvChainG c))), fl.Ok) :
    let rf := cs.map (fun c => GenFieldQ.base (.recv (recvChainG c)))
    let K := (cs.map (fun c => c.messageKeys.length)).sum
    PieceBounded (6 * cs.length + 2 * K) cs.length (9 * cs.length) (212576 * cs.length) rf ∧
    36 * K ≤ (rf.map (fun fl => fl.enc.length)).sum ∧
    K ≤ 2000 * cs.length := by
  induction cs with
  | nil =>
    exact ⟨pieceBounded_nil, by simp, by simp⟩
  | cons c cs ih =>
    have hcOk : (recvChainG c).Ok := (hOk _ List.mem_cons_self).1
    have hkeys : (recvChainG c).keys = c.messageKeys := rfl
    obtain ⟨cT, cO, cR, cS, _⟩ := chainMergeEvents_bounds hcOk
    have cw := genFieldQ_recv_enc_length_ge hcOk
    have ck_le : c.messageKeys.length ≤ 2000 := by
      have hm := hcOk.2.2.2.2
      rw [hkeys] at hm
      have h2000 : maxMessageKeys = 2000 := by decide
      omega
    rw [hkeys] at cT cw
    obtain ⟨ihPB, ihW, ihK⟩ := ih (fun fl hfl => hOk fl (List.mem_cons_of_mem _ hfl))
    have hcPB : PieceBounded (6 + 2 * c.messageKeys.length) 1 9 212576
        [GenFieldQ.base (.recv (recvChainG c))] :=
      pieceBounded_singleton fun _ => ⟨cT, cO, cR, Nat.le_trans cS (Nat.min_le_right _ _)⟩
    have hcomb := pieceBounded_append hcPB ihPB
    refine ⟨?_, ?_, ?_⟩
    · intro hOkAll
      obtain ⟨h1, h2, h3, h4⟩ := hcomb hOkAll
      simp only [List.singleton_append, List.map_cons, List.sum_cons, List.length_cons] at h1 h2 h3 h4 ⊢
      exact ⟨by omega, by omega, by omega, by omega⟩
    · simp only [List.map_cons, List.sum_cons]
      omega
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

private theorem map_ite_singleton {α β : Type} (p : Prop) [Decidable p] (x : α) (f : α → β) :
    (if p then [] else [x]).map f = if p then [] else [f x] := by
  split_ifs <;> rfl

private theorem genFieldsQ_absolute_and_tiny_bounds
    {s : Session (List (BitVec 8))}
    (hOk : ∀ fl ∈ genFieldsQ s, fl.Ok)
    (hrc : s.state.receiverChains.length ≤ 5) :
    ∃ K : Nat,
      K ≤ 10000 ∧
      36 * K ≤ ((genFieldsQ s).map (fun fl => fl.enc.length)).sum ∧
      ((genFieldsQ s).map (fun fl => tinyAllocCount (fieldInnerEvents fl))).sum ≤ 48 + 2 * K ∧
      ((genFieldsQ s).map (fun fl => otherAllocCount (fieldInnerEvents fl))).sum ≤ 9 ∧
      ((genFieldsQ s).map (fun fl => reallocCount (fieldInnerEvents fl))).sum ≤ 45 ∧
      ((genFieldsQ s).map (fun fl => deserSmallTotalReq (fieldInnerEvents fl))).sum ≤ 1336352 := by
  set pVer : List GenFieldQ :=
    if s.state.sessionVersion = 0 then [] else [.base (.version s.state.sessionVersion)]
  set pLik : List GenFieldQ :=
    if s.state.localIdentity.serialize = [] then [] else [.base (.lik s.state.localIdentity.serialize)]
  set pRik : List GenFieldQ :=
    match s.state.remoteIdentity with
    | some ik => if ik.serialize = [] then [] else [.base (.rik ik.serialize)]
    | none => []
  set pRoot : List GenFieldQ :=
    if keyToBytes32 s.state.rootKey = [] then [] else [.base (.root (keyToBytes32 s.state.rootKey))]
  set pPrev : List GenFieldQ :=
    if s.state.previousCounter = 0 then [] else [.base (.prevCounter s.state.previousCounter)]
  set pSend : List GenFieldQ :=
    match s.state.senderChain with
    | some c => [.base (.sender (senderChainG c))]
    | none => []
  set pRecv : List GenFieldQ :=
    s.state.receiverChains.map (fun c => GenFieldQ.base (.recv (recvChainG c)))
  set pPend : List GenFieldQ := pendingFieldQ s.pendingPreKey
  set pRem : List GenFieldQ :=
    if s.remoteRegistrationId = 0 then [] else [.remReg s.remoteRegistrationId]
  set pLoc : List GenFieldQ :=
    if s.localRegistrationId = 0 then [] else [.locReg s.localRegistrationId]
  set pAbk : List GenFieldQ :=
    if s.aliceBaseKey = [] then [] else [.abk s.aliceBaseKey]
  set pKyb : List GenFieldQ :=
    match s.pendingKyberPreKey with
    | some k => [.kyber k.preKeyId k.ciphertext]
    | none => []
  set pPq : List GenFieldQ :=
    if s.state.pqRatchetState = [] then [] else [.pq s.state.pqRatchetState]
  set preFlds := pVer ++ pLik ++ pRik ++ pRoot ++ pPrev ++ pSend
  set postFlds := pPend ++ pRem ++ pLoc ++ pAbk ++ pKyb ++ pPq
  have hdecomp : genFieldsQ s = preFlds ++ pRecv ++ postFlds := by
    dsimp only [genFieldsQ, genFieldsX, genFields,
      preFlds, postFlds, pVer, pLik, pRik, pRoot, pPrev, pSend, pRecv,
      pPend, pRem, pLoc, pAbk, pKyb, pPq]
    rcases s.state.remoteIdentity with _ | ik <;>
      rcases s.state.senderChain with _ | sc <;>
      rcases s.pendingKyberPreKey with _ | kyb <;>
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
        Function.comp_def, map_ite_singleton,
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, pendingFieldQ,
        List.append_nil, List.append_assoc, ↓reduceIte]
  have hOk3 : ∀ fl ∈ preFlds ++ pRecv ++ postFlds, fl.Ok := hdecomp ▸ hOk
  have hOkRecv : ∀ fl ∈ pRecv, fl.Ok := fun fl hfl =>
    hOk3 fl (List.mem_append_left _ (List.mem_append_right _ hfl))
  obtain ⟨pbRecv0, rW, rK⟩ := recvChains_sum_bounds s.state.receiverChains hOkRecv
  set K := (s.state.receiverChains.map (fun c => c.messageKeys.length)).sum
  have pbRecv : PieceBounded (30 + 2 * K) 5 45 1062880 pRecv :=
    pieceBounded_mono pbRecv0 (by omega) hrc (by omega) (by omega)
  have pbVer : PieceBounded 0 0 0 0 pVer := by
    unfold pVer
    split_ifs
    · exact pieceBounded_nil
    · exact pb_varint rfl
  have pbLik : PieceBounded 2 0 0 0 pLik := by
    unfold pLik
    split_ifs
    · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
    · exact pb_tiny33 fun h => by
        have hb : s.state.localIdentity.serialize.length = 33 := h
        exact ⟨s.state.localIdentity.serialize.length, rfl, by omega, by omega⟩
  have pbRik : PieceBounded 2 0 0 0 pRik := by
    unfold pRik
    rcases s.state.remoteIdentity with _ | ik
    · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
    · dsimp only
      split_ifs
      · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
      · exact pb_tiny33 fun h => by
          have hb : ik.serialize.length = 33 := h
          exact ⟨ik.serialize.length, rfl, by omega, by omega⟩
  have pbRoot : PieceBounded 2 0 0 0 pRoot := by
    unfold pRoot
    split_ifs
    · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
    · exact pb_tiny33 fun h => by
        have hb : (keyToBytes32 s.state.rootKey).length = 32 := h
        exact ⟨(keyToBytes32 s.state.rootKey).length, rfl, by omega, by omega⟩
  have pbPrev : PieceBounded 0 0 0 0 pPrev := by
    unfold pPrev
    split_ifs
    · exact pieceBounded_nil
    · exact pb_varint rfl
  have pbSend : PieceBounded 6 0 0 0 pSend := by
    unfold pSend
    rcases s.state.senderChain with _ | c
    · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
    · exact pieceBounded_singleton fun h => by
        obtain ⟨h1, h2, h3, h4, _⟩ := chainMergeEvents_sender_bounds h.1 h.2.2.2
        simp only [fieldInnerEvents]
        exact ⟨h1, Nat.le_of_eq h2, Nat.le_of_eq h3, Nat.le_of_eq h4⟩
  have pbPre : PieceBounded 12 0 0 0 preFlds :=
    pieceBounded_append
      (pieceBounded_append
        (pieceBounded_append
          (pieceBounded_append (pieceBounded_append pbVer pbLik) pbRik) pbRoot) pbPrev) pbSend
  have pbPend : PieceBounded 2 0 0 0 pPend := pb_pendingFieldQ s.pendingPreKey
  have pbRem : PieceBounded 0 0 0 0 pRem := by
    unfold pRem
    split_ifs
    · exact pieceBounded_nil
    · exact pb_varint rfl
  have pbLoc : PieceBounded 0 0 0 0 pLoc := by
    unfold pLoc
    split_ifs
    · exact pieceBounded_nil
    · exact pb_varint rfl
  have pbAbk : PieceBounded 2 0 0 0 pAbk := by
    unfold pAbk
    split_ifs
    · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
    · exact pb_tiny33 fun h => by
        have hb : s.aliceBaseKey.length = 33 := h
        exact ⟨s.aliceBaseKey.length, rfl, by omega, by omega⟩
  have pbKyb : PieceBounded 0 2 0 3138 pKyb := by
    unfold pKyb
    rcases s.pendingKyberPreKey with _ | k
    · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
    · exact pieceBounded_singleton fun h => by
        have hct : k.ciphertext.length = 1569 := h
        obtain ⟨h1, h2, h3, h4, _⟩ := bytesMergeEvents_1569_exact
        simp only [fieldInnerEvents, basicFieldByteLen, hct]
        exact ⟨by omega, by omega, by omega, by omega⟩
  have pbPq : PieceBounded 2 2 0 270334 pPq := by
    unfold pPq
    split_ifs
    · exact pieceBounded_mono pieceBounded_nil (by decide) (by decide) (by decide) (by decide)
    · exact pieceBounded_singleton fun _ => by
        obtain ⟨h1, h2, h3, h4, _⟩ := bytesMergeEvents_general_bounds s.state.pqRatchetState.length
        simp only [fieldInnerEvents, basicFieldByteLen]
        exact ⟨h1, h2, by omega, Nat.le_trans h4 (Nat.min_le_right _ _)⟩
  have pbPost : PieceBounded 6 4 0 273472 postFlds :=
    pieceBounded_append
      (pieceBounded_append
        (pieceBounded_append
          (pieceBounded_append (pieceBounded_append pbPend pbRem) pbLoc) pbAbk) pbKyb) pbPq
  have pbAll := pieceBounded_append (pieceBounded_append pbPre pbRecv) pbPost
  obtain ⟨totT, totO, totR, totS⟩ := pbAll hOk3
  rw [← hdecomp] at totT totO totR totS
  have hwAll : 36 * K ≤ ((genFieldsQ s).map (fun fl => fl.enc.length)).sum := by
    rw [hdecomp]
    simp only [List.map_append, List.sum_append]
    dsimp only [pRecv]
    omega
  exact ⟨K, by omega, hwAll, by omega, by omega, by omega, by omega⟩

/-! ## 8. Exported `DeserBoundedTotalEvs` Profile Theorems -/

private theorem tiny_cap_arith {K bsLen : Nat} (hK : K ≤ 10000) (hw : 36 * K ≤ bsLen) :
    48 + 2 * K ≤ min 20064 (bsLen / 18 + 64) := by
  omega

/-- Set B `sessDeserEvents` profile: every `r` in
`DeserializeScopeP_Q NonEmptyV1Q` (`= Slots.scopeKit`) satisfies Set B `DeserBoundedTotalEvs`
at `bs := encodeRecord r`, with no extra hypotheses. -/
theorem sessDeserEvents_deserBoundedTotalEvs_of_scope
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    DeserBoundedTotalEvs
      (min 20064 ((encodeRecord r).length / 18 + 64))
      16
      48
      (min (12 * (encodeRecord r).length + 4096) 2000000)
      (14 * (encodeRecord r).length + 4096)
      (6 * (encodeRecord r).length + 4096)
      (sessDeserEvents r) := by
  obtain ⟨s, hs, hSess⟩ := hr.2
  have hrec : recFieldsQ r = genFieldsQ s := by simp [recFieldsQ, hs]
  have hOk : ∀ fl ∈ recFieldsQ r, fl.Ok := recFieldsQ_ok r hr
  have hrc5 : s.state.receiverChains.length ≤ 5 := by
    have hm : maxReceiverChains = 5 := by decide
    have h1 := hSess.1
    omega
  have hR_eq : recvCount (recFieldsQ r) = s.state.receiverChains.length := by
    have h1 := ssgqAfter_recv_length r (recFieldsQ r).length
    rw [List.take_length, ssgqAfter_recFieldsQ r hr s hs] at h1
    simpa [ssgqOf, ssgOf] using h1.symm
  have hcap8 : vecCap4Of (recvCount (recFieldsQ r)) ≤ 8 :=
    vecCap4Of_le_eight (by omega)
  have hO8 := vec104CumF_le_of_pow2 fOther (vecCap4Of_pow2 _) isPow2Cap4_8 hcap8
  have hR8 := vec104CumF_le_of_pow2 fRealloc (vecCap4Of_pow2 _) isPow2Cap4_8 hcap8
  have hS8 := vec104CumF_le_of_pow2 fSmall (vecCap4Of_pow2 _) isPow2Cap4_8 hcap8
  have hTot8 := vec104CumF_le_of_pow2 fTotal (vecCap4Of_pow2 _) isPow2Cap4_8 hcap8
  have hc8 := vec104CumF_at_8
  have hstats := fieldsEventsAux_stats 0 (recFieldsQ r)
  simp only [vecCap4Of, Nat.zero_add, vec104CumF_zero, Nat.add_zero] at hstats
  obtain ⟨stT, stO, stR, stS, stTot, stMax⟩ := hstats
  have henc := encodeRecord_eq_recFieldsQ r hr
  have hbs_ge : ((recFieldsQ r).map (fun fl => fl.enc.length)).sum ≤ (encodeRecord r).length := by
    rw [← flatMap_enc_length_eq_sum]
    conv_rhs => rw [henc]
    simp only [List.length_append]
    omega
  obtain ⟨linS, linTot⟩ := sum_linear_small_total hOk
  obtain ⟨K, hK10000, hKw, absT, absO, absR, absS⟩ :=
    genFieldsQ_absolute_and_tiny_bounds (hrec ▸ hOk) hrc5
  rw [← hrec] at hKw absT absO absR absS
  have hTiny := tiny_cap_arith hK10000 (Nat.le_trans hKw hbs_ge)
  unfold sessDeserEvents DeserBoundedTotalEvs
  refine ⟨?_, ?_, ?_, Nat.le_min.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [stT]
    exact Nat.le_trans absT hTiny
  · rw [stO]
    exact Nat.le_trans (Nat.add_le_add absO (hc8.1 ▸ hO8)) (by decide)
  · rw [stR]
    exact Nat.le_trans (Nat.add_le_add absR (hc8.2.1 ▸ hR8)) (by decide)
  · rw [stS]
    exact Nat.add_le_add (Nat.le_trans linS (Nat.mul_le_mul_left 12 hbs_ge))
      (Nat.le_trans (hc8.2.2.1 ▸ hS8) (by decide))
  · rw [stS]
    exact Nat.le_trans (Nat.add_le_add absS (hc8.2.2.1 ▸ hS8)) (by decide)
  · rw [stTot]
    exact Nat.add_le_add (Nat.le_trans linTot (Nat.mul_le_mul_left 14 hbs_ge))
      (Nat.le_trans (hc8.2.2.2 ▸ hTot8) (by decide))
  · intro ev hev
    rcases stMax ev hev with ⟨fl, hfl, hevIn⟩ | ⟨hrOuter, haOuter⟩
    · obtain ⟨_, _, hMaxFl⟩ := fieldInnerEvents_pointwise_linear (hOk fl hfl)
      obtain ⟨hrFl, haFl⟩ := hMaxFl ev hevIn
      have hfl_le : fl.enc.length ≤ (encodeRecord r).length :=
        Nat.le_trans (mem_enc_le_sum hfl) hbs_ge
      exact ⟨Nat.le_trans hrFl (Nat.add_le_add_right (Nat.mul_le_mul_left 6 hfl_le) 4096), haFl⟩
    · have hOuter832 : eventStepReq ev ≤ 832 :=
        Nat.le_trans hrOuter (Nat.mul_le_mul_right 104 hcap8)
      exact ⟨Nat.le_trans hOuter832 (Nat.le_trans (by decide : 832 ≤ 4096) (Nat.le_add_left _ _)),
        haOuter⟩

/-- Set A `sessDeserEvents` profile: `(·, 64, 128, ·)` corollary from `hr` alone. -/
theorem sessDeserEvents_deserBoundedTotalEvs_setA_of_scope
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    DeserBoundedTotalEvs
      (min 20064 ((encodeRecord r).length / 18 + 64))
      64
      128
      (min (12 * (encodeRecord r).length + 4096) 2000000)
      (14 * (encodeRecord r).length + 4096)
      (6 * (encodeRecord r).length + 4096)
      (sessDeserEvents r) :=
  deserBoundedTotalEvs_mono (sessDeserEvents_deserBoundedTotalEvs_of_scope hr)
    (Nat.le_refl _) (by decide) (by decide) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Set B `sessDeserEvents` profile at `bs.length ≤ 2 MiB`. -/
theorem sessDeserEvents_deserBoundedTotalEvs_setB
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (_hlen : (encodeRecord r).length ≤ 2097152) :
    DeserBoundedTotalEvs
      (min 20064 ((encodeRecord r).length / 18 + 64))
      16
      48
      (min (12 * (encodeRecord r).length + 4096) 2000000)
      (14 * (encodeRecord r).length + 4096)
      (6 * (encodeRecord r).length + 4096)
      (sessDeserEvents r) :=
  sessDeserEvents_deserBoundedTotalEvs_of_scope hr

/-- Set A `sessDeserEvents` profile at `bs.length ≤ 2 MiB`. -/
theorem sessDeserEvents_deserBoundedTotalEvs_real
    {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (_hlen : (encodeRecord r).length ≤ 2097152) :
    DeserBoundedTotalEvs
      (min 20064 ((encodeRecord r).length / 18 + 64))
      64
      128
      (min (12 * (encodeRecord r).length + 4096) 2000000)
      (14 * (encodeRecord r).length + 4096)
      (6 * (encodeRecord r).length + 4096)
      (sessDeserEvents r) :=
  sessDeserEvents_deserBoundedTotalEvs_setA_of_scope hr

/-! ## 9. CLI Domain-Chain Bridges (`CliPqxdhInputs ⇒ FilesOkPeer ⇒ scopeKit ⇒ Profile`) -/

/-- Scope monotonicity of `FilesOkPeer`. -/
theorem filesOkPeer_mono {S₁ S₂ : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal}
    (h : FilesOkPeer S₁ F peer) (himp : ∀ r, S₁ r → S₂ r) :
    FilesOkPeer S₂ F peer := by
  refine ⟨h.nameLt, h.textLt, h.sessPathOk, h.idPathOk, h.sessPathLt, h.idPathLt, ?_, h.idGet⟩
  obtain ⟨bs, hget, hwf⟩ := h.sessGet
  refine ⟨bs, hget, ?_⟩
  rcases hwf with rfl | ⟨r, hbs, hr⟩
  · exact .inl rfl
  · exact .inr ⟨r, hbs, himp r hr⟩

/-- On every `CliPqxdhInputs W i`, the domain peer party `st.party.other` satisfies
`FilesOkPeer scopeIn` and `FilesOkPeer scopeKit` on `runFiles i`. -/
theorem exists_filesOkPeer_scopeKit_of_cliPqxdhInputs
    {W : PEParams} {i : Inputs} (hi : CliPqxdhInputs W i) :
    ∃ P : Party,
      FilesOkPeer scopeIn (runFiles i) (partyAddr P) ∧
      FilesOkPeer scopeKit (runFiles i) (partyAddr P) := by
  obtain ⟨st, hwf, hcases⟩ := hi
  have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
  have hcap := pqSessBytes_le_fileCapBytes hwf
  refine ⟨st.party.other, ?_⟩
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ | ⟨m, rc, _, rfl⟩ |
    ⟨c, rc, _, _, _, rfl⟩
  · have hok := filesOkPeer_pqInit W st b t hcov hcap
    exact ⟨hok, filesOkPeer_mono hok (fun _ => scopeKit_of_scopeIn)⟩
  · have hok := filesOkPeer_pqSend W st m r hcov hcap
    exact ⟨hok, filesOkPeer_mono hok (fun _ => scopeKit_of_scopeIn)⟩
  · have hok := filesOkPeer_pqRecv W st (wireWhisper :: c) rc hcov hcap
    exact ⟨hok, filesOkPeer_mono hok (fun _ => scopeKit_of_scopeIn)⟩
  · have hok := filesOkPeer_pqRecv W st (wirePrekey :: m.bytes) rc hcov hcap
    exact ⟨hok, filesOkPeer_mono hok (fun _ => scopeKit_of_scopeIn)⟩
  · have hok := filesOkPeer_pqRecv W st c rc hcov hcap
    exact ⟨hok, filesOkPeer_mono hok (fun _ => scopeKit_of_scopeIn)⟩

/-- On every `CliPqxdhInputs W i` whose `argv` parses to a wrapper command `c` with
`callPeer c = some peer`, `FilesOkPeer scopeIn (runFiles i) (addrValOf peer)` holds. -/
theorem filesOkPeer_scopeIn_of_cliPqxdhInputs
    {W : PEParams} {i : Inputs} {c : CallV} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hpeer : callPeer c = some peer) :
    FilesOkPeer scopeIn (runFiles i) (addrValOf peer) := by
  obtain ⟨st, hwf, hcases⟩ := hi
  have hcov := fun x g hs => ratchetScopeCoversPq_scopeIn W st x g hwf hs
  have hcap := pqSessBytes_le_fileCapBytes hwf
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨ct, rc, _, rfl⟩ | ⟨m, rc, _, rfl⟩ |
    ⟨ct, rc, _, _, _, rfl⟩
  · have ha : (pqInitInputs W st b t).argv =
        (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
    rw [callPeer_of_cmd (.init (partyAddress st.party.other) bundleDir) rfl (ha ▸ hparse) hpeer]
    exact filesOkPeer_pqInit W st b t hcov hcap
  · have ha : (pqSendInputs W st m r).argv =
        (Cmd.send (partyAddress st.party.other)).argv := rfl
    rw [callPeer_of_cmd (.send (partyAddress st.party.other)) rfl (ha ▸ hparse) hpeer]
    exact filesOkPeer_pqSend W st m r hcov hcap
  · have ha : (pqRecvInputs W st (wireWhisper :: ct) rc).argv =
        (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hparse) hpeer]
    exact filesOkPeer_pqRecv W st (wireWhisper :: ct) rc hcov hcap
  · have ha : (pqRecvInputs W st (wirePrekey :: m.bytes) rc).argv =
        (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hparse) hpeer]
    exact filesOkPeer_pqRecv W st (wirePrekey :: m.bytes) rc hcov hcap
  · have ha : (pqRecvInputs W st ct rc).argv =
        (Cmd.recv (partyAddress st.party.other)).argv := rfl
    rw [callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hparse) hpeer]
    exact filesOkPeer_pqRecv W st ct rc hcov hcap

/-- On every `CliPqxdhInputs W i` whose `argv` parses to `c` with `callPeer c = some peer`,
`FilesOkPeer scopeKit (runFiles i) (addrValOf peer)` holds (`scopeKit = DeserializeScopeP_Q NonEmptyV1Q`). -/
theorem filesOkPeer_scopeKit_of_cliPqxdhInputs
    {W : PEParams} {i : Inputs} {c : CallV} {peer : AddrV}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hpeer : callPeer c = some peer) :
    FilesOkPeer scopeKit (runFiles i) (addrValOf peer) :=
  filesOkPeer_mono (filesOkPeer_scopeIn_of_cliPqxdhInputs hi hparse hpeer)
    (fun _ => scopeKit_of_scopeIn)

/-- Any non-empty session file `bs ≠ []` read from `StoresGhost.opened.sessions` under
`FilesOkPeer scopeKit F rem` decodes to a `scopeKit` (`= DeserializeScopeP_Q NonEmptyV1Q`) record `r`
whose `sessDeserEvents r` satisfies both Set B and Set A `DeserBoundedTotalEvs` at `bs`. -/
theorem scopeKit_of_filesOkPeer_sessGet
    {F : FsFiles} {rem : AddrVal} {bs : List (BitVec 8)}
    (hok : FilesOkPeer scopeKit F rem)
    (hget : StoresGhost.opened.sessions.get cliIo.rd F (addressText rem) = .ok bs)
    (hne : bs ≠ []) :
    ∃ r : SessionRecord (List (BitVec 8)),
      encodeRecord r = bs ∧
      scopeKit r ∧
      SessDeserSetBEnv bs (sessDeserEvents r) ∧
      SessDeserSetAEnv bs (sessDeserEvents r) := by
  obtain ⟨bs', hget', hwf⟩ := hok.sessGet
  rw [hget] at hget'
  injection hget' with heq
  subst heq
  rcases hwf with rfl | ⟨r, hbs, hr⟩
  · exact False.elim (hne rfl)
  · refine ⟨r, hbs, hr, ?_, ?_⟩
    · simpa only [SessDeserSetBEnv, hbs] using sessDeserEvents_deserBoundedTotalEvs_of_scope hr
    · simpa only [SessDeserSetAEnv, hbs] using sessDeserEvents_deserBoundedTotalEvs_setA_of_scope hr

/-- End-to-end named domain chain (`CliPqxdhInputs ⇒ FilesOkPeer scopeKit ⇒ scopeKit ⇒ Set B / Set A`)
for any non-empty peer session file read on `runFiles i`. -/
theorem cliPqxdhInputs_sessGet_scopeKit_and_profile
    {W : PEParams} {i : Inputs} {c : CallV} {peer : AddrV} {bs : List (BitVec 8)}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hpeer : callPeer c = some peer)
    (hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles i) (addressText (addrValOf peer)) = .ok bs)
    (hne : bs ≠ []) :
    ∃ r : SessionRecord (List (BitVec 8)),
      encodeRecord r = bs ∧
      scopeKit r ∧
      SessDeserSetBEnv bs (sessDeserEvents r) ∧
      SessDeserSetAEnv bs (sessDeserEvents r) :=
  scopeKit_of_filesOkPeer_sessGet
    (filesOkPeer_scopeKit_of_cliPqxdhInputs hi hparse hpeer) hget hne

/-- Full empty-or-`scopeKit` disjunction (`DCAN` `RecordDeserializeCancelEnv` + Set B / Set A)
for any session file `bs` read from `StoresGhost.opened.sessions` under `FilesOkPeer scopeKit F rem`. -/
theorem sessGet_empty_or_scopeKit_of_filesOkPeer
    {F : FsFiles} {rem : AddrVal} {bs : List (BitVec 8)}
    (hok : FilesOkPeer scopeKit F rem)
    (hget : StoresGhost.opened.sessions.get cliIo.rd F (addressText rem) = .ok bs) :
    bs = [] ∨
      ∃ r : SessionRecord (List (BitVec 8)),
        bs = encodeRecord r ∧
        DeserializeScopeP_Q NonEmptyV1Q r ∧
        SessDeserSetBEnv bs (sessDeserEvents r) ∧
        SessDeserSetAEnv bs (sessDeserEvents r) := by
  by_cases hne : bs = []
  · exact Or.inl hne
  · obtain ⟨r, hbs, hr, hB, hA⟩ := scopeKit_of_filesOkPeer_sessGet hok hget hne
    exact Or.inr ⟨r, hbs.symm, hr, hB, hA⟩

/-- End-to-end `CliPqxdhInputs` empty-or-`scopeKit` link (`CliPqxdhInputs ⇒ FilesOkPeer scopeKit ⇒
bs = [] ∨ (bs = encodeRecord r ∧ DeserializeScopeP_Q NonEmptyV1Q r ∧ Set B ∧ Set A)`), connecting `CliPqxdhInputs` to the `sessDeserEvents` allocation profiles. -/
theorem cliPqxdhInputs_sessGet_empty_or_scopeKit
    {W : PEParams} {i : Inputs} {c : CallV} {peer : AddrV} {bs : List (BitVec 8)}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hpeer : callPeer c = some peer)
    (hget : StoresGhost.opened.sessions.get cliIo.rd (runFiles i) (addressText (addrValOf peer)) = .ok bs) :
    bs = [] ∨
      ∃ r : SessionRecord (List (BitVec 8)),
        bs = encodeRecord r ∧
        DeserializeScopeP_Q NonEmptyV1Q r ∧
        SessDeserSetBEnv bs (sessDeserEvents r) ∧
        SessDeserSetAEnv bs (sessDeserEvents r) :=
  sessGet_empty_or_scopeKit_of_filesOkPeer
    (filesOkPeer_scopeKit_of_cliPqxdhInputs hi hparse hpeer) hget

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserProfile
