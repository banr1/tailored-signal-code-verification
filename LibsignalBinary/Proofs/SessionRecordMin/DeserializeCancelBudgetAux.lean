/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineInst
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Fields

/-!
# Scratch-Cancellation Envelopes for `SessionRecord::deserialize`

Defines `SessDeserializeCancelEnv` and `RecordDeserializeCancelEnv` over the `sessDeserEvents` trace
(block `46`, `DeserializeScopeP_Q NonEmptyV1Q`, including `bytesVtableDrop` `.free` scratch
deallocations), proves per-event request and alignment bounds
(`eventStepReq ev ≤ max 212992 (encodeRecord r).length`, `eventStepAlign ev ≤ 16`), and derives the
closed `fineCostModel` cumulative small-slot byte bound `deserCancelFineCumExpr`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux

open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  IdentityKey MessageKeyGenerator PublicKey ReceiverChain SenderChain maxMessageKeys
)
open CryptoGames.LibsignalSessionApi (PendingKyberPreKey PendingPreKey Session SessionRecord)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG GenField chainGAfter genFields recvChainG senderChainG
)
open CryptoVerification.E2E.Record.L1GX (GenFieldX genFieldsX pendingFieldX)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (
  GenFieldQ clearPqSession encodeRecord_eq_recFieldsQ genFieldsQ
  noPq_of_mem_genFieldsX recFieldsQ recFieldsQ_ok
)
open LibsignalBinary.Heap (
  AllocEvent rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (
  eventStepAlign eventStepReq fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq
  smallAllocCost_le_two_mul_add
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (
  bytesFreshSmallCost chainFieldBytesSmallCost chainFieldStepEvents
  chainMergeEvents chainMergeSmallCost chainRemEvents chainRemEvents_eq_cons
  chainRemEvents_ge chainRemEvents_zero
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  basicFieldByteLen basicFieldSmallCost mergeFieldQEvents nextCapRecv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldChainsBudget (
  fieldQSmallCost
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  IsPow2Cap4 le_vecCap4Of vec104CumOfCap vec104CumOfCap_le_of_pow2 vec104GrowEvents
  vecCap4Of vecCap4Of_le_two_mul_sub_two vecCap4Of_mono vecCap4Of_pow2
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  bytesDropEvents bytesMergeAllocEvents bytesMergeEvents doReserveEvents_zero reserveCap_zero_zero
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget (
  fieldsEventsAux nextCapRecv_eq_vecCap4Of recvCount recvCount_append
  sessDeserEvents sessDeserRecvCap sessDeserSmallCost
)

/-! ## 1. Scratch-Cancellation Environments & Membership -/

/-- Record-indexed cancellation environment for `SessionRecord::deserialize` (Block `46`,
`lsProg_46 H`) on `DeserializeScopeP_Q NonEmptyV1Q`: binds `evs` to the exact trace
`sessDeserEvents r` (which includes every `bytesVtableDrop` `.free` scratch deallocation). -/
def SessDeserializeCancelEnv (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  DeserializeScopeP_Q NonEmptyV1Q r ∧ evs = sessDeserEvents r

/-- Wire-byte-indexed cancellation environment for `load_session` / `SessionRecord::deserialize`:
either `bs = [] ∧ evs = []` (empty session file fast path, returning `None` with `0` allocations),
or `bs = encodeRecord r` for some `r` in `DeserializeScopeP_Q NonEmptyV1Q` with
`evs = sessDeserEvents r`. -/
def RecordDeserializeCancelEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  (bs = [] ∧ evs = []) ∨
    ∃ r : SessionRecord (List (BitVec 8)),
      bs = encodeRecord r ∧ DeserializeScopeP_Q NonEmptyV1Q r ∧ evs = sessDeserEvents r

theorem sessDeserEvents_mem_sessDeserializeCancelEnv
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    SessDeserializeCancelEnv r (sessDeserEvents r) :=
  ⟨hr, rfl⟩

theorem sessDeserEvents_mem_recordDeserializeCancelEnv
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    RecordDeserializeCancelEnv (encodeRecord r) (sessDeserEvents r) :=
  Or.inr ⟨r, rfl, hr, rfl⟩

theorem nil_mem_recordDeserializeCancelEnv :
    RecordDeserializeCancelEnv [] [] :=
  Or.inl ⟨rfl, rfl⟩

theorem sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv
    {r : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : SessDeserializeCancelEnv r evs) :
    RecordDeserializeCancelEnv (encodeRecord r) evs :=
  Or.inr ⟨r, rfl, h.1, h.2⟩

/-! ## 2. Structural & Doubling-Schedule Helpers -/

private theorem length_le_flatMap_of_mem {α β : Type} (f : α → List β) {x : α} {xs : List α}
    (hx : x ∈ xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hx with rfl | hm
    · omega
    · have := ih hm; omega

theorem pq_length_le_encodeRecord_cancel {Q : List (BitVec 8) → Prop}
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q Q r)
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) :
    s.state.pqRatchetState.length ≤ (encodeRecord r).length := by
  by_cases hpq : s.state.pqRatchetState = []
  · simp [hpq]
  · have hmem : GenFieldQ.pq s.state.pqRatchetState ∈ recFieldsQ r := by
      simp only [recFieldsQ, hs, genFieldsQ, hpq, ↓reduceIte,
        List.mem_append, List.mem_singleton, or_true]
    have h1 := length_le_flatMap_of_mem GenFieldQ.enc hmem
    have henc_pq : s.state.pqRatchetState.length ≤
        (GenFieldQ.pq s.state.pqRatchetState).enc.length := by
      simp only [GenFieldQ.enc, GenFieldQ.payload, List.length_append]
      omega
    have henc_rec := encodeRecord_eq_recFieldsQ r hr
    rw [henc_rec]
    simp only [List.length_append]
    omega

set_option maxHeartbeats 400000 in
theorem recvCount_recFieldsQ_le_five {Q : List (BitVec 8) → Prop}
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q Q r) :
    recvCount (recFieldsQ r) ≤ 5 := by
  have ⟨_, s, hs, hscope⟩ := hr
  have h5 : s.state.receiverChains.length ≤ 5 := hscope.1
  have hmap_cnt : ∀ cs : List ReceiverChain,
      recvCount (cs.map (fun c => GenFieldQ.base (.recv (recvChainG c)))) = cs.length := by
    intro cs; induction cs with
    | nil => rfl
    | cons _ _ ih =>
      simp only [List.map_cons, recvCount, List.length_cons, ih]
      omega
  have hpend_cnt : recvCount
      ((pendingFieldX s.pendingPreKey).map Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    rcases s.pendingPreKey with _ | p
    · rfl
    · dsimp only [pendingFieldX]
      split_ifs
      · rcases p.preKeyId with _ | i <;> rfl
      · rfl
  have hc1 : recvCount ((if s.state.sessionVersion = 0 then []
      else [GenField.version s.state.sessionVersion]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc2 : recvCount ((if s.state.localIdentity.serialize = [] then []
      else [GenField.lik s.state.localIdentity.serialize]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc3 : ∀ ik : IdentityKey,
      recvCount ((if ik.serialize = [] then []
        else [GenField.rik ik.serialize]).map GenFieldQ.base) = 0 := fun _ => by
    split_ifs <;> rfl
  have hc4 : recvCount ((if keyToBytes32 s.state.rootKey = [] then []
      else [GenField.root (keyToBytes32 s.state.rootKey)]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc5 : recvCount ((if s.state.previousCounter = 0 then []
      else [GenField.prevCounter s.state.previousCounter]).map GenFieldQ.base) = 0 := by
    split_ifs <;> rfl
  have hc6 : ∀ c : SenderChain,
      recvCount ([GenField.sender (senderChainG c)].map GenFieldQ.base) = 0 := fun _ => rfl
  have hc10 : recvCount ((if s.remoteRegistrationId = 0 then []
      else [GenFieldX.remReg s.remoteRegistrationId]).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    split_ifs <;> rfl
  have hc11 : recvCount ((if s.localRegistrationId = 0 then []
      else [GenFieldX.locReg s.localRegistrationId]).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    split_ifs <;> rfl
  have hc13 : recvCount ((if s.aliceBaseKey = [] then []
      else [GenFieldX.abk s.aliceBaseKey]).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := by
    split_ifs <;> rfl
  have hc14 : ∀ ky : PendingKyberPreKey,
      recvCount ([GenFieldX.kyber ky.preKeyId ky.ciphertext].map
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ) = 0 := fun _ => rfl
  have hc15 : recvCount (if s.state.pqRatchetState = [] then []
      else [GenFieldQ.pq s.state.pqRatchetState]) = 0 := by
    split_ifs <;> rfl
  have hfn : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘ GenFieldX.base) =
      GenFieldQ.base := by
    funext f; rfl
  have hfn_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘ GenFieldX.base ∘
      fun c => GenField.recv (recvChainG c)) =
      (fun c => GenFieldQ.base (.recv (recvChainG c))) := by
    funext c; rfl
  unfold recFieldsQ
  rw [hs]
  dsimp only [genFieldsQ, genFieldsX, genFields, clearPqSession]
  simp only [List.map_append, List.map_map, hfn_recv, hfn, recvCount_append,
    ↓reduceIte, List.map_nil]
  rw [hmap_cnt, hpend_cnt, hc1, hc2, hc4, hc5, hc10, hc11, hc13, hc15]
  rcases s.state.remoteIdentity with _ | ik <;>
    rcases s.state.senderChain with _ | sc <;>
    rcases s.pendingKyberPreKey with _ | ky <;>
    simp only [List.map_nil, hc3, hc6, hc14, show recvCount [] = 0 from rfl] <;>
    omega

def chainHdrFields (c : ChainG) : List ChainField :=
  (if c.srk = [] then [] else [ChainField.srk c.srk]) ++
    (if c.priv = [] then [] else [ChainField.priv c.priv]) ++
    (match c.ck with | some (i, k) => [ChainField.ck i k] | none => [])

theorem chain_fields_eq_hdr_append_keys (c : ChainG) :
    c.fields = chainHdrFields c ++ c.keys.map ChainField.key :=
  rfl

theorem chainHdrFields_length_le (c : ChainG) :
    (chainHdrFields c).length ≤ 3 := by
  unfold chainHdrFields
  rcases c.ck with _ | ⟨i, k⟩ <;> split_ifs <;> simp

theorem chainHdrFields_no_key (c : ChainG) {f : ChainField} (hf : f ∈ chainHdrFields c) :
    (∀ mkg, f ≠ .key mkg) ∧
      (c.Ok → ∃ n, n ≤ 33 ∧ ∀ lenMk, chainFieldStepEvents lenMk f = bytesMergeEvents 0 n) := by
  unfold chainHdrFields at hf
  simp only [List.mem_append] at hf
  rcases hf with (h1 | h2) | h3
  · split_ifs at h1 with hsrk
    · cases h1
    · simp only [List.mem_singleton] at h1; subst h1
      refine ⟨fun _ h => ChainField.noConfusion h, fun hcOk => ⟨c.srk.length, ?_, fun _ => rfl⟩⟩
      have hb : c.srk.length = 33 := hcOk.1
      omega
  · split_ifs at h2 with hpriv
    · cases h2
    · simp only [List.mem_singleton] at h2; subst h2
      refine ⟨fun _ h => ChainField.noConfusion h, fun hcOk => ⟨c.priv.length, ?_, fun _ => rfl⟩⟩
      have hb : c.priv.length = 32 := hcOk.2.1.resolve_left hpriv
      omega
  · rcases hck : c.ck with _ | ⟨i, k⟩
    · simp [hck] at h3
    · simp only [hck, List.mem_singleton] at h3; subst h3
      refine ⟨fun _ h => ChainField.noConfusion h, fun hcOk => ⟨k.length, ?_, fun _ => rfl⟩⟩
      have hb : k.length = 32 := hcOk.2.2.1 (i, k) hck
      omega

private theorem take_length_add {α : Type} (xs ys : List α) (j : Nat) :
    (xs ++ ys).take (xs.length + j) = xs ++ ys.take j := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Nat.succ_add, ih]

private theorem take_map_local {α β : Type} (f : α → β) (xs : List α) (j : Nat) :
    (xs.map f).take j = (xs.take j).map f := by
  induction xs generalizing j with
  | nil => cases j <;> rfl
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j' =>
      change f x :: (xs.map f).take j' = f x :: (xs.take j').map f
      rw [ih j']

theorem getElem_length_add {α : Type} (xs ys : List α) (j : Nat)
    (hj : j < ys.length) (h : xs.length + j < (xs ++ ys).length) :
    (xs ++ ys)[xs.length + j]'h = ys[j]'hj := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, Nat.succ_add, List.cons_append, List.getElem_cons_succ]
    exact ih _

theorem getElem_prefix_of_lt {α : Type} (xs ys : List α) (k : Nat)
    (hk : k < xs.length) (h : k < (xs ++ ys).length) :
    (xs ++ ys)[k]'h = xs[k]'hk := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.cons_append, List.getElem_cons_succ]
      exact ih k' (Nat.lt_of_succ_lt_succ hk) _

private theorem foldl_no_key_keys (hs : List ChainField)
    (hno : ∀ f ∈ hs, ∀ mkg, f ≠ .key mkg) (v : ChainG) :
    (hs.foldl ChainG.apply v).keys = v.keys := by
  induction hs generalizing v with
  | nil => rfl
  | cons f rest ih =>
    have hf_ne := hno f List.mem_cons_self
    have hv : (v.apply f).keys = v.keys := by
      cases f with
      | srk _ | priv _ | ck _ _ => rfl
      | key mkg => exact False.elim (hf_ne mkg rfl)
    simp only [List.foldl_cons]
    rw [ih (fun g hg => hno g (List.mem_cons_of_mem f hg)) (v.apply f), hv]

private theorem foldl_map_key_keys (ks : List MessageKeyGenerator) (v : ChainG) :
    ((ks.map ChainField.key).foldl ChainG.apply v).keys = v.keys ++ ks := by
  induction ks generalizing v with
  | nil => simp
  | cons mk rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih (v.apply (.key mk))]
    simp [ChainG.apply, List.append_assoc]

theorem chainGAfter_keys_length_at_key (c : ChainG) {j : Nat} (hj : j ≤ c.keys.length) :
    (chainGAfter c ((chainHdrFields c).length + j)).keys.length = j := by
  unfold chainGAfter
  rw [chain_fields_eq_hdr_append_keys, take_length_add, take_map_local, List.foldl_append]
  rw [foldl_map_key_keys,
    foldl_no_key_keys (chainHdrFields c) (fun f hf => (chainHdrFields_no_key c hf).1)]
  have hempty : ChainG.empty.keys = [] := rfl
  rw [hempty, List.nil_append, List.length_take, Nat.min_eq_left hj]

theorem vecCap4Of_le_2048_of_le_2000 {n : Nat} (hn : n ≤ 2000) :
    vecCap4Of n ≤ 2048 := by
  by_cases h5 : 5 ≤ n
  · have hlt4096 : vecCap4Of n < 4096 := by
      have h2 := vecCap4Of_le_two_mul_sub_two h5
      omega
    rcases vecCap4Of_pow2 n with h0 | ⟨k, hk⟩
    · omega
    · rw [hk] at hlt4096 ⊢
      have hk10 : k < 10 := by
        by_contra hge
        have hpow : 1024 ≤ 2 ^ k := by
          calc 1024 = 2 ^ 10 := by decide
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hge)
        omega
      have hpow9 : 2 ^ k ≤ 512 := by
        calc 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 512 := by decide
      omega
  · have hle4 : n ≤ 4 := by omega
    calc vecCap4Of n ≤ vecCap4Of 4 := vecCap4Of_mono hle4
      _ = 4 := by decide
      _ ≤ 2048 := by decide

def growPoints2000 : List Nat :=
  [0, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

def growPoints5 : List Nat :=
  [0, 4]

theorem isPow2Cap4_lt_2000 {j : Nat} (hp : IsPow2Cap4 j) (hlt : j < 2000) :
    j ∈ growPoints2000 ∧ j ≤ 1024 := by
  rcases hp with rfl | ⟨k, rfl⟩
  · exact ⟨by decide, by decide⟩
  · have hk9 : k < 9 := by
      by_contra hge
      have hge' : 9 ≤ k := Nat.not_lt.mp hge
      have hpow : 512 ≤ 2 ^ k := by
        calc 512 = 2 ^ 9 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hge'
      omega
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
    · omega

theorem isPow2Cap4_lt_5 {j : Nat} (hp : IsPow2Cap4 j) (hlt : j < 5) :
    j ∈ growPoints5 ∧ j ≤ 4 := by
  rcases hp with rfl | ⟨k, rfl⟩
  · exact ⟨by decide, by decide⟩
  · have hk1 : k < 1 := by
      by_contra hge
      have hge' : 1 ≤ k := Nat.not_lt.mp hge
      have hpow : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hge'
      omega
    rcases k with _ | k
    · exact ⟨by decide, by decide⟩
    · omega

theorem filter_lt_length_mono (L : List Nat) {a b : Nat} (hab : a ≤ b) :
    (L.filter (· < a)).length ≤ (L.filter (· < b)).length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter]
    by_cases hxa : decide (x < a) = true
    · have hxb : decide (x < b) = true :=
        decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true hxa) hab)
      simp only [hxa, hxb, List.length_cons]
      exact Nat.succ_le_succ ih
    · simp only [Bool.not_eq_true] at hxa
      rw [hxa]
      cases decide (x < b) <;> simp only [List.length_cons]
      · exact ih
      · exact Nat.le_succ_of_le ih

theorem filter_lt_succ_of_mem {L : List Nat} {j : Nat} (hj : j ∈ L) :
    (L.filter (· < j)).length + 1 ≤ (L.filter (· < j + 1)).length := by
  induction L with
  | nil => cases hj
  | cons x xs ih =>
    simp only [List.filter]
    rcases List.mem_cons.mp hj with rfl | hmem
    · have h1 : decide (j < j) = false := decide_eq_false (Nat.lt_irrefl j)
      have h2 : decide (j < j + 1) = true := decide_eq_true (Nat.lt_succ_self j)
      rw [h1, h2, List.length_cons]
      exact Nat.succ_le_succ (filter_lt_length_mono xs (Nat.le_succ j))
    · have hrec := ih hmem
      by_cases hxj : decide (x < j) = true
      · have hxj1 : decide (x < j + 1) = true :=
          decide_eq_true (Nat.lt_succ_of_lt (of_decide_eq_true hxj))
        rw [hxj, hxj1, List.length_cons, List.length_cons]
        omega
      · simp only [Bool.not_eq_true] at hxj
        rw [hxj]
        cases decide (x < j + 1) <;> simp only [List.length_cons] <;> omega

theorem sum_map_le_const_mul {α : Type} (xs : List α) (f : α → Nat) (C : Nat)
    (h : ∀ x ∈ xs, f x ≤ C) :
    (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rw [Nat.add_comm (rest.length * C) C]
    exact Nat.add_le_add h1 h2

/-! ## 3. Per-Event `eventStepReq` & `eventStepAlign` Bounds (`sessDeserEvents_req_align`) -/

private theorem req_align_rustAlloc_local {req al : Nat} (hal : al ≤ 16) :
    ∀ ev ∈ rustAllocEvents req al, eventStepReq ev ≤ req ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split <;> intro ev hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
    simp only [eventStepReq, eventStepAlign] <;> omega

private theorem req_align_rustDealloc_local (req al : Nat) :
    ∀ ev ∈ rustDeallocEvents req al, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩

private theorem req_align_rustRealloc_local {old new al : Nat} (hal : al ≤ 16) :
    ∀ ev ∈ rustReallocEvents old new al, eventStepReq ev ≤ new ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  split <;> intro ev hev
  · rw [List.mem_singleton] at hev; subst hev
    exact ⟨Nat.le_refl new, hal⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · simp only [eventStepReq, eventStepAlign]; omega
    · exact ⟨Nat.zero_le new, Nat.le_refl 16⟩

private theorem req_align_bytesMergeEvents (n : Nat) :
    ∀ ev ∈ bytesMergeEvents 0 n, eventStepReq ev ≤ max n 8 ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  by_cases hn0 : n = 0
  · subst hn0; simp at hev
  · have hlt : 0 < n := Nat.pos_of_ne_zero hn0
    unfold bytesMergeEvents bytesMergeAllocEvents bytesDropEvents at hev
    simp only [hn0, hlt, ↓reduceIte, doReserveEvents_zero, reserveCap_zero_zero,
      List.mem_append] at hev
    rcases hev with (ha1 | ha2) | hd
    · obtain ⟨hr, hal⟩ := req_align_rustAlloc_local (by decide) ev ha1
      exact ⟨Nat.le_trans hr (Nat.le_max_left n 8), hal⟩
    · exact req_align_rustAlloc_local (by decide) ev ha2
    · obtain ⟨hr, hal⟩ := req_align_rustDealloc_local n 1 ev hd
      exact ⟨Nat.le_trans hr (Nat.zero_le _), hal⟩

private theorem req_align_vec104GrowEvents {cap : Nat} (hcap : cap ≤ 1024) :
    ∀ ev ∈ vec104GrowEvents cap, eventStepReq ev ≤ 212992 ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold vec104GrowEvents at hev
  split_ifs at hev with h0
  · obtain ⟨hr, hal⟩ := req_align_rustAlloc_local (by decide) ev hev
    exact ⟨Nat.le_trans hr (by decide), hal⟩
  · obtain ⟨hr, hal⟩ := req_align_rustRealloc_local (by decide) ev hev
    have hmul : 2 * cap * 104 ≤ 212992 := by
      calc 2 * cap * 104 = 208 * cap := by omega
        _ ≤ 208 * 1024 := Nat.mul_le_mul_left 208 hcap
        _ = 212992 := by decide
    exact ⟨Nat.le_trans hr hmul, hal⟩

private theorem req_align_chainRemEvents {c : ChainG} (hcOk : c.Ok)
    (hkeys : c.keys.length ≤ 2000) (k : Nat) :
    ∀ ev ∈ chainRemEvents c k, eventStepReq ev ≤ 212992 ∧ eventStepAlign ev ≤ 16 := by
  induction hrem : c.fields.length - k generalizing k with
  | zero =>
    have hge : c.fields.length ≤ k := by omega
    rw [chainRemEvents_ge hge]
    intro _ h; cases h
  | succ d ih =>
    have hlt : k < c.fields.length := by omega
    rw [chainRemEvents_eq_cons hlt]
    intro ev hev
    rw [List.mem_append] at hev
    rcases hev with hstep | htail
    · by_cases hhdr : k < (chainHdrFields c).length
      · have hfl_eq : c.fields[k]'hlt = (chainHdrFields c)[k]'hhdr :=
          getElem_prefix_of_lt (chainHdrFields c) (c.keys.map ChainField.key) k hhdr hlt
        have hmem_hdr : (chainHdrFields c)[k]'hhdr ∈ chainHdrFields c := List.getElem_mem hhdr
        obtain ⟨n, hn33, hstep_eq⟩ := (chainHdrFields_no_key c hmem_hdr).2 hcOk
        rw [hfl_eq, hstep_eq] at hstep
        obtain ⟨hr, hal⟩ := req_align_bytesMergeEvents n ev hstep
        exact ⟨Nat.le_trans hr (by omega), hal⟩
      · have hge_hdr : (chainHdrFields c).length ≤ k := Nat.not_lt.mp hhdr
        let j := k - (chainHdrFields c).length
        have hk_eq : k = (chainHdrFields c).length + j := by omega
        have hj_lt : j < c.keys.length := by
          have hlen_f : c.fields.length = (chainHdrFields c).length + c.keys.length := by
            rw [chain_fields_eq_hdr_append_keys, List.length_append, List.length_map]
          omega
        have hfl_eq : c.fields[k]'hlt = ChainField.key (c.keys[j]'hj_lt) := by
          have hk_lt2 : (chainHdrFields c).length + j <
              (chainHdrFields c ++ c.keys.map ChainField.key).length := by
            rw [← hk_eq]; exact hlt
          have h1 := getElem_length_add (chainHdrFields c) (c.keys.map ChainField.key) j
            (by rw [List.length_map]; exact hj_lt) hk_lt2
          simp only [List.getElem_map] at h1
          have h2 : c.fields[k]'hlt =
              (chainHdrFields c ++ c.keys.map ChainField.key)[(chainHdrFields c).length + j]'hk_lt2 := by
            congr 1
          exact h2.trans h1
        have hlenMk : (chainGAfter c k).keys.length = j := by
          rw [hk_eq]
          exact chainGAfter_keys_length_at_key c (Nat.le_of_lt hj_lt)
        rw [hfl_eq, hlenMk] at hstep
        dsimp only [chainFieldStepEvents] at hstep
        rw [List.mem_append] at hstep
        rcases hstep with hbm | hgrow
        · have hseed32 : (c.keys[j]'hj_lt).seed.length = 32 :=
            hcOk.2.2.2.1 _ (List.getElem_mem hj_lt)
          rw [hseed32] at hbm
          obtain ⟨hr, hal⟩ := req_align_bytesMergeEvents 32 ev hbm
          exact ⟨Nat.le_trans hr (by decide), hal⟩
        · split_ifs at hgrow with hjcap
          · cases hgrow
          · have heq_cap : vecCap4Of j = j := Nat.le_antisymm (Nat.not_lt.mp hjcap) (le_vecCap4Of j)
            have hpj : IsPow2Cap4 j := heq_cap ▸ vecCap4Of_pow2 j
            have hj1024 : vecCap4Of j ≤ 1024 := by
              rw [heq_cap]
              exact (isPow2Cap4_lt_2000 hpj (Nat.lt_of_lt_of_le hj_lt hkeys)).2
            exact req_align_vec104GrowEvents hj1024 ev hgrow
    · exact ih (k + 1) (by omega) ev htail

private theorem req_align_chainMergeEvents {c : ChainG} (hcOk : c.Ok)
    (hkeys : c.keys.length ≤ 2000) :
    ∀ ev ∈ chainMergeEvents c, eventStepReq ev ≤ 212992 ∧ eventStepAlign ev ≤ 16 := by
  rw [← chainRemEvents_zero c]
  exact req_align_chainRemEvents hcOk hkeys 0

private theorem basicFieldByteLen_le_of_mem_recFieldsQ
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    {fl : GenFieldQ} (hmem : fl ∈ recFieldsQ r) (hok : fl.Ok) :
    basicFieldByteLen fl ≤ max 1569 (encodeRecord r).length := by
  have ⟨_, s, hs, _⟩ := hr
  cases fl with
  | base f =>
    cases f with
    | version _ | prevCounter _ | sender _ | recv _ =>
      simp [basicFieldByteLen]
    | lik b | rik b | pending b =>
      have hb : b.length = 33 := hok
      simp only [basicFieldByteLen, hb]; omega
    | root b =>
      have hb : b.length = 32 := hok
      simp only [basicFieldByteLen, hb]; omega
  | pendingId _ k =>
    have hk : k.length = 33 := hok
    simp only [basicFieldByteLen, hk]; omega
  | pendingSpk _ k _ =>
    have hk : k.length = 33 := hok.1
    simp only [basicFieldByteLen, hk]; omega
  | remReg _ | locReg _ =>
    simp [basicFieldByteLen]
  | abk b =>
    have hb : b.length = 33 := hok
    simp only [basicFieldByteLen, hb]; omega
  | kyber _ ct =>
    have hct : ct.length = 1569 := hok
    simp only [basicFieldByteLen, hct]; omega
  | pq b =>
    simp only [recFieldsQ, hs, genFieldsQ, List.mem_append, List.mem_map] at hmem
    rcases hmem with ⟨fx, hfx, hq⟩ | hpq_mem
    · cases fx <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ] at hq
      exact False.elim (noPq_of_mem_genFieldsX rfl hfx)
    · split_ifs at hpq_mem with hpq0
      · cases hpq_mem
      · simp only [List.mem_singleton, GenFieldQ.pq.injEq] at hpq_mem
        subst hpq_mem
        have hpq_le := pq_length_le_encodeRecord_cancel hr hs
        simp only [basicFieldByteLen]
        exact Nat.le_trans hpq_le (Nat.le_max_right 1569 _)

private theorem fieldsEventsAux_req_align
    {maxR : Nat} (h212 : 212992 ≤ maxR)
    (n : Nat) (flds : List GenFieldQ)
    (hn5 : n + recvCount flds ≤ 5)
    (hflds : ∀ fl ∈ flds, fl.Ok ∧
      (∀ c : ChainG, fl = .base (.recv c) → c.keys.length ≤ 2000) ∧
      basicFieldByteLen fl ≤ maxR) :
    ∀ ev ∈ fieldsEventsAux (vecCap4Of n) n flds,
      eventStepReq ev ≤ maxR ∧ eventStepAlign ev ≤ 16 := by
  induction flds generalizing n with
  | nil => intro _ h; cases h
  | cons fl rest ih =>
    let n' := match fl with | .base (.recv _) => n + 1 | _ => n
    have hcap' : nextCapRecv (vecCap4Of n) n fl = vecCap4Of n' := nextCapRecv_eq_vecCap4Of n fl
    have hn_cnt : n' + recvCount rest = n + recvCount (fl :: rest) := by
      cases fl with
      | base f => (cases f <;> simp [n', recvCount]); omega
      | _ => simp [n', recvCount]
    obtain ⟨hok, hrc_keys, hb_le⟩ := hflds fl List.mem_cons_self
    intro ev hev
    simp only [fieldsEventsAux] at hev
    rw [hcap', List.mem_append] at hev
    rcases hev with hhd | htl
    · cases fl with
      | base f =>
        cases f with
        | sender c =>
          have hcOk : c.Ok := hok.1
          have hcKeys0 : c.keys = [] := hok.2.2.2
          obtain ⟨hr, hal⟩ := req_align_chainMergeEvents hcOk (by simp [hcKeys0]) ev hhd
          exact ⟨Nat.le_trans hr h212, hal⟩
        | recv c =>
          dsimp only [mergeFieldQEvents] at hhd
          rw [List.mem_append] at hhd
          rcases hhd with hcm | hgr
          · have hcOk : c.Ok := hok.1
            obtain ⟨hr, hal⟩ := req_align_chainMergeEvents hcOk (hrc_keys c rfl) ev hcm
            exact ⟨Nat.le_trans hr h212, hal⟩
          · split_ifs at hgr with heq
            · have hn_lt5 : n < 5 := by
                dsimp only [recvCount] at hn5; omega
              have hcap_le : vecCap4Of n ≤ 1024 := by
                rw [← heq]; omega
              obtain ⟨hr, hal⟩ := req_align_vec104GrowEvents hcap_le ev hgr
              exact ⟨Nat.le_trans hr h212, hal⟩
            · cases hgr
        | version _ | lik _ | rik _ | root _ | prevCounter _ | pending _ =>
          obtain ⟨hr, hal⟩ := req_align_bytesMergeEvents (basicFieldByteLen _) ev hhd
          exact ⟨Nat.le_trans hr (Nat.max_le.mpr ⟨hb_le, Nat.le_trans (by decide) h212⟩), hal⟩
      | _ =>
        obtain ⟨hr, hal⟩ := req_align_bytesMergeEvents (basicFieldByteLen _) ev hhd
        exact ⟨Nat.le_trans hr (Nat.max_le.mpr ⟨hb_le, Nat.le_trans (by decide) h212⟩), hal⟩
    · exact ih n' (by rw [hn_cnt]; exact hn5)
        (fun g hg => hflds g (List.mem_cons_of_mem fl hg)) ev htl

private theorem toGenFieldQ_eq_recv_iff (fx : GenFieldX) (c : ChainG) :
    Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ fx = .base (.recv c) ↔
      fx = .base (.recv c) := by
  cases fx <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ]

theorem recv_keys_le_2000_of_mem_recFieldsQ
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    {c : ChainG} (hmem : GenFieldQ.base (.recv c) ∈ recFieldsQ r) :
    c.keys.length ≤ 2000 := by
  have ⟨⟨_, _, hr_repr⟩, s, hs, _⟩ := hr
  have hmk := (hr_repr s hs).1
  simp only [recFieldsQ, hs, genFieldsQ, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨fx, hfx, hq⟩ | hpq
  · rw [toGenFieldQ_eq_recv_iff] at hq
    subst hq
    unfold genFieldsX at hfx
    simp only [List.mem_append, List.mem_map] at hfx
    have hnot_ext : ¬ ((GenFieldX.base (.recv c) ∈ pendingFieldX s.pendingPreKey) ∨
        (GenFieldX.base (.recv c) ∈
          if s.remoteRegistrationId = 0 then [] else [GenFieldX.remReg s.remoteRegistrationId]) ∨
        (GenFieldX.base (.recv c) ∈
          if s.localRegistrationId = 0 then [] else [GenFieldX.locReg s.localRegistrationId]) ∨
        (GenFieldX.base (.recv c) ∈
          if s.aliceBaseKey = [] then [] else [GenFieldX.abk s.aliceBaseKey]) ∨
        (GenFieldX.base (.recv c) ∈
          match s.pendingKyberPreKey with
          | some k => [GenFieldX.kyber k.preKeyId k.ciphertext]
          | none => []) ∨
        (GenFieldX.base (.recv c) ∈
          if ([] : List (BitVec 8)) = [] then [] else [GenFieldX.pq []])) := by
      rintro (hp | hr1 | hl1 | ha1 | hk1 | hpq1)
      · rcases hpp : s.pendingPreKey with _ | p <;> simp only [pendingFieldX, hpp] at hp
        · simp at hp
        · split_ifs at hp
          · rcases hpid : p.preKeyId with _ | i <;> simp [hpid] at hp
          · simp at hp
      · split_ifs at hr1 <;> simp at hr1
      · split_ifs at hl1 <;> simp at hl1
      · split_ifs at ha1 <;> simp at ha1
      · rcases hky : s.pendingKyberPreKey with _ | ky <;> simp [hky] at hk1
      · simp at hpq1
    have hbase : ∃ a ∈ genFields
        { s with state := { s.state with pqRatchetState := [] }, pendingPreKey := none },
        GenFieldX.base a = GenFieldX.base (.recv c) := by tauto
    obtain ⟨f, hf, hfeq⟩ := hbase
    injection hfeq with hfeq'
    subst hfeq'
    unfold genFields at hf
    simp only [List.mem_append, List.mem_map] at hf
    have hnot_other : ¬ ((GenField.recv c ∈
          if s.state.sessionVersion = 0 then [] else [GenField.version s.state.sessionVersion]) ∨
        (GenField.recv c ∈
          if s.state.localIdentity.serialize = [] then []
          else [GenField.lik s.state.localIdentity.serialize]) ∨
        (GenField.recv c ∈
          match s.state.remoteIdentity with
          | some ik => if ik.serialize = [] then [] else [GenField.rik ik.serialize]
          | none => []) ∨
        (GenField.recv c ∈
          if keyToBytes32 s.state.rootKey = [] then []
          else [GenField.root (keyToBytes32 s.state.rootKey)]) ∨
        (GenField.recv c ∈
          if s.state.previousCounter = 0 then []
          else [GenField.prevCounter s.state.previousCounter]) ∨
        (GenField.recv c ∈
          match s.state.senderChain with
          | some sc => [GenField.sender (senderChainG sc)]
          | none => []) ∨
        (GenField.recv c ∈
          match (none : Option PendingPreKey) with
          | some p => [GenField.pending p.baseKey.serialize]
          | none => [])) := by
      rintro (gv | gl | gr | grt | gpc | gsc | gp)
      · split_ifs at gv <;> simp at gv
      · split_ifs at gl <;> simp at gl
      · rcases hrik : s.state.remoteIdentity with _ | ik <;> simp [hrik] at gr
      · split_ifs at grt <;> simp at grt
      · split_ifs at gpc <;> simp at gpc
      · rcases hsc : s.state.senderChain with _ | sc <;> simp [hsc] at gsc
      · simp at gp
    have hrc_ex : ∃ a ∈ s.state.receiverChains,
        GenField.recv (recvChainG a) = GenField.recv c := by tauto
    obtain ⟨rc, hrc_mem, hrc_eq⟩ := hrc_ex
    injection hrc_eq with hc_eq
    subst hc_eq
    exact hmk rc hrc_mem
  · split_ifs at hpq <;> simp at hpq

/-- Every event in `sessDeserEvents r` (`DeserializeScopeP_Q NonEmptyV1Q r`) has
`eventStepReq ev ≤ max 212992 (encodeRecord r).length` and `eventStepAlign ev ≤ 16`. -/
theorem sessDeserEvents_req_align
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    ∀ ev ∈ sessDeserEvents r,
      eventStepReq ev ≤ max 212992 (encodeRecord r).length ∧ eventStepAlign ev ≤ 16 := by
  have hok_all := recFieldsQ_ok r hr
  have hn5 : 0 + recvCount (recFieldsQ r) ≤ 5 := by
    rw [Nat.zero_add]; exact recvCount_recFieldsQ_le_five hr
  unfold sessDeserEvents
  change ∀ ev ∈ fieldsEventsAux (vecCap4Of 0) 0 (recFieldsQ r), _
  refine fieldsEventsAux_req_align (Nat.le_max_left 212992 _) 0 (recFieldsQ r) hn5 ?_
  intro fl hmem
  have hok := hok_all fl hmem
  refine ⟨hok, fun c hfl => ?_, ?_⟩
  · subst hfl; exact recv_keys_le_2000_of_mem_recFieldsQ hr hmem
  · have hb := basicFieldByteLen_le_of_mem_recFieldsQ hr hmem hok
    exact Nat.le_trans hb
      (Nat.max_le.mpr ⟨Nat.le_trans (by decide) (Nat.le_max_left 212992 _),
        Nat.le_max_right 212992 _⟩)

theorem sessDeserEvents_req_align_2MiB
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r)
    (hlen : (encodeRecord r).length ≤ 2097152) :
    ∀ ev ∈ sessDeserEvents r, eventStepReq ev ≤ 2097152 ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  obtain ⟨hreq, hal⟩ := sessDeserEvents_req_align hr ev hev
  exact ⟨Nat.le_trans hreq (Nat.max_le.mpr ⟨by decide, hlen⟩), hal⟩

/-! ## 4. Closed `fineCostModel` Cumulative Small-Slot Byte Bound (`deserCancelFineCumExpr`) -/

/-- Closed `fineCostModel` `cumSmall` upper bound for a single receiver chain
(`≤ 2,000` message keys, `priv = []`, `srk` `33 B`, `ck` `32 B`, `Vec<104>` cap `≤ 2,048`). -/
def deserRecvChainFineCum : Nat :=
  bytesFreshSmallCost fineCostModel 33 +
    2001 * bytesFreshSmallCost fineCostModel 32 +
    vec104CumOfCap fineCostModel 2048

/-- Closed `fineCostModel` `cumSmall` upper bound for the sender chain
(`keys = []`, `srk` `33 B`, `priv` `32 B`, `ck` `32 B`). -/
def deserSenderChainFineCum : Nat :=
  bytesFreshSmallCost fineCostModel 33 + 2 * bytesFreshSmallCost fineCostModel 32

/-- Closed `fineCostModel` `cumSmall` expression bounding `sessDeserSmallCost fineCostModel r`
across all `r` in `DeserializeScopeP_Q NonEmptyV1Q` (independent of `|encodeRecord r|`). -/
def deserCancelFineCumExpr : Nat :=
  4 * bytesFreshSmallCost fineCostModel 33 +
    bytesFreshSmallCost fineCostModel 32 +
    deserSenderChainFineCum +
    5 * deserRecvChainFineCum +
    bytesFreshSmallCost fineCostModel 1569 +
    559746 +
    vec104CumOfCap fineCostModel 8

private theorem chainMergeSmallCost_sender_fine_le {c : ChainG} (hcOk : c.Ok) (hk0 : c.keys = []) :
    chainMergeSmallCost fineCostModel c ≤ deserSenderChainFineCum := by
  unfold chainMergeSmallCost deserSenderChainFineCum
  rw [chain_fields_eq_hdr_append_keys, hk0, List.map_nil, List.append_nil, List.length_nil]
  have hcap0 : vec104CumOfCap fineCostModel (vecCap4Of 0) = 0 := by simp
  rw [hcap0, Nat.add_zero]
  unfold chainHdrFields
  have hsrk : ((if c.srk = [] then [] else [ChainField.srk c.srk]).map
      (chainFieldBytesSmallCost fineCostModel)).sum ≤ bytesFreshSmallCost fineCostModel 33 := by
    split_ifs with hs
    · simp
    · have hb : c.srk.length = 33 := hcOk.1
      simp [chainFieldBytesSmallCost, hb]
  have hpriv : ((if c.priv = [] then [] else [ChainField.priv c.priv]).map
      (chainFieldBytesSmallCost fineCostModel)).sum ≤ bytesFreshSmallCost fineCostModel 32 := by
    split_ifs with hp
    · simp
    · have hb : c.priv.length = 32 := hcOk.2.1.resolve_left hp
      simp [chainFieldBytesSmallCost, hb]
  have hck : ((match c.ck with | some (i, k) => [ChainField.ck i k] | none => []).map
      (chainFieldBytesSmallCost fineCostModel)).sum ≤ bytesFreshSmallCost fineCostModel 32 := by
    rcases hck_eq : c.ck with _ | ⟨i, k⟩
    · simp
    · have hb : k.length = 32 := hcOk.2.2.1 (i, k) hck_eq
      simp [chainFieldBytesSmallCost, hb]
  simp only [List.map_append, List.sum_append]
  omega

private theorem chainMergeSmallCost_recv_fine_le {rc : ReceiverChain}
    (hcOk : (recvChainG rc).Ok) (hmk : rc.messageKeys.length ≤ maxMessageKeys) :
    chainMergeSmallCost fineCostModel (recvChainG rc) ≤ deserRecvChainFineCum := by
  set c := recvChainG rc
  have hpriv_nil : c.priv = [] := rfl
  have hkeys_le : c.keys.length ≤ 2000 := hmk
  unfold chainMergeSmallCost deserRecvChainFineCum
  rw [chain_fields_eq_hdr_append_keys, List.map_append, List.sum_append]
  unfold chainHdrFields
  rw [hpriv_nil]
  simp only [↓reduceIte, List.append_nil]
  have hsrk : ((if c.srk = [] then [] else [ChainField.srk c.srk]).map
      (chainFieldBytesSmallCost fineCostModel)).sum ≤ bytesFreshSmallCost fineCostModel 33 := by
    split_ifs with hs
    · simp
    · have hb : c.srk.length = 33 := hcOk.1
      simp [chainFieldBytesSmallCost, hb]
  have hck : ((match c.ck with | some (i, k) => [ChainField.ck i k] | none => []).map
      (chainFieldBytesSmallCost fineCostModel)).sum ≤ bytesFreshSmallCost fineCostModel 32 := by
    rcases hck_eq : c.ck with _ | ⟨i, k⟩
    · simp
    · have hb : k.length = 32 := hcOk.2.2.1 (i, k) hck_eq
      simp [chainFieldBytesSmallCost, hb]
  have hkeys_sum : ((c.keys.map ChainField.key).map (chainFieldBytesSmallCost fineCostModel)).sum ≤
      2000 * bytesFreshSmallCost fineCostModel 32 := by
    rw [List.map_map]
    refine Nat.le_trans (sum_map_le_const_mul c.keys _ (bytesFreshSmallCost fineCostModel 32) ?_)
      (Nat.mul_le_mul_right _ hkeys_le)
    intro mkg hmkg
    have hb : mkg.seed.length = 32 := hcOk.2.2.2.1 mkg hmkg
    simp [chainFieldBytesSmallCost, hb]
  have hcap_le : vecCap4Of c.keys.length ≤ 2048 := vecCap4Of_le_2048_of_le_2000 hkeys_le
  have hcum_cap : vec104CumOfCap fineCostModel (vecCap4Of c.keys.length) ≤
      vec104CumOfCap fineCostModel 2048 :=
    vec104CumOfCap_le_of_pow2 fineCostModel (vecCap4Of_pow2 _) (Or.inr ⟨9, by decide⟩) hcap_le
  simp only [List.map_append, List.sum_append]
  have h2001 : bytesFreshSmallCost fineCostModel 32 + 2000 * bytesFreshSmallCost fineCostModel 32 =
      2001 * bytesFreshSmallCost fineCostModel 32 := by omega
  omega

private theorem basicFieldSmallCost_pq_fine_le (b : List (BitVec 8)) :
    basicFieldSmallCost fineCostModel (.pq b) ≤ 559746 := by
  unfold basicFieldSmallCost basicFieldByteLen
  dsimp only
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeMetaCost_eq]
  split_ifs with h0 hsm
  · exact Nat.zero_le _
  · have h1 := smallAllocCost_le_two_mul_add b.length
    have h2 := smallAllocCost_le_two_mul_add (max b.length 8)
    have hm : max b.length 8 ≤ 135167 := Nat.max_le.mpr ⟨hsm, by decide⟩
    have hb1 : 2 * b.length + 9539 ≤ 2 * 135167 + 9539 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsm) 9539
    have hb2 : 2 * max b.length 8 + 9539 ≤ 2 * 135167 + 9539 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hm) 9539
    calc HasFineReallocCredit.smallAllocCost fineCostModel b.length +
          HasFineReallocCredit.smallAllocCost fineCostModel (max b.length 8)
      _ ≤ (2 * b.length + 9539) + (2 * max b.length 8 + 9539) := Nat.add_le_add h1 h2
      _ ≤ (2 * 135167 + 9539) + (2 * 135167 + 9539) := Nat.add_le_add hb1 hb2
      _ = 559746 := by decide
  · decide

private theorem basicFieldSmallCost_eq_bytesFresh {fl : GenFieldQ}
    (hle : basicFieldByteLen fl ≤ 1569) :
    basicFieldSmallCost fineCostModel fl =
      bytesFreshSmallCost fineCostModel (basicFieldByteLen fl) := by
  unfold basicFieldSmallCost bytesFreshSmallCost
  rw [fineCostModel_smallMaxReq_eq]
  have hsm : basicFieldByteLen fl ≤ 135167 := Nat.le_trans hle (by decide)
  simp [hsm]

private theorem serialize_pk_length_eq_33 (pk : PublicKey) :
    pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

private theorem serialize_ik_length_eq_33 (ik : IdentityKey) :
    ik.serialize.length = 33 :=
  serialize_pk_length_eq_33 ik.publicKey

set_option maxHeartbeats 800000 in
theorem sessDeserSmallCost_fine_le_expr
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    sessDeserSmallCost fineCostModel r ≤ deserCancelFineCumExpr := by
  have hok_all := recFieldsQ_ok r hr
  have ⟨⟨_, _, hr_repr⟩, s, hs, hscope⟩ := hr
  have h5 : s.state.receiverChains.length ≤ 5 := hscope.1
  have hmk : ∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys :=
    (hr_repr s hs).1
  have hmem_sub : ∀ fl ∈ (genFieldsX (clearPqSession s)).map
      Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fl ∈ recFieldsQ r := by
    intro fl hfl
    simp only [recFieldsQ, hs, genFieldsQ, List.mem_append]
    exact Or.inl hfl
  have hmem_base0 : ∀ f ∈ genFields { clearPqSession s with pendingPreKey := none },
      GenFieldQ.base f ∈ recFieldsQ r := by
    intro f hf
    apply hmem_sub
    rw [List.mem_map]
    refine ⟨.base f, ?_, rfl⟩
    have hin : GenFieldX.base f ∈
        (genFields { clearPqSession s with pendingPreKey := none }).map GenFieldX.base :=
      List.mem_map_of_mem hf
    unfold genFieldsX
    simp only [List.mem_append]
    tauto
  have hroot_len : keyToBytes32 s.state.rootKey ≠ [] →
      (keyToBytes32 s.state.rootKey).length = 32 := fun he => by
    apply hok_all (.base (.root (keyToBytes32 s.state.rootKey)))
    apply hmem_base0
    unfold genFields
    simp only [clearPqSession, he, ↓reduceIte, List.mem_append, List.mem_singleton]
    tauto
  have habk_len : s.aliceBaseKey ≠ [] → s.aliceBaseKey.length = 33 := fun he => by
    apply hok_all (.abk s.aliceBaseKey)
    apply hmem_sub
    rw [List.mem_map]
    refine ⟨.abk s.aliceBaseKey, ?_, rfl⟩
    unfold genFieldsX
    simp only [clearPqSession, he, ↓reduceIte, List.mem_append, List.mem_singleton]
    tauto
  have hrc_cap : sessDeserRecvCap r ≤ 8 := by
    unfold sessDeserRecvCap
    calc vecCap4Of (recvCount (recFieldsQ r))
      _ ≤ vecCap4Of 5 := vecCap4Of_mono (recvCount_recFieldsQ_le_five hr)
      _ = 8 := by decide
  have hrc_cum : vec104CumOfCap fineCostModel (sessDeserRecvCap r) ≤
      vec104CumOfCap fineCostModel 8 :=
    vec104CumOfCap_le_of_pow2 fineCostModel (vecCap4Of_pow2 _) (Or.inr ⟨1, by decide⟩) hrc_cap
  have hrecv_sum : ((s.state.receiverChains.map
      (fun rc => GenFieldQ.base (.recv (recvChainG rc)))).map
      (fieldQSmallCost fineCostModel)).sum ≤ 5 * deserRecvChainFineCum := by
    rw [List.map_map]
    refine Nat.le_trans
      (sum_map_le_const_mul s.state.receiverChains _ deserRecvChainFineCum ?_)
      (Nat.mul_le_mul_right deserRecvChainFineCum h5)
    intro rc hrc
    have hrc_in : GenFieldQ.base (.recv (recvChainG rc)) ∈ recFieldsQ r := by
      apply hmem_base0
      have hin : GenField.recv (recvChainG rc) ∈
          s.state.receiverChains.map (fun c => GenField.recv (recvChainG c)) :=
        List.mem_map_of_mem hrc
      unfold genFields
      simp only [clearPqSession, List.mem_append]
      tauto
    exact chainMergeSmallCost_recv_fine_le (hok_all _ hrc_in).1 (hmk rc hrc)
  have hpend : (((pendingFieldX s.pendingPreKey).map
      (fieldQSmallCost fineCostModel ∘
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) ≤
      bytesFreshSmallCost fineCostModel 33 := by
    rcases s.pendingPreKey with _ | p
    · simp [pendingFieldX]
    · dsimp only [pendingFieldX]
      have hpk33 := serialize_pk_length_eq_33 p.baseKey
      split_ifs
      · rcases p.preKeyId with _ | i
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
            Function.comp_apply, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
            fieldQSmallCost]
          rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hpk33])]
          simp [basicFieldByteLen, hpk33]
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
            Function.comp_apply, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
            fieldQSmallCost]
          rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hpk33])]
          simp [basicFieldByteLen, hpk33]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
          Function.comp_apply, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
          fieldQSmallCost]
        rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hpk33])]
        simp [basicFieldByteLen, hpk33]
  have h1 : (((if s.state.sessionVersion = 0 then []
      else [GenField.version s.state.sessionVersion]).map
      (fieldQSmallCost fineCostModel ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQSmallCost, basicFieldSmallCost, basicFieldByteLen]
  have h2 : (((if s.state.localIdentity.serialize = [] then []
      else [GenField.lik s.state.localIdentity.serialize]).map
      (fieldQSmallCost fineCostModel ∘ GenFieldQ.base)).sum) ≤
      bytesFreshSmallCost fineCostModel 33 := by
    have hik33 := serialize_ik_length_eq_33 s.state.localIdentity
    split_ifs
    · simp
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Function.comp_apply, fieldQSmallCost]
      rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hik33])]
      simp [basicFieldByteLen, hik33]
  have h3 : ∀ ik : IdentityKey,
      (((if ik.serialize = [] then [] else [GenField.rik ik.serialize]).map
        (fieldQSmallCost fineCostModel ∘ GenFieldQ.base)).sum) ≤
        bytesFreshSmallCost fineCostModel 33 := fun ik => by
    have hik33 := serialize_ik_length_eq_33 ik
    split_ifs
    · simp
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Function.comp_apply, fieldQSmallCost]
      rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hik33])]
      simp [basicFieldByteLen, hik33]
  have h4 : (((if keyToBytes32 s.state.rootKey = [] then []
      else [GenField.root (keyToBytes32 s.state.rootKey)]).map
      (fieldQSmallCost fineCostModel ∘ GenFieldQ.base)).sum) ≤
      bytesFreshSmallCost fineCostModel 32 := by
    split_ifs with he
    · simp
    · have hr32 := hroot_len he
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Function.comp_apply, fieldQSmallCost]
      rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hr32])]
      simp [basicFieldByteLen, hr32]
  have h5_pc : (((if s.state.previousCounter = 0 then []
      else [GenField.prevCounter s.state.previousCounter]).map
      (fieldQSmallCost fineCostModel ∘ GenFieldQ.base)).sum) = 0 := by
    split_ifs <;> simp [fieldQSmallCost, basicFieldSmallCost, basicFieldByteLen]
  have h6 : ∀ sc : SenderChain, s.state.senderChain = some sc →
      (([GenField.sender (senderChainG sc)].map
        (fieldQSmallCost fineCostModel ∘ GenFieldQ.base)).sum) ≤
        deserSenderChainFineCum := fun sc hsc => by
    have hsc_in : GenFieldQ.base (.sender (senderChainG sc)) ∈ recFieldsQ r := by
      apply hmem_base0
      unfold genFields
      simp only [clearPqSession, hsc, List.mem_append, List.mem_singleton]
      tauto
    have hok_sc := hok_all _ hsc_in
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Function.comp_apply, fieldQSmallCost]
    exact chainMergeSmallCost_sender_fine_le hok_sc.1 hok_sc.2.2.2
  have h10 : (((if s.remoteRegistrationId = 0 then []
      else [GenFieldX.remReg s.remoteRegistrationId]).map
      (fieldQSmallCost fineCostModel ∘
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
      fieldQSmallCost, basicFieldSmallCost, basicFieldByteLen]
  have h11 : (((if s.localRegistrationId = 0 then []
      else [GenFieldX.locReg s.localRegistrationId]).map
      (fieldQSmallCost fineCostModel ∘
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) = 0 := by
    split_ifs <;> simp [Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ,
      fieldQSmallCost, basicFieldSmallCost, basicFieldByteLen]
  have h13 : (((if s.aliceBaseKey = [] then []
      else [GenFieldX.abk s.aliceBaseKey]).map
      (fieldQSmallCost fineCostModel ∘
        Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) ≤
      bytesFreshSmallCost fineCostModel 33 := by
    split_ifs with he
    · simp
    · have hab33 := habk_len he
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        Function.comp_apply, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQSmallCost]
      rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hab33])]
      simp [basicFieldByteLen, hab33]
  have h14 : ∀ ky : PendingKyberPreKey, s.pendingKyberPreKey = some ky →
      (([GenFieldX.kyber ky.preKeyId ky.ciphertext].map
        (fieldQSmallCost fineCostModel ∘
          Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ)).sum) ≤
        bytesFreshSmallCost fineCostModel 1569 := fun ky hky => by
    have hct1569 : ky.ciphertext.length = 1569 := hscope.2.2.1 ky hky
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Function.comp_apply, Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ, fieldQSmallCost]
    rw [basicFieldSmallCost_eq_bytesFresh (by simp [basicFieldByteLen, hct1569])]
    simp [basicFieldByteLen, hct1569]
  have h15 : (((if s.state.pqRatchetState = [] then []
      else [GenFieldQ.pq s.state.pqRatchetState]).map
      (fieldQSmallCost fineCostModel)).sum) ≤ 559746 := by
    split_ifs
    · simp
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        fieldQSmallCost]
      exact basicFieldSmallCost_pq_fine_le s.state.pqRatchetState
  have hfn : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘ GenFieldX.base) =
      GenFieldQ.base := by
    funext f; rfl
  have hfn_recv : (Symbolic.Swarm.TRREF.B3DeserQ.GenFieldX.toGenFieldQ ∘ GenFieldX.base ∘
      fun c => GenField.recv (recvChainG c)) =
      (fun c => GenFieldQ.base (.recv (recvChainG c))) := by
    funext c; rfl
  unfold sessDeserSmallCost deserCancelFineCumExpr
  unfold recFieldsQ
  rw [hs]
  dsimp only [genFieldsQ, genFieldsX, genFields, clearPqSession]
  simp only [List.map_append, List.map_map, hfn_recv, hfn, List.sum_append,
    ↓reduceIte, List.map_nil, List.sum_nil]
  simp only [List.map_map] at hrecv_sum
  rw [h1, h5_pc, h10, h11]
  set B33 := bytesFreshSmallCost fineCostModel 33
  set B32 := bytesFreshSmallCost fineCostModel 32
  set BSC := deserSenderChainFineCum
  set BRC := 5 * deserRecvChainFineCum
  set B1569 := bytesFreshSmallCost fineCostModel 1569
  set BPQ := 559746
  set BVC := vec104CumOfCap fineCostModel 8
  rcases hrik : s.state.remoteIdentity with _ | ik <;>
    rcases hsc : s.state.senderChain with _ | sc <;>
    rcases hky : s.pendingKyberPreKey with _ | ky
  all_goals
    try (have hsc_le := h6 sc hsc)
    try (have hky_le := h14 ky hky)
    try (have hrik_le := h3 ik)
    simp only [List.map_nil, List.sum_nil]
    omega

end LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
