/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs

/-!
# Agreement of memory-level and canonical protobuf encodings

Proves `encSessionMem G s = encSession s` and `encRecordMem g r = encodeRecord r` whenever the
in-memory ghost byte slices match the model's canonical serializations (`CanonSession`,
`CanonRecord`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record

/-- On a canonical receiver-chain ghost, `encChainMem` agrees with `encReceiverChain`. -/
theorem encChainMem_eq_of_canon (gc : ChainGhost × ReceiverChain) (h : CanonChain gc) :
    encChainMem gc = encReceiverChain gc.2 := by
  obtain ⟨h1, h2⟩ := h
  simp [encChainMem, encReceiverChain, h1, h2, bytesField]

theorem encChainsMem_eq_of_canon :
    ∀ (gs : List ChainGhost) (cs : List ReceiverChain), gs.length = cs.length →
      (∀ gc ∈ gs.zip cs, CanonChain gc) →
      ((gs.zip cs).map fun gc => lenField 7 (encChainMem gc)).flatten =
        (cs.map fun c => lenField 7 (encReceiverChain c)).flatten
  | [], [], _, _ => rfl
  | g :: gs, c :: cs, hlen, hc => by
    simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons]
    rw [encChainMem_eq_of_canon (g, c) (hc _ (by simp)),
      encChainsMem_eq_of_canon gs cs (by simpa using hlen)
        (fun gc hm => hc gc (List.mem_cons_of_mem _ hm))]
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

theorem encSenderFieldMem_eq_of_canon (og : Option SenderChainGhost) (os : Option SenderChain)
    (h : CanonSender og os) :
    encSenderFieldMem og os = msgField 6 (os.map encSenderChain) := by
  match og, os, h with
  | none, none, _ => rfl
  | some g, some sc, ⟨h1, h2⟩ =>
    simp [encSenderFieldMem, msgField, encChainMem, encSenderChain, senderGhostAsChain,
      senderAsChain, h1, h2]

theorem encPendingFieldMem_eq_of_canon (og : Option TailVecGhost) (op : Option PendingPreKey)
    (h : CanonPending og op) :
    encPendingFieldMem og op = msgField 9 (op.map encPendingPreKey) := by
  match og, op, h with
  | none, none, _ => rfl
  | some g, some p, h1 =>
    simp only [CanonPending] at h1
    simp [encPendingFieldMem, msgField, encPendingMem, encPendingPreKey, h1]

/-- On a canonical session ghost, `encSessionMem` agrees with `encSession`. -/
theorem encSessionMem_eq_of_canon (G : SessionGhost) (s : Session (List (BitVec 8)))
    (h : CanonSession G s) : encSessionMem G s = encSession s := by
  obtain ⟨hl, hr, hs, hlen, hc, hp⟩ := h
  simp only [encSessionMem, encSession, hl, hr, encSenderFieldMem_eq_of_canon _ _ hs,
    encChainsMem_eq_of_canon _ _ hlen hc, encPendingFieldMem_eq_of_canon _ _ hp]

theorem encCurMem_eq_of_canon (oG : Option SessionGhost) (os : Option (Session (List (BitVec 8))))
    (h : CanonCur oG os) : encCurMem oG os = msgField 1 (os.map encSession) := by
  match oG, os, h with
  | none, none, _ => rfl
  | some G, some s, hc =>
    simp only [CanonCur] at hc
    simp [encCurMem, msgField, encSessionMem_eq_of_canon G s hc]

/-- On a canonical record ghost, `encRecordMem` agrees with `encodeRecord`. -/
theorem encRecordMem_eq_of_canon (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    (h : CanonRecord g r) : encRecordMem g r = encodeRecord r :=
  encCurMem_eq_of_canon _ _ h

end CryptoVerification.E2E.Record.Serialization
