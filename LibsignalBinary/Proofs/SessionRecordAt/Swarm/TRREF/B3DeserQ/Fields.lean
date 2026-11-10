/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
import LibsignalBinary.Proofs.E2E.Record.L1GX.Fields
import LibsignalBinary.Proofs.E2E.RecordX.Length

/-!
# Pure Field Decomposition and Length Bounds for `DeserializeScopeP_Q NonEmptyV1Q`

Projects `DeserializeScopeP_Q` sessions via `clearPqSession` (`pqRatchetState := []`) to lift the
`L1GX` field decomposition theorems while adjoining the optional trailing tag-15 (`pq_ratchet_state`)
field (`encSession_eq_genFieldsQ`, `encodeRecord_eq_recFieldsQ`, `recFieldsQ_ok`, `recFieldsQ_fresh`,
`ssgqAfter_recFieldsQ`, and `encodeRecord_length_ltQ`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs

theorem L1_B3DeserQ_Fields : True := trivial

/-! ## Projection to `clearPqSession` and `clearPqRecord` -/

/-- Clear `pqRatchetState` so the session lies in `L1GX`'s `DeserializeScopeP`. -/
def clearPqSession (s : Session (List (BitVec 8))) : Session (List (BitVec 8)) :=
  { s with state := { s.state with pqRatchetState := [] } }

/-- Clear `pqRatchetState` on the current session of a `SessionRecord`. -/
def clearPqRecord (r : SessionRecord (List (BitVec 8))) : SessionRecord (List (BitVec 8)) :=
  ⟨r.currentSession.map clearPqSession⟩

@[simp] theorem toSSGQ_ssgxOf_clearPqSession (s : Session (List (BitVec 8)))
    (pq : List (BitVec 8)) :
    SSGX.toSSGQ (ssgxOf (clearPqSession s)) pq = SSGX.toSSGQ (ssgxOf s) pq := rfl

theorem recFieldsX_clearPqRecord_of_some {r : SessionRecord (List (BitVec 8))}
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) :
    recFieldsX (clearPqRecord r) = genFieldsX (clearPqSession s) := by
  simp [clearPqRecord, hs, recFieldsX]

/-- Every record in `DeserializeScopeP_Q Q` projects via `clearPqRecord` into `DeserializeScopeP`. -/
theorem deserializeScopeP_clearPq {Q : List (BitVec 8) → Prop}
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q Q r) :
    DeserializeScopeP (clearPqRecord r) := by
  obtain ⟨⟨hInScope, _, hRepr⟩, s, hs, hSessScope⟩ := hr
  refine ⟨⟨?_, ?_, ?_⟩, clearPqSession s, ?_, hSessScope⟩
  · intro s' hs'
    simp only [clearPqRecord, hs, Option.map_some, Option.some.injEq] at hs'
    subst hs'
    exact hInScope s hs
  · intro s' hs'
    simp only [clearPqRecord, hs, Option.map_some, Option.some.injEq] at hs'
    subst hs'
    rfl
  · intro s' hs'
    simp only [clearPqRecord, hs, Option.map_some, Option.some.injEq] at hs'
    subst hs'
    exact hRepr s hs
  · simp [clearPqRecord, hs]

/-- Extract `SessionScopeP s` and `Q s.state.pqRatchetState` from `DeserializeScopeP_Q Q r`. -/
theorem deserializeScopePQ_session {Q : List (BitVec 8) → Prop}
    {r : SessionRecord (List (BitVec 8))} (hr : DeserializeScopeP_Q Q r)
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) :
    SessionScopeP s ∧ Q s.state.pqRatchetState := by
  obtain ⟨⟨_, hQ, _⟩, s', hs', hsc⟩ := hr
  rw [hs] at hs'
  cases hs'
  exact ⟨hsc, hQ s hs⟩

/-! ## `encSession_eq_genFieldsQ` and `encodeRecord_eq_recFieldsQ` -/

private theorem encSession_eq_clearPq_append (s : Session (List (BitVec 8))) :
    encSession s = encSession (clearPqSession s) ++ bytesField 15 s.state.pqRatchetState := by
  unfold encSession clearPqSession
  simp only [show bytesField 15 ([] : List (BitVec 8)) = [] from rfl,
    List.append_nil, List.append_assoc]

private theorem flatMap_map_toGenFieldQ (xs : List GenFieldX) :
    (xs.map GenFieldX.toGenFieldQ).flatMap GenFieldQ.enc = xs.flatMap GenFieldX.enc := by
  induction xs with
  | nil => rfl
  | cons fx xs ih =>
    simp only [List.map_cons, List.flatMap_cons, toGenFieldQ_enc, ih]

private theorem pq_bytesField_eq (b : List (BitVec 8)) :
    bytesField 15 b = (if b = [] then [] else [GenFieldQ.pq b]).flatMap GenFieldQ.enc := by
  unfold bytesField
  split_ifs <;> simp [GenFieldQ.enc, GenFieldQ.tag, GenFieldQ.wt, GenFieldQ.payload, lenField]

/-- `encSession s` is the concatenation `(genFieldsQ s).flatMap GenFieldQ.enc`. -/
theorem encSession_eq_genFieldsQ {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    encSession s = (genFieldsQ s).flatMap GenFieldQ.enc := by
  have hrP := deserializeScopeP_clearPq hr
  have hsP : (clearPqRecord r).currentSession = some (clearPqSession s) := by
    simp [clearPqRecord, hs]
  have hX := encSession_eq_genFieldsX (clearPqRecord r) hrP (clearPqSession s) hsP
  rw [encSession_eq_clearPq_append s, hX, genFieldsQ, ← show clearPqSession s =
      { s with state := { s.state with pqRatchetState := [] } } from rfl,
    List.flatMap_append, flatMap_map_toGenFieldQ, pq_bytesField_eq]

/-- `encodeRecord r` is key `0x0a` + varint length + `(recFieldsQ r).flatMap GenFieldQ.enc`. -/
theorem encodeRecord_eq_recFieldsQ {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r) :
    encodeRecord r = encodeKey 1 .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 ((recFieldsQ r).flatMap GenFieldQ.enc).length) ++
      (recFieldsQ r).flatMap GenFieldQ.enc := by
  have ⟨s, hs, _⟩ := hr.2
  have hrec : recFieldsQ r = genFieldsQ s := by simp [recFieldsQ, hs]
  rw [hrec, ← encSession_eq_genFieldsQ r hr s hs]
  simp [encodeRecord, hs, msgField, lenField]

/-! ## Well-formedness (`recFieldsQ_ok`) -/

/-- Every field of a `DeserializeScopeP_Q NonEmptyV1Q` record satisfies `GenFieldQ.Ok`. -/
theorem recFieldsQ_ok (r : SessionRecord (List (BitVec 8)))
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    ∀ fl ∈ recFieldsQ r, fl.Ok := by
  have ⟨s, hs, _⟩ := hr.2
  have hrP := deserializeScopeP_clearPq hr
  have hX := recFieldsX_ok (clearPqRecord r) hrP
  have hpq : s.state.pqRatchetState.length < 2 ^ 32 := (deserializeScopePQ_session hr hs).2
  have hrecX := recFieldsX_clearPqRecord_of_some hs
  simp only [recFieldsQ, hs, genFieldsQ, List.mem_append, List.mem_map]
  rintro fl (⟨fx, hfx, rfl⟩ | h15)
  · have hfx' : fx ∈ genFieldsX (clearPqSession s) := hfx
    rw [toGenFieldQ_ok fx (noPq_of_mem_genFieldsX rfl hfx')]
    exact hX fx (hrecX ▸ hfx')
  · split_ifs at h15
    · cases h15
    · simp only [List.mem_singleton] at h15
      subst h15
      exact hpq

/-! ## Freshness and final state (`recFieldsQ_fresh`, `ssgqAfter_recFieldsQ`) -/

/-- Folding mapped `GenFieldX` fields (all `NoPq`) preserves `pq` and acts via `SSGX.apply`. -/
theorem foldl_map_toGenFieldQ (v : SSGX) (pq : List (BitVec 8)) (xs : List GenFieldX)
    (hxs : ∀ fx ∈ xs, GenFieldX.NoPq fx) :
    (xs.map GenFieldX.toGenFieldQ).foldl SSGQ.apply (SSGX.toSSGQ v pq) =
      SSGX.toSSGQ (xs.foldl SSGX.apply v) pq := by
  induction xs generalizing v with
  | nil => rfl
  | cons fx xs ih =>
    have hnpq : GenFieldX.NoPq fx := hxs fx (List.mem_cons_self ..)
    simp only [List.map_cons, List.foldl_cons]
    have hstep : (SSGX.toSSGQ v pq).apply (GenFieldX.toGenFieldQ fx) =
        SSGX.toSSGQ (v.apply fx) pq := by
      rcases v with ⟨b, e⟩
      cases fx with
      | pq _ => cases hnpq
      | _ => rfl
    rw [hstep]
    exact ih (v.apply fx) (fun f hf => hxs f (List.mem_cons_of_mem _ hf))

/-- Folding `NoPq` fields over `SSGX` preserves `ext.pq`. -/
theorem foldl_apply_pq_of_noPq (v : SSGX) (xs : List GenFieldX)
    (hxs : ∀ fx ∈ xs, GenFieldX.NoPq fx) :
    (xs.foldl SSGX.apply v).ext.pq = v.ext.pq := by
  induction xs generalizing v with
  | nil => rfl
  | cons fx xs ih =>
    have hnpq : GenFieldX.NoPq fx := hxs fx (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    rw [ih (v.apply fx) (fun f hf => hxs f (List.mem_cons_of_mem _ hf))]
    rcases v with ⟨b, e⟩
    cases fx with
    | pq _ => cases hnpq
    | _ => rfl

theorem recFieldsX_of_some {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    (hs : r.currentSession = some s) :
    recFieldsX r = genFieldsX s := by
  unfold recFieldsX
  rw [hs]

theorem recFieldsQ_of_some {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    (hs : r.currentSession = some s) :
    recFieldsQ r = genFieldsQ s := by
  unfold recFieldsQ
  rw [hs]

theorem toSSGX_toSSGQ (v : SSGX) (pq : List (BitVec 8)) (hpq : v.ext.pq = [] := by rfl) :
    (SSGX.toSSGQ v pq).toSSGX = v := by
  rcases v with ⟨b, ⟨_, _, _, _, _, _, pq'⟩⟩
  dsimp only at hpq
  subst hpq
  rfl

@[simp] theorem toSSGQ_pq (v : SSGX) (pq : List (BitVec 8)) :
    (SSGX.toSSGQ v pq).ext.pq = pq := rfl

theorem recFieldsQ_eq_map_recFieldsX_append {r : SessionRecord (List (BitVec 8))}
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s) :
    recFieldsQ r = (recFieldsX (clearPqRecord r)).map GenFieldX.toGenFieldQ ++
      (if s.state.pqRatchetState = [] then [] else [GenFieldQ.pq s.state.pqRatchetState]) := by
  rw [recFieldsX_clearPqRecord_of_some hs, recFieldsQ_of_some hs, genFieldsQ]
  rfl

theorem ssgqAfter_eq_toSSGQ_clearPq_of_le {r : SessionRecord (List (BitVec 8))}
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s)
    {k : Nat} (hk : k ≤ (recFieldsX (clearPqRecord r)).length) :
    ssgqAfter r k = SSGX.toSSGQ (ssgxAfter (clearPqRecord r) k) [] := by
  have hrecP := recFieldsX_clearPqRecord_of_some hs
  unfold ssgqAfter ssgxAfter
  rw [recFieldsQ_eq_map_recFieldsX_append hs]
  have hle : k ≤ ((recFieldsX (clearPqRecord r)).map GenFieldX.toGenFieldQ).length := by
    simpa using hk
  rw [List.take_append_of_le_length hle, ← List.map_take,
    show SSGQ.empty = SSGX.toSSGQ SSGX.empty [] from rfl,
    foldl_map_toGenFieldQ _ _ _ (fun fx hfx =>
      noPq_of_mem_genFieldsX rfl (hrecP ▸ List.mem_of_mem_take hfx))]

/-- The `k`-th field of `recFieldsQ r` is fresh against `ssgqAfter r k`. -/
theorem recFieldsQ_fresh {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r)
    (k : Nat) (hk : k < (recFieldsQ r).length) :
    ((recFieldsQ r)[k]'hk).Fresh (ssgqAfter r k) := by
  have ⟨s, hs, _⟩ := hr.2
  have hrP := deserializeScopeP_clearPq hr
  have hrecP := recFieldsX_clearPqRecord_of_some hs
  by_cases hkP : k < (recFieldsX (clearPqRecord r)).length
  · have hltM : k < ((recFieldsX (clearPqRecord r)).map GenFieldX.toGenFieldQ).length := by
      simpa using hkP
    have hget : (recFieldsQ r)[k]'hk =
        GenFieldX.toGenFieldQ ((recFieldsX (clearPqRecord r))[k]'hkP) := by
      simp only [recFieldsQ_eq_map_recFieldsX_append hs]
      rw [List.getElem_append_left hltM, List.getElem_map]
    have hpqAfter : (ssgxAfter (clearPqRecord r) k).ext.pq = [] := by
      unfold ssgxAfter
      exact foldl_apply_pq_of_noPq SSGX.empty _ (fun fx hfx =>
        noPq_of_mem_genFieldsX rfl (hrecP ▸ List.mem_of_mem_take hfx))
    rw [hget, ssgqAfter_eq_toSSGQ_clearPq_of_le hs (Nat.le_of_lt hkP), toGenFieldQ_fresh_iff,
      toSSGX_toSSGQ _ _ hpqAfter, toSSGQ_pq]
    exact ⟨recFieldsX_fresh (clearPqRecord r) hrP k hkP, rfl⟩
  · have hlenQ : (recFieldsQ r).length = (recFieldsX (clearPqRecord r)).length +
        (if s.state.pqRatchetState = [] then [] else [GenFieldQ.pq s.state.pqRatchetState]).length := by
      rw [recFieldsQ_eq_map_recFieldsX_append hs, List.length_append, List.length_map]
    split_ifs at hlenQ with hpq
    · simp only [List.length_nil, Nat.add_zero] at hlenQ
      omega
    · simp only [List.length_singleton] at hlenQ
      have hkeq : k = (recFieldsX (clearPqRecord r)).length := by omega
      subst hkeq
      have hget : (recFieldsQ r)[(recFieldsX (clearPqRecord r)).length]'hk =
          GenFieldQ.pq s.state.pqRatchetState := by
        simp only [recFieldsQ_eq_map_recFieldsX_append hs, hpq, ↓reduceIte]
        have hleM : ((recFieldsX (clearPqRecord r)).map GenFieldX.toGenFieldQ).length ≤
            (recFieldsX (clearPqRecord r)).length := by simp
        rw [List.getElem_append_right hleM]
        simp
      rw [hget, ssgqAfter_eq_toSSGQ_clearPq_of_le hs (Nat.le_refl _)]
      rfl

/-- The decoded value after all fields of `recFieldsQ r` is `ssgqOf s`. -/
theorem ssgqAfter_recFieldsQ {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScopeP_Q Q r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    ssgqAfter r (recFieldsQ r).length = ssgqOf s := by
  have hrP := deserializeScopeP_clearPq hr
  have hsP : (clearPqRecord r).currentSession = some (clearPqSession s) := by
    simp [clearPqRecord, hs]
  have hAfterX := ssgxAfter_recFieldsX (clearPqRecord r) hrP (clearPqSession s) hsP
  have hrecP := recFieldsX_clearPqRecord_of_some hs
  unfold ssgqAfter
  rw [List.take_length, recFieldsQ_eq_map_recFieldsX_append hs, List.foldl_append]
  have hfoldX : (recFieldsX (clearPqRecord r)).foldl SSGX.apply SSGX.empty =
      ssgxOf (clearPqSession s) := by
    unfold ssgxAfter at hAfterX
    rw [List.take_length] at hAfterX
    exact hAfterX
  rw [show SSGQ.empty = SSGX.toSSGQ SSGX.empty [] from rfl,
    foldl_map_toGenFieldQ _ _ _ (fun fx hfx => noPq_of_mem_genFieldsX rfl (hrecP ▸ hfx)),
    hfoldX, toSSGQ_ssgxOf_clearPqSession]
  split_ifs with hpq
  · simp [ssgqOf_eq_toSSGQ, hpq]
  · simp [SSGQ.apply, ssgqOf_eq_toSSGQ, SSGX.toSSGQ, ExtraG.toExtraGQ]

/-- Before the optional final tag-15 field, `ssgqAfter r k` has `ext.pq = []`. -/
theorem ssgqAfter_pq_empty_of_lt {Q : List (BitVec 8) → Prop}
    (r : SessionRecord (List (BitVec 8))) (_hr : DeserializeScopeP_Q Q r)
    {s : Session (List (BitVec 8))} (hs : r.currentSession = some s)
    {k : Nat} (hk : k ≤ (genFieldsX (clearPqSession s)).length) :
    (ssgqAfter r k).ext.pq = [] := by
  have hk' : k ≤ (recFieldsX (clearPqRecord r)).length := by
    rwa [recFieldsX_clearPqRecord_of_some hs]
  rw [ssgqAfter_eq_toSSGQ_clearPq_of_le hs hk']
  rfl

/-! ## Encoded record length bounds (`encodeRecord_length_ltQ`) -/

/-- For `r` in `DeserializeScopeP_Q NonEmptyV1Q`, `(encodeRecord r).length < 2 ^ 33`
(specifically `< 2 ^ 20 + 2 ^ 32 + 40`, well below `2 ^ 62`). -/
theorem encodeRecord_length_ltQ {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    (encodeRecord r).length < 2 ^ 33 := by
  have ⟨s, hs, _⟩ := hr.2
  have hrP := deserializeScopeP_clearPq hr
  have hltP : (encodeRecord (clearPqRecord r)).length < 2 ^ 20 :=
    encodeRecord_length_ltX hrP
  have hpq : s.state.pqRatchetState.length < 2 ^ 32 :=
    (deserializeScopePQ_session hr hs).2
  have hencP : encodeRecord (clearPqRecord r) = lenField 1 (encSession (clearPqSession s)) := by
    simp [encodeRecord, clearPqRecord, hs, msgField]
  have henc : encodeRecord r = lenField 1 (encSession s) := by
    simp [encodeRecord, hs, msgField]
  have hgeP : (encSession (clearPqSession s)).length ≤ (encodeRecord (clearPqRecord r)).length := by
    rw [hencP]
    exact lenField_length_ge' 1 (encSession (clearPqSession s))
  have hle : (encodeRecord r).length ≤ (encSession s).length + 20 := by
    rw [henc]
    exact lenField_length_le' 1 (encSession s)
  have h15 : (bytesField 15 s.state.pqRatchetState).length ≤
      s.state.pqRatchetState.length + 20 :=
    bytesField_length_le' 15 s.state.pqRatchetState
  have hlenS : (encSession s).length =
      (encSession (clearPqSession s)).length + (bytesField 15 s.state.pqRatchetState).length := by
    rw [encSession_eq_clearPq_append, List.length_append]
  omega

/-- Corollary: `(encodeRecord r).length < 2 ^ 62` for `r` in `DeserializeScopeP_Q NonEmptyV1Q`. -/
theorem encodeRecord_length_lt62_of_Q {r : SessionRecord (List (BitVec 8))}
    (hr : DeserializeScopeP_Q NonEmptyV1Q r) :
    (encodeRecord r).length < 2 ^ 62 :=
  Nat.lt_trans (encodeRecord_length_ltQ hr) (by decide)

end Symbolic.Swarm.TRREF.B3DeserQ
