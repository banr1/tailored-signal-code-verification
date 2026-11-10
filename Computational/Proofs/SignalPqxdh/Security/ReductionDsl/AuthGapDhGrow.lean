/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake

/-!
# One-step growth bounds for the shallow `Auth` Gap-DH simulator

Proves that one step of `fgAuthStep` or `fgAuthStepHalt` grows each tracked state list and
`respRecs` by at most one entry.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp

/-- Every tracked list of the state grows by at most one entry. -/
def AGrow {S : Setup} (st st' : FgAuthSimState S) : Prop :=
  st'.base.principals.length ≤ st.base.principals.length + 1 ∧
  st'.base.spkBundles.length ≤ st.base.spkBundles.length + 1 ∧
  st'.base.opkEntries.length ≤ st.base.opkEntries.length + 1 ∧
  st'.base.sessions.length ≤ st.base.sessions.length + 1 ∧
  st'.base.usedSendSessions.length ≤ st.base.usedSendSessions.length + 1 ∧
  st'.base.usedRecvOPK.length ≤ st.base.usedRecvOPK.length + 1 ∧
  st'.base.usedRecvNoOPK.length ≤ st.base.usedRecvNoOPK.length + 1 ∧
  st'.base.seenKyberBaseKeys.length ≤ st.base.seenKyberBaseKeys.length + 1 ∧
  st'.base.roCache.length ≤ st.base.roCache.length + 1 ∧
  st'.base.rootRoCache.length ≤ st.base.rootRoCache.length + 1 ∧
  st'.base.advKeys.length ≤ st.base.advKeys.length + 1 ∧
  st'.rawRoCache.length ≤ st.rawRoCache.length + 1 ∧
  st'.advKeyPows.length ≤ st.advKeyPows.length + 1

def AllOut {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (mx : OracleComp spec α)
    (P : α → Prop) : Prop :=
  ∀ x ∈ support mx, P x

theorem AllOut.pure_of {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} {P : α → Prop} {a : α}
    (h : P a) : AllOut (pure a : OracleComp spec α) P := by
  intro x hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  exact hx ▸ h

theorem AllOut.bind_of {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type} {P : β → Prop}
    {mx : OracleComp spec α} {f : α → OracleComp spec β} (h : ∀ a, AllOut (f a) P) :
    AllOut (mx >>= f) P := by
  intro x hx
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨a, _, hx⟩ := hx
  exact h a x hx

theorem checkAndMarkKyberUsed_snd_length (L : List (Nat × KeyId × KeyId × Bytes)) (k : Nat)
    (a b : KeyId) (c : Bytes) :
    (checkAndMarkKyberBaseKeySeen L k a b c).2.length ≤ L.length + 1 := by
  simp only [checkAndMarkKyberBaseKeySeen]
  split <;> simp only [List.length_cons] <;> omega

theorem AGrow.refl {S : Setup} (st : FgAuthSimState S) : AGrow st st := by
  simp only [AGrow]; omega

theorem AGrow.send {S : Setup} (st : FgAuthSimState S) (se : AuthInitiatorEntry S)
    (sid : SessionId S) (fgL' : List FgPatchEntry) (fgRootL' : List FgRootEntry) :
    AGrow st { st with
      base := { st.base with
        sessions := se :: st.base.sessions
        usedSendSessions := sid :: st.base.usedSendSessions }
      fgL := fgL'
      fgRootL := fgRootL' } := by
  simp only [AGrow, List.length_cons]; omega

macro "agrow_leaf" : tactic => `(tactic| first
  | exact AGrow.refl _
  | exact AGrow.send _ _ _ _ _
  | (simp only [AGrow, List.length_cons, List.length_map]; omega))

theorem AllOut.ite_of {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} {P : α → Prop}
    (c : Prop) [Decidable c] {t e : OracleComp spec α}
    (ht : AllOut t P) (he : AllOut e P) : AllOut (if c then t else e) P := by
  split_ifs <;> assumption

macro "agrow_loop" : tactic => `(tactic| repeat' (first
  | with_reducible refine AllOut.bind_of (fun _ => ?_)
  | with_reducible refine AllOut.pure_of ?_
  | with_reducible refine AllOut.ite_of _ ?_ ?_
  | split
  | dsimp (config := { zeta := false }) only))

theorem fgRoQueryAuthGdh_grow {S : Setup} (K : Nat) (secrets : Bytes) (st : FgAuthSimState S) :
    AllOut (fgRoQueryAuthGdh K secrets st) (fun x => AGrow st x.2) := by
  unfold fgRoQueryAuthGdh
  agrow_loop
  all_goals agrow_leaf

theorem fgRoRootQueryAuthGdh_grow {S : Setup} (K : Nat) (rk dh : Bytes)
    (st : FgAuthSimState S) :
    AllOut (fgRoRootQueryAuthGdh K rk dh st) (fun x => AGrow st x.2) := by
  unfold fgRoRootQueryAuthGdh
  agrow_loop
  all_goals agrow_leaf

theorem fgRunSendAuthGdh_grow {S : Setup} (useDh1 : Bool) (t K : Nat) (U : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : FgAuthSimState S) :
    AllOut (fgRunSendAuthGdh useDh1 t S K U sid u bundle m0 m1 st) (fun x => AGrow st x.2) := by
  unfold fgRunSendAuthGdh
  agrow_loop
  all_goals agrow_leaf

theorem fgRunRecvOPKAuthGdh_grow {S : Setup} (K : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (msg : PreKeyMsg) (r : List AuthRespRecord) (st : FgAuthSimState S) :
    AllOut (fgRunRecvOPKAuthGdh S K k j o msg { st with respRecs := r })
      (fun x => AGrow st x.2) := by
  unfold fgRunRecvOPKAuthGdh fgFinishRecvAuthGdh fgFinishRecvStep2AuthGdh
  dsimp only
  have hlen := checkAndMarkKyberUsed_snd_length st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
    msg.hdr.spkId msg.hdr.ekAPk
  generalize checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
    msg.hdr.ekAPk = c at hlen ⊢
  obtain ⟨b, L'⟩ := c
  dsimp only at hlen
  agrow_loop
  all_goals agrow_leaf

theorem fgRunRecvNoOPKAuthGdh_grow {S : Setup} (K : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (msg : PreKeyMsg) (r : List AuthRespRecord) (st : FgAuthSimState S) :
    AllOut (fgRunRecvNoOPKAuthGdh S K k j l msg { st with respRecs := r })
      (fun x => AGrow st x.2) := by
  unfold fgRunRecvNoOPKAuthGdh fgFinishRecvAuthGdh fgFinishRecvStep2AuthGdh
  dsimp only
  have hlen := checkAndMarkKyberUsed_snd_length st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
    msg.hdr.spkId msg.hdr.ekAPk
  generalize checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
    msg.hdr.ekAPk = c at hlen ⊢
  obtain ⟨b, L'⟩ := c
  dsimp only at hlen
  agrow_loop
  all_goals agrow_leaf

theorem fgAuthStep_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes) (q : AuthQuery S)
    (st : FgAuthSimState S) : ∀ x ∈ support (fgAuthStep useDh1 t s S K U V q st), AGrow st x.2 := by
  show AllOut (fgAuthStep useDh1 t s S K U V q st) (fun x => AGrow st x.2)
  cases q with
  | recvOPK k j o msg => exact fgRunRecvOPKAuthGdh_grow _ _ _ _ _ _ _
  | recvNoOPK k j l msg => exact fgRunRecvNoOPKAuthGdh_grow _ _ _ _ _ _ _
  | roQuery secrets => exact fgRoQueryAuthGdh_grow _ _ _
  | roRootQuery rk dh => exact fgRoRootQueryAuthGdh_grow _ _ _ _
  | revealDhSecrets => exact AllOut.pure_of (AGrow.refl _)
  | sendOPK u i bundle m0 m1 =>
    dsimp only [fgAuthStep]
    split
    · exact AllOut.pure_of (AGrow.refl _)
    · exact fgRunSendAuthGdh_grow _ _ _ _ _ _ _ _ _ _
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [fgAuthStep]
    split
    · exact AllOut.pure_of (AGrow.refl _)
    · exact fgRunSendAuthGdh_grow _ _ _ _ _ _ _ _ _ _
  | _ =>
    dsimp only [fgAuthStep]
    agrow_loop
    all_goals agrow_leaf

theorem fgAuthStepHalt_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuthSimState S) :
    ∀ x ∈ support (fgAuthStepHalt useDh1 t s S K U V q st), AGrow st x.2 := by
  unfold fgAuthStepHalt
  split
  · exact AllOut.pure_of (by agrow_leaf)
  · exact fgAuthStep_grow _ _ _ _ _ _ _ _

/-! ## `respRecs` growth bound -/

private theorem fgRoQueryAuthGdh_respRecs_eq {S : Setup} (K : Nat) (secrets : Bytes)
    (st : FgAuthSimState S) :
    AllOut (fgRoQueryAuthGdh K secrets st) (fun x => x.2.respRecs = st.respRecs) := by
  unfold fgRoQueryAuthGdh
  agrow_loop

private theorem fgRoRootQueryAuthGdh_respRecs_eq {S : Setup} (K : Nat) (rk dh : Bytes)
    (st : FgAuthSimState S) :
    AllOut (fgRoRootQueryAuthGdh K rk dh st) (fun x => x.2.respRecs = st.respRecs) := by
  unfold fgRoRootQueryAuthGdh
  agrow_loop

private theorem fgRunSendAuthGdh_respRecs_eq {S : Setup} (useDh1 : Bool) (t K : Nat) (U : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : FgAuthSimState S) :
    AllOut (fgRunSendAuthGdh useDh1 t S K U sid u bundle m0 m1 st)
      (fun x => x.2.respRecs = st.respRecs) := by
  unfold fgRunSendAuthGdh
  agrow_loop

private theorem fgRunRecvOPKAuthGdh_respRecs_eq {S : Setup} (K : Nat) (k : Fin S.N_id)
    (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg) (st : FgAuthSimState S) :
    AllOut (fgRunRecvOPKAuthGdh S K k j o msg st) (fun x => x.2.respRecs = st.respRecs) := by
  unfold fgRunRecvOPKAuthGdh fgFinishRecvAuthGdh fgFinishRecvStep2AuthGdh
  dsimp only
  generalize checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
    msg.hdr.spkId msg.hdr.ekAPk = c
  obtain ⟨_, _⟩ := c
  agrow_loop

private theorem fgRunRecvNoOPKAuthGdh_respRecs_eq {S : Setup} (K : Nat) (k : Fin S.N_id)
    (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) (st : FgAuthSimState S) :
    AllOut (fgRunRecvNoOPKAuthGdh S K k j l msg st) (fun x => x.2.respRecs = st.respRecs) := by
  unfold fgRunRecvNoOPKAuthGdh fgFinishRecvAuthGdh fgFinishRecvStep2AuthGdh
  dsimp only
  generalize checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
    msg.hdr.spkId msg.hdr.ekAPk = c
  obtain ⟨_, _⟩ := c
  agrow_loop

theorem fgAuthStep_respRecs_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuthSimState S) :
    ∀ x ∈ support (fgAuthStep useDh1 t s S K U V q st),
      x.2.respRecs.length ≤ st.respRecs.length + 1 := by
  show AllOut (fgAuthStep useDh1 t s S K U V q st)
    (fun x => x.2.respRecs.length ≤ st.respRecs.length + 1)
  cases q with
  | recvOPK k j o msg =>
    intro x hx
    have heq := fgRunRecvOPKAuthGdh_respRecs_eq K k j o msg _ x hx
    simp only [heq, List.length_cons]
    omega
  | recvNoOPK k j l msg =>
    intro x hx
    have heq := fgRunRecvNoOPKAuthGdh_respRecs_eq K k j l msg _ x hx
    simp only [heq, List.length_cons]
    omega
  | roQuery secrets =>
    intro x hx
    rw [fgRoQueryAuthGdh_respRecs_eq K secrets st x hx]
    exact Nat.le_succ _
  | roRootQuery rk dh =>
    intro x hx
    rw [fgRoRootQueryAuthGdh_respRecs_eq K rk dh st x hx]
    exact Nat.le_succ _
  | revealDhSecrets =>
    exact AllOut.pure_of (Nat.le_succ _)
  | sendOPK u i bundle m0 m1 =>
    dsimp only [fgAuthStep]
    split
    · exact AllOut.pure_of (Nat.le_succ _)
    · intro x hx
      rw [fgRunSendAuthGdh_respRecs_eq useDh1 t K U _ u bundle m0 m1 st x hx]
      exact Nat.le_succ _
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [fgAuthStep]
    split
    · exact AllOut.pure_of (Nat.le_succ _)
    · intro x hx
      rw [fgRunSendAuthGdh_respRecs_eq useDh1 t K U _ u bundle m0 m1 st x hx]
      exact Nat.le_succ _
  | _ =>
    dsimp only [fgAuthStep]
    agrow_loop
    all_goals exact Nat.le_succ _

theorem fgAuthStepHalt_respRecs_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuthSimState S) :
    ∀ x ∈ support (fgAuthStepHalt useDh1 t s S K U V q st),
      x.2.respRecs.length ≤ st.respRecs.length + 1 := by
  unfold fgAuthStepHalt
  split
  · exact AllOut.pure_of (Nat.le_succ _)
  · exact fgAuthStep_respRecs_grow _ _ _ _ _ _ _ _

end SignalPqxdh.Security.ReductionDsl.AuthHs
