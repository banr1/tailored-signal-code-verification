/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh

/-!
# One-Step Growth Bounds for the Shallow `KeyInd` Gap-DH Simulator

One step of `fgKeyIndStep`, `fgKeyIndStepIk`, or `fgKeyIndStepOpk` grows each state list (except
`fgL` and `advRoLog`) by at most one entry.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

/-- Every list of the state grows by at most one entry. -/
def Grow {S : Setup} (st st' : FgKeyIndSimState S) : Prop :=
  st'.base.principals.length ≤ st.base.principals.length + 1 ∧
  st'.base.spkBundles.length ≤ st.base.spkBundles.length + 1 ∧
  st'.base.opkEntries.length ≤ st.base.opkEntries.length + 1 ∧
  st'.base.sessions.length ≤ st.base.sessions.length + 1 ∧
  st'.base.respSessions.length ≤ st.base.respSessions.length + 1 ∧
  st'.base.usedRecvOPK.length ≤ st.base.usedRecvOPK.length + 1 ∧
  st'.base.usedRecvNoOPK.length ≤ st.base.usedRecvNoOPK.length + 1 ∧
  st'.base.seenKyberBaseKeys.length ≤ st.base.seenKyberBaseKeys.length + 1 ∧
  st'.base.roCache.length ≤ st.base.roCache.length + 1 ∧
  st'.base.advKeys.length ≤ st.base.advKeys.length + 1 ∧
  st'.rawRoCache.length ≤ st.rawRoCache.length + 1 ∧
  st'.advKeyPows.length ≤ st.advKeyPows.length + 1

/-- Every output in the support of `mx` satisfies `P`. -/
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

theorem Grow.refl {S : Setup} (st : FgKeyIndSimState S) : Grow st st := by
  simp only [Grow]; omega

macro "grow_leaf" : tactic => `(tactic| first
  | exact Grow.refl _
  | (simp only [Grow, List.length_cons, List.length_map]; omega))

macro "grow_loop" : tactic => `(tactic| repeat' (first
  | with_reducible refine AllOut.bind_of (fun _ => ?_)
  | with_reducible refine AllOut.pure_of ?_
  | split
  | dsimp only))

theorem fgRoQueryGdh_grow {S : Setup} (K : Nat) (secrets : Bytes) (st : FgKeyIndSimState S) :
    AllOut (fgRoQueryGdh K secrets st) (fun x => Grow st x.2) := by
  unfold fgRoQueryGdh
  grow_loop
  all_goals grow_leaf

theorem fgRunInitiateGdh_grow {S : Setup} (useDh1 : Bool) (t K : Nat) (U : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) :
    AllOut (fgRunInitiateGdh useDh1 t S K U sid u bundle st) (fun x => Grow st x.2) := by
  unfold fgRunInitiateGdh
  grow_loop
  all_goals grow_leaf

theorem fgRunAcceptOPKGdh_grow {S : Setup} (K : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    AllOut (fgRunAcceptOPKGdh S K k j o hdr st) (fun x => Grow st x.2) := by
  unfold fgRunAcceptOPKGdh
  have hlen := checkAndMarkKyberUsed_snd_length st.base.seenKyberBaseKeys k.val hdr.pqspkId
    hdr.spkId hdr.ekAPk
  generalize checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
    hdr.ekAPk = c at hlen ⊢
  obtain ⟨r, L'⟩ := c
  dsimp only at hlen
  grow_loop
  all_goals grow_leaf

theorem fgRunAcceptNoOPKGdh_grow {S : Setup} (K : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    AllOut (fgRunAcceptNoOPKGdh S K k j l hdr st) (fun x => Grow st x.2) := by
  unfold fgRunAcceptNoOPKGdh
  have hlen := checkAndMarkKyberUsed_snd_length st.base.seenKyberBaseKeys k.val hdr.pqspkId
    hdr.spkId hdr.ekAPk
  generalize checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
    hdr.ekAPk = c at hlen ⊢
  obtain ⟨r, L'⟩ := c
  dsimp only at hlen
  grow_loop
  all_goals grow_leaf

theorem fgGenOPKGdhOpk_grow {S : Setup} (o : Nat) (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (oo : Fin S.N_opk) (st : FgKeyIndSimState S) :
    AllOut (fgGenOPKGdhOpk o S V u j oo st) (fun x => Grow st x.2) := by
  unfold fgGenOPKGdhOpk
  grow_loop
  all_goals grow_leaf

theorem fgRunAcceptOPKGdhOpk_grow {S : Setup} (K : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (o : Fin S.N_opk) (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    AllOut (fgRunAcceptOPKGdhOpk S K k j o hdr st) (fun x => Grow st x.2) := by
  unfold fgRunAcceptOPKGdhOpk
  have hlen := checkAndMarkKyberUsed_snd_length st.base.seenKyberBaseKeys k.val hdr.pqspkId
    hdr.spkId hdr.ekAPk
  generalize checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
    hdr.ekAPk = c at hlen ⊢
  obtain ⟨r, L'⟩ := c
  dsimp only at hlen
  grow_loop
  all_goals grow_leaf

theorem fgKeyIndStep_grow {S : Setup} (useDh1 : Bool) (t s K : Nat) (U V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    ∀ x ∈ support (fgKeyIndStep useDh1 t s S K U V q st), Grow st x.2 := by
  show AllOut (fgKeyIndStep useDh1 t s S K U V q st) (fun x => Grow st x.2)
  cases q with
  | acceptOPK k j o hdr => exact fgRunAcceptOPKGdh_grow _ _ _ _ _ _
  | acceptNoOPK k j l hdr => exact fgRunAcceptNoOPKGdh_grow _ _ _ _ _ _
  | roQuery secrets => exact fgRoQueryGdh_grow _ _ _
  | revealDhSecrets => exact AllOut.pure_of (Grow.refl _)
  | initiateOPK u i bundle =>
    dsimp only [fgKeyIndStep]
    split
    · exact AllOut.pure_of (Grow.refl _)
    · exact fgRunInitiateGdh_grow _ _ _ _ _ _ _ _
  | initiateNoOPK u i bundle =>
    dsimp only [fgKeyIndStep]
    split
    · exact AllOut.pure_of (Grow.refl _)
    · exact fgRunInitiateGdh_grow _ _ _ _ _ _ _ _
  | _ =>
    dsimp only [fgKeyIndStep]
    grow_loop
    all_goals grow_leaf

theorem fgKeyIndStepIk_grow {S : Setup} (t p K : Nat) (U V : Bytes) (q : KeyIndQuery S)
    (st : FgKeyIndSimState S) :
    ∀ x ∈ support (fgKeyIndStepIk t p S K U V q st), Grow st x.2 := by
  unfold fgKeyIndStepIk
  split <;> exact fgKeyIndStep_grow _ _ _ _ _ _ _ _

theorem fgKeyIndStepOpk_grow {S : Setup} (t o K : Nat) (U V : Bytes) (q : KeyIndQuery S)
    (st : FgKeyIndSimState S) :
    ∀ x ∈ support (fgKeyIndStepOpk t o S K U V q st), Grow st x.2 := by
  unfold fgKeyIndStepOpk
  split
  · exact fgGenOPKGdhOpk_grow _ _ _ _ _ _
  · exact fgRunAcceptOPKGdhOpk_grow _ _ _ _ _ _
  · exact fgKeyIndStep_grow _ _ _ _ _ _ _ _

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
