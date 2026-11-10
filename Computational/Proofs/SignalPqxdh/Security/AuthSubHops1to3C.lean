/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.CollisionsC
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
import Computational.Proofs.SignalPqxdh.Security.SigHop

/-!
# PQXDH authentication post-handshake sub-hops 1–3: `PrimBaseSpec` liftings and `ValidAuthHybrid`

Defines `PrimBaseSpec` step liftings, `cacheAuthAdvKeysFixed` commutation lemmas, and the
`ValidAuthHybrid` state-size invariant for `pqxdh_auth` sub-hops 1–3.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security

namespace AuthSubHops1to3

/-! ## `PrimBaseSpec` combinators and `cacheAuthAdvKeys` -/

def cacheAuthAdvKeys {S : Setup} (P : Primitives) (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with
    base := { hst.base with
      advKeys := hst.base.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) } }

def cacheAuthAdvKeysFixed {S : Setup} (P : Primitives) (hst : AuthHybridStateFixed S) :
    AuthHybridStateFixed S :=
  { hst with toAuthHybridState := cacheAuthAdvKeys P hst.toAuthHybridState }

@[simp] theorem cacheAuthAdvKeys_empty (S : Setup) (P : Primitives) (secb : Bool) :
    cacheAuthAdvKeys P (AuthHybridState.empty S secb) = AuthHybridState.empty S secb := rfl

@[simp] theorem cacheAuthAdvKeysFixed_empty (S : Setup) (P : Primitives) (secb : Bool) :
    cacheAuthAdvKeysFixed P (AuthHybridStateFixed.empty S secb) =
      AuthHybridStateFixed.empty S secb := rfl

@[simp] theorem finalizeAuthFixed_cacheAuthAdvKeys {S : Setup}
    (P : Primitives) (secb b' : Bool) (hst : AuthHybridState S) :
    finalizeAuthFixed P secb b' (cacheAuthAdvKeys P hst) =
      finalizeAuthFixed P secb b' hst := rfl

theorem validAdvKeysPow8_cacheAuthAdvKeys {S : Setup} (P : Primitives) (hst : AuthHybridState S) :
    ValidAdvKeysPow8 P (cacheAuthAdvKeys P hst).base.advKeys := by
  intro p hp
  simp only [cacheAuthAdvKeys, List.mem_map] at hp
  rcases hp with ⟨⟨_, pk⟩, _, rfl⟩
  rfl

@[simp] theorem isAdvRegistered_cacheAuthAdvKeys (P : Primitives)
    (advKeys : List (Bytes × Bytes)) (pk : Bytes) :
    isAdvRegistered P (advKeys.map (fun (_, pk') => (P.pow8 pk', pk'))) pk =
      isAdvRegistered P advKeys pk := by
  unfold isAdvRegistered
  simp [List.any_map, Function.comp_def]

@[simp] theorem koskBundleOk_cacheAuthAdvKeys (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    koskBundleOk P principals spkBundles opkEntries
      (advKeys.map (fun (_, pk') => (P.pow8 pk', pk'))) bundle =
      koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  unfold koskBundleOk
  rw [isAdvRegistered_cacheAuthAdvKeys, isAdvRegistered_cacheAuthAdvKeys]
  cases bundle.opkB? <;> simp

@[simp] theorem koskSenderOk_cacheAuthAdvKeys (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes) :
    koskSenderOk P principals (advKeys.map (fun (_, pk') => (P.pow8 pk', pk'))) ikAPk =
      koskSenderOk P principals advKeys ikAPk := by
  unfold koskSenderOk
  rw [isAdvRegistered_cacheAuthAdvKeys]

@[simp] theorem simulateQ_primQ_spqrInitSend (P : Primitives) (k coins : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.spqrInitSend k coins)) =
      pure (P.spqrInitSend k coins) := rfl

@[simp] theorem simulateQ_primQ_spqrInitRecv (P : Primitives) (k msg : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.spqrInitRecv k msg)) =
      pure (P.spqrInitRecv k msg) := rfl

@[simp] theorem simulateQ_primQ_rootCreateChain (P : Primitives) (rk dh : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.rootCreateChain rk dh)) =
      pure (P.rootCreateChain rk dh) := rfl

@[simp] theorem simulateQ_primQ_chainKdfSeed (P : Primitives) (ck : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.chainKdfSeed ck)) =
      pure (P.chainKdfSeed ck) := rfl

@[simp] theorem simulateQ_primQ_chainKdfNext (P : Primitives) (ck : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.chainKdfNext ck)) =
      pure (P.chainKdfNext ck) := rfl

@[simp] theorem simulateQ_primQ_deriveMsgKeys (P : Primitives) (mkSeed : Bytes)
    (salt? : Option Bytes) :
    simulateQ (primBaseImpl P) (primQ (.deriveMsgKeys mkSeed salt?)) =
      pure (P.deriveMsgKeys mkSeed salt?) := rfl

@[simp] theorem simulateQ_primQ_aeadEnc (P : Primitives) (mk : MessageKeys) (ad pt : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.aeadEnc mk ad pt)) =
      pure (P.aeadEnc mk ad pt) := rfl

@[simp] theorem simulateQ_primQ_aeadDec (P : Primitives) (mk : MessageKeys) (ad ct : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.aeadDec mk ad ct)) =
      pure (P.aeadDec mk ad ct) := rfl

@[simp] theorem evalHkdfOrRo_true_eq_pure (P : Primitives)
    (roCache : List (Bytes × DRKey)) (secrets : Bytes) :
    evalHkdfOrRo true P roCache secrets = evalHkdfRoPure roCache secrets := rfl

@[simp] theorem evalRootKdfOrRo_true_eq_pure (P : Primitives)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes))) (rk dh : Bytes) :
    evalRootKdfOrRo true P rootRoCache rk dh = evalRootKdfRoPure rootRoCache rk dh := rfl

theorem primBounded_mapMPrim {α β : Type} (f : α → OracleComp PrimBaseSpec β) (k : Nat)
    (hf : ∀ a, PrimBounded (f a) k) :
    ∀ (xs : List α), PrimBounded (mapMPrim f xs) (xs.length * k)
  | [] => by simp [mapMPrim]
  | x :: xs => by
    simp only [mapMPrim, List.length_cons, Nat.succ_mul]
    refine primBounded_bind_le (xs.length * k) (hf x) (fun y => ?_) (by omega)
    exact primBounded_bind_le 0 (primBounded_mapMPrim f k hf xs) (fun ys => primBounded_pure')

theorem primBounded_mapMPrim_take {α β : Type} (f : α → OracleComp PrimBaseSpec β) (k N : Nat)
    (xs : List α) (hf : ∀ a, PrimBounded (f a) k) :
    PrimBounded (mapMPrim f (xs.take N)) (N * k) :=
  primBounded_mono (primBounded_mapMPrim f k hf (xs.take N))
    (Nat.mul_le_mul_right k (List.length_take_le N xs))

theorem simulateQ_mapMPrim {α β : Type} (P : Primitives)
    (f : α → OracleComp PrimBaseSpec β) (fPure : α → β)
    (hf : ∀ a, simulateQ (primBaseImpl P) (f a) = pure (fPure a)) :
    ∀ (xs : List α), simulateQ (primBaseImpl P) (mapMPrim f xs) = pure (xs.map fPure)
  | [] => by simp [mapMPrim]
  | x :: xs => by
    simp only [mapMPrim, simulateQ_bind, hf x, pure_bind, List.map_cons]
    rw [simulateQ_mapMPrim P f fPure hf xs, pure_bind]
    rfl

theorem primBounded_consumeFirstMPrim {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (mark : α → α) (k : Nat)
    (hp : ∀ a, PrimBounded (p a) k) :
    ∀ (xs : List α), PrimBounded (consumeFirstMPrim p mark xs) (xs.length * k)
  | [] => by simp [consumeFirstMPrim]
  | x :: xs => by
    simp only [consumeFirstMPrim, List.length_cons, Nat.succ_mul]
    refine primBounded_bind_le (xs.length * k) (hp x) (fun b => ?_) (by omega)
    cases b with
    | true => exact primBounded_pure'
    | false =>
      exact primBounded_bind_le 0 (primBounded_consumeFirstMPrim p mark k hp xs)
        (fun _ => primBounded_pure')

theorem primBounded_consumeFirstMPrim_take {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (mark : α → α) (k N : Nat)
    (xs : List α) (hp : ∀ a, PrimBounded (p a) k) :
    PrimBounded (consumeFirstMPrim p mark (xs.take N)) (N * k) :=
  primBounded_mono (primBounded_consumeFirstMPrim p mark k hp (xs.take N))
    (Nat.mul_le_mul_right k (List.length_take_le N xs))

theorem primBounded_matchSentOPKPrim (r : RecvdOPKEvent) (s : SentOPKEvent) :
    PrimBounded (matchSentOPKPrim r s) 10 := by
  unfold matchSentOPKPrim
  refine primBounded_bind_le 9 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 8 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 7 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 6 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 5 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 4 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_matchSentOPKPrim (P : Primitives) (r : RecvdOPKEvent) (s : SentOPKEvent) :
    simulateQ (primBaseImpl P) (matchSentOPKPrim r s) = pure (matchSentOPK P r s) := rfl

theorem simulateQ_consumeFirstMPrim_opk (P : Primitives) (r : RecvdOPKEvent) :
    ∀ (xs : List SentOPKEvent),
      simulateQ (primBaseImpl P)
        (consumeFirstMPrim (matchSentOPKPrim r) (fun s => { s with matched := true }) xs) =
      pure (consumeMatchingSentOPK P r xs)
  | [] => rfl
  | x :: xs => by
    simp only [consumeFirstMPrim, consumeMatchingSentOPK, simulateQ_bind,
      simulateQ_matchSentOPKPrim, pure_bind]
    cases matchSentOPK P r x with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
      rw [simulateQ_consumeFirstMPrim_opk P r xs, pure_bind]
      rfl

theorem primBounded_matchSentNoOPKPrim (r : RecvdNoOPKEvent) (s : SentNoOPKEvent) :
    PrimBounded (matchSentNoOPKPrim r s) 8 := by
  unfold matchSentNoOPKPrim
  refine primBounded_bind_le 7 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 6 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 5 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 4 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_matchSentNoOPKPrim (P : Primitives) (r : RecvdNoOPKEvent) (s : SentNoOPKEvent) :
    simulateQ (primBaseImpl P) (matchSentNoOPKPrim r s) = pure (matchSentNoOPK P r s) := rfl

theorem simulateQ_consumeFirstMPrim_noOpk (P : Primitives) (r : RecvdNoOPKEvent) :
    ∀ (xs : List SentNoOPKEvent),
      simulateQ (primBaseImpl P)
        (consumeFirstMPrim (matchSentNoOPKPrim r) (fun s => { s with matched := true }) xs) =
      pure (consumeMatchingSentNoOPK P r xs)
  | [] => rfl
  | x :: xs => by
    simp only [consumeFirstMPrim, consumeMatchingSentNoOPK, simulateQ_bind,
      simulateQ_matchSentNoOPKPrim, pure_bind]
    cases matchSentNoOPK P r x with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind]
      rw [simulateQ_consumeFirstMPrim_noOpk P r xs, pure_bind]
      rfl

theorem primBounded_checkBundleProvenanceExactPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    PrimBounded (checkBundleProvenanceExactPrim S principals spkBundles opkEntries bundle)
      (S.N_dh * 4) := by
  unfold checkBundleProvenanceExactPrim
  have h4 : S.N_dh * 2 + S.N_dh * 2 = S.N_dh * 4 := by omega
  rw [← h4]
  refine primBounded_bind_le (S.N_dh * 2)
    (primBounded_findHonestPrincipalPrim S principals bundle.ikB) (fun r => ?_)
  cases r with
  | none => exact primBounded_pure'
  | some kp =>
    rcases kp with ⟨k, _⟩
    dsimp only
    cases bundle.opkB? with
    | none =>
      exact primBounded_bind_le 0 (primBounded_pure false (S.N_dh * 2)) (fun _ => primBounded_pure')
    | some opkPair =>
      rcases opkPair with ⟨_, opkPk⟩
      dsimp only
      refine primBounded_bind_le 0
        (primBounded_anyMPrim_take _ 2 S.N_dh opkEntries (fun _ => ?_))
        (fun _ => primBounded_pure')
      refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_checkBundleProvenanceExactPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (hPrin : principals.length ≤ S.N_dh)
    (hOpk : opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (checkBundleProvenanceExactPrim S principals spkBundles opkEntries bundle) =
      pure (checkBundleProvenanceExact P principals spkBundles opkEntries bundle) := by
  unfold checkBundleProvenanceExactPrim checkBundleProvenanceExact
  rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P principals bundle.ikB hPrin, pure_bind]
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, _⟩
    dsimp only
    cases bundle.opkB? with
    | none => rfl
    | some opkPair =>
      rcases opkPair with ⟨_, opkPk⟩
      dsimp only
      rw [List.take_of_length_le hOpk, simulateQ_bind,
          simulateQ_anyMPrim P _
            (fun ((u, _, _), e) => u == k && P.pow8 e.opkPk == P.pow8 opkPk) (fun _ => rfl)
            opkEntries,
          pure_bind]
      rfl

theorem primBounded_checkBundleSpkHonIdealPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) :
    PrimBounded (checkBundleSpkHonIdealPrim S principals spkBundles bundle)
      (S.N_dh * 4) := by
  unfold checkBundleSpkHonIdealPrim
  have h4 : S.N_dh * 2 + S.N_dh * 2 = S.N_dh * 4 := by omega
  rw [← h4]
  refine primBounded_bind_le (S.N_dh * 2)
    (primBounded_findHonestPrincipalPrim S principals bundle.ikB) (fun r => ?_)
  cases r with
  | none => exact primBounded_pure'
  | some kp =>
    rcases kp with ⟨k, pEntry⟩
    dsimp only
    refine primBounded_anyMPrim_take _ 2 S.N_dh spkBundles (fun _ => ?_)
    refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
    exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_checkBundleSpkHonIdealPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (hPrin : principals.length ≤ S.N_dh)
    (hSpk : spkBundles.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (checkBundleSpkHonIdealPrim S principals spkBundles bundle) =
      pure (checkBundleSpkHonIdeal P principals spkBundles bundle) := by
  unfold checkBundleSpkHonIdealPrim checkBundleSpkHonIdeal
  rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P principals bundle.ikB hPrin, pure_bind]
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, pEntry⟩
    dsimp only
    rw [List.take_of_length_le hSpk]
    exact simulateQ_anyMPrim P
      (fun ((u, _), b) => do
        let p1 ← primQ (.pow8 b.spkPk)
        let p2 ← primQ (.pow8 bundle.spkB)
        return (u == k && ((pEntry.corrupted && p1 == p2) || b.spkPk == bundle.spkB)))
      (fun ((u, _), b) =>
        u == k && ((pEntry.corrupted && P.pow8 b.spkPk == P.pow8 bundle.spkB) ||
          b.spkPk == bundle.spkB))
      (fun ⟨⟨_, _⟩, _⟩ => rfl) spkBundles

theorem primBounded_sameOpkPkPrim (o1 o2 : Option Bytes) :
    PrimBounded (sameOpkPkPrim o1 o2) 2 := by
  unfold sameOpkPkPrim
  cases o1 <;> cases o2
  · exact primBounded_pure'
  · exact primBounded_pure'
  · exact primBounded_pure'
  · refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
    exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem primBounded_matchIdealAuthHandshakePrim {S : Setup}
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    PrimBounded (matchIdealAuthHandshakePrim ikBPk spkBPk opkBPk? pqspkBPk hdr s) 10 := by
  unfold matchIdealAuthHandshakePrim
  refine primBounded_bind_le 9 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 8 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 7 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 6 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 5 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 4 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 2 (primBounded_sameOpkPkPrim opkBPk? s.peerOpkPk?) (fun _ => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_matchIdealAuthHandshakePrim {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    simulateQ (primBaseImpl P)
      (matchIdealAuthHandshakePrim ikBPk spkBPk opkBPk? pqspkBPk hdr s) =
      pure (matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr s) := by
  unfold matchIdealAuthHandshakePrim matchIdealAuthHandshake sameOpkPkPrim
  cases opkBPk? <;> cases s.peerOpkPk? <;> rfl

theorem primBounded_allHonestEcPksAuthPrim (S : Setup) (st : AuthState S) :
    PrimBounded (allHonestEcPksAuthPrim S st) (S.N_dh * 5) := by
  unfold allHonestEcPksAuthPrim
  have h1 : S.N_dh * 1 + (S.N_dh * 1 + (S.N_dh * 1 + S.N_dh * 2)) = S.N_dh * 5 := by omega
  rw [← h1]
  refine primBounded_bind_le (S.N_dh * 1 + (S.N_dh * 1 + S.N_dh * 2))
    (primBounded_mapMPrim_take _ 1 S.N_dh st.principals (fun _ => primBounded_primQ _))
    (fun _ => ?_)
  refine primBounded_bind_le (S.N_dh * 1 + S.N_dh * 2)
    (primBounded_mapMPrim_take _ 1 S.N_dh st.spkBundles (fun _ => primBounded_primQ _))
    (fun _ => ?_)
  refine primBounded_bind_le (S.N_dh * 2)
    (primBounded_mapMPrim_take _ 1 S.N_dh st.opkEntries (fun _ => primBounded_primQ _))
    (fun _ => ?_)
  refine primBounded_bind_le 0
    (primBounded_mapMPrim_take _ 2 S.N_dh st.sessions (fun s => ?_)) (fun _ => primBounded_pure')
  exact primBounded_bind_le 1 (primBounded_primQ _) (fun _ => primBounded_primQ _)

theorem simulateQ_allHonestEcPksAuthPrim (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh)
    (hSpk : hst.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.base.opkEntries.length ≤ S.N_dh)
    (hSess : hst.base.sessions.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (allHonestEcPksAuthPrim S hst.base) =
      pure (allHonestEcPksAuth P hst) := by
  unfold allHonestEcPksAuthPrim allHonestEcPksAuth HasAuthState.toAuthState
  dsimp only
  rw [List.take_of_length_le hPrin, List.take_of_length_le hSpk,
      List.take_of_length_le hOpk, List.take_of_length_le hSess,
      simulateQ_bind,
      simulateQ_mapMPrim P _ (fun (_, e) => P.pow8 e.ikAPk) (fun _ => rfl) hst.base.principals,
      pure_bind, simulateQ_bind,
      simulateQ_mapMPrim P _ (fun (_, b) => P.pow8 b.spkPk) (fun _ => rfl) hst.base.spkBundles,
      pure_bind, simulateQ_bind,
      simulateQ_mapMPrim P _ (fun (_, o) => P.pow8 o.opkPk) (fun _ => rfl) hst.base.opkEntries,
      pure_bind, simulateQ_bind,
      simulateQ_mapMPrim P _ (fun s => P.pow8 (P.x25519Base s.ekASk)) (fun _ => rfl)
        hst.base.sessions,
      pure_bind]
  rfl

def ValidRecvKemRecords (P : Primitives) (recvRecs : List RecvKemRecord) : Prop :=
  ∀ r ∈ recvRecs, P.kemDecaps r.pqspkSk r.kemCt = some r.kemSs

theorem hasBadKemShCrRecordsPure_eq {S : Setup} (P : Primitives)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord)
    (hValid : ValidRecvKemRecords P recvRecs) :
    hasBadKemShCrRecordsPure initRecs recvRecs =
      hasBadKemShCrRecords P initRecs recvRecs := by
  unfold hasBadKemShCrRecordsPure hasBadKemShCrRecords
  congr 1
  funext i
  induction recvRecs with
  | nil => rfl
  | cons r rs ih =>
    have hr : P.kemDecaps r.pqspkSk r.kemCt = some r.kemSs := hValid r List.mem_cons_self
    have hbeq : (P.kemDecaps r.pqspkSk r.kemCt == some i.kemSs) = (r.kemSs == i.kemSs) := by
      rw [hr]
      cases h : (r.kemSs == i.kemSs)
      · have hne : r.kemSs ≠ i.kemSs := beq_eq_false_iff_ne.mp h
        exact beq_eq_false_iff_ne.mpr (fun heq => hne (Option.some.inj heq))
      · have heq : r.kemSs = i.kemSs := beq_iff_eq.mp h
        exact beq_iff_eq.mpr (congrArg some heq)
    simp only [List.any_cons, hbeq, ih (fun r' hr' => hValid r' (List.mem_cons_of_mem _ hr'))]

theorem allChallengedCleanAux {S : Setup} (useRo : Bool) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (sessions : List (AuthInitiatorEntry S))
    (hNoSig : sessions.any (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) = false) :
    sessions.all (fun s => !s.challenged || (s.fresh && s.pqspkHonest)) =
      sessions.all (fun s => !s.challenged || authInitCorruptionClause P useRo principals s) := by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hNoSig
    rcases hNoSig with ⟨hs, hss⟩
    simp only [List.all_cons, ih hss]
    congr 1
    congr 1
    unfold authInitCorruptionClause
    cases hfresh : s.fresh with
    | false => rfl
    | true =>
      rw [hfresh] at hs
      cases hpq : s.pqspkHonest with
      | false =>
        rw [hpq] at hs
        simp at hs
      | true =>
        cases useRo <;> simp

theorem allChallengedCleanPure_eq_of_hasBadSigAuth_false {S : Setup}
    (useRo : Bool) (P : Primitives) (hst : AuthHybridState S)
    (hNoSig : hasBadSigAuth hst = false) :
    allChallengedCleanPure hst.base =
      hst.base.sessions.all (fun s =>
        !s.challenged || authInitCorruptionClause P useRo hst.base.principals s) :=
  allChallengedCleanAux useRo P hst.base.principals hst.base.sessions hNoSig

theorem primBounded_finalizeAuthFixedPrim (S : Setup) (secb b' : Bool)
    (finalSt : AuthHybridState S) :
    PrimBounded (finalizeAuthFixedPrim S secb b' finalSt) (S.N_dh * 5) := by
  unfold finalizeAuthFixedPrim
  refine primBounded_bind_le 0 (primBounded_allHonestEcPksAuthPrim S finalSt.base) (fun _ => ?_)
  split_ifs
  · exact primBounded_embedUnif ($ᵗ Bool) 0
  · exact primBounded_pure'
  · exact primBounded_embedUnif ($ᵗ Bool) 0
  · exact primBounded_pure'

theorem simulateQ_finalizeAuthFixedPrim (S : Setup) (P : Primitives)
    (secb b' : Bool) (finalSt : AuthHybridState S)
    (hPrin : finalSt.base.principals.length ≤ S.N_dh)
    (hSpk : finalSt.base.spkBundles.length ≤ S.N_dh)
    (hOpk : finalSt.base.opkEntries.length ≤ S.N_dh)
    (hSess : finalSt.base.sessions.length ≤ S.N_dh)
    (hValidKem : ValidRecvKemRecords P finalSt.recvKemRecs) :
    simulateQ (primBaseImpl P) (finalizeAuthFixedPrim S secb b' finalSt) =
      finalizeAuthFixed P secb b' finalSt := by
  unfold finalizeAuthFixedPrim finalizeAuthFixed
  rw [simulateQ_bind, simulateQ_allHonestEcPksAuthPrim S P finalSt hPrin hSpk hOpk hSess,
      pure_bind, hasBadKemShCrRecordsPure_eq P finalSt.initKemRecs finalSt.recvKemRecs hValidKem]
  have hEc :
    hasDuplicateBytes (allHonestEcPksAuth P finalSt) = hasEcPkCollisionAuth P finalSt := rfl
  have hKem :
    hasBadKemShCrRecords P finalSt.initKemRecs finalSt.recvKemRecs = hasBadKemShCrAuth P finalSt :=
      rfl
  rw [hEc, hKem]
  dsimp only
  by_cases hBad : (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt ||
                   hasKemPkCollisionAuth finalSt || hasBadKemShCrAuth P finalSt) = true
  · simp only [hBad, ↓reduceIte, simulateQ_embedUnif]
  · have hBadF : (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt ||
                  hasKemPkCollisionAuth finalSt || hasBadKemShCrAuth P finalSt) = false :=
      Bool.eq_false_iff.mpr hBad
    have hNoSig : hasBadSigAuth finalSt = false := by
      revert hBadF
      cases hasEcPkCollisionAuth P finalSt <;> cases hasBadSigAuth finalSt <;> simp
    rw [← allChallengedCleanPure_eq_of_hasBadSigAuth_false true P finalSt hNoSig]
    simp only [hBadF, Bool.false_eq_true, ↓reduceIte]
    cases finalSt.base.hasWonAuth
    · split <;> simp [simulateQ_embedUnif]
    · rfl

/-! ## `ValidAuthHybrid` invariant and step liftings -/

/-- State-size and KEM-record invariant on `AuthHybridStateFixed S` for `PrimBaseSpec` simulation. -/
structure ValidAuthHybrid (S : Setup) (P : Primitives) (hst : AuthHybridStateFixed S) : Prop where
  validEc      : ValidEcLists S hst.toAuthHybridState.base.principals
                   hst.toAuthHybridState.base.spkBundles
                   hst.toAuthHybridState.base.opkEntries
                   hst.toAuthHybridState.base.usedSendSessions
  sess_le      : hst.toAuthHybridState.base.sessions.length ≤
                   hst.toAuthHybridState.base.usedSendSessions.length
  ideal_le     : hst.toAuthHybridState.idealSessions.length ≤
                   hst.toAuthHybridState.base.usedSendSessions.length
  sentOPK_le   : hst.toAuthHybridState.base.sentOPKEvents.length ≤
                   hst.toAuthHybridState.base.usedSendSessions.length
  sentNoOPK_le : hst.toAuthHybridState.base.sentNoOPKEvents.length ≤
                   hst.toAuthHybridState.base.usedSendSessions.length
  validKem     : ValidRecvKemRecords P hst.toAuthHybridState.recvKemRecs

theorem validAuthHybrid_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidAuthHybrid S P (AuthHybridStateFixed.empty S secb) :=
  ⟨validEcLists_nil S, le_rfl, le_rfl, le_rfl, le_rfl, fun _ h => by cases h⟩

theorem ValidAuthHybrid.sum_lengths_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.principals.length +
    hst.toAuthHybridState.base.spkBundles.length +
    hst.toAuthHybridState.base.opkEntries.length +
    hst.toAuthHybridState.base.usedSendSessions.length ≤ S.N_dh := by
  let st := hst.toAuthHybridState.base
  let sessPks : List (SessionId S × Bytes) := st.usedSendSessions.map (fun sid => (sid, []))
  have hMap : sessPks.map Prod.fst = st.usedSendSessions := by
    simp [sessPks, List.map_map, Function.comp_def]
  have hV : ValidEcLists S st.principals st.spkBundles st.opkEntries (sessPks.map Prod.fst) := by
    rw [hMap]; exact h.validEc
  have hTag :=
    validTaggedPks_ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries sessPks hV
  have hLen := validTaggedPks_length_le hTag
  unfold ecTaggedFromLists at hLen
  simp only [sessPks, List.length_append, List.length_map] at hLen
  exact hLen

theorem ValidAuthHybrid.principals_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.principals.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega

theorem ValidAuthHybrid.spkBundles_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega

theorem ValidAuthHybrid.opkEntries_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega

theorem ValidAuthHybrid.usedSend_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.usedSendSessions.length ≤ S.N_dh := by
  have := h.sum_lengths_le; omega

theorem ValidAuthHybrid.sessions_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.sessions.length ≤ S.N_dh :=
  le_trans h.sess_le h.usedSend_le

theorem ValidAuthHybrid.idealSessions_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.idealSessions.length ≤ S.N_dh :=
  le_trans h.ideal_le h.usedSend_le

theorem ValidAuthHybrid.sentOPKEvents_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.sentOPKEvents.length ≤ S.N_dh :=
  le_trans h.sentOPK_le h.usedSend_le

theorem ValidAuthHybrid.sentNoOPKEvents_le {S : Setup} {P : Primitives}
    {hst : AuthHybridStateFixed S} (h : ValidAuthHybrid S P hst) :
    hst.toAuthHybridState.base.sentNoOPKEvents.length ≤ S.N_dh :=
  le_trans h.sentNoOPK_le h.usedSend_le

@[simp] theorem consumeMatchingSentOPK_length (P : Primitives) (r : RecvdOPKEvent) :
    ∀ (xs : List SentOPKEvent), (consumeMatchingSentOPK P r xs).2.length = xs.length
  | [] => rfl
  | x :: xs => by
    simp only [consumeMatchingSentOPK]
    split
    · rfl
    · simp [consumeMatchingSentOPK_length P r xs]

@[simp] theorem consumeMatchingSentNoOPK_length (P : Primitives) (r : RecvdNoOPKEvent) :
    ∀ (xs : List SentNoOPKEvent), (consumeMatchingSentNoOPK P r xs).2.length = xs.length
  | [] => rfl
  | x :: xs => by
    simp only [consumeMatchingSentNoOPK]
    split
    · rfl
    · simp [consumeMatchingSentNoOPK_length P r xs]

def RecvFinishTag.toPure {S : Setup} (checkAuth : Bool) (P : Primitives) :
    RecvFinishTag S →
    Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))) →
    AuthResponse × AuthHybridState S
  | .opk k j o kEntry bEntry oEntry usedTriples' msg hstDec =>
    finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec
  | .noOpk k j l kEntry bEntry usedTriples' msg hstDec =>
    finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec

theorem primBounded_recvFinishTag_runPrim (S : Setup) (checkAuth : Bool) (tag : RecvFinishTag S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    PrimBounded (tag.runPrim S checkAuth res?) (S.N_dh * 12) := by
  have h12 : S.N_dh * 2 + S.N_dh * 10 = S.N_dh * 12 := by omega
  cases tag with
  | opk k j o kEntry bEntry oEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.runPrim
    cases res? with
    | none => exact primBounded_pure'
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only
      rw [← h12]
      refine primBounded_bind_le (S.N_dh * 10)
        (primBounded_findHonestPrincipalPrim S hstDec.base.principals msg.hdr.ikAPk) (fun r => ?_)
      cases r with
      | none => exact primBounded_pure'
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        dsimp only
        split_ifs
        · exact primBounded_bind_le 0
            (primBounded_consumeFirstMPrim_take _ _ 10 S.N_dh hstDec.base.sentOPKEvents
              (primBounded_matchSentOPKPrim _))
            (fun _ => primBounded_pure')
        · exact primBounded_pure'
  | noOpk k j l kEntry bEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.runPrim
    cases res? with
    | none => exact primBounded_pure'
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only
      rw [← h12]
      refine primBounded_bind_le (S.N_dh * 10)
        (primBounded_findHonestPrincipalPrim S hstDec.base.principals msg.hdr.ikAPk) (fun r => ?_)
      cases r with
      | none => exact primBounded_pure'
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        dsimp only
        split_ifs
        · exact primBounded_bind_le 0
            (primBounded_consumeFirstMPrim_take _ _ 10 S.N_dh hstDec.base.sentNoOPKEvents
              (fun a => (primBounded_matchSentNoOPKPrim _ a).mono (by omega)))
            (fun _ => primBounded_pure')
        · exact primBounded_pure'

theorem simulateQ_recvFinishTag_runPrim (S : Setup) (checkAuth : Bool) (P : Primitives)
    (tag : RecvFinishTag S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))))
    (hPrin : tag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : tag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : tag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (tag.runPrim S checkAuth res?) =
      pure (tag.toPure checkAuth P res?) := by
  cases tag with
  | opk k j o kEntry bEntry oEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.runPrim RecvFinishTag.toPure finishAuthHybridRecvOPK
    cases res? with
    | none => rfl
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only [RecvFinishTag.hstDec] at hPrin hSentOPK ⊢
      rw [simulateQ_bind,
          simulateQ_findHonestPrincipalPrim S P hstDec.base.principals msg.hdr.ikAPk hPrin,
          pure_bind]
      cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
      | none => rfl
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        dsimp only
        split_ifs
        · rw [List.take_of_length_le hSentOPK, simulateQ_bind,
              simulateQ_consumeFirstMPrim_opk P _ hstDec.base.sentOPKEvents, pure_bind]
          rfl
        · rfl
  | noOpk k j l kEntry bEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.runPrim RecvFinishTag.toPure finishAuthHybridRecvNoOPK
    cases res? with
    | none => rfl
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only [RecvFinishTag.hstDec] at hPrin hSentNoOPK ⊢
      rw [simulateQ_bind,
          simulateQ_findHonestPrincipalPrim S P hstDec.base.principals msg.hdr.ikAPk hPrin,
          pure_bind]
      cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
      | none => rfl
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        dsimp only
        split_ifs
        · rw [List.take_of_length_le hSentNoOPK, simulateQ_bind,
              simulateQ_consumeFirstMPrim_noOpk P _ hstDec.base.sentNoOPKEvents, pure_bind]
          rfl
        · rfl

theorem recvFinishTag_toPure_cacheAuthAdvKeys {S : Setup} (checkAuth : Bool) (P : Primitives)
    (tag : RecvFinishTag S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    (tag.mapState (cacheAuthAdvKeys P)).toPure checkAuth P res? =
      Prod.map id (cacheAuthAdvKeys P) (tag.toPure checkAuth P res?) := by
  cases tag with
  | opk k j o kEntry bEntry oEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.mapState RecvFinishTag.toPure finishAuthHybridRecvOPK cacheAuthAdvKeys
    cases res? with
    | none => rfl
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only
      cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
      | none => rfl
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        dsimp only
        split_ifs <;> rfl
  | noOpk k j l kEntry bEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.mapState RecvFinishTag.toPure finishAuthHybridRecvNoOPK cacheAuthAdvKeys
    cases res? with
    | none => rfl
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      dsimp only
      cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
      | none => rfl
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        dsimp only
        split_ifs <;> rfl

def PreparedAuthRecvPrim.toPure {S : Setup} (checkAuth : Bool) (P : Primitives)
    (p : PreparedAuthRecvPrim S) : PreparedAuthRecv S where
  kEntry                    := p.kEntry
  bEntry                    := p.bEntry
  opkPk?                    := p.opkPk?
  secrets                   := p.secrets
  dhRatchet                 := p.dhRatchet
  isUncorruptedHonestSender := p.isUncorruptedHonestSender
  matchedSess?              := p.matchedSess?
  sameEph                   := p.sameEph
  hstDec                    := p.hstDec
  finish                    := p.finishTag.toPure checkAuth P

def prepareAuthHybridRecvOPKPure {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) : Option (PreparedAuthRecvPrim S) :=
  let st := hst.base
  if st.hasWonAuth then
    none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    none
  else if st.usedRecvOPK.contains (k.val, j.val, o.val) then
    none
  else if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
    none
  else
    match st.principals.find? (fun (idx, _) => idx == k.val),
          st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)),
          st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
    | some (_, kEntry), some (_, bEntry), some (_, oEntry) =>
      if oEntry.consumed then none
      else
        let (replayOk, usedTriples') :=
          checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId
            msg.hdr.ekAPk
        if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then none
        else
          match P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => none
          | some ss =>
            let rRec : RecvKemRecord := {
              k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
              pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
            }
            let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
            let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
            let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
            let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
            let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
            let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
            let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
            let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
            let isUncorruptedHonestSender : Bool :=
              match senderPrincipal? with
              | some (_, sEntry) => !sEntry.corrupted
              | none             => false
            let matchedSess? : Option (IdealAuthSession S) :=
              hstDec.idealSessions.find?
                (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
                  bEntry.pqspkPk msg.hdr)
            let sameEph : Bool :=
              match matchedSess? with
              | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk
              | none   => false
            some {
              kEntry := kEntry, bEntry := bEntry, opkPk? := some oEntry.opkPk,
              secrets := secrets, dhRatchet := dhRatchet,
              isUncorruptedHonestSender := isUncorruptedHonestSender,
              matchedSess? := matchedSess?, sameEph := sameEph, hstDec := hstDec,
              finishTag := .opk k j o kEntry bEntry oEntry usedTriples' msg hstDec }
    | _, _, _ => none

theorem prepareAuthHybridRecvOPKPure_map_toPure {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (prepareAuthHybridRecvOPKPure P k j o msg hst).map (PreparedAuthRecvPrim.toPure true P) =
      prepareAuthHybridRecvOPK true P k j o msg hst := by
  unfold prepareAuthHybridRecvOPKPure prepareAuthHybridRecvOPK
  dsimp only; simp only [Bool.true_and]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  rcases h1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
  rcases h2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    with _ | ⟨_, bEntry⟩ <;>
  rcases h3 : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    with _ | ⟨_, oEntry⟩ <;>
  simp only [h1, h2, h3]
  all_goals try rfl
  split; · rfl
  split; · rfl
  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt <;> rfl

theorem prepareAuthHybridRecvOPKPure_cacheAuthAdvKeys {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeys P hst) =
      (prepareAuthHybridRecvOPKPure P k j o msg hst).map
        (PreparedAuthRecvPrim.mapState (cacheAuthAdvKeys P)) := by
  unfold prepareAuthHybridRecvOPKPure cacheAuthAdvKeys
  dsimp only
  rw [koskSenderOk_cacheAuthAdvKeys]
  repeat (first | rfl | split)

theorem primBounded_prepareAuthHybridRecvOPKPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    PrimBounded (prepareAuthHybridRecvOPKPrim S k j o msg hst) (S.N_dh * 14 + 12) := by
  unfold prepareAuthHybridRecvOPKPrim
  dsimp only
  split; · exact primBounded_pure'
  split
  · exact primBounded_pure'
  · split
    · exact primBounded_pure'
    · have htot : (S.N_dh * 2 + 2) + (S.N_dh * 12 + 10) = S.N_dh * 14 + 12 := by omega
      rw [← htot]
      refine primBounded_bind_le (S.N_dh * 12 + 10)
        (primBounded_koskSenderOkPrim S hst.base.principals hst.base.advKeys msg.hdr.ikAPk)
        (fun koskOk => ?_)
      split
      · exact primBounded_pure'
      · split
        · split
          · exact primBounded_pure'
          · refine primBounded_bind_le (S.N_dh * 12 + 9) (primBounded_primQ _)
              (fun canon => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 12 + 8) (primBounded_primQ _)
              (fun canonEph => ?_) (by omega)
            split
            · exact primBounded_pure'
            · refine primBounded_bind_le (S.N_dh * 12 + 7) (primBounded_primQ _)
                (fun ss? => ?_) (by omega)
              cases ss? with
              | none => exact primBounded_pure'
              | some ss =>
                dsimp only
                refine primBounded_bind_le (S.N_dh * 12 + 6) (primBounded_primQ _)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_primQ _)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le (S.N_dh * 12 + 3) (primBounded_primQ _)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le (S.N_dh * 12 + 2) (primBounded_primQ _)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le (S.N_dh * 10 + 2)
                  (primBounded_findHonestPrincipalPrim S hst.base.principals msg.hdr.ikAPk)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le 2
                  (primBounded_findMPrim_take _ 10 S.N_dh _
                    (primBounded_matchIdealAuthHandshakePrim _ _ _ _ _))
                  (fun matchedSess? => ?_) (by omega)
                cases matchedSess? with
                | none =>
                  exact primBounded_pure'
                | some s =>
                  dsimp only
                  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_) (by omega)
                  exact primBounded_bind_le 0 (primBounded_primQ _)
                    (fun _ => primBounded_pure') (by omega)
        · exact primBounded_pure'

theorem simulateQ_prepareAuthHybridRecvOPKPrim (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh)
    (hIdeal : hst.idealSessions.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.base.advKeys) :
    simulateQ (primBaseImpl P) (prepareAuthHybridRecvOPKPrim S k j o msg hst) =
      pure (prepareAuthHybridRecvOPKPure P k j o msg hst) := by
  unfold prepareAuthHybridRecvOPKPrim prepareAuthHybridRecvOPKPure
  dsimp only
  split; · rfl
  split
  · rfl
  · split
    · rfl
    · rw [simulateQ_bind,
          simulateQ_koskSenderOkPrim S P hst.base.principals hst.base.advKeys
            msg.hdr.ikAPk hPrin hAdv,
          pure_bind]
      split
      · rfl
      · rcases h1 : hst.base.principals.find? (fun (idx, _) => idx == k.val)
          with _ | ⟨_, kEntry⟩ <;>
        rcases h2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
          with _ | ⟨_, bEntry⟩ <;>
        rcases h3 : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
          with _ | ⟨_, oEntry⟩ <;>
        simp only [h1, h2, h3]
        all_goals try rfl
        split
        · rfl
        · rw [simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind,
              simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind]
          split
          · rfl
          · rw [simulateQ_bind, simulateQ_primQ_kemDecaps, pure_bind]
            cases P.kemDecaps _ msg.hdr.kemCt with
            | none => rfl
            | some ss =>
              dsimp only
              repeat rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
              rw [simulateQ_bind,
                  simulateQ_findHonestPrincipalPrim S P hst.base.principals msg.hdr.ikAPk hPrin,
                  pure_bind, List.take_of_length_le hIdeal, simulateQ_bind,
                  simulateQ_findMPrim P _
                    (matchIdealAuthHandshake P _ _ _ _ msg.hdr)
                    (simulateQ_matchIdealAuthHandshakePrim P _ _ _ _ _)
                    hst.idealSessions,
                  pure_bind]
              cases hst.idealSessions.find?
                (matchIdealAuthHandshake P _ _ _ _ msg.hdr) with
              | none => rfl
              | some s => rfl

def prepareAuthHybridRecvNoOPKPure {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) : Option (PreparedAuthRecvPrim S) :=
  let st := hst.base
  if st.hasWonAuth then
    none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val &&
       msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then
    none
  else if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then
    none
  else if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then
    none
  else
    match st.principals.find? (fun (idx, _) => idx == k.val),
          st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | some (_, kEntry), some (_, bEntry) =>
      let (replayOk, usedTriples') :=
        checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then none
      else
        match P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => none
        | some ss =>
          let rRec : RecvKemRecord := {
            k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
            pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss
          }
          let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
          let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
          let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
          let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
          let secrets := buildSecrets dh1 dh2 dh3 none ss
          let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
          let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
          let isUncorruptedHonestSender : Bool :=
            match senderPrincipal? with
            | some (_, sEntry) => !sEntry.corrupted
            | none             => false
          let matchedSess? : Option (IdealAuthSession S) :=
            hstDec.idealSessions.find?
              (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr)
          let sameEph : Bool :=
            match matchedSess? with
            | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk
            | none   => false
          some {
            kEntry := kEntry, bEntry := bEntry, opkPk? := none,
            secrets := secrets, dhRatchet := dhRatchet,
            isUncorruptedHonestSender := isUncorruptedHonestSender,
            matchedSess? := matchedSess?, sameEph := sameEph, hstDec := hstDec,
            finishTag := .noOpk k j l kEntry bEntry usedTriples' msg hstDec }
    | _, _ => none

theorem prepareAuthHybridRecvNoOPKPure_map_toPure {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (prepareAuthHybridRecvNoOPKPure P k j l msg hst).map (PreparedAuthRecvPrim.toPure true P) =
      prepareAuthHybridRecvNoOPK true P k j l msg hst := by
  unfold prepareAuthHybridRecvNoOPKPure prepareAuthHybridRecvNoOPK
  dsimp only; simp only [Bool.true_and]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  rcases h1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
  rcases h2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    with _ | ⟨_, bEntry⟩ <;>
  simp only [h1, h2]
  all_goals try rfl
  split; · rfl
  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt <;> rfl

theorem prepareAuthHybridRecvNoOPKPure_cacheAuthAdvKeys {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeys P hst) =
      (prepareAuthHybridRecvNoOPKPure P k j l msg hst).map
        (PreparedAuthRecvPrim.mapState (cacheAuthAdvKeys P)) := by
  unfold prepareAuthHybridRecvNoOPKPure cacheAuthAdvKeys
  dsimp only
  rw [koskSenderOk_cacheAuthAdvKeys]
  repeat (first | rfl | split)

theorem primBounded_prepareAuthHybridRecvNoOPKPrim (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    PrimBounded (prepareAuthHybridRecvNoOPKPrim S k j l msg hst) (S.N_dh * 14 + 11) := by
  unfold prepareAuthHybridRecvNoOPKPrim
  dsimp only
  split; · exact primBounded_pure'
  split
  · exact primBounded_pure'
  · split
    · exact primBounded_pure'
    · have htot : (S.N_dh * 2 + 2) + (S.N_dh * 12 + 9) = S.N_dh * 14 + 11 := by omega
      rw [← htot]
      refine primBounded_bind_le (S.N_dh * 12 + 9)
        (primBounded_koskSenderOkPrim S hst.base.principals hst.base.advKeys msg.hdr.ikAPk)
        (fun koskOk => ?_)
      split
      · exact primBounded_pure'
      · split
        · refine primBounded_bind_le (S.N_dh * 12 + 8) (primBounded_primQ _)
            (fun canon => ?_) (by omega)
          refine primBounded_bind_le (S.N_dh * 12 + 7) (primBounded_primQ _)
            (fun canonEph => ?_) (by omega)
          split
          · exact primBounded_pure'
          · refine primBounded_bind_le (S.N_dh * 12 + 6) (primBounded_primQ _)
              (fun ss? => ?_) (by omega)
            cases ss? with
            | none => exact primBounded_pure'
            | some ss =>
              dsimp only
              refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_primQ _)
                (fun _ => ?_) (by omega)
              refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _)
                (fun _ => ?_) (by omega)
              refine primBounded_bind_le (S.N_dh * 12 + 3) (primBounded_primQ _)
                (fun _ => ?_) (by omega)
              refine primBounded_bind_le (S.N_dh * 12 + 2) (primBounded_primQ _)
                (fun _ => ?_) (by omega)
              refine primBounded_bind_le (S.N_dh * 10 + 2)
                (primBounded_findHonestPrincipalPrim S hst.base.principals msg.hdr.ikAPk)
                (fun _ => ?_) (by omega)
              refine primBounded_bind_le 2
                (primBounded_findMPrim_take _ 10 S.N_dh _
                  (primBounded_matchIdealAuthHandshakePrim _ _ _ _ _))
                (fun matchedSess? => ?_) (by omega)
              cases matchedSess? with
              | none =>
                exact primBounded_pure'
              | some s =>
                dsimp only
                refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_) (by omega)
                exact primBounded_bind_le 0 (primBounded_primQ _)
                  (fun _ => primBounded_pure') (by omega)
        · exact primBounded_pure'

theorem simulateQ_prepareAuthHybridRecvNoOPKPrim (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh)
    (hIdeal : hst.idealSessions.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.base.advKeys) :
    simulateQ (primBaseImpl P) (prepareAuthHybridRecvNoOPKPrim S k j l msg hst) =
      pure (prepareAuthHybridRecvNoOPKPure P k j l msg hst) := by
  unfold prepareAuthHybridRecvNoOPKPrim prepareAuthHybridRecvNoOPKPure
  dsimp only
  split; · rfl
  split
  · rfl
  · split
    · rfl
    · rw [simulateQ_bind,
          simulateQ_koskSenderOkPrim S P hst.base.principals hst.base.advKeys
            msg.hdr.ikAPk hPrin hAdv,
          pure_bind]
      split
      · rfl
      · rcases h1 : hst.base.principals.find? (fun (idx, _) => idx == k.val)
          with _ | ⟨_, kEntry⟩ <;>
        rcases h2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
          with _ | ⟨_, bEntry⟩ <;>
        simp only [h1, h2]
        all_goals try rfl
        rw [simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind,
            simulateQ_bind, simulateQ_primQ_isCanonical, pure_bind]
        split
        · rfl
        · rw [simulateQ_bind, simulateQ_primQ_kemDecaps, pure_bind]
          cases P.kemDecaps _ msg.hdr.kemCt with
          | none => rfl
          | some ss =>
            dsimp only
            repeat rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
            rw [simulateQ_bind,
                simulateQ_findHonestPrincipalPrim S P hst.base.principals msg.hdr.ikAPk hPrin,
                pure_bind, List.take_of_length_le hIdeal, simulateQ_bind,
                simulateQ_findMPrim P _
                  (matchIdealAuthHandshake P _ _ _ _ msg.hdr)
                  (simulateQ_matchIdealAuthHandshakePrim P _ _ _ _ _)
                  hst.idealSessions,
                pure_bind]
            cases hst.idealSessions.find?
              (matchIdealAuthHandshake P _ _ _ _ msg.hdr) with
            | none => rfl
            | some s => rfl

end AuthSubHops1to3
end SignalPqxdh.Security
