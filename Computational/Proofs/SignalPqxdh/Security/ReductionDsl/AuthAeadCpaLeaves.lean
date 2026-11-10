/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaShallow

/-!
# Leaf Invariants of the Shallow `AeadIndCpa` Steps

Proves the `CpaInv` / `CpaSendLeaf` leaf invariants of the shallow send / non-send / cutoff steps
of the `Auth` `AeadIndCpa` simulator, and `stepAuthOtherPrim_cpa_eq` relating the `useRo`
other-query step to `AuthSubHops1to3.stepAuthOtherPrim` when `hasWonAuth = false`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

section Leaves

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

theorem finishAuthCpaSendFixedPure_inv (n : Nat) (fresh isIdeal : Bool)
    (p : AuthCpaPausePayload S) (ct : Bytes) (hst : AuthHybridStateFixed S)
    (hI : CpaInv n hst) (hro : p.roCache.length ≤ n + 1)
    (hroot : p.rootRoCache.length ≤ n + 1) :
    CpaInv (n + 1) (finishAuthCpaSendFixedPure fresh isIdeal p ct hst).2 := by
  try dsimp only
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩, h17⟩, hw⟩ := hI
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩ <;>
    simp only [finishAuthCpaSendFixedPure] <;> (try split) <;>
    (try simp only [List.length_cons]) <;> omega

theorem evalHkdfOrRoPrim_true_eq (c : List (Bytes × DRKey)) (sec : Bytes) :
    evalHkdfOrRoPrim true c sec = embedUnif (AuthSubHops1to3.evalHkdfRoPure c sec) := by
  unfold evalHkdfOrRoPrim AuthSubHops1to3.evalHkdfRoPure
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases c.find? (fun x => x.1 == sec) with
  | some p => rfl
  | none =>
    simp only [embedUnif, liftComp_bind, liftComp_pure]

theorem stepAuthOtherPrim_cpa_eq (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hw : hst.toAuthHybridState.base.hasWonAuth = false)
    (hq : (match q with
      | .sendOPK .. | .sendNoOPK .. | .recvOPK .. | .recvNoOPK .. | .revealDhSecrets => false
      | _ => true) = true) :
    stepAuthOtherPrim true S q hst = AuthSubHops1to3.stepAuthOtherPrim S q hst := by
  cases q <;> simp only [reduceCtorEq] at hq <;>
    simp only [SignalPqxdh.Security.stepAuthOtherPrim, AuthSubHops1to3.stepAuthOtherPrim, hw,
      Bool.false_eq_true, ite_false, evalHkdfOrRoPrim_true_eq, Bool.not_true]
  all_goals rfl

theorem aeadHkdfRoPure_length_le {n : Nat} (c : List (Bytes × DRKey)) (sec : Bytes)
    (h : c.length ≤ n) :
    AllLeaves (fun p => p.2.length ≤ n + 1) (SignalPqxdh.Security.evalHkdfRoPure c sec) := by
  unfold SignalPqxdh.Security.evalHkdfRoPure
  cases c.find? (fun x => x.1 == sec) with
  | some p => rcases p with ⟨_, _⟩; exact AllLeaves.pure (by simp; omega)
  | none => exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by simp; omega))

theorem aeadRootKdfRoPure_length_le {n : Nat}
    (c : List ((Bytes × Bytes) × (Bytes × Bytes))) (rk dh : Bytes) (h : c.length ≤ n) :
    AllLeaves (fun p => p.2.length ≤ n + 1) (SignalPqxdh.Security.evalRootKdfRoPure c rk dh) := by
  unfold SignalPqxdh.Security.evalRootKdfRoPure
  cases c.find? (fun x => x.1 == (rk, dh)) with
  | some p => rcases p with ⟨_, _⟩; exact AllLeaves.pure (by simp; omega)
  | none =>
    exact AllLeaves.bind_const _ (fun _ =>
      AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by simp; omega)))

theorem evalHkdfOrRoPrim_true_length_le {n : Nat} (c : List (Bytes × DRKey)) (sec : Bytes)
    (h : c.length ≤ n) :
    AllLeaves (fun p => p.2.length ≤ n + 1) (evalHkdfOrRoPrim true c sec) := by
  unfold evalHkdfOrRoPrim
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  cases c.find? (fun x => x.1 == sec) with
  | some p => rcases p with ⟨_, _⟩; exact AllLeaves.pure (by simp; omega)
  | none => exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by simp; omega))

def PrepCpaOk {S : Setup} (n : Nat) (m0 m1 : Bytes) :
    Option (Bool × Bool × AuthCpaPausePayload S) → Prop
  | none => True
  | some (_, _, p) =>
    p.roCache.length ≤ n + 1 ∧ p.rootRoCache.length ≤ n + 1 ∧ p.m0 = m0 ∧ p.m1 = m1

theorem prepAuthCpaSendFixedPrim_leaves (n : Nat) (sid : SessionId S)
    (u : Fin S.N_id) (b : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
    (hI : CpaInv n hst) :
    AllLeaves (PrepCpaOk n m0 m1) (prepAuthCpaSendFixedPrim S sid u b m0 m1 hst) := by
  unfold prepAuthCpaSendFixedPrim
  dsimp only
  split
  rotate_left
  · exact AllLeaves.pure trivial
  refine AllLeaves.bind_const _ (fun peer => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun kosk => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun kem => ?_)
  rcases kem with _ | ⟨ss, kemCt⟩
  · exact AllLeaves.pure trivial
  dsimp only
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun prov => ?_)
  refine AllLeaves.bind_const _ (fun spkHonIdeal => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun dr hdr => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact AllLeaves.bind_const _ (fun _ =>
        AllLeaves.pure (Nat.le_trans hI.bnd.roCache_le (Nat.le_succ n)))
    · exact AllLeaves.embedUnif (aeadHkdfRoPure_length_le _ _ hI.bnd.roCache_le)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun rr hrr => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.pure (Nat.le_trans hI.bnd.rootRoCache_le (Nat.le_succ n))))
    · exact AllLeaves.embedUnif (aeadRootKdfRoPure_length_le _ _ _ hI.bnd.rootRoCache_le)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun spqr => ?_)
  rcases spqr with _ | ⟨_, _, _⟩
  · exact AllLeaves.pure trivial
  · exact AllLeaves.pure ⟨hdr, hrr, rfl, rfl⟩

theorem tryPauseAuthCpaSendFixedPrim_leaves (allowPause : Bool) (cut n : Nat) (sid : SessionId S)
    (u : Fin S.N_id) (b : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
    (hI : CpaInv n hst) :
    AllLeaves (CpaSendLeaf n)
      (tryPauseAuthCpaSendFixedPrim allowPause cut S sid u b m0 m1 hst) := by
  have hInl : ∀ (r : AuthResponse) (h : AuthHybridStateFixed S), CpaInv (n + 1) h →
      CpaSendLeaf n (.inl (r, h)) := fun _ _ hh => hh
  unfold tryPauseAuthCpaSendFixedPrim
  dsimp only
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hInl _ _ (hI.mono (Nat.le_succ n))))
    (fun hlen => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hInl _ _ (hI.mono (Nat.le_succ n))))
    (fun _ => ?_)
  refine AllLeaves.bind (prepAuthCpaSendFixedPrim_leaves S n sid u b m0 m1 hst hI)
    (fun prep hprep => ?_)
  rcases prep with _ | ⟨fresh, ideal, rawP⟩
  · exact AllLeaves.pure (hInl _ _ (hI.mono (Nat.le_succ n)))
  obtain ⟨hro, hroot, hm0, hm1⟩ := hprep
  have hlen' : m0.length = m1.length := by simpa using hlen
  dsimp only
  refine AllLeaves.ite fresh (fun _ => ?_) (fun _ => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact AllLeaves.pure (show CpaPauseInv n _ _ _ from
        ⟨rfl, hm0.symm, hm1.symm, by simpa [hm0, hm1] using hlen', hI, hro, hroot⟩)
    · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
      exact AllLeaves.pure (hInl _ _ (finishAuthCpaSendFixedPure_inv S n _ _ _ _ _ hI hro hroot))
  · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
    exact AllLeaves.pure (hInl _ _ (finishAuthCpaSendFixedPure_inv S n _ _ _ _ _ hI hro hroot))

set_option hygiene false in
macro "cpa_close" : tactic => `(tactic| (
  try dsimp only
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩, h17⟩, hw⟩ := hI
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩ <;>
    (try split) <;> (try simp only [List.length_cons, List.length_map]) <;> omega))

theorem stepAuthOtherPrim_true_leaves (n : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hI : CpaInv n hst) :
    AllLeaves (fun x => CpaInv (n + 1) x.2) (stepAuthOtherPrim true S q hst) := by
  cases q <;> unfold SignalPqxdh.Security.stepAuthOtherPrim <;> dsimp only
  case roQuery secrets =>
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n))) (fun _ => ?_)
    refine AllLeaves.bind (evalHkdfOrRoPrim_true_length_le _ _ hI.bnd.roCache_le) ?_
    intro x hx
    exact AllLeaves.pure (by cpa_close)
  case roRootQuery rk dh =>
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n))) (fun _ => ?_)
    refine AllLeaves.bind
      (AllLeaves.embedUnif (aeadRootKdfRoPure_length_le _ _ _ hI.bnd.rootRoCache_le)) ?_
    intro x hx
    exact AllLeaves.pure (by cpa_close)
  all_goals repeat (first
    | exact AllLeaves.pure (hI.mono (Nat.le_succ n))
    | (refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine AllLeaves.bind_const _ (fun _ => ?_)))
  all_goals exact AllLeaves.pure (by cpa_close)

def RecvSchedOk {S : Setup} (n : Nat)
    (x : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) × AuthMkSaltCache S) : Prop :=
  x.2.length ≤ n + 1 ∧ ∀ dk rk1 ck pt ro root, x.1 = some (dk, rk1, ck, pt, ro, root) →
    ro.length ≤ n + 1 ∧ root.length ≤ n + 1

theorem evalAuthRecvScheduleCpaFixedPrim_leaves (n : Nat) (hstDec : AuthHybridStateFixed S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes) (secrets : Bytes)
    (msg : PreKeyMsg)
    (hro : hstDec.toAuthHybridState.base.roCache.length ≤ n)
    (hroot : hstDec.toAuthHybridState.base.rootRoCache.length ≤ n)
    (hmk : hstDec.mkSaltCache.length ≤ n) :
    AllLeaves (RecvSchedOk n)
      (evalAuthRecvScheduleCpaFixedPrim S hstDec kEntry bEntry opkPk? secrets msg) := by
  unfold evalAuthRecvScheduleCpaFixedPrim
  dsimp only
  refine AllLeaves.bind_const _ (fun sender => ?_)
  refine AllLeaves.bind_const _ (fun matched => ?_)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun dr hdr => ?_)
  · rcases matched with _ | s
    · dsimp only
      refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
      · exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (Nat.le_trans hro (Nat.le_succ n)))
      · exact AllLeaves.embedUnif (aeadHkdfRoPure_length_le _ _ hro)
    · exact AllLeaves.pure (Nat.le_trans hro (Nat.le_succ n))
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun sameEph => ?_)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun rr hrr => ?_)
  · rcases matched with _ | s
    · dsimp only
      refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
      · exact AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
          AllLeaves.pure (Nat.le_trans hroot (Nat.le_succ n))))
      · exact AllLeaves.embedUnif (aeadRootKdfRoPure_length_le _ _ _ hroot)
    · dsimp only
      refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
      · exact AllLeaves.pure (Nat.le_trans hroot (Nat.le_succ n))
      · exact AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
          AllLeaves.pure (Nat.le_trans hroot (Nat.le_succ n))))
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun spqr => ?_)
  rcases spqr with _ | ⟨_, salt⟩
  · exact AllLeaves.pure ⟨Nat.le_trans hmk (Nat.le_succ n), fun _ _ _ _ _ _ h => by cases h⟩
  have hsome : ∀ (dk : DRKey) (rk1 ck pt : Bytes) (c : AuthMkSaltCache S),
      c.length ≤ n + 1 → RecvSchedOk n (some (dk, rk1, ck, pt, dr.2, rr.2), c) :=
    fun _ _ _ _ _ hc => ⟨hc, fun _ _ _ _ _ _ h => by
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, -, -, rfl, rfl⟩ := h
      exact ⟨hdr, hrr⟩⟩
  have hnone : ∀ (c : AuthMkSaltCache S), c.length ≤ n + 1 → RecvSchedOk n (none, c) :=
    fun _ hc => ⟨hc, fun _ _ _ _ _ _ h => by cases h⟩
  rcases matched with _ | s <;> dsimp only
  · refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun mk hmk' => ?_)
    · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_) <;>
        exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (Nat.le_trans hmk (Nat.le_succ n)))
    · refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hnone _ hmk')) (fun _ => ?_)
      refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hnone _ hmk')) (fun _ => ?_)
      refine AllLeaves.bind_const _ (fun pt? => ?_)
      rcases pt? with _ | pt
      · exact AllLeaves.pure (hnone _ hmk')
      · exact AllLeaves.pure (hsome _ _ _ _ _ hmk')
  · refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun mk hmk' => ?_)
    · refine AllLeaves.ite _ (fun _ => AllLeaves.pure (Nat.le_trans hmk (Nat.le_succ n)))
        (fun _ => ?_)
      refine AllLeaves.ite _ (fun _ => ?_) (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.pure (Nat.le_trans hmk (Nat.le_succ n))))
      split
      · exact AllLeaves.pure (Nat.le_trans hmk (Nat.le_succ n))
      · exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by simp; omega))
    · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
      · exact AllLeaves.ite _ (fun _ => AllLeaves.pure (hsome _ _ _ _ _ hmk'))
          (fun _ => AllLeaves.pure (hnone _ hmk'))
      · refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hnone _ hmk')) (fun _ => ?_)
        refine AllLeaves.bind_const _ (fun pt? => ?_)
        rcases pt? with _ | pt
        · exact AllLeaves.pure (hnone _ hmk')
        · exact AllLeaves.pure (hsome _ _ _ _ _ hmk')

theorem stepAuthCpaNonSendPrim_leaves (n : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hI : CpaInv n hst) :
    AllLeaves (fun x => CpaInv (n + 1) x.2) (stepAuthCpaNonSendPrim S q hst) := by
  have hT := fun k p sp e =>
    checkAndMarkKyberUsed_length_le hst.toAuthHybridState.base.seenKyberBaseKeys k p sp e
      hI.bnd.usedKyberTriples_le
  cases q <;> unfold stepAuthCpaNonSendPrim <;> dsimp only
  case recvOPK k j o msg =>
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
    split <;> try exact AllLeaves.pure (by cpa_close)
    split <;> try exact AllLeaves.pure (by cpa_close)
    split <;> try exact AllLeaves.pure (by cpa_close)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
    · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
      refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
      refine AllLeaves.bind_const _ (fun ss? => ?_)
      rcases ss? with _ | ss
      · exact AllLeaves.pure (by cpa_close)
      dsimp only
      have := hT k msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))))
      refine AllLeaves.bind (evalAuthRecvScheduleCpaFixedPrim_leaves S n _ _ _ _ _ _
        hI.bnd.roCache_le hI.bnd.rootRoCache_le hI.bnd.mkSaltCache_le) ?_
      intro x ⟨hc, hres⟩
      split
      · next drKey rk1 ck1_1 pt ro root heq =>
        obtain ⟨hro', hroot'⟩ := hres _ _ _ _ _ _ heq
        exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by cpa_close))
      · exact AllLeaves.pure (by cpa_close)
  case recvNoOPK k j l msg =>
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
    split <;> try exact AllLeaves.pure (by cpa_close)
    split <;> try exact AllLeaves.pure (by cpa_close)
    · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
      refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_close)) (fun _ => ?_)
      refine AllLeaves.bind_const _ (fun ss? => ?_)
      rcases ss? with _ | ss
      · exact AllLeaves.pure (by cpa_close)
      dsimp only
      have := hT k msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.bind_const _ (fun _ => ?_)))
      refine AllLeaves.bind (evalAuthRecvScheduleCpaFixedPrim_leaves S n _ _ _ _ _ _
        hI.bnd.roCache_le hI.bnd.rootRoCache_le hI.bnd.mkSaltCache_le) ?_
      intro x ⟨hc, hres⟩
      split
      · next drKey rk1 ck1_1 pt ro root heq =>
        obtain ⟨hro', hroot'⟩ := hres _ _ _ _ _ _ heq
        exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by cpa_close))
      · exact AllLeaves.pure (by cpa_close)
  all_goals first
    | exact AllLeaves.pure (hI.mono (Nat.le_succ n))
    | exact stepAuthOtherPrim_true_leaves S n _ hst hI

theorem stepAuthCpaCutoffPrim_leaves (cut n : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hI : CpaInv n hst) :
    AllLeaves (fun x => CpaInv (n + 1) x.2) (stepAuthCpaCutoffPrim cut S q hst) := by
  have hSend : ∀ (sid : SessionId S) (u : Fin S.N_id) (b : PreKeyBundleInput) (m0 m1 : Bytes),
      AllLeaves (fun x => CpaInv (n + 1) x.2)
        (runAuthSendCpaCutoffPrim cut S sid u b m0 m1 hst) := by
    intro sid u b m0 m1
    unfold runAuthSendCpaCutoffPrim
    refine AllLeaves.bind (tryPauseAuthCpaSendFixedPrim_leaves S false cut n sid u b m0 m1 hst hI)
      (fun res hres => ?_)
    rcases res with ⟨r, h⟩ | _
    · exact AllLeaves.pure hres
    · exact AllLeaves.pure (hI.mono (Nat.le_succ n))
  cases q <;> unfold stepAuthCpaCutoffPrim <;> dsimp only
  case sendOPK u i b m0 m1 =>
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n))) (fun _ => hSend ..)
  case sendNoOPK u i b m0 m1 =>
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n))) (fun _ => hSend ..)
  all_goals exact stepAuthCpaNonSendPrim_leaves S n _ hst hI

/-! ## Creation-order slot leaf invariants -/

theorem finishAuthCpaSendFixedPure_ideal_le (n : Nat) (fresh isIdeal : Bool)
    (p : AuthCpaPausePayload S) (ct : Bytes) (hst : AuthHybridStateFixed S)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ n) :
    (finishAuthCpaSendFixedPure fresh isIdeal p ct hst).2.toAuthHybridState.idealSessions.length ≤
      n + 1 := by
  cases isIdeal <;>
    simp only [finishAuthCpaSendFixedPure, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
    omega

theorem finishAuthCpaSendFixedPure_slot_inv (n ns' : Nat) (fresh isIdeal : Bool)
    (p : AuthCpaPausePayload S) (ct : Bytes) (hst : AuthHybridStateFixed S)
    (hI : CpaInv n hst) (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ n)
    (hns' : ns' ≤ n + 1) (hro : p.roCache.length ≤ n + 1)
    (hroot : p.rootRoCache.length ≤ n + 1) :
    CpaSlotInv (n + 1) (ns', (finishAuthCpaSendFixedPure fresh isIdeal p ct hst).2) :=
  ⟨finishAuthCpaSendFixedPure_inv S n fresh isIdeal p ct hst hI hro hroot,
   finishAuthCpaSendFixedPure_ideal_le S n fresh isIdeal p ct hst hIdeal,
   hns'⟩

theorem cpaTryPauseSendSlotPrim_leaves (allowPause : Bool) (cut n : Nat) (sid : SessionId S)
    (u : Fin S.N_id) (b : PreKeyBundleInput) (m0 m1 : Bytes) (shst : CpaSlotSt S)
    (hI : CpaSlotInv n shst) :
    AllLeaves (CpaSlotSendLeaf cut n)
      (cpaTryPauseSendSlotPrim allowPause cut S sid u b m0 m1 shst) := by
  rcases shst with ⟨ns, hst⟩
  have hInl : ∀ (r : AuthResponse) (sh : CpaSlotSt S), CpaSlotInv (n + 1) sh →
      CpaSlotSendLeaf cut n (.inl (r, sh)) := fun _ _ hh => hh
  unfold cpaTryPauseSendSlotPrim
  dsimp only
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hInl _ _ (hI.mono (Nat.le_succ n))))
    (fun hlen => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (hInl _ _ (hI.mono (Nat.le_succ n))))
    (fun _ => ?_)
  refine AllLeaves.bind (prepAuthCpaSendFixedPrim_leaves S n sid u b m0 m1 hst hI.inv)
    (fun prep hprep => ?_)
  rcases prep with _ | ⟨fresh, ideal, rawP⟩
  · exact AllLeaves.pure (hInl _ _ (hI.mono (Nat.le_succ n)))
  obtain ⟨hro, hroot, hm0, hm1⟩ := hprep
  have hlen' : m0.length = m1.length := by simpa using hlen
  dsimp only
  refine AllLeaves.ite fresh (fun _ => ?_) (fun _ => ?_)
  · refine AllLeaves.ite _ (fun hp => ?_) (fun _ => ?_)
    · have hns : ns = cut := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact hp.2
      exact AllLeaves.pure (show CpaSlotPauseInv cut n _ _ _ from
        ⟨⟨rfl, hm0.symm, hm1.symm, by simpa [hm0, hm1] using hlen', hI.inv, hro, hroot⟩,
         hI.ideal_le, hI.slot_le, hns⟩)
    · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
      exact AllLeaves.pure (hInl _ _
        (finishAuthCpaSendFixedPure_slot_inv S n (ns + 1) _ _ _ _ _ hI.inv hI.ideal_le
          (Nat.succ_le_succ hI.slot_le) hro hroot))
  · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
    exact AllLeaves.pure (hInl _ _
      (finishAuthCpaSendFixedPure_slot_inv S n ns _ _ _ _ _ hI.inv hI.ideal_le
        (Nat.le_trans hI.slot_le (Nat.le_succ n)) hro hroot))

set_option hygiene false in
macro "cpa_slot_close" : tactic => `(tactic| (
  refine ⟨by cpa_close, ?_⟩
  try dsimp only
  omega))

theorem stepAuthOtherPrim_true_ideal_leaves (n : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ n) :
    AllLeaves (fun x => CpaInv (n + 1) x.2 ∧
        x.2.toAuthHybridState.idealSessions.length ≤ n + 1)
      (stepAuthOtherPrim true S q hst) := by
  cases q <;> unfold SignalPqxdh.Security.stepAuthOtherPrim <;> dsimp only
  case roQuery secrets =>
    refine AllLeaves.ite _
      (fun _ => AllLeaves.pure ⟨hI.mono (Nat.le_succ n), Nat.le_trans hIdeal (Nat.le_succ n)⟩)
      (fun _ => ?_)
    refine AllLeaves.bind (evalHkdfOrRoPrim_true_length_le _ _ hI.bnd.roCache_le) ?_
    intro x hx
    exact AllLeaves.pure (by cpa_slot_close)
  case roRootQuery rk dh =>
    refine AllLeaves.ite _
      (fun _ => AllLeaves.pure ⟨hI.mono (Nat.le_succ n), Nat.le_trans hIdeal (Nat.le_succ n)⟩)
      (fun _ => ?_)
    refine AllLeaves.bind
      (AllLeaves.embedUnif (aeadRootKdfRoPure_length_le _ _ _ hI.bnd.rootRoCache_le)) ?_
    intro x hx
    exact AllLeaves.pure (by cpa_slot_close)
  all_goals repeat (first
    | exact AllLeaves.pure ⟨hI.mono (Nat.le_succ n), Nat.le_trans hIdeal (Nat.le_succ n)⟩
    | (refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_))
    | split
    | (refine AllLeaves.bind_const _ (fun _ => ?_)))
  all_goals exact AllLeaves.pure (by cpa_slot_close)

theorem stepAuthCpaNonSendPrim_ideal_leaves (n : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst)
    (hIdeal : hst.toAuthHybridState.idealSessions.length ≤ n) :
    AllLeaves (fun x => CpaInv (n + 1) x.2 ∧
        x.2.toAuthHybridState.idealSessions.length ≤ n + 1)
      (stepAuthCpaNonSendPrim S q hst) := by
  have hT := fun k p sp e =>
    checkAndMarkKyberUsed_length_le hst.toAuthHybridState.base.seenKyberBaseKeys k p sp e
      hI.bnd.usedKyberTriples_le
  cases q <;> unfold stepAuthCpaNonSendPrim <;> dsimp only
  case recvOPK k j o msg =>
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
    split <;> try exact AllLeaves.pure (by cpa_slot_close)
    split <;> try exact AllLeaves.pure (by cpa_slot_close)
    split <;> try exact AllLeaves.pure (by cpa_slot_close)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
    · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
      refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
      refine AllLeaves.bind_const _ (fun ss? => ?_)
      rcases ss? with _ | ss
      · exact AllLeaves.pure (by cpa_slot_close)
      dsimp only
      have := hT k msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))))
      refine AllLeaves.bind (evalAuthRecvScheduleCpaFixedPrim_leaves S n _ _ _ _ _ _
        hI.bnd.roCache_le hI.bnd.rootRoCache_le hI.bnd.mkSaltCache_le) ?_
      intro x ⟨hc, hres⟩
      split
      · next drKey rk1 ck1_1 pt ro root heq =>
        obtain ⟨hro', hroot'⟩ := hres _ _ _ _ _ _ heq
        exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by cpa_slot_close))
      · exact AllLeaves.pure (by cpa_slot_close)
  case recvNoOPK k j l msg =>
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
    split <;> try exact AllLeaves.pure (by cpa_slot_close)
    split <;> try exact AllLeaves.pure (by cpa_slot_close)
    · refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
      refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by cpa_slot_close)) (fun _ => ?_)
      refine AllLeaves.bind_const _ (fun ss? => ?_)
      rcases ss? with _ | ss
      · exact AllLeaves.pure (by cpa_slot_close)
      dsimp only
      have := hT k msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.bind_const _ (fun _ => ?_)))
      refine AllLeaves.bind (evalAuthRecvScheduleCpaFixedPrim_leaves S n _ _ _ _ _ _
        hI.bnd.roCache_le hI.bnd.rootRoCache_le hI.bnd.mkSaltCache_le) ?_
      intro x ⟨hc, hres⟩
      split
      · next drKey rk1 ck1_1 pt ro root heq =>
        obtain ⟨hro', hroot'⟩ := hres _ _ _ _ _ _ heq
        exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by cpa_slot_close))
      · exact AllLeaves.pure (by cpa_slot_close)
  all_goals first
    | exact AllLeaves.pure ⟨hI.mono (Nat.le_succ n), Nat.le_trans hIdeal (Nat.le_succ n)⟩
    | exact stepAuthOtherPrim_true_ideal_leaves S n _ hst hI hIdeal

theorem cpaStepCutoffSlotPrim_leaves (cut n : Nat) (q : AuthQuery S) (shst : CpaSlotSt S)
    (hI : CpaSlotInv n shst) :
    AllLeaves (fun x => CpaSlotInv (n + 1) x.2) (cpaStepCutoffSlotPrim cut S q shst) := by
  have hSend : ∀ (sid : SessionId S) (u : Fin S.N_id) (b : PreKeyBundleInput) (m0 m1 : Bytes),
      AllLeaves (fun x => CpaSlotInv (n + 1) x.2)
        (cpaRunSendCutoffSlotPrim cut S sid u b m0 m1 shst) := by
    intro sid u b m0 m1
    unfold cpaRunSendCutoffSlotPrim
    refine AllLeaves.bind (cpaTryPauseSendSlotPrim_leaves S false cut n sid u b m0 m1 shst hI)
      (fun res hres => ?_)
    rcases res with ⟨r, sh⟩ | _
    · exact AllLeaves.pure hres
    · exact AllLeaves.pure (hI.mono (Nat.le_succ n))
  cases q <;> unfold cpaStepCutoffSlotPrim <;> dsimp only
  case sendOPK u i b m0 m1 =>
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n))) (fun _ => hSend ..)
  case sendNoOPK u i b m0 m1 =>
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n))) (fun _ => hSend ..)
  all_goals
    refine AllLeaves.bind
      (stepAuthCpaNonSendPrim_ideal_leaves S n _ shst.2 hI.inv hI.ideal_le)
      (fun x ⟨hinv, hideal⟩ =>
        AllLeaves.pure ⟨hinv, hideal, Nat.le_trans hI.slot_le (Nat.le_succ n)⟩)

end Leaves

end SignalPqxdh.Security.ReductionDsl.AuthAead
