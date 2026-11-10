/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.SigHopC
public import Computational.Proofs.SignalPqxdh.Security.SigHop
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopA
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_ReductionsAuthHandshake
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyA

/-!
# One-Key Simplified `Auth` Simulator

Defines the simplified `Auth` oracle simulator `pqxdhAuthSimImpl1Key` over `pqxdhAuthImpl1KeyG` and
relates it to `pqxdhAuthWithProvImpl1Key` via `projAuthSim`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory
open SignalPqxdh
open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

/-- Simplified one-key `Auth` oracle omitting win/event logs and caching `(P.pow8 pk, pk)` in
`advKeys`. -/
def pqxdhAuthSimImpl1Key (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthState S) ProbComp) := fun q =>
  match q with
  | .sendOPK u i bundle m0 m1 => do
    if bundle.opkB?.isNone then return .noneResp
    runAuthSendSim S P (.sendOPK u i) u bundle m0 m1
  | .sendNoOPK u i bundle m0 m1 => do
    if bundle.opkB?.isSome then return .noneResp
    runAuthSendSim S P (.sendNoOPK u i) u bundle m0 m1
  | .recvOPK k j o msg => do
    let st ← get
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvOPK.contains (k.val, j.val, o.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let some (_, oEntry) := st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
      | return .noneResp
    if oEntry.consumed then return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ←
      liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    let opkEntries' := st.opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some _ =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvHonestResp
    | none =>
      set { st with
        opkEntries       := opkEntries'
        usedRecvOPK      := (k.val, j.val, o.val) :: st.usedRecvOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | .recvNoOPK k j l msg => do
    let st ← get
    if !(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32) then
      return .noneResp
    if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then return .noneResp
    if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then return .noneResp
    let some (_, kEntry) := st.principals.find? (fun (idx, _) => idx == k.val)
      | return .noneResp
    let some (_, bEntry) := st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
      | return .noneResp
    let (replayOk, usedTriples') :=
      checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
    if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then return .noneResp
    let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return .noneResp
    let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
    let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
    let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
    let secrets := buildSecrets dh1 dh2 dh3 none ss
    let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
    let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
    let ((rk1, ck1_0), rootRoCache') ←
      liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
    let mkSeed := P.chainKdfSeed ck1_0
    let ck1_1 := P.chainKdfNext ck1_0
    let some (_pqrStB, spqrSalt?) := P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg
      | return .noneResp
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let some pt := P.aeadDec deriveMessageKeys ad msg.aeadCt
      | return .noneResp
    match findHonestPrincipal P st.principals msg.hdr.ikAPk with
    | some _ =>
      set { st with
        usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvHonestResp
    | none =>
      set { st with
        usedRecvNoOPK    := (k.val, j.val, l.val) :: st.usedRecvNoOPK
        seenKyberBaseKeys := usedTriples'
        roCache          := roCache'
        rootRoCache      := rootRoCache' }
      return .recvUnfreshResp drKey rk1 ck1_1 pt
  | .registerKey sk => do
    let st ← get
    if sk.length != 32 then return .noneResp
    let pk := P.x25519Base sk
    let pk8 := P.pow8 pk
    set { st with advKeys := (pk8, pk) :: st.advKeys }
    return .pkResp pk
  | q_other => pqxdhAuthImpl1KeyG true true S P q_other

theorem pqxdhAuthWithProvImpl1Key_eq_1KeyG (S : Setup) (P : Primitives) (provFn : ProvFnType)
    (q : AuthQuery S)
    (h1 : ∀ u i bundle m0 m1, q ≠ .sendOPK u i bundle m0 m1)
    (h2 : ∀ u i bundle m0 m1, q ≠ .sendNoOPK u i bundle m0 m1) :
    pqxdhAuthWithProvImpl1Key S P provFn q = pqxdhAuthImpl1KeyG true true S P q := by
  cases q with
  | initPrin u => rfl
  | sendOPK u i bundle m0 m1 => exact absurd rfl (h1 u i bundle m0 m1)
  | sendNoOPK u i bundle m0 m1 => exact absurd rfl (h2 u i bundle m0 m1)
  | _ =>
    rw [pqxdhAuthWithProvImpl1Key_eq_of_ne_initPrin S P provFn _ (by intro _ h; cases h),
      SignalPqxdh.pqxdhAuthImpl1KeyG_eq_of_ne_initPrin true true S P _ (by intro _ h; cases h)]
    rfl

theorem pqxdhAuthSimImpl_commutes_projAuthSim1Key (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (q : AuthQuery S) (st : AuthState S) :
    CommutesRel (projAuthSim S P) st
      (pqxdhAuthSimImpl1Key S P q)
      (pqxdhAuthWithProvImpl1Key S P (checkBundleProvenanceNoOpk P) q) := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl; dsimp only
    by_cases h : bundle.opkB?.isNone = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendSim_commutes_projAuthSim S P (.sendOPK u i) u bundle m0 m1 st
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl; dsimp only
    by_cases h : bundle.opkB?.isSome = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendSim_commutes_projAuthSim S P (.sendNoOPK u i) u bundle m0 m1 st
  | recvOPK k j o msg =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl pqxdhAuthImpl1KeyG
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    rw [koskSenderOk_map_cache]
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => exact CommutesRel.pure _ st _
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => exact CommutesRel.pure _ st _
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => exact CommutesRel.pure _ st _
        | some op =>
          rcases op with ⟨_, oEntry⟩; dsimp only
          apply CommutesRel.ite; · exact CommutesRel.pure _ st _
          apply CommutesRel.ite; · exact CommutesRel.pure _ st _
          by_cases hct : msg.hdr.kemCt.length = kyberCtLen
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
            simp only [hctb, Bool.false_eq_true, ↓reduceIte]
            cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none => exact CommutesRel.pure _ st _
            | some ss =>
              dsimp only
              apply CommutesRel.liftM_bind; rintro ⟨drKey, roCache'⟩
              apply CommutesRel.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
              cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
              | none => exact CommutesRel.pure _ st _
              | some spqr =>
                rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
                cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                  (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                | none => exact CommutesRel.pure _ st _
                | some pt =>
                  dsimp only
                  cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
                  | none => exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
                  | some sp =>
                    rcases sp with ⟨_, senderEntry⟩; dsimp only
                    cases !senderEntry.corrupted <;>
                      exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
          · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
            rw [hP.kemDecaps_len_reject _ _ hct]
            simp only [hctb, ↓reduceIte]
            exact CommutesRel.pure _ st _
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl pqxdhAuthImpl1KeyG
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    rw [koskSenderOk_map_cache]
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    apply CommutesRel.ite; · exact CommutesRel.pure _ st _
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => exact CommutesRel.pure _ st _
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => exact CommutesRel.pure _ st _
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        apply CommutesRel.ite; · exact CommutesRel.pure _ st _
        by_cases hct : msg.hdr.kemCt.length = kyberCtLen
        · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = false := by simp [hct]
          simp only [hctb, Bool.false_eq_true, ↓reduceIte]
          cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => exact CommutesRel.pure _ st _
          | some ss =>
            dsimp only
            apply CommutesRel.liftM_bind; rintro ⟨drKey, roCache'⟩
            apply CommutesRel.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
            cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
            | none => exact CommutesRel.pure _ st _
            | some spqr =>
              rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
              cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
              | none => exact CommutesRel.pure _ st _
              | some pt =>
                dsimp only
                cases findHonestPrincipal P st.principals msg.hdr.ikAPk with
                | none => exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
                | some sp =>
                  rcases sp with ⟨_, senderEntry⟩; dsimp only
                  cases !senderEntry.corrupted <;>
                    exact CommutesRel.set_bind _ st _ _ rfl (CommutesRel.pure _ _ _)
        · have hctb : (msg.hdr.kemCt.length != kyberCtLen) = true := by simp [hct]
          rw [hP.kemDecaps_len_reject _ _ hct]
          simp only [hctb, ↓reduceIte]
          exact CommutesRel.pure _ st _
  | registerKey sk =>
    unfold pqxdhAuthSimImpl1Key pqxdhAuthWithProvImpl1Key pqxdhAuthWithProvImpl pqxdhAuthImpl1Key pqxdhAuthImpl pqxdhAuthImpl1KeyG registerAdvKey
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    split_ifs
    · exact CommutesRel.pure _ st _
    · exact CommutesRel.set_bind (projAuthSim S P) st _ _ rfl (CommutesRel.pure _ _ _)
  | initPrin u | corruptIK u | genSPK u j | genOPK u j o | roQuery _ | roRootQuery _ _
      | revealDhSecrets =>
    rw [pqxdhAuthWithProvImpl1Key_eq_1KeyG S P _ _ (by intro _ _ _ _ _ h; cases h)
      (by intro _ _ _ _ _ h; cases h)]
    unfold pqxdhAuthSimImpl1Key pqxdhAuthImpl1KeyG
    apply CommutesRel.get_bind
    dsimp only [projAuthSim]
    repeat (first
      | apply CommutesRel.pure
      | (rw [pure_bind, pure_bind])
      | (apply CommutesRel.liftM_bind; intro _)
      | (apply CommutesRel.set_bind; rfl)
      | apply CommutesRel.ite
      | split)

theorem simulateQ_pqxdhAuthSimImplPrim1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (st : AuthState S)
    (hPrin : st.principals.length ≤ S.N_dh)
    (hSpk : st.spkBundles.length ≤ S.N_dh)
    (hOpk : st.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P st.advKeys) :
    simulateQ (primBaseImpl P) ((pqxdhAuthSimImplPrim1Key S q).run st) =
      (pqxdhAuthSimImpl1Key S P q).run st := by
  unfold pqxdhAuthSimImplPrim1Key runAuthRecvOPKSimPrim runAuthRecvNoOPKSimPrim runAuthRecvFinishSimPrim
    runAuthRecvStep2SimPrim pqxdhAuthSimImpl1Key pqxdhAuthImpl1KeyG
  cases q with
  | initPrin u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
        simulateQ_embedUnif]
      congr 1
  | corruptIK u =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) <;> rfl
  | genSPK u j =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
          simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim]
        congr 1
  | genOPK u j o =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        StateT.run_pure, pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure,
        simulateQ_embedUnif]
      congr 1
  | sendOPK u i bundle m0 m1 =>
    dsimp only
    split_ifs
    · rfl
    · exact simulateQ_runAuthSendSimPrim S P (.sendOPK u i) u bundle m0 m1 st hPrin hSpk hOpk hAdv
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only
    split_ifs
    · rfl
    · exact simulateQ_runAuthSendSimPrim S P (.sendNoOPK u i) u bundle m0 m1 st hPrin hSpk hOpk hAdv
  | recvOPK k j o msg =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte]; rfl
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : st.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [h2, ↓reduceIte]; rfl
    simp only [h2, Bool.false_eq_true, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
      simulateQ_bind]
    rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys msg.hdr.ikAPk hPrin hAdv, pure_bind]
    by_cases h3 : (!koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk) = true
    · simp only [h3, ↓reduceIte]; rfl
    simp only [h3, Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rfl
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rfl
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        cases st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => rfl
        | some op =>
          rcases op with ⟨_, oEntry⟩; dsimp only
          by_cases h4 : oEntry.consumed = true
          · simp only [h4, ↓reduceIte]; rfl
          simp only [h4, Bool.false_eq_true, ↓reduceIte]
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
            simulateQ_bind]
          rw [simulateQ_primQ_isCanonical, pure_bind, simulateQ_primQ_isCanonical, pure_bind]
          by_cases h5 : (!(checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId
            msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical
            msg.ephAPk) = true
          · simp only [h5, ↓reduceIte]; rfl
          simp only [h5, Bool.false_eq_true, ↓reduceIte]
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
            simulateQ_bind]
          rw [simulateQ_primQ_kemDecaps, pure_bind]
          cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => rfl
          | some ss =>
            dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
              simulateQ_bind]
            rw [simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_primQ_x25519, pure_bind,
                simulateQ_evalHkdfOrRoPrim]
            congr 1; ext ⟨drKey, roCache'⟩
            rw [simulateQ_primQ_x25519, pure_bind,
                simulateQ_evalRootKdfOrRoPrim]
            congr 1; ext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
            rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                simulateQ_primQ_chainKdfNext, pure_bind,
                simulateQ_primQ_spqrInitRecv, pure_bind]
            cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
            | none => rfl
            | some spqr =>
              rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind,
                bind_assoc,
                simulateQ_bind]
              rw [simulateQ_primQ_deriveMsgKeys, pure_bind,
                  simulateQ_primQ_aeadDec, pure_bind]
              cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
                (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
              | none => rfl
              | some pt =>
                dsimp only
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  pure_bind, bind_assoc, simulateQ_bind]
                rw [simulateQ_findHonestPrincipalPrim S P st.principals msg.hdr.ikAPk hPrin,
                  pure_bind]
                cases findHonestPrincipal P st.principals msg.hdr.ikAPk <;> rfl
  | recvNoOPK k j l msg =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
         msg.hdr.pqspkId == UInt32.ofNat j.val &&
         msg.hdr.opkId? == none &&
         msg.hdr.ikAPk.length == 32 &&
         msg.hdr.ekAPk.length == 32 &&
         msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte]; rfl
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : st.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [h2, ↓reduceIte]; rfl
    simp only [h2, Bool.false_eq_true, ↓reduceIte]
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
      simulateQ_bind]
    rw [simulateQ_koskSenderOkPrim S P st.principals st.advKeys msg.hdr.ikAPk hPrin hAdv, pure_bind]
    by_cases h3 : (!koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk) = true
    · simp only [h3, ↓reduceIte]; rfl
    simp only [h3, Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => rfl
    | some kp =>
      rcases kp with ⟨_, kEntry⟩; dsimp only
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => rfl
      | some bp =>
        rcases bp with ⟨_, bEntry⟩; dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
          simulateQ_bind]
        rw [simulateQ_primQ_isCanonical, pure_bind, simulateQ_primQ_isCanonical, pure_bind]
        by_cases h5 : (!(checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId
          msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical
          msg.ephAPk) = true
        · simp only [h5, ↓reduceIte]; rfl
        simp only [h5, Bool.false_eq_true, ↓reduceIte]
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
          simulateQ_bind]
        rw [simulateQ_primQ_kemDecaps, pure_bind]
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => rfl
        | some ss =>
          dsimp only
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
            simulateQ_bind]
          rw [simulateQ_primQ_x25519, pure_bind,
              simulateQ_primQ_x25519, pure_bind,
              simulateQ_primQ_x25519, pure_bind,
              simulateQ_evalHkdfOrRoPrim]
          congr 1; ext ⟨drKey, roCache'⟩
          rw [simulateQ_primQ_x25519, pure_bind,
              simulateQ_evalRootKdfOrRoPrim]
          congr 1; ext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
          rw [simulateQ_primQ_chainKdfSeed, pure_bind,
              simulateQ_primQ_chainKdfNext, pure_bind,
              simulateQ_primQ_spqrInitRecv, pure_bind]
          cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
          | none => rfl
          | some spqr =>
            rcases spqr with ⟨_, spqrSalt?⟩; dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, pure_bind, bind_assoc,
              simulateQ_bind]
            rw [simulateQ_primQ_deriveMsgKeys, pure_bind,
                simulateQ_primQ_aeadDec, pure_bind]
            cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?)
              (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
            | none => rfl
            | some pt =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                pure_bind, bind_assoc, simulateQ_bind]
              rw [simulateQ_findHonestPrincipalPrim S P st.principals msg.hdr.ikAPk hPrin,
                pure_bind]
              cases findHonestPrincipal P st.principals msg.hdr.ikAPk <;> rfl
  | roQuery secrets =>
    simp only [ Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, pure_bind, bind_assoc, simulateQ_bind, simulateQ_evalHkdfOrRoPrim]
    rfl
  | roRootQuery rk dh =>
    simp only [ Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, pure_bind, bind_assoc, simulateQ_bind, simulateQ_evalRootKdfOrRoPrim]
    rfl
  | revealDhSecrets =>
    rfl
  | registerKey sk =>
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
        pure_bind, bind_assoc, simulateQ_bind]
      rw [simulateQ_primQ_x25519Base, pure_bind, simulateQ_primQ_pow8, pure_bind]
      rfl

end Proofs.SignalPqxdh.Security

end
