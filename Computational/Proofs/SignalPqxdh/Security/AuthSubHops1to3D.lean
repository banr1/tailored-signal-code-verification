/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
import VCVio.EvalDist.Monad.Basic

/-!
# `PrfChainKey` Sub-Hop `PrimBaseSpec` Simulation and Creation-Order Slot Helpers

Proves `PrimBaseSpec` query-budget bounds and `simulateQ` equivalences for the `G3.6 → G3.7`
chain-key hybrid (`authCkStepWith`), together with creation-order `SlotM` well-formedness
invariants (`AuthSlotStateWf`) and slot-indexed send/receive helpers.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

namespace AuthSubHops1to3

theorem primBounded_finishAuthHybridSendPrim (S : Setup)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S) :
    PrimBounded
      (finishAuthHybridSendPrim S sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst)
      (S.N_dh * 8 + 3) := by
  unfold finishAuthHybridSendPrim
  refine primBounded_bind_le (S.N_dh * 4 + 3)
    (primBounded_checkBundleProvenanceExactPrim S hst.base.principals
      hst.base.spkBundles hst.base.opkEntries bundle)
    (fun _ => ?_) (by omega)
  exact primBounded_bind_le 0
    (primBounded_checkBundleSpkHonIdealPrim S hst.base.principals hst.base.spkBundles bundle)
    (fun _ => primBounded_pure') (by omega)

theorem simulateQ_finishAuthHybridSendPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh)
    (hSpk : hst.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.base.opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthHybridSendPrim S sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst) =
      pure (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst) := by
  unfold finishAuthHybridSendPrim finishAuthHybridSend
  rw [simulateQ_bind,
      simulateQ_checkBundleProvenanceExactPrim S P hst.base.principals
        hst.base.spkBundles hst.base.opkEntries bundle hPrin hOpk,
      pure_bind,
      simulateQ_bind,
      simulateQ_checkBundleSpkHonIdealPrim S P hst.base.principals
        hst.base.spkBundles bundle hPrin hSpk,
      pure_bind]
  rfl

theorem primBounded_finishAuthSendCkPrim (S : Setup)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes) :
    PrimBounded
      (finishAuthSendCkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p)
      (S.N_dh * 8 + 5) := by
  unfold finishAuthSendCkPrim
  refine primBounded_bind_le (S.N_dh * 8 + 4) (primBounded_primQ _) (fun _ => ?_) (by omega)
  refine primBounded_bind_le (S.N_dh * 8 + 3) (primBounded_primQ _) (fun _ => ?_) (by omega)
  exact primBounded_bind_le 0
    (primBounded_finishAuthHybridSendPrim S sid uEntry peerPrincipal? _ bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] p.1 p.2
      spqrSalt? pqRatchetMsg _ _ _ msgPlain _ _ hst.toAuthHybridState)
    (fun _ => primBounded_pure') (by omega)

def finishAuthSendCkSlots {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes) :
    AuthResponse × AuthHybridStateFixed S :=
  let (resp, hst0) := finishAuthSendCk P sid uEntry peerPrincipal? bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p
  (resp, { hst0 with slots := hst.slots })

theorem simulateQ_finishAuthSendCkPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthSendCkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p) =
      pure (finishAuthSendCkSlots P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p) := by
  unfold finishAuthSendCkPrim finishAuthSendCkSlots finishAuthSendCk
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
      simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind,
      simulateQ_bind,
      simulateQ_finishAuthHybridSendPrim S P sid uEntry peerPrincipal? _ bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] p.1 p.2
        spqrSalt? pqRatchetMsg _ _ _ msgPlain _ _ hst.toAuthHybridState hPrin hSpk hOpk,
      pure_bind]
  rfl

theorem primBounded_finishAuthRecvCkSlotsPrim (S : Setup)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) (slots' : AuthSlotState) :
    PrimBounded
      (finishAuthRecvCkSlotsPrim S msg prep drKey rk1 spqrSalt? recvCount' p slots')
      (S.N_dh * 12 + 2) := by
  unfold finishAuthRecvCkSlotsPrim
  refine primBounded_bind_le (S.N_dh * 12 + 1) (primBounded_primQ _) (fun _ => ?_) (by omega)
  refine primBounded_bind_le (S.N_dh * 12) (primBounded_primQ _) (fun _ => ?_) (by omega)
  exact primBounded_bind_le 0
    (primBounded_recvFinishTag_runPrim S true prep.finishTag _)
    (fun _ => primBounded_pure') (by omega)

theorem primBounded_finishAuthRecvCkPrim (S : Setup)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) :
    PrimBounded
      (finishAuthRecvCkPrim S msg prep drKey rk1 spqrSalt? recvCount' p)
      (S.N_dh * 12 + 2) :=
  primBounded_finishAuthRecvCkSlotsPrim S msg prep drKey rk1 spqrSalt? recvCount' p {}

theorem simulateQ_finishAuthRecvCkPrim (S : Setup) (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes)
    (hPrin : prep.finishTag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthRecvCkPrim S msg prep drKey rk1 spqrSalt? recvCount' p) =
      pure (finishAuthRecvCk P msg (prep.toPure true P) drKey rk1 spqrSalt? recvCount' p) := by
  unfold finishAuthRecvCkPrim finishAuthRecvCkSlotsPrim finishAuthRecvCk PreparedAuthRecvPrim.toPure
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
      simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind,
      simulateQ_bind,
      simulateQ_recvFinishTag_runPrim S true P prep.finishTag _ hPrin hSentOPK hSentNoOPK,
      pure_bind]
  rfl

@[simp] theorem recvFinishTag_mapState_toPure_fst {S : Setup} (checkAuth : Bool) (P : Primitives)
    (tag : RecvFinishTag S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    ((tag.mapState (cacheAuthAdvKeys P)).toPure checkAuth P res?).1 =
      (tag.toPure checkAuth P res?).1 := by
  rw [recvFinishTag_toPure_cacheAuthAdvKeys]; rfl

@[simp] theorem recvFinishTag_mapState_toPure_snd {S : Setup} (checkAuth : Bool) (P : Primitives)
    (tag : RecvFinishTag S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    ((tag.mapState (cacheAuthAdvKeys P)).toPure checkAuth P res?).2 =
      cacheAuthAdvKeys P (tag.toPure checkAuth P res?).2 := by
  rw [recvFinishTag_toPure_cacheAuthAdvKeys]; rfl

@[simp] theorem cacheAuthAdvKeys_roCache {S : Setup} (P : Primitives) (hst : AuthHybridState S) :
    (cacheAuthAdvKeys P hst).base.roCache = hst.base.roCache := rfl

@[simp] theorem cacheAuthAdvKeys_rootRoCache {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) :
    (cacheAuthAdvKeys P hst).base.rootRoCache = hst.base.rootRoCache := rfl

theorem primBounded_stepAuthOtherPrim (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    PrimBounded (stepAuthOtherPrim S q hst) 4 := by
  unfold stepAuthOtherPrim; dsimp only
  by_cases hWon : hst.base.hasWonAuth = true
  · simp only [hWon, ↓reduceIte]; exact primBounded_pure'
  simp only [hWon, Bool.false_eq_true, ↓reduceIte]
  cases q with
  | initPrin u =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_) (by omega)
      refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_) (by omega)
      refine primBounded_bind_le 3 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_) (by omega)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure') (by omega)
  | corruptIK u =>
    dsimp only
    split <;> exact primBounded_pure'
  | genSPK u j =>
    dsimp only
    split
    · exact primBounded_pure'
    · split
      · exact primBounded_pure'
      · refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0)
          (fun _ => ?_) (by omega)
        refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_) (by omega)
        refine primBounded_bind_le 3 (primBounded_embedUnif sampleRandom64 0)
          (fun _ => ?_) (by omega)
        refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_) (by omega)
        refine primBounded_bind_le 1 primBounded_sampleKemKeyGenPrim (fun _ => ?_) (by omega)
        refine primBounded_bind_le 1 (primBounded_embedUnif sampleRandom64 0)
          (fun _ => ?_) (by omega)
        exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure') (by omega)
  | genOPK u j o =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_) (by omega)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure') (by omega)
  | registerKey sk =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_) (by omega)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure') (by omega)
  | roQuery secrets =>
    dsimp only
    exact primBounded_bind_le 0 (primBounded_embedUnif _ 0) (fun _ => primBounded_pure') (by omega)
  | roRootQuery rk dh =>
    dsimp only
    exact primBounded_bind_le 0 (primBounded_embedUnif _ 0) (fun _ => primBounded_pure') (by omega)
  | revealDhSecrets => exact primBounded_pure'
  | sendOPK _ _ _ _ _ => exact primBounded_pure'
  | sendNoOPK _ _ _ _ _ => exact primBounded_pure'
  | recvOPK _ _ _ _ => exact primBounded_pure'
  | recvNoOPK _ _ _ _ => exact primBounded_pure'

theorem simulateQ_stepAuthOtherPrim (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (hNotSend : ¬isAuthSendQuery (Sum.inr q))
    (hNotRecv : ¬isAuthRecvQuery (Sum.inr q)) :
    simulateQ (primBaseImpl P) (stepAuthOtherPrim S q (cacheAuthAdvKeysFixed P hst)) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$> authCkOtherStep S P q hst := by
  have hIfPos {α : Type} {c : Prop} [Decidable c] (hc : c) (a b : α) :
      (if c then a else b) = a := by split_ifs; rfl
  have hIfNeg {α : Type} {c : Prop} [Decidable c] (hc : ¬c) (a b : α) :
      (if c then a else b) = b := by split_ifs; rfl
  unfold stepAuthOtherPrim authCkOtherStep
  dsimp only
  have hWonEq : (cacheAuthAdvKeysFixed P hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
  by_cases hWon : hst.base.hasWonAuth = true
  · rw [hIfPos (hWonEq.trans hWon), hIfPos hWon]
    simp [Prod.map]
  rw [hIfNeg (hWonEq ▸ hWon), hIfNeg hWon]
  cases q with
  | sendOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | sendNoOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | recvOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | recvNoOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | initPrin u =>
    unfold pqxdhAuthImpl cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, pure_bind, bind_assoc,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
        map_bind, map_pure, Prod.map]
      rfl
  | corruptIK u =>
    unfold pqxdhAuthImpl cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_set, StateT.run_pure, Prod.map]
  | genSPK u j =>
    unfold pqxdhAuthImpl cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim,
          simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]
        rfl
  | genOPK u j o =>
    unfold pqxdhAuthImpl cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, pure_bind, bind_assoc,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
        map_bind, map_pure, Prod.map]
      rfl
  | registerKey sk =>
    unfold pqxdhAuthImpl registerAdvKey cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · rfl
  | roQuery secrets =>
    unfold pqxdhAuthImpl cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]
    rfl
  | roRootQuery rk dh =>
    unfold pqxdhAuthImpl cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      simulateQ_bind, simulateQ_embedUnif, evalRootKdfOrRo_true_eq_pure, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]
    rfl
  | revealDhSecrets =>
    unfold pqxdhAuthImpl cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    rfl

theorem primBounded_sampCkPairPrim (ideal : Bool) :
    PrimBounded (sampCkPairPrim ideal) 2 := by
  unfold sampCkPairPrim
  refine primBounded_bind_le 2 (primBounded_embedUnif sampleBytes32 0) (fun _ => ?_) (by omega)
  cases ideal
  · refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_) (by omega)
    exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure') (by omega)
  · refine primBounded_bind_le 2 (primBounded_embedUnif sampleBytes32 0) (fun _ => ?_) (by omega)
    exact primBounded_bind_le 0 (primBounded_embedUnif sampleBytes32 0)
      (fun _ => primBounded_pure') (by omega)

@[simp] theorem simulateQ_sampCkPairPrim (P : Primitives) (ideal : Bool) :
    simulateQ (primBaseImpl P) (sampCkPairPrim ideal) = sampCkPair P ideal := by
  unfold sampCkPairPrim sampCkPair
  cases ideal <;>
    simp only [simulateQ_bind, simulateQ_embedUnif] <;>
    rfl

theorem primBounded_sampAtCkPrim (idx : Nat) (p : Bytes × Bytes) (s : Nat) :
    PrimBounded (sampAtCkPrim idx p s) 2 := by
  unfold sampAtCkPrim
  split
  · exact primBounded_pure'
  · exact primBounded_sampCkPairPrim (s < idx)

@[simp] theorem simulateQ_sampAtCkPrim (P : Primitives) (idx : Nat) (p : Bytes × Bytes) (s : Nat) :
    simulateQ (primBaseImpl P) (sampAtCkPrim idx p s) =
      (if s == idx then pure p else sampCkPair P (s < idx)) := by
  unfold sampAtCkPrim
  split
  · rfl
  · exact simulateQ_sampCkPairPrim P (s < idx)

theorem checkBundleProvenanceExact_spk_pqspk (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    (checkBundleProvenanceExact P principals spkBundles opkEntries bundle).1 =
      ((findHonestPrincipal P principals bundle.ikB).map (fun p =>
        spkBundles.any (fun ((u, _), b) => u == p.1 && b.spkPk == bundle.spkB))).getD false ∧
    (checkBundleProvenanceExact P principals spkBundles opkEntries bundle).2.2 =
      ((findHonestPrincipal P principals bundle.ikB).map (fun p =>
        spkBundles.any
          (fun ((u, _), b) => u == p.1 && b.pqspkPk == bundle.pqspkB))).getD false := by
  unfold checkBundleProvenanceExact
  rcases findHonestPrincipal P principals bundle.ikB with _ | ⟨k, _⟩ <;> exact ⟨rfl, rfl⟩

private theorem primBounded_ite {α : Type} (c : Bool) (t e : OracleComp PrimBaseSpec α) (n : Nat)
    (ht : PrimBounded t n) (he : PrimBounded e n) : PrimBounded (if c then t else e) n := by
  cases c <;> [exact he; exact ht]

theorem primBounded_authCkSendWithPrim (S : Setup)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (hSamp : ∀ s, PrimBounded (sampAt s) 2)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    PrimBounded (authCkSendWithPrim S sampAt sid u bundle m0 m1 hst) (S.N_dh * 22 + 21) := by
  unfold authCkSendWithPrim
  dsimp only
  split; · exact primBounded_pure'
  split
  · exact primBounded_pure'
  · split
    · exact primBounded_pure'
    · split
      · exact primBounded_pure'
      · refine primBounded_bind_le (S.N_dh * 20 + 21)
          (primBounded_findHonestPrincipalPrim S hst.toAuthHybridState.base.principals bundle.ikB)
          (fun peerPrincipal? => ?_) (by omega)
        refine primBounded_ite _ _ _ _ primBounded_pure' ?_
        · refine primBounded_bind_le (S.N_dh * 14 + 18)
            (primBounded_koskBundleOkPrim S _ _ _ _ bundle)
            (fun koskOk => ?_) (by omega)
          by_cases hKosk : (!koskOk) = true
          · simp only [hKosk, ↓reduceIte]; exact primBounded_pure'
          · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleScalar32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleCoins32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleScalar32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleCoins32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 12 + 18) (primBounded_resolveSigPkPrim S _ _)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 12 + 17) (primBounded_primQ _)
              (fun v1 => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 12 + 16) (primBounded_primQ _)
              (fun v2 => ?_) (by omega)
            by_cases hSig : (!(v1 && v2)) = true
            · simp only [hSig, ↓reduceIte]; exact primBounded_pure'
            · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
              refine primBounded_bind_le (S.N_dh * 12 + 15) (primBounded_primQ _)
                (fun kem? => ?_) (by omega)
              cases kem? with
              | none => exact primBounded_pure'
              | some pair =>
                rcases pair with ⟨ss, kemCt⟩
                dsimp only
                refine primBounded_bind_le (S.N_dh * 12 + 14) (primBounded_primQ _)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le (S.N_dh * 12 + 13) (primBounded_primQ _)
                  (fun _ => ?_) (by omega)
                refine primBounded_bind_le (S.N_dh * 8 + 13)
                  (primBounded_checkBundleSpkHonIdealPrim S _ _ bundle) (fun _ => ?_) (by omega)
                refine primBounded_ite _ _ _ _ ?_ ?_
                · refine primBounded_bind_le (S.N_dh * 8 + 13)
                    (primBounded_embedUnif sampleDRKey96 0)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 13)
                    (primBounded_embedUnif sampleBytes32 0)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 12) (primBounded_primQ _)
                    (fun spqr? => ?_) (by omega)
                  cases spqr? with
                  | none => exact primBounded_pure'
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                    dsimp only
                    refine primBounded_bind_le (S.N_dh * 8 + 10) (hSamp _) (fun p => ?_) (by omega)
                    exact (primBounded_finishAuthSendCkPrim S sid _ _ bundle m0 m1
                      _ _ ss kemCt _ _ _ _ spqrSalt? pqRatchetMsg _ _ p).mono (by omega)
                · refine primBounded_bind_le (S.N_dh * 8 + 12) (primBounded_primQ _)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 11) (primBounded_primQ _)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 10) (primBounded_primQ _)
                    (fun _ => ?_) (by omega)
                  have hDh4 : ∀ ekASk, PrimBounded
                      (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                        let d4 ← primQ (.x25519 ekASk opkPk)
                        pure (some d4))) 1 := by
                    intro ekASk
                    cases bundle.opkB? with
                    | none => exact primBounded_pure'
                    | some p =>
                      exact primBounded_bind_le 0 (primBounded_primQ _)
                        (fun _ => primBounded_pure') (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 9) (hDh4 _) (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 9) (primBounded_embedUnif _ 0)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 8) (primBounded_primQ _)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 8) (primBounded_embedUnif _ 0)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 7) (primBounded_primQ _)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 6) (primBounded_primQ _)
                    (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 5) (primBounded_primQ _)
                    (fun spqr? => ?_) (by omega)
                  cases spqr? with
                  | none => exact primBounded_pure'
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                    dsimp only
                    refine primBounded_bind_le (S.N_dh * 8 + 4) (primBounded_primQ _)
                      (fun _ => ?_) (by omega)
                    refine primBounded_bind_le (S.N_dh * 8 + 3) (primBounded_primQ _)
                      (fun _ => ?_) (by omega)
                    exact primBounded_bind_le 0
                      (primBounded_finishAuthHybridSendPrim S sid _ _ _ bundle m0 m1
                        _ _ ss kemCt _ _ _ _ _ _ _ spqrSalt? pqRatchetMsg
                        _ _ _ _ _ _ hst.toAuthHybridState)
                      (fun _ => primBounded_pure') (by omega)

def authCkSendWithSlots (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    pure (.noneResp, hst)
  else if m0.length != m1.length then
    pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then
    pure (.noneResp, hst)
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← sampleScalar32
          let kemCoins ← sampleCoins32
          let ephASk ← sampleScalar32
          let spqrCoins ← sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let prov :=
                checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool :=
                isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let drKey ← sampleDRKey96
                let rk1 ← sampleBytes32
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let (sIdx, slots') := hst.slots.allocSend sid
                  let p ← sampAt sIdx
                  pure (finishAuthSendCkSlots P sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
                    pqRatchetMsg msgPlain { hst with slots := slots' } p)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets
                let dhRatchet := P.x25519 ephASk bundle.spkB
                let ((rk1, ck1_0), rootRoCache') ←
                  evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') :=
                    finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount,
                                slots := hst.slots })

theorem simulateQ_authCkSendWithPrim (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.toAuthHybridState.base.advKeys) :
    simulateQ (primBaseImpl P) (authCkSendWithPrim S sampAt sid u bundle m0 m1 hst) =
      authCkSendWithSlots S P sampAtPure sid u bundle m0 m1 hst := by
  unfold authCkSendWithPrim authCkSendWithSlots
  dsimp only
  by_cases hWon : hst.base.hasWonAuth = true
  · simp only [hWon, ↓reduceIte]; rfl
  simp only [Bool.not_eq_true] at hWon
  simp only [hWon, Bool.false_eq_true, ↓reduceIte]
  by_cases hLen : (m0.length != m1.length) = true
  · simp only [hLen, ↓reduceIte]; rfl
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (hst.toAuthHybridState.base.usedSendSessions.contains sid) = true
    · simp only [hUsed, ↓reduceIte]; rfl
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩
        dsimp only
        rw [simulateQ_bind,
            simulateQ_findHonestPrincipalPrim S P
              hst.toAuthHybridState.base.principals bundle.ikB hPrin,
            pure_bind]
        have hProv2 := (checkBundleProvenanceExact_spk_pqspk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle).2
        cases hpeer : findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB with
        | none =>
          dsimp only
          by_cases hCh : (m0 != m1) = true
          · simp only [Bool.not_false, Bool.true_and, hCh, ↓reduceIte]; rfl
          · simp only [Bool.not_false, Bool.true_and, hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind,
                simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv, pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp only [hKosk, ↓reduceIte]; rfl
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify
                  (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [hSig, ↓reduceIte]; rfl
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => rfl
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P
                        hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind]
                  simp only [Option.isSome, Bool.false_and, Bool.or_false,
                    Bool.false_eq_true, ↓reduceIte]
                  rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                  have hDh4 : simulateQ (primBaseImpl P)
                      (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                        let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                      pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                    cases bundle.opkB? with
                    | none => rfl
                    | some opkPair =>
                      rcases opkPair with ⟨_, opkPk⟩
                      simp only [simulateQ_bind, simulateQ_pure]; rfl
                  rw [simulateQ_bind, hDh4, pure_bind]
                  simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure]
                  congr 1; funext ⟨drKey, roCache'⟩
                  rw [simulateQ_primQ_x25519, pure_bind]; simp only [evalRootKdfOrRo_true_eq_pure]
                  congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                  rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                      simulateQ_primQ_chainKdfNext, pure_bind,
                      simulateQ_primQ_spqrInitSend, pure_bind]
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => rfl
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                        simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                        simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1
                          ekASk _ ss kemCt
                          ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg
                          _ _ _ _ roCache' rootRoCache'
                          hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                    rfl
        | some pPair =>
          rcases pPair with ⟨pIdx, pEntry⟩; dsimp only
          rw [hpeer] at hProv2
          by_cases hCh : (!!pEntry.corrupted && (m0 != m1)) = true
          · simp only [hCh, ↓reduceIte]; rfl
          · simp only [hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind,
                simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv, pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp only [hKosk, ↓reduceIte]; rfl
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify
                  (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [hSig, ↓reduceIte]; rfl
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => rfl
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P
                        hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind, ← hProv2]
                  split
                  · simp only [simulateQ_bind, simulateQ_embedUnif]
                    congr 1; funext drKey; congr 1; funext rk1
                    rw [simulateQ_primQ_spqrInitSend, pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => rfl
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      rw [simulateQ_bind, hSamp]
                      congr 1; funext p
                      exact simulateQ_finishAuthSendCkPrim S P sid uEntry
                        (some (pIdx, pEntry)) bundle m0 m1 ekASk _ ss kemCt ephASk _
                        drKey rk1 spqrSalt? pqRatchetMsg _ { hst with slots := _ } p
                        hPrin hSpk hOpk
                  · rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                    have hDh4 : simulateQ (primBaseImpl P)
                        (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                          let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                        pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                      cases bundle.opkB? with
                      | none => rfl
                      | some opkPair =>
                        rcases opkPair with ⟨_, opkPk⟩
                        simp only [simulateQ_bind, simulateQ_pure]; rfl
                    rw [simulateQ_bind, hDh4, pure_bind]
                    simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure]
                    congr 1; funext ⟨drKey, roCache'⟩
                    rw [simulateQ_primQ_x25519, pure_bind]; simp only [evalRootKdfOrRo_true_eq_pure]
                    congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                        simulateQ_primQ_chainKdfNext, pure_bind,
                        simulateQ_primQ_spqrInitSend, pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => rfl
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                          simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                          simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1
                            ekASk _ ss kemCt
                            ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg
                            _ _ _ _ roCache' rootRoCache'
                            hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                      rfl

theorem simulateQ_authCkSendWithSlotsPrim (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.toAuthHybridState.base.advKeys) :
    simulateQ (primBaseImpl P) (authCkSendWithPrim S sampAt sid u bundle m0 m1 hst) =
      authCkSendWithSlots S P sampAtPure sid u bundle m0 m1 hst :=
  simulateQ_authCkSendWithPrim S P sampAt sampAtPure hSamp sid u bundle m0 m1 hst
    hPrin hSpk hOpk hAdv

theorem authCkSendWithSlots_cacheAuthAdvKeysFixed (S : Setup) (P : Primitives)
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    authCkSendWithSlots S P sampAtPure sid u bundle m0 m1 (cacheAuthAdvKeysFixed P hst) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$>
        authCkSendWithSlots S P sampAtPure sid u bundle m0 m1 hst := by
  unfold authCkSendWithSlots
  dsimp only
  have hWonEq : (cacheAuthAdvKeysFixed P hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
  rw [hWonEq]
  by_cases hWon : hst.base.hasWonAuth = true
  · simp [hWon, Prod.map]
  simp only [hWon, Bool.false_eq_true, ↓reduceIte]
  unfold cacheAuthAdvKeysFixed cacheAuthAdvKeys
  dsimp only
  rw [koskBundleOk_cacheAuthAdvKeys]
  split; · simp [Prod.map]
  split; · simp [Prod.map]
  split
  · simp [Prod.map]
  · split
    · simp [Prod.map]
    · split
      · simp [Prod.map]
      · simp only [map_bind]
        congr 1; funext ekASk; congr 1; funext kemCoins
        congr 1; funext ephASk; congr 1; funext spqrCoins
        split
        · simp [Prod.map]
        · cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp [Prod.map]
          | some pair =>
            rcases pair with ⟨ss, kemCt⟩
            dsimp only
            split
            · simp only [map_bind]
              congr 1; funext drKey
              congr 1; funext rk1
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [Prod.map]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                dsimp only
                simp only [map_bind, map_pure]
                congr 1
            · simp only [map_bind]
              congr 1; funext ⟨drKey, roCache'⟩
              congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [Prod.map]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                dsimp only
                simp [Prod.map, finishAuthHybridSend]

theorem authCkSendWith_cacheAuthAdvKeysFixed (S : Setup) (P : Primitives)
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    authCkSendWith S P sampAtPure sid u bundle m0 m1 (cacheAuthAdvKeysFixed P hst) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$>
        authCkSendWith S P sampAtPure sid u bundle m0 m1 hst := by
  unfold authCkSendWith
  dsimp only
  have hWonEq : (cacheAuthAdvKeysFixed P hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
  rw [hWonEq]
  by_cases hWon : hst.base.hasWonAuth = true
  · simp [hWon, Prod.map]
  simp only [hWon, Bool.false_eq_true, ↓reduceIte]
  unfold cacheAuthAdvKeysFixed cacheAuthAdvKeys
  dsimp only
  rw [koskBundleOk_cacheAuthAdvKeys]
  split; · simp [Prod.map]
  split; · simp [Prod.map]
  split
  · simp [Prod.map]
  · split
    · simp [Prod.map]
    · split
      · simp [Prod.map]
      · simp only [map_bind]
        congr 1; funext ekASk; congr 1; funext kemCoins
        congr 1; funext ephASk; congr 1; funext spqrCoins
        split
        · simp [Prod.map]
        · cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp [Prod.map]
          | some pair =>
            rcases pair with ⟨ss, kemCt⟩
            dsimp only
            split
            · simp only [map_bind]
              congr 1; funext drKey
              congr 1; funext rk1
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [Prod.map]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                dsimp only
                simp only [map_bind, map_pure]
                congr 1
            · simp only [map_bind]
              congr 1; funext ⟨drKey, roCache'⟩
              congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [Prod.map]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                dsimp only
                simp [Prod.map, finishAuthHybridSend]

theorem prepareAuthHybridRecvOPKPure_finishTag_base {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (prep : PreparedAuthRecvPrim S)
    (h : prepareAuthHybridRecvOPKPure P k j o msg hst = some prep) :
    prep.finishTag.hstDec = prep.hstDec ∧ prep.hstDec.base = hst.base := by
  unfold prepareAuthHybridRecvOPKPure at h
  dsimp only at h
  split at h; · contradiction
  split at h; · contradiction
  split at h; · contradiction
  split at h; · contradiction
  rcases h1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
  rcases h2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    with _ | ⟨_, bEntry⟩ <;>
  rcases h3 : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    with _ | ⟨_, oEntry⟩ <;>
  simp only [h1, h2, h3] at h
  all_goals try contradiction
  split at h; · contradiction
  split at h; · contradiction
  cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt <;> rw [hDec] at h
  · contradiction
  · injection h with hEq; subst hEq; exact ⟨rfl, rfl⟩

theorem prepareAuthHybridRecvNoOPKPure_finishTag_base {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (prep : PreparedAuthRecvPrim S)
    (h : prepareAuthHybridRecvNoOPKPure P k j l msg hst = some prep) :
    prep.finishTag.hstDec = prep.hstDec ∧ prep.hstDec.base = hst.base := by
  unfold prepareAuthHybridRecvNoOPKPure at h
  dsimp only at h
  split at h; · contradiction
  split at h; · contradiction
  split at h; · contradiction
  split at h; · contradiction
  rcases h1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with _ | ⟨_, kEntry⟩ <;>
  rcases h2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    with _ | ⟨_, bEntry⟩ <;>
  simp only [h1, h2] at h
  all_goals try contradiction
  split at h; · contradiction
  cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt <;> rw [hDec] at h
  · contradiction
  · injection h with hEq; subst hEq; exact ⟨rfl, rfl⟩

theorem primBounded_authCkRecvWithPrim (S : Setup)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (hSamp : ∀ s, PrimBounded (sampAt s) 2)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) :
    PrimBounded (authCkRecvWithPrim S sampAt msg prep? hst) (S.N_dh * 12 + 5) := by
  unfold authCkRecvWithPrim
  cases prep? with
  | none => exact primBounded_pure'
  | some prep =>
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _)
            (fun pqr? => ?_) (by omega)
          cases pqr? with
          | none =>
            exact primBounded_bind_le 0
              (primBounded_recvFinishTag_runPrim S true prep.finishTag none)
              (fun _ => primBounded_pure') (by omega)
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact (primBounded_finishAuthRecvCkSlotsPrim S msg prep s.drKey s.rk1
              spqrSalt? _ _ _).mono (by omega)
        · refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_embedUnif sampleBytes32 0)
            (fun _ => ?_) (by omega)
          refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _)
            (fun pqr? => ?_) (by omega)
          cases pqr? with
          | none =>
            exact primBounded_bind_le 0
              (primBounded_recvFinishTag_runPrim S true prep.finishTag none)
              (fun _ => primBounded_pure') (by omega)
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            refine primBounded_bind_le (S.N_dh * 12 + 2) (hSamp _) (fun p => ?_) (by omega)
            exact primBounded_finishAuthRecvCkSlotsPrim S msg prep s.drKey _ spqrSalt? _ p _
      | none =>
        dsimp only
        refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_embedUnif sampleDRKey96 0)
          (fun _ => ?_) (by omega)
        refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_embedUnif sampleBytes32 0)
          (fun _ => ?_) (by omega)
        refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _)
          (fun pqr? => ?_) (by omega)
        cases pqr? with
        | none =>
          exact primBounded_bind_le 0 (primBounded_recvFinishTag_runPrim S true prep.finishTag none)
            (fun _ => primBounded_pure') (by omega)
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only
          refine primBounded_bind_le (S.N_dh * 12 + 2) (hSamp _) (fun p => ?_) (by omega)
          exact primBounded_finishAuthRecvCkSlotsPrim S msg prep _ _ spqrSalt? _ p _
    · refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_embedUnif _ 0)
        (fun _ => ?_) (by omega)
      refine primBounded_bind_le (S.N_dh * 12 + 5) (primBounded_embedUnif _ 0)
        (fun _ => ?_) (by omega)
      refine primBounded_bind_le (S.N_dh * 12 + 4) (primBounded_primQ _) (fun _ => ?_) (by omega)
      refine primBounded_bind_le (S.N_dh * 12 + 3) (primBounded_primQ _) (fun _ => ?_) (by omega)
      refine primBounded_bind_le (S.N_dh * 12 + 2) (primBounded_primQ _) (fun pqr? => ?_) (by omega)
      cases pqr? with
      | none =>
        exact primBounded_bind_le 0 (primBounded_recvFinishTag_runPrim S true prep.finishTag none)
          (fun _ => primBounded_pure') (by omega)
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        dsimp only
        refine primBounded_bind_le (S.N_dh * 12 + 1) (primBounded_primQ _) (fun _ => ?_) (by omega)
        refine primBounded_bind_le (S.N_dh * 12) (primBounded_primQ _) (fun _ => ?_) (by omega)
        exact primBounded_bind_le 0 (primBounded_recvFinishTag_runPrim S true prep.finishTag _)
          (fun _ => primBounded_pure') (by omega)

def finishAuthRecvCkSlots {S : Setup} (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) (slots' : AuthSlotState) :
    AuthResponse × AuthHybridStateFixed S :=
  let (resp, hst0) := finishAuthRecvCk P msg prep drKey rk1 spqrSalt? recvCount' p
  (resp, { hst0 with slots := slots' })

theorem simulateQ_finishAuthRecvCkSlotsPrim (S : Setup) (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (p : Bytes × Bytes) (slots' : AuthSlotState)
    (hPrin : prep.finishTag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthRecvCkSlotsPrim S msg prep drKey rk1 spqrSalt? recvCount' p slots') =
      pure (finishAuthRecvCkSlots P msg (prep.toPure true P) drKey rk1 spqrSalt? recvCount' p slots') := by
  unfold finishAuthRecvCkSlotsPrim finishAuthRecvCkSlots finishAuthRecvCk PreparedAuthRecvPrim.toPure
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
      simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind,
      simulateQ_bind,
      simulateQ_recvFinishTag_runPrim S true P prep.finishTag _ hPrin hSentOPK hSentNoOPK,
      pure_bind]
  rfl

def authCkRecvWithSlots (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            pure (finishAuthRecvCkSlots P msg prep s.drKey s.rk1 spqrSalt? recvCount'
              (s.mkSeed, s.ck1_1) hst.slots)
        else
          let rk1 ← sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            let p ← sampAt rSlot
            pure (finishAuthRecvCkSlots P msg prep s.drKey rk1 spqrSalt? recvCount' p slots')
      | none =>
        let drKey ← sampleDRKey96
        let rk1 ← sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          let p ← sampAt rSlot
          pure (finishAuthRecvCkSlots P msg prep drKey rk1 spqrSalt? recvCount' p slots')
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ←
        evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })

theorem simulateQ_authCkRecvWithPrim (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S)
    (hPrep : ∀ prep, prep? = some prep →
      prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
      prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
      prep.finishTag.hstDec.base.principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (authCkRecvWithPrim S sampAt msg prep? hst) =
      authCkRecvWithSlots S P sampAtPure msg (prep?.map (PreparedAuthRecvPrim.toPure true P)) hst := by
  unfold authCkRecvWithPrim authCkRecvWithSlots
  cases prep? with
  | none => rfl
  | some prep =>
    obtain ⟨hSentOPK, hSentNoOPK, hPrin⟩ := hPrep prep rfl
    dsimp only [Option.map, PreparedAuthRecvPrim.toPure]
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · rw [simulateQ_bind, simulateQ_primQ_spqrInitRecv, pure_bind]
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            rw [simulateQ_bind,
                simulateQ_recvFinishTag_runPrim S true P prep.finishTag none
                  hPrin hSentOPK hSentNoOPK, pure_bind]
            rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact simulateQ_finishAuthRecvCkSlotsPrim S P msg prep s.drKey s.rk1
              spqrSalt? _ _ _ hPrin hSentOPK hSentNoOPK
        · simp only [simulateQ_bind, simulateQ_embedUnif]
          congr 1; funext rk1
          rw [simulateQ_primQ_spqrInitRecv, pure_bind]
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            dsimp only
            rw [simulateQ_bind,
                simulateQ_recvFinishTag_runPrim S true P prep.finishTag none
                  hPrin hSentOPK hSentNoOPK, pure_bind]
            rfl
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            rw [simulateQ_bind, hSamp]
            congr 1; funext p
            exact simulateQ_finishAuthRecvCkSlotsPrim S P msg prep s.drKey rk1
              spqrSalt? _ p _ hPrin hSentOPK hSentNoOPK
      | none =>
        dsimp only
        simp only [simulateQ_bind, simulateQ_embedUnif]
        congr 1; funext drKey; congr 1; funext rk1
        rw [simulateQ_primQ_spqrInitRecv, pure_bind]
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          dsimp only
          rw [simulateQ_bind,
              simulateQ_recvFinishTag_runPrim S true P prep.finishTag none
                hPrin hSentOPK hSentNoOPK, pure_bind]
          rfl
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only
          rw [simulateQ_bind, hSamp]
          congr 1; funext p
          exact simulateQ_finishAuthRecvCkSlotsPrim S P msg prep drKey rk1
            spqrSalt? _ p _ hPrin hSentOPK hSentNoOPK
    · simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure,
        evalRootKdfOrRo_true_eq_pure]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      rw [simulateQ_primQ_chainKdfSeed, pure_bind,
          simulateQ_primQ_chainKdfNext, pure_bind,
          simulateQ_primQ_spqrInitRecv, pure_bind]
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        dsimp only
        rw [simulateQ_bind,
            simulateQ_recvFinishTag_runPrim S true P prep.finishTag none hPrin hSentOPK hSentNoOPK,
            pure_bind]
        rfl
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        dsimp only
        rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
            simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind,
            simulateQ_bind,
            simulateQ_recvFinishTag_runPrim S true P prep.finishTag _ hPrin hSentOPK hSentNoOPK,
            pure_bind]
        rfl

theorem authCkRecvWith_cacheAuthAdvKeysFixed (S : Setup) (P : Primitives)
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) :
    authCkRecvWith S P sampAtPure msg
      ((prep?.map (PreparedAuthRecvPrim.mapState (cacheAuthAdvKeys P))).map
        (PreparedAuthRecvPrim.toPure true P))
      (cacheAuthAdvKeysFixed P hst) =
    Prod.map id (cacheAuthAdvKeysFixed P) <$>
      authCkRecvWith S P sampAtPure msg
        (prep?.map (PreparedAuthRecvPrim.toPure true P)) hst := by
  unfold authCkRecvWith cacheAuthAdvKeysFixed
  cases prep? with
  | none => simp [Prod.map]
  | some prep =>
    dsimp only [Option.map, PreparedAuthRecvPrim.mapState, PreparedAuthRecvPrim.toPure]
    simp only [cacheAuthAdvKeys_roCache, cacheAuthAdvKeys_rootRoCache]
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            simp [Prod.map, finishAuthRecvCk]
        · simp only [map_bind]
          congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            simp only [map_bind, map_pure]
            congr 1; funext p
            simp [Prod.map, finishAuthRecvCk]
      | none =>
        dsimp only
        simp only [map_bind]
        congr 1; funext drKey
        congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [Prod.map]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only
          simp only [map_bind, map_pure]
          congr 1; funext p
          simp [Prod.map, finishAuthRecvCk]
    · simp only [map_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => simp [Prod.map]
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        dsimp only
        simp [Prod.map]

theorem primBounded_authCkStepWithPrim (S : Setup)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (hSamp : ∀ s, PrimBounded (sampAt s) 2)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    PrimBounded (authCkStepWithPrim S sampAt q hst) (S.N_dh * 26 + 21) := by
  unfold authCkStepWithPrim
  cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only
    split
    · exact primBounded_pure'
    · exact (primBounded_authCkSendWithPrim S sampAt hSamp
        (.sendOPK u i) u bundle m0 m1 hst).mono (by omega)
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only
    split
    · exact primBounded_pure'
    · exact (primBounded_authCkSendWithPrim S sampAt hSamp
        (.sendNoOPK u i) u bundle m0 m1 hst).mono (by omega)
  | recvOPK k j o msg =>
    dsimp only
    exact primBounded_bind_le (S.N_dh * 12 + 5)
      (primBounded_prepareAuthHybridRecvOPKPrim S k j o msg hst.toAuthHybridState)
      (fun prep? => primBounded_authCkRecvWithPrim S sampAt hSamp msg prep? hst)
      (by omega)
  | recvNoOPK k j l msg =>
    dsimp only
    exact primBounded_bind_le (S.N_dh * 12 + 5)
      (primBounded_prepareAuthHybridRecvNoOPKPrim S k j l msg hst.toAuthHybridState)
      (fun prep? => primBounded_authCkRecvWithPrim S sampAt hSamp msg prep? hst)
      (by omega)
  | _ =>
    exact (primBounded_stepAuthOtherPrim S _ hst).mono (by omega)

@[simp] theorem validAuthHybrid_cacheAuthAdvKeysFixed {S : Setup} (P : Primitives)
    (hst : AuthHybridStateFixed S) :
    ValidAuthHybrid S P (cacheAuthAdvKeysFixed P hst) ↔ ValidAuthHybrid S P hst := by
  constructor <;> (rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩)

namespace SlotM

theorem wf_run_none_of_run'_eq {κ α St : Type} {Wf : St → Prop}
    (m : SlotM κ (α × St)) (lazyRun : ProbComp (α × St))
    (hEq : m.run' none = lazyRun)
    (hWf : ∀ x ∈ support lazyRun, Wf x.2) :
    ∀ y ∈ support (m.run none), Wf y.1.2 := by
  intro y hy
  apply hWf y.1
  rw [← hEq, StateT.run'_eq, support_map]
  exact ⟨y, hy, rfl⟩

theorem evalDist_preSample_eq_lazy_of_slotStep_inv
    {ι κ α : Type} {QSpec : OracleSpec.{0, 0} ι} {St : Type}
    (samp : ProbComp κ) (Wf : St → Prop) (hasFired : St → Bool)
    (implLazy : QueryImpl QSpec (StateT St ProbComp))
    (implPre : κ → QueryImpl QSpec (StateT St ProbComp))
    (stepSlot : (q : ι) → St → SlotM κ (QSpec.Range q × St))
    (hSlotComp : ∀ q st, SlotComp samp (stepSlot q st))
    (hSome : ∀ k q st, (stepSlot q st).run' (some k) = (implPre k q).run st)
    (hNone : ∀ q st (g : QSpec.Range q × St → ProbComp Bool),
      Wf st → 𝒟[(stepSlot q st).run' none >>= g] = 𝒟[(implLazy q).run st >>= g])
    (hAfter : ∀ k q st, Wf st → hasFired st = true →
      (implPre k q).run st = (implLazy q).run st ∧
      ∀ x ∈ support ((implLazy q).run st), hasFired x.2 = true)
    (hFire : ∀ q st y, Wf st → y ∈ support ((stepSlot q st).run none) →
      y.2.isSome = true → hasFired y.1.2 = true)
    (hWfLazy : ∀ q st, Wf st → ∀ x ∈ support ((implLazy q).run st), Wf x.2)
    (hWfSlotNone : ∀ q st, Wf st → ∀ y ∈ support ((stepSlot q st).run none), Wf y.1.2)
    (oa : OracleComp (unifSpec + QSpec) α) (st0 : St) (hWf0 : Wf st0)
    (obs : α × St → ProbComp Bool) :
    let fullPre := fun k =>
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implPre k
    let fullLazy :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implLazy
    𝒟[samp >>= fun k => (simulateQ (fullPre k) oa).run st0 >>= obs] =
      𝒟[(simulateQ fullLazy oa).run st0 >>= obs] := by
  intro fullPre fullLazy
  let implSlot : QueryImpl QSpec (StateT St (SlotM κ)) := fun q => StateT.mk (stepSlot q)
  let fullSlot : QueryImpl (unifSpec + QSpec) (StateT St (SlotM κ)) :=
    (QueryImpl.ofLift unifSpec (SlotM κ)).liftTarget (StateT St (SlotM κ)) + implSlot
  have hInl : ∀ (uq : unifSpec.Domain)
      (mx : (unifSpec + QSpec).Range (Sum.inl uq) → OracleComp (unifSpec + QSpec) α) (st : St),
      (simulateQ fullSlot (liftM (OracleSpec.query (Sum.inl uq)) >>= mx)).run st =
        ((liftM (liftM (OracleSpec.query (spec := unifSpec) uq) : ProbComp _) : SlotM κ _) >>=
          fun u => (simulateQ fullSlot (mx u)).run st) := fun _ _ _ => rfl
  have hInr : ∀ (gq : QSpec.Domain)
      (mx : (unifSpec + QSpec).Range (Sum.inr gq) → OracleComp (unifSpec + QSpec) α) (st : St),
      (simulateQ fullSlot (liftM (OracleSpec.query (Sum.inr gq)) >>= mx)).run st =
        (stepSlot gq st >>= fun x => (simulateQ fullSlot (mx x.1)).run x.2) := fun _ _ _ => rfl
  have hSimSlotComp : ∀ (oa' : OracleComp (unifSpec + QSpec) α) (st : St),
      SlotComp samp ((simulateQ fullSlot oa').run st) := by
    intro oa'
    induction oa' using OracleComp.inductionOn with
    | pure a =>
      intro st; simp only [simulateQ_pure, StateT.run_pure]; exact SlotComp.pure samp (a, st)
    | query_bind q mx ih =>
      intro st; rcases q with uq | gq
      · exact SlotComp.of_eq (hInl uq mx st) ((SlotComp.liftComp samp _).bind fun u => ih u st)
      · exact SlotComp.of_eq (hInr gq mx st) ((hSlotComp gq st).bind fun x => ih x.1 x.2)
  have hSimSome : ∀ (k : κ) (oa' : OracleComp (unifSpec + QSpec) α) (st : St),
      ((simulateQ fullSlot oa').run st).run' (some k) = (simulateQ (fullPre k) oa').run st := by
    intro k oa'
    induction oa' using OracleComp.inductionOn with
    | pure a => intro st; simp [simulateQ_pure, StateT.run_pure]
    | query_bind q mx ih =>
      intro st; rcases q with uq | gq
      · rw [hInl uq mx st, run'_liftComp_bind, simulateQ_run_query_inl_local]
        congr 1; ext u; exact ih u st
      · rw [hInr gq mx st, run'_bind_of_slotComp_some (hSlotComp gq st) k, hSome k gq st,
          simulateQ_run_query_inr_local]
        congr 1; ext ⟨r, st'⟩; exact ih r st'
  have hSimNone : ∀ (oa' : OracleComp (unifSpec + QSpec) α) (st : St) (o : Option κ),
      Wf st → (o.isSome = true → hasFired st = true) →
      𝒟[((simulateQ fullSlot oa').run st).run' o >>= obs] =
        𝒟[(simulateQ fullLazy oa').run st >>= obs] := by
    intro oa'
    induction oa' using OracleComp.inductionOn with
    | pure a => intro st o _ _; simp [simulateQ_pure, StateT.run_pure]
    | query_bind q mx ih =>
      intro st o hWf hInv; rcases q with uq | gq
      · rw [hInl uq mx st, run'_liftComp_bind, simulateQ_run_query_inl_local, bind_assoc, bind_assoc]
        exact OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ih u st o hWf hInv)
      · rw [hInr gq mx st, simulateQ_run_query_inr_local, bind_assoc]
        rcases o with _ | k
        · rw [← hNone gq st (fun x => (simulateQ fullLazy (mx x.1)).run x.2 >>= obs) hWf]
          simp only [StateT.run'_eq, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc,
            Function.comp_apply, pure_bind]
          refine OracleComp.evalDist_bind_congr_of_support ((stepSlot gq st).run none) _ _
            fun ⟨⟨r, st'⟩, o'⟩ hy => ?_
          have hWf' : Wf st' := hWfSlotNone gq st hWf _ hy
          have hInv' : o'.isSome = true → hasFired st' = true := hFire gq st _ hWf hy
          simpa only [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
            pure_bind] using ih r st' o' hWf' hInv'
        · have hFired : hasFired st = true := hInv rfl
          rw [run'_bind_of_slotComp_some (hSlotComp gq st) k, hSome k gq st,
            (hAfter k gq st hWf hFired).1, bind_assoc]
          refine OracleComp.evalDist_bind_congr_of_support ((implLazy gq).run st) _ _
            fun ⟨r, st'⟩ hx => ?_
          exact ih r st' (some k) (hWfLazy gq st hWf (r, st') hx)
            (fun _ => (hAfter k gq st hWf hFired).2 (r, st') hx)
  have hEagerLazy := SlotComp.eager_eq_lazy_run' (hSimSlotComp oa st0) obs
  simp_rw [hSimSome _ oa st0] at hEagerLazy
  rw [hEagerLazy, hSimNone oa st0 none hWf0 (fun h => by cases h)]

end SlotM

def authCreationSlotFired (idx : Nat) {S : Setup} (hst : AuthHybridStateFixed S) : Bool :=
  decide (idx < hst.slots.nextSlot)

structure AuthSlotStateWf (S : Setup) (hst : AuthHybridStateFixed S) : Prop where
  send_lt    : ∀ (sid : SessionId S) k, hst.slots.lookupSend sid = some k → k < hst.slots.nextSlot
  recv_lt    : ∀ rc k, hst.slots.recvTbl rc = some k → k < hst.slots.nextSlot
  send_fresh : ∀ sid : SessionId S,
    hst.toAuthHybridState.base.usedSendSessions.contains sid = false →
    hst.slots.lookupSend sid = none
  recv_fresh : ∀ rc, hst.recvCount ≤ rc → hst.slots.recvTbl rc = none
  ideal_send : ∀ s ∈ hst.toAuthHybridState.idealSessions,
    hst.toAuthHybridState.base.usedSendSessions.contains s.sid = true ∧
    ∃ k < hst.slots.nextSlot, hst.slots.lookupSend s.sid = some k
  slot_inj   : ∀ (sid1 sid2 : SessionId S) k,
    hst.slots.lookupSend sid1 = some k → hst.slots.lookupSend sid2 = some k → sid1 = sid2

theorem authSlotStateWf_empty (S : Setup) (secb : Bool) :
    AuthSlotStateWf S (AuthHybridStateFixed.empty S secb) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro sid _ h; cases sid <;> simp [AuthHybridStateFixed.empty, AuthSlotState.lookupSend] at h
  · intro _ _ h; simp [AuthHybridStateFixed.empty] at h
  · intro sid _; cases sid <;> rfl
  · intro _ _; rfl
  · intro _ hs; simp [AuthHybridStateFixed.empty, AuthHybridState.empty] at hs
  · intro sid1 _ _ h1 _; cases sid1 <;> simp [AuthHybridStateFixed.empty, AuthSlotState.lookupSend] at h1

theorem allocSend_of_none {S : Setup} (ss : AuthSlotState) (sid : SessionId S)
    (hSend : IsSendSessionId S sid) (hNone : ss.lookupSend sid = none) :
    (ss.allocSend sid).1 = ss.nextSlot ∧
    (ss.allocSend sid).2.nextSlot = ss.nextSlot + 1 ∧
    (ss.allocSend sid).2.recvTbl = ss.recvTbl ∧
    ∀ sid' : SessionId S,
      (ss.allocSend sid).2.lookupSend sid' =
        if sid' = sid then some ss.nextSlot else ss.lookupSend sid' := by
  cases sid with
  | sendOPK u i =>
    simp only [AuthSlotState.lookupSend] at hNone
    simp only [AuthSlotState.allocSend, hNone]
    refine ⟨trivial, trivial, trivial, fun sid' => ?_⟩
    cases sid' with
    | sendOPK u' i' =>
      simp only [AuthSlotState.lookupSend]
      by_cases hu : u'.1 = u.1
      · have huEq : u' = u := Fin.ext hu
        subst huEq
        by_cases hi : i'.1 = i.1
        · have hiEq : i' = i := Fin.ext hi
          subst hiEq; simp
        · have hne : (SessionId.sendOPK u' i' : SessionId S) ≠ SessionId.sendOPK u' i := by
            intro h; injection h with _ h2; exact hi (congrArg Fin.val h2)
          simp [hi, hne]
      · have hne : (SessionId.sendOPK u' i' : SessionId S) ≠ SessionId.sendOPK u i := by
          intro h; injection h with h1 _; exact hu (congrArg Fin.val h1)
        simp [hu, hne]
    | sendNoOPK _ _ => simp [AuthSlotState.lookupSend]
    | recvOPK _ _ _ => simp [AuthSlotState.lookupSend]
    | recvNoOPK _ _ _ => simp [AuthSlotState.lookupSend]
  | sendNoOPK u i =>
    simp only [AuthSlotState.lookupSend] at hNone
    simp only [AuthSlotState.allocSend, hNone]
    refine ⟨trivial, trivial, trivial, fun sid' => ?_⟩
    cases sid' with
    | sendOPK _ _ => simp [AuthSlotState.lookupSend]
    | sendNoOPK u' i' =>
      simp only [AuthSlotState.lookupSend]
      by_cases hu : u'.1 = u.1
      · have huEq : u' = u := Fin.ext hu
        subst huEq
        by_cases hi : i'.1 = i.1
        · have hiEq : i' = i := Fin.ext hi
          subst hiEq; simp
        · have hne : (SessionId.sendNoOPK u' i' : SessionId S) ≠ SessionId.sendNoOPK u' i := by
            intro h; injection h with _ h2; exact hi (congrArg Fin.val h2)
          simp [hi, hne]
      · have hne : (SessionId.sendNoOPK u' i' : SessionId S) ≠ SessionId.sendNoOPK u i := by
          intro h; injection h with h1 _; exact hu (congrArg Fin.val h1)
        simp [hu, hne]
    | recvOPK _ _ _ => simp [AuthSlotState.lookupSend]
    | recvNoOPK _ _ _ => simp [AuthSlotState.lookupSend]
  | recvOPK _ _ _ => exact False.elim hSend
  | recvNoOPK _ _ _ => exact False.elim hSend

theorem allocRecv_of_none {S : Setup} (ss : AuthSlotState) (rc : Nat)
    (hNone : ss.recvTbl rc = none) :
    (ss.allocRecv rc).1 = ss.nextSlot ∧
    (ss.allocRecv rc).2.nextSlot = ss.nextSlot + 1 ∧
    (∀ sid' : SessionId S, (ss.allocRecv rc).2.lookupSend sid' = ss.lookupSend sid') ∧
    (∀ r', (ss.allocRecv rc).2.recvTbl r' = if r' = rc then some ss.nextSlot else ss.recvTbl r') := by
  simp only [AuthSlotState.allocRecv, hNone]
  refine ⟨trivial, trivial, fun sid' => ?_, fun _ => trivial⟩
  cases sid' <;> rfl

theorem allocSend_lt_nextSlot {S : Setup} (ss : AuthSlotState) (sid : SessionId S)
    (hSend : IsSendSessionId S sid)
    (hLt : ∀ (sid' : SessionId S) k, ss.lookupSend sid' = some k → k < ss.nextSlot) :
    (ss.allocSend sid).1 < (ss.allocSend sid).2.nextSlot := by
  cases sid with
  | sendOPK u i =>
    simp only [AuthSlotState.allocSend]
    cases h : ss.sendOpkTbl u.1 i.1 with
    | none => dsimp only; omega
    | some k => exact hLt (.sendOPK u i) k h
  | sendNoOPK u i =>
    simp only [AuthSlotState.allocSend]
    cases h : ss.sendNoOpkTbl u.1 i.1 with
    | none => dsimp only; omega
    | some k => exact hLt (.sendNoOPK u i) k h
  | recvOPK _ _ _ => exact False.elim hSend
  | recvNoOPK _ _ _ => exact False.elim hSend

theorem allocRecv_lt_nextSlot (ss : AuthSlotState) (rc : Nat)
    (hLt : ∀ r k, ss.recvTbl r = some k → k < ss.nextSlot) :
    (ss.allocRecv rc).1 < (ss.allocRecv rc).2.nextSlot := by
  simp only [AuthSlotState.allocRecv]
  cases h : ss.recvTbl rc with
  | none => dsimp only; omega
  | some k => exact hLt rc k h

private def isAuthSendQueryB {S : Setup} : (Nat ⊕ AuthQuery S) → Bool
  | .inr (.sendOPK _ _ _ _ _)   => true
  | .inr (.sendNoOPK _ _ _ _ _) => true
  | _                           => false

@[local simp] private theorem isAuthSendQueryB_eq_true_iff {S : Setup} (q : Nat ⊕ AuthQuery S) :
    isAuthSendQueryB q = true ↔ isAuthSendQuery q := by
  rcases q with _ | q
  · simp [isAuthSendQueryB, isAuthSendQuery]
  · cases q <;> simp [isAuthSendQueryB, isAuthSendQuery]

def isAuthSessQueryB {S : Setup} : (Nat ⊕ AuthQuery S) → Bool
  | .inr (.sendOPK _ _ _ _ _)   => true
  | .inr (.sendNoOPK _ _ _ _ _) => true
  | .inr (.recvOPK _ _ _ _)     => true
  | .inr (.recvNoOPK _ _ _ _)   => true
  | _                           => false

theorem isQueryBoundP_bool_or_add {ι α : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (b1 b2 b : ι → Bool)
    (hOr : ∀ i, b i = true → b1 i = true ∨ b2 i = true)
    (n1 n2 : Nat)
    (h1 : IsQueryBoundP oa (fun i => b1 i = true) n1)
    (h2 : IsQueryBoundP oa (fun i => b2 i = true) n2) :
    IsQueryBoundP oa (fun i => b i = true) (n1 + n2) := by
  induction oa using OracleComp.inductionOn generalizing n1 n2 with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind i k ih =>
    rw [isQueryBoundP_query_bind_iff] at h1 h2 ⊢
    rcases h1 with ⟨hf1, hc1⟩
    rcases h2 with ⟨hf2, hc2⟩
    cases hb : b i with
    | false =>
      refine ⟨Or.inl (by simp), fun u => ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (ih u _ _ (hc1 u) (hc2 u)).mono (by split_ifs <;> omega)
    | true =>
      rcases hOr i hb with hb1 | hb2
      · have hn1 : 0 < n1 := by
          rcases hf1 with hAbs | hp
          · exact False.elim (hAbs hb1)
          · exact hp
        refine ⟨Or.inr (by omega), fun u => ?_⟩
        simp only [↓reduceIte]
        exact (ih u _ _ (hc1 u) (hc2 u)).mono (by simp only [hb1, ↓reduceIte]; split_ifs <;> omega)
      · have hn2 : 0 < n2 := by
          rcases hf2 with hAbs | hp
          · exact False.elim (hAbs hb2)
          · exact hp
        refine ⟨Or.inr (by omega), fun u => ?_⟩
        simp only [↓reduceIte]
        exact (ih u _ _ (hc1 u) (hc2 u)).mono (by simp only [hb2, ↓reduceIte]; split_ifs <;> omega)

theorem isQueryBoundP_bool_imp {ι α : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (b1 b2 : ι → Bool)
    (hImp : ∀ i, b2 i = true → b1 i = true) (n : Nat)
    (h1 : IsQueryBoundP oa (fun i => b1 i = true) n) :
    IsQueryBoundP oa (fun i => b2 i = true) n := by
  simpa using isQueryBoundP_bool_or_add oa b1 (fun _ => false) b2
    (fun i hi => Or.inl (hImp i hi)) n 0 h1 (by
      clear h1
      induction oa using OracleComp.inductionOn with
      | pure _ => exact isQueryBoundP_pure _ _ _
      | query_bind _ _ ih =>
        rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp), fun u => ih u⟩)

theorem isQueryBoundP_isAuthSessQueryB_min (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    IsQueryBoundP A.1.run (fun q => isAuthSessQueryB q = true) (min b.q_total S.N_sess_tot) := by
  let isRecvB : (Nat ⊕ AuthQuery S) → Bool := fun
    | .inr (.recvOPK _ _ _ _) => true
    | .inr (.recvNoOPK _ _ _ _) => true
    | _ => false
  have hRecvIff : ∀ q, isRecvB q = true ↔ isAuthRecvQuery q := by
    rintro (_ | q)
    · simp [isRecvB, isAuthRecvQuery]
    · cases q <;> simp [isRecvB, isAuthRecvQuery]
  have hSend : IsQueryBoundP A.1.run (fun q => isAuthSendQueryB q = true) S.N_send_tot := by
    simpa only [isAuthSendQueryB_eq_true_iff] using A.2.2.1
  have hRecv : IsQueryBoundP A.1.run (fun q => isRecvB q = true) S.N_recv_tot := by
    simpa only [hRecvIff] using A.2.2.2.1
  have hSess : IsQueryBoundP A.1.run (fun q => isAuthSessQueryB q = true) S.N_sess_tot := by
    have hSum := isQueryBoundP_bool_or_add A.1.run isAuthSendQueryB isRecvB isAuthSessQueryB
      (fun q hq => by
        cases q with
        | inl _ => cases hq
        | inr q => cases q <;> simp_all [isAuthSessQueryB, isAuthSendQueryB, isRecvB])
      S.N_send_tot S.N_recv_tot hSend hRecv
    simpa only [Setup.N_sess_tot] using hSum
  have hTot : IsQueryBoundP A.1.run (fun q => isAuthSessQueryB q = true) b.q_total :=
    isQueryBoundP_bool_imp A.1.run isGameQuery isAuthSessQueryB
      (fun q hq => by cases q with | inl _ => cases hq | inr _ => rfl) b.q_total
      (SignalPqxdh.QueryBounded.auth_total A.2)
  by_cases hle : b.q_total ≤ S.N_sess_tot
  · rwa [Nat.min_eq_left hle]
  · rwa [Nat.min_eq_right (Nat.le_of_not_le hle)]

theorem simulateQ_finishAuthSendCkSlotsPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (p : Bytes × Bytes)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthSendCkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p) =
      pure (finishAuthSendCkSlots P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p) :=
  simulateQ_finishAuthSendCkPrim S P sid uEntry peerPrincipal? bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst p
    hPrin hSpk hOpk

theorem simulateQ_authCkRecvWithSlotsPrim (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S)
    (hPrep : ∀ prep, prep? = some prep →
      prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
      prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
      prep.finishTag.hstDec.base.principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (authCkRecvWithPrim S sampAt msg prep? hst) =
      authCkRecvWithSlots S P sampAtPure msg (prep?.map (PreparedAuthRecvPrim.toPure true P)) hst :=
  simulateQ_authCkRecvWithPrim S P sampAt sampAtPure hSamp msg prep? hst hPrep

theorem authCkRecvWithSlots_cacheAuthAdvKeysFixed (S : Setup) (P : Primitives)
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) :
    authCkRecvWithSlots S P sampAtPure msg
      ((prep?.map (PreparedAuthRecvPrim.mapState (cacheAuthAdvKeys P))).map
        (PreparedAuthRecvPrim.toPure true P))
      (cacheAuthAdvKeysFixed P hst) =
    Prod.map id (cacheAuthAdvKeysFixed P) <$>
      authCkRecvWithSlots S P sampAtPure msg
        (prep?.map (PreparedAuthRecvPrim.toPure true P)) hst := by
  unfold authCkRecvWithSlots cacheAuthAdvKeysFixed
  cases prep? with
  | none => simp [Prod.map]
  | some prep =>
    dsimp only [Option.map, PreparedAuthRecvPrim.mapState, PreparedAuthRecvPrim.toPure]
    simp only [cacheAuthAdvKeys_roCache, cacheAuthAdvKeys_rootRoCache]
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only; simp [Prod.map, finishAuthRecvCkSlots, finishAuthRecvCk]
        · simp only [map_bind]; congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only; simp only [map_bind, map_pure]; congr 1; funext p
            simp [Prod.map, finishAuthRecvCkSlots, finishAuthRecvCk]
      | none =>
        dsimp only; simp only [map_bind]; congr 1; funext drKey; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [Prod.map]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only; simp only [map_bind, map_pure]; congr 1; funext p
          simp [Prod.map, finishAuthRecvCkSlots, finishAuthRecvCk]
    · simp only [map_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => simp [Prod.map]
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        dsimp only; simp [Prod.map]


end AuthSubHops1to3

end SignalPqxdh.Security
