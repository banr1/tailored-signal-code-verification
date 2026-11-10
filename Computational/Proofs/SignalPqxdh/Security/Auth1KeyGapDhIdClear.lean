/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdPreSample

/-!
# Clearing the target signing secret in the one-key `Auth` simulator

**Checked by Lean.** Defines `clearAuthSecSign tIdx`, which clears `secIKAsign` at principal `tIdx`
in `FgAuthSimState S`, and proves that `AuthDh3.fgAuthStepPure` commutes with `clearAuthSecSign` on
every query except `.initPrin`, `.corruptIK`, and `.genSPK`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh1Key

namespace Proofs.SignalPqxdh.Security

local macro "splitc" : tactic =>
  `(tactic| (split <;> (rename_i hc; try simp only [hc, ↓reduceIte, Bool.false_eq_true, pure_bind])))

def clearAuthSecSignBase {S : Setup} (tIdx : ℕ) (st : AuthState S) : AuthState S :=
  { st with principals := st.principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) }

/-- Clear `secIKAsign` at principal `tIdx` in `FgAuthSimState S`. -/
def clearAuthSecSign {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) : FgAuthSimState S :=
  { st with base := clearAuthSecSignBase tIdx st.base }

@[simp] theorem clearAuthSecSign_base_principals {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.principals =
      st.base.principals.map (fun (idx, e) => (idx, clearTargetPrinSecSign tIdx idx e)) := rfl
@[simp] theorem clearAuthSecSign_base_spkBundles {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.spkBundles = st.base.spkBundles := rfl
@[simp] theorem clearAuthSecSign_base_opkEntries {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.opkEntries = st.base.opkEntries := rfl
@[simp] theorem clearAuthSecSign_base_sessions {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.sessions = st.base.sessions := rfl
@[simp] theorem clearAuthSecSign_base_usedSendSessions {S : Setup} (tIdx : ℕ)
    (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.usedSendSessions = st.base.usedSendSessions := rfl
@[simp] theorem clearAuthSecSign_base_usedRecvOPK {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.usedRecvOPK = st.base.usedRecvOPK := rfl
@[simp] theorem clearAuthSecSign_base_usedRecvNoOPK {S : Setup} (tIdx : ℕ)
    (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.usedRecvNoOPK = st.base.usedRecvNoOPK := rfl
@[simp] theorem clearAuthSecSign_base_seenKyberBaseKeys {S : Setup} (tIdx : ℕ)
    (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.seenKyberBaseKeys = st.base.seenKyberBaseKeys := rfl
@[simp] theorem clearAuthSecSign_base_advKeys {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.advKeys = st.base.advKeys := rfl
@[simp] theorem clearAuthSecSign_base_secb {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).base.secb = st.base.secb := rfl
@[simp] theorem clearAuthSecSign_fgL {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).fgL = st.fgL := rfl
@[simp] theorem clearAuthSecSign_fgRootL {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).fgRootL = st.fgRootL := rfl
@[simp] theorem clearAuthSecSign_rawRoCache {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).rawRoCache = st.rawRoCache := rfl
@[simp] theorem clearAuthSecSign_advRoLog {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).advRoLog = st.advRoLog := rfl
@[simp] theorem clearAuthSecSign_respRecs {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).respRecs = st.respRecs := rfl
@[simp] theorem clearAuthSecSign_advKeyPows {S : Setup} (tIdx : ℕ) (st : FgAuthSimState S) :
    (clearAuthSecSign tIdx st).advKeyPows = st.advKeyPows := rfl

@[simp] theorem isTargetPrinCorrupted_clearAuthSecSign {S : Setup} (targetIdx tIdx : ℕ)
    (st : FgAuthSimState S) :
    isTargetPrinCorrupted targetIdx (clearAuthSecSign tIdx st) =
      isTargetPrinCorrupted targetIdx st := by
  unfold isTargetPrinCorrupted
  rw [clearAuthSecSign_base_principals, find?_idx_map_clearTargetPrinSecSign]
  cases st.base.principals.find? (fun (idx, _) => idx == targetIdx) with
  | none => rfl
  | some p => rcases p with ⟨_, e⟩; simp

theorem fgRunSendAuthPure_clearAuthSecSign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U : Bytes) (sid : SessionId S)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (st : FgAuthSimState S) :
    AuthDh3.fgRunSendAuthPure P ddh useDh1 targetIdx S maxLen U sid u bundle m0 m1
        (clearAuthSecSign tIdx st) =
      (AuthDh3.fgRunSendAuthPure P ddh useDh1 targetIdx S maxLen U sid u bundle m0 m1 st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  unfold AuthDh3.fgRunSendAuthPure
  dsimp only [clearAuthSecSign_base_usedSendSessions,
    clearAuthSecSign_base_spkBundles, clearAuthSecSign_base_opkEntries,
    clearAuthSecSign_base_sessions, clearAuthSecSign_base_secb, clearAuthSecSign_fgL,
    clearAuthSecSign_fgRootL, clearAuthSecSign_advKeyPows]
  simp only [clearAuthSecSign_base_principals, find?_idx_map_clearTargetPrinSecSign, findHonestPrincipal_take_map_clearTargetPrinSecSign,
    koskBundleOkTake_map_clearTargetPrinSecSign, resolveSigPk_take_map_clearTargetPrinSecSign]
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, pure_bind]
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  by_cases h2 : st.base.usedSendSessions.contains sid = true
  · simp only [h2, ↓reduceIte, pure_bind]
  simp only [h2, Bool.false_eq_true, ↓reduceIte]
  cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => simp only [Option.map_none, pure_bind]
  | some pu =>
    rcases pu with ⟨idx, uEntry⟩
    simp only [Option.map_some, clearTargetPrinSecSign_secIKA0, clearTargetPrinSecSign_ikAPk]
    rcases hPeer : findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB with
      _ | ⟨k, pEntry⟩ <;>
      simp only [Option.map_none, Option.isSome_none, Option.map_some, Option.isSome_some,
        clearTargetPrinSecSign_corrupted]
    all_goals
      splitc
      splitc
      simp only [bind_assoc]
      congr 1; funext ekASkRaw
      congr 1; funext kemCoins
      congr 1; funext ephASk
      congr 1; funext spqrCoins
      splitc
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp only [pure_bind]
      | some sc =>
        rcases sc with ⟨ss, kemCt⟩
        simp only [bind_assoc]
        congr 1; funext x
        congr 1; funext y
        cases P.spqrInitSend x.1.pqrKey spqrCoins with
        | none => simp only [pure_bind]
        | some z =>
          rcases z with ⟨_, _, _⟩
          simp only [pure_bind]; rfl

theorem fgFinishRecvStep2AuthPure_clearAuthSecSign (S : Setup) (P : Primitives) (tIdx : ℕ)
    (msg : PreKeyMsg) (kEntry kEntry' : PrincipalEntry) (hk : kEntry'.ikAPk = kEntry.ikAPk)
    (drKey : DRKey) (fgL' : List FgPatchEntry) (rk1 ck1_1 : Bytes) (fgRootL' : List FgRootEntry)
    (mkSeed : Bytes) (spqrSalt? : Option Bytes) (updBase : AuthState S → AuthState S)
    (hUpd : ∀ b, updBase (clearAuthSecSignBase tIdx b) = clearAuthSecSignBase tIdx (updBase b))
    (st : FgAuthSimState S) :
    AuthDh3.fgFinishRecvStep2AuthPure S P msg kEntry' drKey fgL' rk1 ck1_1 fgRootL' mkSeed
        spqrSalt? updBase (clearAuthSecSign tIdx st) =
      (AuthDh3.fgFinishRecvStep2AuthPure S P msg kEntry drKey fgL' rk1 ck1_1 fgRootL' mkSeed
        spqrSalt? updBase st >>= fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  unfold AuthDh3.fgFinishRecvStep2AuthPure
  simp only [hk, clearAuthSecSign_base_principals, findHonestPrincipal_take_map_clearTargetPrinSecSign]
  cases P.aeadDec (P.deriveMsgKeys mkSeed spqrSalt?)
      (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
  | none => simp only [pure_bind]
  | some pt =>
    dsimp only
    have hSt : ({ clearAuthSecSign tIdx st with
        base := updBase (clearAuthSecSign tIdx st).base, fgL := fgL', fgRootL := fgRootL' } :
          FgAuthSimState S) =
        clearAuthSecSign tIdx { st with base := updBase st.base, fgL := fgL', fgRootL := fgRootL' } := by
      show ({ clearAuthSecSign tIdx st with
        base := updBase (clearAuthSecSignBase tIdx st.base), fgL := fgL', fgRootL := fgRootL' } :
          FgAuthSimState S) = _
      rw [hUpd]; rfl
    rw [hSt]
    cases findHonestPrincipal P (st.base.principals.take S.N_dh) msg.hdr.ikAPk <;>
      simp only [Option.map_none, Option.map_some, pure_bind]

theorem fgFinishRecvAuthPure_clearAuthSecSign (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (tIdx : ℕ)
    (msg : PreKeyMsg) (kEntry kEntry' : PrincipalEntry) (hk : kEntry'.ikAPk = kEntry.ikAPk)
    (hk0 : kEntry'.secIKA0 = kEntry.secIKA0) (bEntry : SpkBundleEntry) (ss : Bytes)
    (pos4? : Option FgPoS) (updBase : AuthState S → AuthState S)
    (hUpd : ∀ b, updBase (clearAuthSecSignBase tIdx b) = clearAuthSecSignBase tIdx (updBase b))
    (st : FgAuthSimState S) :
    AuthDh3.fgFinishRecvAuthPure S P ddh maxLen msg kEntry' bEntry ss pos4? updBase
        (clearAuthSecSign tIdx st) =
      (AuthDh3.fgFinishRecvAuthPure S P ddh maxLen msg kEntry bEntry ss pos4? updBase st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  unfold AuthDh3.fgFinishRecvAuthPure
  simp only [hk, hk0, clearAuthSecSign_fgL, clearAuthSecSign_fgRootL, bind_assoc]
  congr 1; funext dkL
  congr 1; funext rkOut
  cases P.spqrInitRecv dkL.1.pqrKey msg.pqRatchetMsg with
  | none => simp only [pure_bind]
  | some spqr =>
    dsimp only
    exact fgFinishRecvStep2AuthPure_clearAuthSecSign S P tIdx msg kEntry kEntry' hk _ _ _ _ _ _ _
      updBase hUpd st

theorem fgRunRecvOPKAuthPure_clearAuthSecSign (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (tIdx : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st : FgAuthSimState S) :
    AuthDh3.fgRunRecvOPKAuthPure S P ddh maxLen k j o msg (clearAuthSecSign tIdx st) =
      (AuthDh3.fgRunRecvOPKAuthPure S P ddh maxLen k j o msg st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  unfold AuthDh3.fgRunRecvOPKAuthPure
  dsimp only [clearAuthSecSign_base_usedRecvOPK, clearAuthSecSign_base_spkBundles,
    clearAuthSecSign_base_opkEntries, clearAuthSecSign_base_seenKyberBaseKeys,
    clearAuthSecSign_advKeyPows]
  simp only [clearAuthSecSign_base_principals, koskSenderOkTake_map_clearTargetPrinSecSign,
    find?_idx_map_clearTargetPrinSecSign]
  splitc
  splitc
  splitc
  all_goals
    cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp only [Option.map_none, pure_bind]
    | some pk =>
      rcases pk with ⟨idx, kEntry⟩
      simp only [Option.map_some]
      cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp only [pure_bind]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        dsimp only
        cases st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => simp only [pure_bind]
        | some po =>
          rcases po with ⟨_, oEntry⟩
          dsimp only
          splitc
          splitc
          all_goals
            cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none => simp only [pure_bind]
            | some ss =>
              dsimp only
              refine fgFinishRecvAuthPure_clearAuthSecSign S P ddh maxLen tIdx msg kEntry _
                (clearTargetPrinSecSign_ikAPk _ _ _) (clearTargetPrinSecSign_secIKA0 _ _ _)
                bEntry ss _ _ (fun _ => ?_) st
              rfl

theorem fgRunRecvNoOPKAuthPure_clearAuthSecSign (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (tIdx : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st : FgAuthSimState S) :
    AuthDh3.fgRunRecvNoOPKAuthPure S P ddh maxLen k j l msg (clearAuthSecSign tIdx st) =
      (AuthDh3.fgRunRecvNoOPKAuthPure S P ddh maxLen k j l msg st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  unfold AuthDh3.fgRunRecvNoOPKAuthPure
  dsimp only [clearAuthSecSign_base_usedRecvNoOPK, clearAuthSecSign_base_spkBundles, clearAuthSecSign_base_seenKyberBaseKeys,
    clearAuthSecSign_advKeyPows]
  simp only [clearAuthSecSign_base_principals, koskSenderOkTake_map_clearTargetPrinSecSign,
    find?_idx_map_clearTargetPrinSecSign]
  splitc
  splitc
  splitc
  all_goals
    cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp only [Option.map_none, pure_bind]
    | some pk =>
      rcases pk with ⟨idx, kEntry⟩
      simp only [Option.map_some]
      cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp only [pure_bind]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        dsimp only
        splitc
        all_goals
          cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => simp only [pure_bind]
          | some ss =>
            dsimp only
            refine fgFinishRecvAuthPure_clearAuthSecSign S P ddh maxLen tIdx msg kEntry _
              (clearTargetPrinSecSign_ikAPk _ _ _) (clearTargetPrinSecSign_secIKA0 _ _ _)
              bEntry ss _ _ (fun _ => ?_) st
            rfl

def isDelegatedAuthQuery {S : Setup} : AuthQuery S → Bool
  | .initPrin _  => false
  | .corruptIK _ => false
  | .genSPK _ _  => false
  | _            => true

theorem fgAuthStepPure_clearAuthSecSign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx tIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S)
    (hq : isDelegatedAuthQuery q = true) (st : FgAuthSimState S) :
    AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q
        (clearAuthSecSign tIdx st) =
      (AuthDh3.fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st >>=
        fun p => pure (p.1, clearAuthSecSign tIdx p.2)) := by
  cases q with
  | initPrin _ => cases hq
  | corruptIK _ => cases hq
  | genSPK _ _ => cases hq
  | genOPK u j o =>
    dsimp only [AuthDh3.fgAuthStepPure]
    simp only [clearAuthSecSign_base_opkEntries]
    by_cases hAny : (st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp only [hAny, ↓reduceIte, pure_bind]
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      rfl
  | sendOPK u i bundle m0 m1 =>
    dsimp only [AuthDh3.fgAuthStepPure]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgRunSendAuthPure_clearAuthSecSign P ddh useDh1 targetIdx tIdx S maxLen U
        (.sendOPK u i) u bundle m0 m1 st
    · simp only [↓reduceIte, pure_bind]
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only [AuthDh3.fgAuthStepPure]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgRunSendAuthPure_clearAuthSecSign P ddh useDh1 targetIdx tIdx S maxLen U
        (.sendNoOPK u i) u bundle m0 m1 st
    · simp only [↓reduceIte, pure_bind]
  | recvOPK k j o msg =>
    dsimp only [AuthDh3.fgAuthStepPure]
    exact fgRunRecvOPKAuthPure_clearAuthSecSign S P ddh maxLen tIdx k j o msg
      { st with respRecs := _ :: st.respRecs }
  | recvNoOPK k j l msg =>
    dsimp only [AuthDh3.fgAuthStepPure]
    exact fgRunRecvNoOPKAuthPure_clearAuthSecSign S P ddh maxLen tIdx k j l msg
      { st with respRecs := _ :: st.respRecs }
  | roQuery secrets =>
    dsimp only [AuthDh3.fgAuthStepPure]
    unfold fgRoQueryAuthPure
    simp only [clearAuthSecSign_advRoLog, clearAuthSecSign_fgL, clearAuthSecSign_rawRoCache]
    cases parseRoSecrets secrets with
    | none =>
      dsimp only
      cases st.rawRoCache.find? (fun (s, _) => s == secrets) with
      | some p => rcases p with ⟨_, dk⟩; dsimp only; simp only [pure_bind]; rfl
      | none => dsimp only; simp only [bind_assoc, pure_bind]; rfl
    | some tup =>
      rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩
      dsimp only; simp only [bind_assoc, pure_bind]; rfl
  | roRootQuery rk dh =>
    dsimp only [AuthDh3.fgAuthStepPure]
    unfold fgRoRootQueryAuthPure
    simp only [clearAuthSecSign_fgRootL, bind_assoc, pure_bind]; rfl
  | revealDhSecrets =>
    dsimp only [AuthDh3.fgAuthStepPure]; simp only [pure_bind]
  | registerKey sk =>
    dsimp only [AuthDh3.fgAuthStepPure]
    simp only [clearAuthSecSign_base_advKeys, clearAuthSecSign_advKeyPows]
    cases sk.length != 32
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]; rfl
    · simp only [↓reduceIte, pure_bind]

end Proofs.SignalPqxdh.Security
