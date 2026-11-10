/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC3
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
import Computational.Proofs.SignalPqxdh.Security.FgGapDhF
import VCVio.EvalDist.Monad.Basic
/-!
# `Auth` hop `G3 → G3.5`: `GapDH` step coupling for `DH3`

Maintains the simulation invariant `FgAuthSimInvDh3` across all `AuthQuery` steps to bound the
per-index `DH3 = CDH(ek_U*, spk_V*)` bad event `badAuthFgDh3At` by `GapDH` (`prob_badAuthFgDh3At_le_gapDh`).
-/

@[expose] public section
set_option autoImplicit false
open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security
namespace AuthDh3
@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_chainKdfSeed (P : Primitives) (ddh : Bytes → Bytes →
  Bytes → Bool) (ck : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh) (primGdhQ (.chainKdfSeed ck)) = pure
      (P.chainKdfSeed ck) := by rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl
@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_chainKdfNext (P : Primitives) (ddh : Bytes → Bytes →
  Bytes → Bool) (ck : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh) (primGdhQ (.chainKdfNext ck)) = pure
      (P.chainKdfNext ck) := by rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl
@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_spqrInitSend (P : Primitives) (ddh : Bytes → Bytes →
  Bytes → Bool) (k r : Bytes) :
    simulateQ (α := Option (Bytes × Option Bytes × Bytes)) (gapDhFullImpl P ddh)
      (primGdhQ (.spqrInitSend k r)) = pure (P.spqrInitSend k r) := by
        rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl
@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_spqrInitRecv (P : Primitives) (ddh : Bytes → Bytes →
  Bytes → Bool) (k m : Bytes) :
    simulateQ (α := Option (Bytes × Option Bytes)) (gapDhFullImpl P ddh)
      (primGdhQ (.spqrInitRecv k m)) = pure (P.spqrInitRecv k m) := by
        rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl
@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_deriveMsgKeys (P : Primitives) (ddh : Bytes → Bytes →
  Bytes → Bool) (seed : Bytes) (salt? : Option Bytes) :
    simulateQ (α := MessageKeys) (gapDhFullImpl P ddh)
      (primGdhQ (.deriveMsgKeys seed salt?)) = pure (P.deriveMsgKeys seed salt?) := by
        rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl
@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_aeadEnc (P : Primitives) (ddh : Bytes → Bytes → Bytes →
  Bool) (mk : MessageKeys) (ad pt : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh)
      (primGdhQ (.aeadEnc mk ad pt)) = pure (P.aeadEnc mk ad pt) := by
        rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl
@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_aeadDec (P : Primitives) (ddh : Bytes → Bytes → Bytes →
  Bool) (mk : MessageKeys) (ad ct : Bytes) :
    simulateQ (α := Option Bytes) (gapDhFullImpl P ddh)
      (primGdhQ (.aeadDec mk ad ct)) = pure (P.aeadDec mk ad ct) := by
        rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl
@[simp]
theorem simulateQ_gapDhFullImpl_embedPrim_findHonestPrincipalPrim (S : Setup) (P : Primitives) (ddh
  : Bytes → Bytes → Bytes → Bool) (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
  simulateQ (gapDhFullImpl P ddh)
      (FgGapDh.embedPrim (spec := gapDhOracleSpec) (FgGapDh.findHonestPrincipalPrim S principals
        ikB)) = pure (findHonestPrincipal P (principals.take S.N_dh) ikB) :=
        by rw [FgGapDh.simulateQ_gapDhFullImpl_embedPrim,
        FgGapDh.simulateQ_primBaseImpl_findHonestPrincipalPrim]
@[simp]
theorem simulateQ_gapDhFullImpl_embedPrim_resolveSigPkPrim (S : Setup) (P : Primitives) (ddh :
  Bytes → Bytes → Bytes → Bool) (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) : simulateQ
  (gapDhFullImpl P ddh)
      (FgGapDh.embedPrim (spec := gapDhOracleSpec) (FgGapDh.resolveSigPkPrim S principals ikB)) =
        pure (resolveSigPk P (principals.take S.N_dh) ikB) :=
        by rw [FgGapDh.simulateQ_gapDhFullImpl_embedPrim,
        FgGapDh.simulateQ_primBaseImpl_resolveSigPkPrim]
@[simp]
theorem simulateQ_gapDhFullImpl_embedPrim_koskSenderOkPrim (S : Setup) (P : Primitives) (ddh :
  Bytes → Bytes → Bytes → Bool) (principals : List (Nat × PrincipalEntry)) (advKeyPows : List (Bytes
  × Bytes)) (ikAPk : Bytes) : simulateQ (gapDhFullImpl P ddh)
      (FgGapDh.embedPrim (spec := gapDhOracleSpec) (FgGapDh.koskSenderOkPrim S principals advKeyPows
        ikAPk)) = pure (koskSenderOkTake S P principals advKeyPows ikAPk) :=
        by rw [FgGapDh.simulateQ_gapDhFullImpl_embedPrim,
        FgGapDh.simulateQ_primBaseImpl_koskSenderOkPrim]
@[simp]
theorem simulateQ_gapDhFullImpl_embedPrim_koskBundleOkPrim (S : Setup) (P : Primitives) (ddh :
  Bytes → Bytes → Bytes → Bool) (principals : List (Nat × PrincipalEntry)) (spkBundles : List ((Nat
  × Nat) × SpkBundleEntry)) (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (advKeyPows : List
  (Bytes × Bytes)) (bundle : PreKeyBundleInput) : simulateQ (gapDhFullImpl P ddh)
      (FgGapDh.embedPrim (spec := gapDhOracleSpec)
        (FgGapDh.koskBundleOkPrim S principals spkBundles opkEntries advKeyPows bundle)) = pure
          (koskBundleOkTake S P principals spkBundles opkEntries advKeyPows bundle) :=
          by rw [FgGapDh.simulateQ_gapDhFullImpl_embedPrim,
          FgGapDh.simulateQ_primBaseImpl_koskBundleOkPrim]
@[simp]
theorem simulateQ_gapDhFullImpl_embedPrim_lookupSpkSkPrim (S : Setup) (P : Primitives) (ddh :
  Bytes → Bytes → Bytes → Bool) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (advKeyPows :
  List (Bytes × Bytes)) (spkB : Bytes) : simulateQ (gapDhFullImpl P ddh)
      (FgGapDh.embedPrim (spec := gapDhOracleSpec) (FgGapDh.lookupSpkSkPrim S spkBundles advKeyPows
        spkB)) = pure (lookupSpkSkTake S P spkBundles advKeyPows spkB) :=
        by rw [FgGapDh.simulateQ_gapDhFullImpl_embedPrim,
        FgGapDh.simulateQ_primBaseImpl_lookupSpkSkPrim]
/-! ## Pure unfolding of `fgAuthStep` and CDH extraction -/
def fgFinishRecvStep2AuthPure (S : Setup) (P : Primitives) (msg : PreKeyMsg) (kEntry :
  PrincipalEntry) (drKey : DRKey) (fgL' : List FgPatchEntry) (rk1 : Bytes) (ck1_1 : Bytes) (fgRootL'
  : List FgRootEntry) (mkSeed : Bytes) (spqrSalt? : Option Bytes) (updBase : AuthState S → AuthState
  S)
    (st : FgAuthSimState S) : ProbComp (AuthResponse × FgAuthSimState S) :=
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  match P.aeadDec deriveMessageKeys (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg)
    msg.aeadCt with
  | none => pure (.noneResp, st)
  | some pt =>
    let st' : FgAuthSimState S := { st with
      base := updBase st.base, fgL := fgL', fgRootL := fgRootL' }
    match findHonestPrincipal P (st.base.principals.take S.N_dh) msg.hdr.ikAPk with
    | some _ => pure (.recvHonestResp, st')
    | none   => pure (.recvUnfreshResp drKey rk1 ck1_1 pt, st')
@[simp]
theorem simulateQ_gapDhFullImpl_fgFinishRecvStep2AuthGdh (S : Setup) (P : Primitives) (ddh : Bytes →
  Bytes → Bytes → Bool) (k : Fin S.N_id) (j : Fin S.N_recv) (msg : PreKeyMsg) (kEntry :
  PrincipalEntry) (drKey : DRKey) (fgL' : List FgPatchEntry) (rk1 : Bytes) (ck1_1 : Bytes) (fgRootL'
  : List FgRootEntry) (mkSeed : Bytes) (spqrSalt? : Option Bytes) (updBase : AuthState S → AuthState
  S) (st : FgAuthSimState S) : simulateQ (gapDhFullImpl P ddh) (fgFinishRecvStep2AuthGdh S k j msg
  kEntry drKey fgL' rk1 ck1_1 fgRootL' mkSeed spqrSalt? updBase st) =
      fgFinishRecvStep2AuthPure S P msg kEntry drKey fgL' rk1 ck1_1 fgRootL' mkSeed spqrSalt?
          updBase st := by
  unfold fgFinishRecvStep2AuthGdh fgFinishRecvStep2AuthPure
  simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_deriveMsgKeys,
    simulateQ_gapDhFullImpl_primGdhQ_aeadDec, pure_bind]
  cases P.aeadDec (P.deriveMsgKeys mkSeed spqrSalt?) (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk
    msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
  | none => rfl
  | some pt =>
    simp only [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim_findHonestPrincipalPrim, pure_bind]
    cases findHonestPrincipal P (st.base.principals.take S.N_dh) msg.hdr.ikAPk <;> rfl
noncomputable def fgFinishRecvAuthPure (S : Setup) (P : Primitives) (ddh : Bytes → Bytes → Bytes →
  Bool) (maxLen : ℕ) (msg : PreKeyMsg) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (ss :
  Bytes) (pos4? : Option FgPoS) (updBase : AuthState S → AuthState S)
    (st : FgAuthSimState S) : ProbComp (AuthResponse × FgAuthSimState S) := do
  let pos1 := computeTwoSideOrPairPosPure P [] bEntry.spkSk msg.hdr.ikAPk bEntry.spkPk
  let pos2 := computeTwoSideOrPairPosPure P [] kEntry.secIKA0 msg.hdr.ekAPk kEntry.ikAPk
  let pos3 := computeTwoSideOrPairPosPure P [] bEntry.spkSk msg.hdr.ekAPk bEntry.spkPk
  let dkL ← fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let posRatchet := computeTwoSideOrPairPosPure P [] bEntry.spkSk msg.ephAPk bEntry.spkPk
  let rkOut ← fgRootPatchPure ddh maxLen dkL.1.rootKey posRatchet st.fgRootL
  let mkSeed := P.chainKdfSeed rkOut.1.2; let ck1_1 := P.chainKdfNext rkOut.1.2
  match P.spqrInitRecv dkL.1.pqrKey msg.pqRatchetMsg with
  | none => pure (.noneResp, st)
  | some spqr =>
    fgFinishRecvStep2AuthPure S P msg kEntry dkL.1 dkL.2 rkOut.1.1 ck1_1 rkOut.2 mkSeed spqr.2
      updBase st
@[simp]
theorem simulateQ_gapDhFullImpl_fgFinishRecvAuthGdh (S : Setup) (P : Primitives) (ddh : Bytes →
  Bytes → Bytes → Bool) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (msg : PreKeyMsg) (kEntry :
  PrincipalEntry) (bEntry : SpkBundleEntry) (ss : Bytes) (pos4? : Option FgPoS) (updBase : AuthState
  S → AuthState S) (st : FgAuthSimState S) : simulateQ (gapDhFullImpl P ddh) (fgFinishRecvAuthGdh S
  maxLen k j msg kEntry bEntry ss pos4? updBase st) =
      fgFinishRecvAuthPure S P ddh maxLen msg kEntry bEntry ss pos4? updBase st := by
  unfold fgFinishRecvAuthGdh fgFinishRecvAuthPure
  simp only [simulateQ_bind, simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
    simulateQ_gapDhFullImpl_fgPatch, simulateQ_gapDhFullImpl_fgRootPatch,
    simulateQ_gapDhFullImpl_primGdhQ_chainKdfSeed, simulateQ_gapDhFullImpl_primGdhQ_chainKdfNext,
    simulateQ_gapDhFullImpl_primGdhQ_spqrInitRecv, pure_bind]
  apply bind_congr; intro dkL; apply bind_congr; intro rkOut
  cases P.spqrInitRecv dkL.1.pqrKey msg.pqRatchetMsg with
  | none => rfl
  | some spqr =>
    exact simulateQ_gapDhFullImpl_fgFinishRecvStep2AuthGdh S P ddh k j msg kEntry dkL.1 dkL.2
      rkOut.1.1 _ rkOut.2 _ spqr.2 updBase st
noncomputable def fgRunRecvOPKAuthPure (S : Setup) (P : Primitives) (ddh : Bytes → Bytes → Bytes →
  Bool) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (st : FgAuthSimState S) : ProbComp (AuthResponse × FgAuthSimState S) := do
  if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
    msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvOPK.contains (k.val, j.val, o.val) then return (.noneResp, st)
  if !koskSenderOkTake S P st.base.principals st.advKeyPows msg.hdr.ikAPk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let some (_, oEntry) := st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.noneResp, st)
  if oEntry.consumed then return (.noneResp, st)
  let (replayOk, usedTriples') := checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val
      msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
  if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
    return (.noneResp, st)
  let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return (.noneResp, st)
  let pos4 := computeTwoSideOrPairPosPure P [] oEntry.opkSk msg.hdr.ekAPk oEntry.opkPk
  let opks' := st.base.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  fgFinishRecvAuthPure S P ddh maxLen msg kEntry bEntry ss (some pos4) (fun base => { base with
      opkEntries := opks', usedRecvOPK := (k.val, j.val, o.val) :: base.usedRecvOPK
      seenKyberBaseKeys := usedTriples' }) st
@[simp]
theorem simulateQ_gapDhFullImpl_fgRunRecvOPKAuthGdh (S : Setup) (P : Primitives) (ddh : Bytes →
  Bytes → Bytes → Bool) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg :
  PreKeyMsg) (st : FgAuthSimState S) : simulateQ (gapDhFullImpl P ddh) (fgRunRecvOPKAuthGdh S maxLen
  k j o msg st) =
      fgRunRecvOPKAuthPure S P ddh maxLen k j o msg st := by
  unfold fgRunRecvOPKAuthGdh fgRunRecvOPKAuthPure
  by_cases hHdr : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
    msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, simulateQ_pure]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : st.base.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [hUsed, ↓reduceIte, simulateQ_pure]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
        simulateQ_gapDhFullImpl_embedPrim_koskSenderOkPrim, pure_bind]
      by_cases hKosk : (!koskSenderOkTake S P st.base.principals st.advKeyPows msg.hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, simulateQ_pure]
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => rfl
            | some op =>
              rcases op with ⟨_, oEntry⟩; dsimp only; by_cases hCons : oEntry.consumed = true
              · simp only [hCons, ↓reduceIte, simulateQ_pure]
              · simp only [hCons, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
                  simulateQ_gapDhFullImpl_primGdhQ_isCanonical, pure_bind]
                by_cases hRep : (!(checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val
                  msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk ||
                  !P.isCanonical msg.ephAPk) = true
                · simp only [hRep, ↓reduceIte, simulateQ_pure]
                · simp only [hRep, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
                    simulateQ_gapDhFullImpl_primGdhQ_kemDecaps, pure_bind]
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => rfl
                  | some ss => simp
noncomputable def fgRunRecvNoOPKAuthPure (S : Setup) (P : Primitives) (ddh : Bytes → Bytes → Bytes →
  Bool) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (st : FgAuthSimState S) : ProbComp (AuthResponse × FgAuthSimState S) := do
  if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 && msg.hdr.ekAPk.length == 32 &&
    msg.ephAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvNoOPK.contains (k.val, j.val, l.val) then return (.noneResp, st)
  if !koskSenderOkTake S P st.base.principals st.advKeyPows msg.hdr.ikAPk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let (replayOk, usedTriples') := checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val
      msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
  if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then
    return (.noneResp, st)
  let some ss := P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt | return (.noneResp, st)
  fgFinishRecvAuthPure S P ddh maxLen msg kEntry bEntry ss none (fun base => { base with
      usedRecvNoOPK := (k.val, j.val, l.val) :: base.usedRecvNoOPK
      seenKyberBaseKeys := usedTriples' }) st
@[simp]
theorem simulateQ_gapDhFullImpl_fgRunRecvNoOPKAuthGdh (S : Setup) (P : Primitives) (ddh : Bytes →
  Bytes → Bytes → Bool) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg :
  PreKeyMsg) (st : FgAuthSimState S) : simulateQ (gapDhFullImpl P ddh) (fgRunRecvNoOPKAuthGdh S
  maxLen k j l msg st) =
      fgRunRecvNoOPKAuthPure S P ddh maxLen k j l msg st := by
  unfold fgRunRecvNoOPKAuthGdh fgRunRecvNoOPKAuthPure
  by_cases hHdr : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 && msg.hdr.ekAPk.length == 32 &&
    msg.ephAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, simulateQ_pure]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : st.base.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [hUsed, ↓reduceIte, simulateQ_pure]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
        simulateQ_gapDhFullImpl_embedPrim_koskSenderOkPrim, pure_bind]
      by_cases hKosk : (!koskSenderOkTake S P st.base.principals st.advKeyPows msg.hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, simulateQ_pure]
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => rfl
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => rfl
          | some bp =>
            rcases bp with ⟨_, bEntry⟩; dsimp only
            simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_isCanonical, pure_bind]
            by_cases hRep : (!(checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
              msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical
              msg.ephAPk) = true
            · simp only [hRep, ↓reduceIte, simulateQ_pure]
            · simp only [hRep, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
                simulateQ_gapDhFullImpl_primGdhQ_kemDecaps, pure_bind]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => rfl
              | some ss => simp
noncomputable def fgRunSendAuthPure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 :
  Bool) (targetIdx : ℕ) (S : Setup) (maxLen : ℕ) (U : Bytes) (sid : SessionId S) (u : Fin S.N_id)
  (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : FgAuthSimState S) : ProbComp (AuthResponse × FgAuthSimState S) := do
  if m0.length != m1.length then return (.noneResp, st)
  if st.base.usedSendSessions.contains sid then return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  let peerPrincipal? := findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB
  let isFreshPeer : Bool := match peerPrincipal? with
    | some (_, pEntry) => !PrincipalEntry.corrupted pEntry
    | none             => false
  if !isFreshPeer && m0 != m1 then return (.noneResp, st)
  if !koskBundleOkTake S P st.base.principals st.base.spkBundles st.base.opkEntries st.advKeyPows
    bundle then
    return (.noneResp, st)
  let isTargetEph : Bool := !useDh1 && (initSessionSlotIdx sid == targetIdx)
  let ekASkRaw ← sampleScalar32; let kemCoins ← sampleCoins32
  let ephASk ← sampleScalar32; let spqrCoins ← sampleCoins32
  let sigPkB := resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig && P.sigVerify sigPkB (encodeKEM
    bundle.pqspkB) bundle.pqspkSig) then
    return (.noneResp, st)
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins | return (.noneResp, st)
  let ekASk := if isTargetEph then [] else ekASkRaw
  let ekAPk := if isTargetEph then U else P.x25519Base ekASkRaw
  let spkSk := lookupSpkSkTake S P st.base.spkBundles st.advKeyPows bundle.spkB
  let pos1 := computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
  let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
  let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
  let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk)))
  let (drKey, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let ephAPk := P.x25519Base ephASk; let dhRatchet := P.x25519 ephASk bundle.spkB
  let posRatchet := mkSecretPosPure P dhRatchet
  let ((rk1, ck1_0), fgRootL') ← fgRootPatchPure ddh maxLen drKey.rootKey posRatchet st.fgRootL
  let mkSeed := P.chainKdfSeed ck1_0; let ck1_1 := P.chainKdfNext ck1_0
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return (.noneResp, st)
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let msgPlain := if isFreshPeer then (if st.base.secb then m1 else m0) else m0
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let hdr : HandshakeHdr := {
    ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId
    opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
  let wireMsg : PreKeyMsg := {
    hdr := hdr, ephAPk := ephAPk, pqRatchetMsg := pqRatchetMsg, aeadCt := aeadCt }
  let (spkHon, opkHon, pqspkHon) :=
    match peerPrincipal? with
    | none => (false, false, false)
    | some (k, _) =>
      (st.base.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB), false,
        st.base.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))
  let sessEntry : AuthInitiatorEntry S := {
    sid := sid, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB
    peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB
    spkHonest := spkHon, opkHonest := opkHon, pqspkHonest := pqspkHon
    ekASk := ekASk, ephASk := ephASk, fresh := isFreshPeer
    challenged := isFreshPeer && (m0 != m1) }
  let base' : AuthState S := { st.base with
    sessions := sessEntry :: st.base.sessions
    usedSendSessions := sid :: st.base.usedSendSessions }
  let st' : FgAuthSimState S := { st with base := base', fgL := fgL', fgRootL := fgRootL' }
  if peerPrincipal?.isSome then
    return (.sendFreshResp wireMsg, st')
  else
    return (.sendUnfreshResp drKey rk1 ck1_1 wireMsg, st')
@[simp]
theorem simulateQ_gapDhFullImpl_fgRunSendAuthGdh (P : Primitives) (ddh : Bytes → Bytes → Bytes →
  Bool) (useDh1 : Bool) (targetIdx : ℕ) (S : Setup) (maxLen : ℕ) (U : Bytes) (sid : SessionId S) (u
  : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (st : FgAuthSimState S) : simulateQ
  (gapDhFullImpl P ddh) (fgRunSendAuthGdh useDh1 targetIdx S maxLen U sid u bundle m0 m1 st) =
      fgRunSendAuthPure P ddh useDh1 targetIdx S maxLen U sid u bundle m0 m1 st := by
  unfold fgRunSendAuthGdh fgRunSendAuthPure; by_cases hLen : (m0.length != m1.length) = true
  · simp only [hLen, ↓reduceIte, simulateQ_pure]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte]
    by_cases hSid : st.base.usedSendSessions.contains sid = true
    · simp only [hSid, ↓reduceIte, simulateQ_pure]
    · simp only [hSid, Bool.false_eq_true, ↓reduceIte]
      cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some pu =>
        rcases pu with ⟨_, uEntry⟩; dsimp only
        rw [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim_findHonestPrincipalPrim, pure_bind]
        by_cases hUnf : (!(match findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB
          with
            | some (_, pEntry) =>
              !PrincipalEntry.corrupted pEntry | none => false) && (m0 != m1)) = true
        · cases hFP : findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;>
            simp_all only [↓reduceIte, simulateQ_pure]
        · cases hFP : findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;> (
            simp_all only [Bool.false_eq_true, ↓reduceIte]
            simp only [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim_koskBundleOkPrim,
              pure_bind]
            by_cases hKosk : (!koskBundleOkTake S P st.base.principals st.base.spkBundles
              st.base.opkEntries st.advKeyPows bundle) = true
            · simp only [hKosk, ↓reduceIte, simulateQ_pure]
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
                simulateQ_gapDhFullImpl_unifGdh]
              congr 1; ext ekASkRaw; congr 1; ext kemCoins; congr 1; ext ephASk; congr 1; ext
                spqrCoins
              simp only [simulateQ_gapDhFullImpl_embedPrim_resolveSigPkPrim,
                simulateQ_gapDhFullImpl_primGdhQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh)
                bundle.ikB) (encodeEC bundle.spkB) bundle.spkSig && P.sigVerify (resolveSigPk P
                (st.base.principals.take S.N_dh) bundle.ikB) (encodeKEM bundle.pqspkB)
                bundle.pqspkSig)) = true
              · simp only [hSig, ↓reduceIte, simulateQ_pure]
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
                  simulateQ_gapDhFullImpl_primGdhQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => rfl
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩; dsimp only
                  simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
                    simulateQ_gapDhFullImpl_embedPrim_lookupSpkSkPrim,
                    simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
                    simulateQ_gapDhFullImpl_computeOptPos, simulateQ_gapDhFullImpl_fgPatch,
                    pure_bind]
                  congr 1; ext ⟨drKey, fgL'⟩; dsimp only
                  simp only [simulateQ_gapDhFullImpl_primGdhQ_x25519,
                    simulateQ_gapDhFullImpl_mkSecretPos, simulateQ_gapDhFullImpl_fgRootPatch,
                    pure_bind]
                  congr 1; ext ⟨⟨rk1, ck1_0⟩, fgRootL'⟩; dsimp only
                  simp only [simulateQ_gapDhFullImpl_primGdhQ_chainKdfSeed,
                    simulateQ_gapDhFullImpl_primGdhQ_chainKdfNext,
                    simulateQ_gapDhFullImpl_primGdhQ_spqrInitSend, pure_bind]
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => rfl
                  | some spqr =>
                    rcases spqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only; simp)
noncomputable def fgAuthStepPure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 :
  Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery S) (st :
  FgAuthSimState S) :
    ProbComp (AuthResponse × FgAuthSimState S) := do
  match q with
  | .initPrin u =>
    if st.base.principals.any (fun (idx, _) => idx == u.val) then return (.noneResp, st)
    let isTargetPrin : Bool := useDh1 && (u.val == targetIdx); let secIKA0Raw ← sampleScalar32
    let secIKAsign ← sampleScalar32
    let entry : PrincipalEntry := {
      secIKA0    := if isTargetPrin then [] else secIKA0Raw
      ikAPk      := if isTargetPrin then U else P.x25519Base secIKA0Raw
      secIKAsign := secIKAsign
      ikSignPk   := P.sigPkGen secIKAsign
      corrupted  := false }
    let base' := { st.base with principals := (u.val, entry) :: st.base.principals }
    return (.initPrinResp entry.ikAPk entry.ikSignPk, { st with base := base' })
  | .corruptIK u =>
    match st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, st)
    | some (_, entry) =>
      let principals' := st.base.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      let base' := { st.base with principals := principals' }
      return (.corrResp entry.secIKA0 entry.secIKAsign, { st with base := base' })
  | .genSPK u j =>
    if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then return (.noneResp, st)
    let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, st)
    let isTargetSpk : Bool := spkBundleFlatIdx S u j == targetSpkIdx; let spkSkRaw ← sampleScalar32
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else P.x25519Base spkSkRaw; let rSpk ← sampleRandom64
    let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
    let (pqspkPk, pqspkSk) ← sampleKemKeyGen P; let rPq ← sampleRandom64
    let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry := {
      spkSk := spkSk, spkPk := spkPk, spkSig := spkSig
      pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
    let base' := { st.base with spkBundles := ((u.val, j.val), bEntry) :: st.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig
      opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
    return (.bundleResp bundleOut, { st with base := base' })
  | .genOPK u j o =>
    if st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then return (.noneResp, st)
    let opkSk ← sampleScalar32; let opkPk := P.x25519Base opkSk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    let base' := { st.base with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.base.opkEntries
        }
    return (.pkResp opkPk, { st with base := base' })
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then return (.noneResp, st)
    fgRunSendAuthPure P ddh useDh1 targetIdx S maxLen U (.sendOPK u i) u bundle m0 m1 st
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then return (.noneResp, st)
    fgRunSendAuthPure P ddh useDh1 targetIdx S maxLen U (.sendNoOPK u i) u bundle m0 m1 st
  | .recvOPK k j o msg =>
    let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
        msg.hdr.ekAPk }
    fgRunRecvOPKAuthPure S P ddh maxLen k j o msg { st with respRecs := rRec :: st.respRecs }
  | .recvNoOPK k j l msg =>
    let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
        msg.hdr.ekAPk }
    fgRunRecvNoOPKAuthPure S P ddh maxLen k j l msg { st with respRecs := rRec :: st.respRecs }
  | .roQuery secrets => fgRoQueryAuthPure P ddh maxLen secrets st
  | .roRootQuery rk dh => fgRoRootQueryAuthPure P ddh maxLen rk dh st
  | .revealDhSecrets => return (.noneResp, st)
  | .registerKey sk =>
    if sk.length != 32 then return (.noneResp, st)
    let pk := P.x25519Base sk; let powPk := P.pow8 pk
    let base' := { st.base with advKeys := (powPk, pk) :: st.base.advKeys }
    return (.pkResp pk, { st with base := base', advKeyPows := (sk, powPk) :: st.advKeyPows })
@[simp]
theorem simulateQ_gapDhFullImpl_fgAuthStep (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
  (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : AuthQuery
  S) (st : FgAuthSimState S) : simulateQ (gapDhFullImpl P ddh) (fgAuthStep useDh1 targetIdx
  targetSpkIdx S maxLen U V q st) =
      fgAuthStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st := by
  cases q with
  | initPrin u => unfold fgAuthStep fgAuthStepPure; dsimp only; split_ifs <;> simp
  | corruptIK u =>
    unfold fgAuthStep fgAuthStepPure; dsimp only
    cases st.base.principals.find? (fun (idx, _) => idx == u.val) <;> simp
  | genSPK u j =>
    unfold fgAuthStep fgAuthStepPure sampleKemKeyGen; dsimp only
    by_cases hAny : (st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [hAny]
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some p => rcases p with ⟨_, uEntry⟩; simp
  | genOPK u j o => unfold fgAuthStep fgAuthStepPure; dsimp only; split_ifs <;> simp
  | sendOPK u i bundle m0 m1 => unfold fgAuthStep fgAuthStepPure; dsimp only; split_ifs <;> simp
  | sendNoOPK u i bundle m0 m1 => unfold fgAuthStep fgAuthStepPure; dsimp only; split_ifs <;> simp
  | recvOPK k j o msg => unfold fgAuthStep fgAuthStepPure; simp
  | recvNoOPK k j l msg => unfold fgAuthStep fgAuthStepPure; simp
  | roQuery secrets => unfold fgAuthStep fgAuthStepPure; simp
  | roRootQuery rk dh => unfold fgAuthStep fgAuthStepPure; simp
  | revealDhSecrets => unfold fgAuthStep fgAuthStepPure; simp
  | registerKey sk => unfold fgAuthStep fgAuthStepPure; dsimp only; split_ifs <;> simp
theorem find?_ddh_3way_wins_of_mem (P : Primitives) (hWF : WellFormedPrimitivesδ P) (u v : Bytes) (L1
  L2 L3 : List Bytes) (h_mem : P.x25519 u (P.x25519Base v) ∈ L1 ∨ P.x25519 u (P.x25519Base v) ∈ L2 ∨
  P.x25519 u (P.x25519Base v) ∈ L3) : (P.pow8 (match L1.find? (fun z => P.isValidDhTriple
  (P.x25519Base u) (P.x25519Base v) z) with
      | some z => z
      | none =>
        match L2.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
        | some z => z
        | none =>
          match L3.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
          | some z => z
          | none => List.replicate 32 0) ==
      P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  cases h1 : L1.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
  | some z1 => exact ddh_eq_pow8_of_find?_some P hWF u v z1 _ h1
  | none =>
    cases h2 : L2.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
    | some z2 => exact ddh_eq_pow8_of_find?_some P hWF u v z2 _ h2
    | none =>
      cases h3 : L3.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
      | some z3 => exact ddh_eq_pow8_of_find?_some P hWF u v z3 _ h3
      | none =>
        exfalso; rcases h_mem with hm1 | hm2 | hm3
        · have hs := find?_ddh_isSome_of_mem P hWF u v _ hm1; rw [h1] at hs; cases hs
        · have hs := find?_ddh_isSome_of_mem P hWF u v _ hm2; rw [h2] at hs; cases hs
        · have hs := find?_ddh_isSome_of_mem P hWF u v _ hm3; rw [h3] at hs; cases hs
theorem pureExtractCdhFromAuthSimState_dh3_wins_of_mem (S : Setup) (P : Primitives) (hWF :
  WellFormedPrimitivesδ P) (maxLen : ℕ) (u v : Bytes) (st : FgAuthSimState S) (h_mem : P.x25519 u
  (P.x25519Base v) ∈ (st.advRoLog.take maxLen).map extractDh3 ∨ P.x25519 u (P.x25519Base v) ∈
  (st.base.sessions.take S.N_dh).map (initAuthDh3Cand P) ∨ P.x25519 u (P.x25519Base v) ∈
  (st.respRecs.take S.N_sess_tot).map (respAuthDh3Cand S P st.base.spkBundles)) : (P.pow8
  (pureExtractCdhFromAuthSimState S P P.isValidDhTriple false maxLen (P.x25519Base u) (P.x25519Base
  v) st) ==
      P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  unfold pureExtractCdhFromAuthSimState; simp only [Bool.false_eq_true, ↓reduceIte]
  exact find?_ddh_3way_wins_of_mem P hWF u v _ _ _ h_mem
/-! ## Simulation invariant `FgAuthSimInvDh3` -/
/-- Step-coupling invariant for `DH3 = CDH(ek_U*, spk_V*)` (`useDh1 = false`). -/
def FgAuthSimInvDh3 (S : Setup) (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ
  P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) : Prop :=
  FgAuthBaseRel false sIdx bIdx st.base hst.base ∧
  st.respRecs = hst.respRecs ∧
  FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys ∧
  FgCacheRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) b.q_total st.fgL st.rawRoCache
    hst.base.roCache ∧
  FgRootCacheRel P vSk b.q_total st.fgRootL hst.base.rootRoCache ∧
  st.fgL.length + rem ≤ b.q_total ∧
  st.fgRootL.length + rem ≤ b.q_total ∧
  hst.advRoLog.length + rem ≤ b.q_total ∧
  ValidAuthEcFg S P hst.base ∧
  spkTargetIsVAuth bIdx (P.x25519Base vSk) hst = true ∧
  (∀ kv ∈ hst.base.principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0) ∧
  (∀ kv ∈ hst.base.spkBundles, kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
    ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = vSk)) ∧
  (∀ kv ∈ hst.base.opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) ∧
  (∀ s ∈ hst.base.sessions, s.ekASk.length = 32 ∧ s.ephASk.length = 32 ∧ ((initSessionSlotIdx s.sid
    == sIdx) = true → s.ekASk = uSk))
theorem fgAuthSimInvDh3_empty (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (secb : Bool) : FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk b.q_total
      (AuthFgCutoffState.empty S secb) (FgAuthSimState.empty S secb) := by
  refine ⟨fgAuthBaseRel_empty S false sIdx bIdx secb, rfl, ⟨rfl, rfl, fun _ h => False.elim
    (List.not_mem_nil h)⟩, ⟨by simp [FgAuthSimState.empty], rfl, List.Forall₂.nil⟩, ⟨by simp
    [FgAuthSimState.empty], List.Forall₂.nil⟩, by simp [FgAuthSimState.empty],
    by simp [FgAuthSimState.empty],
    by simp [AuthFgCutoffState.empty], validAuthEcFg_empty S P secb, rfl, ?_, ?_, ?_, ?_⟩
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
theorem fgAuthSimInvDh3_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (maxLen sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32)
  (hvSk : vSk.length = 32) (_a : Bool) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (_hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk rem hst st) : 𝒟[(pure (badAuthFgDh3AtCore P maxLen sIdx bIdx hst.base
  hst.advRoLog hst.respRecs) : ProbComp Bool)] {true} ≤ 𝒟[(pure (P.pow8
  (pureExtractCdhFromAuthSimState S P P.isValidDhTriple false b.q_total (P.x25519Base uSk)
  (P.x25519Base vSk) st) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  by_cases hBad : badAuthFgDh3AtCore P maxLen sIdx bIdx hst.base hst.advRoLog hst.respRecs = true
  · rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, _, _, _, _, hAdvLen, _, _, _, hSpks, _, hSess⟩
    have hBad' := hBad; unfold badAuthFgDh3AtCore at hBad'
    cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => rw [hFS] at hBad'; cases hBad'
    | some s =>
      rw [hFS] at hBad'
      cases hFB : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
      | none => rw [hFB] at hBad'; cases hBad'
      | some kb =>
        rcases kb with ⟨k, bEntry⟩; rw [hFB] at hBad'
        dsimp only at hBad'; rcases Bool.and_eq_true_iff.mp hBad' with ⟨_, hAny⟩
        have hsMem : s ∈ hst.base.sessions := List.mem_of_find?_eq_some hFS
        have hsIdx : (initSessionSlotIdx s.sid == sIdx) = true :=
          List.find?_some (p := fun s : AuthInitiatorEntry S => initSessionSlotIdx s.sid == sIdx) hFS
        have hbMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFB
        have hbIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
          List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) => spkBundleFlatIdxVal S x.1
            == bIdx) hFB
        have hsEq : s.ekASk = uSk := (hSess s hsMem).2.2 hsIdx
        have hbSkEq : bEntry.spkSk = vSk := (hSpks (k, bEntry) hbMem).2.2 hbIdx
        have hbPkEq : bEntry.spkPk = P.x25519Base vSk := by
          rw [(hSpks (k, bEntry) hbMem).2.1, hbSkEq]
        rw [hsEq, hbPkEq] at hAny; have hSpkEq := hBaseRel.spkBundles_eq
        have hSessEq := hBaseRel.sessions_eq
        have hMemDisj : P.x25519 uSk (P.x25519Base vSk) ∈ (st.advRoLog.take b.q_total).map
          extractDh3 ∨ P.x25519 uSk (P.x25519Base vSk) ∈ (st.base.sessions.take S.N_dh).map
          (initAuthDh3Cand P) ∨ P.x25519 uSk (P.x25519Base vSk) ∈
              (st.respRecs.take S.N_sess_tot).map (respAuthDh3Cand S P st.base.spkBundles) := by
          rcases Bool.or_eq_true_iff.mp hAny with hAny12 | hAny3
          · rcases Bool.or_eq_true_iff.mp hAny12 with hAny1 | hAny2
            · rcases List.any_eq_true.mp hAny1 with ⟨sec, hSecTake, hSecEq⟩
              have hSecMem : sec ∈ hst.advRoLog := List.mem_of_mem_take hSecTake
              have hSecMemTake : sec ∈ st.advRoLog.take b.q_total := by
                rw [hAdvEq.1, List.take_of_length_le (by omega)]; exact hSecMem
              exact Or.inl (by rw [← beq_iff_eq.mp hSecEq]; exact List.mem_map_of_mem hSecMemTake)
            · rcases List.any_eq_true.mp hAny2 with ⟨s', hs'Take, hs'And⟩
              rcases Bool.and_eq_true_iff.mp hs'And with ⟨hs'Ne, hs'Eq⟩
              have hs'Mem : s' ∈ hst.base.sessions := List.mem_of_mem_take hs'Take
              have hs'Len : s'.ekASk.length = 32 := (hSess s' hs'Mem).1
              have hs'IdxF : (initSessionSlotIdx s'.sid == sIdx) = false := by
                simpa [bne] using hs'Ne
              refine Or.inr (Or.inl ?_); rw [hSessEq]
              unfold eraseAuthSessionsOptFg; rw [← List.map_take]
              have hCandEq : initAuthDh3Cand P (eraseAuthSessionEntryOptFg false sIdx s') =
                    P.x25519 uSk (P.x25519Base vSk) := by
                unfold initAuthDh3Cand eraseAuthSessionEntryOptFg
                simp [hs'IdxF, isEmpty_false_of_length_eq_32 hs'Len, beq_iff_eq.mp hs'Eq]
              rw [← hCandEq]; exact List.mem_map_of_mem (List.mem_map_of_mem hs'Take)
          · rcases List.any_eq_true.mp hAny3 with ⟨r, hrTake, hrEq⟩; refine Or.inr (Or.inr ?_)
            rw [hRespEq, hSpkEq, ← beq_iff_eq.mp hrEq]; exact List.mem_map_of_mem hrTake
        have hWin := pureExtractCdhFromAuthSimState_dh3_wins_of_mem S P hP.toWellFormedPrimitivesδ
          b.q_total uSk vSk st hMemDisj
        rw [hBad, hWin]
  · have hBadF : badAuthFgDh3AtCore P maxLen sIdx bIdx hst.base hst.advRoLog hst.respRecs = false :=
      Bool.eq_false_iff.mpr hBad
    rw [hBadF]; simp
/-! ## Step coupling for `FgAuthSimInvDh3` -/
theorem deadAuthDh3_eq_of_spk_sess {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes) {hst1
  hst2 : AuthFgCutoffState S} (hSpk : hst2.base.spkBundles = hst1.base.spkBundles) (hUsed :
  hst2.base.usedSendSessions = hst1.base.usedSendSessions) (hSess : hst2.base.sessions =
  hst1.base.sessions) :
    deadAuthDh3 P sIdx bIdx V hst2 = deadAuthDh3 P sIdx bIdx V hst1 := by
  unfold deadAuthDh3 spkTargetIsVAuth; rw [hSpk, hUsed, hSess]
theorem fgAuthStepCoupling_dh3_unchanged (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (hDead :
  deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP sIdx bIdx
  uSk vSk huSk hvSk (rem + 1) hst st) (r : AuthResponse) (k1 : AuthResponse × AuthFgCutoffState S →
  ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st',
  deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk
  vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[k1 (r, hst)] {true} ≤ 𝒟[k2 (r, st)] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  exact hCont r hst st hDead ⟨h1, h2, h3, h4, h5, by omega, by omega, by omega, h9, h10, h11, h12,
    h13, h14⟩
theorem fgAuthStepCoupling_dh3_unchanged_resp (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (rRec :
  AuthRespRecord) (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv :
  FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (r : AuthResponse) (k1 :
  AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S →
  ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
  FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2
  (r, st')] {true}) :
    𝒟[k1 (r, { hst with respRecs := rRec :: hst.respRecs })] {true} ≤
      𝒟[k2 (r, { st with respRecs := rRec :: st.respRecs })] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  exact hCont r _ _ hDead ⟨h1, by dsimp; rw [h2], h3, h4, h5, by dsimp; omega, by dsimp; omega,
    by dsimp; omega, h9, h10, h11, h12, h13, h14⟩
theorem couple_fgPatch_and_fgRootPatch (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (R :
  FgSlotReps P) {vSk : Bytes} (hvSk : vSk.length = 32) {maxLen : ℕ} {fgL : List FgPatchEntry}
  {rawRoCache : List (Bytes × DRKey)} {roCache : List (Bytes × DRKey)} {fgRootL : List FgRootEntry}
  {rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes))} {pos1 pos2 pos3 : FgPoS} {pos4? : Option
  FgPoS} {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes} {posRatchet : FgPoS} {dhRatchet :
  Bytes} (hCache : FgCacheRel R maxLen fgL rawRoCache roCache) (hRootCache : FgRootCacheRel P vSk
  maxLen fgRootL rootRoCache) (hFgLt : fgL.length < maxLen) (hRootLt : fgRootL.length < maxLen)
  (hTup : FgTupleRel R pos1 pos2 pos3 pos4? dh1 dh2 dh3 dh4? ss) (hPosR : FgRootPosRep P vSk
  posRatchet dhRatchet) (f1 : (DRKey × List (Bytes × DRKey)) → ((Bytes × Bytes) × List ((Bytes ×
  Bytes) × (Bytes × Bytes))) → ProbComp Bool) (f2 : (DRKey × List FgPatchEntry) → ((Bytes × Bytes) ×
  List FgRootEntry) → ProbComp Bool) (hf : ∀ drKey rk1 ck1_0 roCache' rootRoCache' fgL' fgRootL',
  FgCacheRel R maxLen fgL' rawRoCache roCache' → FgRootCacheRel P vSk maxLen fgRootL' rootRoCache' →
  fgL'.length ≤ fgL.length + 1 → fgRootL'.length ≤ fgRootL.length + 1 → 𝒟[f1 (drKey, roCache')
  ((rk1, ck1_0), rootRoCache')] {true} ≤ 𝒟[f2 (drKey, fgL') ((rk1, ck1_0), fgRootL')] {true}) :
  𝒟[evalHkdfOrRo true P roCache (buildSecrets dh1 dh2 dh3 dh4? ss) >>= fun dk => evalRootKdfOrRo
  true P rootRoCache dk.1.rootKey dhRatchet >>= fun rkc => f1 dk rkc] {true} ≤ 𝒟[fgPatchPure
  P.isValidDhTriple maxLen pos1 pos2 pos3 pos4? ss fgL >>= fun dkL => fgRootPatchPure
  P.isValidDhTriple maxLen dkL.1.rootKey posRatchet fgRootL >>= fun rkcL =>
            f2 dkL rkcL] {true} := by
  have hRootStep : ∀ drKey roCache' fgL', FgCacheRel R maxLen fgL' rawRoCache roCache' → fgL'.length
    ≤ fgL.length + 1 → 𝒟[evalRootKdfOrRo true P rootRoCache drKey.rootKey dhRatchet >>= fun rkc =>
    f1 (drKey, roCache') rkc] {true} ≤ 𝒟[fgRootPatchPure P.isValidDhTriple maxLen drKey.rootKey
    posRatchet fgRootL >>= fun rkcL =>
            f2 (drKey, fgL') rkcL] {true} := by
    intro drKey roCache' fgL' hC' hLen'
    rcases fgRootPatchPure_eq_or_sample P hP hvSk hRootCache hPosR with
      ⟨rk1, ck1_0, hREval, hRFg⟩ | ⟨hREval, hRFg, hRStep⟩
    · rw [hREval, hRFg]; simp only [pure_bind]
      exact hf drKey rk1 ck1_0 roCache' rootRoCache fgL' fgRootL hC' hRootCache hLen' (by omega)
    · rw [hREval, hRFg]; simp only [bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleBytes32 _ _ (fun rk1 _ => ?_)
      refine evalDist_bind_true_mono_of_support sampleBytes32 _ _ (fun ck1_0 _ => ?_)
      exact hf drKey rk1 ck1_0 roCache' _ fgL' _ hC' (hRStep rk1 ck1_0 hRootLt) hLen' (by simp)
  rcases fgPatchPure_eq_or_sample R hCache hTup with
    ⟨drKey, hEval, hFg⟩ | ⟨hEval, hFg, hStepCache⟩
  · rw [hEval, hFg]; simp only [pure_bind]; exact hRootStep drKey roCache fgL hCache (by omega)
  · rw [hEval, hFg]; simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun drKey _ => ?_)
    exact hRootStep drKey _ _ (hStepCache drKey hFgLt) (by simp)
theorem fgAuthStepCoupling_dh3_initPrin (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp
  Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P
  sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk
  rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl false sIdx
  bIdx (some uSk) (some vSk) S P (.initPrin u)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P
  P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := hBaseRel.principals_eq
  unfold pqxdhAuthFgPreImpl; dsimp only; rw [liftAuthFgHybrid_liftAuthBase_eq]
  unfold liftAuthFgBase fgPreAuthInitPrin fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, hPrinEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKA0 hSec0 => ?_)
    have hLen0 : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
    let entry : PrincipalEntry := {
      secIKA0 := secIKA0, ikAPk := P.x25519Base secIKA0,
      secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
    apply hCont (.initPrinResp entry.ikAPk entry.ikSignPk)
    · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · refine ⟨⟨hBaseRel.secb_eq, by dsimp [erasePrincipalsOptFg], hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩,
        hRespEq, hAdvEq, hCache, hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
        ⟨(validPrincipals_cons S u entry hst.base.principals hValidEc.1 hAny).1, hValidEc.2.1,
          hValidEc.2.2.1, hValidEc.2.2.2⟩,
        hSpkV, ?_, hSpks, hOpks, hSess⟩
      intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
      · exact ⟨hLen0, rfl⟩
      · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
theorem fgAuthStepCoupling_dh3_corruptIK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp
  Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P
  sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk
  rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl false sIdx
  bIdx (some uSk) (some vSk) S P (.corruptIK u)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P
  P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := hBaseRel.principals_eq
  change 𝒟[(liftAuthFgHybrid (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true
    S P (.corruptIK u)))).run hst >>= k1] {true} ≤ _
  rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinEq, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    simp only [StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
  | some p =>
    rcases p with ⟨_, entry⟩
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    apply hCont (.corrResp entry.secIKA0 entry.secIKAsign)
    · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · refine ⟨⟨hBaseRel.secb_eq, by dsimp [erasePrincipalsOptFg], hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩,
        hRespEq, hAdvEq, hCache, hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
        ⟨(validPrincipals_map_corrupted S P u.val hst.base.principals hValidEc.1).1, hValidEc.2.1,
          hValidEc.2.2.1, hValidEc.2.2.2⟩,
        hSpkV, ?_, hSpks, hOpks, hSess⟩
      intro kv hkv; rw [List.mem_map] at hkv
      rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩; have hPr := hPrins (idx, e) heMem
      by_cases hIdx : idx == u.val <;> simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq <;>
        (subst hEq; exact hPr)
theorem fgAuthStepCoupling_dh3_genOPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (rem : ℕ) (hst :
  AuthFgCutoffState S) (st : FgAuthSimState S) (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk)
  hst = false) (hInv : FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 :
  AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S →
  ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
  FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2
  (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.genOPK u j
  o)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genOPK u j o) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := hBaseRel.opkEntries_eq
  change 𝒟[(liftAuthFgHybrid (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true
    S P (.genOPK u j o)))).run hst >>= k1] {true} ≤ _
  rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpkEq, bind_assoc, pure_bind]
  cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun opkSk hOpk => ?_)
    have hLen : opkSk.length = 32 := length_of_mem_support_sampleScalar32 hOpk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false }
    apply hCont (.pkResp (P.x25519Base opkSk))
    · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · refine ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
        by dsimp, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩,
        hRespEq, hAdvEq, hCache, hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
        ⟨hValidEc.1, hValidEc.2.1, (validOpkEntries_cons S u j o oEntry hst.base.opkEntries
          hValidEc.2.2.1 hAny).1, hValidEc.2.2.2⟩,
        hSpkV, hPrins, hSpks, ?_, hSess⟩
      intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
      · exact ⟨hLen, rfl⟩
      · exact hOpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
theorem fgAuthStepCoupling_dh3_genSPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (u : Fin S.N_id) (j : Fin S.N_recv) (rem : ℕ) (hst : AuthFgCutoffState S) (st :
  FgAuthSimState S) (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv :
  FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse ×
  AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont
  : ∀ r hst' st', deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
  𝒟[(pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run hst >>= k1]
  {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := hBaseRel.principals_eq
  have hSpkAnyEq : st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) =
      hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) := by
    rw [hBaseRel.spkBundles_eq]; exact any_idx_eraseSpkBundlesFg S bIdx (u.val, j.val)
      hst.base.spkBundles
  unfold pqxdhAuthFgPreImpl; dsimp only; rw [liftAuthFgHybrid_liftAuthBase_eq]
  unfold liftAuthFgBase fgPreAuthGenSPK fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkAnyEq, hPrinEq, bind_assoc,
    pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    | some p =>
      rcases p with ⟨_, uEntry⟩; dsimp only; by_cases hTgt : (spkBundleFlatIdx S u j == bIdx) = true
      · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, evalDist_sampleScalar32_const]
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support (sampleKemKeyGen P) _ _ (fun ⟨pqspkPk, pqspkSk⟩
          _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        have hTgtVal : spkBundleFlatIdxVal S (u.val, j.val) = bIdx := by
          simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using beq_iff_eq.mp hTgt
        let bEntry : SpkBundleEntry := {
          spkSk := vSk, spkPk := P.x25519Base vSk,
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base vSk)) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        have hSpkV' : spkTargetIsVAuth bIdx (P.x25519Base vSk)
            { hst with base := { hst.base with spkBundles := ((u.val, j.val), bEntry) ::
                hst.base.spkBundles } } = true := by
          have h0 := hSpkV; unfold spkTargetIsVAuth at h0 ⊢; simp [hTgtVal, h0, bEntry]
        apply hCont (.bundleResp _)
        · unfold deadAuthDh3 at hDead ⊢; rw [hSpkV']; rw [hSpkV] at hDead; exact hDead
        · refine ⟨⟨hBaseRel.secb_eq, rfl, ?_, hBaseRel.opkEntries_eq, hBaseRel.sessions_eq,
            hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq,
            hBaseRel.usedKyberTriples_eq⟩, hRespEq, hAdvEq, hCache, hRootCache, by dsimp; omega,
            by dsimp; omega, by dsimp; omega,
            ⟨hValidEc.1, (validSpkBundles_cons S u j bEntry hst.base.spkBundles hValidEc.2.1
              hAny).1, hValidEc.2.2⟩,
            hSpkV', hPrins, ?_, hOpks, hSess⟩
          · dsimp only [eraseSpkBundlesFg, List.map]; rw [hBaseRel.spkBundles_eq]; unfold
              eraseSpkBundlesFg eraseSpkBundleEntryFg; simp; intro hNe; exact False.elim (hNe
              hTgtVal)
          · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hvSk, rfl, fun _ => rfl⟩
            · exact hSpks kv hMem
      · have hTgtF : (spkBundleFlatIdx S u j == bIdx) = false := Bool.eq_false_iff.mpr hTgt
        have hTgtValNe : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := by
          simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hTgtF
        simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
        refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun spkSk hSpk => ?_)
        have hLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpk
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support (sampleKemKeyGen P) _ _ (fun ⟨pqspkPk, pqspkSk⟩
          _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        let bEntry : SpkBundleEntry := {
          spkSk := spkSk, spkPk := P.x25519Base spkSk,
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base spkSk)) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        have hSpkV' : spkTargetIsVAuth bIdx (P.x25519Base vSk)
            { hst with base := { hst.base with spkBundles := ((u.val, j.val), bEntry) ::
                hst.base.spkBundles } } = true := by
          have h0 := hSpkV; unfold spkTargetIsVAuth at h0 ⊢; simp [hTgtValNe, h0]
        apply hCont (.bundleResp _)
        · unfold deadAuthDh3 at hDead ⊢; rw [hSpkV']; rw [hSpkV] at hDead; exact hDead
        · refine ⟨⟨hBaseRel.secb_eq, rfl, ?_, hBaseRel.opkEntries_eq, hBaseRel.sessions_eq,
            hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq,
            hBaseRel.usedKyberTriples_eq⟩, hRespEq, hAdvEq, hCache, hRootCache, by dsimp; omega,
            by dsimp; omega, by dsimp; omega,
            ⟨hValidEc.1, (validSpkBundles_cons S u j bEntry hst.base.spkBundles hValidEc.2.1
              hAny).1, hValidEc.2.2⟩,
            hSpkV', hPrins, ?_, hOpks, hSess⟩
          · dsimp only [eraseSpkBundlesFg, List.map]; rw [hBaseRel.spkBundles_eq]; unfold
              eraseSpkBundlesFg eraseSpkBundleEntryFg; simp; intro hEq; exact False.elim
              (beq_eq_false_iff_ne.mp hTgtValNe hEq)
          · intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hLen, rfl, fun h => by rw [hTgtValNe] at h; cases h⟩
            · exact hSpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
theorem fgAuthStepCoupling_dh3_roQuery (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (secrets : Bytes) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp
  Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P
  sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk
  rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl false sIdx
  bIdx (some uSk) (some vSk) S P (.roQuery secrets)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P
  P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roQuery secrets) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl pqxdhAuthHybridKoskImpl liftAuthBase pqxdhAuthImpl
    mkG3Hybrid fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    bind_assoc, pure_bind]
  rcases fgRoQueryAuthPure_eq_or_sample (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) hCache with
    ⟨dk, hEval, hFg⟩ | ⟨newRaw, newFgL, hEval, hFg, hStep⟩
  · rw [hEval, hFg]; simp only [pure_bind]; apply hCont (.drKeyResp dk)
    · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · exact ⟨hBaseRel, hRespEq, ⟨by dsimp; rw [hAdvEq.1], hAdvEq.2⟩, hCache, hRootCache,
        by dsimp; omega, by dsimp; omega, by dsimp [List.length_cons]; omega,
        hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  · rw [hEval, hFg]; simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun dk _ => ?_)
    rcases hStep dk (by omega) with ⟨hLenNew, hCacheNew⟩; apply hCont (.drKeyResp dk)
    · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · exact ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq,
        ⟨by dsimp; rw [hAdvEq.1], hAdvEq.2⟩, hCacheNew, hRootCache, by dsimp; omega,
        by dsimp; omega, by dsimp [List.length_cons]; omega,
        validAuthEcFg_of_fields_eq hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
theorem fgAuthStepCoupling_dh3_roRootQuery (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (rk dh : Bytes) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp
  Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P
  sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk
  rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl false sIdx
  bIdx (some uSk) (some vSk) S P (.roRootQuery rk dh)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P
  P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roRootQuery rk dh) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  change 𝒟[(liftAuthFgHybrid (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true true
    S P (.roRootQuery rk dh)))).run hst >>= k1] {true} ≤ _
  rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc,
    pure_bind]
  rcases fgRoRootQueryAuthPure_eq_or_sample hP hvSk hRootCache (rk := rk) (dh := dh) with
    ⟨rk1, ck1_0, hEval, hFg⟩ | ⟨hEval, hFg, hStep⟩
  · rw [hEval, hFg]; simp only [pure_bind]; apply hCont (.rootKdfResp rk1 ck1_0)
    · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · exact ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, by omega, by omega, by dsimp; omega,
        hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  · rw [hEval, hFg]; simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleBytes32 _ _ (fun rk1 _ => ?_)
    refine evalDist_bind_true_mono_of_support sampleBytes32 _ _ (fun ck1_0 _ => ?_)
    have hRootNew := hStep rk1 ck1_0 (by omega); apply hCont (.rootKdfResp rk1 ck1_0)
    · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
    · exact ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
        hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
        hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩, hRespEq,
        hAdvEq, hCache, hRootNew, by dsimp; omega, by dsimp [List.length_cons]; omega,
        by dsimp; omega, validAuthEcFg_of_fields_eq hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
/-! ### Handshake step coupling -/
theorem hdr_lengths_of_guard_false {b1 b2 b3 : Bool} {ik ek eph : Bytes} (h : (!(b1 && b2 && b3 &&
  (ik.length == 32) && (ek.length == 32) && (eph.length == 32))) = false) :
    ik.length = 32 ∧ ek.length = 32 ∧ eph.length = 32 := by
  simp only [Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at h; exact ⟨h.1.1.2, h.1.2, h.2⟩
theorem canon_ek_eph_of_guard_false {P : Primitives} {repOk : Bool} {ek eph : Bytes} (h : (!repOk ||
  !P.isCanonical ek || !P.isCanonical eph) = false) :
    onCurveKeyLocal P ek ∧ onCurveKeyLocal P eph := by
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h; exact ⟨Or.inl h.1.2, Or.inl h.2⟩
@[simp]
theorem evalAuthHybridRecvSchedule_g3_true {S : Setup} (P : Primitives) (hst : AuthHybridState S)
  (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes) (secrets : Bytes) (msg
  : PreKeyMsg) : evalAuthHybridRecvSchedule .g3 true P hst kEntry bEntry opkPk? secrets msg = (do
      let (drKey, roCache') ← evalHkdfOrRo true P hst.base.roCache secrets
      let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
      let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P hst.base.rootRoCache drKey.rootKey
          dhRatchet
      let mkSeed := P.chainKdfSeed ck1_0; let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => return none
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        match P.aeadDec deriveMessageKeys ad msg.aeadCt with
        | none => return none
        | some pt => return some (drKey, rk1, ck1_1, pt, roCache', rootRoCache')) := by
  unfold evalAuthHybridRecvSchedule
  dsimp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk, AuthHybridStage.idealCk,
    AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
    AuthHybridStage.idealUnmatchedRecvAead]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind, ite_self]
  apply bind_congr; rintro ⟨drKey, roCache'⟩; apply bind_congr; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
  cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none => rfl
  | some spqrPair => rcases spqrPair with ⟨_pqrStB, spqrSalt?⟩; rfl
theorem fgAuthStepCoupling_dh3_recvNoOPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) (rem :
  ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (hDead : deadAuthDh3 P sIdx bIdx
  (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk
  (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse ×
  FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P sIdx bIdx (P.x25519Base
  vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r,
  hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) (some
  vSk) S P (.recvNoOPK k j l msg)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple
  false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.recvNoOPK k j l msg) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hLengths := validAuthEc_lengths_le_fg S P hst.base hValidEc
  have hPrinEq : st.base.principals = hst.base.principals := hBaseRel.principals_eq
  have hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) =
    (hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))).map
        (fun (idx, b) => (idx, eraseSpkBundleEntryFg S bIdx idx b)) := by
    rw [hBaseRel.spkBundles_eq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val)
      hst.base.spkBundles
  have hUsedEq : st.base.usedRecvNoOPK = hst.base.usedRecvNoOPK := hBaseRel.usedRecvNoOPK_eq
  have hKybEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := hBaseRel.usedKyberTriples_eq
  have hTakePrin : hst.base.principals.take S.N_dh = hst.base.principals := List.take_of_length_le
    hLengths.1
  have hKoskEq : koskSenderOkTake S P hst.base.principals st.advKeyPows msg.hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk :=
    koskSenderOkTake_eq_koskSenderOk S P hst.base.principals st.advKeyPows hst.base.advKeys
      msg.hdr.ikAPk hLengths.1 hAdvEq.2.1
  let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
  unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl pqxdhAuthHybridKoskImpl mkG3Hybrid fgAuthStepPure
    fgRunRecvNoOPKAuthPure
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinEq, hSpkFind, hUsedEq, hKybEq,
    hKoskEq, bind_assoc, pure_bind]
  by_cases hHdr : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 && msg.hdr.ekAPk.length == 32 &&
    msg.ephAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st rRec
      hDead hInv0 .noneResp k1 k2 hCont
  · rcases hdr_lengths_of_guard_false (Bool.eq_false_iff.mpr hHdr) with ⟨hIkLen, hEkLen, hEphLen⟩
    simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
        rRec hDead hInv0 .noneResp k1 k2 hCont
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
          rRec hDead hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst
            st rRec hDead hInv0 .noneResp k1 k2 hCont
        | some pk =>
          rcases pk with ⟨k0, kEntry⟩; dsimp only
          rcases hPrins (k0, kEntry) (List.mem_of_find?_eq_some hFK) with ⟨hkSkLen, hkPk⟩
          cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
            exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst
              st rRec hDead hInv0 .noneResp k1 k2 hCont
          | some pb =>
            rcases pb with ⟨kb0, bEntry⟩; dsimp only [Option.map]
            rcases hSpks (kb0, bEntry) (List.mem_of_find?_eq_some hFB) with ⟨hbSkLen, hbPk, hbTgt⟩
            simp only [eraseSpkBundleEntryFg_pqspkSk]
            by_cases hRep : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
              msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical
              msg.ephAPk) = true
            · simp only [hRep, ↓reduceIte, StateT.run_pure, pure_bind]
              exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem
                hst st rRec hDead hInv0 .noneResp k1 k2 hCont
            · rcases canon_ek_eph_of_guard_false (Bool.eq_false_iff.mpr hRep) with ⟨hEkOnCurve,
                hEphOnCurve⟩
              simp only [hRep, Bool.false_eq_true, ↓reduceIte]
              cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none =>
                simp only [StateT.run_pure, pure_bind]
                exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem
                  hst st rRec hDead hInv0 .noneResp k1 k2 hCont
              | some ss =>
                have hIkOnCurve : onCurveKeyLocal P msg.hdr.ikAPk := onCurveKeyLocal_of_koskSenderOk
                  P hst.base.principals hst.base.advKeys msg.hdr.ikAPk hPrins hAdvEq.2.2 hKosk
                have hPos1 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                  (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ikAPk bEntry.spkPk)
                    (P.x25519 bEntry.spkSk msg.hdr.ikAPk) :=
                  computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                    msg.hdr.ikAPk ⟨hbSkLen, hbPk, hbTgt⟩ hIkOnCurve
                have hPos2 : FgPosLeftRep P uSk (computeTwoSideOrPairPosPure P [] kEntry.secIKA0
                  msg.hdr.ekAPk kEntry.ikAPk)
                    (P.x25519 kEntry.secIKA0 msg.hdr.ekAPk) := by
                  rw [computeTwoSideOrPairPosPure_nil_right_len32 P kEntry.secIKA0 msg.hdr.ekAPk
                    kEntry.ikAPk hkSkLen]
                  exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec2 _
                    (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                have hPos3 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                  (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ekAPk bEntry.spkPk)
                    (P.x25519 bEntry.spkSk msg.hdr.ekAPk) :=
                  computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                    msg.hdr.ekAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEkOnCurve
                have hPosR : FgRootPosRep P vSk (computeTwoSideOrPairPosPure P []
                  (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.ephAPk bEntry.spkPk)
                    (P.x25519 bEntry.spkSk msg.ephAPk) :=
                  fgRootPosRep_of_fgPosRightRep (computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep
                    P hP S bIdx vSk kb0 bEntry msg.ephAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEphOnCurve)
                have hTup : FgTupleRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk)
                  (computeTwoSideOrPairPosPure P [] (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk
                  msg.hdr.ikAPk bEntry.spkPk) (computeTwoSideOrPairPosPure P [] kEntry.secIKA0
                  msg.hdr.ekAPk kEntry.ikAPk) (computeTwoSideOrPairPosPure P []
                  (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ekAPk bEntry.spkPk) none
                  (P.x25519 bEntry.spkSk msg.hdr.ikAPk) (P.x25519 kEntry.secIKA0 msg.hdr.ekAPk)
                  (P.x25519 bEntry.spkSk msg.hdr.ekAPk)
                    none ss :=
                  ⟨hPos1, hPos2, hPos3, trivial, hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _ hDec⟩
                unfold fgFinishRecvAuthPure fgFinishRecvStep2AuthPure
                simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self,
                  evalAuthHybridRecvSchedule_g3_true, eraseSpkBundleEntryFg_spkPk, hPrinEq,
                  hTakePrin, bind_assoc, pure_bind]
                refine couple_fgPatch_and_fgRootPatch P hP (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk)
                  hvSk hCache hRootCache (by omega) (by omega) hTup hPosR _ _ (fun drKey rk1 ck1_0
                  roCache' rootRoCache' fgL' fgRootL' hCache' hRootCache' hFgLen' hRootLen' => ?_);
                  dsimp only
                cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                | none =>
                  simp only [StateT.run_pure, pure_bind]
                  exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk
                    rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                | some spqr =>
                  rcases spqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                  cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?) (firstMsgAD
                    msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                  | none =>
                    simp only [StateT.run_pure, pure_bind]
                    exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk
                      rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                  | some pt =>
                    dsimp only; simp only [pure_bind]
                    cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                    | some sp =>
                      rcases sp with ⟨_, senderEntry⟩
                      cases hCorr : senderEntry.corrupted <;> (
                        simp only [hCorr, Bool.not_true, Bool.not_false, Bool.false_eq_true,
                          ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                        apply hCont .recvHonestResp
                        · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
                        · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                            hBaseRel.opkEntries_eq, hBaseRel.sessions_eq,
                            hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
                            by dsimp; rw [hUsedEq], rfl⟩,
                            by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                            by dsimp; omega, by dsimp; omega, by dsimp; omega,
                            validAuthEcFg_of_fields_eq hValidEc, hSpkV, hPrins, hSpks, hOpks,
                              hSess⟩)
                    | none =>
                      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                      apply hCont (.recvUnfreshResp drKey rk1 (P.chainKdfNext ck1_0) pt)
                      · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
                      · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                          hBaseRel.opkEntries_eq, hBaseRel.sessions_eq,
                          hBaseRel.usedSendSessions_eq, hBaseRel.usedRecvOPK_eq,
                          by dsimp; rw [hUsedEq], rfl⟩,
                          by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                          by dsimp; omega, by dsimp; omega, by dsimp; omega,
                          validAuthEcFg_of_fields_eq hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
theorem fgAuthStepCoupling_dh3_recvOPK (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg) (rem : ℕ)
  (hst : AuthFgCutoffState S) (st : FgAuthSimState S) (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base
  vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
  (k1 : AuthResponse × AuthFgCutoffState S → ProbComp Bool) (k2 : AuthResponse × FgAuthSimState S →
  ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
  FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2
  (r, st')] {true}) : 𝒟[(pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.recvOPK k j
  o msg)).run hst >>= k1] {true} ≤ 𝒟[fgAuthStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.recvOPK k j o msg) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hLengths := validAuthEc_lengths_le_fg S P hst.base hValidEc
  have hPrinEq : st.base.principals = hst.base.principals := hBaseRel.principals_eq
  have hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) =
    (hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))).map
        (fun (idx, b) => (idx, eraseSpkBundleEntryFg S bIdx idx b)) := by
    rw [hBaseRel.spkBundles_eq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val)
      hst.base.spkBundles
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := hBaseRel.opkEntries_eq
  have hUsedEq : st.base.usedRecvOPK = hst.base.usedRecvOPK := hBaseRel.usedRecvOPK_eq
  have hKybEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys := hBaseRel.usedKyberTriples_eq
  have hTakePrin : hst.base.principals.take S.N_dh = hst.base.principals := List.take_of_length_le
    hLengths.1
  have hKoskEq : koskSenderOkTake S P hst.base.principals st.advKeyPows msg.hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk :=
    koskSenderOkTake_eq_koskSenderOk S P hst.base.principals st.advKeyPows hst.base.advKeys
      msg.hdr.ikAPk hLengths.1 hAdvEq.2.1
  let rRec : AuthRespRecord := { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk :=
      msg.hdr.ekAPk }
  unfold pqxdhAuthFgPreImpl pqxdhAuthFgImpl pqxdhAuthHybridKoskImpl mkG3Hybrid fgAuthStepPure
    fgRunRecvOPKAuthPure
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinEq, hSpkFind, hOpkEq, hUsedEq,
    hKybEq, hKoskEq, bind_assoc, pure_bind]
  by_cases hHdr : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
    msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
    msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st rRec
      hDead hInv0 .noneResp k1 k2 hCont
  · rcases hdr_lengths_of_guard_false (Bool.eq_false_iff.mpr hHdr) with ⟨hIkLen, hEkLen, hEphLen⟩
    simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : hst.base.usedRecvOPK.contains (k.val, j.val, o.val) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
        rRec hDead hInv0 .noneResp k1 k2 hCont
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
          rRec hDead hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          simp only [StateT.run_pure, pure_bind]
          exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst
            st rRec hDead hInv0 .noneResp k1 k2 hCont
        | some pk =>
          rcases pk with ⟨k0, kEntry⟩; dsimp only
          rcases hPrins (k0, kEntry) (List.mem_of_find?_eq_some hFK) with ⟨hkSkLen, hkPk⟩
          cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            dsimp only [Option.map]; simp only [StateT.run_pure, pure_bind]
            exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst
              st rRec hDead hInv0 .noneResp k1 k2 hCont
          | some pb =>
            rcases pb with ⟨kb0, bEntry⟩; dsimp only [Option.map]
            rcases hSpks (kb0, bEntry) (List.mem_of_find?_eq_some hFB) with ⟨hbSkLen, hbPk, hbTgt⟩
            cases hFO : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
              with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem
                hst st rRec hDead hInv0 .noneResp k1 k2 hCont
            | some po =>
              rcases po with ⟨ko0, oEntry⟩; dsimp only
              rcases hOpks (ko0, oEntry) (List.mem_of_find?_eq_some hFO) with ⟨hoSkLen, hoPk⟩
              by_cases hCons : oEntry.consumed = true
              · simp only [hCons, ↓reduceIte, StateT.run_pure, pure_bind]
                exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk rem
                  hst st rRec hDead hInv0 .noneResp k1 k2 hCont
              · simp only [hCons, Bool.false_eq_true, ↓reduceIte, eraseSpkBundleEntryFg_pqspkSk]
                by_cases hRep : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                  msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 || !P.isCanonical msg.hdr.ekAPk ||
                  !P.isCanonical msg.ephAPk) = true
                · simp only [hRep, ↓reduceIte, StateT.run_pure, pure_bind]
                  exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk
                    rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                · rcases canon_ek_eph_of_guard_false (Bool.eq_false_iff.mpr hRep) with ⟨hEkOnCurve,
                    hEphOnCurve⟩
                  simp only [hRep, Bool.false_eq_true, ↓reduceIte]
                  cases hDec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none =>
                    simp only [StateT.run_pure, pure_bind]
                    exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk hvSk
                      rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                  | some ss =>
                    have hIkOnCurve : onCurveKeyLocal P msg.hdr.ikAPk :=
                      onCurveKeyLocal_of_koskSenderOk P hst.base.principals hst.base.advKeys
                      msg.hdr.ikAPk hPrins hAdvEq.2.2 hKosk
                    have hPos1 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ikAPk bEntry.spkPk)
                        (P.x25519 bEntry.spkSk msg.hdr.ikAPk) :=
                      computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                        msg.hdr.ikAPk ⟨hbSkLen, hbPk, hbTgt⟩ hIkOnCurve
                    have hPos2 : FgPosLeftRep P uSk (computeTwoSideOrPairPosPure P [] kEntry.secIKA0
                      msg.hdr.ekAPk kEntry.ikAPk)
                        (P.x25519 kEntry.secIKA0 msg.hdr.ekAPk) := by
                      rw [computeTwoSideOrPairPosPure_nil_right_len32 P kEntry.secIKA0 msg.hdr.ekAPk
                        kEntry.ikAPk hkSkLen]
                      exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec2 _
                        (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                    have hPos3 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ekAPk bEntry.spkPk)
                        (P.x25519 bEntry.spkSk msg.hdr.ekAPk) :=
                      computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
                        msg.hdr.ekAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEkOnCurve
                    have hPos4 : FgOptLeftRep P uSk (some (computeTwoSideOrPairPosPure P []
                      oEntry.opkSk msg.hdr.ekAPk oEntry.opkPk))
                        (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) := by
                      dsimp only [FgOptLeftRep]
                      rw [computeTwoSideOrPairPosPure_nil_right_len32 P oEntry.opkSk msg.hdr.ekAPk
                        oEntry.opkPk hoSkLen]
                      exact ⟨hP.toWellFormedPrimitivesδ.x25519_len _ _, Or.inl rfl⟩
                    have hPosR : FgRootPosRep P vSk (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.ephAPk bEntry.spkPk)
                        (P.x25519 bEntry.spkSk msg.ephAPk) :=
                      fgRootPosRep_of_fgPosRightRep
                        (computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0
                        bEntry msg.ephAPk ⟨hbSkLen, hbPk, hbTgt⟩ hEphOnCurve)
                    have hTup : FgTupleRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk)
                      (computeTwoSideOrPairPosPure P [] (eraseSpkBundleEntryFg S bIdx kb0
                      bEntry).spkSk msg.hdr.ikAPk bEntry.spkPk) (computeTwoSideOrPairPosPure P []
                      kEntry.secIKA0 msg.hdr.ekAPk kEntry.ikAPk) (computeTwoSideOrPairPosPure P []
                      (eraseSpkBundleEntryFg S bIdx kb0 bEntry).spkSk msg.hdr.ekAPk bEntry.spkPk)
                      (some (computeTwoSideOrPairPosPure P [] oEntry.opkSk msg.hdr.ekAPk
                      oEntry.opkPk)) (P.x25519 bEntry.spkSk msg.hdr.ikAPk) (P.x25519 kEntry.secIKA0
                      msg.hdr.ekAPk) (P.x25519 bEntry.spkSk msg.hdr.ekAPk)
                        (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss :=
                      ⟨hPos1, hPos2, hPos3, hPos4, hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _
                        hDec⟩
                    have hValidOpk' : ValidOpkEntries S (hst.base.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else
                            (idx, e))) :=
                      (validOpkEntries_map_consumed S P (k.val, j.val, o.val) hst.base.opkEntries
                        hValidEc.2.2.1).1
                    have hOpks' : ∀ kv ∈ hst.base.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else
                          (idx, e)),
                        kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk := by
                      intro kv hkv; rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
                      have hO := hOpks (idx, e) heMem
                      by_cases hIdx : idx == (k.val, j.val, o.val) <;>
                        simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq <;>
                        (subst hEq; exact hO)
                    unfold fgFinishRecvAuthPure fgFinishRecvStep2AuthPure
                    simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
                      monadLift_self, evalAuthHybridRecvSchedule_g3_true,
                      eraseSpkBundleEntryFg_spkPk, hPrinEq, hTakePrin, bind_assoc, pure_bind]
                    refine couple_fgPatch_and_fgRootPatch P hP (FgSlotReps.ofDh3 P hP uSk vSk huSk
                      hvSk) hvSk hCache hRootCache (by omega) (by omega) hTup hPosR _ _ (fun drKey
                      rk1 ck1_0 roCache' rootRoCache' fgL' fgRootL' hCache' hRootCache' hFgLen'
                      hRootLen' => ?_); dsimp only
                    cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
                    | none =>
                      simp only [StateT.run_pure, pure_bind]
                      exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk
                        hvSk rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                    | some spqr =>
                      rcases spqr with ⟨_pqrStB, spqrSalt?⟩; dsimp only
                      cases P.aeadDec (P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?) (firstMsgAD
                        msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg) msg.aeadCt with
                      | none =>
                        simp only [StateT.run_pure, pure_bind]
                        exact fgAuthStepCoupling_dh3_unchanged_resp S b P hP sIdx bIdx uSk vSk huSk
                          hvSk rem hst st rRec hDead hInv0 .noneResp k1 k2 hCont
                      | some pt =>
                        dsimp only; simp only [pure_bind]
                        cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                        | some sp =>
                          rcases sp with ⟨_, senderEntry⟩
                          cases hCorr : senderEntry.corrupted <;> (
                            simp only [hCorr, Bool.not_true, Bool.not_false, Bool.false_eq_true,
                              ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
                              pure_bind]
                            apply hCont .recvHonestResp
                            · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
                            · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                                rfl, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
                                by dsimp; rw [hUsedEq], hBaseRel.usedRecvNoOPK_eq, rfl⟩,
                                by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                                by dsimp; omega, by dsimp; omega, by dsimp; omega,
                                ⟨hValidEc.1, hValidEc.2.1, hValidOpk', hValidEc.2.2.2⟩,
                                hSpkV, hPrins, hSpks, hOpks', hSess⟩)
                        | none =>
                          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
                          apply hCont (.recvUnfreshResp drKey rk1 (P.chainKdfNext ck1_0) pt)
                          · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
                          · exact ⟨⟨hBaseRel.secb_eq, rfl, hBaseRel.spkBundles_eq,
                              rfl, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
                              by dsimp; rw [hUsedEq], hBaseRel.usedRecvNoOPK_eq, rfl⟩,
                              by dsimp; rw [hRespEq], hAdvEq, hCache', hRootCache',
                              by dsimp; omega, by dsimp; omega, by dsimp; omega,
                              ⟨hValidEc.1, hValidEc.2.1, hValidOpk', hValidEc.2.2.2⟩,
                              hSpkV, hPrins, hSpks, hOpks', hSess⟩
theorem validAuthEcFg_cons_session {S : Setup} {P : Primitives} {st st' : AuthState S} {sid :
  SessionId S} {sessEntry : AuthInitiatorEntry S} (hV : ValidAuthEcFg S P st) (hSend : IsSendSessionId
  S sid) (hFresh : st.usedSendSessions.contains sid = false) (hSid : sessEntry.sid = sid) (hP :
  st'.principals = st.principals) (hS : st'.spkBundles = st.spkBundles) (hO : st'.opkEntries =
  st.opkEntries) (hSess : st'.sessions = sessEntry :: st.sessions) (hUsed : st'.usedSendSessions =
  sid :: st.usedSendSessions) :
    ValidAuthEcFg S P st' := by
  rcases hV with ⟨hVP, hVS, hVO, hVSess, hUsed1⟩
  have hFresh' : ((sessPksAuth S P st).map Prod.fst).any (fun s => s == sid) = false := by
    rw [← hUsed1]; revert hFresh; simp; rintro h x hx rfl; exact h hx
  have hCons := (validSessionIds_cons S sid ((sessPksAuth S P st).map Prod.fst) hSend hVSess
    hFresh').1
  refine ⟨by rw [hP]; exact hVP, by rw [hS]; exact hVS, by rw [hO]; exact hVO, ?_, ?_⟩
  · unfold sessPksAuth; rw [hSess, List.map_cons, List.map_cons, hSid]; exact hCons
  · unfold sessPksAuth; rw [hUsed, hSess, List.map_cons, List.map_cons, hSid, hUsed1]; rfl
theorem fgAuthStepCoupling_dh3_send (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (sid : SessionId S) (hSend : IsSendSessionId S sid) (u : Fin S.N_id) (bundle :
  PreKeyBundleInput) (m0 m1 : Bytes) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp
  Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P
  sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk
  rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) (hDeadCont : ∀ r hst', deadAuthDh3
  P sIdx bIdx (P.x25519Base vSk) hst' = true → 𝒟[k1 (r, hst')] {true} = 0) : 𝒟[(liftAuthFgHybrid
  (fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P sid u bundle m0 m1)).run hst >>= k1]
  {true} ≤ 𝒟[fgRunSendAuthPure P P.isValidDhTriple false sIdx S b.q_total
          (P.x25519Base uSk) sid u bundle m0 m1 st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
    hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  have hLengths := validAuthEc_lengths_le_fg S P hst.base hValidEc
  have hSecbEq : st.base.secb = hst.base.secb := hBaseRel.secb_eq
  have hPrinEq : st.base.principals = hst.base.principals := hBaseRel.principals_eq
  have hSpkEq : st.base.spkBundles = eraseSpkBundlesFg S bIdx hst.base.spkBundles :=
    hBaseRel.spkBundles_eq
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := hBaseRel.opkEntries_eq
  have hUsedEq : st.base.usedSendSessions = hst.base.usedSendSessions :=
    hBaseRel.usedSendSessions_eq
  have hTakePrin : hst.base.principals.take S.N_dh = hst.base.principals := List.take_of_length_le
    hLengths.1
  have hKoskEq : koskBundleOkTake S P hst.base.principals (eraseSpkBundlesFg S bIdx
    hst.base.spkBundles) hst.base.opkEntries st.advKeyPows bundle =
      koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries hst.base.advKeys
          bundle :=
    koskBundleOkTake_eraseSpk_eq S P bIdx hst.base.principals hst.base.spkBundles
      hst.base.opkEntries st.advKeyPows hst.base.advKeys bundle hLengths.1 hLengths.2.1
      hLengths.2.2.1 hAdvEq.2.1
  by_cases hLen : (m0.length != m1.length) = true
  · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLen, ↓reduceIte, StateT.run_pure,
      pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
  · have hLenF : (m0.length != m1.length) = false := Bool.eq_false_iff.mpr hLen
    by_cases hUsed : hst.base.usedSendSessions.contains sid = true
    · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsed,
        Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    · have hUsedF : hst.base.usedSendSessions.contains sid = false := Bool.eq_false_iff.mpr hUsed
      cases hFU : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsedF, hPrinEq,
          hFU, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      | some pu =>
        rcases pu with ⟨u0, uEntry⟩
        rcases hPrins (u0, uEntry) (List.mem_of_find?_eq_some hFU) with ⟨huSkLen, huPk⟩
        by_cases hUnf : (!(match findHonestPrincipal P hst.base.principals bundle.ikB with
            | some (_, pEntry) => !pEntry.corrupted | none => false) && (m0 != m1)) = true
        · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsedF,
            hPrinEq, hFU, hTakePrin, Bool.false_eq_true, ↓reduceIte, pure_bind]
          cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
          | none =>
            simp_all only [↓reduceIte, StateT.run_pure, pure_bind]; exact
              fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
              hInv0 .noneResp k1 k2 hCont
          | some fp =>
            rcases fp with ⟨_, pEntry⟩; simp_all only [↓reduceIte, StateT.run_pure, pure_bind];
              exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
              hDead hInv0 .noneResp k1 k2 hCont
        · have hUnfF := Bool.eq_false_iff.mpr hUnf
          by_cases hKosk : (!koskBundleOk P hst.base.principals hst.base.spkBundles
            hst.base.opkEntries hst.base.advKeys bundle) = true
          · unfold liftAuthFgHybrid fgPreAuthSendHybrid fgRunSendAuthPure mkG3Hybrid
            simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hLenF, hUsedEq, hUsedF,
              hPrinEq, hFU, hTakePrin, hSpkEq, hOpkEq, hKoskEq, hKosk, Bool.false_eq_true,
              ↓reduceIte, pure_bind]
            cases hFP : findHonestPrincipal P hst.base.principals bundle.ikB with
            | none =>
              simp_all only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]; exact
                fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some fp =>
              rcases fp with ⟨_, pEntry⟩; simp_all only [Bool.false_eq_true, ↓reduceIte,
                StateT.run_pure, pure_bind]; exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx
                bIdx uSk vSk huSk hvSk rem hst st hDead hInv0 .noneResp k1 k2 hCont
          · have hKoskF := Bool.eq_false_iff.mpr hKosk
            have hKoskT : koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
                hst.base.advKeys bundle = true := by
              simpa using hKoskF
            rw [fgPreAuthSendHybrid_run_eq_afterCoins false sIdx (some uSk) P sid u bundle m0 m1 hst
              hLenF hUsedF uEntry ⟨u0, hFU⟩ hUnfF hKoskT]
            unfold fgRunSendAuthPure sampleAuthSendCoins
            simp only [hLenF, hUsedEq, hUsedF, hPrinEq, hFU, hTakePrin, hUnfF, hSpkEq, hOpkEq,
              hKoskEq, hKoskF, hSecbEq, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, bind_assoc, pure_bind]
            by_cases hTgt : (initSessionSlotIdx sid == sIdx) = true
            · simp only [hTgt, ↓reduceIte, pure_bind, evalDist_sampleScalar32_const]
              refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
              refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ephASk hEph => ?_)
              have hEphLen : ephASk.length = 32 := length_of_mem_support_sampleScalar32 hEph
              refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun spqrCoins _ => ?_)
              unfold fgPreAuthSendAfterCoins; dsimp only
              by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig && P.sigVerify (resolveSigPk P
                hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [hSig, ↓reduceIte, pure_bind]
                exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst
                  st hDead hInv0 .noneResp k1 k2 hCont
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
                | none =>
                  simp only [pure_bind]
                  exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem
                    hst st hDead hInv0 .noneResp k1 k2 hCont
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩; dsimp only
                  by_cases hPowV : (P.pow8 bundle.spkB == P.pow8 (P.x25519Base vSk)) = true
                  · have hPowEq : P.pow8 bundle.spkB = P.pow8 (P.x25519Base vSk) := beq_iff_eq.mp
                      hPowV
                    have hBundleOnCurve := onCurveKeyLocal_of_koskBundleOk P hst.base.principals
                      hst.base.spkBundles hst.base.opkEntries hst.base.advKeys bundle hPrins hOpks
                      hAdvEq.2.2 hKosk
                    let spkSk := lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx hst.base.spkBundles)
                        st.advKeyPows bundle.spkB
                    have hPos1 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P uEntry.secIKA0
                      spkSk uEntry.ikAPk bundle.spkB)
                        (P.x25519 uEntry.secIKA0 bundle.spkB) := by
                      rw [computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 spkSk uEntry.ikAPk
                        bundle.spkB huSkLen]
                      exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec1 _
                        (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                    have hPos2 : FgPosLeftRep P uSk (computeTwoSideOrPairPosPure P [] []
                      (P.x25519Base uSk) bundle.ikB)
                        (P.x25519 uSk bundle.ikB) := by
                      rw [computeTwoSideOrPairPosPure_nil_nil]
                      exact fgPosLeftRep_mkPair_left P hP.toWellFormedPrimitivesδ uSk bundle.ikB
                        hBundleOnCurve.1
                    have hPos3 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P [] []
                      (P.x25519Base uSk) bundle.spkB)
                        (P.x25519 uSk bundle.spkB) := by
                      rw [computeTwoSideOrPairPosPure_nil_nil]
                      exact fgPosRightRep_mkPair_left_of_pow8 P hP.toWellFormedPrimitivesδ uSk vSk
                        bundle.spkB huSk hvSk (hP.pow8_base_len bundle.spkB vSk hPowEq) hPowEq
                    have hPos4 : FgOptLeftRep P uSk (computeOptPosPure P [] (P.x25519Base uSk)
                      (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk))))
                        (bundle.opkB?.map (fun (_, opkPk) => P.x25519 uSk opkPk)) :=
                      computeOptPosPure_nil_uSk_fgOptLeftRep P hP.toWellFormedPrimitivesδ uSk
                        bundle.opkB? hBundleOnCurve.2
                    have hPosR : FgRootPosRep P vSk (mkSecretPosPure P (P.x25519 ephASk
                      bundle.spkB))
                        (P.x25519 ephASk bundle.spkB) :=
                      fgRootPosRep_mkSecret P vSk _
                    have hTup : FgTupleRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk)
                      (computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB)
                      (computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.ikB)
                      (computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.spkB)
                      (computeOptPosPure P [] (P.x25519Base uSk) (bundle.opkB?.map (fun (_,
                      opkPk) => ([], opkPk)))) (P.x25519 uEntry.secIKA0 bundle.spkB) (P.x25519 uSk
                      bundle.ikB) (P.x25519 uSk bundle.spkB)
                        (bundle.opkB?.map (fun (_, opkPk) => P.x25519 uSk opkPk)) ss :=
                      ⟨hPos1, hPos2, hPos3, hPos4, (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _
                        hEnc).1⟩
                    simp only [bind_assoc]
                    refine couple_fgPatch_and_fgRootPatch P hP (FgSlotReps.ofDh3 P hP uSk vSk huSk
                      hvSk) hvSk hCache hRootCache (by omega) (by omega) hTup hPosR _ _ (fun drKey
                      rk1 ck1_0 roCache' rootRoCache' fgL' fgRootL' hCache' hRootCache' hFgLen'
                      hRootLen' => ?_); dsimp only
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none =>
                      simp only [pure_bind]
                      exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk
                        rem hst st hDead hInv0 .noneResp k1 k2 hCont
                    | some spqr =>
                      rcases spqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      simp only [pure_bind]
                      cases (findHonestPrincipal P hst.base.principals bundle.ikB).isSome <;> (
                        simp only [Bool.false_eq_true, ↓reduceIte]; apply hCont _
                        · unfold deadAuthDh3; unfold spkTargetIsVAuth at hSpkV ⊢; simp [hTgt,
                            hPowEq]
                        · refine ⟨⟨rfl, rfl, rfl,
                            rfl, ?_, rfl, hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq,
                              hBaseRel.usedKyberTriples_eq⟩,
                            hRespEq, hAdvEq, hCache', hRootCache',
                            by dsimp; omega, by dsimp; omega, by dsimp; omega,
                            validAuthEcFg_cons_session hValidEc hSend hUsedF rfl rfl rfl rfl rfl
                              rfl,
                            hSpkV, hPrins, hSpks, hOpks, ?_⟩
                          · dsimp only; rw [hBaseRel.sessions_eq]
                            unfold eraseAuthSessionsOptFg eraseAuthSessionEntryOptFg
                              checkBundleProvenanceExact
                            cases findHonestPrincipal P hst.base.principals bundle.ikB <;> simp
                              [beq_iff_eq.mp hTgt]
                          · intro s hs; rcases List.mem_cons.mp hs with rfl | hMem
                            · exact ⟨huSk, hEphLen, fun _ => rfl⟩
                            · exact hSess s hMem)
                  · have hPowNe : (P.pow8 bundle.spkB != P.pow8 (P.x25519Base vSk)) = true := by
                      simpa [bne] using hPowV
                    simp only [bind_assoc]; refine le_trans (le_of_eq ?_) zero_le
                    refine evalDist_bind_true_eq_zero_of_support _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
                    refine evalDist_bind_true_eq_zero_of_support _ _ (fun ⟨⟨rk1, ck1_0⟩,
                      rootRoCache'⟩ _ => ?_)
                    rcases Option.isSome_iff_exists.mp (hP.toWellFormedPrimitivesδ.spqrInitSend_some
                      drKey.pqrKey spqrCoins) with
                      ⟨⟨pqrStA, spqrSalt?, pqRatchetMsg⟩, hSpqr⟩
                    rw [hSpqr]; dsimp only; simp only [pure_bind]; apply hDeadCont
                    unfold deadAuthDh3; unfold spkTargetIsVAuth at hSpkV ⊢
                    simp [hSpkV, hTgt, hPowNe]
            · have hTgtF : (initSessionSlotIdx sid == sIdx) = false := Bool.eq_false_iff.mpr hTgt
              simp only [hTgtF, Bool.false_eq_true, ↓reduceIte]
              refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ekASk hEk => ?_)
              have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hEk
              refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
              refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ephASk hEph => ?_)
              have hEphLen : ephASk.length = 32 := length_of_mem_support_sampleScalar32 hEph
              refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun spqrCoins _ => ?_)
              unfold fgPreAuthSendAfterCoins; dsimp only
              by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig && P.sigVerify (resolveSigPk P
                hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [hSig, ↓reduceIte, pure_bind]
                exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst
                  st hDead hInv0 .noneResp k1 k2 hCont
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
                | none =>
                  simp only [pure_bind]
                  exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem
                    hst st hDead hInv0 .noneResp k1 k2 hCont
                | some sc =>
                  rcases sc with ⟨ss, kemCt⟩; dsimp only
                  let spkSk := lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx hst.base.spkBundles)
                      st.advKeyPows bundle.spkB
                  have hPos1 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P uEntry.secIKA0
                    spkSk uEntry.ikAPk bundle.spkB)
                      (P.x25519 uEntry.secIKA0 bundle.spkB) := by
                    rw [computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 spkSk uEntry.ikAPk
                      bundle.spkB huSkLen]
                    exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec1 _
                      (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                  have hPos2 : FgPosLeftRep P uSk (computeTwoSideOrPairPosPure P ekASk []
                    (P.x25519Base ekASk) bundle.ikB)
                      (P.x25519 ekASk bundle.ikB) := by
                    rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] (P.x25519Base ekASk)
                      bundle.ikB hEkLen]
                    exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec2 _
                      (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                  have hPos3 : FgPosRightRep P vSk (computeTwoSideOrPairPosPure P ekASk []
                    (P.x25519Base ekASk) bundle.spkB)
                      (P.x25519 ekASk bundle.spkB) := by
                    rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] (P.x25519Base ekASk)
                      bundle.spkB hEkLen]
                    exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec3 _
                      (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                  have hPos4 : FgOptLeftRep P uSk (computeOptPosPure P ekASk (P.x25519Base ekASk)
                    (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk))))
                      (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) :=
                    computeOptPosPure_left_len32_fgOptLeftRep P hP.toWellFormedPrimitivesδ uSk ekASk
                      (P.x25519Base ekASk) hEkLen bundle.opkB?
                  have hPosR : FgRootPosRep P vSk (mkSecretPosPure P (P.x25519 ephASk bundle.spkB))
                      (P.x25519 ephASk bundle.spkB) :=
                    fgRootPosRep_mkSecret P vSk _
                  have hTup : FgTupleRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk)
                    (computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB)
                    (computeTwoSideOrPairPosPure P ekASk [] (P.x25519Base ekASk) bundle.ikB)
                    (computeTwoSideOrPairPosPure P ekASk [] (P.x25519Base ekASk) bundle.spkB)
                    (computeOptPosPure P ekASk (P.x25519Base ekASk) (bundle.opkB?.map (fun (_,
                    opkPk) => ([], opkPk)))) (P.x25519 uEntry.secIKA0 bundle.spkB) (P.x25519 ekASk
                    bundle.ikB) (P.x25519 ekASk bundle.spkB)
                      (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss :=
                    ⟨hPos1, hPos2, hPos3, hPos4, (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _
                      hEnc).1⟩
                  simp only [bind_assoc]
                  refine couple_fgPatch_and_fgRootPatch P hP (FgSlotReps.ofDh3 P hP uSk vSk huSk
                    hvSk) hvSk hCache hRootCache (by omega) (by omega) hTup hPosR _ _ (fun drKey rk1
                    ck1_0 roCache' rootRoCache' fgL' fgRootL' hCache' hRootCache' hFgLen'
                    hRootLen' => ?_); dsimp only
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none =>
                    simp only [pure_bind]
                    exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem
                      hst st hDead hInv0 .noneResp k1 k2 hCont
                  | some spqr =>
                    rcases spqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    simp only [pure_bind]
                    cases (findHonestPrincipal P hst.base.principals bundle.ikB).isSome <;> (
                      simp only [Bool.false_eq_true, ↓reduceIte]; apply hCont _
                      · unfold deadAuthDh3 at hDead ⊢; unfold spkTargetIsVAuth at hDead ⊢
                        simp only [List.any_cons, List.find?_cons, hTgtF, Bool.false_or]
                        exact hDead
                      · refine ⟨⟨rfl, rfl, rfl,
                          rfl, ?_, rfl, hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq,
                            hBaseRel.usedKyberTriples_eq⟩,
                          hRespEq, hAdvEq, hCache', hRootCache',
                          by dsimp; omega, by dsimp; omega, by dsimp; omega,
                          validAuthEcFg_cons_session hValidEc hSend hUsedF rfl rfl rfl rfl rfl rfl,
                          hSpkV, hPrins, hSpks, hOpks, ?_⟩
                        · dsimp only; rw [hBaseRel.sessions_eq]
                          unfold eraseAuthSessionsOptFg eraseAuthSessionEntryOptFg
                            checkBundleProvenanceExact
                          cases findHonestPrincipal P hst.base.principals bundle.ikB <;> simp
                            [beq_eq_false_iff_ne.mp hTgtF]
                        · intro s hs; rcases List.mem_cons.mp hs with rfl | hMem
                          · exact ⟨hEkLen, hEphLen, fun h => by rw [hTgtF] at h; cases h⟩
                          · exact hSess s hMem)
theorem fgAuthStepCoupling_dh3 (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk :
  vSk.length = 32) (q : AuthQuery S) (rem : ℕ) (hst : AuthFgCutoffState S) (st : FgAuthSimState S)
  (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = false) (hInv : FgAuthSimInvDh3 S b P hP
  sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st) (k1 : AuthResponse × AuthFgCutoffState S → ProbComp
  Bool) (k2 : AuthResponse × FgAuthSimState S → ProbComp Bool) (hCont : ∀ r hst' st', deadAuthDh3 P
  sIdx bIdx (P.x25519Base vSk) hst' = false → FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk
  rem hst' st' → 𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) (hDeadCont : ∀ r hst', deadAuthDh3
  P sIdx bIdx (P.x25519Base vSk) hst' = true → 𝒟[k1 (r, hst')] {true} = 0) : 𝒟[(pqxdhAuthFgPreImpl
  false sIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true} ≤ 𝒟[(fgAuthSimImpl P
  P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hRhs : (fgAuthSimImpl P P.isValidDhTriple false sIdx bIdx S b.q_total (P.x25519Base uSk)
    (P.x25519Base vSk) q).run st = fgAuthStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q st := by
    unfold fgAuthSimImpl; simp
  rw [hRhs]; cases q with
  | initPrin u =>
    exact fgAuthStepCoupling_dh3_initPrin S b P hP sIdx bIdx uSk vSk huSk hvSk u rem hst st hDead
      hInv k1 k2 hCont
  | corruptIK u =>
    exact fgAuthStepCoupling_dh3_corruptIK S b P hP sIdx bIdx uSk vSk huSk hvSk u rem hst st hDead
      hInv k1 k2 hCont
  | genSPK u j =>
    exact fgAuthStepCoupling_dh3_genSPK S b P hP sIdx bIdx uSk vSk huSk hvSk u j rem hst st hDead
      hInv k1 k2 hCont
  | genOPK u j o =>
    exact fgAuthStepCoupling_dh3_genOPK S b P hP sIdx bIdx uSk vSk huSk hvSk u j o rem hst st hDead
      hInv k1 k2 hCont
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl fgAuthStepPure; cases hOpt : bundle.opkB?.isNone
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isNone then return .noneResp
          fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P (.sendOPK u i) u bundle m0 m1)).run
            hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P (.sendOPK u i) u
            bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq]; simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
      exact fgAuthStepCoupling_dh3_send S b P hP sIdx bIdx uSk vSk huSk hvSk (.sendOPK u i) trivial
        u bundle m0 m1 rem hst st hDead hInv k1 k2 hCont hDeadCont
    · unfold liftAuthFgHybrid mkG3Hybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpt, ↓reduceIte, StateT.run_pure,
        pure_bind]
      exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl fgAuthStepPure; cases hOpt : bundle.opkB?.isSome
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isSome then return .noneResp
          fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P (.sendNoOPK u i) u bundle m0
            m1)).run hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P (.sendNoOPK u i) u
            bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq]; simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
      exact fgAuthStepCoupling_dh3_send S b P hP sIdx bIdx uSk vSk huSk hvSk (.sendNoOPK u i)
        trivial u bundle m0 m1 rem hst st hDead hInv k1 k2 hCont hDeadCont
    · unfold liftAuthFgHybrid mkG3Hybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpt, ↓reduceIte, StateT.run_pure,
        pure_bind]
      exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv .noneResp k1 k2 hCont
  | recvOPK k j o msg =>
    exact fgAuthStepCoupling_dh3_recvOPK S b P hP sIdx bIdx uSk vSk huSk hvSk k j o msg rem hst st
      hDead hInv k1 k2 hCont
  | recvNoOPK k j l msg =>
    exact fgAuthStepCoupling_dh3_recvNoOPK S b P hP sIdx bIdx uSk vSk huSk hvSk k j l msg rem hst st
      hDead hInv k1 k2 hCont
  | roQuery secrets =>
    exact fgAuthStepCoupling_dh3_roQuery S b P hP sIdx bIdx uSk vSk huSk hvSk secrets rem hst st
      hDead hInv k1 k2 hCont
  | roRootQuery rk dh =>
    exact fgAuthStepCoupling_dh3_roRootQuery S b P hP sIdx bIdx uSk vSk huSk hvSk rk dh rem hst st
      hDead hInv k1 k2 hCont
  | revealDhSecrets =>
    have hInv0 := hInv
    change 𝒟[(liftAuthFgHybrid (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true
      true S P .revealDhSecrets))).run hst >>= k1] {true} ≤ _
    rw [liftAuthFgHybrid_liftAuthBase_eq]; unfold liftAuthFgBase pqxdhAuthImpl fgAuthStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv0 .noneResp k1 k2 hCont
  | registerKey sk =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseRel, hRespEq, hAdvEq, hCache, hRootCache, hFgLen, hRootLen, hAdvLen,
      hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
    change 𝒟[(liftAuthFgHybrid (do let h ← get; let _ := h.base; liftAuthBase (pqxdhAuthImpl true
      true S P (.registerKey sk)))).run hst >>= k1] {true} ≤ _
    rw [liftAuthFgHybrid_liftAuthBase_eq]
    unfold liftAuthFgBase pqxdhAuthImpl registerAdvKey fgAuthStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    by_cases hLen : (sk.length != 32) = true
    · simp only [hLen, ↓reduceIte, StateT.run_pure, pure_bind]
      exact fgAuthStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
        hInv0 .noneResp k1 k2 hCont
    · have hSkLen32 : sk.length = 32 := by
        cases hEq : (sk.length == 32)
        · simp [bne, hEq] at hLen
        · exact beq_iff_eq.mp hEq
      simp only [hLen, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind]
      apply hCont (.pkResp (P.x25519Base sk))
      · rw [deadAuthDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl rfl]; exact hDead
      · refine ⟨⟨hBaseRel.secb_eq, hBaseRel.principals_eq, hBaseRel.spkBundles_eq,
          hBaseRel.opkEntries_eq, hBaseRel.sessions_eq, hBaseRel.usedSendSessions_eq,
          hBaseRel.usedRecvOPK_eq, hBaseRel.usedRecvNoOPK_eq, hBaseRel.usedKyberTriples_eq⟩,
          hRespEq, ⟨hAdvEq.1, by dsimp; rw [hAdvEq.2.1]; rfl, ?_⟩,
          hCache, hRootCache, by dsimp; omega, by dsimp; omega, by dsimp; omega,
          validAuthEcFg_of_fields_eq hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩
        intro kv hkv; rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hSkLen32, rfl⟩
        · exact hAdvEq.2.2 kv hMem
end AuthDh3
/-! ## Per-index `DH3` `GapDH` bounds -/
theorem prob_badAuthFgDh3AtCore_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (AuthAdversary S) b) (sIdx : ℕ) (hsIdx : sIdx ∈
  Finset.range S.N_send_tot) (bIdx : ℕ) (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) : (𝒟[runAuthFgSim
  S P A.1 >>= fun x => pure (badAuthFgDh3AtCore P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog
  x.2.2.respRecs)] {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt false sIdx bIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx; unfold GapDH
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runAuthFgSim_eq_preSample_dh3 sIdx bIdx P hP A.1 (fun x => pure (badAuthFgDh3AtCore
    P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog x.2.2.respRecs))]
  rw [gapDhExp_fgAuthGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ AuthQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.auth_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead (deadAuthDh3 P sIdx bIdx (P.x25519Base vSk))
    (AuthDh3.FgAuthSimInvDh3 S b P hP sIdx bIdx uSk vSk huLen hvLen) (pqxdhAuthFgPreImpl false sIdx
    bIdx (some uSk) (some vSk) S P) (fgAuthSimImpl P P.isValidDhTriple false sIdx bIdx S b.q_total
    (P.x25519Base uSk) (P.x25519Base vSk)) (fun q s1 hD x hx =>
    pqxdhAuthFgPreImpl_preserves_deadAuthDh3 P sIdx bIdx hsLt uSk vSk q s1 hD x hx) (fun q rem s1 s2
    hDF hInv k1 k2 hCont hDeadCont => AuthDh3.fgAuthStepCoupling_dh3 S b P hP sIdx bIdx uSk vSk
    huLen hvLen q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont) (fun x => pure (badAuthFgDh3AtCore P
    b.q_ro sIdx bIdx x.2.base x.2.advRoLog x.2.respRecs)) (fun x => pure (P.pow8
    (pureExtractCdhFromAuthSimState S P P.isValidDhTriple false b.q_total (P.x25519Base uSk)
    (P.x25519Base vSk) x.2) == P.pow8 (P.x25519 uSk (P.x25519Base vSk)))) (fun a s1 hD =>
    by simp [badAuthFgDh3AtCore_eq_false_of_deadAuthDh3 P b.q_ro sIdx bIdx (P.x25519Base vSk) s1
    hD])
    (fun a rem s1 s2 hDF hInv => AuthDh3.fgAuthSimInvDh3_terminal_le S b P hP b.q_ro sIdx bIdx uSk
      vSk huLen hvLen a rem s1 s2 hDF hInv)
    A.1.run b.q_total hQb
    (AuthFgCutoffState.empty S secb)
    (FgAuthSimState.empty S secb)
    (AuthDh3.fgAuthSimInvDh3_empty S b P hP sIdx bIdx uSk vSk huLen hvLen secb)
/-- Bounds the per-index `DH3` bad-event probability in `runAuthFgSim` by `GapDH`. -/
theorem prob_badAuthFgDh3At_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives) (hP :
  CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (AuthAdversary S) b) (sIdx : ℕ) (hsIdx : sIdx ∈
  Finset.range S.N_send_tot) (bIdx : ℕ) (hbIdx : bIdx ∈ Finset.range S.N_spk_tot) : (𝒟[runAuthFgSim
  S P A.1 >>= fun x => pure (badAuthFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog
  x.2.2.respRecs)] {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt false sIdx bIdx S b A) := by
  refine le_trans ?_ (prob_badAuthFgDh3AtCore_le_gapDh S b P hP A sIdx hsIdx bIdx hbIdx)
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  refine evalDist_bind_true_mono_of_support (runAuthFgSim S P A.1) _ _ (fun x _ => ?_)
  by_cases h : badAuthFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog x.2.2.respRecs = true
  · rw [h, badAuthFgDh3At_imp_core P b.q_ro sIdx bIdx _ _ _ h]
  · simp [Bool.eq_false_iff.mpr h]
end Proofs.SignalPqxdh.Security
