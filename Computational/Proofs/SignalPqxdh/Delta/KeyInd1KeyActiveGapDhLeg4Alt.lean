/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1Key -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyCD -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre -- proof-setup: allow-public-import

/-!
# Active Creation-Order `GapDhWithSign` Leg `DH4` Bound

Proves `prob_badKeyIndFgDh4OrdAt_1Key_le_gapDhWithSign_active`, bounding the `DH4` bad event at
OPK-initiator creation ordinal `sOpkOrd` and OPK creation ordinal `opkOrd` by `GapDhWithSignReal`
against `fgKeyInd1KeyGapDhActiveAdvAtOpk`.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory (measure_ne_top)
open OracleSpec OracleComp
open SignalPqxdh (Setup Bytes PrincipalEntry SpkBundleEntry OpkEntry PreKeyBundleInput
  HandshakeHdr SessionId KeyIndQuery KeyIndResponse KeyIndState KeyIndInitiatorEntry
  KeyIndAdversary keyIndSpec QueryBudget BoundedAdv isGameQuery QueryBounded Primitives
  CryptoWellFormedPrimitivesδ GapDhWithSign gapDhWithSignExp GapDhWithSignReal activeOpkCount
  activeSendOpkCount sampleScalar32 sampleRandom64 encodeEC encodeKEM findHonestPrincipal
  resolveSigPk koskBundleOk pqxdhKeyIndImpl)
open SignalPqxdh.Security (opkSlotFlatIdx opkSlotFlatIdx_lt opkSlotFlatIdx_inj IsSendSessionId)
open SignalPqxdh.Security.FgGapDh (FgKeyIndSimState spkBundleFlatIdx initSessionSlotIdx)
open SignalPqxdh.Security.FgGapDh.Opk (opkFlatIdx noSpkIdx)
open SignalPqxdh.Security.FgGapDh1Key (FgKeyInd1KeySimState)
open Proofs.SignalPqxdh.Security.FgGapDh (KeyIndFgCutoffState
  initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt
  StateT_run_mk liftFgBase pqxdhKeyIndFgImpl pqxdhKeyIndFgPreImpl fgPreGenSPK fgPreInitiate
  mem_support_liftFgBase simulateQ_run_query_inl simulateQ_run_query_inr
  evalDist_bind_true_eq_zero_of_support evalDist_bind_true_mono_of_support
  length_of_mem_support_sampleScalar32 eraseSessionEntryFg eraseSessionsFg any_sid_eraseSessionsFg
  gapDhFullImpl koskBundleOkTake fgRunInitiatePure fgKeyIndStepPure
  simulateQ_gapDhFullImpl_embedPrim simulateQ_gapDhFullImpl_unifGdh
  simulateQ_gapDhFullImpl_primGdhQ_x25519Base simulateQ_gapDhFullImpl_primGdhQ_sigSign
  simulateQ_gapDhFullImpl_primGdhQ_sigVerify simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen
  simulateQ_gapDhFullImpl_primGdhQ_kemEncaps simulateQ_gapDhFullImpl_computeTwoSideOrPairPos
  simulateQ_gapDhFullImpl_computeOptPos simulateQ_gapDhFullImpl_fgPatch
  simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh
  simulateQ_primBaseImpl_koskBundleOkPrim simulateQ_primBaseImpl_resolveSigPkPrim
  simulateQ_primBaseImpl_lookupSpkSkPrim simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim
  simulateQ_primBaseImpl_checkBundleProvenancePrim simulateQ_primBaseImpl_findHonestPrincipalPrim
  simulateQ_gapDhFullImpl_fgKeyIndStep)
open Proofs.SignalPqxdh.Security.FgGapDh.Opk (eraseOpkEntryFg eraseOpkEntriesFg
  any_idx_eraseOpkEntriesFg eraseStateFgOpk spkBundleFlatIdx_ne_noSpkIdx opkTargetIsV deadDh4
  badKeyIndFgDh4At badKeyIndFgDh4At_eq_false_of_deadDh4 fgPreGenOPK
  fgSimInvDh4_terminal_le fgGenOPKPureOpk fgKeyIndStepPureOpk
  fgRunAcceptOPKPureOpk pureExtractCdh4FromAdvRoLog
  simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog)
open Proofs.SignalPqxdh.Security.FgGapDh1Key (runKeyIndFgSim1Key fgPreInitPrin1Key
  pqxdhKeyIndFgPreImpl1KeyOpk pqxdhKeyIndFgPreImpl1KeyOpk_preserves_deadDh4
  fgInitPrin1KeyPure fgGenSPK1KeyPure fgKeyInd1KeyStepPureOpk fgKeyInd1KeySimImplOpk
  gapDhWithSignFullImpl
  simulateQ_gapDhWithSignFullImpl_liftGdhToSign simulateQ_gapDhWithSignFullImpl_unifGdhSign
  simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base
  simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen
  simulateQ_gapDhWithSignFullImpl_sigChalQ simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep
  FgSimInvDh4_1Key fgSimInvDh4_1Key_empty fgStepCoupling_dh4_1Key)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (FgActiveParams
  activeParamsDh4 FgKeyInd1KeyActiveSimState optNatMatches optNatMatches_none liftSimStep1KeyActive
  fgInitPrin1KeyActiveGdh fgGenSpkActiveGdh fgGenSPK1KeyActiveGdh fgGenOPKActiveGdh
  fgRunInitiateActiveGdh fgInitiateActiveGdh fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveFinish
  fgKeyInd1KeyActiveRunWithParams fgKeyInd1KeyGapDhActiveAdvAtOpk)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre (opkSlotAtOrd
  isOpkInitSession opkSessions sessOpkSlotAtOrd badKeyIndFgDh4OrdAt ordLookup opkSlotAtOrd_eq
  sessOpkSlotAtOrd_eq ordLookup_of_ge ordLookup_cons_eq ordLookup_cons_of_lt
  ordLookup_mem_of_lt
  curOpkSlot curSessOpkSlot pqxdhKeyIndFgPreImpl1KeyOrdOpk
  evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh4)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLeg4Alt

public section
/-! ## Pure evaluation of `fgKeyInd1KeyGapDhActiveAdvAtOpk` -/

private noncomputable def fgGenSpkActivePure {S : Setup} (P : Primitives)
    (spkIdx : Nat) (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyIndSimState S) : ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  let isTargetSpk : Bool := st.base.spkBundles.length == spkIdx
  let spkSkRaw ← sampleScalar32; let spkPkRaw := P.x25519Base spkSkRaw
  let spkSk := if isTargetSpk then [] else spkSkRaw
  let spkPk := if isTargetSpk then V else spkPkRaw
  let rSpk ← sampleRandom64; let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
  let seedKem ← sampleRandom64; let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
  let rPq ← sampleRandom64; let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
  let bEntry : SpkBundleEntry :=
    { spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
      pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
  let base' := { st.base with spkBundles := ((u.val, j.val), bEntry) :: st.base.spkBundles }
  let bundleOut : PreKeyBundleInput :=
    { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig,
      opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
  return (.bundleResp bundleOut, { st with base := base' })

private noncomputable def fgGenSPK1KeyActivePure {S : Setup} (P : Primitives) (uSk : Bytes)
    (spkIdx : Nat) (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if optNatMatches stA.resolvedPrin? u.val then
    if stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, stA)
    let some (_, uEntry) := stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, stA)
    if stA.st1.sigBudget == 0 then return (.noneResp, stA)
    let isTargetSpk : Bool := stA.st1.sim.base.spkBundles.length == spkIdx
    let spkSkRaw ← sampleScalar32; let spkPkRaw := P.x25519Base spkSkRaw
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else spkPkRaw
    let rSpk ← sampleRandom64; let spkSig := P.sigSign uSk (encodeEC spkPk) rSpk
    let seedKem ← sampleRandom64; let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
    let rPq ← sampleRandom64; let pqspkSig := P.sigSign uSk (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry :=
      { spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
        pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
    let base' :=
      { stA.st1.sim.base with spkBundles := ((u.val, j.val), bEntry) :: stA.st1.sim.base.spkBundles }
    let bundleOut : PreKeyBundleInput :=
      { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig,
        opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
    return (.bundleResp bundleOut,
      { stA with st1 := { sim := { stA.st1.sim with base := base' }, sigBudget := stA.st1.sigBudget - 1 } })
  else
    let (resp, sim') ← fgGenSpkActivePure P spkIdx V u j stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })

private noncomputable def fgKeyInd1KeyActiveStepPureDh4 (ephOpkOrd opkOrd : Nat)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : Nat) (U V : Bytes) (q : KeyIndQuery S)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) :=
  match q with
  | .initPrin u => do
    let (resp, st1') ← fgInitPrin1KeyPure P false S.N_id U u stA.st1
    return (resp, { stA with st1 := st1' })
  | .genSPK u j =>
    fgGenSPK1KeyActivePure P uSk (maxLen + 1) V u j stA
  | .genOPK u j o => do
    let tOpk := if stA.st1.sim.base.opkEntries.length == opkOrd
      then opkFlatIdx S u j o else S.N_opk_tot
    let (resp, sim') ← fgGenOPKPureOpk P tOpk S V u j o stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then pure (.noneResp, stA)
    else do
      let tEph := if stA.sendOpkCnt == ephOpkOrd
        then initSessionSlotIdx (.sendOPK u i) else S.N_send_tot
      let (resp, sim') ← fgRunInitiatePure P ddh false tEph S maxLen U (.sendOPK u i) u bundle
        stA.st1.sim
      let cnt' := if stA.st1.sim.base.sessions.length < sim'.base.sessions.length
        then stA.sendOpkCnt + 1 else stA.sendOpkCnt
      return (resp, { stA with st1 := { stA.st1 with sim := sim' }, sendOpkCnt := cnt' })
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then pure (.noneResp, stA)
    else do
      let (resp, sim') ← fgRunInitiatePure P ddh false S.N_send_tot S maxLen U
        (.sendNoOPK u i) u bundle stA.st1.sim
      return (resp, { stA with st1 := { stA.st1 with sim := sim' } })
  | .acceptOPK k j o hdr => do
    let (resp, sim') ← fgRunAcceptOPKPureOpk P ddh S maxLen k j o hdr stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })
  | q_other => do
    let (resp, sim') ←
      fgKeyIndStepPure P ddh false ephOpkOrd (maxLen + 1) S maxLen U V q_other stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })

private noncomputable def fgKeyInd1KeyActiveSimImplDh4 (ephOpkOrd opkOrd : Nat)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : Nat) (U V : Bytes) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) :=
  fun q => StateT.mk (fgKeyInd1KeyActiveStepPureDh4 ephOpkOrd opkOrd P uSk ddh S maxLen U V q)

private theorem security_embedPrim_eq :
    @SignalPqxdh.Security.embedPrim = @SignalPqxdh.Security.FgGapDh.embedPrim := rfl

private theorem security_primQ_eq :
    @SignalPqxdh.Security.primQ = @SignalPqxdh.Security.FgGapDh.primQ := rfl

private theorem security_findMPrim_eq {α : Type}
    (p : α → OracleComp SignalPqxdh.PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.findMPrim p L = SignalPqxdh.Security.FgGapDh.findMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    unfold SignalPqxdh.Security.findMPrim SignalPqxdh.Security.FgGapDh.findMPrim
    rw [ih]

private theorem security_anyMPrim_eq {α : Type}
    (p : α → OracleComp SignalPqxdh.PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.anyMPrim p L = SignalPqxdh.Security.FgGapDh.anyMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    unfold SignalPqxdh.Security.anyMPrim SignalPqxdh.Security.FgGapDh.anyMPrim
    rw [ih]

private theorem security_findHonestPrincipalPrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    SignalPqxdh.Security.findHonestPrincipalPrim S principals ikB =
      SignalPqxdh.Security.FgGapDh.findHonestPrincipalPrim S principals ikB := by
  unfold SignalPqxdh.Security.findHonestPrincipalPrim
    SignalPqxdh.Security.FgGapDh.findHonestPrincipalPrim
  simp only [security_primQ_eq, security_findMPrim_eq]

private theorem security_isHonestUncorruptedPeerPrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    SignalPqxdh.Security.isHonestUncorruptedPeerPrim S principals ikB =
      SignalPqxdh.Security.FgGapDh.isHonestUncorruptedPeerPrim S principals ikB := by
  unfold SignalPqxdh.Security.isHonestUncorruptedPeerPrim
    SignalPqxdh.Security.FgGapDh.isHonestUncorruptedPeerPrim
  rw [security_findHonestPrincipalPrim_eq]
  rfl

private theorem security_checkBundleProvenancePrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (bundle : PreKeyBundleInput) :
    SignalPqxdh.Security.checkBundleProvenancePrim S principals spkBundles opkEntries bundle =
      SignalPqxdh.Security.FgGapDh.checkBundleProvenancePrim S principals spkBundles opkEntries
        bundle := by
  unfold SignalPqxdh.Security.checkBundleProvenancePrim
    SignalPqxdh.Security.FgGapDh.checkBundleProvenancePrim
  simp only [security_primQ_eq, security_findHonestPrincipalPrim_eq, security_anyMPrim_eq]
  rfl

private theorem simulateQ_gapDhFullImpl_fgGenSpkActiveGdh {S : Setup}
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (spkIdx : Nat) (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgGenSpkActiveGdh spkIdx V u j st) =
      fgGenSpkActivePure P spkIdx V u j st := by
  unfold fgGenSpkActiveGdh fgGenSpkActivePure
  dsimp only
  cases st.base.spkBundles.any (fun x => x.1 == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.base.principals.find? (fun x => x.1 == u.val) with
    | none => simp
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh,
        simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
        simulateQ_gapDhFullImpl_primGdhQ_sigSign,
        simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen,
        pure_bind, simulateQ_pure]
  · simp

private theorem initSessionSlotIdx_lt_of_isSendSessionId {S : Setup} (sid : SessionId S)
    (hSend : IsSendSessionId S sid) : initSessionSlotIdx sid < S.N_send_tot := by
  cases sid with
  | sendOPK u i => have := initSessionSlotIdx_sendOPK_lt u i; unfold Setup.N_send_tot; omega
  | sendNoOPK u i => exact initSessionSlotIdx_sendNoOPK_lt u i
  | recvOPK _ _ _ => cases hSend
  | recvNoOPK _ _ _ => cases hSend

private theorem simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh_dh4
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) (ephOpkOrd : Nat)
    (S : Setup) (maxLen : Nat) (U : Bytes) (hasOpk : Bool) (sid : SessionId S)
    (hSend : IsSendSessionId S sid) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (st : FgKeyIndSimState S) (sendOpkCnt : Nat) :
    simulateQ (gapDhFullImpl P ddh)
      (fgRunInitiateActiveGdh false true ephOpkOrd S maxLen U hasOpk sid u bundle st sendOpkCnt) =
      if (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome) then
        pure (.noneResp, (st, sendOpkCnt))
      else do
        let tEph := if hasOpk && (sendOpkCnt == ephOpkOrd) then initSessionSlotIdx sid else S.N_send_tot
        let (r, sim') ← fgRunInitiatePure P ddh false tEph S maxLen U sid u bundle st
        let cnt' := if hasOpk && decide (st.base.sessions.length < sim'.base.sessions.length)
          then sendOpkCnt + 1 else sendOpkCnt
        return (r, (sim', cnt')) := by
  unfold fgRunInitiateActiveGdh fgRunInitiatePure
  simp only [security_embedPrim_eq, security_findHonestPrincipalPrim_eq,
    security_isHonestUncorruptedPeerPrim_eq, security_checkBundleProvenancePrim_eq]
  have hGuard : (!(if hasOpk then bundle.opkB?.isSome else !bundle.opkB?.isSome)) =
      (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome) := by
    cases hasOpk <;> cases bundle.opkB? <;> rfl
  rw [hGuard]
  cases (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.base.sessions.any (fun e => e.sid == sid)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.base.principals.find? (fun x => x.1 == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, uEntry⟩; dsimp only
        simp only [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
          simulateQ_primBaseImpl_koskBundleOkPrim, pure_bind]
        by_cases hKosk : (!koskBundleOkTake S P st.base.principals st.base.spkBundles
          st.base.opkEntries st.advKeyPows bundle) = true
        · simp [hKosk]
        · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
            simulateQ_gapDhFullImpl_unifGdh, simulateQ_gapDhFullImpl_embedPrim,
            simulateQ_primBaseImpl_resolveSigPkPrim, simulateQ_gapDhFullImpl_primGdhQ_sigVerify,
            pure_bind, bind_assoc]
          congr 1; ext ekASkRaw; congr 1; ext kemCoins
          by_cases hv :
              (!(P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                  (encodeEC bundle.spkB) bundle.spkSig &&
                 P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                  (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
          · simp [hv]
          · simp only [hv, Bool.false_eq_true, ↓reduceIte,
              simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_kemEncaps, pure_bind]
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none => simp
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              have hEph : (if hasOpk then (!false) && (sendOpkCnt == ephOpkOrd)
                  else (!false) && ((!true) && (st.base.sessions.length == ephOpkOrd))) =
                  (!false && (initSessionSlotIdx sid ==
                    if hasOpk && (sendOpkCnt == ephOpkOrd) then initSessionSlotIdx sid
                    else S.N_send_tot)) := by
                have hNeN : (initSessionSlotIdx sid == S.N_send_tot) = false :=
                  beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_lt_of_isSendSessionId sid hSend))
                cases hasOpk <;> cases (sendOpkCnt == ephOpkOrd) <;> simp [hNeN]
              simp only [hEph, simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
                simulateQ_gapDhFullImpl_embedPrim, simulateQ_primBaseImpl_lookupSpkSkPrim,
                simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
                simulateQ_gapDhFullImpl_computeOptPos, simulateQ_gapDhFullImpl_fgPatch,
                simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh,
                simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim,
                simulateQ_primBaseImpl_checkBundleProvenancePrim,
                simulateQ_primBaseImpl_findHonestPrincipalPrim, pure_bind, bind_assoc]
              congr 1; ext ⟨drKeyReal, fgL'⟩; congr 1; ext drKeyRand
              cases findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;>
                cases hasOpk <;> simp
    · simp
  · simp

private theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveStep_dh4
    (ephOpkOrd opkOrd : Nat) (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (b : QueryBudget) (U V : Bytes)
    (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgKeyInd1KeyActiveStep (activeParamsDh4 b U V ephOpkOrd opkOrd) S b.q_total q stA) =
      fgKeyInd1KeyActiveStepPureDh4 ephOpkOrd opkOrd P uSk ddh S b.q_total U V q stA := by
  cases q with
  | initPrin u =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPureDh4
      fgInitPrin1KeyActiveGdh fgInitPrin1KeyPure activeParamsDh4
    dsimp only
    cases stA.st1.sim.base.principals.any (fun x => x.1 == u.val) <;>
      simp [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign,
        simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base, simulateQ_pure]
  | genSPK u j =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPureDh4
      fgGenSPK1KeyActiveGdh fgGenSPK1KeyActivePure activeParamsDh4
    dsimp only
    by_cases hPrin : optNatMatches stA.resolvedPrin? u.val = true
    · simp only [hPrin, ↓reduceIte]
      cases stA.st1.sim.base.spkBundles.any (fun x => x.1 == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases stA.st1.sim.base.principals.find? (fun x => x.1 == u.val) with
        | none => simp
        | some p =>
          rcases p with ⟨_, uEntry⟩; dsimp only
          by_cases hZero : (stA.st1.sigBudget == 0) = true
          · simp [hZero]
          · simp only [hZero, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
              simulateQ_gapDhWithSignFullImpl_unifGdhSign,
              simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base,
              simulateQ_gapDhWithSignFullImpl_sigChalQ,
              simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen,
              simulateQ_pure, pure_bind, bind_assoc]
      · simp
    · simp only [hPrin, Bool.false_eq_true, ↓reduceIte, liftSimStep1KeyActive,
        simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
        simulateQ_gapDhFullImpl_fgGenSpkActiveGdh, simulateQ_pure]
  | genOPK u j o =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPureDh4
      fgGenOPKActiveGdh fgGenOPKPureOpk activeParamsDh4
    dsimp only
    have hNeN : (opkFlatIdx S u j o == S.N_opk_tot) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (opkSlotFlatIdx_lt S u.isLt j.isLt o.isLt))
    cases stA.st1.sim.base.opkEntries.any (fun x => x.1 == (u.val, j.val, o.val)) <;>
      cases (stA.st1.sim.base.opkEntries.length == opkOrd) <;>
      simp [hNeN, simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign,
        simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base, simulateQ_pure]
  | initiateOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPureDh4 fgInitiateActiveGdh activeParamsDh4
    dsimp only
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh_dh4 P ddh ephOpkOrd S b.q_total U true
        (.sendOPK u i) trivial u bundle stA.st1.sim stA.sendOpkCnt]
    cases bundle.opkB?.isNone <;> simp
  | initiateNoOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPureDh4 fgInitiateActiveGdh activeParamsDh4
    dsimp only
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh_dh4 P ddh ephOpkOrd S b.q_total U false
        (.sendNoOPK u i) trivial u bundle stA.st1.sim stA.sendOpkCnt]
    cases bundle.opkB?.isSome <;> simp
  | acceptOPK k j o hdr =>
    simp [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPureDh4, activeParamsDh4,
      liftSimStep1KeyActive, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk]
  | _ =>
    simp only [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPureDh4, activeParamsDh4,
      liftSimStep1KeyActive, simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgKeyIndStep, simulateQ_pure]

private theorem gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAtOpk_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes) (ephOpkOrd opkOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdvAtOpk ephOpkOrd opkOrd S b A) =
    (do
      let u ← sampleScalar32; let v ← sampleScalar32
      let U := P.x25519Base u; let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgKeyInd1KeyActiveSimState.empty S b secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) +
        fgKeyInd1KeyActiveSimImplDh4 ephOpkOrd opkOrd P u ddh S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdh4FromAdvRoLog ddh b.q_total U V finalSt.st1.sim.advRoLog) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhActiveAdvAtOpk
  congr 1; funext u; congr 1; funext v
  let pa := activeParamsDh4 b (P.x25519Base u) (P.x25519Base v) ephOpkOrd opkOrd
  have hRun : simulateQ (gapDhWithSignFullImpl P u ddh) (fgKeyInd1KeyActiveRunWithParams pa S b A) =
      (do
        let secb ← $ᵗ Bool
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) +
          fgKeyInd1KeyActiveSimImplDh4 ephOpkOrd opkOrd P u ddh S b.q_total
            (P.x25519Base u) (P.x25519Base v)
        let (_, finalSt) ← (simulateQ impl A.1.run).run (FgKeyInd1KeyActiveSimState.empty S b secb)
        return pureExtractCdh4FromAdvRoLog ddh b.q_total (P.x25519Base u) (P.x25519Base v)
          finalSt.st1.sim.advRoLog) := by
    unfold fgKeyInd1KeyActiveRunWithParams; dsimp only
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign]
    congr 1; funext secb
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep P u ddh _ _
      (simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveStep_dh4 ephOpkOrd opkOrd P u ddh S b
        (P.x25519Base u) (P.x25519Base v))]
    congr 1; funext ⟨_, finalSt⟩
    simp [fgKeyInd1KeyActiveFinish, pa, activeParamsDh4,
      simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog]
  change (simulateQ (gapDhWithSignFullImpl P u ddh) (fgKeyInd1KeyActiveRunWithParams pa S b A) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [hRun]; simp only [bind_assoc, pure_bind]

/-! ## Invariant-guarded `simulateQ` combinators -/

private theorem evalDist_simulateQ_eq_zero_of_dead_preserved_inv
    {ι α St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (Inv : St → Prop) (Dead : St → Bool)
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hInvPres : ∀ q st, Inv st → ∀ x ∈ support ((impl q).run st), Inv x.2)
    (hPres : ∀ q st, Inv st → Dead st = true → ∀ x ∈ support ((impl q).run st), Dead x.2 = true)
    (obs : α × St → ProbComp Bool)
    (hObs : ∀ a st, Inv st → Dead st = true → 𝒟[obs (a, st)] {true} = 0)
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) (hInv : Inv st) (hDead : Dead st = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    𝒟[(simulateQ full oa).run st >>= obs] {true} = 0 := by
  intro full
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs a st hInv hDead
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full]
      rw [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun u _ => ih u st hInv hDead)
    · dsimp only [full]
      rw [simulateQ_run_query_inr, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun x hx =>
        ih x.1 x.2 (hInvPres gq st hInv x hx) (hPres gq st hInv hDead x hx))

private theorem evalDist_simulateQ_le_of_step_or_dead_inv
    {ι α St1 St2 : Type} {QSpec : OracleSpec.{0, 0} ι}
    (Inv1 : St1 → Prop) (Dead : St1 → Bool) (Rel : ℕ → St1 → St2 → Prop)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hInvPres : ∀ q s1, Inv1 s1 → ∀ x ∈ support ((impl1 q).run s1), Inv1 x.2)
    (hDeadPres : ∀ q s1, Inv1 s1 → Dead s1 = true →
      ∀ x ∈ support ((impl1 q).run s1), Dead x.2 = true)
    (hStep : ∀ (q : ι) (rem : ℕ) (s1 : St1) (s2 : St2),
      Inv1 s1 → Dead s1 = false → Rel (rem + 1) s1 s2 →
      ∀ (k1 : QSpec.Range q × St1 → ProbComp Bool)
        (k2 : QSpec.Range q × St2 → ProbComp Bool),
        (∀ r s1' s2', Inv1 s1' → Dead s1' = false → Rel rem s1' s2' →
          𝒟[k1 (r, s1')] {true} ≤ 𝒟[k2 (r, s2')] {true}) →
        (∀ r s1', Inv1 s1' → Dead s1' = true → 𝒟[k1 (r, s1')] {true} = 0) →
        𝒟[(impl1 q).run s1 >>= k1] {true} ≤ 𝒟[(impl2 q).run s2 >>= k2] {true})
    (obs1 : α × St1 → ProbComp Bool) (obs2 : α × St2 → ProbComp Bool)
    (hDeadObs : ∀ a s1, Inv1 s1 → Dead s1 = true → 𝒟[obs1 (a, s1)] {true} = 0)
    (hObs : ∀ a rem s1 s2, Inv1 s1 → Dead s1 = false → Rel rem s1 s2 →
      𝒟[obs1 (a, s1)] {true} ≤ 𝒟[obs2 (a, s2)] {true})
    (oa : OracleComp (unifSpec + QSpec) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ ι => isGameQuery q = true) rem)
    (s1 : St1) (s2 : St2) (hInv1 : Inv1 s1) (hRel : Rel rem s1 s2) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run s1 >>= obs1] {true} ≤
      𝒟[(simulateQ full2 oa).run s2 >>= obs2] {true} := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing rem s1 s2 with
  | pure a =>
    by_cases hD : Dead s1 = true
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind, hDeadObs a s1 hInv1 hD, zero_le]
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hObs a rem s1 s2 hInv1 (Bool.eq_false_iff.mpr hD) hRel
  | query_bind q mx ih =>
    by_cases hD : Dead s1 = true
    · rw [evalDist_simulateQ_eq_zero_of_dead_preserved_inv Inv1 Dead impl1 hInvPres hDeadPres obs1
        hDeadObs _ s1 hInv1 hD]
      exact zero_le
    · have hDF : Dead s1 = false := Bool.eq_false_iff.mpr hD
      rw [isQueryBoundP_query_bind_iff] at hQb
      rcases q with uq | gq
      · rcases hQb with ⟨_, hCont⟩
        simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at hCont
        dsimp only [full1, full2]
        rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
        exact evalDist_bind_true_mono_of_support _ _ _ (fun u _ =>
          ih u rem (hCont u) s1 s2 hInv1 hRel)
      · rcases hQb with ⟨hAbs | hPos, hCont⟩
        · exfalso; exact hAbs rfl
        · obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at hCont
          dsimp only [full1, full2]
          rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
          let k1' : QSpec.Range gq × St1 → ProbComp Bool :=
            open scoped Classical in
            fun x => if Inv1 x.2 then (simulateQ full1 (mx x.1)).run x.2 >>= obs1 else pure false
          have hLhsEq : 𝒟[(impl1 gq).run s1 >>= fun x =>
              (simulateQ full1 (mx x.1)).run x.2 >>= obs1] =
              𝒟[(impl1 gq).run s1 >>= k1'] :=
            OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => by
              simp only [k1', hInvPres gq s1 hInv1 x hx, ↓reduceIte])
          rw [hLhsEq]
          exact hStep gq rem' s1 s2 hInv1 hDF hRel
            k1'
            (fun x => (simulateQ full2 (mx x.1)).run x.2 >>= obs2)
            (fun r s1' s2' hI' _ hR => by
              simp only [k1', hI', ↓reduceIte]
              exact ih r rem' (hCont r) s1' s2' hI' hR)
            (fun r s1' hI' hD' => by
              simp only [k1', hI', ↓reduceIte]
              exact evalDist_simulateQ_eq_zero_of_dead_preserved_inv Inv1 Dead impl1 hInvPres
                hDeadPres obs1 hDeadObs (mx r) s1' hI' hD')

/-! ## State bounds and dynamic slot retargeting -/

private def MiniValid (S : Setup) (st : KeyIndState S) : Prop :=
  (∀ kv ∈ st.opkEntries, kv.1.1 < S.N_id ∧ kv.1.2.1 < S.N_recv ∧ kv.1.2.2 < S.N_opk) ∧
  (∀ s ∈ st.sessions, IsSendSessionId S s.sid)

private theorem miniValid_empty (S : Setup) (secb : Bool) :
    MiniValid S (KeyIndFgCutoffState.empty S secb).base :=
  ⟨fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩

private theorem miniValid_of_maps {S : Setup} {st1 st2 : KeyIndState S}
    (hV : MiniValid S st1)
    (hOpk : st2.opkEntries.map Prod.fst = st1.opkEntries.map Prod.fst)
    (hSess : st2.sessions.map KeyIndInitiatorEntry.sid =
      st1.sessions.map KeyIndInitiatorEntry.sid) :
    MiniValid S st2 := by
  refine ⟨fun kv hMem => ?_, fun s hMem => ?_⟩
  · have hFst : kv.1 ∈ st1.opkEntries.map Prod.fst := hOpk ▸ List.mem_map_of_mem hMem
    rcases List.mem_map.mp hFst with ⟨kv0, hMem0, hkEq⟩
    exact hkEq ▸ hV.1 kv0 hMem0
  · have hSid : s.sid ∈ st1.sessions.map KeyIndInitiatorEntry.sid :=
      hSess ▸ List.mem_map_of_mem hMem
    rcases List.mem_map.mp hSid with ⟨s0, hMem0, hsEq⟩
    exact hsEq ▸ hV.2 s0 hMem0

private theorem ordLookup_map_proj {α β γ : Type} (proj : β → γ) (f : α → β) (dflt : γ)
    (xs : List α) (ord : Nat) :
    ordLookup proj dflt (xs.map f) ord = ordLookup (proj ∘ f) dflt xs ord := by
  unfold ordLookup
  rw [← List.map_reverse, List.getElem?_map]
  cases xs.reverse[ord]? <;> rfl

private theorem opkSlotAtOrd_eq_of_map_fst {S : Setup} {st1 st2 : KeyIndState S} (opkOrd : Nat)
    (hOpk : st2.opkEntries.map Prod.fst = st1.opkEntries.map Prod.fst) :
    opkSlotAtOrd S st2 opkOrd = opkSlotAtOrd S st1 opkOrd := by
  have h1 : opkSlotAtOrd S st1 opkOrd =
      ordLookup (opkSlotFlatIdx S) S.N_opk_tot (st1.opkEntries.map Prod.fst) opkOrd := by
    rw [opkSlotAtOrd_eq]; exact (ordLookup_map_proj (opkSlotFlatIdx S) Prod.fst _ _ _).symm
  have h2 : opkSlotAtOrd S st2 opkOrd =
      ordLookup (opkSlotFlatIdx S) S.N_opk_tot (st2.opkEntries.map Prod.fst) opkOrd := by
    rw [opkSlotAtOrd_eq]; exact (ordLookup_map_proj (opkSlotFlatIdx S) Prod.fst _ _ _).symm
  rw [h2, hOpk, ← h1]

private theorem opkSessions_map_sid_of_map_sid {S : Setup} {st1 st2 : KeyIndState S}
    (hSess : st2.sessions.map KeyIndInitiatorEntry.sid =
      st1.sessions.map KeyIndInitiatorEntry.sid) :
    (opkSessions st2).map KeyIndInitiatorEntry.sid =
      (opkSessions st1).map KeyIndInitiatorEntry.sid := by
  have hf : ∀ (L : List (KeyIndInitiatorEntry S)),
      (L.filter isOpkInitSession).map KeyIndInitiatorEntry.sid =
        (L.map KeyIndInitiatorEntry.sid).filter (fun sid =>
          match sid with | .sendOPK _ _ => true | _ => false) := by
    intro L
    induction L with
    | nil => rfl
    | cons s ss ih =>
      rw [List.filter_cons, List.map_cons, List.filter_cons]
      have hs : isOpkInitSession s = match s.sid with | .sendOPK _ _ => true | _ => false := rfl
      rw [hs]
      cases h : s.sid <;> simp [h, ih]
  unfold opkSessions
  rw [hf st2.sessions, hf st1.sessions, hSess]

private theorem sessOpkSlotAtOrd_eq_of_map_sid {S : Setup} {st1 st2 : KeyIndState S} (sOpkOrd : Nat)
    (hSess : st2.sessions.map KeyIndInitiatorEntry.sid =
      st1.sessions.map KeyIndInitiatorEntry.sid) :
    sessOpkSlotAtOrd S st2 sOpkOrd = sessOpkSlotAtOrd S st1 sOpkOrd := by
  have hMap := opkSessions_map_sid_of_map_sid hSess
  have h1 : sessOpkSlotAtOrd S st1 sOpkOrd =
      ordLookup initSessionSlotIdx S.N_send_tot
        ((opkSessions st1).map KeyIndInitiatorEntry.sid) sOpkOrd := by
    rw [sessOpkSlotAtOrd_eq]
    exact (ordLookup_map_proj initSessionSlotIdx KeyIndInitiatorEntry.sid _ _ _).symm
  have h2 : sessOpkSlotAtOrd S st2 sOpkOrd =
      ordLookup initSessionSlotIdx S.N_send_tot
        ((opkSessions st2).map KeyIndInitiatorEntry.sid) sOpkOrd := by
    rw [sessOpkSlotAtOrd_eq]
    exact (ordLookup_map_proj initSessionSlotIdx KeyIndInitiatorEntry.sid _ _ _).symm
  rw [h2, hMap, ← h1]

private theorem opkSessions_length_eq_of_map_sid {S : Setup} {st1 st2 : KeyIndState S}
    (hSess : st2.sessions.map KeyIndInitiatorEntry.sid =
      st1.sessions.map KeyIndInitiatorEntry.sid) :
    (opkSessions st2).length = (opkSessions st1).length := by
  have hMap := congrArg List.length (opkSessions_map_sid_of_map_sid hSess)
  simpa using hMap

private theorem eraseOpkEntriesFg_of_absent {S : Setup} (o1 o2 : ℕ)
    (entries : List ((Nat × Nat × Nat) × OpkEntry))
    (h1 : ∀ kv ∈ entries, (opkSlotFlatIdx S kv.1 == o1) = false)
    (h2 : ∀ kv ∈ entries, (opkSlotFlatIdx S kv.1 == o2) = false) :
    eraseOpkEntriesFg S o1 entries = eraseOpkEntriesFg S o2 entries :=
  List.map_congr_left fun ⟨k, e⟩ hMem => by
    dsimp only [eraseOpkEntryFg]; simp [h1 (k, e) hMem, h2 (k, e) hMem]

private theorem eraseSessionsFg_of_absent {S : Setup} (s1 s2 : ℕ)
    (sessions : List (KeyIndInitiatorEntry S))
    (h1 : ∀ s ∈ sessions, (initSessionSlotIdx s.sid == s1) = false)
    (h2 : ∀ s ∈ sessions, (initSessionSlotIdx s.sid == s2) = false) :
    eraseSessionsFg s1 sessions = eraseSessionsFg s2 sessions :=
  List.map_congr_left fun s hMem => by unfold eraseSessionEntryFg; rw [h1 s hMem, h2 s hMem]

private theorem opkTargetIsV_of_absent {S : Setup} (oIdx : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S)
    (hAbs : ∀ kv ∈ hst.base.opkEntries, (opkSlotFlatIdx S kv.1 == oIdx) = false) :
    opkTargetIsV oIdx V hst = true :=
  List.all_eq_true.mpr fun kv hMem => by simp [hAbs kv hMem]

private def SlotRetargetOpk {S : Setup} (o1 o2 : ℕ) (st : KeyIndState S) : Prop :=
  o1 = o2 ∨ ((∀ kv ∈ st.opkEntries, (opkSlotFlatIdx S kv.1 == o1) = false) ∧
    (∀ kv ∈ st.opkEntries, (opkSlotFlatIdx S kv.1 == o2) = false))

private def SlotRetargetSess {S : Setup} (s1 s2 : ℕ) (st : KeyIndState S) : Prop :=
  s1 = s2 ∨ ((∀ s ∈ st.sessions, (initSessionSlotIdx s.sid == s1) = false) ∧
    (∀ s ∈ st.sessions, (initSessionSlotIdx s.sid == s2) = false))

private theorem deadDh4_retarget {S : Setup} (P : Primitives) (s1 s2 o1 o2 : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S) (hS : SlotRetargetSess s1 s2 hst.base)
    (hO : SlotRetargetOpk o1 o2 hst.base) :
    deadDh4 P s1 o1 V hst = deadDh4 P s2 o2 V hst := by
  have hOEq : opkTargetIsV o1 V hst = opkTargetIsV o2 V hst :=
    hO.elim (fun h => h ▸ rfl) fun ⟨h1, h2⟩ => by
      rw [opkTargetIsV_of_absent o1 V hst h1, opkTargetIsV_of_absent o2 V hst h2]
  have hSEq : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == s1) =
      hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == s2) :=
    hS.elim (fun h => h ▸ rfl) fun ⟨h1, h2⟩ => by
      rw [List.find?_eq_none.mpr fun s hs => by simp [h1 s hs],
        List.find?_eq_none.mpr fun s hs => by simp [h2 s hs]]
  unfold deadDh4; rw [hOEq, hSEq]

private theorem fgSimInvDh4_1Key_retarget {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {s1 s2 o1 o2 : ℕ} {uSk vSk : Bytes}
    {huSk : uSk.length = 32} {hvSk : vSk.length = 32} {rem : ℕ}
    {hst : KeyIndFgCutoffState S} {st : FgKeyInd1KeySimState S}
    (hInv : FgSimInvDh4_1Key S b P hP s1 o1 uSk vSk huSk hvSk rem hst st)
    (hS : SlotRetargetSess s1 s2 hst.base) (hO : SlotRetargetOpk o1 o2 hst.base) :
    FgSimInvDh4_1Key S b P hP s2 o2 uSk vSk huSk hvSk rem hst st := by
  rcases hInv with ⟨hBase, hAdv, hCache, hFgLen, hAdvLen, hVEc, hOV1, hPrin, hSpk, hOpk1, hSess1⟩
  refine ⟨?_, hAdv, hCache, hFgLen, hAdvLen, hVEc, ?_, hPrin, hSpk, ?_, ?_⟩
  · have hOEq : eraseOpkEntriesFg S o1 hst.base.opkEntries =
        eraseOpkEntriesFg S o2 hst.base.opkEntries :=
      hO.elim (fun h => h ▸ rfl) fun ⟨h1, h2⟩ => eraseOpkEntriesFg_of_absent o1 o2 _ h1 h2
    have hSEq : eraseSessionsFg s1 hst.base.sessions = eraseSessionsFg s2 hst.base.sessions :=
      hS.elim (fun h => h ▸ rfl) fun ⟨h1, h2⟩ => eraseSessionsFg_of_absent s1 s2 _ h1 h2
    rw [hBase]; unfold eraseStateFgOpk; rw [hOEq, hSEq]
  · exact hO.elim (fun h => h ▸ hOV1) fun ⟨_, h2⟩ => opkTargetIsV_of_absent o2 _ hst h2
  · intro kv hMem; refine ⟨(hOpk1 kv hMem).1, (hOpk1 kv hMem).2.1, fun hEq2 => ?_⟩
    exact hO.elim (fun h => (hOpk1 kv hMem).2.2 (h ▸ hEq2)) fun ⟨_, h2⟩ =>
      absurd (h2 kv hMem) (by simp [hEq2])
  · intro s hMem; refine ⟨(hSess1 s hMem).1, (hSess1 s hMem).2.1, fun hEq2 => ?_⟩
    exact hS.elim (fun h => (hSess1 s hMem).2.2 (h ▸ hEq2)) fun ⟨_, h2⟩ =>
      absurd (h2 s hMem) (by simp [hEq2])

private def stepOpkSlot {S : Setup} (opkOrd : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) : Nat :=
  if opkOrd < hst.base.opkEntries.length then opkSlotAtOrd S hst.base opkOrd
  else match q with
    | .genOPK u j o =>
      if !hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) &&
         (hst.base.opkEntries.length == opkOrd) then opkFlatIdx S u j o else S.N_opk_tot
    | _ => S.N_opk_tot

private def stepSessOpkSlot {S : Setup} (sOpkOrd : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) : Nat :=
  if sOpkOrd < (opkSessions hst.base).length then sessOpkSlotAtOrd S hst.base sOpkOrd
  else match q with
    | .initiateOPK u i bundle =>
      if bundle.opkB?.isSome && !hst.base.sessions.any (fun e => e.sid == .sendOPK u i) &&
         ((opkSessions hst.base).length == sOpkOrd) then initSessionSlotIdx (.sendOPK u i)
      else S.N_send_tot
    | _ => S.N_send_tot

private theorem opk_absent_N {S : Setup} {st : KeyIndState S} (hV : MiniValid S st) :
    ∀ kv ∈ st.opkEntries, (opkSlotFlatIdx S kv.1 == S.N_opk_tot) = false := fun kv hMem =>
  have hb := hV.1 kv hMem
  beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (opkSlotFlatIdx_lt S hb.1 hb.2.1 hb.2.2))

private theorem sess_absent_N {S : Setup} {st : KeyIndState S} (hV : MiniValid S st) :
    ∀ s ∈ st.sessions, (initSessionSlotIdx s.sid == S.N_send_tot) = false := fun s hMem =>
  beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_lt_of_isSendSessionId s.sid (hV.2 s hMem)))

private theorem opk_absent_of_fresh {S : Setup} {st : KeyIndState S} (hV : MiniValid S st)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hAny : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = false) :
    ∀ kv ∈ st.opkEntries, (opkSlotFlatIdx S kv.1 == opkFlatIdx S u j o) = false := fun kv hMem =>
  Bool.eq_false_iff.mpr fun hEq => by
    have hb := hV.1 kv hMem
    have hk := opkSlotFlatIdx_inj S hb.2.1 hb.2.2 j.isLt o.isLt (beq_iff_eq.mp hEq)
    exact Bool.false_ne_true (hAny.symm.trans (List.any_eq_true.mpr ⟨kv, hMem, beq_iff_eq.mpr hk⟩))

private theorem sess_absent_of_fresh {S : Setup} {st : KeyIndState S}
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (hAny : st.sessions.any (fun e => e.sid == sid) = false) :
    ∀ s ∈ st.sessions, (initSessionSlotIdx s.sid == initSessionSlotIdx sid) = false := fun s hMem =>
  Bool.eq_false_iff.mpr fun hEq => by
    have hSid := initSessionSlotIdx_inj_of_lt (beq_iff_eq.mp hEq)
      (initSessionSlotIdx_lt_of_isSendSessionId sid hSend)
    exact Bool.false_ne_true (hAny.symm.trans (List.any_eq_true.mpr ⟨s, hMem, beq_iff_eq.mpr hSid⟩))

private theorem stepOpkSlot_retarget_pre {S : Setup} (opkOrd : ℕ) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) (hV : MiniValid S hst.base) :
    SlotRetargetOpk (opkSlotAtOrd S hst.base opkOrd) (stepOpkSlot opkOrd q hst) hst.base := by
  by_cases hLt : opkOrd < hst.base.opkEntries.length
  · exact Or.inl (by simp [stepOpkSlot, hLt])
  · refine Or.inr ⟨?_, ?_⟩
    · rw [opkSlotAtOrd_eq, ordLookup_of_ge (Nat.le_of_not_lt hLt)]; exact opk_absent_N hV
    · unfold stepOpkSlot; simp only [hLt, ↓reduceIte]
      cases q with
      | genOPK u j o =>
        dsimp only; split_ifs with hC
        · exact opk_absent_of_fresh hV u j o (by simpa using (Bool.and_eq_true_iff.mp hC).1)
        · exact opk_absent_N hV
      | _ => exact opk_absent_N hV

private theorem stepSessOpkSlot_retarget_pre {S : Setup} (sOpkOrd : ℕ) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) (hV : MiniValid S hst.base) :
    SlotRetargetSess (sessOpkSlotAtOrd S hst.base sOpkOrd) (stepSessOpkSlot sOpkOrd q hst) hst.base := by
  by_cases hLt : sOpkOrd < (opkSessions hst.base).length
  · exact Or.inl (by simp [stepSessOpkSlot, hLt])
  · refine Or.inr ⟨?_, ?_⟩
    · rw [sessOpkSlotAtOrd_eq, ordLookup_of_ge (Nat.le_of_not_lt hLt)]; exact sess_absent_N hV
    · unfold stepSessOpkSlot; simp only [hLt, ↓reduceIte]
      cases q with
      | initiateOPK u i bundle =>
        dsimp only; split_ifs with hC
        · exact sess_absent_of_fresh (.sendOPK u i) trivial
            (by simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hC).1).2)
        · exact sess_absent_N hV
      | _ => exact sess_absent_N hV

private theorem genOPK_beq_stepOpkSlot {S : Setup} (opkOrd : ℕ)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hst : KeyIndFgCutoffState S) (hV : MiniValid S hst.base)
    (hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = false) :
    (opkFlatIdx S u j o == stepOpkSlot opkOrd (.genOPK u j o) hst) =
      (hst.base.opkEntries.length == opkOrd) := by
  unfold stepOpkSlot
  by_cases hLt : opkOrd < hst.base.opkEntries.length
  · simp only [hLt, ↓reduceIte, beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)]
    rcases ordLookup_mem_of_lt (proj := fun kv : (Nat × Nat × Nat) × OpkEntry =>
      opkSlotFlatIdx S kv.1) (dflt := S.N_opk_tot) hLt with ⟨kv, hMem, hk⟩
    rw [opkSlotAtOrd_eq, hk, BEq.comm]; exact opk_absent_of_fresh hV u j o hAny kv hMem
  · simp only [hLt, ↓reduceIte, hAny, Bool.not_false, Bool.true_and]
    have hNeN : (opkFlatIdx S u j o == S.N_opk_tot) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (opkSlotFlatIdx_lt S u.isLt j.isLt o.isLt))
    cases (hst.base.opkEntries.length == opkOrd) <;> simp [hNeN]

private theorem initiateOPK_beq_stepSessOpkSlot {S : Setup} (sOpkOrd : ℕ)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S) (_hV : MiniValid S hst.base) (hOpk : bundle.opkB?.isSome = true)
    (hAny : hst.base.sessions.any (fun e => e.sid == .sendOPK u i) = false) :
    (initSessionSlotIdx (.sendOPK u i) == stepSessOpkSlot sOpkOrd (.initiateOPK u i bundle) hst) =
      ((opkSessions hst.base).length == sOpkOrd) := by
  unfold stepSessOpkSlot
  by_cases hLt : sOpkOrd < (opkSessions hst.base).length
  · simp only [hLt, ↓reduceIte, beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)]
    rcases ordLookup_mem_of_lt (proj := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid)
      (dflt := S.N_send_tot) hLt with ⟨se, hMem, hs⟩
    rw [sessOpkSlotAtOrd_eq, hs, BEq.comm]
    exact sess_absent_of_fresh (.sendOPK u i) trivial hAny se (List.mem_of_mem_filter hMem)
  · simp only [hLt, ↓reduceIte, hOpk, hAny, Bool.not_false, Bool.true_and]
    have hNeN : (initSessionSlotIdx (.sendOPK u i) == S.N_send_tot) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_lt_of_isSendSessionId (.sendOPK u i) trivial))
    cases ((opkSessions hst.base).length == sOpkOrd) <;> simp [hNeN]

private theorem sendNoOPK_beq_stepSessOpkSlot {S : Setup} (sOpkOrd : ℕ)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S) :
    (initSessionSlotIdx (.sendNoOPK u i) == stepSessOpkSlot sOpkOrd (.initiateNoOPK u i bundle) hst) =
      false := by
  unfold stepSessOpkSlot
  by_cases hLt : sOpkOrd < (opkSessions hst.base).length
  · simp only [hLt, ↓reduceIte]
    rcases ordLookup_mem_of_lt (proj := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid)
      (dflt := S.N_send_tot) hLt with ⟨se, hMem, hs⟩
    rw [sessOpkSlotAtOrd_eq, hs]
    have hIsOpk : isOpkInitSession se = true := (List.mem_filter.mp hMem).2
    cases hSid : se.sid with
    | sendOPK u' i' =>
      exact Bool.eq_false_iff.mpr fun hEq => by
        have := initSessionSlotIdx_inj_of_lt (beq_iff_eq.mp hEq)
          (initSessionSlotIdx_lt_of_isSendSessionId (.sendOPK u' i') trivial)
        cases this
    | _ => simp [isOpkInitSession, hSid] at hIsOpk
  · simp only [hLt, ↓reduceIte]
    exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))

private theorem liftFgBase_run_congr {S : Setup} {m1 m2 : StateT (KeyIndState S) ProbComp KeyIndResponse}
    {hst : KeyIndFgCutoffState S} (h : m1.run hst.base = m2.run hst.base) :
    (liftFgBase m1).run hst = (liftFgBase m2).run hst := by
  unfold liftFgBase; dsimp only [StateT_run_mk]; rw [h]

private theorem pqxdhKeyIndFgPreImpl1KeyOrdOpk_run_eq {S : Setup} (sOpkOrd opkOrd : ℕ)
    (uSk vSk : Bytes) (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hV : MiniValid S hst.base) :
    (pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk) S P q).run hst =
      (pqxdhKeyIndFgPreImpl1KeyOpk (stepSessOpkSlot sOpkOrd q hst) (stepOpkSlot opkOrd q hst)
        (some uSk) (some vSk) S P q).run hst := by
  dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdOpk, StateT_run_mk]
  cases q with
  | genOPK u j o =>
    refine liftFgBase_run_congr ?_
    unfold fgPreGenOPK; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · have h1 : (opkFlatIdx S u j o == curOpkSlot opkOrd (.genOPK u j o) hst) =
          (hst.base.opkEntries.length == opkOrd) := by
        unfold curOpkSlot
        have hNeN : (opkFlatIdx S u j o == S.N_opk_tot) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (opkSlotFlatIdx_lt S u.isLt j.isLt o.isLt))
        cases (hst.base.opkEntries.length == opkOrd) <;> simp [hNeN]
      simp only [Bool.false_eq_true, ↓reduceIte, h1, genOPK_beq_stepOpkSlot opkOrd u j o hst hV hAny]
    · simp
  | initiateOPK u i bundle =>
    refine liftFgBase_run_congr ?_
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hOpt : bundle.opkB? with
    | none => simp
    | some _ =>
      have hSome : bundle.opkB?.isSome = true := by simp [hOpt]
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
      unfold fgPreInitiate; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      cases hAny : hst.base.sessions.any (fun e => e.sid == .sendOPK u i)
      · have h1 : (initSessionSlotIdx (.sendOPK u i) ==
            curSessOpkSlot sOpkOrd (.initiateOPK u i bundle) hst) =
            ((opkSessions hst.base).length == sOpkOrd) := by
          unfold curSessOpkSlot
          have hNeN : (initSessionSlotIdx (.sendOPK u i) == S.N_send_tot) = false :=
            beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_lt_of_isSendSessionId (.sendOPK u i) trivial))
          cases ((opkSessions hst.base).length == sOpkOrd) <;> simp [hNeN]
        simp only [Bool.false_eq_true, ↓reduceIte, h1,
          initiateOPK_beq_stepSessOpkSlot sOpkOrd u i bundle hst hV hSome hAny]
      · simp
  | initiateNoOPK u i bundle =>
    refine liftFgBase_run_congr ?_
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB? with
    | some _ => simp
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      unfold fgPreInitiate; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      have h1 : (initSessionSlotIdx (.sendNoOPK u i) ==
          curSessOpkSlot sOpkOrd (.initiateNoOPK u i bundle) hst) = false := by
        unfold curSessOpkSlot
        exact beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))
      simp only [h1, sendNoOPK_beq_stepSessOpkSlot sOpkOrd u i bundle hst]
  | _ => rfl

/-! ## Post-step retargeting and active step coupling -/

private def isInitiateOpkQuery {S : Setup} : KeyIndQuery S → Bool
  | .initiateOPK _ _ _ => true
  | _ => false

private theorem stepOpkSlot_eq_of_ne_genOPK {S : Setup} (opkOrd : Nat) (q : KeyIndQuery S)
    (hq : ∀ u j o, q ≠ .genOPK u j o) (hst : KeyIndFgCutoffState S) :
    stepOpkSlot opkOrd q hst = opkSlotAtOrd S hst.base opkOrd := by
  unfold stepOpkSlot
  split_ifs with hLt
  · rfl
  · rw [opkSlotAtOrd_eq, ordLookup_of_ge (Nat.le_of_not_lt hLt)]
    cases q with
    | genOPK u j o => exact absurd rfl (hq u j o)
    | _ => rfl

private theorem stepSessOpkSlot_eq_of_ne_initiateOPK {S : Setup} (sOpkOrd : Nat) (q : KeyIndQuery S)
    (hq : ∀ u i b, q ≠ .initiateOPK u i b) (hst : KeyIndFgCutoffState S) :
    stepSessOpkSlot sOpkOrd q hst = sessOpkSlotAtOrd S hst.base sOpkOrd := by
  unfold stepSessOpkSlot
  split_ifs with hLt
  · rfl
  · rw [sessOpkSlotAtOrd_eq, ordLookup_of_ge (Nat.le_of_not_lt hLt)]
    cases q with
    | initiateOPK u i b => exact absurd rfl (hq u i b)
    | _ => rfl

private theorem fgPreInitiate_step_shape {S : Setup} (useDh1 : Bool) (sIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S) (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((fgPreInitiate useDh1 sIdx optUsk S P sid u bundle).run st)) :
    x.2.spkBundles = st.spkBundles ∧ x.2.opkEntries = st.opkEntries ∧
    (x.2.sessions = st.sessions ∨
      (st.sessions.any (fun e => e.sid == sid) = false ∧
       ∃ se : KeyIndInitiatorEntry S, se.sid = sid ∧ x.2.sessions = se :: st.sessions)) := by
  unfold fgPreInitiate at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx; revert hx
  cases hAny : st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, Or.inl rfl⟩
    | some p =>
      rcases p with ⟨_, _⟩; dsimp only
      cases koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, Or.inl rfl⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind]
        rintro ⟨_, _, _, _, hb⟩; revert hb; split_ifs
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, Or.inl rfl⟩
        · cases P.kemEncaps bundle.pqspkB _ with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
            intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, Or.inl rfl⟩
          | some sc =>
            rcases sc with ⟨_, _⟩; dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
              bind_assoc, pure_bind, MonadAttach.mem_support_bind]
            rintro ⟨⟨_, _⟩, _, _, _, hb⟩; revert hb
            cases findHonestPrincipal P st.principals bundle.ikB <;>
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; rw [(Prod.mk.inj hEq).2]
              exact ⟨rfl, rfl, Or.inr ⟨trivial, _, rfl, rfl⟩⟩
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, Or.inl rfl⟩

private theorem mem_support_pqxdhKeyIndFgImpl_base {S : Setup} (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgImpl S P q).run hst)) :
    (x.1, x.2.base) ∈ support ((pqxdhKeyIndImpl true S P q).run hst.base) := by
  cases q <;>
  · unfold pqxdhKeyIndFgImpl at hx
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨r, b'⟩, hb, hEq⟩
    cases hEq
    exact hb

private theorem pqxdhKeyIndImpl_other_maps {S : Setup} (P : Primitives)
    (q : KeyIndQuery S)
    (hNoGenSpk : ∀ u j, q ≠ .genSPK u j)
    (hNoGenOpk : ∀ u j o, q ≠ .genOPK u j o)
    (hNoInitOpk : ∀ u i b, q ≠ .initiateOPK u i b)
    (hNoInitNoOpk : ∀ u i b, q ≠ .initiateNoOPK u i b)
    (st : KeyIndState S) (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((pqxdhKeyIndImpl true S P q).run st)) :
    x.2.spkBundles.length = st.spkBundles.length ∧
    x.2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst ∧
    x.2.sessions.map KeyIndInitiatorEntry.sid =
      st.sessions.map KeyIndInitiatorEntry.sid := by
  have hShape :=
    Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths.mem_support_pqxdhKeyIndImpl
      true S P q st x hx
  cases q with
  | genSPK u j => exact absurd rfl (hNoGenSpk u j)
  | genOPK u j o => exact absurd rfl (hNoGenOpk u j o)
  | initiateOPK u i b => exact absurd rfl (hNoInitOpk u i b)
  | initiateNoOPK u i b => exact absurd rfl (hNoInitNoOpk u i b)
  | initPrin u =>
    rcases hShape with hEq | ⟨_, _, _, hEq⟩ <;> (rw [hEq]; exact ⟨rfl, rfl, rfl⟩)
  | corruptIK u =>
    rcases hShape with hEq | hEq <;> (rw [hEq]; exact ⟨rfl, rfl, rfl⟩)
  | revealSpkSk u j =>
    rcases hShape with hEq | hEq
    · rw [hEq]; exact ⟨rfl, rfl, rfl⟩
    · rw [hEq]; exact ⟨by simp, rfl, rfl⟩
  | acceptOPK k j o hdr =>
    rcases hShape with ⟨_, hSpk, hSess, hOpkMap⟩
    refine ⟨by rw [hSpk], ?_, by rw [hSess]⟩
    have := congrArg (List.map Prod.fst) hOpkMap
    simpa only [List.map_map, Function.comp_def] using this
  | testSession sid | revealSessionKey sid =>
    rcases hShape with ⟨_, hSpk, hOpk, hSessMap⟩
    refine ⟨by rw [hSpk], by rw [hOpk], ?_⟩
    have := congrArg (List.map Prod.fst) hSessMap
    simpa only [List.map_map, Function.comp_def] using this
  | acceptNoOPK k j o hdr | roQuery _ | registerKey _ | revealDhSecrets =>
    rcases hShape with ⟨_, hSpk, hOpk, hSess⟩
    exact ⟨by rw [hSpk], by rw [hOpk], by rw [hSess]⟩

private theorem pqxdhKeyIndFgPreImpl1KeyOrdOpk_step_props {S : Setup} (sOpkOrd opkOrd : ℕ)
    (uSk vSk : Bytes) (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hV : MiniValid S hst.base)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    MiniValid S x.2.base ∧
    x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 ∧
    SlotRetargetOpk (stepOpkSlot opkOrd q hst) (opkSlotAtOrd S x.2.base opkOrd) x.2.base ∧
    SlotRetargetSess (stepSessOpkSlot sOpkOrd q hst) (sessOpkSlotAtOrd S x.2.base sOpkOrd) x.2.base ∧
    (opkSessions x.2.base).length =
      (if isInitiateOpkQuery q && decide (hst.base.sessions.length < x.2.base.sessions.length)
       then (opkSessions hst.base).length + 1 else (opkSessions hst.base).length) := by
  rw [pqxdhKeyIndFgPreImpl1KeyOrdOpk_run_eq sOpkOrd opkOrd uSk vSk P q hst hV] at hx
  have hUnchanged (hSpk : x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1)
      (hOpkMap : x.2.base.opkEntries.map Prod.fst = hst.base.opkEntries.map Prod.fst)
      (hSessMap : x.2.base.sessions.map KeyIndInitiatorEntry.sid =
        hst.base.sessions.map KeyIndInitiatorEntry.sid)
      (hNoGenOpk : ∀ u j o, q ≠ .genOPK u j o)
      (hNoInitOpk : ∀ u i b, q ≠ .initiateOPK u i b) :
      MiniValid S x.2.base ∧
      x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 ∧
      SlotRetargetOpk (stepOpkSlot opkOrd q hst) (opkSlotAtOrd S x.2.base opkOrd) x.2.base ∧
      SlotRetargetSess (stepSessOpkSlot sOpkOrd q hst) (sessOpkSlotAtOrd S x.2.base sOpkOrd) x.2.base ∧
      (opkSessions x.2.base).length =
        (if isInitiateOpkQuery q && decide (hst.base.sessions.length < x.2.base.sessions.length)
         then (opkSessions hst.base).length + 1 else (opkSessions hst.base).length) := by
    have hSessLen : x.2.base.sessions.length = hst.base.sessions.length := by
      have := congrArg List.length hSessMap; simpa using this
    refine ⟨miniValid_of_maps hV hOpkMap hSessMap, hSpk, ?_, ?_, ?_⟩
    · rw [stepOpkSlot_eq_of_ne_genOPK opkOrd q hNoGenOpk hst, opkSlotAtOrd_eq_of_map_fst opkOrd hOpkMap]
      exact Or.inl rfl
    · rw [stepSessOpkSlot_eq_of_ne_initiateOPK sOpkOrd q hNoInitOpk hst,
        sessOpkSlotAtOrd_eq_of_map_sid sOpkOrd hSessMap]
      exact Or.inl rfl
    · rw [opkSessions_length_eq_of_map_sid hSessMap, hSessLen]
      simp
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndFgPreImpl1KeyOpk fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩; have hB := (Prod.mk.inj hEq).2
      exact hUnchanged (by rw [hB]; dsimp; omega) (by rw [hB]) (by rw [hB])
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact hUnchanged (by rw [hB]; omega) (by rw [hB]) (by rw [hB])
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | genSPK u j =>
    unfold pqxdhKeyIndFgPreImpl1KeyOpk
      Proofs.SignalPqxdh.Security.FgGapDh.Opk.pqxdhKeyIndFgPreImplOpk
      pqxdhKeyIndFgPreImpl fgPreGenSPK at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
    cases hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact hUnchanged (by rw [hB]; omega) (by rw [hB]) (by rw [hB])
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      | some p =>
        rcases p with ⟨_, _⟩; dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff]
        rintro ⟨_, _, _, _, _, _, _, _, hEq⟩; have hB := (Prod.mk.inj hEq).2
        exact hUnchanged (by rw [hB]; simp) (by rw [hB]) (by rw [hB])
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact hUnchanged (by rw [hB]; omega) (by rw [hB]) (by rw [hB])
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  | genOPK u j o =>
    unfold pqxdhKeyIndFgPreImpl1KeyOpk
      Proofs.SignalPqxdh.Security.FgGapDh.Opk.pqxdhKeyIndFgPreImplOpk fgPreGenOPK at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
    cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩; have hB := (Prod.mk.inj hEq).2
      refine ⟨⟨?_, by rw [hB]; exact hV.2⟩, by rw [hB]; dsimp; omega, ?_, ?_, ?_⟩
      · intro kv hMem; rw [hB] at hMem
        rcases List.mem_cons.mp hMem with rfl | hOld
        · exact ⟨u.isLt, j.isLt, o.isLt⟩
        · exact hV.1 kv hOld
      · refine Or.inl ?_
        unfold stepOpkSlot
        by_cases hLt : opkOrd < hst.base.opkEntries.length
        · simp only [hLt, ↓reduceIte, opkSlotAtOrd_eq, hB, ordLookup_cons_of_lt _ _ _ hLt]
        · simp only [hLt, ↓reduceIte, hAny, Bool.not_false, Bool.true_and]
          by_cases hEqOrd : hst.base.opkEntries.length = opkOrd
          · subst hEqOrd; simp only [beq_self_eq_true, ↓reduceIte]
            rw [opkSlotAtOrd_eq, hB]; dsimp only
            rw [ordLookup_cons_eq]; rfl
          · have hGt : hst.base.opkEntries.length + 1 ≤ opkOrd := by omega
            simp only [beq_eq_false_iff_ne.mpr hEqOrd, Bool.false_eq_true, ↓reduceIte]
            rw [opkSlotAtOrd_eq, hB]; dsimp only
            rw [ordLookup_of_ge (by simpa using hGt)]
      · rw [stepSessOpkSlot_eq_of_ne_initiateOPK sOpkOrd _ (fun _ _ _ h => by cases h) hst,
          sessOpkSlotAtOrd_eq_of_map_sid (st1 := hst.base) (st2 := x.2.base) sOpkOrd (by rw [hB])]
        exact Or.inl rfl
      · rw [opkSessions_length_eq_of_map_sid (st1 := hst.base) (st2 := x.2.base) (by rw [hB])]
        have hSL : x.2.base.sessions.length = hst.base.sessions.length := by rw [hB]
        simp [isInitiateOpkQuery, hSL]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      refine ⟨by rw [hB]; exact hV, by rw [hB]; omega, ?_, ?_, ?_⟩
      · refine Or.inl ?_
        unfold stepOpkSlot
        by_cases hLt : opkOrd < hst.base.opkEntries.length
        · simp only [hLt, ↓reduceIte, hB]
        · simp only [hLt, ↓reduceIte, hAny, Bool.not_true, Bool.false_and, Bool.false_eq_true]
          rw [hB, opkSlotAtOrd_eq, ordLookup_of_ge (Nat.le_of_not_lt hLt)]
      · rw [stepSessOpkSlot_eq_of_ne_initiateOPK sOpkOrd _ (fun _ _ _ h => by cases h) hst,
          sessOpkSlotAtOrd_eq_of_map_sid (st1 := hst.base) (st2 := x.2.base) sOpkOrd (by rw [hB])]
        exact Or.inl rfl
      · rw [opkSessions_length_eq_of_map_sid (st1 := hst.base) (st2 := x.2.base) (by rw [hB])]
        have hSL : x.2.base.sessions.length = hst.base.sessions.length := by rw [hB]
        simp [isInitiateOpkQuery, hSL]
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl1KeyOpk
      Proofs.SignalPqxdh.Security.FgGapDh.Opk.pqxdhKeyIndFgPreImplOpk
      pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    cases hOpt : bundle.opkB? with
    | none =>
      simp only [hOpt, Option.isNone_none, ↓reduceIte, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hb
      have hB := (Prod.mk.inj hb).2
      refine ⟨by rw [hB]; exact hV, by rw [hB]; omega, ?_, ?_, ?_⟩
      · rw [stepOpkSlot_eq_of_ne_genOPK opkOrd _ (fun _ _ _ h => by cases h) hst, hB]
        exact Or.inl rfl
      · refine Or.inl ?_
        unfold stepSessOpkSlot
        by_cases hLt : sOpkOrd < (opkSessions hst.base).length
        · simp only [hLt, ↓reduceIte, hB]
        · simp only [hLt, ↓reduceIte, hOpt, Option.isSome_none, Bool.false_and, Bool.false_eq_true]
          rw [hB, sessOpkSlotAtOrd_eq, ordLookup_of_ge (Nat.le_of_not_lt hLt)]
      · rw [hB]; simp [isInitiateOpkQuery]
    | some opkPk =>
      simp only [hOpt, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hb
      rcases fgPreInitiate_step_shape false _ (some uSk) P (.sendOPK u i) u bundle hst.base
        (x.1, x.2.base) hb with ⟨hSpk, hOpk, hSessShape⟩
      dsimp only at hSpk hOpk hSessShape
      have hV' : MiniValid S x.2.base := by
        refine ⟨by rw [hOpk]; exact hV.1, fun s hs => ?_⟩
        rcases hSessShape with hEq | ⟨_, se, hSid, hCons⟩
        · rw [hEq] at hs; exact hV.2 s hs
        · rw [hCons] at hs
          rcases List.mem_cons.mp hs with rfl | hOld
          · rw [hSid]; trivial
          · exact hV.2 s hOld
      refine ⟨hV', by rw [hSpk]; omega, ?_, ?_, ?_⟩
      · rw [stepOpkSlot_eq_of_ne_genOPK opkOrd _ (fun _ _ _ h => by cases h) hst,
          opkSlotAtOrd_eq_of_map_fst (st1 := hst.base) (st2 := x.2.base) opkOrd (by rw [hOpk])]
        exact Or.inl rfl
      · rcases hSessShape with hSessEq | ⟨hAnyF, se, hSid, hCons⟩
        · have hOpkSessEq : opkSessions x.2.base = opkSessions hst.base := by
            unfold opkSessions; rw [hSessEq]
          have hPre := stepSessOpkSlot_retarget_pre sOpkOrd (.initiateOPK u i bundle) hst hV
          have hSessOrdEq : sessOpkSlotAtOrd S x.2.base sOpkOrd = sessOpkSlotAtOrd S hst.base sOpkOrd := by
            rw [sessOpkSlotAtOrd_eq, sessOpkSlotAtOrd_eq, hOpkSessEq]
          unfold SlotRetargetSess at hPre ⊢
          rw [hSessOrdEq, hSessEq]
          exact hPre.elim (fun h => Or.inl h.symm) fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩
        · refine Or.inl ?_
          have hIsOpk : isOpkInitSession se = true := by unfold isOpkInitSession; rw [hSid]
          have hOpkCons : opkSessions x.2.base = se :: opkSessions hst.base := by
            unfold opkSessions; rw [hCons, List.filter_cons, hIsOpk]; simp
          unfold stepSessOpkSlot
          by_cases hLt : sOpkOrd < (opkSessions hst.base).length
          · simp only [hLt, ↓reduceIte, sessOpkSlotAtOrd_eq, hOpkCons, ordLookup_cons_of_lt _ _ _ hLt]
          · simp only [hLt, ↓reduceIte, hOpt, Option.isSome_some, hAnyF, Bool.not_false,
              Bool.true_and]
            by_cases hEqOrd : (opkSessions hst.base).length = sOpkOrd
            · subst hEqOrd
              simp only [beq_self_eq_true, ↓reduceIte, sessOpkSlotAtOrd_eq, hOpkCons,
                ordLookup_cons_eq, hSid]
            · have hGt : (opkSessions hst.base).length + 1 ≤ sOpkOrd := by omega
              simp only [beq_eq_false_iff_ne.mpr hEqOrd, Bool.false_eq_true, ↓reduceIte]
              rw [sessOpkSlotAtOrd_eq, hOpkCons, ordLookup_of_ge (by simpa using hGt)]
      · rcases hSessShape with hSessEq | ⟨_, se, hSid, hCons⟩
        · have hOpkSessEq : opkSessions x.2.base = opkSessions hst.base := by
            unfold opkSessions; rw [hSessEq]
          rw [hOpkSessEq, hSessEq]; simp [isInitiateOpkQuery]
        · have hIsOpk : isOpkInitSession se = true := by unfold isOpkInitSession; rw [hSid]
          have hOpkCons : opkSessions x.2.base = se :: opkSessions hst.base := by
            unfold opkSessions; rw [hCons, List.filter_cons, hIsOpk]; simp
          rw [hOpkCons, hCons]; simp [isInitiateOpkQuery]
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl1KeyOpk
      Proofs.SignalPqxdh.Security.FgGapDh.Opk.pqxdhKeyIndFgPreImplOpk
      pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    cases hOpt : bundle.opkB? with
    | some _ =>
      simp only [hOpt, Option.isSome_some, ↓reduceIte, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hb
      have hB := (Prod.mk.inj hb).2
      exact hUnchanged (by rw [hB]; omega) (by rw [hB]) (by rw [hB])
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    | none =>
      simp only [hOpt, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hb
      rcases fgPreInitiate_step_shape false _ (some uSk) P (.sendNoOPK u i) u bundle hst.base
        (x.1, x.2.base) hb with ⟨hSpk, hOpk, hSessShape⟩
      dsimp only at hSpk hOpk hSessShape
      have hV' : MiniValid S x.2.base := by
        refine ⟨by rw [hOpk]; exact hV.1, fun s hs => ?_⟩
        rcases hSessShape with hEq | ⟨_, se, hSid, hCons⟩
        · rw [hEq] at hs; exact hV.2 s hs
        · rw [hCons] at hs
          rcases List.mem_cons.mp hs with rfl | hOld
          · rw [hSid]; trivial
          · exact hV.2 s hOld
      have hOpkSessEq : opkSessions x.2.base = opkSessions hst.base := by
        rcases hSessShape with hEq | ⟨_, se, hSid, hCons⟩
        · unfold opkSessions; rw [hEq]
        · have hNotOpk : isOpkInitSession se = false := by unfold isOpkInitSession; rw [hSid]
          unfold opkSessions; rw [hCons, List.filter_cons, hNotOpk]; simp
      refine ⟨hV', by rw [hSpk]; omega, ?_, ?_, ?_⟩
      · rw [stepOpkSlot_eq_of_ne_genOPK opkOrd _ (fun _ _ _ h => by cases h) hst,
          opkSlotAtOrd_eq_of_map_fst (st1 := hst.base) (st2 := x.2.base) opkOrd (by rw [hOpk])]
        exact Or.inl rfl
      · rw [stepSessOpkSlot_eq_of_ne_initiateOPK sOpkOrd _ (fun _ _ _ h => by cases h) hst,
          sessOpkSlotAtOrd_eq, sessOpkSlotAtOrd_eq, hOpkSessEq]
        exact Or.inl rfl
      · rw [hOpkSessEq]; simp [isInitiateOpkQuery]
  | _ =>
    have hb := mem_support_pqxdhKeyIndFgImpl_base P _ hst x hx
    rcases pqxdhKeyIndImpl_other_maps P _
      (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      hst.base (x.1, x.2.base) hb with ⟨hSpk, hOpk, hSess⟩
    dsimp only at hSpk hOpk hSess
    exact hUnchanged (by omega) hOpk hSess
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)

private theorem pqxdhKeyIndFgPreImpl1KeyOrdOpk_preserves_deadDh4Ord {S : Setup}
    (sOpkOrd opkOrd : ℕ) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hV : MiniValid S hst.base)
    (hDead : deadDh4 P (sessOpkSlotAtOrd S hst.base sOpkOrd) (opkSlotAtOrd S hst.base opkOrd)
      (P.x25519Base vSk) hst = true)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    deadDh4 P (sessOpkSlotAtOrd S x.2.base sOpkOrd) (opkSlotAtOrd S x.2.base opkOrd)
      (P.x25519Base vSk) x.2 = true := by
  have hsLt : sessOpkSlotAtOrd S hst.base sOpkOrd < S.N_send_tot := by
    have hD := hDead
    unfold deadDh4 at hD
    cases hF : hst.base.sessions.find?
        (fun s => initSessionSlotIdx s.sid == sessOpkSlotAtOrd S hst.base sOpkOrd) with
    | none => rw [hF] at hD; simp at hD
    | some se =>
      have hMem := List.mem_of_find?_eq_some hF
      have hEq : initSessionSlotIdx se.sid = sessOpkSlotAtOrd S hst.base sOpkOrd :=
        beq_iff_eq.mp (List.find?_some
          (p := fun s : KeyIndInitiatorEntry S =>
            initSessionSlotIdx s.sid == sessOpkSlotAtOrd S hst.base sOpkOrd) hF)
      rw [← hEq]
      exact initSessionSlotIdx_lt_of_isSendSessionId se.sid (hV.2 se hMem)
  have hOrdLt : sOpkOrd < (opkSessions hst.base).length := by
    by_contra hGe
    rw [sessOpkSlotAtOrd_eq, ordLookup_of_ge (Nat.le_of_not_lt hGe)] at hsLt
    exact Nat.lt_irrefl _ hsLt
  have hStepSessEq : stepSessOpkSlot sOpkOrd q hst = sessOpkSlotAtOrd S hst.base sOpkOrd := by
    simp [stepSessOpkSlot, hOrdLt]
  have hDeadPre : deadDh4 P (stepSessOpkSlot sOpkOrd q hst) (stepOpkSlot opkOrd q hst)
      (P.x25519Base vSk) hst = true := by
    rw [← deadDh4_retarget P (sessOpkSlotAtOrd S hst.base sOpkOrd)
      (stepSessOpkSlot sOpkOrd q hst) (opkSlotAtOrd S hst.base opkOrd) (stepOpkSlot opkOrd q hst)
      (P.x25519Base vSk) hst (stepSessOpkSlot_retarget_pre sOpkOrd q hst hV)
      (stepOpkSlot_retarget_pre opkOrd q hst hV)]
    exact hDead
  rcases pqxdhKeyIndFgPreImpl1KeyOrdOpk_step_props sOpkOrd opkOrd uSk vSk P q hst hV x hx with
    ⟨_, _, hRetOpk, hRetSess, _⟩
  rw [pqxdhKeyIndFgPreImpl1KeyOrdOpk_run_eq sOpkOrd opkOrd uSk vSk P q hst hV] at hx
  have hDeadMid := pqxdhKeyIndFgPreImpl1KeyOpk_preserves_deadDh4 P
    (stepSessOpkSlot sOpkOrd q hst) (stepOpkSlot opkOrd q hst)
    (hStepSessEq ▸ hsLt) uSk vSk q hst hDeadPre x hx
  rwa [deadDh4_retarget P (stepSessOpkSlot sOpkOrd q hst) (sessOpkSlotAtOrd S x.2.base sOpkOrd)
    (stepOpkSlot opkOrd q hst) (opkSlotAtOrd S x.2.base opkOrd) (P.x25519Base vSk) x.2
    hRetSess hRetOpk] at hDeadMid

private def nextActiveStateDh4 {S : Setup} (q : KeyIndQuery S)
    (stA : FgKeyInd1KeyActiveSimState S) (st1' : FgKeyInd1KeySimState S) :
    FgKeyInd1KeyActiveSimState S :=
  if isInitiateOpkQuery q then
    let cnt' := if stA.st1.sim.base.sessions.length < st1'.sim.base.sessions.length
      then stA.sendOpkCnt + 1 else stA.sendOpkCnt
    { stA with st1 := st1', sendOpkCnt := cnt' }
  else { stA with st1 := st1' }

private theorem fgRunInitiatePure_congr_target {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (t1 t2 maxLen : ℕ) (U : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S)
    (h : st.base.sessions.any (fun e => e.sid == sid) = false →
      (initSessionSlotIdx sid == t1) = (initSessionSlotIdx sid == t2)) :
    fgRunInitiatePure P ddh false t1 S maxLen U sid u bundle st =
      fgRunInitiatePure P ddh false t2 S maxLen U sid u bundle st := by
  unfold fgRunInitiatePure
  cases hAny : st.base.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte, h hAny]
  · rfl

private theorem fgKeyIndStepPure_other_irrel {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (t1 t2 spk1 spk2 maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S)
    (hNoGenSpk : ∀ u j, q ≠ .genSPK u j)
    (hNoInitOpk : ∀ u i b, q ≠ .initiateOPK u i b)
    (hNoInitNoOpk : ∀ u i b, q ≠ .initiateNoOPK u i b)
    (st : FgKeyIndSimState S) :
    fgKeyIndStepPure P ddh false t1 spk1 S maxLen U V q st =
      fgKeyIndStepPure P ddh false t2 spk2 S maxLen U V q st := by
  cases q with
  | genSPK u j => exact absurd rfl (hNoGenSpk u j)
  | initiateOPK u i b => exact absurd rfl (hNoInitOpk u i b)
  | initiateNoOPK u i b => exact absurd rfl (hNoInitNoOpk u i b)
  | initPrin _ => unfold fgKeyIndStepPure; dsimp only; simp
  | _ => rfl

private def FgActiveRelDh4 (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sOpkOrd opkOrd : Nat)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : Nat) (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S) : Prop :=
  FgSimInvDh4_1Key S b P hP (sessOpkSlotAtOrd S hst.base sOpkOrd)
    (opkSlotAtOrd S hst.base opkOrd) uSk vSk huSk hvSk rem hst stA.st1 ∧
  stA.resolvedPrin? = none ∧
  stA.sendOpkCnt = (opkSessions hst.base).length ∧
  hst.base.spkBundles.length + rem ≤ b.q_total

private theorem fgKeyInd1KeyActiveStepPureDh4_eq {S : Setup} (b : QueryBudget)
    (sOpkOrd opkOrd : Nat) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : Nat) (hst : KeyIndFgCutoffState S)
    (stA : FgKeyInd1KeyActiveSimState S)
    (hV : MiniValid S hst.base)
    (hRel : FgActiveRelDh4 S b P hP sOpkOrd opkOrd uSk vSk huSk hvSk (rem + 1) hst stA) :
    let sIdx := stepSessOpkSlot sOpkOrd q hst
    let oIdx := stepOpkSlot opkOrd q hst
    let U := P.x25519Base uSk
    let V := P.x25519Base vSk
    fgKeyInd1KeyActiveStepPureDh4 sOpkOrd opkOrd P uSk P.isValidDhTriple S b.q_total U V q stA =
      ((fgKeyInd1KeySimImplOpk P uSk P.isValidDhTriple sIdx oIdx S b.q_total U V q).run stA.st1 >>=
        fun p => pure (p.1, nextActiveStateDh4 q stA p.2)) := by
  intro sIdx oIdx U V
  rcases hRel with ⟨hInv0, hResNone, hCntEq, hSpkRem⟩
  have hInv : FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst stA.st1 :=
    fgSimInvDh4_1Key_retarget hInv0
      (stepSessOpkSlot_retarget_pre sOpkOrd q hst hV)
      (stepOpkSlot_retarget_pre opkOrd q hst hV)
  have hBase : stA.st1.sim.base = eraseStateFgOpk sIdx oIdx hst.base := hInv.1
  cases q with
  | initPrin u =>
    unfold fgKeyInd1KeyActiveStepPureDh4 fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk
      nextActiveStateDh4 isInitiateOpkQuery
    simp
  | genSPK u j =>
    have hSpkLen : stA.st1.sim.base.spkBundles.length = hst.base.spkBundles.length := by
      rw [hBase]; rfl
    have hSpkNe : (stA.st1.sim.base.spkBundles.length == b.q_total + 1) = false :=
      beq_eq_false_iff_ne.mpr (by omega)
    have hNoSpk : (spkBundleFlatIdx S u j == noSpkIdx S) = false :=
      spkBundleFlatIdx_ne_noSpkIdx S u j
    unfold fgKeyInd1KeyActiveStepPureDh4 fgGenSPK1KeyActivePure fgGenSpkActivePure
      fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk fgGenSPK1KeyPure fgKeyIndStepPure
      nextActiveStateDh4 isInitiateOpkQuery
    dsimp only [StateT_run_mk, Bool.false_eq_true, ↓reduceIte]
    simp only [hResNone, optNatMatches_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    cases stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, _⟩
        dsimp only
        simp [hSpkNe, hNoSpk]
    · simp
  | genOPK u j o =>
    have hOpkLen : stA.st1.sim.base.opkEntries.length = hst.base.opkEntries.length := by
      rw [hBase]; simp [eraseStateFgOpk, eraseOpkEntriesFg]
    have hOpkAny : stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) =
        hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) := by
      rw [hBase]; exact any_idx_eraseOpkEntriesFg S oIdx (u.val, j.val, o.val) hst.base.opkEntries
    unfold fgKeyInd1KeyActiveStepPureDh4 fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk
      fgKeyIndStepPureOpk fgGenOPKPureOpk nextActiveStateDh4 isInitiateOpkQuery
    dsimp only [StateT_run_mk, Bool.false_eq_true, ↓reduceIte]
    cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · have hAnySim : stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) =
          false := hOpkAny.trans hAny
      have hT1 : (opkFlatIdx S u j o ==
          if stA.st1.sim.base.opkEntries.length == opkOrd then opkFlatIdx S u j o else S.N_opk_tot) =
          (hst.base.opkEntries.length == opkOrd) := by
        rw [hOpkLen]
        have hNeN : (opkFlatIdx S u j o == S.N_opk_tot) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (opkSlotFlatIdx_lt S u.isLt j.isLt o.isLt))
        cases (hst.base.opkEntries.length == opkOrd) <;> simp [hNeN]
      have hT2 : (opkFlatIdx S u j o == oIdx) = (hst.base.opkEntries.length == opkOrd) :=
        genOPK_beq_stepOpkSlot opkOrd u j o hst hV hAny
      simp only [hAnySim, Bool.false_eq_true, ↓reduceIte]
      rw [hT1, hT2]
      simp
    · have hAnySim : stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) =
          true := hOpkAny.trans hAny
      simp only [hAnySim, ↓reduceIte]
      simp
  | initiateOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStepPureDh4 fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk
      fgKeyIndStepPureOpk fgKeyIndStepPure nextActiveStateDh4 isInitiateOpkQuery
    dsimp only [StateT_run_mk, ↓reduceIte]
    cases hOpt : bundle.opkB? with
    | none =>
      simp
    | some _ =>
      have hSome : bundle.opkB?.isSome = true := by simp [hOpt]
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      have hSessAny : stA.st1.sim.base.sessions.any (fun e => e.sid == .sendOPK u i) =
          hst.base.sessions.any (fun e => e.sid == .sendOPK u i) := by
        rw [hBase]; exact any_sid_eraseSessionsFg sIdx (.sendOPK u i) hst.base.sessions
      have hCongr :
          fgRunInitiatePure P P.isValidDhTriple false
            (if stA.sendOpkCnt == sOpkOrd then initSessionSlotIdx (.sendOPK u i) else S.N_send_tot)
            S b.q_total U (.sendOPK u i) u bundle stA.st1.sim =
          fgRunInitiatePure P P.isValidDhTriple false sIdx
            S b.q_total U (.sendOPK u i) u bundle stA.st1.sim := by
        refine fgRunInitiatePure_congr_target P P.isValidDhTriple _ _ b.q_total U (.sendOPK u i)
          u bundle stA.st1.sim fun hAnySim => ?_
        have hAnyBase : hst.base.sessions.any (fun e => e.sid == .sendOPK u i) = false :=
          hSessAny.symm.trans hAnySim
        rw [initiateOPK_beq_stepSessOpkSlot sOpkOrd u i bundle hst hV hSome hAnyBase, hCntEq]
        have hNeN : (initSessionSlotIdx (.sendOPK u i) == S.N_send_tot) = false :=
          beq_eq_false_iff_ne.mpr
            (Nat.ne_of_lt (initSessionSlotIdx_lt_of_isSendSessionId (.sendOPK u i) trivial))
        cases ((opkSessions hst.base).length == sOpkOrd) <;> simp [hNeN]
      rw [hCongr]
  | initiateNoOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStepPureDh4 fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk
      fgKeyIndStepPureOpk fgKeyIndStepPure nextActiveStateDh4 isInitiateOpkQuery
    dsimp only [StateT_run_mk, Bool.false_eq_true, ↓reduceIte]
    cases hOpt : bundle.opkB? with
    | some _ => simp
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      have hCongr :
          fgRunInitiatePure P P.isValidDhTriple false S.N_send_tot
            S b.q_total U (.sendNoOPK u i) u bundle stA.st1.sim =
          fgRunInitiatePure P P.isValidDhTriple false sIdx
            S b.q_total U (.sendNoOPK u i) u bundle stA.st1.sim := by
        refine fgRunInitiatePure_congr_target P P.isValidDhTriple _ _ b.q_total U (.sendNoOPK u i)
          u bundle stA.st1.sim fun _ => ?_
        have hNeN : (initSessionSlotIdx (.sendNoOPK u i) == S.N_send_tot) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))
        rw [hNeN, sendNoOPK_beq_stepSessOpkSlot sOpkOrd u i bundle hst]
      rw [hCongr]
  | acceptOPK k j o hdr =>
    unfold fgKeyInd1KeyActiveStepPureDh4 fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk
      fgKeyIndStepPureOpk nextActiveStateDh4 isInitiateOpkQuery
    dsimp only [StateT_run_mk, Bool.false_eq_true, ↓reduceIte]
    simp
  | _ =>
    unfold fgKeyInd1KeyActiveStepPureDh4 fgKeyInd1KeySimImplOpk fgKeyInd1KeyStepPureOpk
      fgKeyIndStepPureOpk nextActiveStateDh4 isInitiateOpkQuery
    dsimp only [StateT_run_mk, Bool.false_eq_true, ↓reduceIte]
    rw [fgKeyIndStepPure_other_irrel P P.isValidDhTriple sOpkOrd sIdx (b.q_total + 1) (noSpkIdx S)
      b.q_total U V _ (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) stA.st1.sim]
    simp

private theorem fgStepCoupling_dh4Ord_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sOpkOrd opkOrd : Nat)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : Nat)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hV : MiniValid S hst.base)
    (hDead : deadDh4 P (sessOpkSlotAtOrd S hst.base sOpkOrd) (opkSlotAtOrd S hst.base opkOrd)
      (P.x25519Base vSk) hst = false)
    (hRel : FgActiveRelDh4 S b P hP sOpkOrd opkOrd uSk vSk huSk hvSk (rem + 1) hst stA)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeyActiveSimState S → ProbComp Bool)
    (hCont : ∀ r hst' stA', MiniValid S hst'.base →
      deadDh4 P (sessOpkSlotAtOrd S hst'.base sOpkOrd) (opkSlotAtOrd S hst'.base opkOrd)
        (P.x25519Base vSk) hst' = false →
      FgActiveRelDh4 S b P hP sOpkOrd opkOrd uSk vSk huSk hvSk rem hst' stA' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, stA')] {true})
    (hDeadCont : ∀ r hst', MiniValid S hst'.base →
      deadDh4 P (sessOpkSlotAtOrd S hst'.base sOpkOrd) (opkSlotAtOrd S hst'.base opkOrd)
        (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk) S P q).run hst >>= k1]
        {true} ≤
      𝒟[(fgKeyInd1KeyActiveSimImplDh4 sOpkOrd opkOrd P uSk P.isValidDhTriple S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run stA >>= k2] {true} := by
  let sIdx := stepSessOpkSlot sOpkOrd q hst
  let oIdx := stepOpkSlot opkOrd q hst
  let lhsRun := (pqxdhKeyIndFgPreImpl1KeyOpk sIdx oIdx (some uSk) (some vSk) S P q).run hst
  have hRunEq :
      (pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk) S P q).run hst =
        lhsRun :=
    pqxdhKeyIndFgPreImpl1KeyOrdOpk_run_eq sOpkOrd opkOrd uSk vSk P q hst hV
  have hStepRhs :
      (fgKeyInd1KeyActiveSimImplDh4 sOpkOrd opkOrd P uSk P.isValidDhTriple S b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q).run stA =
      ((fgKeyInd1KeySimImplOpk P uSk P.isValidDhTriple sIdx oIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run stA.st1 >>=
        fun p => pure (p.1, nextActiveStateDh4 q stA p.2)) :=
    fgKeyInd1KeyActiveStepPureDh4_eq b sOpkOrd opkOrd P hP uSk vSk huSk hvSk q rem hst stA hV hRel
  rw [hRunEq, hStepRhs, bind_assoc]
  let k1Supp : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool :=
    open scoped Classical in
    fun x => if x ∈ support lhsRun then k1 x else pure false
  have hLhsEq : 𝒟[lhsRun >>= k1] = 𝒟[lhsRun >>= k1Supp] :=
    OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => by simp [k1Supp, hx])
  rw [hLhsEq]
  have hDeadPre : deadDh4 P sIdx oIdx (P.x25519Base vSk) hst = false := by
    rw [← deadDh4_retarget P (sessOpkSlotAtOrd S hst.base sOpkOrd) sIdx
      (opkSlotAtOrd S hst.base opkOrd) oIdx (P.x25519Base vSk) hst
      (stepSessOpkSlot_retarget_pre sOpkOrd q hst hV)
      (stepOpkSlot_retarget_pre opkOrd q hst hV)]
    exact hDead
  have hInvPre : FgSimInvDh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk (rem + 1) hst stA.st1 :=
    fgSimInvDh4_1Key_retarget hRel.1
      (stepSessOpkSlot_retarget_pre sOpkOrd q hst hV)
      (stepOpkSlot_retarget_pre opkOrd q hst hV)
  exact fgStepCoupling_dh4_1Key S b P hP sIdx oIdx uSk vSk huSk hvSk q rem hst stA.st1
    hDeadPre hInvPre
    k1Supp
    (fun p => k2 (p.1, nextActiveStateDh4 q stA p.2))
    (fun r hst' st1' hDF' hInv' => by
      by_cases hx : (r, hst') ∈ support lhsRun
      · simp only [k1Supp, hx, ↓reduceIte]
        have hxOrd : (r, hst') ∈ support
            ((pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk) S P q).run hst) :=
          hRunEq ▸ hx
        rcases pqxdhKeyIndFgPreImpl1KeyOrdOpk_step_props sOpkOrd opkOrd uSk vSk P q hst hV
          (r, hst') hxOrd with ⟨hV', hSpkStep, hRetOpk, hRetSess, hOpkCntStep⟩
        dsimp only at hV' hSpkStep hRetOpk hRetSess hOpkCntStep
        have hDFPost : deadDh4 P (sessOpkSlotAtOrd S hst'.base sOpkOrd)
            (opkSlotAtOrd S hst'.base opkOrd) (P.x25519Base vSk) hst' = false := by
          rw [← deadDh4_retarget P sIdx (sessOpkSlotAtOrd S hst'.base sOpkOrd)
            oIdx (opkSlotAtOrd S hst'.base opkOrd) (P.x25519Base vSk) hst' hRetSess hRetOpk]
          exact hDF'
        have hInvPost : FgSimInvDh4_1Key S b P hP (sessOpkSlotAtOrd S hst'.base sOpkOrd)
            (opkSlotAtOrd S hst'.base opkOrd) uSk vSk huSk hvSk rem hst' st1' :=
          fgSimInvDh4_1Key_retarget hInv' hRetSess hRetOpk
        have hSessLenPre : stA.st1.sim.base.sessions.length = hst.base.sessions.length := by
          rw [hInvPre.1]; simp [eraseStateFgOpk, eraseSessionsFg]
        have hSessLenPost : st1'.sim.base.sessions.length = hst'.base.sessions.length := by
          rw [hInv'.1]; simp [eraseStateFgOpk, eraseSessionsFg]
        have hNextSt1 : (nextActiveStateDh4 q stA st1').st1 = st1' := by
          unfold nextActiveStateDh4; split_ifs <;> rfl
        have hNextPrin : (nextActiveStateDh4 q stA st1').resolvedPrin? = none := by
          unfold nextActiveStateDh4; split_ifs <;> exact hRel.2.1
        have hNextCnt : (nextActiveStateDh4 q stA st1').sendOpkCnt =
            (opkSessions hst'.base).length := by
          unfold nextActiveStateDh4
          rw [hOpkCntStep, hSessLenPre, hSessLenPost, hRel.2.2.1]
          by_cases hQ : isInitiateOpkQuery q = true <;>
            by_cases hSLt : hst.base.sessions.length < hst'.base.sessions.length <;>
            simp [hQ, hSLt]
        have hSpkRem' : hst'.base.spkBundles.length + rem ≤ b.q_total := by
          have := hRel.2.2.2; omega
        exact hCont r hst' (nextActiveStateDh4 q stA st1') hV' hDFPost
          ⟨by rw [hNextSt1]; exact hInvPost, hNextPrin, hNextCnt, hSpkRem'⟩
      · simp [k1Supp, hx])
    (fun r hst' hDT' => by
      by_cases hx : (r, hst') ∈ support lhsRun
      · simp only [k1Supp, hx, ↓reduceIte]
        have hxOrd : (r, hst') ∈ support
            ((pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk) S P q).run hst) :=
          hRunEq ▸ hx
        rcases pqxdhKeyIndFgPreImpl1KeyOrdOpk_step_props sOpkOrd opkOrd uSk vSk P q hst hV
          (r, hst') hxOrd with ⟨hV', _, hRetOpk, hRetSess, _⟩
        have hDTPost : deadDh4 P (sessOpkSlotAtOrd S hst'.base sOpkOrd)
            (opkSlotAtOrd S hst'.base opkOrd) (P.x25519Base vSk) hst' = true := by
          rw [← deadDh4_retarget P sIdx (sessOpkSlotAtOrd S hst'.base sOpkOrd)
            oIdx (opkSlotAtOrd S hst'.base opkOrd) (P.x25519Base vSk) hst' hRetSess hRetOpk]
          exact hDT'
        exact hDeadCont r hst' hV' hDTPost
      · simp [k1Supp, hx])

/-- Creation-order per-ordinal `GapDhWithSign` bound for Leg `DH4` (`EK_A` at OPK-initiator
    ordinal `sOpkOrd`, `OPK_B` at `opkOrd`) against
    `fgKeyInd1KeyGapDhActiveAdvAtOpk sOpkOrd opkOrd S b A`. -/
theorem prob_badKeyIndFgDh4OrdAt_1Key_le_gapDhWithSign_active
    (S : Setup) (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (KeyIndAdversary S) b)
    {sOpkOrd opkOrd : Nat} (_hsOrd : sOpkOrd < activeSendOpkCount S b.q_on)
    (_hoOrd : opkOrd < activeOpkCount S b.q_on) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)]
        {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpkOrd opkOrd S b A) := by
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh4 sOpkOrd opkOrd P A.1
    (fun x => pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAtOpk_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    A.2.2.2.2.1
  exact evalDist_simulateQ_le_of_step_or_dead_inv
    (fun s1 => MiniValid S s1.base)
    (fun s1 => deadDh4 P (sessOpkSlotAtOrd S s1.base sOpkOrd) (opkSlotAtOrd S s1.base opkOrd)
      (P.x25519Base vSk) s1)
    (FgActiveRelDh4 S b P hP sOpkOrd opkOrd uSk vSk huLen hvLen)
    (pqxdhKeyIndFgPreImpl1KeyOrdOpk sOpkOrd opkOrd (some uSk) (some vSk) S P)
    (fgKeyInd1KeyActiveSimImplDh4 sOpkOrd opkOrd P uSk P.isValidDhTriple S b.q_total
      (P.x25519Base uSk) (P.x25519Base vSk))
    (fun q s1 hV x hx =>
      (pqxdhKeyIndFgPreImpl1KeyOrdOpk_step_props sOpkOrd opkOrd uSk vSk P q s1 hV x hx).1)
    (fun q s1 hV hD x hx =>
      pqxdhKeyIndFgPreImpl1KeyOrdOpk_preserves_deadDh4Ord sOpkOrd opkOrd uSk vSk P q s1 hV hD x hx)
    (fun q rem s1 s2 hV hDF hRel k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh4Ord_1Key S b P hP sOpkOrd opkOrd uSk vSk huLen hvLen q rem s1 s2 hV hDF hRel
        k1 k2 hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdh4FromAdvRoLog P.isValidDhTriple b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.st1.sim.advRoLog) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun _ s1 _ hD => by
      unfold badKeyIndFgDh4OrdAt
      simp [badKeyIndFgDh4At_eq_false_of_deadDh4 P b.q_ro _ _ (P.x25519Base vSk) s1 hD])
    (fun a rem s1 s2 _ hDF hRel => by
      unfold badKeyIndFgDh4OrdAt
      exact fgSimInvDh4_terminal_le S b P hP b.q_ro
        (sessOpkSlotAtOrd S s1.base sOpkOrd) (opkSlotAtOrd S s1.base opkOrd)
        uSk vSk huLen hvLen a rem s1 s2.st1.sim hDF hRel.1)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeyActiveSimState.empty S b secb)
    (miniValid_empty S secb)
    ⟨fgSimInvDh4_1Key_empty S b P hP _ _ uSk vSk huLen hvLen secb, rfl, rfl,
      by simp [KeyIndFgCutoffState.empty, KeyIndState.empty]⟩

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLeg4Alt
