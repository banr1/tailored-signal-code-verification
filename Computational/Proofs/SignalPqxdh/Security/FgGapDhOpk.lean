/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import VCVio.EvalDist.Monad.Basic

/-!
# Fiedler–Günther `KeyInd` `GapDH` Reduction, Case D (`DH4 = CDH(ek_U*, opk_V*)`)

Embeds the `GapDH` challenge `(U, V)` as the ephemeral key of initiator slot `sIdx` and the
public key of one-time prekey slot `oIdx`, and characterizes the simulator under `gapDhFullImpl`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh.Opk

open Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh.Opk
export _root_.SignalPqxdh.Security.FgGapDh.Opk (
  opkFlatIdx noSpkIdx fgGenOPKGdhOpk fgRunAcceptOPKGdhOpk
  fgKeyIndStepOpk extractCdh4FromAdvRoLog
  fgKeyIndGapDhRunAtOpk fgKeyIndGapDhAdvAtOpk
)
theorem spkBundleFlatIdx_lt (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    spkBundleFlatIdx S u j < S.N_spk_tot := by
  unfold spkBundleFlatIdx Setup.N_spk_tot
  have hu : u.val + 1 ≤ S.N_id := u.isLt
  have hj : j.val < S.N_recv := j.isLt
  calc u.val * S.N_recv + j.val
      < u.val * S.N_recv + S.N_recv := Nat.add_lt_add_left hj _
    _ = (u.val + 1) * S.N_recv := by ring
    _ ≤ S.N_id * S.N_recv := Nat.mul_le_mul_right S.N_recv hu

theorem spkBundleFlatIdx_ne_noSpkIdx (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) :
    (spkBundleFlatIdx S u j == noSpkIdx S) = false := by
  have := spkBundleFlatIdx_lt S u j
  unfold noSpkIdx
  simp only [beq_eq_false_iff_ne, ne_eq]
  omega

noncomputable def fgGenOPKPureOpk (P : Primitives) (targetOpkIdx : ℕ) (S : Setup) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (st : FgKeyIndSimState S) : ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
    return (.noneResp, st)
  let isTargetOpk : Bool := opkFlatIdx S u j o == targetOpkIdx
  let opkSkRaw ← sampleScalar32
  let opkPkRaw := P.x25519Base opkSkRaw
  let oEntry : OpkEntry := {
    opkSk    := if isTargetOpk then [] else opkSkRaw
    opkPk    := if isTargetOpk then V else opkPkRaw
    consumed := false }
  let base' := { st.base with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.base.opkEntries }
  return (.pkResp oEntry.opkPk, { st with base := base' })

@[simp]
theorem simulateQ_gapDhFullImpl_fgGenOPKGdhOpk (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetOpkIdx : ℕ) (S : Setup) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgGenOPKGdhOpk targetOpkIdx S V u j o st) =
      fgGenOPKPureOpk P targetOpkIdx S V u j o st := by
  unfold fgGenOPKGdhOpk fgGenOPKPureOpk
  split_ifs <;> simp

noncomputable def fgRunAcceptOPKPureOpk (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvOPK.contains (k.val, j.val, o.val) then
    return (.noneResp, st)
  if !koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let some (_, oEntry) := st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.noneResp, st)
  if oEntry.consumed then
    return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let canon := P.isCanonical hdr.ekAPk
  let dh1Zero := P.x25519 (List.replicate 32 0) hdr.ikAPk
  let dh2Zero := P.x25519 (List.replicate 32 0) hdr.ekAPk
  let ss? := P.kemDecaps bEntry.pqspkSk hdr.kemCt
  if !(replayOk && canon &&
       dh1Zero != List.replicate 32 0 &&
       dh2Zero != List.replicate 32 0) then
    return (.noneResp, st)
  let some ss := ss?
    | return (.noneResp, st)
  let pos1 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
  let pos2 := computeTwoSideOrPairPosPure P [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
  let pos3 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
  let pos4 := computeTwoSideOrPairPosPure P [] oEntry.opkSk hdr.ekAPk oEntry.opkPk
  let (drKey, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 (some pos4) ss st.fgL
  let opkEntries' := st.base.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  let senderHonestOpt := findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk
  let rInit : KeyIndRespEntry S := {
    sid          := .recvOPK k j o
    respIkPk     := kEntry.ikAPk
    spkPk        := bEntry.spkPk
    opkPk?       := some oEntry.opkPk
    pqspkPk      := bEntry.pqspkPk
    hdr          := hdr
    senderHonest := senderHonestOpt.isSome
    drKeyReal    := drKey
    drKeyRand    := drKey
  }
  let drKeyRand ← choosePartnerDrKeyRandPure P st.base.sessions rInit
  let base' : KeyIndState S := { st.base with
    opkEntries       := opkEntries'
    usedRecvOPK      := (k.val, j.val, o.val) :: st.base.usedRecvOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { rInit with drKeyRand := drKeyRand } :: st.base.respSessions
  }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  match senderHonestOpt with
  | some _ => return (.acceptFreshResp, st')
  | none   => return (.drKeyResp drKey, st')

@[simp]
theorem simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgRunAcceptOPKGdhOpk S maxLen k j o hdr st) =
      fgRunAcceptOPKPureOpk P ddh S maxLen k j o hdr st := by
  unfold fgRunAcceptOPKGdhOpk fgRunAcceptOPKPureOpk
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, simulateQ_pure]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (st.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [hUsed, ↓reduceIte, simulateQ_pure]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte,
        simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
        simulateQ_primBaseImpl_koskSenderOkPrim, pure_bind]
      by_cases hSender : (!koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk) = true
      · simp only [hSender, ↓reduceIte, simulateQ_pure]
      · simp only [hSender, Bool.false_eq_true, ↓reduceIte]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => simp
      | some pk =>
        rcases pk with ⟨_, kEntry⟩
        dsimp only
        cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => simp
        | some pb =>
          rcases pb with ⟨_, bEntry⟩
          dsimp only
          cases st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => simp
          | some po =>
            rcases po with ⟨_, oEntry⟩
            dsimp only
            by_cases hCons : oEntry.consumed = true
            · simp only [hCons, ↓reduceIte, simulateQ_pure]
            · simp only [hCons, Bool.false_eq_true, ↓reduceIte]
              rcases checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys
                  k.val hdr.pqspkId hdr.spkId hdr.ekAPk with ⟨replayOk, usedTriples'⟩
              dsimp only
              simp only [simulateQ_bind,
                simulateQ_gapDhFullImpl_primGdhQ_isCanonical,
                simulateQ_gapDhFullImpl_primGdhQ_x25519,
                simulateQ_gapDhFullImpl_primGdhQ_kemDecaps,
                pure_bind]
              by_cases hChk : (!(replayOk && P.isCanonical hdr.ekAPk &&
                   P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                   P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0)) = true
              · simp only [hChk, ↓reduceIte, simulateQ_pure]
              · simp only [hChk, Bool.false_eq_true, ↓reduceIte]
                cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                | none => simp
                | some ss =>
                  simp only [simulateQ_bind,
                    simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
                    simulateQ_gapDhFullImpl_fgPatch,
                    simulateQ_gapDhFullImpl_embedPrim,
                    simulateQ_primBaseImpl_findHonestPrincipalPrim,
                    simulateQ_gapDhFullImpl_choosePartnerDrKeyRandGdh,
                    pure_bind]
                  congr 1; ext ⟨drKey, fgL'⟩
                  congr 1; ext drKeyRand
                  cases findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;> simp

noncomputable def fgKeyIndStepPureOpk (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetOpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    ProbComp (KeyIndResponse × FgKeyIndSimState S) :=
  match q with
  | .genOPK u j o => fgGenOPKPureOpk P targetOpkIdx S V u j o st
  | .acceptOPK k j o hdr => fgRunAcceptOPKPureOpk P ddh S maxLen k j o hdr st
  | q => fgKeyIndStepPure P ddh false targetIdx (noSpkIdx S) S maxLen U V q st

@[simp]
theorem simulateQ_gapDhFullImpl_fgKeyIndStepOpk (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndStepOpk targetIdx targetOpkIdx S maxLen U V q st) =
      fgKeyIndStepPureOpk P ddh targetIdx targetOpkIdx S maxLen U V q st := by
  cases q
  case genOPK u j o => exact simulateQ_gapDhFullImpl_fgGenOPKGdhOpk P ddh targetOpkIdx S V u j o st
  case acceptOPK k j o hdr =>
    exact simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk P ddh S maxLen k j o hdr st
  all_goals
    simp only [fgKeyIndStepOpk, fgKeyIndStepPureOpk]
    exact simulateQ_gapDhFullImpl_fgKeyIndStep P ddh false targetIdx (noSpkIdx S) S maxLen U V _ st

/-- Pure `QueryImpl` induced by simulating `fgKeyIndStepOpk` under `gapDhFullImpl P ddh`. -/
noncomputable def fgKeyIndSimImplOpk (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetOpkIdx : ℕ) (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyIndSimState S) ProbComp) :=
  fun gq => StateT.mk (fun st =>
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndStepOpk targetIdx targetOpkIdx S maxLen U V gq st))

theorem fgKeyIndSimImplOpk_run (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetOpkIdx : ℕ) (S : Setup) (maxLen : ℕ) (U V : Bytes)
    (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    (fgKeyIndSimImplOpk P ddh targetIdx targetOpkIdx S maxLen U V q).run st =
      fgKeyIndStepPureOpk P ddh targetIdx targetOpkIdx S maxLen U V q st := by
  unfold fgKeyIndSimImplOpk
  simp

def pureExtractCdh4FromAdvRoLog (ddh : Bytes → Bytes → Bytes → Bool)
    (maxLen : ℕ) (U V : Bytes) (advRoLog : List Bytes) : Bytes :=
  let cands := (advRoLog.take maxLen).map extractDh4
  match cands.find? (fun z => ddh U V z) with
  | some z => z
  | none   => List.replicate 32 0

@[simp]
theorem simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (U V : Bytes) (advRoLog : List Bytes) :
    simulateQ (gapDhFullImpl P ddh) (extractCdh4FromAdvRoLog maxLen U V advRoLog) =
      pure (pureExtractCdh4FromAdvRoLog ddh maxLen U V advRoLog) := by
  unfold extractCdh4FromAdvRoLog
  dsimp only [pureExtractCdh4FromAdvRoLog]
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_findMGdh P ddh
    (fun z => ddhGdhQ U V z) (fun z => ddh U V z)
    (fun z => simulateQ_gapDhFullImpl_ddhGdhQ P ddh U V z), pure_bind]
  cases ((advRoLog.take maxLen).map extractDh4).find? (fun z => ddh U V z) <;> simp

theorem pureExtractCdh4FromAdvRoLog_wins_of_mem
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (maxLen : ℕ) (u v : Bytes) (advRoLog : List Bytes)
    (h_mem : ∃ sec ∈ advRoLog.take maxLen, extractDh4 sec = P.x25519 u (P.x25519Base v)) :
    (P.pow8 (pureExtractCdh4FromAdvRoLog P.isValidDhTriple maxLen
      (P.x25519Base u) (P.x25519Base v) advRoLog) ==
      P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  dsimp only [pureExtractCdh4FromAdvRoLog]
  set cands := (advRoLog.take maxLen).map extractDh4
  rcases h_mem with ⟨sec, hsec_mem, hsec_eq⟩
  have hcands_mem : P.x25519 u (P.x25519Base v) ∈ cands := by
    rw [← hsec_eq]
    exact List.mem_map_of_mem hsec_mem
  have hddh_target : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v)
      (P.x25519 u (P.x25519Base v)) = true :=
    (hWF.ddh_consistent u v (P.x25519 u (P.x25519Base v))).mpr rfl
  have hfind_some :
      (cands.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z)).isSome =
        true :=
    List.find?_isSome.mpr ⟨P.x25519 u (P.x25519Base v), hcands_mem, hddh_target⟩
  rcases Option.isSome_iff_exists.mp hfind_some with ⟨Z, hZ⟩
  have hZ_ddh : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) Z = true :=
    List.find?_some hZ
  have hZ_pow : P.pow8 Z = P.pow8 (P.x25519 u (P.x25519Base v)) :=
    (hWF.ddh_consistent u v Z).mp hZ_ddh
  rw [hZ]
  simp [hZ_pow]

theorem simulateQ_gapDhFullImpl_fgKeyIndGapDhRunAtOpk
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) :
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndGapDhRunAtOpk targetIdx targetOpkIdx S b A U V) =
    (do
      let secb ← $ᵗ Bool
      let initSt := FgKeyIndSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyIndSimState S) ProbComp) +
        fgKeyIndSimImplOpk P ddh targetIdx targetOpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return pureExtractCdh4FromAdvRoLog ddh b.q_total U V finalSt.advRoLog) := by
  unfold fgKeyIndGapDhRunAtOpk
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh]
  congr 1
  ext secb
  rw [simulateQ_bind,
      simulateQ_gapDhFullImpl_runWithGdhStep P ddh
        (fgKeyIndStepOpk targetIdx targetOpkIdx S b.q_total U V)
        (fgKeyIndSimImplOpk P ddh targetIdx targetOpkIdx S b.q_total U V)
        (fun _ _ => rfl)]
  congr 1
  ext res
  exact simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog P ddh b.q_total U V res.2.advRoLog

theorem gapDhExp_fgKeyIndGapDhAdvAtOpk_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhExp P ddh pow8 (fgKeyIndGapDhAdvAtOpk targetIdx targetOpkIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgKeyIndSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyIndSimState S) ProbComp) +
        fgKeyIndSimImplOpk P ddh targetIdx targetOpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdh4FromAdvRoLog ddh b.q_total U V finalSt.advRoLog) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhExp fgKeyIndGapDhAdvAtOpk
  dsimp only [gapDhFullImpl, gapDhDdhImpl]
  congr 1; ext u
  congr 1; ext v
  change (simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndGapDhRunAtOpk targetIdx targetOpkIdx S b A (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhFullImpl_fgKeyIndGapDhRunAtOpk]
  simp only [bind_assoc, pure_bind]

end Proofs.SignalPqxdh.Security.FgGapDh.Opk
