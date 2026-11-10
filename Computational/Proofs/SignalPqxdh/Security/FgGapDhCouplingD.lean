/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingC
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Hop 4 (`G3 → G3.5`): Reduction to a Coupling of Tagged Runs

Shows distributional equivalence between `pqxdhKeyIndAdvTestImpl` and `pqxdhKeyIndAdvTagImpl`,
reduces `keyIndAdvG3` to a `RelCoupled` coupling of lazy tagged runs, and defines
`LazyTagCacheAgree` and `lazyStop`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security

@[simp]
theorem recordAcceptKemGeneric_run {S : Setup} {Base Resp : Type} (P : Primitives)
    (getBundles : Base → List ((Nat × Nat) × SpkBundleEntry))
    (isNoneResp : Resp → Bool)
    (k : Fin S.N_id) (j : Fin S.N_recv) (hdr : HandshakeHdr)
    (out : Resp) (hst : ShCrState S Base) :
    (recordAcceptKemGeneric P getBundles isNoneResp k j hdr out).run hst =
      if isNoneResp out then pure (out, hst)
      else
        match (getBundles hst.base).find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => pure (out, hst)
        | some (_, bEntry) =>
          match P.kemDecaps bEntry.pqspkSk hdr.kemCt with
          | none => pure (out, hst)
          | some ss =>
            let r : RecvKemRecord := {
              bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
              pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
              kemCt := hdr.kemCt, kemSs := ss }
            pure (out, { hst with recvKemRecs := r :: hst.recvKemRecs }) := rfl

theorem evalDist_step_relEagerTag_acceptOPK {S : Setup} (testReal : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P (.acceptOPK k j o hdr)).run adv >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P (.acceptOPK k j o hdr)).run lst >>= k2] := by
  rcases hRel with ⟨rfl, hWF⟩
  rw [pqxdhKeyIndAdvTagImpl_run]
  dsimp only [tagStepView]
  rw [tagStepAcceptOPK_getLazyView]
  dsimp only [pqxdhKeyIndAdvTestImpl, pqxdhKeyIndAdvG3Impl, pqxdhKeyIndShCrImpl,
    liftKeyIndAdvShCr, runShCrAcceptGeneric, tagStepAcceptOPK,
    resolveLazyAdv, resolveLazyShCr]
  simp only [StateT.run_mk, StateT.run_bind, liftShCrBase_run, pqxdhKeyIndImpl,
    StateT.run_get, pure_bind, bind_assoc]
  have hUsedEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).usedRecvOPK =
      lst.adv.shCr.base.usedRecvOPK := rfl
  have hPrinEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).principals =
      lst.adv.shCr.base.principals := rfl
  have hSpkEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).spkBundles =
      lst.adv.shCr.base.spkBundles := rfl
  have hOpkEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).opkEntries =
      lst.adv.shCr.base.opkEntries := rfl
  have hKyberEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).seenKyberBaseKeys =
      lst.adv.shCr.base.seenKyberBaseKeys := rfl
  have hRoEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).roCache =
      lst.adv.shCr.base.roCache := rfl
  have hAdvKeysEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).advKeys =
      lst.adv.shCr.base.advKeys := rfl
  rw [hUsedEq, hPrinEq, hSpkEq, hOpkEq, hKyberEq, hRoEq, hAdvKeysEq]
  by_cases hHdr : !(hdr.spkId == UInt32.ofNat j.val && hdr.pqspkId == UInt32.ofNat j.val &&
      hdr.opkId? == some (UInt32.ofNat o.val) && hdr.ikAPk.length == 32 && hdr.ekAPk.length == 32)
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
      isNoneKeyIndResp, runLazyPost]
    exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : lst.adv.shCr.base.usedRecvOPK.contains (k.val, j.val, o.val)
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
        isNoneKeyIndResp, runLazyPost]
      exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : !koskSenderOk P lst.adv.shCr.base.principals lst.adv.shCr.base.advKeys
        hdr.ikAPk
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
          isNoneKeyIndResp, runLazyPost]
        exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hPrin : lst.adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
          isNoneKeyIndResp, runLazyPost]
        exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
      | some kp =>
        dsimp only
        cases hSpk : lst.adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
            isNoneKeyIndResp, runLazyPost]
          exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
        | some bp =>
          dsimp only
          cases hOpk : lst.adv.shCr.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
            o.val)) with
          | none =>
            simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
              isNoneKeyIndResp, runLazyPost]
            exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
          | some op =>
            dsimp only
            by_cases hCons : op.2.consumed
            · simp only [hCons, ↓reduceIte, StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
                isNoneKeyIndResp, runLazyPost]
              exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
            · simp only [hCons, Bool.false_eq_true, ↓reduceIte]
              cases hAcc : Model.acceptKeys P
                { ikBSk := kp.2.secIKA0, ikBPk := kp.2.ikAPk, spkBSk := bp.2.spkSk,
                  spkBPk := bp.2.spkPk, opkBSk? := some op.2.opkSk, pqspkBSk := bp.2.pqspkSk,
                  pqspkBPk := bp.2.pqspkPk, trustedPeer := true,
                  replayOk := (checkAndMarkKyberBaseKeySeen lst.adv.shCr.base.seenKyberBaseKeys k.val
                    hdr.pqspkId hdr.spkId hdr.ekAPk).1,
                  hdr := hdr } with
              | none =>
                simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
                  isNoneKeyIndResp, runLazyPost]
                exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
              | some _ =>
                dsimp only
                cases hDec : P.kemDecaps bp.2.pqspkSk hdr.kemCt with
                | none =>
                  simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
                    isNoneKeyIndResp, runLazyPost]
                  exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
                | some ss =>
                  dsimp only
                  rw [evalHkdfOrRo_true_eq_evalCache]
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                    StateT.run_set, recordKeyIndResp, StateT.run_get,
                    runLazyPost, Bool.or_true, evalRoIf, ↓reduceIte, roLens, CacheLens.eval,
                    withAdvRoCache, withShCrRoCache, withBaseRoCache,
                    bind_assoc, pure_bind]
                  refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun q hq => ?_)
                  rcases q with ⟨drKey, roCache'⟩
                  let r0 : KeyIndRespEntry S := {
                    sid := .recvOPK k j o, respIkPk := kp.2.ikAPk, spkPk := bp.2.spkPk,
                    opkPk? := some op.2.opkPk, pqspkPk := bp.2.pqspkPk, hdr := hdr,
                    senderHonest := (findHonestPrincipal P lst.adv.shCr.base.principals
                      hdr.ikAPk).isSome,
                    drKeyReal := tagDRKey (buildSecrets (P.x25519 bp.2.spkSk hdr.ikAPk) (P.x25519
                      kp.2.secIKA0 hdr.ekAPk) (P.x25519 bp.2.spkSk hdr.ekAPk) (some (P.x25519
                      op.2.opkSk hdr.ekAPk)) ss),
                    drKeyRand := default }
                  have hPartMap :
                      (resolveLazyBase lst.randCache lst.adv.shCr.base).sessions.find?
                        (fun s => keyIndPartner P s
                          { r0 with drKeyReal := drKey, drKeyRand := drKey }) =
                      (lst.adv.shCr.base.sessions.find? (fun s => keyIndPartner P s r0)).map
                        (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache) := by
                    have hEqFn : (fun s => keyIndPartner P s
                      { r0 with drKeyReal := drKey, drKeyRand := drKey }) =
                        (fun s => keyIndPartner P s r0) := rfl
                    rw [hEqFn]
                    exact find_partner_map_resolveSessionEntry P lst.adv.shCr.base.roCache
                      lst.randCache
                      lst.adv.shCr.base.sessions r0
                  rw [hPartMap]
                  cases hPart : lst.adv.shCr.base.sessions.find? (fun s => keyIndPartner P s r0)
                    with
                  | some s =>
                    dsimp only [Option.map]
                    have hsMem : s ∈ lst.adv.shCr.base.sessions := List.mem_of_find?_eq_some hPart
                    have hRel' : ∀ (sh : Bool), RelEagerTag
                        { shCr := { lst.adv.shCr with
                            base := { (resolveLazyBase lst.randCache lst.adv.shCr.base) with
                              opkEntries := lst.adv.shCr.base.opkEntries.map (fun (idx, e) =>
                                if idx == (k.val, j.val, o.val) then (idx,
                                  { e with consumed := true }) else (idx, e))
                              usedRecvOPK := (k.val, j.val, o.val) :: lst.adv.shCr.base.usedRecvOPK
                              seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                                lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                                hdr.ekAPk).2
                              roCache := roCache'
                              respSessions := { r0 with senderHonest := sh, drKeyReal := drKey,
                                                        drKeyRand := (resolveSessionEntry
                                                          lst.adv.shCr.base.roCache lst.randCache
                                                          s).drKeyRand } ::
                                (resolveLazyBase lst.randCache lst.adv.shCr.base).respSessions }
                            recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                             pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                             kemCt := hdr.kemCt, kemSs := ss } ::
                                               lst.adv.shCr.recvKemRecs }
                          advRoLog := lst.adv.advRoLog }
                        { lst with adv := { lst.adv with shCr := { lst.adv.shCr with
                            base := { lst.adv.shCr.base with
                              opkEntries := lst.adv.shCr.base.opkEntries.map (fun (idx, e) =>
                                if idx == (k.val, j.val, o.val) then (idx,
                                  { e with consumed := true }) else (idx, e))
                              usedRecvOPK := (k.val, j.val, o.val) :: lst.adv.shCr.base.usedRecvOPK
                              seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                                lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                                hdr.ekAPk).2
                              roCache := roCache'
                              respSessions :=
                                { r0 with senderHonest := sh, drKeyRand := s.drKeyRand } ::
                                lst.adv.shCr.base.respSessions }
                            recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                             pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                             kemCt := hdr.kemCt, kemSs := ss } ::
                                               lst.adv.shCr.recvKemRecs } } } := by
                      intro sh
                      refine ⟨?_, ?_, hWF.sess_rand, ?_, ?_, ?_⟩
                      · dsimp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, List.map]
                        have hHead :
                            resolveRespEntry roCache' lst.randCache
                              { r0 with senderHonest := sh, drKeyRand := s.drKeyRand } =
                            { r0 with senderHonest := sh, drKeyReal := drKey,
                                      drKeyRand := (resolveSessionEntry lst.adv.shCr.base.roCache
                                        lst.randCache s).drKeyRand } := by
                          unfold resolveRespEntry resolveSessionEntry
                          dsimp only [r0]
                          simp only [tagDRKey_rootKey, (lookupCacheKey_evalCache_self _ _ (drKey,
                            roCache') hq).1]
                        have hSess :
                            List.map (resolveSessionEntry roCache' lst.randCache)
                              lst.adv.shCr.base.sessions =
                            List.map (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache)
                              lst.adv.shCr.base.sessions :=
                          map_resolveSessionEntry_evalCache_ro _ _ _ _ hWF.sess_ro (drKey, roCache')
                            hq
                        have hTailResp :
                            List.map (resolveRespEntry roCache' lst.randCache)
                              lst.adv.shCr.base.respSessions =
                            List.map (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache)
                              lst.adv.shCr.base.respSessions :=
                          map_resolveRespEntry_evalCache_ro _ _ _ _ hWF.resp_ro (drKey, roCache') hq
                        rw [hHead, hSess, hTailResp]
                      · intro x hx
                        exact (lookupCacheKey_evalCache_preserves _ x.drKeyReal.rootKey _
                          (hWF.sess_ro x hx) (drKey, roCache') hq).2
                      · intro r hr
                        simp only [List.mem_cons] at hr
                        rcases hr with rfl | hr
                        · dsimp only [r0]
                          rw [tagDRKey_rootKey]
                          exact (lookupCacheKey_evalCache_self _ _ (drKey, roCache') hq).2
                        · exact (lookupCacheKey_evalCache_preserves _ r.drKeyReal.rootKey _
                            (hWF.resp_ro r hr) (drKey, roCache') hq).2
                      · intro r hr
                        simp only [List.mem_cons] at hr
                        rcases hr with rfl | hr
                        · exact hWF.sess_rand s hsMem
                        · exact hWF.resp_rand r hr
                      · intro p hp
                        simp only [List.length_cons]
                        have hplen := hWF.rand_len p hp
                        omega
                    cases findHonestPrincipal P lst.adv.shCr.base.principals hdr.ikAPk <;>
                    · simp only [Option.isSome, StateT.run_set, StateT.run_pure, pure_bind,
                        recordAcceptKemGeneric_run, isNoneKeyIndResp, Bool.false_eq_true,
                          ↓reduceIte, hSpk, hDec]
                      exact hk _ _ _ (hRel' _)
                  | none =>
                    dsimp only [Option.map]
                    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                      StateT.run_set, evalRandIf, ↓reduceIte, randLens, CacheLens.eval, bind_assoc,
                      pure_bind]
                    have hFindPid : lst.randCache.find? (fun (x, _) => x == freshPidBytes
                      lst.adv.shCr.base) = none := by
                      refine find_none_of_length_lt lst.randCache (freshPidBytes lst.adv.shCr.base)
                        (lst.adv.shCr.base.sessions.length + lst.adv.shCr.base.respSessions.length)
                          hWF.rand_len ?_
                      exact freshPidBytes_length lst.adv.shCr.base
                    rw [evalCache_eq_sample_of_find_none lst.randCache (freshPidBytes
                      lst.adv.shCr.base) hFindPid]
                    simp only [bind_assoc, pure_bind]
                    refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun drKeyRand _ => ?_)
                    have hRel' : ∀ (sh : Bool), RelEagerTag
                        { shCr := { lst.adv.shCr with
                            base := { (resolveLazyBase lst.randCache lst.adv.shCr.base) with
                              opkEntries := lst.adv.shCr.base.opkEntries.map (fun (idx, e) =>
                                if idx == (k.val, j.val, o.val) then (idx,
                                  { e with consumed := true }) else (idx, e))
                              usedRecvOPK := (k.val, j.val, o.val) :: lst.adv.shCr.base.usedRecvOPK
                              seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                                lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                                hdr.ekAPk).2
                              roCache := roCache'
                              respSessions :=
                                { r0 with senderHonest := sh, drKeyReal := drKey, drKeyRand :=
                                drKeyRand } ::
                                (resolveLazyBase lst.randCache lst.adv.shCr.base).respSessions }
                            recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                             pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                             kemCt := hdr.kemCt, kemSs := ss } ::
                                               lst.adv.shCr.recvKemRecs }
                          advRoLog := lst.adv.advRoLog }
                        { adv := { lst.adv with shCr := { lst.adv.shCr with
                            base := { lst.adv.shCr.base with
                              opkEntries := lst.adv.shCr.base.opkEntries.map (fun (idx, e) =>
                                if idx == (k.val, j.val, o.val) then (idx,
                                  { e with consumed := true }) else (idx, e))
                              usedRecvOPK := (k.val, j.val, o.val) :: lst.adv.shCr.base.usedRecvOPK
                              seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                                lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                                hdr.ekAPk).2
                              roCache := roCache'
                              respSessions :=
                                { r0 with senderHonest := sh, drKeyRand := tagDRKey (freshPidBytes
                                lst.adv.shCr.base) } ::
                                lst.adv.shCr.base.respSessions }
                            recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                             pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                             kemCt := hdr.kemCt, kemSs := ss } ::
                                               lst.adv.shCr.recvKemRecs } }
                          randCache := (freshPidBytes lst.adv.shCr.base, drKeyRand) :: lst.randCache
                            } := by
                      intro sh
                      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                      · dsimp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, List.map]
                        have hHead :
                            resolveRespEntry roCache' ((freshPidBytes lst.adv.shCr.base, drKeyRand)
                              :: lst.randCache)
                              { r0 with senderHonest := sh, drKeyRand := tagDRKey (freshPidBytes
                                lst.adv.shCr.base) } =
                            { r0 with senderHonest := sh, drKeyReal := drKey, drKeyRand := drKeyRand
                              } := by
                          unfold resolveRespEntry
                          dsimp only [r0]
                          simp only [tagDRKey_rootKey, lookupCacheKey_cons_self,
                            (lookupCacheKey_evalCache_self _ _ (drKey, roCache') hq).1]
                        have hSess :
                            List.map (resolveSessionEntry roCache' ((freshPidBytes
                              lst.adv.shCr.base, drKeyRand) :: lst.randCache))
                              lst.adv.shCr.base.sessions =
                            List.map (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache)
                              lst.adv.shCr.base.sessions := by
                          rw [map_resolveSessionEntry_evalCache_ro _ _ _ _ hWF.sess_ro (drKey,
                            roCache') hq,
                              map_resolveSessionEntry_cons_rand _ _ _ _ _ hWF.sess_rand hFindPid]
                        have hTailResp :
                            List.map (resolveRespEntry roCache' ((freshPidBytes lst.adv.shCr.base,
                              drKeyRand) :: lst.randCache))
                              lst.adv.shCr.base.respSessions =
                            List.map (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache)
                              lst.adv.shCr.base.respSessions := by
                          rw [map_resolveRespEntry_evalCache_ro _ _ _ _ hWF.resp_ro (drKey,
                            roCache') hq,
                              map_resolveRespEntry_cons_rand _ _ _ _ _ hWF.resp_rand hFindPid]
                        rw [hHead, hSess, hTailResp]
                      · intro s hs
                        exact (lookupCacheKey_evalCache_preserves _ s.drKeyReal.rootKey _
                          (hWF.sess_ro s hs) (drKey, roCache') hq).2
                      · intro s hs
                        exact find_cons_isSome_of_isSome _ _ _ _ (hWF.sess_rand s hs)
                      · intro r hr
                        simp only [List.mem_cons] at hr
                        rcases hr with rfl | hr
                        · dsimp only [r0]
                          rw [tagDRKey_rootKey]
                          exact (lookupCacheKey_evalCache_self _ _ (drKey, roCache') hq).2
                        · exact (lookupCacheKey_evalCache_preserves _ r.drKeyReal.rootKey _
                            (hWF.resp_ro r hr) (drKey, roCache') hq).2
                      · intro r hr
                        simp only [List.mem_cons] at hr
                        rcases hr with rfl | hr
                        · simp [tagDRKey_rootKey]
                        · exact find_cons_isSome_of_isSome _ _ _ _ (hWF.resp_rand r hr)
                      · intro p hp
                        simp only [List.mem_cons, List.length_cons] at hp ⊢
                        rcases hp with rfl | hp
                        · dsimp only
                          rw [freshPidBytes_length]
                          omega
                        · have hplen := hWF.rand_len p hp
                          omega
                    cases findHonestPrincipal P lst.adv.shCr.base.principals hdr.ikAPk <;>
                    · simp only [Option.isSome, StateT.run_pure, pure_bind,
                        recordAcceptKemGeneric_run, isNoneKeyIndResp, Bool.false_eq_true,
                          ↓reduceIte, hSpk, hDec]
                      exact hk _ _ _ (hRel' _)

theorem evalDist_step_relEagerTag_acceptNoOPK {S : Setup} (testReal : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst)
    (k1 : KeyIndResponse × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P (.acceptNoOPK k j l hdr)).run adv >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P (.acceptNoOPK k j l hdr)).run lst >>= k2] :=
        by
  rcases hRel with ⟨rfl, hWF⟩
  rw [pqxdhKeyIndAdvTagImpl_run]
  dsimp only [tagStepView]
  rw [tagStepAcceptNoOPK_getLazyView]
  dsimp only [pqxdhKeyIndAdvTestImpl, pqxdhKeyIndAdvG3Impl, pqxdhKeyIndShCrImpl,
    liftKeyIndAdvShCr, runShCrAcceptGeneric, tagStepAcceptNoOPK,
    resolveLazyAdv, resolveLazyShCr]
  simp only [StateT.run_mk, StateT.run_bind, liftShCrBase_run, pqxdhKeyIndImpl,
    StateT.run_get, pure_bind, bind_assoc]
  have hUsedEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).usedRecvNoOPK =
      lst.adv.shCr.base.usedRecvNoOPK := rfl
  have hPrinEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).principals =
      lst.adv.shCr.base.principals := rfl
  have hSpkEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).spkBundles =
      lst.adv.shCr.base.spkBundles := rfl
  have hKyberEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).seenKyberBaseKeys =
      lst.adv.shCr.base.seenKyberBaseKeys := rfl
  have hRoEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).roCache =
      lst.adv.shCr.base.roCache := rfl
  have hAdvKeysEq : (resolveLazyBase lst.randCache lst.adv.shCr.base).advKeys =
      lst.adv.shCr.base.advKeys := rfl
  rw [hUsedEq, hPrinEq, hSpkEq, hKyberEq, hRoEq, hAdvKeysEq]
  by_cases hHdr : !(hdr.spkId == UInt32.ofNat j.val && hdr.pqspkId == UInt32.ofNat j.val &&
      hdr.opkId? == none && hdr.ikAPk.length == 32 && hdr.ekAPk.length == 32)
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
      isNoneKeyIndResp, runLazyPost]
    exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : lst.adv.shCr.base.usedRecvNoOPK.contains (k.val, j.val, l.val)
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
        isNoneKeyIndResp, runLazyPost]
      exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : !koskSenderOk P lst.adv.shCr.base.principals lst.adv.shCr.base.advKeys
        hdr.ikAPk
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
          isNoneKeyIndResp, runLazyPost]
        exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hPrin : lst.adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
          isNoneKeyIndResp, runLazyPost]
        exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
      | some kp =>
        dsimp only
        cases hSpk : lst.adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
            isNoneKeyIndResp, runLazyPost]
          exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
        | some bp =>
          dsimp only
          cases hAcc : Model.acceptKeys P
            { ikBSk := kp.2.secIKA0, ikBPk := kp.2.ikAPk, spkBSk := bp.2.spkSk,
              spkBPk := bp.2.spkPk, opkBSk? := none, pqspkBSk := bp.2.pqspkSk,
              pqspkBPk := bp.2.pqspkPk, trustedPeer := true,
              replayOk := (checkAndMarkKyberBaseKeySeen lst.adv.shCr.base.seenKyberBaseKeys k.val
                hdr.pqspkId hdr.spkId hdr.ekAPk).1,
              hdr := hdr } with
          | none =>
            simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
              isNoneKeyIndResp, runLazyPost]
            exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
          | some _ =>
            dsimp only
            cases hDec : P.kemDecaps bp.2.pqspkSk hdr.kemCt with
            | none =>
              simp only [StateT.run_pure, pure_bind, recordAcceptKemGeneric_run,
                isNoneKeyIndResp, runLazyPost]
              exact hk .noneResp (resolveLazyAdv lst) lst ⟨rfl, hWF⟩
            | some ss =>
              dsimp only
              rw [evalHkdfOrRo_true_eq_evalCache]
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                StateT.run_set, recordKeyIndResp, StateT.run_get,
                runLazyPost, Bool.or_true, evalRoIf, ↓reduceIte, roLens, CacheLens.eval,
                withAdvRoCache, withShCrRoCache, withBaseRoCache,
                bind_assoc, pure_bind]
              refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun q hq => ?_)
              rcases q with ⟨drKey, roCache'⟩
              let r0 : KeyIndRespEntry S := {
                sid := .recvNoOPK k j l, respIkPk := kp.2.ikAPk, spkPk := bp.2.spkPk,
                opkPk? := none, pqspkPk := bp.2.pqspkPk, hdr := hdr,
                senderHonest := (findHonestPrincipal P lst.adv.shCr.base.principals
                  hdr.ikAPk).isSome,
                drKeyReal := tagDRKey (buildSecrets (P.x25519 bp.2.spkSk hdr.ikAPk) (P.x25519
                  kp.2.secIKA0 hdr.ekAPk) (P.x25519 bp.2.spkSk hdr.ekAPk) none ss),
                drKeyRand := default }
              have hPartMap :
                  (resolveLazyBase lst.randCache lst.adv.shCr.base).sessions.find?
                    (fun s => keyIndPartner P s
                      { r0 with drKeyReal := drKey, drKeyRand := drKey }) =
                  (lst.adv.shCr.base.sessions.find? (fun s => keyIndPartner P s r0)).map
                    (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache) := by
                have hEqFn : (fun s => keyIndPartner P s
                  { r0 with drKeyReal := drKey, drKeyRand := drKey }) =
                    (fun s => keyIndPartner P s r0) := rfl
                rw [hEqFn]
                exact find_partner_map_resolveSessionEntry P lst.adv.shCr.base.roCache lst.randCache
                  lst.adv.shCr.base.sessions r0
              rw [hPartMap]
              cases hPart : lst.adv.shCr.base.sessions.find? (fun s => keyIndPartner P s r0) with
              | some s =>
                dsimp only [Option.map]
                have hsMem : s ∈ lst.adv.shCr.base.sessions := List.mem_of_find?_eq_some hPart
                have hRel' : ∀ (sh : Bool), RelEagerTag
                    { shCr := { lst.adv.shCr with
                        base := { (resolveLazyBase lst.randCache lst.adv.shCr.base) with
                          usedRecvNoOPK := (k.val, j.val, l.val) :: lst.adv.shCr.base.usedRecvNoOPK
                          seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                            lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                            hdr.ekAPk).2
                          roCache := roCache'
                          respSessions := { r0 with senderHonest := sh, drKeyReal := drKey,
                                                    drKeyRand := (resolveSessionEntry
                                                      lst.adv.shCr.base.roCache lst.randCache
                                                      s).drKeyRand } ::
                            (resolveLazyBase lst.randCache lst.adv.shCr.base).respSessions }
                        recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                         pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                         kemCt := hdr.kemCt, kemSs := ss } ::
                                           lst.adv.shCr.recvKemRecs }
                      advRoLog := lst.adv.advRoLog }
                    { lst with adv := { lst.adv with shCr := { lst.adv.shCr with
                        base := { lst.adv.shCr.base with
                          usedRecvNoOPK := (k.val, j.val, l.val) :: lst.adv.shCr.base.usedRecvNoOPK
                          seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                            lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                            hdr.ekAPk).2
                          roCache := roCache'
                          respSessions :=
                            { r0 with senderHonest := sh, drKeyRand := s.drKeyRand } ::
                            lst.adv.shCr.base.respSessions }
                        recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                         pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                         kemCt := hdr.kemCt, kemSs := ss } ::
                                           lst.adv.shCr.recvKemRecs } } } := by
                  intro sh
                  refine ⟨?_, ?_, hWF.sess_rand, ?_, ?_, ?_⟩
                  · dsimp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, List.map]
                    have hHead :
                        resolveRespEntry roCache' lst.randCache
                          { r0 with senderHonest := sh, drKeyRand := s.drKeyRand } =
                        { r0 with senderHonest := sh, drKeyReal := drKey,
                                  drKeyRand := (resolveSessionEntry lst.adv.shCr.base.roCache
                                    lst.randCache s).drKeyRand } := by
                      unfold resolveRespEntry resolveSessionEntry
                      dsimp only [r0]
                      simp only [tagDRKey_rootKey, (lookupCacheKey_evalCache_self _ _ (drKey,
                        roCache') hq).1]
                    have hSess :
                        List.map (resolveSessionEntry roCache' lst.randCache)
                          lst.adv.shCr.base.sessions =
                        List.map (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache)
                          lst.adv.shCr.base.sessions :=
                      map_resolveSessionEntry_evalCache_ro _ _ _ _ hWF.sess_ro (drKey, roCache') hq
                    have hTailResp :
                        List.map (resolveRespEntry roCache' lst.randCache)
                          lst.adv.shCr.base.respSessions =
                        List.map (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache)
                          lst.adv.shCr.base.respSessions :=
                      map_resolveRespEntry_evalCache_ro _ _ _ _ hWF.resp_ro (drKey, roCache') hq
                    rw [hHead, hSess, hTailResp]
                  · intro x hx
                    exact (lookupCacheKey_evalCache_preserves _ x.drKeyReal.rootKey _ (hWF.sess_ro x
                      hx) (drKey, roCache') hq).2
                  · intro r hr
                    simp only [List.mem_cons] at hr
                    rcases hr with rfl | hr
                    · dsimp only [r0]
                      rw [tagDRKey_rootKey]
                      exact (lookupCacheKey_evalCache_self _ _ (drKey, roCache') hq).2
                    · exact (lookupCacheKey_evalCache_preserves _ r.drKeyReal.rootKey _ (hWF.resp_ro
                        r hr) (drKey, roCache') hq).2
                  · intro r hr
                    simp only [List.mem_cons] at hr
                    rcases hr with rfl | hr
                    · exact hWF.sess_rand s hsMem
                    · exact hWF.resp_rand r hr
                  · intro p hp
                    simp only [List.length_cons]
                    have hplen := hWF.rand_len p hp
                    omega
                cases findHonestPrincipal P lst.adv.shCr.base.principals hdr.ikAPk <;>
                · simp only [Option.isSome, StateT.run_set, StateT.run_pure, pure_bind,
                    recordAcceptKemGeneric_run, isNoneKeyIndResp, Bool.false_eq_true, ↓reduceIte,
                      hSpk, hDec]
                  exact hk _ _ _ (hRel' _)
              | none =>
                dsimp only [Option.map]
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  evalRandIf, ↓reduceIte, randLens, CacheLens.eval, bind_assoc, pure_bind]
                have hFindPid : lst.randCache.find? (fun (x, _) => x == freshPidBytes
                  lst.adv.shCr.base) = none := by
                  refine find_none_of_length_lt lst.randCache (freshPidBytes lst.adv.shCr.base)
                    (lst.adv.shCr.base.sessions.length + lst.adv.shCr.base.respSessions.length)
                      hWF.rand_len ?_
                  exact freshPidBytes_length lst.adv.shCr.base
                rw [evalCache_eq_sample_of_find_none lst.randCache (freshPidBytes lst.adv.shCr.base)
                  hFindPid]
                simp only [bind_assoc, pure_bind]
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun drKeyRand _ => ?_)
                have hRel' : ∀ (sh : Bool), RelEagerTag
                    { shCr := { lst.adv.shCr with
                        base := { (resolveLazyBase lst.randCache lst.adv.shCr.base) with
                          usedRecvNoOPK := (k.val, j.val, l.val) :: lst.adv.shCr.base.usedRecvNoOPK
                          seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                            lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                            hdr.ekAPk).2
                          roCache := roCache'
                          respSessions :=
                            { r0 with senderHonest := sh, drKeyReal := drKey, drKeyRand := drKeyRand
                            } ::
                            (resolveLazyBase lst.randCache lst.adv.shCr.base).respSessions }
                        recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                         pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                         kemCt := hdr.kemCt, kemSs := ss } ::
                                           lst.adv.shCr.recvKemRecs }
                      advRoLog := lst.adv.advRoLog }
                    { adv := { lst.adv with shCr := { lst.adv.shCr with
                        base := { lst.adv.shCr.base with
                          usedRecvNoOPK := (k.val, j.val, l.val) :: lst.adv.shCr.base.usedRecvNoOPK
                          seenKyberBaseKeys := (checkAndMarkKyberBaseKeySeen
                            lst.adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                            hdr.ekAPk).2
                          roCache := roCache'
                          respSessions :=
                            { r0 with senderHonest := sh, drKeyRand := tagDRKey (freshPidBytes
                            lst.adv.shCr.base) } ::
                            lst.adv.shCr.base.respSessions }
                        recvKemRecs := { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                                         pqspkPk := bp.2.pqspkPk, pqspkSk := bp.2.pqspkSk,
                                         kemCt := hdr.kemCt, kemSs := ss } ::
                                           lst.adv.shCr.recvKemRecs } }
                      randCache := (freshPidBytes lst.adv.shCr.base, drKeyRand) :: lst.randCache }
                        := by
                  intro sh
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                  · dsimp only [resolveLazyAdv, resolveLazyShCr, resolveLazyBase, List.map]
                    have hHead :
                        resolveRespEntry roCache' ((freshPidBytes lst.adv.shCr.base, drKeyRand) ::
                          lst.randCache)
                          { r0 with senderHonest := sh, drKeyRand := tagDRKey (freshPidBytes
                            lst.adv.shCr.base) } =
                        { r0 with senderHonest := sh, drKeyReal := drKey, drKeyRand := drKeyRand }
                          := by
                      unfold resolveRespEntry
                      dsimp only [r0]
                      simp only [tagDRKey_rootKey, lookupCacheKey_cons_self,
                        (lookupCacheKey_evalCache_self _ _ (drKey, roCache') hq).1]
                    have hSess :
                        List.map (resolveSessionEntry roCache' ((freshPidBytes lst.adv.shCr.base,
                          drKeyRand) :: lst.randCache))
                          lst.adv.shCr.base.sessions =
                        List.map (resolveSessionEntry lst.adv.shCr.base.roCache lst.randCache)
                          lst.adv.shCr.base.sessions := by
                      rw [map_resolveSessionEntry_evalCache_ro _ _ _ _ hWF.sess_ro (drKey, roCache')
                        hq,
                          map_resolveSessionEntry_cons_rand _ _ _ _ _ hWF.sess_rand hFindPid]
                    have hTailResp :
                        List.map (resolveRespEntry roCache' ((freshPidBytes lst.adv.shCr.base,
                          drKeyRand) :: lst.randCache))
                          lst.adv.shCr.base.respSessions =
                        List.map (resolveRespEntry lst.adv.shCr.base.roCache lst.randCache)
                          lst.adv.shCr.base.respSessions := by
                      rw [map_resolveRespEntry_evalCache_ro _ _ _ _ hWF.resp_ro (drKey, roCache')
                        hq,
                          map_resolveRespEntry_cons_rand _ _ _ _ _ hWF.resp_rand hFindPid]
                    rw [hHead, hSess, hTailResp]
                  · intro s hs
                    exact (lookupCacheKey_evalCache_preserves _ s.drKeyReal.rootKey _ (hWF.sess_ro s
                      hs) (drKey, roCache') hq).2
                  · intro s hs
                    exact find_cons_isSome_of_isSome _ _ _ _ (hWF.sess_rand s hs)
                  · intro r hr
                    simp only [List.mem_cons] at hr
                    rcases hr with rfl | hr
                    · dsimp only [r0]
                      rw [tagDRKey_rootKey]
                      exact (lookupCacheKey_evalCache_self _ _ (drKey, roCache') hq).2
                    · exact (lookupCacheKey_evalCache_preserves _ r.drKeyReal.rootKey _ (hWF.resp_ro
                        r hr) (drKey, roCache') hq).2
                  · intro r hr
                    simp only [List.mem_cons] at hr
                    rcases hr with rfl | hr
                    · simp [tagDRKey_rootKey]
                    · exact find_cons_isSome_of_isSome _ _ _ _ (hWF.resp_rand r hr)
                  · intro p hp
                    simp only [List.mem_cons, List.length_cons] at hp ⊢
                    rcases hp with rfl | hp
                    · dsimp only
                      rw [freshPidBytes_length]
                      omega
                    · have hplen := hWF.rand_len p hp
                      omega
                cases findHonestPrincipal P lst.adv.shCr.base.principals hdr.ikAPk <;>
                · simp only [Option.isSome, StateT.run_pure, pure_bind,
                    recordAcceptKemGeneric_run, isNoneKeyIndResp, Bool.false_eq_true, ↓reduceIte,
                      hSpk, hDec]
                  exact hk _ _ _ (hRel' _)

theorem evalDist_step_relEagerTag {S : Setup} (testReal : Bool) (P : Primitives)
    (q : KeyIndQuery S) (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst)
    (k1 : (keyIndSpec S).Range q × KeyIndAdvCutoffState S → ProbComp Bool)
    (k2 : (keyIndSpec S).Range q × KeyIndLazyState S → ProbComp Bool)
    (hk : ∀ r s1' s2', RelEagerTag s1' s2' → 𝒟[k1 (r, s1')] = 𝒟[k2 (r, s2')]) :
    𝒟[(pqxdhKeyIndAdvTestImpl testReal S P q).run adv >>= k1] =
      𝒟[(pqxdhKeyIndAdvTagImpl true true testReal S P q).run lst >>= k2] := by
  cases q with
  | initPrin u =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_of_simple testReal P (.initPrin u)
      (Or.inl ⟨u, rfl⟩) lst hWF k1 k2 hk
  | corruptIK u =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_of_simple testReal P (.corruptIK u)
      (Or.inr (Or.inl ⟨u, rfl⟩)) lst hWF k1 k2 hk
  | genSPK u j =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_of_simple testReal P (.genSPK u j)
      (Or.inr (Or.inr (Or.inl ⟨u, j, rfl⟩))) lst hWF k1 k2 hk
  | genOPK u j o =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_of_simple testReal P (.genOPK u j o)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨u, j, o, rfl⟩)))) lst hWF k1 k2 hk
  | revealDhSecrets =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_of_simple testReal P .revealDhSecrets
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) lst hWF k1 k2 hk
  | registerKey sk =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_of_simple testReal P (.registerKey sk)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sk, rfl⟩)))))) lst hWF k1 k2 hk
  | revealSpkSk u j =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_of_simple testReal P (.revealSpkSk u j)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, j, rfl⟩)))))) lst hWF k1 k2 hk
  | roQuery sec =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_roQuery testReal P sec lst hWF k1 k2 hk
  | revealSessionKey sid =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_revealSessionKey testReal P sid lst hWF k1 k2 hk
  | testSession sid =>
    rcases hRel with ⟨rfl, hWF⟩
    exact evalDist_step_relEagerTag_testSession testReal P sid lst hWF k1 k2 hk
  | initiateOPK u i bundle =>
    exact evalDist_step_relEagerTag_initiateOPK testReal P u i bundle adv lst hRel k1 k2 hk
  | initiateNoOPK u i bundle =>
    exact evalDist_step_relEagerTag_initiateNoOPK testReal P u i bundle adv lst hRel k1 k2 hk
  | acceptOPK k j o hdr =>
    exact evalDist_step_relEagerTag_acceptOPK testReal P k j o hdr adv lst hRel k1 k2 hk
  | acceptNoOPK k j l hdr =>
    exact evalDist_step_relEagerTag_acceptNoOPK testReal P k j l hdr adv lst hRel k1 k2 hk

theorem evalDist_simulateQ_testImpl_eq_tagImpl_true_true {S : Setup} {α : Type}
    (testReal : Bool) (P : Primitives)
    (obs1 : α × KeyIndAdvCutoffState S → ProbComp Bool)
    (obs2 : α × KeyIndLazyState S → ProbComp Bool)
    (hObs : ∀ a s1 s2, RelEagerTag s1 s2 → 𝒟[obs1 (a, s1)] = 𝒟[obs2 (a, s2)])
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    (adv : KeyIndAdvCutoffState S) (lst : KeyIndLazyState S)
    (hRel : RelEagerTag adv lst) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndAdvCutoffState S)
      ProbComp) +
      pqxdhKeyIndAdvTestImpl testReal S P
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndLazyState S)
      ProbComp) +
      pqxdhKeyIndAdvTagImpl true true testReal S P
    𝒟[(_root_.simulateQ full1 oa).run adv >>= obs1] =
      𝒟[(_root_.simulateQ full2 oa).run lst >>= obs2] :=
  CacheLens.evalDist_simulateQ_eq_of_rel RelEagerTag
    (pqxdhKeyIndAdvTestImpl testReal S P)
    (pqxdhKeyIndAdvTagImpl true true testReal S P)
    (fun q s1 s2 hR k1 k2 hk => evalDist_step_relEagerTag testReal P q s1 s2 hR k1 k2 hk)
    obs1 obs2 hObs oa adv lst hRel

theorem evalDist_simulateQ_testImpl_finalizeKeyIndG3_eq_tagImpl_false_false {S : Setup}
    (testReal : Bool) (P : Primitives) (secb : Bool)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) :
    let initTrue : KeyIndAdvCutoffState S :=
      { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndAdvCutoffState S)
      ProbComp) +
      pqxdhKeyIndAdvTestImpl testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndLazyState S)
      ProbComp) +
      pqxdhKeyIndAdvTagImpl false false testReal S P
    𝒟[(_root_.simulateQ fullTest oa).run initTrue >>= fun p => finalizeKeyIndG3 S P secb p.1
      p.2.shCr] =
      𝒟[(_root_.simulateQ full00 oa).run (KeyIndLazyState.empty S) >>=
        fun p => finalizeKeyIndG3 S P secb p.1 p.2.adv.shCr] := by
  intro initTrue fullTest full00
  rw [evalDist_simulateQ_testImpl_eq_tagImpl_true_true testReal P
    (fun p => finalizeKeyIndG3 S P secb p.1 p.2.shCr)
    (fun p => finalizeKeyIndG3 S P secb p.1 p.2.adv.shCr)
    (fun a s1 s2 ⟨hEq, _⟩ => by
      subst hEq
      dsimp only [resolveLazyAdv]
      rw [finalizeKeyIndG3_resolveLazyShCr])
    oa initTrue (KeyIndLazyState.empty S) (relEagerTag_empty S)]
  exact evalDist_simulateQ_pqxdhKeyIndAdvTagImpl_true_true_eq_false_false testReal P oa
    (isInvariant_randLens_finalizeKeyIndG3 S P secb)
    (isInvariant_roLens_finalizeKeyIndG3 S P secb)
    (KeyIndLazyState.empty S)

theorem evalDist_simulateQ_testImpl_badKeyIndFgAny_eq_tagImpl_false_false {S : Setup}
    (testReal : Bool) (P : Primitives) (maxLen : ℕ)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool) :
    let initTrue : KeyIndAdvCutoffState S :=
      { shCr := { base := KeyIndState.empty S true }, advRoLog := [] }
    let fullTest := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndAdvCutoffState S)
      ProbComp) +
      pqxdhKeyIndAdvTestImpl testReal S P
    let full00 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndLazyState S)
      ProbComp) +
      pqxdhKeyIndAdvTagImpl false false testReal S P
    𝒟[(_root_.simulateQ fullTest oa).run initTrue >>=
        fun p => pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog)] =
      𝒟[(_root_.simulateQ full00 oa).run (KeyIndLazyState.empty S) >>=
        fun p => pure (badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog)] := by
  intro initTrue fullTest full00
  rw [evalDist_simulateQ_testImpl_eq_tagImpl_true_true testReal P
    (fun p => pure (badKeyIndFgAny4 P maxLen p.2.shCr.base p.2.advRoLog))
    (fun p => pure (badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog))
    (fun a s1 s2 ⟨hEq, _⟩ => by
      subst hEq
      dsimp only [resolveLazyAdv, resolveLazyShCr]
      rw [badKeyIndFgAny_resolveLazyBase])
    oa initTrue (KeyIndLazyState.empty S) (relEagerTag_empty S)]
  exact evalDist_simulateQ_pqxdhKeyIndAdvTagImpl_true_true_eq_false_false testReal P oa
    (isInvariant_randLens_badKeyIndFgAny S P maxLen)
    (isInvariant_roLens_badKeyIndFgAny S P maxLen)
    (KeyIndLazyState.empty S)

theorem RelCoupled.and_support {α β : Type} {R : α → β → Prop}
    {m5 : ProbComp α} {m6 : ProbComp β}
    (h : RelCoupled R m5 m6) :
    RelCoupled (fun x5 x6 => R x5 x6 ∧ x5 ∈ support m5 ∧ x6 ∈ support m6) m5 m6 := by
  classical
  refine ⟨fun w5 w6 hle => ?_, fun w6 w5 hle => ?_⟩
  · let w5' : α → ℝ≥0∞ := fun x5 => if x5 ∈ support m5 then w5 x5 else 0
    let w6' : β → ℝ≥0∞ := fun x6 => if x6 ∈ support m6 then w6 x6 else ⊤
    have hEq5 : probExpect m5 w5 = probExpect m5 w5' :=
      le_antisymm
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m5 w5 w5' (fun x hx => by simp only
          [w5', hx, ↓reduceIte, le_refl]))
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m5 w5' w5 (fun x hx => by simp only
          [w5', hx, ↓reduceIte, le_refl]))
    have hEq6 : probExpect m6 w6' = probExpect m6 w6 :=
      le_antisymm
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m6 w6' w6 (fun x hx => by simp only
          [w6', hx, ↓reduceIte, le_refl]))
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m6 w6 w6' (fun x hx => by simp only
          [w6', hx, ↓reduceIte, le_refl]))
    rw [hEq5, ← hEq6]
    refine h.le_left w5' w6' (fun x5 x6 hR => ?_)
    by_cases hx5 : x5 ∈ support m5
    · by_cases hx6 : x6 ∈ support m6
      · simp only [w5', w6', hx5, hx6, ↓reduceIte]
        exact hle x5 x6 ⟨hR, hx5, hx6⟩
      · simp only [w6', hx6, ↓reduceIte, le_top]
    · simp only [w5', hx5, ↓reduceIte, zero_le]
  · let w6' : β → ℝ≥0∞ := fun x6 => if x6 ∈ support m6 then w6 x6 else 0
    let w5' : α → ℝ≥0∞ := fun x5 => if x5 ∈ support m5 then w5 x5 else ⊤
    have hEq6 : probExpect m6 w6 = probExpect m6 w6' :=
      le_antisymm
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m6 w6 w6' (fun x hx => by simp only
          [w6', hx, ↓reduceIte, le_refl]))
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m6 w6' w6 (fun x hx => by simp only
          [w6', hx, ↓reduceIte, le_refl]))
    have hEq5 : probExpect m5 w5' = probExpect m5 w5 :=
      le_antisymm
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m5 w5' w5 (fun x hx => by simp only
          [w5', hx, ↓reduceIte, le_refl]))
        (_root_.SignalPqxdh.Security.probExpect_mono_of_support m5 w5 w5' (fun x hx => by simp only
          [w5', hx, ↓reduceIte, le_refl]))
    rw [hEq6, ← hEq5]
    refine h.le_right w6' w5' (fun x5 x6 hR => ?_)
    by_cases hx6 : x6 ∈ support m6
    · by_cases hx5 : x5 ∈ support m5
      · simp only [w6', w5', hx6, hx5, ↓reduceIte]
        exact hle x5 x6 ⟨hR, hx5, hx6⟩
      · simp only [w5', hx5, ↓reduceIte, le_top]
    · simp only [w6', hx6, ↓reduceIte, zero_le]

def lookupCache {K : Type} [BEq K] (c : List (K × DRKey)) (k : K) : Option DRKey :=
  (c.find? (fun (x, _) => x == k)).map Prod.snd

@[simp]
theorem lookupCache_nil {K : Type} [BEq K] (k : K) :
    lookupCache ([] : List (K × DRKey)) k = none := rfl

@[simp]
theorem lookupCache_cons_eq {K : Type} [BEq K] [LawfulBEq K]
    (c : List (K × DRKey)) (k : K) (dk : DRKey) :
    lookupCache ((k, dk) :: c) k = some dk := by
  simp [lookupCache]

theorem lookupCache_cons_of_beq_false {K : Type} [BEq K]
    (c : List (K × DRKey)) (k q : K) (dk : DRKey) (hne : (k == q) = false) :
    lookupCache ((k, dk) :: c) q = lookupCache c q := by
  simp [lookupCache, hne]

theorem relCoupled_evalCache_of_lookup_eq {K : Type} [BEq K] [LawfulBEq K]
    (c1 c2 : List (K × DRKey)) (k1 k2 : K)
    (hEq : lookupCache c1 k1 = lookupCache c2 k2) :
    RelCoupled
      (fun p1 p2 =>
        p1.1 = p2.1 ∧
        lookupCache p1.2 k1 = lookupCache p2.2 k2 ∧
        (∀ q1, (k1 == q1) = false → lookupCache p1.2 q1 = lookupCache c1 q1) ∧
        (∀ q2, (k2 == q2) = false → lookupCache p2.2 q2 = lookupCache c2 q2))
      (evalCache c1 k1)
      (evalCache c2 k2) := by
  unfold evalCache
  unfold lookupCache at hEq
  cases h1 : c1.find? (fun (x, _) => x == k1) with
  | none =>
    rw [h1, Option.map_none] at hEq
    cases h2 : c2.find? (fun (x, _) => x == k2) with
    | none =>
      refine RelCoupled.bind_same sampleDRKey96 (fun dk _ => ?_)
      refine RelCoupled.of_pure ⟨rfl, ?_, ?_, ?_⟩
      · rw [lookupCache_cons_eq, lookupCache_cons_eq]
      · intro q1 hne1
        exact lookupCache_cons_of_beq_false c1 k1 q1 dk hne1
      · intro q2 hne2
        exact lookupCache_cons_of_beq_false c2 k2 q2 dk hne2
    | some p2 =>
      rw [h2, Option.map_some] at hEq
      nomatch hEq
  | some p1 =>
    rcases p1 with ⟨x1, dk1⟩
    rw [h1, Option.map_some] at hEq
    cases h2 : c2.find? (fun (x, _) => x == k2) with
    | none =>
      rw [h2, Option.map_none] at hEq
      nomatch hEq
    | some p2 =>
      rcases p2 with ⟨x2, dk2⟩
      rw [h2, Option.map_some] at hEq
      injection hEq with hdk
      subst hdk
      refine RelCoupled.of_pure ⟨rfl, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
      unfold lookupCache
      rw [h1, h2]
      rfl

/-- Whether `sec` can appear in `ro5` (`testReal = false` lazy `roCache`):
    either in `adv.advRoLog`, or as `drKeyReal.rootKey` of an unfresh or revealed session. -/
def ro5KeyInView {S : Setup} (adv : KeyIndAdvCutoffState S) (sec : Bytes) : Bool :=
  adv.advRoLog.contains sec ||
  adv.shCr.base.sessions.any (fun s => (!s.fresh || s.revealed) && (s.drKeyReal.rootKey == sec)) ||
  adv.shCr.base.respSessions.any (fun r => (!r.senderHonest || r.revealed) && (r.drKeyReal.rootKey
    == sec))

def testedRealKeyInView {S : Setup} (adv : KeyIndAdvCutoffState S) (sec : Bytes) : Bool :=
  adv.shCr.base.sessions.any (fun s => s.tested && (s.drKeyReal.rootKey == sec)) ||
  adv.shCr.base.respSessions.any (fun r => r.tested && (r.drKeyReal.rootKey == sec))

def testedRandKeyInView {S : Setup} (adv : KeyIndAdvCutoffState S) (kRand : Bytes) : Bool :=
  adv.shCr.base.sessions.any (fun s => s.tested && (s.drKeyRand.rootKey == kRand)) ||
  adv.shCr.base.respSessions.any (fun r => r.tested && (r.drKeyRand.rootKey == kRand))

def testedPairInView {S : Setup} (adv : KeyIndAdvCutoffState S) (kReal kRand : Bytes) : Bool :=
  adv.shCr.base.sessions.any (fun s =>
    s.tested && (s.drKeyReal.rootKey == kReal) && (s.drKeyRand.rootKey == kRand)) ||
  adv.shCr.base.respSessions.any (fun r =>
    r.tested && (r.drKeyReal.rootKey == kReal) && (r.drKeyRand.rootKey == kRand))

/-- Sticky stop predicate firing when a tested session's `kReal` enters `ro5KeyInView` or two
    tested sessions conflict on `kReal`/`kRand` or `sid`. -/
def lazyStop {S : Setup} (adv : KeyIndAdvCutoffState S) : Bool :=
  adv.shCr.base.sessions.any (fun s => s.tested && ro5KeyInView adv s.drKeyReal.rootKey) ||
  adv.shCr.base.respSessions.any (fun r => r.tested && ro5KeyInView adv r.drKeyReal.rootKey) ||
  adv.shCr.base.sessions.any (fun s1 => s1.tested &&
    (adv.shCr.base.sessions.any (fun s2 => s2.tested &&
      (((s1.drKeyReal.rootKey == s2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
        s2.drKeyRand.rootKey)) ||
       ((s1.sid == s2.sid) && !(s1.drKeyReal.rootKey == s2.drKeyReal.rootKey)))) ||
     adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
      ((s1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
        r2.drKeyRand.rootKey))))) ||
  adv.shCr.base.respSessions.any (fun r1 => r1.tested &&
    adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
      (((r1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (r1.drKeyRand.rootKey ==
        r2.drKeyRand.rootKey)) ||
       ((r1.sid == r2.sid) && !(r1.drKeyReal.rootKey == r2.drKeyReal.rootKey)))))

@[simp]
theorem ro5KeyInView_withAdvRoCache {S : Setup} (c : List (Bytes × DRKey))
    (adv : KeyIndAdvCutoffState S) (sec : Bytes) :
    ro5KeyInView (withAdvRoCache c adv) sec = ro5KeyInView adv sec := rfl

@[simp]
theorem testedRealKeyInView_withAdvRoCache {S : Setup} (c : List (Bytes × DRKey))
    (adv : KeyIndAdvCutoffState S) (sec : Bytes) :
    testedRealKeyInView (withAdvRoCache c adv) sec = testedRealKeyInView adv sec := rfl

@[simp]
theorem testedRandKeyInView_withAdvRoCache {S : Setup} (c : List (Bytes × DRKey))
    (adv : KeyIndAdvCutoffState S) (kRand : Bytes) :
    testedRandKeyInView (withAdvRoCache c adv) kRand = testedRandKeyInView adv kRand := rfl

@[simp]
theorem testedPairInView_withAdvRoCache {S : Setup} (c : List (Bytes × DRKey))
    (adv : KeyIndAdvCutoffState S) (kReal kRand : Bytes) :
    testedPairInView (withAdvRoCache c adv) kReal kRand = testedPairInView adv kReal kRand := rfl

@[simp]
theorem lazyStop_withAdvRoCache {S : Setup} (c : List (Bytes × DRKey))
    (adv : KeyIndAdvCutoffState S) :
    lazyStop (withAdvRoCache c adv) = lazyStop adv := rfl

@[simp]
theorem roCache_withAdvRoCache {S : Setup} (c : List (Bytes × DRKey))
    (adv : KeyIndAdvCutoffState S) :
    (withAdvRoCache c adv).shCr.base.roCache = c := rfl

/-- Cache agreement invariant between `lst5` (`testReal = false`) and `lst6` (`testReal = true`)
    in `pqxdhKeyIndAdvTagImpl false false`. -/
def LazyTagCacheAgree {S : Setup} (lst5 lst6 : KeyIndLazyState S) : Prop :=
  getLazyView lst5 = getLazyView lst6 ∧
  (∀ sec, ro5KeyInView lst5.adv sec = false →
    lookupCache lst5.adv.shCr.base.roCache sec = none) ∧
  (∀ sec, ro5KeyInView lst5.adv sec = false → testedRealKeyInView lst5.adv sec = false →
    lookupCache lst6.adv.shCr.base.roCache sec = none) ∧
  (∀ sec, testedRealKeyInView lst5.adv sec = false →
    lookupCache lst5.adv.shCr.base.roCache sec = lookupCache lst6.adv.shCr.base.roCache sec) ∧
  (∀ kRand, testedRandKeyInView lst5.adv kRand = false →
    lookupCache lst5.randCache kRand = none) ∧
  (∀ kReal kRand, testedPairInView lst5.adv kReal kRand = true →
    lookupCache lst5.randCache kRand = lookupCache lst6.adv.shCr.base.roCache kReal)

theorem lazyTagCacheAgree_empty (S : Setup) :
    LazyTagCacheAgree (KeyIndLazyState.empty S) (KeyIndLazyState.empty S) := by
  refine ⟨rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro kReal kRand h
  nomatch h

theorem finalizeKeyIndG3_eq_of_lazyTagCacheAgree {S : Setup} (P : Primitives)
    (b : Bool) (lst5 lst6 : KeyIndLazyState S) (hAg : LazyTagCacheAgree lst5 lst6) :
    finalizeKeyIndG3 S P true b lst5.adv.shCr = finalizeKeyIndG3 S P true b lst6.adv.shCr := by
  have hView : (withAdvRoCache [] lst5.adv).shCr = (withAdvRoCache [] lst6.adv).shCr :=
    congrArg KeyIndAdvCutoffState.shCr hAg.1
  dsimp only [withAdvRoCache] at hView
  rw [← finalizeKeyIndG3_withShCrRoCache S P true b ([] : List (Bytes × DRKey)) lst5.adv.shCr,
      ← finalizeKeyIndG3_withShCrRoCache S P true b ([] : List (Bytes × DRKey)) lst6.adv.shCr,
      hView]

theorem testedRealKeyInView_of_testedPairInView {S : Setup}
    (adv : KeyIndAdvCutoffState S) (kReal kRand : Bytes)
    (h : testedPairInView adv kReal kRand = true) :
    testedRealKeyInView adv kReal = true := by
  unfold testedPairInView at h
  unfold testedRealKeyInView
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨s, hs, ⟨ht, hR⟩, _⟩ | ⟨r, hr, ⟨ht, hR⟩, _⟩
  · exact Or.inl ⟨s, hs, ht, hR⟩
  · exact Or.inr ⟨r, hr, ht, hR⟩

theorem testedRandKeyInView_of_testedPairInView {S : Setup}
    (adv : KeyIndAdvCutoffState S) (kReal kRand : Bytes)
    (h : testedPairInView adv kReal kRand = true) :
    testedRandKeyInView adv kRand = true := by
  unfold testedPairInView at h
  unfold testedRandKeyInView
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with ⟨s, hs, ⟨ht, _⟩, hRd⟩ | ⟨r, hr, ⟨ht, _⟩, hRd⟩
  · exact Or.inl ⟨s, hs, ht, hRd⟩
  · exact Or.inr ⟨r, hr, ht, hRd⟩

theorem exists_testedPairInView_of_testedRealKeyInView {S : Setup}
    (adv : KeyIndAdvCutoffState S) (kReal : Bytes)
    (h : testedRealKeyInView adv kReal = true) :
    ∃ kRand, testedPairInView adv kReal kRand = true := by
  unfold testedRealKeyInView at h
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨s, hs, ht, hR⟩ | ⟨r, hr, ht, hR⟩
  · refine ⟨s.drKeyRand.rootKey, ?_⟩
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inl ⟨s, hs, ⟨ht, hR⟩, beq_self_eq_true _⟩
  · refine ⟨r.drKeyRand.rootKey, ?_⟩
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨r, hr, ⟨ht, hR⟩, beq_self_eq_true _⟩

theorem exists_testedPairInView_of_testedRandKeyInView {S : Setup}
    (adv : KeyIndAdvCutoffState S) (kRand : Bytes)
    (h : testedRandKeyInView adv kRand = true) :
    ∃ kReal, testedPairInView adv kReal kRand = true := by
  unfold testedRandKeyInView at h
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨s, hs, ht, hRd⟩ | ⟨r, hr, ht, hRd⟩
  · refine ⟨s.drKeyReal.rootKey, ?_⟩
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inl ⟨s, hs, ⟨ht, beq_self_eq_true _⟩, hRd⟩
  · refine ⟨r.drKeyReal.rootKey, ?_⟩
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨r, hr, ⟨ht, beq_self_eq_true _⟩, hRd⟩

theorem not_testedRealKeyInView_of_lazyStop_false_of_ro5KeyInView {S : Setup}
    (adv : KeyIndAdvCutoffState S) (sec : Bytes)
    (hStop : lazyStop adv = false)
    (hRo5 : ro5KeyInView adv sec = true) :
    testedRealKeyInView adv sec = false := by
  cases hT : testedRealKeyInView adv sec
  · rfl
  · exfalso
    unfold testedRealKeyInView at hT
    unfold lazyStop at hStop
    simp only [Bool.or_eq_false_iff] at hStop
    rcases hStop with ⟨⟨⟨hS1, hR1⟩, _⟩, _⟩
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hT
    rcases hT with ⟨s, hs, ht, rfl⟩ | ⟨r, hr, ht, rfl⟩
    · have hTrue : adv.shCr.base.sessions.any (fun s => s.tested && ro5KeyInView adv
        s.drKeyReal.rootKey) = true :=
        List.any_eq_true.mpr ⟨s, hs, by simp [ht, hRo5]⟩
      rw [hS1] at hTrue; nomatch hTrue
    · have hTrue : adv.shCr.base.respSessions.any (fun r => r.tested && ro5KeyInView adv
        r.drKeyReal.rootKey) = true :=
        List.any_eq_true.mpr ⟨r, hr, by simp [ht, hRo5]⟩
      rw [hR1] at hTrue; nomatch hTrue

theorem testedPair_beq_eq_of_lazyStop_false {S : Setup}
    (adv : KeyIndAdvCutoffState S) (kReal1 kRand1 kReal2 kRand2 : Bytes)
    (hStop : lazyStop adv = false)
    (h1 : testedPairInView adv kReal1 kRand1 = true)
    (h2 : testedPairInView adv kReal2 kRand2 = true) :
    (kReal1 == kReal2) = (kRand1 == kRand2) := by
  unfold lazyStop at hStop
  simp only [Bool.or_eq_false_iff] at hStop
  rcases hStop with ⟨⟨_, hSS⟩, hRR⟩
  unfold testedPairInView at h1 h2
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h1 h2
  by_contra hNe
  have hBne : ((kReal1 == kReal2) != (kRand1 == kRand2)) = true := by
    revert hNe
    cases kReal1 == kReal2 <;> cases kRand1 == kRand2 <;> intro hNe
    · exact False.elim (hNe rfl)
    · rfl
    · rfl
    · exact False.elim (hNe rfl)
  rcases h1 with ⟨s1, hs1, ⟨ht1, rfl⟩, rfl⟩ | ⟨r1, hr1, ⟨ht1, rfl⟩, rfl⟩
  · rcases h2 with ⟨s2, hs2, ⟨ht2, rfl⟩, rfl⟩ | ⟨r2, hr2, ⟨ht2, rfl⟩, rfl⟩
    · have hTrue : (adv.shCr.base.sessions.any (fun s1 => s1.tested &&
        (adv.shCr.base.sessions.any (fun s2 => s2.tested &&
          (((s1.drKeyReal.rootKey == s2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
            s2.drKeyRand.rootKey)) ||
           ((s1.sid == s2.sid) && !(s1.drKeyReal.rootKey == s2.drKeyReal.rootKey)))) ||
         adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
          ((s1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
            r2.drKeyRand.rootKey)))))) = true := by
        refine List.any_eq_true.mpr ⟨s1, hs1, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true]
        exact ⟨ht1, Or.inl (List.any_eq_true.mpr ⟨s2, hs2, by simp [ht2, hBne]⟩)⟩
      rw [hSS] at hTrue; nomatch hTrue
    · have hTrue : (adv.shCr.base.sessions.any (fun s1 => s1.tested &&
        (adv.shCr.base.sessions.any (fun s2 => s2.tested &&
          (((s1.drKeyReal.rootKey == s2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
            s2.drKeyRand.rootKey)) ||
           ((s1.sid == s2.sid) && !(s1.drKeyReal.rootKey == s2.drKeyReal.rootKey)))) ||
         adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
          ((s1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
            r2.drKeyRand.rootKey)))))) = true := by
        refine List.any_eq_true.mpr ⟨s1, hs1, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true]
        exact ⟨ht1, Or.inr (List.any_eq_true.mpr ⟨r2, hr2, by simp [ht2, hBne]⟩)⟩
      rw [hSS] at hTrue; nomatch hTrue
  · rcases h2 with ⟨s2, hs2, ⟨ht2, rfl⟩, rfl⟩ | ⟨r2, hr2, ⟨ht2, rfl⟩, rfl⟩
    · have hBneSym : ((s2.drKeyReal.rootKey == r1.drKeyReal.rootKey) !=
          (s2.drKeyRand.rootKey == r1.drKeyRand.rootKey)) = true := by
        rw [BEq.comm (a := s2.drKeyReal.rootKey), BEq.comm (a := s2.drKeyRand.rootKey)]
        exact hBne
      have hTrue : (adv.shCr.base.sessions.any (fun s1 => s1.tested &&
        (adv.shCr.base.sessions.any (fun s2 => s2.tested &&
          (((s1.drKeyReal.rootKey == s2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
            s2.drKeyRand.rootKey)) ||
           ((s1.sid == s2.sid) && !(s1.drKeyReal.rootKey == s2.drKeyReal.rootKey)))) ||
         adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
          ((s1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
            r2.drKeyRand.rootKey)))))) = true := by
        refine List.any_eq_true.mpr ⟨s2, hs2, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true]
        exact ⟨ht2, Or.inr (List.any_eq_true.mpr ⟨r1, hr1, by simp [ht1, hBneSym]⟩)⟩
      rw [hSS] at hTrue; nomatch hTrue
    · have hTrue : (adv.shCr.base.respSessions.any (fun r1 => r1.tested &&
        adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
          (((r1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (r1.drKeyRand.rootKey ==
            r2.drKeyRand.rootKey)) ||
           ((r1.sid == r2.sid) && !(r1.drKeyReal.rootKey == r2.drKeyReal.rootKey)))))) = true := by
        refine List.any_eq_true.mpr ⟨r1, hr1, ?_⟩
        simp only [Bool.and_eq_true]
        exact ⟨ht1, List.any_eq_true.mpr ⟨r2, hr2, by simp [ht2, hBne]⟩⟩
      rw [hRR] at hTrue; nomatch hTrue

theorem tested_same_sid_keys_eq_of_lazyStop_false_sessions {S : Setup}
    (adv : KeyIndAdvCutoffState S) (s1 s2 : KeyIndInitiatorEntry S)
    (hStop : lazyStop adv = false)
    (hs1 : s1 ∈ adv.shCr.base.sessions) (ht1 : s1.tested = true)
    (hs2 : s2 ∈ adv.shCr.base.sessions) (ht2 : s2.tested = true)
    (hSid : s1.sid = s2.sid) :
    s1.drKeyReal.rootKey = s2.drKeyReal.rootKey ∧ s1.drKeyRand.rootKey = s2.drKeyRand.rootKey := by
  have hReal : s1.drKeyReal.rootKey = s2.drKeyReal.rootKey := by
    by_contra hNe
    have hBeqF : (s1.drKeyReal.rootKey == s2.drKeyReal.rootKey) = false :=
      beq_eq_false_iff_ne.mpr hNe
    unfold lazyStop at hStop
    simp only [Bool.or_eq_false_iff] at hStop
    rcases hStop with ⟨⟨_, hSS⟩, _⟩
    have hTrue : (adv.shCr.base.sessions.any (fun s1 => s1.tested &&
      (adv.shCr.base.sessions.any (fun s2 => s2.tested &&
        (((s1.drKeyReal.rootKey == s2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
          s2.drKeyRand.rootKey)) ||
         ((s1.sid == s2.sid) && !(s1.drKeyReal.rootKey == s2.drKeyReal.rootKey)))) ||
       adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
        ((s1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (s1.drKeyRand.rootKey ==
          r2.drKeyRand.rootKey)))))) = true := by
      refine List.any_eq_true.mpr ⟨s1, hs1, ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨ht1, Or.inl (List.any_eq_true.mpr ⟨s2, hs2, by simp [ht2, hSid, hBeqF]⟩)⟩
    rw [hSS] at hTrue; nomatch hTrue
  have hP1 : testedPairInView adv s1.drKeyReal.rootKey s1.drKeyRand.rootKey = true := by
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inl ⟨s1, hs1, ⟨ht1, beq_self_eq_true _⟩, beq_self_eq_true _⟩
  have hP2 : testedPairInView adv s2.drKeyReal.rootKey s2.drKeyRand.rootKey = true := by
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inl ⟨s2, hs2, ⟨ht2, beq_self_eq_true _⟩, beq_self_eq_true _⟩
  have hBeq := testedPair_beq_eq_of_lazyStop_false adv _ _ _ _ hStop hP1 hP2
  rw [hReal, beq_self_eq_true] at hBeq
  exact ⟨hReal, beq_iff_eq.mp hBeq.symm⟩

theorem tested_same_sid_keys_eq_of_lazyStop_false_respSessions {S : Setup}
    (adv : KeyIndAdvCutoffState S) (r1 r2 : KeyIndRespEntry S)
    (hStop : lazyStop adv = false)
    (hr1 : r1 ∈ adv.shCr.base.respSessions) (ht1 : r1.tested = true)
    (hr2 : r2 ∈ adv.shCr.base.respSessions) (ht2 : r2.tested = true)
    (hSid : r1.sid = r2.sid) :
    r1.drKeyReal.rootKey = r2.drKeyReal.rootKey ∧ r1.drKeyRand.rootKey = r2.drKeyRand.rootKey := by
  have hReal : r1.drKeyReal.rootKey = r2.drKeyReal.rootKey := by
    by_contra hNe
    have hBeqF : (r1.drKeyReal.rootKey == r2.drKeyReal.rootKey) = false :=
      beq_eq_false_iff_ne.mpr hNe
    unfold lazyStop at hStop
    simp only [Bool.or_eq_false_iff] at hStop
    rcases hStop with ⟨_, hRR⟩
    have hTrue : (adv.shCr.base.respSessions.any (fun r1 => r1.tested &&
      adv.shCr.base.respSessions.any (fun r2 => r2.tested &&
        (((r1.drKeyReal.rootKey == r2.drKeyReal.rootKey) != (r1.drKeyRand.rootKey ==
          r2.drKeyRand.rootKey)) ||
         ((r1.sid == r2.sid) && !(r1.drKeyReal.rootKey == r2.drKeyReal.rootKey)))))) = true := by
      refine List.any_eq_true.mpr ⟨r1, hr1, ?_⟩
      simp only [Bool.and_eq_true]
      exact ⟨ht1, List.any_eq_true.mpr ⟨r2, hr2, by simp [ht2, hSid, hBeqF]⟩⟩
    rw [hRR] at hTrue; nomatch hTrue
  have hP1 : testedPairInView adv r1.drKeyReal.rootKey r1.drKeyRand.rootKey = true := by
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨r1, hr1, ⟨ht1, beq_self_eq_true _⟩, beq_self_eq_true _⟩
  have hP2 : testedPairInView adv r2.drKeyReal.rootKey r2.drKeyRand.rootKey = true := by
    unfold testedPairInView
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨r2, hr2, ⟨ht2, beq_self_eq_true _⟩, beq_self_eq_true _⟩
  have hBeq := testedPair_beq_eq_of_lazyStop_false adv _ _ _ _ hStop hP1 hP2
  rw [hReal, beq_self_eq_true] at hBeq
  exact ⟨hReal, beq_iff_eq.mp hBeq.symm⟩

theorem lazyStop_runLazyPost_false_false {S : Setup}
    (post : LazyPost) (lst : KeyIndLazyState S)
    {y : KeyIndResponse × KeyIndLazyState S}
    (hy : y ∈ support (runLazyPost false false S post lst)) :
    lazyStop y.2.adv = lazyStop lst.adv := by
  cases post with
  | done resp =>
    simp only [runLazyPost, support_pure, Set.mem_singleton_iff] at hy
    subst hy; rfl
  | evalRo sec mkResp =>
    simp only [runLazyPost, CacheLens.eval, roLens, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, c'⟩, _, rfl⟩
    rfl
  | evalRand pid mkResp =>
    simp only [runLazyPost, CacheLens.eval, randLens, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, c'⟩, _, rfl⟩
    rfl
  | handshake isHonest freshResp unfreshResp secrets pid? =>
    cases pid? <;>
    · dsimp only [runLazyPost, evalRoIf, evalRandIf] at hy
      cases isHonest
      · simp only [Bool.not_false, Bool.true_or, ↓reduceIte, CacheLens.eval, roLens,
          bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff] at hy
        rcases hy with ⟨⟨dk, c'⟩, _, rfl⟩
        rfl
      · simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
          support_pure, Set.mem_singleton_iff] at hy
        subst hy; rfl

theorem lazyTagCacheAgree_setLazyView_of_noCache {S : Setup}
    (lst5 lst6 : KeyIndLazyState S) (adv' : KeyIndAdvCutoffState S)
    (hAg : LazyTagCacheAgree lst5 lst6)
    (hRo5Mono : ∀ sec, ro5KeyInView lst5.adv sec = true → ro5KeyInView adv' sec = true)
    (hTestReal : ∀ sec, testedRealKeyInView adv' sec = testedRealKeyInView lst5.adv sec)
    (hTestRand : ∀ kRand, testedRandKeyInView adv' kRand = testedRandKeyInView lst5.adv kRand)
    (hTestPair : ∀ kReal kRand, testedPairInView adv' kReal kRand = testedPairInView lst5.adv kReal
      kRand) :
    LazyTagCacheAgree (setLazyView adv' lst5) (setLazyView adv' lst6) := by
  rcases hAg with ⟨_, hRo5None, hRo6None, hRoEq, hRandNone, hPairEq⟩
  have hRo5False : ∀ sec, ro5KeyInView adv' sec = false → ro5KeyInView lst5.adv sec = false := by
    intro sec hF
    cases h : ro5KeyInView lst5.adv sec
    · rfl
    · rw [hRo5Mono sec h] at hF; nomatch hF
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro sec hF
    dsimp only [setLazyView] at hF ⊢
    rw [ro5KeyInView_withAdvRoCache] at hF
    exact hRo5None sec (hRo5False sec hF)
  · intro sec hF hTF
    dsimp only [setLazyView] at hF hTF ⊢
    rw [ro5KeyInView_withAdvRoCache] at hF
    rw [testedRealKeyInView_withAdvRoCache, hTestReal sec] at hTF
    exact hRo6None sec (hRo5False sec hF) hTF
  · intro sec hTF
    dsimp only [setLazyView] at hTF ⊢
    rw [testedRealKeyInView_withAdvRoCache, hTestReal sec] at hTF
    exact hRoEq sec hTF
  · intro kRand hRF
    dsimp only [setLazyView] at hRF ⊢
    rw [testedRandKeyInView_withAdvRoCache, hTestRand kRand] at hRF
    exact hRandNone kRand hRF
  · intro kReal kRand hPT
    dsimp only [setLazyView] at hPT ⊢
    rw [testedPairInView_withAdvRoCache, hTestPair kReal kRand] at hPT
    exact hPairEq kReal kRand hPT

theorem relCoupled_evalRo_setLazyView {S : Setup}
    (lst5 lst6 : KeyIndLazyState S) (adv' : KeyIndAdvCutoffState S)
    (sec : Bytes) (mkResp : DRKey → KeyIndResponse)
    (hAg : LazyTagCacheAgree lst5 lst6)
    (hSecIn : ro5KeyInView adv' sec = true)
    (hRo5Mono : ∀ k, ro5KeyInView lst5.adv k = true → ro5KeyInView adv' k = true)
    (hTestReal : ∀ k, testedRealKeyInView adv' k = testedRealKeyInView lst5.adv k)
    (hTestRand : ∀ kRand, testedRandKeyInView adv' kRand = testedRandKeyInView lst5.adv kRand)
    (hTestPair : ∀ kReal kRand, testedPairInView adv' kReal kRand = testedPairInView lst5.adv kReal
      kRand) :
    RelCoupled
      (fun y5 y6 =>
        (y5.1 = y6.1 ∧ LazyTagCacheAgree y5.2 y6.2) ∨
        (lazyStop y5.2.adv = true ∧ lazyStop y6.2.adv = true))
      (runLazyPost false false S (.evalRo sec mkResp) (setLazyView adv' lst5))
      (runLazyPost false false S (.evalRo sec mkResp) (setLazyView adv' lst6)) := by
  by_cases hStop : lazyStop adv' = true
  · refine RelCoupled.of_support _ _ (fun y5 hy5 y6 hy6 => Or.inr ⟨?_, ?_⟩)
    · rw [lazyStop_runLazyPost_false_false _ _ hy5]
      exact hStop
    · rw [lazyStop_runLazyPost_false_false _ _ hy6]
      exact hStop
  · have hStopF : lazyStop adv' = false := Bool.eq_false_iff.mpr hStop
    have hSecNotTested' : testedRealKeyInView adv' sec = false :=
      not_testedRealKeyInView_of_lazyStop_false_of_ro5KeyInView adv' sec hStopF hSecIn
    have hSecNotTested : testedRealKeyInView lst5.adv sec = false := by
      rw [← hTestReal sec]; exact hSecNotTested'
    rcases hAg with ⟨_, hRo5None, hRo6None, hRoEq, hRandNone, hPairEq⟩
    have hRo5False : ∀ k, ro5KeyInView adv' k = false → ro5KeyInView lst5.adv k = false := by
      intro k hF
      cases h : ro5KeyInView lst5.adv k
      · rfl
      · rw [hRo5Mono k h] at hF; nomatch hF
    have hLookEq : lookupCache lst5.adv.shCr.base.roCache sec =
        lookupCache lst6.adv.shCr.base.roCache sec := hRoEq sec hSecNotTested
    unfold runLazyPost CacheLens.eval
    simp only [roLens, setLazyView, roCache_withAdvRoCache, bind_assoc, pure_bind]
    refine (relCoupled_evalCache_of_lookup_eq
      lst5.adv.shCr.base.roCache lst6.adv.shCr.base.roCache sec sec hLookEq).bind ?_
    intro p1 p2 ⟨hDk, hEqSec, hRest1, hRest2⟩
    rcases p1 with ⟨dk1, c5'⟩
    rcases p2 with ⟨dk2, c6'⟩
    dsimp only at hDk hEqSec hRest1 hRest2
    subst hDk
    refine RelCoupled.of_pure (Or.inl ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩)
    · intro q hF
      simp only [ro5KeyInView_withAdvRoCache] at hF
      simp only [roCache_withAdvRoCache]
      have hne : (sec == q) = false := by
        cases h : sec == q
        · rfl
        · have hEqQ : sec = q := beq_iff_eq.mp h
          subst hEqQ; rw [hSecIn] at hF; nomatch hF
      rw [hRest1 q hne]
      exact hRo5None q (hRo5False q hF)
    · intro q hF hTF
      simp only [ro5KeyInView_withAdvRoCache] at hF
      simp only [testedRealKeyInView_withAdvRoCache, hTestReal q] at hTF
      simp only [roCache_withAdvRoCache]
      have hne : (sec == q) = false := by
        cases h : sec == q
        · rfl
        · have hEqQ : sec = q := beq_iff_eq.mp h
          subst hEqQ; rw [hSecIn] at hF; nomatch hF
      rw [hRest2 q hne]
      exact hRo6None q (hRo5False q hF) hTF
    · intro q hTF
      simp only [testedRealKeyInView_withAdvRoCache, hTestReal q] at hTF
      simp only [roCache_withAdvRoCache]
      by_cases h : (sec == q) = true
      · have hEqQ : sec = q := beq_iff_eq.mp h
        subst hEqQ; exact hEqSec
      · have hne : (sec == q) = false := Bool.eq_false_iff.mpr h
        rw [hRest1 q hne, hRest2 q hne]
        exact hRoEq q hTF
    · intro kRand hRF
      simp only [testedRandKeyInView_withAdvRoCache, hTestRand kRand] at hRF
      exact hRandNone kRand hRF
    · intro kReal kRand hPT
      simp only [testedPairInView_withAdvRoCache] at hPT
      simp only [roCache_withAdvRoCache]
      have hne : (sec == kReal) = false := by
        cases h : sec == kReal
        · rfl
        · have hEqK : sec = kReal := beq_iff_eq.mp h
          subst hEqK
          have hT := testedRealKeyInView_of_testedPairInView adv' sec kRand hPT
          rw [hSecNotTested'] at hT; nomatch hT
      rw [hRest2 kReal hne]
      rw [hTestPair kReal kRand] at hPT
      exact hPairEq kReal kRand hPT

end Proofs.SignalPqxdh.Security
