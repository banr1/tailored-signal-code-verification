/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B2
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops4to5B
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key Clean-Session Invariant at Receive Stage `G5`

Proves that `AuthCleanSessionInv` is preserved by the split-stage `Auth` hybrid oracles over
`pqxdhAuthImpl1KeyG` when the receive stage is `.g5`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt
  initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt RelProbUpToBad
    simulateQ_relProbUpToBad evalDist_simulateQ_eq_of_step_or_bad)

theorem authCleanSessionInv_pqxdhAuthHybridSplitKoskImpl_g5_1Key {S : Setup}
    (sendStage : AuthHybridStage) (useRo checkAuth : Bool)
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S)
    (hInv : AuthCleanSessionInv P S hst)
    (resp : AuthResponse) (hst' : AuthHybridState S)
    (hmem : (resp, hst') ∈
      support ((pqxdhAuthHybridSplitKoskImpl1Key sendStage .g5 useRo checkAuth S P q).run hst)) :
    AuthCleanSessionInv P S hst' := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h : bundle.opkB?.isNone = true
    · simp only [ h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [runAuthHybridSendKosk_eq] at hmem
      exact authCleanSessionInv_evalAuthHybridSendKosk sendStage useRo P hWF
        (.sendOPK u i) u bundle m0 m1 hst hInv resp hst' hmem
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h : bundle.opkB?.isSome = true
    · simp only [ h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [runAuthHybridSendKosk_eq] at hmem
      exact authCleanSessionInv_evalAuthHybridSendKosk sendStage useRo P hWF
        (.sendNoOPK u i) u bundle m0 m1 hst hInv resp hst' hmem
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq1Key] at hmem
    unfold prepareAuthHybridRecvOPK at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                     msg.hdr.pqspkId == UInt32.ofNat j.val &&
                     msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                     msg.hdr.ikAPk.length == 32 &&
                     msg.hdr.ekAPk.length == 32 &&
                     msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
        · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
          cases hp : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          | some kp =>
            rcases kp with ⟨_, kEntry⟩
            cases hb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some bp =>
              rcases bp with ⟨idxB, bEntry⟩
              cases ho : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
                o.val)) with
              | none =>
                simp only [hp, hb, ho, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              | some op =>
                rcases op with ⟨_, oEntry⟩
                simp only [hp, hb, ho] at hmem
                by_cases h4 : oEntry.consumed = true
                · simp only [ h4, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                    ] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hmem
                  by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                    msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                                 !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                  · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                      ] at hmem
                    rcases hmem with ⟨_, rfl⟩; exact hInv
                  · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                    cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                    | none =>
                      simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                      rcases hmem with ⟨_, rfl⟩; exact hInv
                    | some ss =>
                      simp only [hdec, mem_support_fmap_iff] at hmem
                      rcases hmem with ⟨res?, hres_mem, hfin⟩
                      have hst_eq : hst' =
                        (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry
                          (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                            msg.hdr.spkId msg.hdr.ekAPk).2
                          msg { hst with recvKemRecs := _ :: hst.recvKemRecs } res?).2 :=
                        (congrArg Prod.snd hfin).symm
                      rw [hst_eq]
                      simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true,
                          beq_iff_eq] at h1
                      rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                      rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                      have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                        msg.hdr.ekAPk) ∉ hst.base.seenKyberBaseKeys := by
                        unfold checkAndMarkKyberBaseKeySeen at hReplay
                        dsimp only at hReplay
                        rw [hPqspkId, hSpkId] at hReplay
                        intro hm
                        have hc := List.contains_iff_mem.mpr hm
                        rw [hc] at hReplay
                        cases hReplay
                      have hTriples' : (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                        msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2 =
                          (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                            msg.hdr.ekAPk) :: hst.base.seenKyberBaseKeys := by
                        unfold checkAndMarkKyberBaseKeySeen
                        simp [hPqspkId, hSpkId, hNotUsed]
                      exact authCleanSessionInv_finishAuthHybridRecvOPK checkAuth P hWF k j o
                        kEntry bEntry oEntry _ msg
                        { hst with recvKemRecs := _ :: hst.recvKemRecs }
                        res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                        (by dsimp only; exact mem_of_find?_fst_beq hp)
                        (by dsimp only; exact mem_of_find?_fst_beq hb)
                        hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                          subst hres_eq
                          exact mem_support_evalAuthHybridRecvSchedule_g5_honest useRo P _
                            kEntry bEntry (some oEntry.opkPk) _ msg dk rk ck pt ro rro hHon
                              hres_mem)
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq1Key] at hmem
    unfold prepareAuthHybridRecvNoOPK at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                     msg.hdr.pqspkId == UInt32.ofNat j.val &&
                     msg.hdr.opkId? == none &&
                     msg.hdr.ikAPk.length == 32 &&
                     msg.hdr.ekAPk.length == 32 &&
                     msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
        · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
          cases hp : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          | some kp =>
            rcases kp with ⟨_, kEntry⟩
            cases hb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some bp =>
              rcases bp with ⟨idxB, bEntry⟩
              simp only [hp, hb] at hmem
              by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                msg.hdr.spkId msg.hdr.ekAPk).1 ||
                             !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
              · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                  ] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                | none =>
                  simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                | some ss =>
                  simp only [hdec, mem_support_fmap_iff] at hmem
                  rcases hmem with ⟨res?, hres_mem, hfin⟩
                  have hst_eq : hst' = (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry
                      (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).2
                      msg { hst with recvKemRecs := _ :: hst.recvKemRecs } res?).2 :=
                    (congrArg Prod.snd hfin).symm
                  rw [hst_eq]
                  simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq
                    ] at h1
                  rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                  simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                  rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                  have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                    msg.hdr.ekAPk) ∉ hst.base.seenKyberBaseKeys := by
                    unfold checkAndMarkKyberBaseKeySeen at hReplay
                    dsimp only at hReplay
                    rw [hPqspkId, hSpkId] at hReplay
                    intro hm
                    have hc := List.contains_iff_mem.mpr hm
                    rw [hc] at hReplay
                    cases hReplay
                  have hTriples' : (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                    msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2 =
                      (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                        msg.hdr.ekAPk) :: hst.base.seenKyberBaseKeys := by
                    unfold checkAndMarkKyberBaseKeySeen
                    simp [hPqspkId, hSpkId, hNotUsed]
                  exact authCleanSessionInv_finishAuthHybridRecvNoOPK checkAuth P hWF k j l
                    kEntry bEntry _ msg
                    { hst with recvKemRecs := _ :: hst.recvKemRecs }
                    res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                    (by dsimp only; exact mem_of_find?_fst_beq hp)
                    (by dsimp only; exact mem_of_find?_fst_beq hb)
                    hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                      subst hres_eq
                      exact mem_support_evalAuthHybridRecvSchedule_g5_honest useRo P _
                        kEntry bEntry none _ msg dk rk ck pt ro rro hHon hres_mem)
  | initPrin u =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, _, _, rfl⟩
      refine ⟨hInv.bundles_canon, hInv.bundles_nodup, ?_, ?_, hInv.no_false_win⟩
      · dsimp only
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hInv.principals_nodup⟩
        intro hmem_fst
        rw [List.mem_map] at hmem_fst
        rcases hmem_fst with ⟨⟨idx0, e0⟩, hmem0, hfst0⟩
        dsimp only at hfst0
        subst hfst0
        exact h (List.any_eq_true.mpr ⟨(u.val, e0), hmem0, by simp⟩)
      · intro s hs
        exact IdealSessionClean.mono (hInv.sessions_inv s hs)
          (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
          (List.Subset.refl _) (List.Subset.refl _)
          (fun k pE hm hc => ⟨pE, List.mem_cons_of_mem _ hm, hc⟩)
  | corruptIK u =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    cases h : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    | some p =>
      rcases p with ⟨_, entry⟩
      simp [h, StateT.run_set] at hbase
      rcases hbase with ⟨_, rfl⟩
      refine ⟨hInv.bundles_canon, hInv.bundles_nodup, ?_, ?_, hInv.no_false_win⟩
      · dsimp only
        rw [List.map_map]
        have hEq :
            List.map (Prod.fst ∘ fun (x : Nat × PrincipalEntry) =>
              if x.1 = u.val then (x.1, { x.2 with corrupted :=
                true }) else x) hst.base.principals =
            List.map Prod.fst hst.base.principals := by
          apply List.map_congr_left
          rintro ⟨idx, e⟩ _
          dsimp only [Function.comp_apply]
          split <;> rfl
        rw [hEq]
        exact hInv.principals_nodup
      · intro s hs
        exact IdealSessionClean.mono (hInv.sessions_inv s hs)
          (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
          (List.Subset.refl _) (List.Subset.refl _)
          (fun k pE hm hc => by
            dsimp only
            by_cases hku : k = u.val
            · refine ⟨{ pE with corrupted := true }, ?_, rfl⟩
              have hmem_map := List.mem_map_of_mem (f := fun (x : Nat × PrincipalEntry) =>
                if x.1 = u.val then (x.1, { x.2 with corrupted := true }) else x) hm
              simpa [hku] using hmem_map
            · refine ⟨pE, ?_, hc⟩
              have hmem_map := List.mem_map_of_mem (f := fun (x : Nat × PrincipalEntry) =>
                if x.1 = u.val then (x.1, { x.2 with corrupted := true }) else x) hm
              simpa [hku] using hmem_map)
  | genSPK u j =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hbase
      cases hp : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [hp] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
      | some p =>
        rcases p with ⟨_, uEntry⟩
        simp only [hp, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hbase
        rcases hbase with ⟨spkSk, _, r1, _, ⟨pqspkPk, pqspkSk⟩, _, r2, _, _, rfl⟩
        refine ⟨?_, ?_, hInv.principals_nodup, ?_, ?_⟩
        · intro kj b hmem_b
          rcases List.mem_cons.mp hmem_b with hhead | htail
          · cases hhead
            exact hWF.canon_base spkSk
          · exact hInv.bundles_canon kj b htail
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, hInv.bundles_nodup⟩
          intro hmem_fst
          rw [List.mem_map] at hmem_fst
          rcases hmem_fst with ⟨⟨kj0, b0⟩, hmem0, hfst0⟩
          dsimp only at hfst0
          subst hfst0
          have hany : (hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true := by
            rw [List.any_eq_true]
            exact ⟨((u.val, j.val), b0), hmem0, by simp⟩
          exact h hany
        · intro s hs
          exact IdealSessionClean.mono (hInv.sessions_inv s hs)
            (List.subset_cons_self _ _) (List.Subset.refl _) (List.Subset.refl _)
            (List.Subset.refl _) (List.Subset.refl _)
        · intro hBadSig hKemColl
          have hKemOld : hasKemPkCollisionAuth hst = false := by
            change hasDuplicateBytes (pqspkPk :: allHonestKemPksAuth hst) = false at hKemColl
            simp only [hasDuplicateBytes, Bool.or_eq_false_iff] at hKemColl
            exact hKemColl.2
          exact hInv.no_false_win hBadSig hKemOld
  | genOPK u j o =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, _, _, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | registerKey sk =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    cases h : registerAdvKey P hst.base.advKeys sk with
    | none => simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    | some kp =>
      rcases kp with ⟨_, _⟩
      simp [h, StateT.run_set] at hbase
      rcases hbase with ⟨_, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | roQuery secrets =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (!useRo) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨⟨_, _⟩, _, _, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | roRootQuery rk dh =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (!useRo) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨⟨_, _⟩, _, _, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | revealDhSecrets =>
    unfold pqxdhAuthHybridSplitKoskImpl1Key pqxdhAuthImpl1KeyG at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : useRo = true <;> (simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv)

theorem authCleanSessionInv_fullSplitFixedImpl_g5_1Key {S : Setup}
    (sendStage : AuthHybridStage) (useRo checkAuth : Bool)
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hInv : AuthCleanSessionInv P S hst.toAuthHybridState)
    (resp : (unifSpec + authSpec S).Range q) (hst' : AuthHybridStateFixed S)
    (hmem : (resp, hst') ∈
      support ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S)
        ProbComp) +
        pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 useRo checkAuth S P) q).run hst)) :
    AuthCleanSessionInv P S hst'.toAuthHybridState := by
  cases q with
  | inl uq =>
    change (resp, hst') ∈
      support ((monadLift (QueryImpl.ofLift unifSpec ProbComp uq) : StateT (AuthHybridStateFixed S)
        ProbComp _).run hst) at hmem
    rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨_, _, h2⟩
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
    rcases h2 with ⟨_, rfl⟩
    exact hInv
  | inr kq =>
    change (resp, hst') ∈
      support ((pqxdhAuthHybridSplitFixedImpl1Key sendStage .g5 useRo checkAuth S P kq).run hst) at hmem
    have hIdeal : (AuthHybridStage.g5).idealMsgKeys = true := rfl
    have hApply :=
      authCleanSessionInv_pqxdhAuthHybridSplitKoskImpl_g5_1Key sendStage useRo checkAuth P hWF kq
        hst.toAuthHybridState hInv
    cases kq with
    | recvOPK k j o msg =>
      clear hApply
      unfold pqxdhAuthHybridSplitFixedImpl1Key at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind,
        pqxdhAuthHybridFixedImpl_recvOPK_eq1Key .g5 hIdeal] at hmem
      unfold prepareAuthHybridRecvOPK at hmem
      by_cases h0 : (checkAuth && hst.toAuthHybridState.base.hasWonAuth) = true
      { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv }
      simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                       msg.hdr.pqspkId == UInt32.ofNat j.val &&
                       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                       msg.hdr.ikAPk.length == 32 &&
                       msg.hdr.ekAPk.length == 32 &&
                       msg.ephAPk.length == 32)) = true
      · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h2 : (hst.toAuthHybridState.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
        · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
          · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
            cases hp : hst.toAuthHybridState.base.principals.find? (fun (idx,
              _) => idx == k.val) with
            | none =>
              simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some kp =>
              rcases kp with ⟨_, kEntry⟩
              cases hb : hst.toAuthHybridState.base.spkBundles.find? (fun (idx,
                _) => idx == (k.val, j.val)) with
              | none =>
                simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              | some bp =>
                rcases bp with ⟨idxB, bEntry⟩
                cases ho : hst.toAuthHybridState.base.opkEntries.find? (fun (idx,
                  _) => idx == (k.val, j.val, o.val)) with
                | none =>
                  simp only [hp, hb, ho, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                | some op =>
                  rcases op with ⟨_, oEntry⟩
                  simp only [hp, hb, ho] at hmem
                  by_cases h4 : oEntry.consumed = true
                  · simp only [ h4, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                      ] at hmem
                    rcases hmem with ⟨_, rfl⟩; exact hInv
                  · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hmem
                    by_cases h5 : (!(checkAndMarkKyberBaseKeySeen
                      hst.toAuthHybridState.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).1 ||
                                   !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                    · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff,
                          Prod.mk.injEq] at hmem
                      rcases hmem with ⟨_, rfl⟩; exact hInv
                    · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                      cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                      | none =>
                        simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                        rcases hmem with ⟨_, rfl⟩; exact hInv
                      | some ss =>
                        simp only [hdec, mem_support_fmap_iff] at hmem
                        rcases hmem with ⟨⟨res?, mkSaltCache'⟩, hres_mem, hfin⟩
                        have hst_eq : hst'.toAuthHybridState =
                          (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry
                            (checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys k.val
                              msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                            msg { hst.toAuthHybridState with recvKemRecs :=
                              _ :: hst.toAuthHybridState.recvKemRecs } res?).2 :=
                          congrArg AuthHybridStateFixed.toAuthHybridState (congrArg Prod.snd
                            hfin).symm
                        rw [hst_eq]
                        simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true,
                            beq_iff_eq] at h1
                        rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                        rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                        have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                          msg.hdr.ekAPk) ∉ hst.toAuthHybridState.base.seenKyberBaseKeys := by
                          unfold checkAndMarkKyberBaseKeySeen at hReplay
                          dsimp only at hReplay
                          rw [hPqspkId, hSpkId] at hReplay
                          intro hm
                          have hc := List.contains_iff_mem.mpr hm
                          rw [hc] at hReplay
                          cases hReplay
                        have hTriples' : (checkAndMarkKyberBaseKeySeen
                          hst.toAuthHybridState.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                            msg.hdr.spkId msg.hdr.ekAPk).2 =
                            (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                              msg.hdr.ekAPk) :: hst.toAuthHybridState.base.seenKyberBaseKeys := by
                          unfold checkAndMarkKyberBaseKeySeen
                          simp [hPqspkId, hSpkId, hNotUsed]
                        exact authCleanSessionInv_finishAuthHybridRecvOPK checkAuth P hWF k j o
                          kEntry bEntry oEntry _ msg
                          { hst.toAuthHybridState with recvKemRecs :=
                            _ :: hst.toAuthHybridState.recvKemRecs }
                          res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                          (by dsimp only; exact mem_of_find?_fst_beq hp)
                          (by dsimp only; exact mem_of_find?_fst_beq hb)
                          hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                            subst hres_eq
                            exact mem_support_evalAuthFixedRecvScheduleCached_g5_honest useRo P _
                              hst.recvCount hst.mkSaltCache kEntry bEntry (some oEntry.opkPk) _ msg
                                dk rk ck pt ro rro mkSaltCache' hHon hres_mem)
    | recvNoOPK k j l msg =>
      clear hApply
      unfold pqxdhAuthHybridSplitFixedImpl1Key at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind,
        pqxdhAuthHybridFixedImpl_recvNoOPK_eq1Key .g5 hIdeal] at hmem
      unfold prepareAuthHybridRecvNoOPK at hmem
      by_cases h0 : (checkAuth && hst.toAuthHybridState.base.hasWonAuth) = true
      { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv }
      simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                       msg.hdr.pqspkId == UInt32.ofNat j.val &&
                       msg.hdr.opkId? == none &&
                       msg.hdr.ikAPk.length == 32 &&
                       msg.hdr.ekAPk.length == 32 &&
                       msg.ephAPk.length == 32)) = true
      · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h2 : (hst.toAuthHybridState.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) =
          true
        · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
          · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
            cases hp : hst.toAuthHybridState.base.principals.find? (fun (idx,
              _) => idx == k.val) with
            | none =>
              simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some kp =>
              rcases kp with ⟨_, kEntry⟩
              cases hb : hst.toAuthHybridState.base.spkBundles.find? (fun (idx,
                _) => idx == (k.val, j.val)) with
              | none =>
                simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              | some bp =>
                rcases bp with ⟨idxB, bEntry⟩
                simp only [hp, hb] at hmem
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys
                  k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                    ] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                  cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none =>
                    simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                    rcases hmem with ⟨_, rfl⟩; exact hInv
                  | some ss =>
                    simp only [hdec, mem_support_fmap_iff] at hmem
                    rcases hmem with ⟨⟨res?, mkSaltCache'⟩, hres_mem, hfin⟩
                    have hst_eq : hst'.toAuthHybridState =
                      (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry
                        (checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys k.val
                          msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                        msg { hst.toAuthHybridState with recvKemRecs :=
                          _ :: hst.toAuthHybridState.recvKemRecs } res?).2 :=
                      congrArg AuthHybridStateFixed.toAuthHybridState (congrArg Prod.snd hfin).symm
                    rw [hst_eq]
                    simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq
                      ] at h1
                    rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                    rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                    have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                      msg.hdr.ekAPk) ∉ hst.toAuthHybridState.base.seenKyberBaseKeys := by
                      unfold checkAndMarkKyberBaseKeySeen at hReplay
                      dsimp only at hReplay
                      rw [hPqspkId, hSpkId] at hReplay
                      intro hm
                      have hc := List.contains_iff_mem.mpr hm
                      rw [hc] at hReplay
                      cases hReplay
                    have hTriples' : (checkAndMarkKyberBaseKeySeen
                      hst.toAuthHybridState.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).2 =
                        (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                          msg.hdr.ekAPk) :: hst.toAuthHybridState.base.seenKyberBaseKeys := by
                      unfold checkAndMarkKyberBaseKeySeen
                      simp [hPqspkId, hSpkId, hNotUsed]
                    exact authCleanSessionInv_finishAuthHybridRecvNoOPK checkAuth P hWF k j l
                      kEntry bEntry _ msg
                      { hst.toAuthHybridState with recvKemRecs :=
                        _ :: hst.toAuthHybridState.recvKemRecs }
                      res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                      (by dsimp only; exact mem_of_find?_fst_beq hp)
                      (by dsimp only; exact mem_of_find?_fst_beq hb)
                      hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                        subst hres_eq
                        exact mem_support_evalAuthFixedRecvScheduleCached_g5_honest useRo P _
                          hst.recvCount hst.mkSaltCache kEntry bEntry none _ msg dk rk ck pt ro rro
                            mkSaltCache' hHon hres_mem)
    | sendOPK u i bundle m0 m1 | sendNoOPK u i bundle m0 m1 | initPrin u | corruptIK u
    | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets | roRootQuery rk dh
    | revealDhSecrets =>
      unfold pqxdhAuthHybridSplitFixedImpl1Key at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get,
        StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨r0, hst0⟩, hmem0, _, rfl⟩
      exact hApply r0 hst0 hmem0

end SignalPqxdh.Security
