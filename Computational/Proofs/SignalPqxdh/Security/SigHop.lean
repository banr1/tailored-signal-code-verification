/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.SigHopC
import Computational.Proofs.SignalPqxdh.Security.Collisions
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Bad-Signature Hop for `KeyInd` and `HndlKeyInd`

Bounds the advantage change from adding the bad-signature abort (`G0_1 → G1`, `H0_1 → H1`) by
`N_id * SigEufCma` via a per-principal signature-forgery reduction and union bound, and combines
it with the EC-collision hop.
-/

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

def noOpkSlotFlatIdx (S : Setup) (p : Nat × Nat × Nat) : Nat :=
  (p.1 * S.N_recv + p.2.1) * S.N_no_opk + p.2.2

theorem noOpkSlotFlatIdx_lt (S : Setup) {u j l : Nat}
    (hu : u < S.N_id) (hj : j < S.N_recv) (hl : l < S.N_no_opk) :
    noOpkSlotFlatIdx S (u, j, l) < S.N_no_opk_tot := by
  unfold noOpkSlotFlatIdx Setup.N_no_opk_tot Setup.N_spk_tot
  have h_uj : u * S.N_recv + j < S.N_id * S.N_recv := spkSlotFlatIdx_lt S hu hj
  have h_uj1 : u * S.N_recv + j + 1 ≤ S.N_id * S.N_recv := Nat.succ_le_of_lt h_uj
  calc (u * S.N_recv + j) * S.N_no_opk + l
      < (u * S.N_recv + j) * S.N_no_opk + S.N_no_opk := Nat.add_lt_add_left hl _
    _ = (u * S.N_recv + j + 1) * S.N_no_opk := by ring
    _ ≤ (S.N_id * S.N_recv) * S.N_no_opk := Nat.mul_le_mul_right S.N_no_opk h_uj1
    _ = S.N_id * S.N_recv * S.N_no_opk := rfl

theorem noOpkSlotFlatIdx_inj (S : Setup) {k1 k2 : Nat × Nat × Nat}
    (hj1 : k1.2.1 < S.N_recv) (hl1 : k1.2.2 < S.N_no_opk)
    (hj2 : k2.2.1 < S.N_recv) (hl2 : k2.2.2 < S.N_no_opk)
    (heq : noOpkSlotFlatIdx S k1 = noOpkSlotFlatIdx S k2) : k1 = k2 := by
  rcases k1 with ⟨u1, j1, l1⟩
  rcases k2 with ⟨u2, j2, l2⟩
  dsimp [noOpkSlotFlatIdx] at hj1 hl1 hj2 hl2 heq
  have hdiv1 : ((u1 * S.N_recv + j1) * S.N_no_opk + l1) / S.N_no_opk = u1 * S.N_recv + j1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt hl1,
        Nat.add_zero]
  have hdiv2 : ((u2 * S.N_recv + j2) * S.N_no_opk + l2) / S.N_no_opk = u2 * S.N_recv + j2 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt hl2,
        Nat.add_zero]
  have huj : spkSlotFlatIdx S (u1, j1) = spkSlotFlatIdx S (u2, j2) := by
    dsimp [spkSlotFlatIdx]; rw [← hdiv1, ← hdiv2, heq]
  have hpair := spkSlotFlatIdx_inj S hj1 hj2 huj
  injection hpair with hu hj
  subst hu; subst hj
  have hl : l1 = l2 := Nat.add_left_cancel heq
  subst hl
  rfl

def ValidUsedRecvOpk (S : Setup) (used : List (Nat × Nat × Nat)) : Prop :=
  (∀ x ∈ used, x.1 < S.N_id ∧ x.2.1 < S.N_recv ∧ x.2.2 < S.N_opk) ∧
  (used.map (opkSlotFlatIdx S)).Nodup

def ValidUsedRecvNoOpk (S : Setup) (used : List (Nat × Nat × Nat)) : Prop :=
  (∀ x ∈ used, x.1 < S.N_id ∧ x.2.1 < S.N_recv ∧ x.2.2 < S.N_no_opk) ∧
  (used.map (noOpkSlotFlatIdx S)).Nodup

theorem validUsedRecvOpk_cons (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (used : List (Nat × Nat × Nat))
    (hV : ValidUsedRecvOpk S used)
    (hFresh : used.contains (k.val, j.val, o.val) = false) :
    ValidUsedRecvOpk S ((k.val, j.val, o.val) :: used) := by
  have hnot_in : opkSlotFlatIdx S (k.val, j.val, o.val) ∉ used.map (opkSlotFlatIdx S) := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨x, hx_mem, hx_eq⟩
    have hx_bounds := hV.1 x hx_mem
    have hxeq : x = (k.val, j.val, o.val) :=
      opkSlotFlatIdx_inj S hx_bounds.2.1 hx_bounds.2.2 j.isLt o.isLt hx_eq
    subst hxeq
    have hcont : used.contains (k.val, j.val, o.val) = true := List.contains_iff_mem.mpr hx_mem
    rw [hFresh] at hcont; cases hcont
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ⟨k.isLt, j.isLt, o.isLt⟩
    · exact hV.1 x hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

theorem validUsedRecvNoOpk_cons (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (used : List (Nat × Nat × Nat))
    (hV : ValidUsedRecvNoOpk S used)
    (hFresh : used.contains (k.val, j.val, l.val) = false) :
    ValidUsedRecvNoOpk S ((k.val, j.val, l.val) :: used) := by
  have hnot_in : noOpkSlotFlatIdx S (k.val, j.val, l.val) ∉ used.map (noOpkSlotFlatIdx S) := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨x, hx_mem, hx_eq⟩
    have hx_bounds := hV.1 x hx_mem
    have hxeq : x = (k.val, j.val, l.val) :=
      noOpkSlotFlatIdx_inj S hx_bounds.2.1 hx_bounds.2.2 j.isLt l.isLt hx_eq
    subst hxeq
    have hcont : used.contains (k.val, j.val, l.val) = true := List.contains_iff_mem.mpr hx_mem
    rw [hFresh] at hcont; cases hcont
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ⟨k.isLt, j.isLt, l.isLt⟩
    · exact hV.1 x hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

def ValidKeyIndResp (S : Setup) (st : KeyIndState S) : Prop :=
  ValidUsedRecvOpk S st.usedRecvOPK ∧
  ValidUsedRecvNoOpk S st.usedRecvNoOPK ∧
  st.respSessions.length ≤ st.usedRecvOPK.length + st.usedRecvNoOPK.length

theorem validKeyIndResp_empty (S : Setup) (secb : Bool) :
    ValidKeyIndResp S (KeyIndState.empty S secb) :=
  ⟨⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   Nat.le_refl 0⟩

theorem validKeyIndResp_length_le (S : Setup) (st : KeyIndState S)
    (hR : ValidKeyIndResp S st) :
    st.respSessions.length ≤ S.N_sess_tot := by
  have hsub1 : (st.usedRecvOPK.map (opkSlotFlatIdx S)).Subperm (List.range S.N_opk_tot) :=
    hR.1.2.subperm (fun y hy => by
      rw [List.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩
      have hb := hR.1.1 x hx
      exact List.mem_range.mpr (opkSlotFlatIdx_lt S hb.1 hb.2.1 hb.2.2))
  have hsub2 : (st.usedRecvNoOPK.map (noOpkSlotFlatIdx S)).Subperm (List.range S.N_no_opk_tot) :=
    hR.2.1.2.subperm (fun y hy => by
      rw [List.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩
      have hb := hR.2.1.1 x hx
      exact List.mem_range.mpr (noOpkSlotFlatIdx_lt S hb.1 hb.2.1 hb.2.2))
  have hle1 : st.usedRecvOPK.length ≤ S.N_opk_tot := by simpa using hsub1.length_le
  have hle2 : st.usedRecvNoOPK.length ≤ S.N_no_opk_tot := by simpa using hsub2.length_le
  have hle3 := hR.2.2
  unfold Setup.N_sess_tot Setup.N_recv_tot
  omega

theorem mem_support_recordKeyIndResp (S : Setup) (P : Primitives)
    (r : KeyIndRespEntry S) (st : KeyIndState S)
    (x : Unit × KeyIndState S) (hx : x ∈ support ((recordKeyIndResp S P r).run st)) :
    x.2.usedRecvOPK = st.usedRecvOPK ∧
    x.2.usedRecvNoOPK = st.usedRecvNoOPK ∧
    x.2.respSessions.length = st.respSessions.length + 1 := by
  unfold recordKeyIndResp at hx; dsimp only at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  split at hx
  · simp only [StateT.run_set, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨rfl, rfl, rfl⟩
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨_, _, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

theorem pqxdhKeyIndCachedImpl_validKeyIndResp_step (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hR : ValidKeyIndResp S st) :
    ∀ x ∈ support ((pqxdhKeyIndCachedImpl useRo S P q).run st), ValidKeyIndResp S x.2 := by
  let proj := fun s : KeyIndState S => (s.usedRecvOPK, s.usedRecvNoOPK, s.respSessions.length)
  have h_from_proj : ∀ m : StateT (KeyIndState S) ProbComp KeyIndResponse,
      PreservesAt proj st m →
      ∀ x ∈ support (m.run st), ValidKeyIndResp S x.2 := by
    intro m hp x hx
    have h := hp x hx
    have h1 : x.2.usedRecvOPK = st.usedRecvOPK := congrArg Prod.fst h
    have h2 : x.2.usedRecvNoOPK = st.usedRecvNoOPK := congrArg (Prod.fst ∘ Prod.snd) h
    have h3 : x.2.respSessions.length = st.respSessions.length := congrArg (Prod.snd ∘ Prod.snd) h
    unfold ValidKeyIndResp at hR ⊢
    rw [h1, h2, h3]; exact hR
  cases q with
  | acceptOPK k j o hdr =>
    change SatisfiesAt (ValidKeyIndResp S) st (pqxdhKeyIndCachedImpl useRo S P (.acceptOPK k j o
        hdr))
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only
    apply SatisfiesAt.get_bind
    apply SatisfiesAt.ite_return _ _ _ _ hR; intro _
    apply SatisfiesAt.ite_return _ _ _ _ hR; intro hFresh
    apply SatisfiesAt.ite_return _ _ _ _ hR; intro _
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    apply SatisfiesAt.ite_return _ _ _ _ hR; intro _
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    apply SatisfiesAt.liftM_bind; intro _ x hx
    simp only [StateT.run_bind, StateT.run_set, pure_bind, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx2⟩
    have hrec := mem_support_recordKeyIndResp S P _ _ y hy
    have hy_eq : x.2 = y.2 := by split at hx2 <;> simp at hx2 <;> exact congrArg Prod.snd hx2
    rw [hy_eq]
    dsimp only at hrec
    refine ⟨?_, ?_, ?_⟩
    · rw [hrec.1]; exact validUsedRecvOpk_cons S k j o st.usedRecvOPK hR.1 hFresh
    · rw [hrec.2.1]; exact hR.2.1
    · rw [hrec.2.2, hrec.1, hrec.2.1, List.length_cons]; have := hR.2.2; omega
  | acceptNoOPK k j l hdr =>
    change SatisfiesAt (ValidKeyIndResp S) st (pqxdhKeyIndCachedImpl useRo S P (.acceptNoOPK k j l
        hdr))
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only
    apply SatisfiesAt.get_bind
    apply SatisfiesAt.ite_return _ _ _ _ hR; intro _
    apply SatisfiesAt.ite_return _ _ _ _ hR; intro hFresh
    apply SatisfiesAt.ite_return _ _ _ _ hR; intro _
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    split; swap; · exact SatisfiesAt.pure _ _ _ hR
    apply SatisfiesAt.liftM_bind; intro _ x hx
    simp only [StateT.run_bind, StateT.run_set, pure_bind, MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨y, hy, hx2⟩
    have hrec := mem_support_recordKeyIndResp S P _ _ y hy
    have hy_eq : x.2 = y.2 := by split at hx2 <;> simp at hx2 <;> exact congrArg Prod.snd hx2
    rw [hy_eq]
    dsimp only at hrec
    refine ⟨?_, ?_, ?_⟩
    · rw [hrec.1]; exact hR.1
    · rw [hrec.2.1]; exact validUsedRecvNoOpk_cons S k j l st.usedRecvNoOPK hR.2.1 hFresh
    · rw [hrec.2.2, hrec.1, hrec.2.1, List.length_cons]; have := hR.2.2; omega
  | testSession sid =>
    apply h_from_proj
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only
    apply PreservesAt.get_bind
    split
    · apply PreservesAt.pure
    · split
      · apply PreservesAt.set_bind; rfl; apply PreservesAt.pure
      · split
        · apply PreservesAt.pure
        · apply PreservesAt.set_bind
          · exact Prod.ext rfl (Prod.ext rfl (List.length_map _))
          · apply PreservesAt.pure
  | revealSessionKey sid =>
    apply h_from_proj
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; dsimp only
    apply PreservesAt.get_bind
    split
    · split
      · apply PreservesAt.pure
      · apply PreservesAt.set_bind; rfl; apply PreservesAt.pure
    · split
      · apply PreservesAt.pure
      · split
        · apply PreservesAt.pure
        · apply PreservesAt.set_bind
          · exact Prod.ext rfl (Prod.ext rfl (List.length_map _))
          · apply PreservesAt.pure
  | initPrin _
  | corruptIK _
  | genSPK _ _
  | genOPK _ _ _
  | initiateOPK _ _ _
  | initiateNoOPK _ _ _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
    apply h_from_proj
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl runKeyIndInitiate
    dsimp only; prove_preserves_at

def ValidKeyIndEcC (S : Setup) (P : Primitives) (st : KeyIndState S) : Prop :=
  ValidKeyIndEc S st ∧ ValidAdvKeysPow8 P st.advKeys ∧ ValidKeyIndResp S st

theorem pqxdhKeyIndCachedImpl_validKeyIndEc_step (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : ValidKeyIndEc S st) :
    ∀ x ∈ support ((pqxdhKeyIndCachedImpl useRo S P q).run st), ValidKeyIndEc S x.2 := by
  cases q with
  | registerKey sk =>
    let proj := fun s : KeyIndState S => (s.principals, s.spkBundles, s.opkEntries, s.sessions)
    have h_from_proj : ∀ s : KeyIndState S, proj s = proj st → ValidKeyIndEc S s := by
      intro s hs
      have hp : s.principals = st.principals := congrArg Prod.fst hs
      have hsb : s.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) hs
      have hop : s.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hs
      have hss : s.sessions = st.sessions := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hs
      unfold ValidKeyIndEc ValidEcLists sessPksKeyInd at hV ⊢; rw [hp, hsb, hop, hss]; exact hV
    have hp : PreservesAt proj st (pqxdhKeyIndCachedImpl useRo S P (.registerKey sk)) := by
      unfold pqxdhKeyIndCachedImpl; dsimp only; prove_preserves_at
    exact fun x hx => h_from_proj x.2 (hp x hx)
  | initPrin _
  | corruptIK _
  | genSPK _ _
  | genOPK _ _ _
  | initiateOPK _ _ _
  | initiateNoOPK _ _ _
  | acceptOPK _ _ _ _
  | acceptNoOPK _ _ _ _
  | testSession _ | revealSessionKey _ | roQuery _ | revealDhSecrets | revealSpkSk _ _ =>
    exact pqxdhKeyIndImpl_validKeyIndEc_step useRo S P _ st hV

theorem pqxdhKeyIndCachedImpl_validAdvKeysPow8_step (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hAdv : ValidAdvKeysPow8 P st.advKeys) :
    ∀ x ∈ support ((pqxdhKeyIndCachedImpl useRo S P q).run st), ValidAdvKeysPow8 P x.2.advKeys := by
  have h_from_adv : ∀ m : StateT (KeyIndState S) ProbComp KeyIndResponse,
      PreservesAt (fun s => s.advKeys) st m →
      ∀ x ∈ support (m.run st), ValidAdvKeysPow8 P x.2.advKeys := by
    intro m hp x hx
    have h_eq : x.2.advKeys = st.advKeys := hp x hx
    rw [h_eq]; exact hAdv
  cases q with
  | registerKey sk =>
    unfold pqxdhKeyIndCachedImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · intro x hx
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact hAdv
    · intro x hx
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hx
      subst hx
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · rfl
      · exact hAdv e he'
  | initPrin _
  | corruptIK _
  | genSPK _ _
  | genOPK _ _ _
  | initiateOPK _ _ _
  | initiateNoOPK _ _ _
  | acceptOPK _ _ _ _
  | acceptNoOPK _ _ _ _
  | testSession _ | revealSessionKey _ | roQuery _ | revealDhSecrets | revealSpkSk _ _ =>
    apply h_from_adv
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl runKeyIndInitiate
    dsimp only; prove_preserves_at

theorem pqxdhKeyIndCachedImpl_validKeyIndEcC_step (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : ValidKeyIndEcC S P st) :
    ∀ x ∈ support ((pqxdhKeyIndCachedImpl useRo S P q).run st), ValidKeyIndEcC S P x.2 :=
  fun x hx => ⟨pqxdhKeyIndCachedImpl_validKeyIndEc_step useRo S P q st hV.1 x hx,
    pqxdhKeyIndCachedImpl_validAdvKeysPow8_step useRo S P q st hV.2.1 x hx,
    pqxdhKeyIndCachedImpl_validKeyIndResp_step useRo S P q st hV.2.2 x hx⟩

def cacheKeyIndAdvKeys (S : Setup) (P : Primitives) (st : KeyIndState S) : KeyIndState S :=
  { st with advKeys := st.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) }

@[simp]
theorem isAdvRegistered_map_cache (P : Primitives) (advKeys : List (Bytes × Bytes)) (pk : Bytes) :
    isAdvRegistered P (advKeys.map (fun (_, pk') => (P.pow8 pk', pk'))) pk =
      isAdvRegistered P advKeys pk := by
  unfold isAdvRegistered
  rw [List.any_map]
  rfl

@[simp]
theorem koskBundleOk_map_cache (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    koskBundleOk P principals spkBundles opkEntries
      (advKeys.map (fun (_, pk') => (P.pow8 pk', pk'))) bundle =
      koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  unfold koskBundleOk
  cases bundle.opkB? <;> simp [isAdvRegistered_map_cache]

@[simp]
theorem koskSenderOk_map_cache (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes) :
    koskSenderOk P principals (advKeys.map (fun (_, pk') => (P.pow8 pk', pk'))) ikAPk =
      koskSenderOk P principals advKeys ikAPk := by
  unfold koskSenderOk
  simp [isAdvRegistered_map_cache]

theorem CommutesRel.recordKeyIndResp_bind_cache (S : Setup) (P : Primitives)
    (st : KeyIndState S) (r : KeyIndRespEntry S)
    {f1 f2 : PUnit → StateT (KeyIndState S) ProbComp KeyIndResponse}
    (hf : ∀ s', CommutesRel (cacheKeyIndAdvKeys S P) s' (f1 PUnit.unit) (f2 PUnit.unit)) :
    CommutesRel (cacheKeyIndAdvKeys S P) st
      (recordKeyIndResp S P r >>= f1) (recordKeyIndResp S P r >>= f2) := by
  unfold recordKeyIndResp
  simp only [bind_assoc]
  apply CommutesRel.get_bind
  dsimp only [cacheKeyIndAdvKeys]
  cases st.sessions.find? (fun s => keyIndPartner P s r) with
  | some s =>
    dsimp only; simp only [bind_assoc]
    rw [pure_bind, pure_bind]
    exact CommutesRel.set_bind (cacheKeyIndAdvKeys S P) st _ _ rfl (hf _)
  | none =>
    dsimp only; simp only [bind_assoc]
    exact CommutesRel.liftM_bind (cacheKeyIndAdvKeys S P) st sampleDRKey96 (fun _ =>
      CommutesRel.set_bind (cacheKeyIndAdvKeys S P) st _ _ rfl (hf _))

macro "prove_commutes_rel_cache" : tactic =>
  `(tactic| repeat (first
    | apply CommutesRel.pure
    | (rw [pure_bind, pure_bind])
    | (apply CommutesRel.recordKeyIndResp_bind_cache; intro _)
    | (apply CommutesRel.liftM_bind; intro _)
    | (apply CommutesRel.set_bind; rfl)
    | apply CommutesRel.ite
    | split))

theorem runKeyIndInitiate_commutes_cache (useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    CommutesRel (cacheKeyIndAdvKeys S P) st
      (runKeyIndInitiate useRo S P sid u bundle)
      (runKeyIndInitiate useRo S P sid u bundle) := by
  unfold runKeyIndInitiate
  apply CommutesRel.get_bind
  dsimp only [cacheKeyIndAdvKeys]
  rw [koskBundleOk_map_cache]
  prove_commutes_rel_cache

theorem pqxdhKeyIndCachedImpl_commutes_cache (useRo : Bool) (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) :
    CommutesRel (cacheKeyIndAdvKeys S P) st
      (pqxdhKeyIndCachedImpl useRo S P q)
      (pqxdhKeyIndImpl useRo S P q) := by
  cases q with
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind
    by_cases h : bundle.opkB?.isNone = true
    · simp only [h, ↓reduceIte]; prove_commutes_rel_cache
    · simp only [h, Bool.false_eq_true,
        ↓reduceIte]; exact runKeyIndInitiate_commutes_cache useRo S P _ u bundle st
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind
    by_cases h : bundle.opkB?.isSome = true
    · simp only [h, ↓reduceIte]; prove_commutes_rel_cache
    · simp only [h, Bool.false_eq_true,
        ↓reduceIte]; exact runKeyIndInitiate_commutes_cache useRo S P _ u bundle st
  | acceptOPK u j o hdr =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [cacheKeyIndAdvKeys]
    rw [koskSenderOk_map_cache]; prove_commutes_rel_cache
  | acceptNoOPK u j l hdr =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [cacheKeyIndAdvKeys]
    rw [koskSenderOk_map_cache]; prove_commutes_rel_cache
  | registerKey sk =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl registerAdvKey; apply CommutesRel.get_bind; dsimp
        only [cacheKeyIndAdvKeys]
    by_cases h : (sk.length != 32) = true
    · simp only [h, ↓reduceIte]; prove_commutes_rel_cache
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; prove_commutes_rel_cache
  | initPrin _
  | corruptIK _
  | genSPK _ _
  | genOPK _ _ _
  | testSession _ | revealSessionKey _ | roQuery _ | revealDhSecrets | revealSpkSk _ _ =>
    unfold pqxdhKeyIndCachedImpl pqxdhKeyIndImpl; apply CommutesRel.get_bind; dsimp only
        [cacheKeyIndAdvKeys, isKeyIndSessionTestable]; prove_commutes_rel_cache

theorem CommutesRel.simulateQ_add_unif {ι : Type} {spec : OracleSpec.{0, 0} ι} {St α : Type}
    (proj : St → St)
    (impl1 impl2 : QueryImpl spec (StateT St ProbComp))
    (h_step : ∀ q st, CommutesRel proj st (impl1 q) (impl2 q))
    (oa : OracleComp (unifSpec + spec) α) (st : St) :
    CommutesRel proj st
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl1) oa)
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
          impl2) oa) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => exact CommutesRel.pure proj st a
  | query_bind q f ih =>
    unfold CommutesRel at ih ⊢
    cases q with
    | inl uq =>
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_left,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind, map_bind]
      exact bind_congr (fun u => ih u st)
    | inr gq =>
      have hq := h_step gq st
      unfold CommutesRel at hq
      simp only [simulateQ_bind, StateT.run_bind, QueryImpl.simulateQ_add_query_right]
      rw [hq, bind_map_left, map_bind]
      exact bind_congr (fun p => ih p.1 p.2)

theorem isQueryBoundP_simulateForSigPrim_prim {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI} {St : Type}
    (S : Setup) (emptySt : Bool → St)
    (stepPrim : (q : ιI) → SigReductionState St →
        OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState St) (GSpec.Range q)))
    (C : Nat) (h_step : ∀ gq st, PrimBounded (stepPrim gq st) C)
    (targetParty : Nat) (targetPk : Bytes)
    (oa : OracleComp (unifSpec + GSpec) Bool) (Q : Nat)
    (h_oa : IsQueryBoundP oa (fun q : Nat ⊕ ιI => q.isRight = true) Q) :
    IsQueryBoundP (simulateForSigPrim S emptySt stepPrim targetParty targetPk oa)
      (fun q : (Nat ⊕ PrimQuery) ⊕ SigQuery => isPrimQuery q = true) (Q * (C + 1)) := by
  unfold simulateForSigPrim
  have h_unif := isQueryBoundP_embedPrim_isPrimQuery (spec := sigOracleSpec)
    (embedUnif ($ᵗ Bool)) 0 (primBounded_embedUnif ($ᵗ Bool) 0)
  simpa [Nat.zero_add, Nat.add_zero] using
    isQueryBoundP_bind h_unif
      (fun secb _ =>
        isQueryBoundP_bind (isQueryBoundP_runWithSigBudgetPrim_prim stepPrim C h_step oa Q h_oa _
            S.N_spk_tot)
          (fun _ _ => isQueryBoundP_pure (fun q : (Nat ⊕ PrimQuery) ⊕ SigQuery => isPrimQuery q =
              true) _ 0))

theorem evalDist_true_eq_probExpect (mx : ProbComp Bool) :
    𝒟[mx] {true} = probExpect mx (fun b => 𝒟[(pure b : ProbComp Bool)] {true}) := by
  simpa using evalDist_bind_true_eq_probExpect mx id

theorem evalDist_pure_bool_true (b : Bool) :
    𝒟[(pure b : ProbComp Bool)] {true} = if b then 1 else 0 := by
  cases b <;> simp

theorem evalDist_bind_true_eq_probExpect_ite {α : Type} (mx : ProbComp α) (p : α → Bool) :
    𝒟[mx >>= fun a => pure (p a)] {true} =
      probExpect mx (fun a => if p a then 1 else 0) := by
  rw [evalDist_bind_true_eq_probExpect]
  congr 1; ext a
  exact evalDist_pure_bool_true (p a)

theorem sigEufCmaExp_eq (P : Primitives) (A : SigEufCmaAdv) :
    sigEufCmaExp P A = (do
      let sk ← sampleScalar32
      let pk := P.sigPkGen sk
      let ((mStar, sigStar), signedMsgs) ← (simulateQ (sigEufCmaFullImpl P sk) (A.run pk)).run []
      return (P.sigVerify pk mStar sigStar && decide (mStar ∉ signedMsgs))) := rfl

theorem evalDist_sigEufCmaExp_simulateForSigPrim_eq {ιI : Type} {GSpec : OracleSpec.{0,
    0} ιI} {St : Type}
    (S : Setup) (P : Primitives) (emptySt : Bool → St)
    (stepPrim : (q : ιI) → SigReductionState St →
        OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState St) (GSpec.Range q)))
    (k : Nat) (oa : OracleComp (unifSpec + GSpec) Bool)
    (q_prim : Nat) :
    𝒟[sigEufCmaExp P ⟨fun pk => simulateForSigPrim S emptySt stepPrim k pk oa,
      2 * S.N_spk_tot, q_prim⟩] {true} =
      probExpect ($ᵗ Bool : ProbComp Bool) (fun secb =>
        probExpect sampleScalar32 (fun sk =>
          probExpect
            ((simulateQ (sigEufCmaFullImpl P sk)
              (runWithSigBudgetPrim stepPrim oa ⟨emptySt secb, k, P.sigPkGen sk,
                  none⟩ S.N_spk_tot)).run [])
            (sigWinInd P sk))) := by
  rw [sigEufCmaExp_eq, evalDist_true_eq_probExpect]
  simp_rw [evalDist_pure_bool_true]
  unfold simulateForSigPrim
  have h_emb : ∀ (sk : Bytes) (f : Bool × List Bytes → ℝ≥0∞),
      probExpect ((simulateQ (sigEufCmaFullImpl P sk)
        (embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ Bool)))).run []) f =
        probExpect ($ᵗ Bool : ProbComp Bool) (fun secb => f (secb, [])) := by
    intro sk f
    unfold sigEufCmaFullImpl
    rw [simulateQ_embedPrim_run, simulateQ_embedUnif, probExpect_map]
  simp only [simulateQ_bind, StateT.run_bind, probExpect_bind, h_emb,
    simulateQ_pure, StateT.run_pure, probExpect_pure]
  rw [probExpect_swap sampleScalar32 ($ᵗ Bool)]
  rfl

theorem SigGameLens.evalDist_badAt_le_sigEufCmaExp {ιI : Type} {GSpec : OracleSpec.{0, 0} ιI}
    {S : Setup} {St R : Type} (L : SigGameLens S St R)
    (P : Primitives) (k : Nat) (emptySt : Bool → St)
    (realImpl : QueryImpl GSpec (StateT St ProbComp))
    (step : (q : ιI) → SigReductionState St →
        ProbComp (SigStepResult (SigReductionState St) (GSpec.Range q)))
    (stepPrim : (q : ιI) → SigReductionState St →
        OracleComp PrimBaseSpec (SigStepResultPrim (SigReductionState St) (GSpec.Range q)))
    (oa : OracleComp (unifSpec + GSpec) Bool)
    (q_prim : Nat)
    (_h_prim : ∀ pk, IsQueryBoundP (simulateForSigPrim S emptySt stepPrim k pk oa)
      (fun q : (Nat ⊕ PrimQuery) ⊕ SigQuery => isPrimQuery q = true) q_prim)
    (Inv : St → Prop)
    (h_inv_empty : ∀ secb, Inv (emptySt secb))
    (h_inv_step : ∀ (gq : ιI) (st : St), Inv st →
      ∀ x ∈ support ((realImpl gq).run st), Inv x.2)
    (h_eval_after : ∀ (sk : Bytes) (gq : ιI) (st : St) (s : SigReductionState St) (budget :
        Nat) (signedMsgs : List Bytes),
      L.ActiveAfter P k sk st s budget signedMsgs → Inv st → evalStepPrim P stepPrim gq s =
          step gq s)
    (h_eval_before : ∀ (sk : Bytes) (gq : ιI) (st : St) (budget : Nat),
      L.ActiveBefore P k st budget → Inv st →
      evalStepPrim P stepPrim gq ⟨st, k, P.sigPkGen sk, none⟩ = step gq ⟨st, k, P.sigPkGen sk,
          none⟩)
    (h_empty : ∀ secb, L.prins (emptySt secb) = [] ∧ L.spks (emptySt secb) = [] ∧
        L.badPeers (emptySt secb) = [])
    (h_won_step : ∀ (gq : ιI) (s : SigReductionState St),
      s.forgery.isSome = true → ∃ defResp, evalStepPrim P stepPrim gq s = pure (.done defResp s))
    (h_safe_step : ∀ (gq : ιI) (st : St), L.Safe P k st →
      ∀ x ∈ support ((realImpl gq).run st), L.Safe P k x.2)
    (h_after_step : ∀ (sk : Bytes) (gq : ιI) (st : St) (s : SigReductionState St)
      (budget : Nat) (signedMsgs : List Bytes)
      (fL : GSpec.Range gq × St → ℝ≥0∞)
      (fR : (GSpec.Range gq × SigReductionState St × Nat) × List Bytes → ℝ≥0∞),
      L.ActiveAfter P k sk st s budget signedMsgs →
      (∀ x, fL x ≤ 1) →
      (∀ x, L.Safe P k x.2 → fL x = 0) →
      (∀ y, SigWon P sk y.1.2.1 y.2 → 1 ≤ fR y) →
      (∀ out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
        fL (out, st') ≤ fR ((out, s', b'), msgs')) →
      probExpect ((realImpl gq).run st) fL ≤
        probExpect (runSigStepSim P sk budget (step gq s) signedMsgs) fR)
    (h_before_step : ∀ (gq : ιI) (st : St) (budget : Nat)
      (fL : GSpec.Range gq × St → ℝ≥0∞)
      (fR : Bytes → (GSpec.Range gq × SigReductionState St × Nat) × List Bytes → ℝ≥0∞),
      L.ActiveBefore P k st budget →
      (∀ out st' b', L.ActiveBefore P k st' b' →
        fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
          fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) →
      (∀ sk out st' s' b' msgs', L.ActiveAfter P k sk st' s' b' msgs' →
        fL (out, st') ≤ fR sk ((out, s', b'), msgs')) →
      probExpect ((realImpl gq).run st) fL ≤
        probExpect sampleScalar32 (fun sk =>
          probExpect (runSigStepSim P sk budget (step gq ⟨st, k, P.sigPkGen sk,
              none⟩) []) (fR sk))) :
    𝒟[(do
      let secb ← $ᵗ Bool
      let initSt := emptySt secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + realImpl
      let (b', finalSt) ← (simulateQ impl oa).run initSt
      return (secb, b', finalSt)) >>= fun (_, _, finalSt) => pure (L.badAt P k finalSt)] {true} ≤
    𝒟[sigEufCmaExp P ⟨fun pk => simulateForSigPrim S emptySt stepPrim k pk oa,
      2 * S.N_spk_tot, q_prim⟩] {true} := by
  rw [evalDist_bind_true_eq_probExpect_ite, evalDist_sigEufCmaExp_simulateForSigPrim_eq]
  simp only [probExpect_bind, probExpect_pure]
  refine probExpect_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact probExpect_activeBefore_le P k realImpl step stepPrim (L.badAt P k) (L.Safe P k)
    (L.ActiveAfter P k) (L.ActiveBefore P k) Inv h_inv_step h_eval_after h_eval_before
    h_won_step (L.safe_badAt_eq_false P k) h_safe_step
    (L.activeAfter_badAt_eq_false P k) h_after_step
    (L.activeBefore_badAt_eq_false P k) h_before_step
    oa (emptySt secb) S.N_spk_tot
    (L.activeBefore_empty P k (emptySt secb) (h_empty secb).1 (h_empty secb).2.1 (h_empty secb).2.2)
    (h_inv_empty secb)

theorem pqxdhKeyIndImpl_initiateOPK_pres (useRo : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (st : KeyIndState S) :
    SatisfiesAt (InitPostKeyInd P b st) st (pqxdhKeyIndImpl useRo S P (.initiateOPK u i b)) :=
  SatisfiesAt.get_bind _ st (SatisfiesAt.ite_return _ st _ _ (initPostKeyInd_refl P b st)
    (fun _ => runKeyIndInitiate_pres useRo S P (.sendOPK u i) u b st))

theorem pqxdhKeyIndImpl_initiateNoOPK_pres (useRo : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (st : KeyIndState S) :
    SatisfiesAt (InitPostKeyInd P b st) st (pqxdhKeyIndImpl useRo S P (.initiateNoOPK u i b)) :=
  SatisfiesAt.get_bind _ st (SatisfiesAt.ite_return _ st _ _ (initPostKeyInd_refl P b st)
    (fun _ => runKeyIndInitiate_pres useRo S P (.sendNoOPK u i) u b st))

theorem isQueryBoundP_isRight_of_isGameQuery {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {oa : OracleComp (unifSpec + spec) α} {n : Nat}
    (h : IsQueryBoundP oa (fun q => isGameQuery q = true) n) :
    IsQueryBoundP oa (fun q => q.isRight = true) n := by
  have heq : (isGameQuery : Nat ⊕ ι → Bool) = Sum.isRight := by
    ext q; cases q <;> rfl
  rwa [heq] at h

def sigReductionKeyIndAt (useRo : Bool) (S : Setup) (b : QueryBudget) (targetParty : Nat)
    (A : BoundedAdv (KeyIndAdversary S) b) : SigEufCmaAdv where
  run          := fun pk => simulateKeyIndForSigPrim useRo S targetParty pk A.val
  q_sig        := 2 * S.N_spk_tot
  q_prim       := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 17)

theorem evalDist_badAt_keyInd_le_sigEufCmaExp (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (k : Nat) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[(do
      let secb ← $ᵗ Bool
      let initSt := KeyIndState.empty S secb
      let impl :=
          (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
        pqxdhKeyIndImpl useRo S P
      let (b', finalSt) ← (simulateQ impl A.val.run).run initSt
      return (secb, b', finalSt)) >>= fun (_, _,
          finalSt) => pure ((keyIndSigLens S).badAt P k finalSt)] {true} ≤
    𝒟[sigEufCmaExp P (sigReductionKeyIndAt useRo S b k A)] {true} := by
  have h_eq :
      ((do
        let secb ← $ᵗ Bool
        let initSt := KeyIndState.empty S secb
        let impl :=
            (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
          pqxdhKeyIndImpl useRo S P
        let (b', finalSt) ← (simulateQ impl A.val.run).run initSt
        return (secb, b', finalSt)) >>= fun (_, _,
            finalSt) => pure ((keyIndSigLens S).badAt P k finalSt)) =
      ((do
        let secb ← $ᵗ Bool
        let initSt := KeyIndState.empty S secb
        let impl :=
            (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
          pqxdhKeyIndCachedImpl useRo S P
        let (b', finalSt) ← (simulateQ impl A.val.run).run initSt
        return (secb, b', finalSt)) >>= fun (_, _,
            finalSt) => pure ((keyIndSigLens S).badAt P k finalSt)) := by
    simp only [bind_assoc, pure_bind]
    refine bind_congr (fun secb => ?_)
    have hsim := CommutesRel.simulateQ_add_unif (cacheKeyIndAdvKeys S P)
      (pqxdhKeyIndCachedImpl useRo S P) (pqxdhKeyIndImpl useRo S P)
      (pqxdhKeyIndCachedImpl_commutes_cache useRo S P) A.val.run (KeyIndState.empty S secb)
    unfold CommutesRel at hsim
    have hemp : cacheKeyIndAdvKeys S P (KeyIndState.empty S secb) = KeyIndState.empty S secb := rfl
    rw [hemp] at hsim
    rw [hsim, bind_map_left]
    rfl
  rw [h_eq]
  refine (keyIndSigLens S).evalDist_badAt_le_sigEufCmaExp P k (KeyIndState.empty S)
    (pqxdhKeyIndCachedImpl useRo S P) (stepKeyIndForSig useRo S P) (stepKeyIndForSigPrim useRo S)
    A.val.run (b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 17))
    (fun pk => isQueryBoundP_simulateForSigPrim_prim S (KeyIndState.empty S)
      (stepKeyIndForSigPrim useRo S) (S.N_dh * 20 + S.N_sess_tot * 8 +
          16) (primBounded_stepKeyIndForSigPrim useRo S)
      k pk A.val.run b.q_total (isQueryBoundP_isRight_of_isGameQuery A.property.2.2.2.1))
    (ValidKeyIndEcC S P)
    (fun secb => ⟨validEcLists_nil S, (fun _ h => by cases h), validKeyIndResp_empty S secb⟩)
    (pqxdhKeyIndCachedImpl_validKeyIndEcC_step useRo S P)
    (fun sk q st s budget signedMsgs hAfter hV => by
      have hs := hAfter.1; subst hs
      have hL := validKeyIndEc_lengths_le S P st hV.1
      have hR := validKeyIndResp_length_le S st hV.2.2
      exact evalStepPrim_stepKeyIndForSigPrim useRo S P hP q _
        (by simpa [SigGameLens.eraseSk,
            keyIndSigLens] using hL.1) hL.2.1 hL.2.2.1 hL.2.2.2 hR hV.2.1)
    (fun sk q st budget _ hV => by
      have hL := validKeyIndEc_lengths_le S P st hV.1
      have hR := validKeyIndResp_length_le S st hV.2.2
      exact evalStepPrim_stepKeyIndForSigPrim useRo S P hP q _ hL.1 hL.2.1 hL.2.2.1 hL.2.2.2 hR
        hV.2.1)
    (fun _ => ⟨rfl, rfl, rfl⟩)
    (fun q s hSome => ⟨.noneResp, by simp [evalStepPrim, stepKeyIndForSigPrim, hSome,
        SigStepResultPrim.toProbComp]⟩)
    ?_ ?_ ?_
  · intro q st hSafe
    cases q with
    | initPrin u => exact (keyIndSigLens S).safe_step_initPrin P k u st hSafe
    | corruptIK u => exact (keyIndSigLens S).safe_step_corruptIK P k u st hSafe
    | genSPK u j => exact (keyIndSigLens S).safe_step_genSPK P k u j st hSafe
    | initiateOPK u i bnd =>
      exact (keyIndSigLens S).safe_step_initiate P k bnd _ st
        (pqxdhKeyIndImpl_initiateOPK_pres useRo S P u i bnd st) hSafe
    | initiateNoOPK u i bnd =>
      exact (keyIndSigLens S).safe_step_initiate P k bnd _ st
        (pqxdhKeyIndImpl_initiateNoOPK_pres useRo S P u i bnd st) hSafe
    | genOPK _ _ _
    | acceptOPK _ _ _ _
    | acceptNoOPK _ _ _ _
    | testSession _
    | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
      exact (keyIndSigLens S).safe_step_other P k _ st
        (pqxdhKeyIndImpl_other_pres useRo S P _ st
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)) hSafe
  · intro sk q st s budget signedMsgs fL fR hAfter hfL1 hfL0 hfR1 hih
    have hs := hAfter.1; subst hs
    cases q with
    | initPrin u =>
      exact (keyIndSigLens S).after_step_initPrin P k sk u st _ budget signedMsgs fL
        fR hAfter hfL0 hih
    | corruptIK u =>
      exact (keyIndSigLens S).after_step_corruptIK P k sk u st _ budget signedMsgs fL
        fR hAfter hfL0 hih
    | genSPK u j =>
      exact (keyIndSigLens S).after_step_genSPK P k sk u j st _ budget signedMsgs fL
        fR hAfter hfL0 hih
    | initiateOPK u i bnd =>
      exact (keyIndSigLens S).after_step_initiate P k sk bnd _ st _ budget signedMsgs fL fR
        (pqxdhKeyIndImpl_other_commutes useRo S P k (.initiateOPK u i bnd) st
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h))
        (pqxdhKeyIndImpl_initiateOPK_pres useRo S P u i bnd st)
        hAfter hfL1 hfL0 hfR1 hih
    | initiateNoOPK u i bnd =>
      exact (keyIndSigLens S).after_step_initiate P k sk bnd _ st _ budget signedMsgs fL fR
        (pqxdhKeyIndImpl_other_commutes useRo S P k (.initiateNoOPK u i bnd) st
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h))
        (pqxdhKeyIndImpl_initiateNoOPK_pres useRo S P u i bnd st)
        hAfter hfL1 hfL0 hfR1 hih
    | genOPK _ _ _
    | acceptOPK _ _ _ _
    | acceptNoOPK _ _ _ _
    | testSession _
    | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
      exact (keyIndSigLens S).after_step_other P k sk _ st _ budget signedMsgs fL fR
        (pqxdhKeyIndImpl_other_commutes useRo S P k _ st
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h))
        (pqxdhKeyIndImpl_other_pres useRo S P _ st
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
        hAfter hfL0 hih
  · intro q st budget fL fR hBefore hih_before hih_after
    cases q with
    | initPrin u =>
      exact (keyIndSigLens S).before_step_initPrin P k u st budget fL fR hBefore
        hih_before hih_after
    | corruptIK u =>
      exact (keyIndSigLens S).before_step_corruptIK P k u st budget fL fR hBefore
        hih_before
    | genSPK u j =>
      exact (keyIndSigLens S).before_step_genSPK P k u j st budget fL fR hBefore
        hih_before
    | initiateOPK u i bnd =>
      exact (keyIndSigLens S).before_step_initiate P k bnd _ st budget fL fR
        (pqxdhKeyIndImpl_initiateOPK_pres useRo S P u i bnd st) hBefore hih_before
    | initiateNoOPK u i bnd =>
      exact (keyIndSigLens S).before_step_initiate P k bnd _ st budget fL fR
        (pqxdhKeyIndImpl_initiateNoOPK_pres useRo S P u i bnd st) hBefore hih_before
    | genOPK _ _ _
    | acceptOPK _ _ _ _
    | acceptNoOPK _ _ _ _
    | testSession _
    | revealSessionKey _ | roQuery _ | revealDhSecrets | registerKey _ | revealSpkSk _ _ =>
      exact (keyIndSigLens S).before_step_other P k _ st budget fL fR
        (pqxdhKeyIndImpl_other_pres useRo S P _ st
          (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
        hBefore hih_before

theorem sigReductionKeyInd_queries (S : Setup) (b : QueryBudget) (A :
    BoundedAdv (KeyIndAdversary S) b) :
    (sigReductionKeyInd S b A).q_sig ≤ 2 * S.N_spk_tot := by
  rfl

theorem sigReductionKeyIndCore_prim_queries (useRo : Bool) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigReductionKeyIndCore useRo S b A).q_prim ≤ primQueryBudget S b := by
  unfold sigReductionKeyIndCore primQueryBudget
  dsimp only
  nlinarith

theorem sigReductionKeyInd_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigReductionKeyInd S b A).q_prim ≤ primQueryBudget S b :=
  sigReductionKeyIndCore_prim_queries true S b A

theorem probExpect_uniformFin (N : ℕ) [NeZero N] (g : ℕ → ℝ≥0∞) :
    probExpect ($ᵗ (Fin N) : ProbComp (Fin N)) (fun k => g k.val) =
      ∑ k ∈ Finset.range N, g k * (N : ℝ≥0∞)⁻¹ := by
  let _ : MeasurableSpace (Fin N) := ⊤
  have _ : DiscreteMeasurableSpace (Fin N) := ⟨fun _ => trivial⟩
  unfold probExpect
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => g k * (N : ℝ≥0∞)⁻¹) N

theorem sigReductionKeyIndCoreRun_pos (useRo : Bool) (S : Setup)
    (A : KeyIndAdversary S) (pk : Bytes) (hN : 0 < S.N_id) :
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    sigReductionKeyIndCoreRun useRo S A pk = (do
      let k ← embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ (Fin S.N_id)))
      simulateKeyIndForSigPrim useRo S k.val pk A) := by
  unfold sigReductionKeyIndCoreRun
  split_ifs
  rfl

theorem evalDist_sigEufCmaExp_CoreRun (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) (hN : 0 < S.N_id) :
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    probExpect (do
      let sk ← sampleScalar32
      let pk := P.sigPkGen sk
      let ((m, sig), signedMsgs) ←
        (simulateQ (sigEufCmaFullImpl P sk) (sigReductionKeyIndCoreRun useRo S A pk)).run []
      return (P.sigVerify pk m sig && decide (m ∉ signedMsgs)))
      (fun b => if b = true then 1 else 0) =
      ∑ k ∈ Finset.range S.N_id,
        probExpect (do
          let sk ← sampleScalar32
          let pk := P.sigPkGen sk
          let ((m, sig), signedMsgs) ←
            (simulateQ (sigEufCmaFullImpl P sk) (simulateKeyIndForSigPrim useRo S k pk A)).run []
          return (P.sigVerify pk m sig && decide (m ∉ signedMsgs)))
          (fun b => if b = true then 1 else 0) * (S.N_id : ℝ≥0∞)⁻¹ := by
  have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
  simp_rw [sigReductionKeyIndCoreRun_pos useRo S A _ hN]
  have h_emb : ∀ (sk : Bytes) (f : Fin S.N_id × List Bytes → ℝ≥0∞),
      probExpect ((simulateQ (sigEufCmaFullImpl P sk)
        (embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ (Fin S.N_id))))).run []) f =
        probExpect ($ᵗ (Fin S.N_id)) (fun k => f (k, [])) := by
    intro sk f
    unfold sigEufCmaFullImpl
    rw [simulateQ_embedPrim_run, simulateQ_embedUnif, probExpect_map]
  simp only [simulateQ_bind, StateT.run_bind, probExpect_bind, h_emb]
  rw [probExpect_swap sampleScalar32 ($ᵗ (Fin S.N_id)),
      probExpect_uniformFin S.N_id (fun k =>
        probExpect sampleScalar32 (fun a =>
          probExpect ((simulateQ (sigEufCmaFullImpl P a) (simulateKeyIndForSigPrim useRo S k
              (P.sigPkGen a) A)).run []) (fun x =>
            probExpect (pure (P.sigVerify (P.sigPkGen a) x.1.1 x.1.2 &&
                decide (x.1.1 ∉ x.2))) (fun b =>
              if b = true then 1 else 0))))]

theorem evalDist_sigEufCmaExp_sigReductionKeyIndCore (useRo : Bool) (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (hN : 0 < S.N_id) :
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    𝒟[sigEufCmaExp P (sigReductionKeyIndCore useRo S b A)] {true} =
      ∑ k ∈ Finset.range S.N_id,
        𝒟[sigEufCmaExp P (sigReductionKeyIndAt useRo S b k A)] {true} * (S.N_id : ℝ≥0∞)⁻¹ := by
  have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
  rw [sigEufCmaExp_eq, evalDist_true_eq_probExpect]
  simp_rw [evalDist_pure_bool_true]
  change probExpect (do
      let sk ← sampleScalar32
      let pk := P.sigPkGen sk
      let ((m, sig), signedMsgs) ←
        (simulateQ (sigEufCmaFullImpl P sk) (sigReductionKeyIndCoreRun useRo S A.val pk)).run []
      return (P.sigVerify pk m sig && decide (m ∉ signedMsgs)))
      (fun b => if b = true then 1 else 0) = _
  rw [evalDist_sigEufCmaExp_CoreRun useRo S P A.val hN]
  congr 1; ext k; congr 1
  rw [sigEufCmaExp_eq, evalDist_true_eq_probExpect]
  simp_rw [evalDist_pure_bool_true]
  rfl

theorem sum_sigReductionKeyIndCore_le (useRo : Bool) (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (∑ k ∈ Finset.range S.N_id, SigEufCma P (sigReductionKeyIndAt useRo S b k A)) ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionKeyIndCore useRo S b A) := by
  by_cases hN : 0 < S.N_id
  · have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    have h_core := evalDist_sigEufCmaExp_sigReductionKeyIndCore useRo S P b A hN
    unfold SigEufCma
    rw [h_core]
    have hfin : ∀ k ∈ Finset.range S.N_id,
        𝒟[sigEufCmaExp P (sigReductionKeyIndAt useRo S b k A)] {true} * (S.N_id : ℝ≥0∞)⁻¹ ≠ ⊤ := by
      intro k _
      exact ENNReal.mul_ne_top (MeasureTheory.measure_ne_top _ {true})
        (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne S.N_id)))
    rw [ENNReal.toReal_sum hfin]
    have hterm : ∀ k ∈ Finset.range S.N_id,
        (𝒟[sigEufCmaExp P (sigReductionKeyIndAt useRo S b k A)] {true} * (S.N_id : ℝ≥0∞)⁻¹).toReal =
          (𝒟[sigEufCmaExp P (sigReductionKeyIndAt useRo S b k A)] {true}).toReal * (S.N_id :
              ℝ)⁻¹ := by
      intro k _
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← mul_assoc,
      mul_comm (S.N_id : ℝ), mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne S.N_id)),
          mul_one]
  · have h0 : S.N_id = 0 := Nat.eq_zero_of_not_pos hN
    simp [h0]

theorem sum_sigReductionKeyInd_le (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (∑ k ∈ Finset.range S.N_id, SigEufCma P (sigReductionKeyIndAt true S b k A)) ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionKeyInd S b A) :=
  sum_sigReductionKeyIndCore_le true S P b A

theorem peerPartyIdx_lt {S : Setup} (hN : 0 < S.N_id) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (peerIkPk : Bytes) :
    peerPartyIdx S P principals peerIkPk < S.N_id := by
  unfold peerPartyIdx
  cases findHonestPrincipal P principals peerIkPk with
  | none => exact hN
  | some p =>
    rcases p with ⟨k, _⟩
    dsimp only
    split_ifs with hk
    · exact hk
    · exact hN

theorem sessionId_pos_N_id {S : Setup} (sid : SessionId S) : 0 < S.N_id := by
  cases sid with
  | sendOPK u _   => exact u.pos
  | sendNoOPK u _ => exact u.pos
  | recvOPK u _   => exact u.pos
  | recvNoOPK u _ => exact u.pos

/-- Per-principal `badSig` predicate in `KeyInd` attributing a forged bundle to principal `k`
outside principal public-key collisions. -/
def hasBadSigKeyIndAt (S : Setup) (P : Primitives) (k : Nat) (st : KeyIndState S) : Bool :=
  (keyIndSigLens S).badAt P k st

theorem hasBadSigKeyInd_eq_any_range (S : Setup) (P : Primitives) (st : KeyIndState S) :
    (hasBadSigKeyInd st && noPrinPkColl P st.principals) =
      (List.range S.N_id).any (fun k => hasBadSigKeyIndAt S P k st) := by
  apply Bool.eq_iff_iff.mpr
  simp only [hasBadSigKeyInd, hasBadSigKeyIndAt, SigGameLens.badAt, keyIndSigLens, badPeersKeyInd,
    List.any_eq_true, List.mem_range, List.mem_map, List.mem_filter,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨s, hs, hfresh, hbad⟩, hnp⟩
    have hN : 0 < S.N_id := sessionId_pos_N_id s.sid
    exact ⟨peerPartyIdx S P st.principals s.peerIkPk,
      peerPartyIdx_lt hN P st.principals s.peerIkPk,
      ⟨s.peerIkPk, ⟨s, ⟨hs, hfresh, hbad⟩, rfl⟩, rfl⟩, hnp⟩
  · rintro ⟨k, _, ⟨_, ⟨s, ⟨hs, hfresh, hbad⟩, rfl⟩, _⟩, hnp⟩
    exact ⟨⟨s, hs, hfresh, hbad⟩, hnp⟩

theorem hasDuplicateBytes_append_of_left :
    ∀ (xs ys : List Bytes), hasDuplicateBytes xs = true → hasDuplicateBytes (xs ++ ys) = true
  | [], _, h => by simp [hasDuplicateBytes] at h
  | x :: xs, ys, h =>
    by
    simp only [List.cons_append, hasDuplicateBytes, Bool.or_eq_true, List.contains_iff_mem,
      List.mem_append] at h ⊢
    rcases h with h1 | h2
    · exact Or.inl (Or.inl h1)
    · exact Or.inr (hasDuplicateBytes_append_of_left xs ys h2)

theorem sigHopTerm_nonneg (S : Setup) (P : Primitives) (B : SigEufCmaAdv) :
    0 ≤ (S.N_id : ℝ) * SigEufCma P B := by
  have h := sigEufCma_nonneg P B
  positivity

/-- Whether `bundle` targets an honest uncorrupted principal while failing bundle provenance. -/
def isBadSigBundle (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : Bool :=
  (isHonestUncorruptedPeer P principals bundle.ikB).isSome &&
  !(let (spkHon, _, pqspkHon) :=
      checkBundleProvenance P principals spkBundles opkEntries bundle
    spkHon && pqspkHon)

/-- Hybrid game `G2` (`H2` when `useRo = false`) for `KeyInd`: `pqxdhKeyIndImpl`, except that
initiating towards an honest uncorrupted principal requires `spkHonest` and `pqspkHonest`. -/
def pqxdhKeyIndG2Impl (useRo : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp) := fun q => do
  match q with
  | .initiateOPK u i bundle =>
    let st ← get
    if (isHonestUncorruptedPeer P st.principals bundle.ikB).isSome then
      let (spkHon, _, pqspkHon) :=
        checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
      if !(spkHon && pqspkHon) then
        return .noneResp
      else
        pqxdhKeyIndImpl useRo S P (.initiateOPK u i bundle)
    else
      pqxdhKeyIndImpl useRo S P (.initiateOPK u i bundle)
  | .initiateNoOPK u i bundle =>
    let st ← get
    if (isHonestUncorruptedPeer P st.principals bundle.ikB).isSome then
      let (spkHon, _, pqspkHon) :=
        checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
      if !(spkHon && pqspkHon) then
        return .noneResp
      else
        pqxdhKeyIndImpl useRo S P (.initiateNoOPK u i bundle)
    else
      pqxdhKeyIndImpl useRo S P (.initiateNoOPK u i bundle)
  | q_other => pqxdhKeyIndImpl useRo S P q_other

noncomputable def badSigProbKeyInd (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyIndSim useRo S P A >>= fun (_, _, finalSt) =>
    pure (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)] {true}).toReal

noncomputable def badSigProbKeyIndAt (useRo : Bool) (S : Setup) (P : Primitives)
    (k : Nat) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[runKeyIndSim useRo S P A >>= fun (_, _, finalSt) =>
    pure (hasBadSigKeyIndAt S P k finalSt)] {true}).toReal

/-- Per-principal `SigEufCma` reduction bound for `KeyInd` and `HndlKeyInd`. -/
theorem badSigProbKeyIndAt_le_sigEufCma (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (k : Nat) (A : BoundedAdv (KeyIndAdversary S) b) :
    badSigProbKeyIndAt useRo S P k A.val ≤ SigEufCma P (sigReductionKeyIndAt useRo S b k A) := by
  unfold badSigProbKeyIndAt SigEufCma
  exact (ENNReal.toReal_le_toReal (MeasureTheory.measure_ne_top _ _) (MeasureTheory.measure_ne_top _
      _)).mpr
    (evalDist_badAt_keyInd_le_sigEufCmaExp useRo S P hP b k A)

theorem badSigProbKeyInd_le_sum (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    badSigProbKeyInd useRo S P A ≤
      ∑ k ∈ Finset.range S.N_id, badSigProbKeyIndAt useRo S P k A := by
  unfold badSigProbKeyInd badSigProbKeyIndAt
  have h_eq :
      (runKeyIndSim useRo S P A >>= fun (_, _, finalSt) =>
        pure (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)) =
      (runKeyIndSim useRo S P A >>= fun (_, _, finalSt) =>
        pure ((List.range S.N_id).any (fun k => hasBadSigKeyIndAt S P k finalSt))) := by
    congr 1; ext ⟨_, _, finalSt⟩
    dsimp only
    rw [hasBadSigKeyInd_eq_any_range S P finalSt]
  rw [h_eq]
  exact toReal_any_range_le_sum (runKeyIndSim useRo S P A) S.N_id
    (fun k (_, _, finalSt) => hasBadSigKeyIndAt S P k finalSt)

/-- Adding `hasBadSigKeyInd` to the abort condition changes the advantage by at most
`badSigProbKeyInd`. -/
theorem keyIndCore_hop_badSig_le_prob (useRo : Bool) (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    |(𝒟[keyIndExpG0_1Core useRo S P A].boolBias).toReal -
     (𝒟[keyIndExpG1Core useRo S P A].boolBias).toReal| ≤
      badSigProbKeyInd useRo S P A := by
  let allClean := fun (finalSt : KeyIndState S) =>
    finalSt.sessions.all (fun s =>
      !s.tested ||
          isKeyIndInitStillFresh P useRo finalSt.principals finalSt.spkBundles finalSt.respSessions
          s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested ||
          isKeyIndRespStillFresh P useRo finalSt.principals finalSt.spkBundles finalSt.sessions r)
  have h1 : keyIndExpG0_1Core useRo S P A =
      (runKeyIndSim useRo S P A >>= fun (secb, b', finalSt) =>
        if !(allClean finalSt) ||
           hasEcPkCollisionKeyInd P finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    simp [allClean, keyIndExpG0_1Core, runKeyIndSim, bind_assoc]
  have h2 : keyIndExpG1Core useRo S P A =
      (runKeyIndSim useRo S P A >>= fun (secb, b', finalSt) =>
        if (!(allClean finalSt) ||
           hasEcPkCollisionKeyInd P finalSt) ||
           (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals) then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
    have h2_0 : keyIndExpG1Core useRo S P A =
      (runKeyIndSim useRo S P A >>= fun (secb, b', finalSt) =>
        if (!(allClean finalSt) ||
           hasEcPkCollisionKeyInd P finalSt) ||
           hasBadSigKeyInd finalSt then
          $ᵗ Bool
        else
          pure (b' == secb)) := by
      simp [allClean, keyIndExpG1Core, runKeyIndSim, bind_assoc]
    rw [h2_0]
    congr 1; ext ⟨secb, b', finalSt⟩
    dsimp only
    have h_or :
        ((!(allClean finalSt) || hasEcPkCollisionKeyInd P finalSt) || hasBadSigKeyInd finalSt) =
        ((!(allClean finalSt) || hasEcPkCollisionKeyInd P finalSt) ||
          (hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)) := by
      cases hnp : noPrinPkColl P finalSt.principals
      · have hdup : hasDuplicateBytes (finalSt.principals.map (fun (_, e) => P.pow8 e.ikAPk)) =
          true := by
          unfold noPrinPkColl at hnp; simpa using hnp
        have hcoll : hasDuplicateBytes (allHonestEcPksKeyInd P finalSt) = true := by
          unfold allHonestEcPksKeyInd
          simp only [HasKeyIndState.toKeyIndState, List.append_assoc]
          exact hasDuplicateBytes_append_of_left _ _ hdup
        simp [hasEcPkCollisionKeyInd, hcoll]
      · simp
    rw [h_or]
  rw [h1, h2]
  exact abs_sub_boolBias_abort_or_le (runKeyIndSim useRo S P A)
    (fun (_, _, finalSt) => !(allClean finalSt) ||
      hasEcPkCollisionKeyInd P finalSt)
    (fun (_, _, finalSt) => hasBadSigKeyInd finalSt && noPrinPkColl P finalSt.principals)
    (fun (secb, b', _) => pure (b' == secb))

theorem keyInd_hop_badSig_le_sum (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG0_1 S P A - keyIndAdvG1 S P A| ≤
      ∑ k ∈ Finset.range S.N_id, badSigProbKeyIndAt true S P k A :=
  (keyIndCore_hop_badSig_le_prob true S P A).trans (badSigProbKeyInd_le_sum true S P A)

/-- Bounds `|keyIndAdvG0_1 - keyIndAdvG1|` by `N_id * SigEufCma`. -/
theorem keyInd_hop_sigEufCma_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyIndAdvG0_1 S P A.val - keyIndAdvG1 S P A.val| ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionKeyInd S b A) := by
  calc |keyIndAdvG0_1 S P A.val - keyIndAdvG1 S P A.val|
      ≤ ∑ k ∈ Finset.range S.N_id, badSigProbKeyIndAt true S P k A.val :=
        keyInd_hop_badSig_le_sum S P A.val
    _ ≤ ∑ k ∈ Finset.range S.N_id, SigEufCma P (sigReductionKeyIndAt true S b k A) :=
        Finset.sum_le_sum (fun k _ => badSigProbKeyIndAt_le_sigEufCma true S P hP b k A)
    _ ≤ (S.N_id : ℝ) * SigEufCma P (sigReductionKeyInd S b A) :=
        sum_sigReductionKeyInd_le S P b A

/-- Combined `G0 → G1` bound for `KeyInd`. -/
theorem keyInd_hop_G0_G1_le (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hP : CryptoWellFormedPrimitivesδ P) :
    |keyIndAdvG0 S P A.val - keyIndAdvG1 S P A.val| ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionKeyInd S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  have h0_01 :
      |keyIndAdvG0 S P A.val - keyIndAdvG0_1 S P A.val| ≤ ecCollProbKeyInd true S P A.val :=
    keyIndCore_hop_ecColl_le_prob true S P A.val
  have h_ec := ecCollProbKeyInd_le_bound true S P hP A.val
  have h01_1 := keyInd_hop_sigEufCma_le S P hP b A
  have h_tri := abs_sub_le (keyIndAdvG0 S P A.val) (keyIndAdvG0_1 S P A.val) (keyIndAdvG1 S P A.val)
  linarith

theorem keyInd_hop_G1_G2_le (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG1 S P A - keyIndAdvG2 S P A| ≤ 0 := by
  rw [keyIndAdvG1_eq_G2 S P A, sub_self, abs_zero]

/-- Combined `G0 → G2` bound for `KeyInd`. -/
theorem keyInd_hop_G0_G2_le (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hP : CryptoWellFormedPrimitivesδ P) :
    |keyIndAdvG0 S P A.val - keyIndAdvG2 S P A.val| ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionKeyInd S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  rw [← keyIndAdvG1_eq_G2 S P A.val]
  exact keyInd_hop_G0_G1_le S P b A hP

theorem keyInd_hop_ecColl_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG0 S P A - keyIndAdvG0_1 S P A| ≤ ecCollProbKeyInd true S P A :=
  keyIndCore_hop_ecColl_le_prob true S P A

theorem keyInd_hop_badSig_le_prob (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    |keyIndAdvG0_1 S P A - keyIndAdvG1 S P A| ≤ badSigProbKeyInd true S P A :=
  keyIndCore_hop_badSig_le_prob true S P A

end SignalPqxdh.Security

namespace SignalPqxdh

export Security (PreservesAt SatisfiesAt CommutesRel erasePrinSk eraseKeyInd badPeersKeyInd keyIndSigLens stepKeyIndForSig stepKeyIndForSigPrim simulateForSigPrim simulateKeyIndForSigPrim sigReductionKeyIndAt sigReductionKeyIndCoreRun sigReductionKeyIndCore sigReductionKeyInd sigReductionHndlKeyInd sigReduction sigReductionKeyInd_queries sigReductionKeyIndCore_prim_queries sigReductionKeyInd_prim_queries sum_sigReductionKeyIndCore_le sum_sigReductionKeyInd_le hasBadSigKeyIndAt hasBadSigKeyInd_eq_any_range sigHopTerm_nonneg isBadSigBundle pqxdhKeyIndG2Impl badSigProbKeyInd badSigProbKeyIndAt badSigProbKeyIndAt_le_sigEufCma badSigProbKeyInd_le_sum keyIndCore_hop_badSig_le_prob keyInd_hop_badSig_le_sum keyInd_hop_sigEufCma_le keyInd_hop_G0_G1_le keyInd_hop_G1_G2_le keyInd_hop_G0_G2_le keyInd_hop_ecColl_le_prob keyInd_hop_badSig_le_prob)

end SignalPqxdh

namespace Proofs.SignalPqxdh.Security

export _root_.SignalPqxdh.Security (PreservesAt SatisfiesAt CommutesRel erasePrinSk eraseKeyInd badPeersKeyInd keyIndSigLens stepKeyIndForSig stepKeyIndForSigPrim simulateForSigPrim simulateKeyIndForSigPrim sigReductionKeyIndAt sigReductionKeyIndCoreRun sigReductionKeyIndCore sigReductionKeyInd sigReductionHndlKeyInd sigReduction sigReductionKeyInd_queries sigReductionKeyIndCore_prim_queries sigReductionKeyInd_prim_queries sum_sigReductionKeyIndCore_le sum_sigReductionKeyInd_le hasBadSigKeyIndAt hasBadSigKeyInd_eq_any_range sigHopTerm_nonneg isBadSigBundle pqxdhKeyIndG2Impl badSigProbKeyInd badSigProbKeyIndAt badSigProbKeyIndAt_le_sigEufCma badSigProbKeyInd_le_sum keyIndCore_hop_badSig_le_prob keyInd_hop_badSig_le_sum keyInd_hop_sigEufCma_le keyInd_hop_G0_G1_le keyInd_hop_G1_G2_le keyInd_hop_G0_G2_le keyInd_hop_ecColl_le_prob keyInd_hop_badSig_le_prob)

end Proofs.SignalPqxdh.Security
