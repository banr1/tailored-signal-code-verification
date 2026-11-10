/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.CollisionsC
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.FgGapDhD
import VCVio.EvalDist.Monad.Basic

/-!
# `INT-CTXT` Slot Invariant and Send Coupling

Defines `RelProbDom`, `projectIntState`, and `IntSlotInv`, and proves the initiator send
coupling for `aeadIntReductionAuthCached`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

/-- One-sided heterogeneous relational dominance up to a right-hand bad/win event `bad`. -/
def RelProbDom {α5 α6 : Type} (R : α5 → α6 → Prop) (bad : α6 → Bool)
    (m5 : ProbComp α5) (m6 : ProbComp α6) : Prop :=
  ∀ (w5 : α5 → ℝ≥0∞) (w6 : α6 → ℝ≥0∞),
    (∀ y5, w5 y5 ≤ 1) →
    (∀ y6, bad y6 = true → w6 y6 = 1) →
    (∀ y5 y6, R y5 y6 → w5 y5 ≤ w6 y6) →
    probExpect m5 w5 ≤ probExpect m6 w6

theorem RelProbDom.of_pure {α5 α6 : Type} {R : α5 → α6 → Prop} {bad : α6 → Bool}
    {x5 : α5} {x6 : α6} (h : R x5 x6) :
    RelProbDom R bad (pure x5) (pure x6) := fun _ _ _ _ hle => by
  simp only [probExpect_pure]; exact hle x5 x6 h

theorem RelProbDom.bad6 {α5 α6 : Type} {R : α5 → α6 → Prop} {bad : α6 → Bool}
    (m5 : ProbComp α5) (m6 : ProbComp α6) (hbad : ∀ y6 ∈ support m6, bad y6 = true) :
    RelProbDom R bad m5 m6 := fun w5 w6 hw5 hw6 _ =>
  (probExpect_const_le_of_support m5 w5 1 (fun y5 _ => hw5 y5)).trans
    (probExpect_eq_const_of_support m6 w6 1 (fun y6 hy6 => hw6 y6 (hbad y6 hy6))).symm.le

theorem RelProbDom.bind_same {β α5 α6 : Type} {R : α5 → α6 → Prop} {bad : α6 → Bool}
    (mx : ProbComp β) {f5 : β → ProbComp α5} {f6 : β → ProbComp α6}
    (h : ∀ b, RelProbDom R bad (f5 b) (f6 b)) :
    RelProbDom R bad (mx >>= f5) (mx >>= f6) := fun w5 w6 hw5 hw6 hle => by
  rw [probExpect_bind, probExpect_bind]
  exact probExpect_mono_of_support mx _ _ (fun b _ => h b w5 w6 hw5 hw6 hle)

theorem RelProbDom.bind_same_of_support {β α5 α6 : Type} {R : α5 → α6 → Prop} {bad : α6 → Bool}
    (mx : ProbComp β) {f5 : β → ProbComp α5} {f6 : β → ProbComp α6}
    (h : ∀ b ∈ support mx, RelProbDom R bad (f5 b) (f6 b)) :
    RelProbDom R bad (mx >>= f5) (mx >>= f6) := fun w5 w6 hw5 hw6 hle => by
  rw [probExpect_bind, probExpect_bind]
  exact probExpect_mono_of_support mx _ _ (fun b hb => h b hb w5 w6 hw5 hw6 hle)

theorem RelProbDom.bind_rel {β5 β6 α5 α6 : Type}
    {R1 : β5 → β6 → Prop} {bad1 : β6 → Bool} {R2 : α5 → α6 → Prop} {bad2 : α6 → Bool}
    {m5 : ProbComp β5} {m6 : ProbComp β6} {f5 : β5 → ProbComp α5} {f6 : β6 → ProbComp α6}
    (hm : RelProbDom R1 bad1 m5 m6)
    (hbad : ∀ b6, bad1 b6 = true → ∀ y6 ∈ support (f6 b6), bad2 y6 = true)
    (hf : ∀ b5 b6, R1 b5 b6 → RelProbDom R2 bad2 (f5 b5) (f6 b6)) :
    RelProbDom R2 bad2 (m5 >>= f5) (m6 >>= f6) := fun w5 w6 hw5 hw6 hle => by
  rw [probExpect_bind, probExpect_bind]
  exact hm _ _ (fun _ => probExpect_const_le_of_support _ _ 1 (fun y5 _ => hw5 y5))
    (fun b6 hb6 => probExpect_eq_const_of_support _ _ 1 (fun y6 hy6 => hw6 y6 (hbad b6 hb6 y6 hy6)))
    (fun b5 b6 hR1 => hf b5 b6 hR1 w5 w6 hw5 hw6 hle)

def ValidAuthLengths (S : Setup) (hst : AuthHybridState S) : Prop :=
  ValidPrincipals S hst.base.principals ∧
  ValidSpkBundles S hst.base.spkBundles ∧
  ValidOpkEntries S hst.base.opkEntries ∧
  ValidSessionIds S hst.base.usedSendSessions ∧
  hst.idealSessions.length ≤ hst.base.usedSendSessions.length

theorem validAuthLengths_empty (S : Setup) (secb : Bool) :
    ValidAuthLengths S (AuthHybridState.empty S secb) :=
  ⟨(validEcLists_nil S).1, (validEcLists_nil S).2.1, (validEcLists_nil S).2.2.1,
   (validEcLists_nil S).2.2.2, le_rfl⟩

theorem validSessionIds_length_le (S : Setup) {sids : List (SessionId S)}
    (hV : ValidSessionIds S sids) : sids.length ≤ S.N_sess_tot := by
  have hNodup : (sids.map (sessSlotFlatIdx S)).Nodup := by
    have hEq : sids.map (ecSessSlotIdx S) =
        (sids.map (sessSlotFlatIdx S)).map (fun n => S.N_id + S.N_spk_tot + S.N_opk_tot + n) := by
      simp [List.map_map, Function.comp_def, ecSessSlotIdx]
    exact (hEq ▸ hV.2).of_map _
  have hSub : (sids.map (sessSlotFlatIdx S)).Subperm (List.range S.N_send_tot) :=
    hNodup.subperm (fun y hy => by
      rcases List.mem_map.mp hy with ⟨s, hs, rfl⟩
      exact List.mem_range.mpr (sessSlotFlatIdx_lt S s (hV.1 s hs)))
  have hle : sids.length ≤ S.N_send_tot := by simpa using hSub.length_le
  unfold Setup.N_sess_tot; omega

theorem validAuthLengths_bounds (S : Setup) (P : Primitives) {hst : AuthHybridState S}
    (hV : ValidAuthLengths S hst) :
    hst.base.principals.length ≤ S.N_dh ∧
    hst.base.spkBundles.length ≤ S.N_dh ∧
    hst.base.opkEntries.length ≤ S.N_dh ∧
    hst.idealSessions.length ≤ S.N_sess_tot := by
  have hTag := validTaggedPks_ecTaggedFromLists S P
    hst.base.principals hst.base.spkBundles hst.base.opkEntries []
    ⟨hV.1, hV.2.1, hV.2.2.1, (validEcLists_nil S).2.2.2⟩
  have hLen := validTaggedPks_length_le_fg hTag
  unfold ecTaggedFromLists at hLen
  simp only [List.length_append, List.length_map, List.length_nil] at hLen
  have hSess := hV.2.2.2.2.trans (validSessionIds_length_le S hV.2.2.2.1)
  exact ⟨by omega, by omega, by omega, hSess⟩

theorem validAdvKeysPow8_map (P : Primitives) (advKeys : List (Bytes × Bytes)) :
    ValidAdvKeysPow8 P (advKeys.map (fun (_, pk) => (P.pow8 pk, pk))) := by
  intro e he; rcases List.mem_map.mp he with ⟨⟨_, pk⟩, _, rfl⟩; rfl

theorem koskBundleOk_map_advKeys (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput) :
    koskBundleOk P principals spkBundles opkEntries
      (advKeys.map (fun (_, pk) => (P.pow8 pk, pk))) bundle =
    koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  have hReg : ∀ pk, isAdvRegistered P (advKeys.map (fun (_, pk) => (P.pow8 pk, pk))) pk =
      isAdvRegistered P advKeys pk := by
    intro pk; unfold isAdvRegistered; rw [List.any_map]; rfl
  unfold koskBundleOk; simp only [hReg]

theorem koskSenderOk_map_advKeys (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes) :
    koskSenderOk P principals (advKeys.map (fun (_, pk) => (P.pow8 pk, pk))) ikAPk =
    koskSenderOk P principals advKeys ikAPk := by
  unfold koskSenderOk isAdvRegistered; rw [List.any_map]; rfl

@[simp] theorem sim_fg_x25519 (P : Primitives) (sk pk : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.x25519 sk pk)) : ProbComp Bytes) = pure (P.x25519 sk pk) :=
        rfl
@[simp] theorem sim_fg_x25519Base (P : Primitives) (sk : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.x25519Base sk)) : ProbComp Bytes) = pure (P.x25519Base sk)
        := rfl
@[simp] theorem sim_fg_pow8 (P : Primitives) (pk : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.pow8 pk)) : ProbComp Bytes) = pure (P.pow8 pk) := rfl
@[simp] theorem sim_fg_isCanonical (P : Primitives) (pk : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.isCanonical pk)) : ProbComp Bool) = pure (P.isCanonical pk)
        := rfl
@[simp] theorem sim_fg_sigVerify (P : Primitives) (pk msg sig : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.sigVerify pk msg sig)) : ProbComp Bool)
        = pure (P.sigVerify pk msg sig) := rfl
@[simp] theorem sim_fg_kemEncaps (P : Primitives) (ek m : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.kemEncaps ek m)) : ProbComp (Option (Bytes × Bytes)))
        = pure (P.kemEncaps ek m) := rfl
@[simp] theorem sim_fg_kemDecaps (P : Primitives) (dk ct : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.kemDecaps dk ct)) : ProbComp (Option Bytes))
        = pure (P.kemDecaps dk ct) := rfl
@[simp] theorem sim_fg_chainKdfSeed (P : Primitives) (ck : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.chainKdfSeed ck)) : ProbComp Bytes)
        = pure (P.chainKdfSeed ck) := rfl
@[simp] theorem sim_fg_chainKdfNext (P : Primitives) (ck : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.chainKdfNext ck)) : ProbComp Bytes)
        = pure (P.chainKdfNext ck) := rfl
@[simp] theorem sim_fg_spqrInitSend (P : Primitives) (k r : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.spqrInitSend k r))
        : ProbComp (Option (Bytes × Option Bytes × Bytes))) = pure (P.spqrInitSend k r) := rfl
@[simp] theorem sim_fg_spqrInitRecv (P : Primitives) (k m : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.spqrInitRecv k m))
        : ProbComp (Option (Bytes × Option Bytes))) = pure (P.spqrInitRecv k m) := rfl
@[simp] theorem sim_fg_deriveMsgKeys (P : Primitives) (seed : Bytes) (salt? : Option Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.deriveMsgKeys seed salt?)) : ProbComp MessageKeys)
        = pure (P.deriveMsgKeys seed salt?) := rfl
@[simp] theorem sim_fg_aeadDec (P : Primitives) (mk : MessageKeys) (ad ct : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.aeadDec mk ad ct)) : ProbComp (Option Bytes))
        = pure (P.aeadDec mk ad ct) := rfl
@[simp] theorem sim_fg_sigPkGen (P : Primitives) (sk : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.sigPkGen sk)) : ProbComp Bytes) = pure (P.sigPkGen sk) :=
        rfl
@[simp] theorem sim_fg_sigSign (P : Primitives) (sk msg r : Bytes) :
    (simulateQ (primBaseImpl P) (primQ (.sigSign sk msg r)) : ProbComp Bytes)
        = pure (P.sigSign sk msg r) := rfl

theorem evalAuthHybridSendSchedule_g3_8 (P : Primitives)
    (roCache : List (Bytes × DRKey))
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (isIdealSend : Bool) (secrets dhRatchet : Bytes) :
    evalAuthHybridSendSchedule .g3_8 true P roCache rootRoCache isIdealSend secrets dhRatchet =
      (if isIdealSend then do
        let dk ← sampleDRKey96; let r ← sampleBytes32; let c ← sampleBytes32
        let ms ← sampleBytes32; let cn ← sampleBytes32
        pure (dk, roCache, (r, c), rootRoCache, (ms, cn))
      else do
        let (dk, roCache') ← evalHkdfRoPure roCache secrets
        let ((r, c), rootRoCache') ← evalRootKdfRoPure rootRoCache dk.rootKey dhRatchet
        pure (dk, roCache', (r, c), rootRoCache', (P.chainKdfSeed c, P.chainKdfNext c))) := by
  cases isIdealSend <;> rfl

end SignalPqxdh.Security
