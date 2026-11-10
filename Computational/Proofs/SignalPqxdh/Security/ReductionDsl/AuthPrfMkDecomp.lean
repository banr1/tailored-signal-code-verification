/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkShallow
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
import VCVio.EvalDist.Monad.Basic

/-!
# Shallow Decomposition of `authMkStepReduction`

Proves that `authMkStepReduction` equals the combined shallow step `prfMkStepC` with the
challenger-query count dropped.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl
open SignalPqxdh SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open OracleSpec OracleComp

variable {S : Setup}

@[simp] theorem sec_embedPrim_eq_fg {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) :
    SignalPqxdh.Security.embedPrim (spec := spec) mx = FgGapDh.embedPrim (spec := spec) mx := rfl

theorem prfMkRunPre_bind {β : Type} (m : OracleComp PrimBaseSpec β)
    (k : β → OracleComp PrimBaseSpec (MkPre S)) (sc : Bool) :
    prfMkRunPre (m >>= k) sc = embedPrimMk m >>= fun b => prfMkRunPre (k b) sc := by
  unfold prfMkRunPre
  simp only [embedPrimMk, sec_embedPrim_eq_fg, embedPrim_bind, bind_assoc]

theorem prfMkRunPre_pure_inl (x : AuthResponse × AuthHybridStateFixed S) (sc : Bool) :
    prfMkRunPre (pure (Sum.inl x) : OracleComp PrimBaseSpec (MkPre S)) sc = pure (x, 0, sc) := by
  simp [prfMkRunPre]

theorem prfMkRunPre_pure_inr (salt? : Option Bytes) (c : MkCont S) (sc : Bool) :
    prfMkRunPre (pure (Sum.inr (salt?, c)) : OracleComp PrimBaseSpec (MkPre S)) sc =
      (do let mk ← deriveMkQ salt?
          let res ← embedPrimMk (c.post mk)
          return (res, 1, sc || c.isSend)) := by
  simp [prfMkRunPre]

theorem prfMkRunPre_map_inl (m : OracleComp PrimBaseSpec (AuthResponse × AuthHybridStateFixed S))
    (sc : Bool) :
    prfMkRunPre (Sum.inl <$> m) sc = (fun x => (x, 0, sc)) <$> embedPrimMk m := by
  rw [map_eq_bind_pure_comp, prfMkRunPre_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_apply, prfMkRunPre_pure_inl]
  rfl

theorem prfMkRunPre_map {β : Type} (f : β → MkPre S) (m : OracleComp PrimBaseSpec β) (sc : Bool) :
    prfMkRunPre (f <$> m) sc = embedPrimMk m >>= fun b => prfMkRunPre (pure (f b)) sc := by
  rw [map_eq_bind_pure_comp, prfMkRunPre_bind]; rfl

attribute [local simp] prfMkRunPre_bind prfMkRunPre_map prfMkRunPre_pure_inl prfMkRunPre_pure_inr

theorem authMkSendReduction_eq (idx : Nat) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S) (sc : Bool) :
    authMkSendReduction S idx sid u bundle m0 m1 hst sc =
      (fun x => (x.1, x.2.2)) <$> prfMkRunPre (mkSendPre S idx sid u bundle m0 m1 hst sc) sc := by
  unfold authMkSendReduction mkSendPre
  simp only [prfMkRunPre_bind, map_bind, embedUnifMk]
  congr 1; funext p
  cases p with
  | done resp hst' => simp [prfMkRunPre_pure_inl]
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
      pqRatchetMsg msgPlain =>
    simp only
    split_ifs with h1 h2
    · obtain ⟨hsc, -⟩ : sc = false ∧ _ := by simpa using h1
      subst hsc
      simp [MkCont.post, MkCont.isSend]
    · simp
    · simp

private theorem mkUnmatchedSlotsPre_eq (idx : Nat) (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (cache : AuthMkSaltCache S) (slots' : AuthSlotState) (sc : Bool) :
    (fun x => (x.1, x.2.2)) <$>
        prfMkRunPre (mkUnmatchedSlotsPre S idx msg prep drKey rk1 spqrSalt? rSlot recvCount' cache
          slots' sc) sc =
      (fun r => (r, sc)) <$>
        finishAuthRecvUnmatchedSlotsReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
          cache slots' sc := by
  unfold mkUnmatchedSlotsPre finishAuthRecvUnmatchedSlotsReduction
  split_ifs with h1 h2 <;> simp [embedUnifMk, MkCont.post, MkCont.isSend]

theorem mkUnmatchedPre_eq (idx : Nat) (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (cache : AuthMkSaltCache S) (sc : Bool) :
    (fun x => (x.1, x.2.2)) <$>
        prfMkRunPre (mkUnmatchedPre S idx msg prep drKey rk1 spqrSalt? rSlot recvCount' cache sc)
          sc =
      (fun r => (r, sc)) <$>
        finishAuthRecvUnmatchedReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
          cache sc :=
  mkUnmatchedSlotsPre_eq idx msg prep drKey rk1 spqrSalt? rSlot recvCount' cache {} sc

private theorem mkMatchedSameEphSlotsPre_eq (idx : Nat) (msg : PreKeyMsg)
    (prep : PreparedAuthRecvPrim S)
    (s : IdealAuthSession S) (sIdx : Nat) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (cache : AuthMkSaltCache S) (slots : AuthSlotState) (sc : Bool) :
    (fun x => (x.1, x.2.2)) <$>
        prfMkRunPre (mkMatchedSameEphSlotsPre S idx msg prep s sIdx spqrSalt? recvCount cache
          slots) sc =
      (fun r => (r, sc)) <$>
        (do let p ← matchedSameEphMkSlotsReduction S idx s sIdx spqrSalt? recvCount cache
            embedPrimMk (finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1)
              p.2 slots p.1)) := by
  unfold mkMatchedSameEphSlotsPre matchedSameEphMkSlotsReduction
  by_cases ha : sIdx = idx
  · by_cases hc : sameSaltKey spqrSalt? s.spqrSalt? = true
    · simp [ha, hc]
    · simp [ha, hc]
      split <;> rename_i heq <;> simp [heq, MkCont.post, MkCont.isSend]
  · by_cases hb : sIdx < idx
    · by_cases hc : sameSaltKey spqrSalt? s.spqrSalt? = true
      · simp [ha, hb, hc]
      · simp [ha, hb, hc]
        split <;> rename_i heq <;> simp [heq]
    · simp [ha, hb]

theorem mkMatchedSameEphPre_eq (idx : Nat) (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S)
    (s : IdealAuthSession S) (spqrSalt? : Option Bytes) (recvCount : Nat)
    (cache : AuthMkSaltCache S) (sc : Bool) :
    (fun x => (x.1, x.2.2)) <$>
        prfMkRunPre (mkMatchedSameEphPre S idx msg prep s spqrSalt? recvCount cache) sc =
      (fun r => (r, sc)) <$>
        (do let p ← matchedSameEphMkReduction S idx s spqrSalt? recvCount cache
            embedPrimMk (finishAuthRecvMkPrim S msg prep s.drKey s.rk1 s.ck1_1 (recvCount + 1)
              p.2 p.1)) :=
  mkMatchedSameEphSlotsPre_eq idx msg prep s (sessionSlotIndex s.sid) spqrSalt? recvCount cache {}
    sc

theorem mkRecvPre_eq (idx : Nat) (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sc : Bool) :
    (fun x => (x.1, x.2.2)) <$> prfMkRunPre (mkRecvPre S idx msg prep? hst sc) sc =
      (fun r => (r, sc)) <$> authMkRecvReduction S idx msg prep? hst sc := by
  unfold mkRecvPre authMkRecvReduction
  rcases prep? with _ | prep
  · simp
  · simp only
    by_cases hI : (prep.matchedSess?.isSome || prep.isUncorruptedHonestSender) = true
    · simp only [hI, ↓reduceIte]
      rcases hm : prep.matchedSess? with _ | s
      · simp only
        simp only [prfMkRunPre_bind, map_bind, embedUnifMk]
        refine bind_congr fun drKey => ?_
        try simp only [prfMkRunPre_bind, map_bind]
        refine bind_congr fun rk1 => ?_
        try simp only [prfMkRunPre_bind, map_bind]
        refine bind_congr fun o => ?_
        rcases o with _ | ⟨_, salt?⟩
        · simp
        · exact mkUnmatchedSlotsPre_eq ..
      · simp only
        by_cases hE : prep.sameEph = true
        · simp only [hE, ↓reduceIte]
          simp only [prfMkRunPre_bind, map_bind]
          refine bind_congr fun o => ?_
          rcases o with _ | ⟨_, salt?⟩
          · simp
          · exact mkMatchedSameEphSlotsPre_eq ..
        · simp only [hE, ↓reduceIte, Bool.false_eq_true]
          simp only [prfMkRunPre_bind, map_bind, embedUnifMk]
          refine bind_congr fun rk1 => ?_
          try simp only [prfMkRunPre_bind, map_bind]
          refine bind_congr fun o => ?_
          rcases o with _ | ⟨_, salt?⟩
          · simp
          · exact mkUnmatchedSlotsPre_eq ..
    · simp only [hI, ↓reduceIte, Bool.false_eq_true]
      simp only [prfMkRunPre_bind, map_bind]
      refine bind_congr fun x => ?_
      try simp only [prfMkRunPre_bind, map_bind]
      refine bind_congr fun y => ?_
      try simp only [prfMkRunPre_bind, map_bind]
      refine bind_congr fun mkSeed => ?_
      try simp only [prfMkRunPre_bind, map_bind]
      refine bind_congr fun ck => ?_
      try simp only [prfMkRunPre_bind, map_bind]
      refine bind_congr fun o => ?_
      rcases o with _ | ⟨_, salt?⟩
      · simp
      · simp

/-- `authMkStepReduction` equals the combined shallow step `prfMkStepC` with the challenger-query
count dropped. -/
theorem authMkStepReduction_eq (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (sc : Bool) :
    authMkStepReduction S idx q hst sc = (fun x => (x.1, x.2.2)) <$> prfMkStepC S idx q hst sc := by
  unfold prfMkStepC
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [authMkStepReduction, mkPre]
    split_ifs
    · simp
    · exact authMkSendReduction_eq ..
  | sendNoOPK u i bundle m0 m1 =>
    simp only [authMkStepReduction, mkPre]
    split_ifs
    · simp
    · exact authMkSendReduction_eq ..
  | recvOPK k j o msg =>
    simp only [authMkStepReduction, mkPre, prfMkRunPre_bind, map_bind]
    refine bind_congr fun prep? => ?_
    rw [mkRecvPre_eq]; simp
  | recvNoOPK k j l msg =>
    simp only [authMkStepReduction, mkPre, prfMkRunPre_bind, map_bind]
    refine bind_congr fun prep? => ?_
    rw [mkRecvPre_eq]; simp
  | _ =>
    simp only [authMkStepReduction, mkPre, prfMkRunPre_map_inl]
    simp

end SignalPqxdh.Security.ReductionDsl.AuthPrf
