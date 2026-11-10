/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C1
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C2
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import VCVio.EvalDist.Monad.Basic

/-!
# One-Shot `G3.8 → split(.g3_8, .g5)` Up-To-Bad Coupling

Defines the all-sessions forgery indicator `authIntForgedAll` and proves that `G3.8` and
`split(.g3_8, .g5, true)` differ by at most `Pr[authIntForgeAllExp = true]`
(`auth_hop_G3_8_split_g5_le_forgeAll`).
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

def authRecvPtAtStage {S : Setup} (stage : AuthHybridStage) (P : Primitives)
    (useIdealBranch sameMsgKeys isUncorruptedHonestSender : Bool)
    (matchedSess? : Option (IdealAuthSession S))
    (deriveMessageKeys : MessageKeys) (ad aeadCt : Bytes) : Option Bytes :=
  if useIdealBranch then
    if sameMsgKeys && stage.idealFreshAead then
      match matchedSess? with
      | some s => if ad == s.ad && aeadCt == s.aeadCt then some s.msgPlain else none
      | none   => none
    else if !sameMsgKeys && isUncorruptedHonestSender && stage.idealUnmatchedRecvAead then
      none
    else
      P.aeadDec deriveMessageKeys ad aeadCt
  else
    P.aeadDec deriveMessageKeys ad aeadCt

/-- All-sessions forgery indicator for the `G3.8 → split(.g3_8, .g5)` receive coupling. -/
def authIntForgedAll {S : Setup} (P : Primitives)
    (useIdealBranch sameMsgKeys isUncorruptedHonestSender : Bool)
    (matchedSess? : Option (IdealAuthSession S))
    (deriveMessageKeys : MessageKeys) (ad aeadCt : Bytes) : Bool :=
  if useIdealBranch then
    if sameMsgKeys then
      match matchedSess? with
      | some s => !(ad == s.ad && aeadCt == s.aeadCt) && (P.aeadDec deriveMessageKeys ad aeadCt).isSome
      | none => (P.aeadDec deriveMessageKeys ad aeadCt).isSome
    else
      isUncorruptedHonestSender && (P.aeadDec deriveMessageKeys ad aeadCt).isSome
  else
    false

theorem authRecvPtAtStage_g3_8_eq_g5_of_forgedAll_false {S : Setup}
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (useIdealBranch sameMsgKeys isUncorruptedHonestSender : Bool)
    (matchedSess? : Option (IdealAuthSession S))
    (deriveMessageKeys : MessageKeys) (ad aeadCt : Bytes)
    (hSessValid : ∀ s, matchedSess? = some s →
      (useIdealBranch = true → sameMsgKeys = true → deriveMessageKeys = s.deriveMessageKeys) ∧
      s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain)
    (hNoForge : authIntForgedAll P useIdealBranch sameMsgKeys isUncorruptedHonestSender
      matchedSess? deriveMessageKeys ad aeadCt = false) :
    authRecvPtAtStage .g3_8 P useIdealBranch sameMsgKeys isUncorruptedHonestSender
      matchedSess? deriveMessageKeys ad aeadCt =
    authRecvPtAtStage .g5 P useIdealBranch sameMsgKeys isUncorruptedHonestSender
      matchedSess? deriveMessageKeys ad aeadCt := by
  unfold authRecvPtAtStage authIntForgedAll at *
  simp only [AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte] at hNoForge ⊢
  cases useIdealBranch with
  | false => rfl
  | true =>
    simp only [↓reduceIte] at hNoForge ⊢
    cases sameMsgKeys with
    | true =>
      simp only [↓reduceIte] at hNoForge ⊢
      cases matchedSess? with
      | none =>
        simp only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hNoForge
        exact hNoForge
      | some s =>
        rcases hSessValid s rfl with ⟨hMkEq, hCtEq⟩
        have hMk := hMkEq rfl rfl; subst hMk
        dsimp only at hNoForge ⊢
        cases hAdCt : (ad == s.ad && aeadCt == s.aeadCt) with
        | true =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hAdCt
          rcases hAdCt with ⟨rfl, rfl⟩; simp [hCtEq, hWF.aead_corr]
        | false =>
          simp only [hAdCt, Bool.not_false, Bool.true_and, Option.isSome_eq_false_iff,
            Option.isNone_iff_eq_none] at hNoForge
          simp [hNoForge]
    | false =>
      cases isUncorruptedHonestSender with
      | false => simp
      | true =>
        simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hNoForge ⊢
        exact hNoForge

def evalAuthRecvScheduleForgeAll {S : Setup} (withForge : Bool) (stage : AuthHybridStage)
    (P : Primitives)
    (hst : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    ProbComp ((Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))) × AuthMkSaltCache S) × Bool) := do
  let st := hst.base
  let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
  let isUncorruptedHonestSender : Bool :=
    match senderPrincipal? with | some (_, sEntry) => !sEntry.corrupted | none => false
  let matchedSess? : Option (IdealAuthSession S) :=
    hst.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
  let useIdealBranch : Bool := matchedSess?.isSome || isUncorruptedHonestSender
  let (drKey, roCache') ←
    if useIdealBranch && true then
      match matchedSess? with
      | some s => pure (s.drKey, st.roCache)
      | none   => do let dk ← sampleDRKey96; pure (dk, st.roCache)
    else evalHkdfOrRo true P st.roCache secrets
  let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
  let sameEph : Bool :=
    match matchedSess? with | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk | none => false
  let ((rk1, ck1_0), rootRoCache') ←
    if useIdealBranch && true then
      match matchedSess? with
      | some s =>
        if sameEph then pure ((s.rk1, s.ck1_0), st.rootRoCache)
        else do let r ← sampleBytes32; let c ← sampleBytes32; pure ((r, c), st.rootRoCache)
      | none => do let r ← sampleBytes32; let c ← sampleBytes32; pure ((r, c), st.rootRoCache)
    else evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
  let (mkSeed, ck1_1) ←
    if useIdealBranch && true then
      match matchedSess? with
      | some s =>
        if sameEph then pure (s.mkSeed, s.ck1_1)
        else do let ms ← sampleBytes32; let cn ← sampleBytes32; pure (ms, cn)
      | none => do let ms ← sampleBytes32; let cn ← sampleBytes32; pure (ms, cn)
    else pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none => return ((none, mkSaltCache), false)
  | some (_pqrStB, spqrSalt?) =>
    let sameMsgKeys : Bool :=
      match matchedSess? with
      | some s => sameEph && (sameSaltKey spqrSalt? s.spqrSalt?)
      | none => false
    let (deriveMessageKeys, mkSaltCache') ←
      if useIdealBranch && true then
        match matchedSess? with
        | some s =>
          if sameMsgKeys then pure (s.deriveMessageKeys, mkSaltCache)
          else if sameEph then
            match mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | some (_, (_, mk)) => pure (mk, mkSaltCache)
            | none => do
              let mk ← sampleMessageKeys80
              pure (mk, ((s.sid, spqrSalt?), (recvCount, mk)) :: mkSaltCache)
          else do let mk ← sampleMessageKeys80; pure (mk, mkSaltCache)
        | none => do let mk ← sampleMessageKeys80; pure (mk, mkSaltCache)
      else pure (P.deriveMsgKeys mkSeed spqrSalt?, mkSaltCache)
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let pt? := authRecvPtAtStage stage P useIdealBranch sameMsgKeys
      isUncorruptedHonestSender matchedSess? deriveMessageKeys ad msg.aeadCt
    let forgedHere :=
      if withForge then
        authIntForgedAll P useIdealBranch sameMsgKeys isUncorruptedHonestSender matchedSess?
          deriveMessageKeys ad msg.aeadCt
      else false
    let res? :=
      match pt? with
      | none => none
      | some pt => some (drKey, rk1, ck1_1, pt, roCache', rootRoCache')
    return ((res?, mkSaltCache'), forgedHere)

theorem optRes_bind_aux {α γ C : Type} (o : Option Bytes) (g : Bytes → α) (c : C)
    (f : Option α × C → ProbComp γ) :
    f ((match o with | none => none | some pt => some (g pt)), c) =
      ((match o with | none => pure (none, c) | some pt => pure (some (g pt), c)) >>= f) := by
  cases o <;> simp

theorem evalAuthRecvScheduleForgeAll_fst {S : Setup} (withForge : Bool)
    (stage : AuthHybridStage) (hStage : stage = .g3_8 ∨ stage = .g5) (P : Primitives)
    (hst : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    {β : Type} (f : (Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))) × AuthMkSaltCache S) → ProbComp β) :
    (evalAuthRecvScheduleForgeAll withForge stage P hst recvCount mkSaltCache
        kEntry bEntry opkPk? secrets msg >>= fun p => f p.1) =
    (evalAuthFixedRecvScheduleCached stage true P hst recvCount mkSaltCache kEntry bEntry opkPk?
        secrets msg >>= f) := by
  rcases hStage with rfl | rfl <;>
  · unfold evalAuthRecvScheduleForgeAll evalAuthFixedRecvScheduleCached
    simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk, AuthHybridStage.idealCk,
      AuthHybridStage.idealMsgKeys]
    refine drKey_step_bind_congr _ _ _ _ _ _ _ _ (fun ⟨drKey, roCache'⟩ => ?_); try dsimp only
    refine rk_ck_step_bind_congr _ _ _ (fun s => ((s.rk1, s.ck1_0), hst.base.rootRoCache))
      (fun r c => ((r, c), hst.base.rootRoCache)) _ _ _ _ _ (fun ⟨⟨rk1, ck1_0⟩,
          rootRoCache'⟩ => ?_); try dsimp only
    refine rk_ck_step_bind_congr _ _ _ (fun s => (s.mkSeed, s.ck1_1))
      (fun ms cn => (ms, cn)) _ _ _ _ _ (fun ⟨mkSeed, ck1_1⟩ => ?_); try dsimp only
    rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩
    · simp
    · dsimp only
      refine msgKeys_step_bind_congr (S := S) _ _ _ _ _ _ _ _ _ _ _ _ (fun ⟨deriveMessageKeys,
          mkSaltCache'⟩ => ?_)
      simp only [pure_bind]
      exact optRes_bind_aux _ _ _ _

def pqxdhAuthForgeAllImpl (withForge : Bool) (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S × Bool) ProbComp) := fun q =>
  StateT.mk fun ⟨hst, forged⟩ =>
    match q with
    | .recvOPK k j o msg =>
      match prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
      | none => pure (.noneResp, ({ hst with recvCount := hst.recvCount + 1 }, forged))
      | some prep =>
        (fun ((res?, mkSaltCache'), forgedHere) =>
          let (resp, hst') := prep.finish res?
          (resp, ({
            toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                mkSaltCache' },
            forged || forgedHere))) <$>
          evalAuthRecvScheduleForgeAll withForge stage P prep.hstDec
            hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    | .recvNoOPK k j l msg =>
      match prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
      | none => pure (.noneResp, ({ hst with recvCount := hst.recvCount + 1 }, forged))
      | some prep =>
        (fun ((res?, mkSaltCache'), forgedHere) =>
          let (resp, hst') := prep.finish res?
          (resp, ({
            toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                mkSaltCache' },
            forged || forgedHere))) <$>
          evalAuthRecvScheduleForgeAll withForge stage P prep.hstDec
            hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
    | qOther =>
      (fun (resp, hst') => (resp, (hst', forged))) <$>
        (pqxdhAuthHybridSplitFixedImpl .g3_8 .g3_8 true true S P qOther).run hst

/-- Experiment running `A` against `split(.g3_8, .g5, true)` and returning whether
    `authIntForgedAll` ever held. -/
noncomputable def authIntForgeAllExp (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := (AuthHybridStateFixed.empty S secb, false)
  let impl :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
          ProbComp) +
    pqxdhAuthForgeAllImpl true .g5 S P
  let (_b', _finalSt, forged) ← (simulateQ impl A.run).run initSt
  return forged

theorem pqxdhAuthForgeAllImpl_fst (withForge : Bool) (stage : AuthHybridStage)
    (hStage : stage = .g3_8 ∨ stage = .g5)
    (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (forged : Bool)
    {β : Type} (f : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp β) :
    ((pqxdhAuthForgeAllImpl withForge stage S P q).run (hst, forged) >>=
      fun p => f (p.1, p.2.1)) =
    ((pqxdhAuthHybridSplitFixedImpl .g3_8 stage true true S P q).run hst >>= f) := by
  have hIdeal : stage.idealMsgKeys = true := by rcases hStage with rfl | rfl <;> rfl
  cases q with
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthForgeAllImpl, pqxdhAuthHybridSplitFixedImpl, StateT.run_mk]
    simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind,
      pqxdhAuthHybridFixedImpl_recvOPK_eq stage hIdeal]
    cases prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none => simp
    | some prep =>
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      exact evalAuthRecvScheduleForgeAll_fst withForge stage hStage P prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        (fun x => f ((prep.finish x.1).1,
          {
            toAuthHybridState := (prep.finish x.1).2, recvCount := hst.recvCount + 1, mkSaltCache :=
                x.2 }))
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthForgeAllImpl, pqxdhAuthHybridSplitFixedImpl, StateT.run_mk]
    simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind,
      pqxdhAuthHybridFixedImpl_recvNoOPK_eq stage hIdeal]
    cases prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none => simp
    | some prep =>
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      exact evalAuthRecvScheduleForgeAll_fst withForge stage hStage P prep.hstDec
        hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        (fun x => f ((prep.finish x.1).1,
          {
            toAuthHybridState := (prep.finish x.1).2, recvCount := hst.recvCount + 1, mkSaltCache :=
                x.2 }))
  | _ =>
    have hg38 : AuthHybridStage.g3_8.idealMsgKeys = true := rfl
    dsimp only [pqxdhAuthForgeAllImpl, StateT.run_mk]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    unfold pqxdhAuthHybridSplitFixedImpl
    simp [hIdeal, hg38]

theorem simulateQ_pqxdhAuthForgeAllImpl_fst {α β : Type}
    (withForge : Bool) (stage : AuthHybridStage) (hStage : stage = .g3_8 ∨ stage = .g5)
    (S : Setup) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S) (forged : Bool)
    (f : α × AuthHybridStateFixed S → ProbComp β) :
    let implForge :=
        (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
            ProbComp) +
      pqxdhAuthForgeAllImpl withForge stage S P
    let implSplit := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthHybridStateFixed S) ProbComp) +
      pqxdhAuthHybridSplitFixedImpl .g3_8 stage true true S P
    ((simulateQ implForge oa).run (hst, forged) >>= fun p => f (p.1, p.2.1)) =
      ((simulateQ implSplit oa).run hst >>= f) := by
  intro implForge implSplit
  induction oa using OracleComp.inductionOn generalizing hst forged with
  | pure a => simp
  | query_bind q mx ih =>
    rcases q with uq | aq
    · dsimp only [implForge, implSplit]
      rw [FgGapDh.simulateQ_run_query_inl, FgGapDh.simulateQ_run_query_inl, bind_assoc, bind_assoc]
      congr 1; funext u; exact ih u hst forged
    · dsimp only [implForge, implSplit]
      rw [FgGapDh.simulateQ_run_query_inr, FgGapDh.simulateQ_run_query_inr, bind_assoc, bind_assoc]
      rw [← pqxdhAuthForgeAllImpl_fst withForge stage hStage S P aq hst forged
        (fun y => (simulateQ implSplit (mx y.1)).run y.2 >>= f)]
      congr 1; funext ⟨r, hst', forged'⟩; exact ih r hst' forged'

theorem pqxdhAuthForgeAllImpl_bad_mono (withForge : Bool) (stage : AuthHybridStage)
    (S : Setup) (P : Primitives) (q : AuthQuery S)
    (s6 : AuthHybridStateFixed S × Bool) (hBad : s6.2 = true) :
    ∀ y ∈ support ((pqxdhAuthForgeAllImpl withForge stage S P q).run s6),
      y.2.2 = true := by
  rcases s6 with ⟨hst, forged⟩; dsimp only at hBad; subst hBad; intro y hy
  cases q with
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthForgeAllImpl, StateT.run_mk] at hy
    cases hprep : prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none => simp only [hprep, support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hy
      rcases hy with ⟨⟨⟨res?, mkSaltCache'⟩, forgedHere⟩, _, rfl⟩; simp
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthForgeAllImpl, StateT.run_mk] at hy
    cases hprep : prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none => simp only [hprep, support_pure, Set.mem_singleton_iff] at hy; subst hy; rfl
    | some prep =>
      simp only [hprep, support_map, Set.mem_image] at hy
      rcases hy with ⟨⟨⟨res?, mkSaltCache'⟩, forgedHere⟩, _, rfl⟩; simp
  | _ =>
    dsimp only [pqxdhAuthForgeAllImpl, StateT.run_mk] at hy
    simp only [support_map, Set.mem_image] at hy; rcases hy with ⟨⟨resp, hst'⟩, _, rfl⟩; rfl

theorem relProbUpToBad_evalAuthRecvScheduleForgeAll {S : Setup}
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (hst : AuthHybridState S)
    (hInv : ∀ s ∈ hst.idealSessions,
      s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧ initSessionSlotIdx s.sid < S.N_send_tot)
    (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    RelProbUpToBad
      (fun p5 p6 => p5.1.1 = p6.1.1 ∧ p5.1.2 = p6.1.2 ∧ p5.2 = false ∧ p6.2 = false)
      (fun p6 => p6.2)
      (evalAuthRecvScheduleForgeAll false .g3_8 P hst recvCount mkSaltCache
        kEntry bEntry opkPk? secrets msg)
      (evalAuthRecvScheduleForgeAll true .g5 P hst recvCount mkSaltCache
        kEntry bEntry opkPk? secrets msg) := by
  unfold evalAuthRecvScheduleForgeAll; dsimp only
  refine relProbUpToBad_drKey_step _ _ _ _ _ _ (fun ⟨drKey, roCache'⟩ => ?_); dsimp only
  refine relProbUpToBad_rk_ck_step _ _ _ (fun s => ((s.rk1, s.ck1_0), hst.base.rootRoCache))
    (fun r c => ((r, c), hst.base.rootRoCache)) _ _ _ (fun ⟨⟨rk1, ck1_0⟩,
        rootRoCache'⟩ => ?_); dsimp only
  refine relProbUpToBad_rk_ck_step _ _ _ (fun s => (s.mkSeed, s.ck1_1))
    (fun ms cn => (ms, cn)) _ _ _ (fun ⟨mkSeed, ck1_1⟩ => ?_); dsimp only
  rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩
  · exact RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, rfl⟩
  · dsimp only
    apply relProbUpToBad_msgKeys_step
    rintro ⟨deriveMessageKeys, mkSaltCache'⟩ hMkEq; dsimp only
    let senderPrincipal? := findHonestPrincipal P hst.base.principals msg.hdr.ikAPk
    let isUncorruptedHonestSender : Bool :=
      match senderPrincipal? with | some (_, sEntry) => !sEntry.corrupted | none => false
    let matchedSess? : Option (IdealAuthSession S) :=
      hst.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
    let useIdealBranch : Bool := matchedSess?.isSome || isUncorruptedHonestSender
    let sameEph : Bool :=
      match matchedSess? with | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk | none => false
    let sameMsgKeys : Bool :=
      match matchedSess? with
      | some s => sameEph && (sameSaltKey spqrSalt? s.spqrSalt?)
      | none => false
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    by_cases hForge : authIntForgedAll P useIdealBranch sameMsgKeys
        isUncorruptedHonestSender matchedSess? deriveMessageKeys ad msg.aeadCt = true
    · refine RelProbUpToBad.bad6 _ _ (fun y6 hy6 => ?_)
      simp only [support_pure, Set.mem_singleton_iff] at hy6; subst hy6; simpa using hForge
    · have hNoForge : authIntForgedAll P useIdealBranch sameMsgKeys
          isUncorruptedHonestSender matchedSess? deriveMessageKeys ad msg.aeadCt = false :=
        Bool.eq_false_iff.mpr hForge
      have hSessValid : ∀ s, matchedSess? = some s →
          (useIdealBranch = true → sameMsgKeys = true → deriveMessageKeys = s.deriveMessageKeys) ∧
          s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain := fun s hs =>
        ⟨fun hId hSm => hMkEq s hs (Bool.and_true useIdealBranch ▸ hId) hSm,
          (hInv s (List.mem_of_find?_eq_some hs)).1⟩
      have hPtEq := authRecvPtAtStage_g3_8_eq_g5_of_forgedAll_false P hWF
        useIdealBranch sameMsgKeys isUncorruptedHonestSender matchedSess? deriveMessageKeys ad msg.aeadCt
        hSessValid hNoForge
      refine RelProbUpToBad.of_pure ⟨?_, rfl, rfl, hNoForge⟩
      dsimp only; rw [hPtEq]

theorem relProbUpToBad_pqxdhAuthForgeAll_step
    (S : Setup) (P : Primitives) (hWF : WellFormedPrimitivesδ P) (q : AuthQuery S)
    (s5 s6 : AuthHybridStateFixed S × Bool)
    (hAgree : s5 = s6 ∧ s6.2 = false ∧ IdealSessionsAeadValid P s5.1) :
    RelProbUpToBad
      (fun y5 y6 => y5.1 = y6.1 ∧ y5.2 = y6.2 ∧ y6.2.2 = false ∧ IdealSessionsAeadValid P y5.2.1)
      (fun y6 => y6.2.2)
      ((pqxdhAuthForgeAllImpl false .g3_8 S P q).run s5)
      ((pqxdhAuthForgeAllImpl true .g5 S P q).run s6) := by
  rcases hAgree with ⟨rfl, hForged, hInv⟩; rcases s5 with ⟨hst, forged⟩
  dsimp only at hForged hInv; subst hForged
  cases q with
  | recvOPK k j o msg =>
    dsimp only [pqxdhAuthForgeAllImpl, StateT.run_mk]
    cases hprep : prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState with
    | none => exact RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, hInv⟩
    | some prep =>
      simp only [map_eq_bind_pure_comp, Function.comp_def]
      have hId :=
          prepareAuthHybridRecvOPK_idealSessions true P k j o msg hst.toAuthHybridState hprep
      have hDecInv : ∀ s ∈ prep.hstDec.idealSessions,
          s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧
              initSessionSlotIdx s.sid < S.N_send_tot := by
        rw [hId.1]; exact hInv
      refine RelProbUpToBad.bind_rel
        (relProbUpToBad_evalAuthRecvScheduleForgeAll P hWF prep.hstDec hDecInv
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun b6 hb6 y6 hy6 => by
          simp only [support_pure, Set.mem_singleton_iff] at hy6; subst hy6; simp [hb6])
        (fun b5 b6 ⟨hEq1, hEq2, hEq3, hEq4⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, forged6⟩
      dsimp only at hEq1 hEq2 hEq3 hEq4; cases hEq1; subst hEq2 hEq3 hEq4
      refine RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, ?_⟩
      unfold IdealSessionsAeadValid; dsimp only; rw [hId.2 res5?]; exact hInv
  | recvNoOPK k j l msg =>
    dsimp only [pqxdhAuthForgeAllImpl, StateT.run_mk]
    cases hprep : prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState with
    | none => exact RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, hInv⟩
    | some prep =>
      simp only [map_eq_bind_pure_comp, Function.comp_def]
      have hId :=
          prepareAuthHybridRecvNoOPK_idealSessions true P k j l msg hst.toAuthHybridState hprep
      have hDecInv : ∀ s ∈ prep.hstDec.idealSessions,
          s.aeadCt = P.aeadEnc s.deriveMessageKeys s.ad s.msgPlain ∧
              initSessionSlotIdx s.sid < S.N_send_tot := by
        rw [hId.1]; exact hInv
      refine RelProbUpToBad.bind_rel
        (relProbUpToBad_evalAuthRecvScheduleForgeAll P hWF prep.hstDec hDecInv
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun b6 hb6 y6 hy6 => by
          simp only [support_pure, Set.mem_singleton_iff] at hy6; subst hy6; simp [hb6])
        (fun b5 b6 ⟨hEq1, hEq2, hEq3, hEq4⟩ => ?_)
      rcases b5 with ⟨⟨res5?, mkSaltCache5'⟩, forged5⟩
      rcases b6 with ⟨⟨res6?, mkSaltCache6'⟩, forged6⟩
      dsimp only at hEq1 hEq2 hEq3 hEq4; cases hEq1; subst hEq2 hEq3 hEq4
      refine RelProbUpToBad.of_pure ⟨rfl, rfl, rfl, ?_⟩
      unfold IdealSessionsAeadValid; dsimp only; rw [hId.2 res5?]; exact hInv
  | _ =>
    dsimp only [pqxdhAuthForgeAllImpl, StateT.run_mk]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
    refine RelProbUpToBad.bind_same_of_support _ (fun ⟨resp, hst'⟩ hp => ?_)
    exact RelProbUpToBad.of_pure
      ⟨rfl, rfl, rfl,
          idealSessionsAeadValid_nonRecvSplitFixed .g3_8 .g3_8 rfl true true P _ hst hInv hp⟩

/-- Up-to-bad bound between `G3.8` and `split(.g3_8, .g5, true)` via `authIntForgeAllExp`. -/
theorem auth_hop_G3_8_split_g5_le_forgeAll (S : Setup) (P : Primitives)
    (hWF : WellFormedPrimitivesδ P) (A : AuthAdversary S) :
    |(𝒟[authFixedExpG3_8 S P A] {true}).toReal -
     (𝒟[authSplitFixedExp .g3_8 .g5 true S P A] {true}).toReal| ≤
      (𝒟[authIntForgeAllExp S P A] {true}).toReal := by
  let impl5 :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
          ProbComp) +
    pqxdhAuthForgeAllImpl false .g3_8 S P
  let impl6 :=
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S × Bool)
          ProbComp) +
    pqxdhAuthForgeAllImpl true .g5 S P
  let fin (secb : Bool) (p : Bool × (AuthHybridStateFixed S × Bool)) : ProbComp Bool :=
    let (b', finalSt, _) := p
    let allChallengedClean := finalSt.toAuthHybridState.base.sessions.all (fun s =>
      !s.challenged || authInitCorruptionClause P true finalSt.toAuthHybridState.base.principals s)
    if hasEcPkCollisionAuth P finalSt.toAuthHybridState || hasBadSigAuth finalSt.toAuthHybridState
        ||
       hasKemPkCollisionAuth finalSt.toAuthHybridState || hasBadKemShCrAuth P
           finalSt.toAuthHybridState then
      $ᵗ Bool
    else if true && finalSt.toAuthHybridState.base.hasWonAuth then pure true
    else if !allChallengedClean then $ᵗ Bool
    else pure (b' == secb)
  have hG38 : authFixedExpG3_8 S P A =
      ($ᵗ Bool >>= fun secb =>
        (simulateQ impl5 A.run).run (AuthHybridStateFixed.empty S secb, false) >>= fin secb) := by
    unfold authFixedExpG3_8
    rw [← authSplitFixedExp_same_true .g3_8 S P A]
    unfold authSplitFixedExp; congr 1; funext secb
    exact (simulateQ_pqxdhAuthForgeAllImpl_fst false .g3_8 (Or.inl rfl) S P A.run
      (AuthHybridStateFixed.empty S secb) false (fun q => fin secb (q.1, q.2, false))).symm
  have hG5 : authSplitFixedExp .g3_8 .g5 true S P A =
      ($ᵗ Bool >>= fun secb =>
        (simulateQ impl6 A.run).run (AuthHybridStateFixed.empty S secb, false) >>= fin secb) := by
    unfold authSplitFixedExp; congr 1; funext secb
    exact (simulateQ_pqxdhAuthForgeAllImpl_fst true .g5 (Or.inr rfl) S P A.run
      (AuthHybridStateFixed.empty S secb) false (fun q => fin secb (q.1, q.2, false))).symm
  rw [hG38, hG5]
  refine evalDist_outer_bind_abs_sub_le' ($ᵗ Bool)
    (fun secb => (simulateQ impl5 A.run).run (AuthHybridStateFixed.empty S secb, false))
    (fun secb => (simulateQ impl6 A.run).run (AuthHybridStateFixed.empty S secb, false))
    (fun _secb p => p.2.2) fin fin (fun secb => ?_)
  have hSim := simulateQ_relProbUpToBad
    (pqxdhAuthForgeAllImpl false .g3_8 S P)
    (pqxdhAuthForgeAllImpl true .g5 S P)
    (fun s5 s6 => s5 = s6 ∧ s6.2 = false ∧ IdealSessionsAeadValid P s5.1)
    (fun s6 => s6.2)
    (pqxdhAuthForgeAllImpl_bad_mono true .g5 S P)
    (relProbUpToBad_pqxdhAuthForgeAll_step S P hWF)
    A.run (AuthHybridStateFixed.empty S secb, false) (AuthHybridStateFixed.empty S secb, false)
    ⟨rfl, rfl, idealSessionsAeadValid_empty S P secb⟩
  exact RelProbUpToBad.evalDist_bind_le hSim (fun _ _ ⟨_, _, hFalse, _⟩ => hFalse) (fin secb)
      (fin secb)
    (fun x5 x6 ⟨h1, h2, _, _⟩ => by
      rcases x5 with ⟨b5, s5, f5⟩; rcases x6 with ⟨b6, s6, f6⟩
      dsimp only at h1 h2; cases h1; cases h2; rfl)

end SignalPqxdh.Security
