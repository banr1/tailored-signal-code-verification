/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh

/-! ## Cutoff boundary lemmas for `authCkCutoffExp` -/

@[simp] theorem find?_matchIdealAuthHandshake_eraseIdealCk1_0 {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (l : List (IdealAuthSession S)) :
    (l.map eraseIdealCk1_0).find? (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr) =
      (l.find? (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr)).map
        eraseIdealCk1_0 := by
  induction l with
  | nil => rfl
  | cons s tl ih =>
    simp only [List.map_cons, List.find?_cons, matchIdealAuthHandshake_eraseIdealCk1_0]
    cases matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s
    · exact ih
    · rfl

@[simp] theorem match_sameEph_map_eraseIdealCk1_0 {S : Setup} (P : Primitives)
    (ms? : Option (IdealAuthSession S)) (ephAPk : Bytes) :
    (match ms?.map eraseIdealCk1_0 with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) =
    (match ms? with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) := by
  cases ms? <;> rfl

@[simp] theorem eraseAuthCk1_0_idealSessions {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0 hst).idealSessions = hst.idealSessions.map eraseIdealCk1_0 := rfl

theorem prepareAuthHybridRecvOPK_eraseAuthCk1_0 {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvOPK checkAuth P k j o msg (eraseAuthCk1_0 hst) =
      (prepareAuthHybridRecvOPK checkAuth P k j o msg hst).map (fun prep =>
        { prep with
          hstDec := eraseAuthCk1_0 prep.hstDec
          matchedSess? := prep.matchedSess?.map eraseIdealCk1_0
          finish := fun res? =>
            let (resp, hst') := prep.finish res?
            (resp, eraseAuthCk1_0 hst') }) := by
  unfold prepareAuthHybridRecvOPK
  dsimp only [eraseAuthCk1_0_base]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split; · rfl
    split
    · rfl
    · simp only [Option.map_some, eraseAuthCk1_0_initKemRecs, eraseAuthCk1_0_recvKemRecs,
        eraseAuthCk1_0_idealSessions, find?_matchIdealAuthHandshake_eraseIdealCk1_0]
      congr 2
      · exact match_sameEph_map_eraseIdealCk1_0 P _ _
      · funext res?
        apply Eq.symm
        exact finishAuthHybridRecvOPK_eraseAuthCk1_0 checkAuth P k j o _ _ _ _ msg _ res?
  · rfl

theorem prepareAuthHybridRecvNoOPK_eraseAuthCk1_0 {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvNoOPK checkAuth P k j l msg (eraseAuthCk1_0 hst) =
      (prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst).map (fun prep =>
        { prep with
          hstDec := eraseAuthCk1_0 prep.hstDec
          matchedSess? := prep.matchedSess?.map eraseIdealCk1_0
          finish := fun res? =>
            let (resp, hst') := prep.finish res?
            (resp, eraseAuthCk1_0 hst') }) := by
  unfold prepareAuthHybridRecvNoOPK
  dsimp only [eraseAuthCk1_0_base]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split
    · rfl
    · simp only [Option.map_some, eraseAuthCk1_0_initKemRecs, eraseAuthCk1_0_recvKemRecs,
        eraseAuthCk1_0_idealSessions, find?_matchIdealAuthHandshake_eraseIdealCk1_0]
      congr 2
      · exact match_sameEph_map_eraseIdealCk1_0 P _ _
      · funext res?
        apply Eq.symm
        exact finishAuthHybridRecvNoOPK_eraseAuthCk1_0 checkAuth P k j l _ _ _ msg _ res?
  · rfl


theorem pqxdhAuthHybridKoskImpl_recvOPK_eq {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridKoskImpl stage useRo checkAuth S P (.recvOPK k j o msg)).run hst =
      (match prepareAuthHybridRecvOPK checkAuth P k j o msg hst with
       | none => pure (.noneResp, hst)
       | some prep => do
         let res? ← evalAuthHybridRecvSchedule stage useRo P prep.hstDec
           prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         pure (prep.finish res?)) := by
  unfold pqxdhAuthHybridKoskImpl prepareAuthHybridRecvOPK
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · rename_i kEntry heq1
    split
    · rename_i bEntry heq2
      split
      · rename_i oEntry heq3
        simp only [heq1, heq2, heq3]
        split; · rfl
        split; · rfl
        rcases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with _ | ss
        · rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind]
          congr 1; funext res?
          cases res? with
          | none => rfl
          | some r =>
            rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
            unfold finishAuthHybridRecvOPK
            dsimp only
            cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
            | none => rfl
            | some p =>
              rcases p with ⟨_, senderEntry⟩
              dsimp only
              cases senderEntry.corrupted <;> rfl
      · rename_i hno3
        split
        · rfl
        · rename_i heq
          split at heq
          · rename_i heq3'
            exact False.elim (hno3 _ _ heq3')
          · cases heq
    · rename_i hno2
      split
      · rfl
      · rename_i heq
        split at heq
        · rename_i heq2' _
          exact False.elim (hno2 _ _ heq2')
        · cases heq
  · rename_i hno1
    split
    · rfl
    · rename_i heq
      split at heq
      · rename_i heq1' _ _
        exact False.elim (hno1 _ _ heq1')
      · cases heq

theorem pqxdhAuthHybridKoskImpl_recvNoOPK_eq {S : Setup} (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) :
    (pqxdhAuthHybridKoskImpl stage useRo checkAuth S P (.recvNoOPK k j l msg)).run hst =
      (match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst with
       | none => pure (.noneResp, hst)
       | some prep => do
         let res? ← evalAuthHybridRecvSchedule stage useRo P prep.hstDec
           prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         pure (prep.finish res?)) := by
  unfold pqxdhAuthHybridKoskImpl prepareAuthHybridRecvNoOPK
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · rename_i kEntry heq1
    split
    · rename_i bEntry heq2
      simp only [heq1, heq2]
      split; · rfl
      rcases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with _ | ss
      · rfl
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift, monadLift_self,
          bind_assoc, pure_bind]
        congr 1; funext res?
        cases res? with
        | none => rfl
        | some r =>
          rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
          unfold finishAuthHybridRecvNoOPK
          dsimp only
          cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
          | none => rfl
          | some p =>
            rcases p with ⟨_, senderEntry⟩
            dsimp only
            cases senderEntry.corrupted <;> rfl
    · rename_i hno2
      split
      · rfl
      · rename_i heq
        split at heq
        · rename_i heq2'
          exact False.elim (hno2 _ _ heq2')
        · cases heq
  · rename_i hno1
    split
    · rfl
    · rename_i heq
      split at heq
      · rename_i heq1' _
        exact False.elim (hno1 _ _ heq1')
      · cases heq

theorem AuthSubHops1to3.runAuthHybridSendKosk_eq {S : Setup} (stage : AuthHybridStage)
    (useRo : Bool) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) :
    (runAuthHybridSendKosk stage useRo S P sid u bundle m0 m1).run hst = (do
      let st := hst.base
      if m0.length != m1.length then pure (.noneResp, hst)
      else if st.usedSendSessions.contains sid then pure (.noneResp, hst)
      else
        match st.principals.find? (fun (idx, _) => idx == u.val) with
        | none => pure (.noneResp, hst)
        | some (_, uEntry) =>
          let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
          let isFreshPeer : Bool :=
            match peerPrincipal? with
            | some (_, pEntry) => !pEntry.corrupted
            | none             => false
          if !isFreshPeer && m0 != m1 then pure (.noneResp, hst)
          else
            let msgPlain :=
              if isFreshPeer then
                if stage.idealFreshAead then m0 else (if st.secb then m1 else m0)
              else
                m0
            if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
              pure (.noneResp, hst)
            else do
              let ekASk ← sampleScalar32
              let kemCoins ← sampleCoins32
              let ephASk ← sampleScalar32
              let spqrCoins ← sampleCoins32
              let sigPkB := resolveSigPk P st.principals bundle.ikB
              if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
                   P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
                pure (.noneResp, hst)
              else
                match P.kemEncaps bundle.pqspkB kemCoins with
                | none => pure (.noneResp, hst)
                | some (ss, kemCt) => do
                  let ekAPk := P.x25519Base ekASk
                  let prov :=
                    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
                  let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
                  let isIdealSend : Bool :=
                    isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
                  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                  let dh2 := P.x25519 ekASk bundle.ikB
                  let dh3 := P.x25519 ekASk bundle.spkB
                  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                  let (drKey, roCache') ←
                    if isIdealSend && stage.idealDrKey then do
                      let dk ← sampleDRKey96
                      pure (dk, st.roCache)
                    else
                      evalHkdfOrRo useRo P st.roCache secrets
                  let ephAPk := P.x25519Base ephASk
                  let dhRatchet := P.x25519 ephASk bundle.spkB
                  let ((rk1, ck1_0), rootRoCache') ←
                    if isIdealSend && stage.idealRk then do
                      let r ← sampleBytes32
                      let c ← sampleBytes32
                      pure ((r, c), st.rootRoCache)
                    else
                      evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet
                  let (mkSeed, ck1_1) ←
                    if isIdealSend && stage.idealCk then do
                      let ms ← sampleBytes32
                      let cn ← sampleBytes32
                      pure (ms, cn)
                    else
                      pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
                  match P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => pure (.noneResp, hst)
                  | some (_pqrStA, spqrSalt?, pqRatchetMsg) => do
                    let deriveMessageKeys ←
                      if isIdealSend && stage.idealMsgKeys then
                        sampleMessageKeys80
                      else
                        pure (P.deriveMsgKeys mkSeed spqrSalt?)
                    let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                    let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                    pure (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain
                      roCache' rootRoCache' hst)) := by
  unfold runAuthHybridSendKosk
  rw [StateT.run_bind, StateT.run_get, pure_bind]
  dsimp only
  cases (m0.length != m1.length) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  cases (hst.base.usedSendSessions.contains sid) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
  rcases h3 : hst.base.principals.find? (fun x => x.1 == u.val) with _ | ⟨_, uEntry⟩ <;> rw [h3]
  · rfl
  · dsimp only
    cases (!(match findHonestPrincipal P hst.base.principals bundle.ikB with
             | some (_, pEntry) => !pEntry.corrupted
             | none => false) && (m0 != m1)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    cases (!koskBundleOk P hst.base.principals hst.base.spkBundles
      hst.base.opkEntries hst.base.advKeys bundle) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    congr 1; funext ekASk
    congr 1; funext kemCoins
    congr 1; funext ephASk
    congr 1; funext spqrCoins
    cases (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
               (encodeEC bundle.spkB) bundle.spkSig &&
             P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
               (encodeKEM bundle.pqspkB) bundle.pqspkSig)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure]
    rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
    · rfl
    · unfold finishAuthHybridSend
      dsimp only
      cases ((match findHonestPrincipal P hst.base.principals bundle.ikB with
              | some (_, pEntry) => !pEntry.corrupted
              | none => false) ||
             ((findHonestPrincipal P hst.base.principals bundle.ikB).isSome &&
              checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles bundle &&
              (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles
                hst.base.opkEntries bundle).2.2)) <;>
      cases stage <;>
      { simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
          AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
          AuthHybridStage.idealFreshAead, Bool.and_false, Bool.and_true,
          Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind]
        repeat (first
          | (rcases P.spqrInitSend _ spqrCoins with _ | ⟨_, _, _⟩; · rfl;
             · simp only [StateT.run_bind, StateT.run_monadLift,
                 StateT.run_set, monadLift_self, bind_assoc, pure_bind];
               try (congr 1; funext _);
               cases (findHonestPrincipal P hst.base.principals bundle.ikB).isSome <;> rfl)
          | (congr 1; funext _)) }

open AuthSubHops1to3

private theorem option_eq_none_or_eq_some {α : Type} (o : Option α) :
    o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp

private theorem forall_support_bind {α β : Type} (m : ProbComp α)
    (f : α → ProbComp β) (P : β → Prop)
    (h : ∀ a, ∀ b ∈ support (f a), P b) :
    ∀ b ∈ support (m >>= f), P b := by
  intro b hb
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hb
  rcases hb with ⟨a, _, hb⟩
  exact h a b hb

private theorem forall_support_pure {α : Type} (x : α) (P : α → Prop) (h : P x) :
    ∀ b ∈ support (pure x : ProbComp α), P b := by
  intro b hb
  rw [support_pure, Set.mem_singleton_iff] at hb
  exact hb ▸ h

def InvCkG3_6 {S : Setup} (P : Primitives) (hst : AuthHybridState S) : Prop :=
  ∀ s ∈ hst.idealSessions, s.mkSeed = P.chainKdfSeed s.ck1_0 ∧ s.ck1_1 = P.chainKdfNext s.ck1_0

theorem invCkG3_6_empty (S : Setup) (P : Primitives) (secb : Bool) :
    InvCkG3_6 P (AuthHybridState.empty S secb) := by
  intro s hs
  cases hs

theorem invCkG3_6_finishAuthHybridSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S) (hInv : InvCkG3_6 P hst) :
    InvCkG3_6 P (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0
      (P.chainKdfSeed ck1_0) (P.chainKdfNext ck1_0)
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst).2 := by
  unfold finishAuthHybridSend InvCkG3_6
  dsimp only
  split
  · intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨rfl, rfl⟩
    · exact hInv s hs
  · exact hInv

theorem invCkG3_6_runAuthHybridSendKosk {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) (hInv : InvCkG3_6 P hst) :
    ∀ x ∈ support ((runAuthHybridSendKosk .g3_6 true S P sid u bundle m0 m1).run hst),
      InvCkG3_6 P x.2 := by
  rw [runAuthHybridSendKosk_eq]
  simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
    AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true (m0.length != m1.length) with h1 | h1 <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
  · rcases bool_eq_false_or_eq_true (hst.base.usedSendSessions.contains sid) with h2 | h2 <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
    · rcases option_eq_none_or_eq_some (hst.base.principals.find? (fun x => x.1 == u.val))
        with h3 | ⟨⟨_, uEntry⟩, h3⟩ <;>
        rw [h3]
      · exact forall_support_pure _ _ hInv
      · dsimp only
        rcases bool_eq_false_or_eq_true
          (!(match findHonestPrincipal P hst.base.principals bundle.ikB with
             | some (_, pEntry) => !pEntry.corrupted
             | none => false) && (m0 != m1)) with hm | hm <;>
          simp only [hm, Bool.false_eq_true, ↓reduceIte]
        · rcases bool_eq_false_or_eq_true (!koskBundleOk P hst.base.principals
            hst.base.spkBundles hst.base.opkEntries hst.base.advKeys bundle) with hk | hk <;>
            simp only [hk, Bool.false_eq_true, ↓reduceIte]
          · refine forall_support_bind _ _ _ (fun ekASk => ?_)
            refine forall_support_bind _ _ _ (fun kemCoins => ?_)
            refine forall_support_bind _ _ _ (fun ephASk => ?_)
            refine forall_support_bind _ _ _ (fun spqrCoins => ?_)
            rcases bool_eq_false_or_eq_true (!(P.sigVerify
              (resolveSigPk P hst.base.principals bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig &&
              P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) with hsig | hsig <;>
              simp only [hsig, Bool.false_eq_true, ↓reduceIte]
            · rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
              · exact forall_support_pure _ _ hInv
              · dsimp only
                rcases bool_eq_false_or_eq_true
                  ((match findHonestPrincipal P hst.base.principals bundle.ikB with
                    | some (_, pEntry) => !pEntry.corrupted
                    | none => false) ||
                   ((findHonestPrincipal P hst.base.principals bundle.ikB).isSome &&
                    checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles bundle &&
                    (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles
                      hst.base.opkEntries bundle).2.2)) with hIdeal | hIdeal <;>
                  simp only [hIdeal, Bool.false_eq_true, ↓reduceIte]
                · refine forall_support_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
                  refine forall_support_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
                  rcases P.spqrInitSend drKey.pqrKey spqrCoins
                    with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                  · exact forall_support_pure _ _ hInv
                  · exact forall_support_pure _ _
                      (invCkG3_6_finishAuthHybridSend P sid uEntry _ _ bundle m0 m1
                      ekASk _ ss kemCt ephASk _ drKey rk1 ck1_0 spqrSalt? pqRatchetMsg
                      _ _ _ _ roCache' rootRoCache' hst hInv)
                · refine forall_support_bind _ _ _ (fun drKey => ?_)
                  refine forall_support_bind _ _ _ (fun rk1 => ?_)
                  refine forall_support_bind _ _ _ (fun ck1_0 => ?_)
                  rcases P.spqrInitSend drKey.pqrKey spqrCoins
                    with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                  · exact forall_support_pure _ _ hInv
                  · exact forall_support_pure _ _
                      (invCkG3_6_finishAuthHybridSend P sid uEntry _ _ bundle m0 m1
                      ekASk _ ss kemCt ephASk _ drKey rk1 ck1_0 spqrSalt? pqRatchetMsg
                      _ _ _ _ _ _ hst hInv)
            · exact forall_support_pure _ _ hInv
          · exact forall_support_pure _ _ hInv
        · exact forall_support_pure _ _ hInv
    · exact forall_support_pure _ _ hInv
  · exact forall_support_pure _ _ hInv

def erasePreparedAuthRecv {S : Setup} (prep : PreparedAuthRecv S) : PreparedAuthRecv S :=
  { prep with
    hstDec := eraseAuthCk1_0 prep.hstDec
    matchedSess? := prep.matchedSess?.map eraseIdealCk1_0
    finish := fun res? =>
      let (resp, hst') := prep.finish res?
      (resp, eraseAuthCk1_0 hst') }

structure PreparedAuthRecvWf {S : Setup} (P : Primitives) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (prep : PreparedAuthRecv S) : Prop where
  idealSessions_eq : prep.hstDec.idealSessions = hst.idealSessions
  finish_idealSessions_eq : ∀ res?, (prep.finish res?).2.idealSessions = hst.idealSessions
  isUncorrupted_eq :
    (match findHonestPrincipal P prep.hstDec.base.principals msg.hdr.ikAPk with
     | some (_, sEntry) => !sEntry.corrupted
     | none => false) = prep.isUncorruptedHonestSender
  matchedSess_eq :
    prep.hstDec.idealSessions.find?
      (matchIdealAuthHandshake P prep.kEntry.ikAPk prep.bEntry.spkPk prep.opkPk?
        prep.bEntry.pqspkPk msg.hdr) =
      prep.matchedSess?
  sameEph_eq :
    (match prep.matchedSess? with
     | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk
     | none => false) = prep.sameEph
  dhRatchet_eq :
    P.x25519 prep.bEntry.spkSk msg.ephAPk = prep.dhRatchet

private theorem finishAuthHybridRecvOPK_idealSessions {S : Setup} (checkAuth : Bool)
    (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples'
      msg hstDec res?).2.idealSessions =
      hstDec.idealSessions := by
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl

private theorem finishAuthHybridRecvNoOPK_idealSessions {S : Setup} (checkAuth : Bool)
    (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples'
      msg hstDec res?).2.idealSessions =
      hstDec.idealSessions := by
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl

theorem prepareAuthHybridRecvOPK_wf {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    ∀ prep, prepareAuthHybridRecvOPK checkAuth P k j o msg hst = some prep →
      PreparedAuthRecvWf P msg hst prep := by
  unfold prepareAuthHybridRecvOPK
  dsimp only
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split
  · split; · intro _ h; cases h
    split; · intro _ h; cases h
    split
    · intro _ h; cases h
    · intro prep h; injection h with h; subst h
      exact ⟨rfl, fun res? => finishAuthHybridRecvOPK_idealSessions _ _ _ _ _ _ _ _ _ _ _ res?,
        rfl, rfl, rfl, rfl⟩
  · intro _ h; cases h

theorem prepareAuthHybridRecvNoOPK_wf {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    ∀ prep, prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst = some prep →
      PreparedAuthRecvWf P msg hst prep := by
  unfold prepareAuthHybridRecvNoOPK
  dsimp only
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split; · intro _ h; cases h
  split
  · split; · intro _ h; cases h
    split
    · intro _ h; cases h
    · intro prep h; injection h with h; subst h
      exact ⟨rfl, fun res? => finishAuthHybridRecvNoOPK_idealSessions _ _ _ _ _ _ _ _ _ _ res?,
        rfl, rfl, rfl, rfl⟩
  · intro _ h; cases h

theorem evalDist_send_eq_authCkSendWith {S : Setup} (stage : AuthHybridStage) (cutoff : Nat)
    (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hDr : stage.idealDrKey = true)
    (hRk : stage.idealRk = true)
    (hMk : stage.idealMsgKeys = false)
    (hAead : stage.idealFreshAead = false)
    (hCut : decide (_root_.SignalPqxdh.Security.RoKem.sessionSlotIndex sid < cutoff) =
      stage.idealCk)
    (hWon : hst.toAuthHybridState.base.hasWonAuth = false)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[((runAuthHybridSendKosk stage true S P sid u bundle m0 m1).run hst.toAuthHybridState) >>=
        fun x => k (x.1, { toAuthHybridState := eraseAuthCk1_0 x.2, recvCount := hst.recvCount })] =
      𝒟[authCkSendWith S P (fun s => sampCkPair P (s < cutoff)) sid u bundle m0 m1
          (eraseAuthFixedCk1_0 hst) >>= k] := by
  rw [runAuthHybridSendKosk_eq]
  unfold authCkSendWith
  dsimp only [eraseAuthFixedCk1_0, eraseAuthCk1_0_base]
  simp only [hWon, hDr, hRk, hMk, hAead,
    Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true (m0.length != m1.length) with h1 | h1 <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true (hst.toAuthHybridState.base.usedSendSessions.contains sid)
    with h2 | h2 <;>
    simp only [h2, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases option_eq_none_or_eq_some
    (hst.toAuthHybridState.base.principals.find? (fun x => x.1 == u.val))
    with h3 | ⟨⟨_, uEntry⟩, h3⟩ <;>
    rw [h3]
  · simp only [pure_bind]
  · dsimp only
    rcases option_eq_none_or_eq_some
      (findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB)
      with hpeer | ⟨⟨pIdx, pEntry⟩, hpeer⟩ <;>
      rw [hpeer] <;> dsimp only
    · rcases bool_eq_false_or_eq_true (m0 != m1) with hm | hm <;>
        simp only [hm, Bool.not_false, Bool.and_false, Bool.and_true,
          Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases bool_eq_false_or_eq_true (!koskBundleOk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles
          hst.toAuthHybridState.base.opkEntries hst.toAuthHybridState.base.advKeys bundle)
        with hk | hk <;>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      rcases bool_eq_false_or_eq_true (!(P.sigVerify
          (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
          (encodeEC bundle.spkB) bundle.spkSig &&
        P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
          (encodeKEM bundle.pqspkB) bundle.pqspkSig)) with hsig | hsig <;>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
      · simp only [pure_bind]
      · dsimp only
        simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
          bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
        refine OracleComp.evalDist_bind_congr_of_support _ _ _
          (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
        rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
        · simp only [pure_bind]
        · simp only [pure_bind]; rfl
    · rcases bool_eq_false_or_eq_true (! !pEntry.corrupted && (m0 != m1)) with hm | hm <;>
        simp only [hm, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases bool_eq_false_or_eq_true (!koskBundleOk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles
          hst.toAuthHybridState.base.opkEntries hst.toAuthHybridState.base.advKeys bundle)
        with hk | hk <;>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      rcases bool_eq_false_or_eq_true (!(P.sigVerify
          (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
          (encodeEC bundle.spkB) bundle.spkSig &&
        P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
          (encodeKEM bundle.pqspkB) bundle.pqspkSig)) with hsig | hsig <;>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
      · simp only [pure_bind]
      · dsimp only
        rcases bool_eq_false_or_eq_true
          (!pEntry.corrupted ||
           ((some (pIdx, pEntry)).isSome &&
            checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles
              bundle &&
            (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles
              hst.toAuthHybridState.base.opkEntries bundle).2.2))
          with hIdeal | hIdeal <;>
          simp only [hIdeal, Bool.true_and, Bool.false_and,
            Bool.false_eq_true, ↓reduceIte, bind_assoc]
        · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _
            (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
          rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
          · simp only [pure_bind]
          · unfold finishAuthHybridSend eraseAuthCk1_0 eraseIdealCk1_0
            dsimp only
            simp only [hIdeal, Bool.false_eq_true, ↓reduceIte, pure_bind]
        · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun drKey _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rk1 _ => ?_)
          change _ = 𝒟[(match P.spqrInitSend drKey.pqrKey spqrCoins with
            | none => pure (.noneResp,
                { toAuthHybridState := eraseAuthCk1_0 hst.toAuthHybridState,
                  recvCount := hst.recvCount })
            | some (_pqrStA, spqrSalt?, pqRatchetMsg) => do
              let p ← sampCkPair P
                (decide (_root_.SignalPqxdh.Security.RoKem.sessionSlotIndex sid < cutoff))
              pure (finishAuthSendCk P sid uEntry (some (pIdx, pEntry)) bundle m0 m1
                ekASk (P.x25519Base ekASk) ss kemCt ephASk (P.x25519Base ephASk) drKey rk1
                spqrSalt? pqRatchetMsg
                (if !pEntry.corrupted then
                  (if hst.toAuthHybridState.base.secb then m1 else m0) else m0)
                { toAuthHybridState := eraseAuthCk1_0 hst.toAuthHybridState,
                  recvCount := hst.recvCount } p)) >>= k]
          rw [hCut]
          cases stage.idealCk <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
          · rcases P.spqrInitSend drKey.pqrKey spqrCoins
              with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩ <;> dsimp only
            · simp only [pure_bind, evalDist_sampleBytes32_bind_const]
            · simp only [bind_assoc, pure_bind]
              rw [← sampCkPair_bind_eq P false]
              unfold finishAuthSendCk finishAuthHybridSend eraseAuthCk1_0 eraseIdealCk1_0
              dsimp only
              simp only [hIdeal, Bool.false_eq_true, ↓reduceIte, pure_bind]; rfl
          · rcases P.spqrInitSend drKey.pqrKey spqrCoins
              with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩ <;> dsimp only
            · simp only [pure_bind, evalDist_sampleBytes32_bind_const]
            · simp only [bind_assoc, pure_bind]
              rw [← sampCkPair_bind_eq P true]
              unfold finishAuthSendCk finishAuthHybridSend eraseAuthCk1_0 eraseIdealCk1_0
              dsimp only
              simp only [hIdeal, ↓reduceIte, bind_assoc, pure_bind]; rfl

theorem evalAuthHybridRecvSchedule_g3_6_of_wf {S : Setup} (useRo : Bool)
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridState S) (prep : PreparedAuthRecv S)
    (hWf : PreparedAuthRecvWf P msg hst prep) :
    evalAuthHybridRecvSchedule .g3_6 useRo P prep.hstDec
      prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg = (do
      let st := prep.hstDec.base
      let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
      if prep.matchedSess?.isSome || prep.isUncorruptedHonestSender then
        match prep.matchedSess? with
        | some s =>
          if prep.sameEph then
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => pure none
            | some (_pqrStB, spqrSalt?) =>
              let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed s.ck1_0) spqrSalt?
              pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
                (s.drKey, s.rk1, P.chainKdfNext s.ck1_0, pt, st.roCache, st.rootRoCache)))
          else do
            let r ← sampleBytes32
            let c ← sampleBytes32
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => pure none
            | some (_pqrStB, spqrSalt?) =>
              let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed c) spqrSalt?
              pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
                (s.drKey, r, P.chainKdfNext c, pt, st.roCache, st.rootRoCache)))
        | none => do
          let dk ← sampleDRKey96
          let r ← sampleBytes32
          let c ← sampleBytes32
          match P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
          | none => pure none
          | some (_pqrStB, spqrSalt?) =>
            let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed c) spqrSalt?
            pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
              (dk, r, P.chainKdfNext c, pt, st.roCache, st.rootRoCache)))
      else do
        let (drKey, roCache') ← evalHkdfOrRo useRo P st.roCache prep.secrets
        let ((rk1, ck1_0), rootRoCache') ←
          evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey prep.dhRatchet
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => pure none
        | some (_pqrStB, spqrSalt?) =>
          let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?
          pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
            (drKey, rk1, P.chainKdfNext ck1_0, pt, roCache', rootRoCache')))) := by
  unfold evalAuthHybridRecvSchedule
  dsimp only
  rw [hWf.matchedSess_eq, hWf.dhRatchet_eq]
  have hU := hWf.isUncorrupted_eq
  have hE := hWf.sameEph_eq
  rcases option_eq_none_or_eq_some
      (findHonestPrincipal P prep.hstDec.base.principals msg.hdr.ikAPk)
      with hs | ⟨⟨_, sEntry⟩, hs⟩ <;>
    simp only [hs] at hU <;>
    rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · simp only [hs, hms, hU.symm, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
      Option.isSome, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
    refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
    rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hms] at hE
    rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hs, hms, hU.symm, hE, hEph, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.or_false, Bool.true_and, Bool.false_and, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      simp only [hs, hms, hU.symm, hsc, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.false_or, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun dk => ?_)
      refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      rcases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
      refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hms] at hE
    rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hs, hms, hU.symm, hsc, hE, hEph, AuthHybridStage.idealDrKey,
        AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.true_or, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)

theorem evalAuthHybridRecvSchedule_g3_7_of_wf {S : Setup} (useRo : Bool)
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridState S) (prep : PreparedAuthRecv S)
    (hWf : PreparedAuthRecvWf P msg hst prep) :
    evalAuthHybridRecvSchedule .g3_7 useRo P prep.hstDec
      prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg = (do
      let st := prep.hstDec.base
      let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
      if prep.matchedSess?.isSome || prep.isUncorruptedHonestSender then
        match prep.matchedSess? with
        | some s =>
          if prep.sameEph then
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => pure none
            | some (_pqrStB, spqrSalt?) =>
              let deriveMessageKeys := P.deriveMsgKeys s.mkSeed spqrSalt?
              pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
                (s.drKey, s.rk1, s.ck1_1, pt, st.roCache, st.rootRoCache)))
          else do
            let r ← sampleBytes32
            let _c ← sampleBytes32
            let ms ← sampleBytes32
            let cn ← sampleBytes32
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => pure none
            | some (_pqrStB, spqrSalt?) =>
              let deriveMessageKeys := P.deriveMsgKeys ms spqrSalt?
              pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
                (s.drKey, r, cn, pt, st.roCache, st.rootRoCache)))
        | none => do
          let dk ← sampleDRKey96
          let r ← sampleBytes32
          let _c ← sampleBytes32
          let ms ← sampleBytes32
          let cn ← sampleBytes32
          match P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
          | none => pure none
          | some (_pqrStB, spqrSalt?) =>
            let deriveMessageKeys := P.deriveMsgKeys ms spqrSalt?
            pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
              (dk, r, cn, pt, st.roCache, st.rootRoCache)))
      else do
        let (drKey, roCache') ← evalHkdfOrRo useRo P st.roCache prep.secrets
        let ((rk1, ck1_0), rootRoCache') ←
          evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey prep.dhRatchet
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => pure none
        | some (_pqrStB, spqrSalt?) =>
          let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?
          pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
            (drKey, rk1, P.chainKdfNext ck1_0, pt, roCache', rootRoCache')))) := by
  unfold evalAuthHybridRecvSchedule
  dsimp only
  rw [hWf.matchedSess_eq, hWf.dhRatchet_eq]
  have hU := hWf.isUncorrupted_eq
  have hE := hWf.sameEph_eq
  rcases option_eq_none_or_eq_some
      (findHonestPrincipal P prep.hstDec.base.principals msg.hdr.ikAPk)
      with hs | ⟨⟨_, sEntry⟩, hs⟩ <;>
    simp only [hs] at hU <;>
    rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · simp only [hs, hms, hU.symm, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
      Option.isSome, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
    refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
    rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hms] at hE
    rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hs, hms, hU.symm, hE, hEph, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.or_false, Bool.true_and, Bool.false_and, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      refine bind_congr (fun ms => ?_)
      refine bind_congr (fun cn => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      simp only [hs, hms, hU.symm, hsc, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.false_or, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun dk => ?_)
      refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      refine bind_congr (fun ms => ?_)
      refine bind_congr (fun cn => ?_)
      rcases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
      refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hms] at hE
    rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hs, hms, hU.symm, hsc, hE, hEph, AuthHybridStage.idealDrKey,
        AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.true_or, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      refine bind_congr (fun ms => ?_)
      refine bind_congr (fun cn => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · refine bind_congr (fun r => ?_)
      refine bind_congr (fun c => ?_)
      refine bind_congr (fun ms => ?_)
      refine bind_congr (fun cn => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)


theorem evalDist_recv_schedule_g3_6_eq_authCkRecvWith_zero {S : Setup}
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (prep : PreparedAuthRecv S)
    (hInv : InvCkG3_6 P hst.toAuthHybridState)
    (hWf : PreparedAuthRecvWf P msg hst.toAuthHybridState prep)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[(do
        let res? ← evalAuthHybridRecvSchedule .g3_6 true P prep.hstDec
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        let (resp, hst') := prep.finish res?
        k (resp, { toAuthHybridState := eraseAuthCk1_0 hst', recvCount := hst.recvCount + 1 }))] =
      𝒟[authCkRecvWith S P (fun s => sampCkPair P (s < 0))
          msg (some (erasePreparedAuthRecv prep)) (eraseAuthFixedCk1_0 hst) >>= k] := by
  rw [evalAuthHybridRecvSchedule_g3_6_of_wf true P msg hst.toAuthHybridState prep hWf]
  have hCut0 : decide (S.N_send_tot + hst.recvCount < 0) = false := by simp
  unfold authCkRecvWith erasePreparedAuthRecv eraseAuthFixedCk1_0 finishAuthRecvCk sampCkPair
  dsimp only [eraseAuthCk1_0_base]
  simp only [hCut0, Bool.false_eq_true, ↓reduceIte]
  rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · rcases bool_eq_false_or_eq_true prep.isUncorruptedHonestSender with hU | hU
    · simp only [hms, hU, Option.isSome, Option.map, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [pure_bind]
    · simp only [hms, hU, Option.isSome, Option.map, Bool.false_or, ↓reduceIte,
        bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun dk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      rcases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [bind_assoc, pure_bind]
      exact evalDist_sampleBytes32_bind_const _
  · have hs_mem : s ∈ hst.toAuthHybridState.idealSessions :=
      hWf.idealSessions_eq ▸ List.mem_of_find?_eq_some (hWf.matchedSess_eq.trans hms)
    obtain ⟨hMk, hCk⟩ := hInv s hs_mem
    rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph
    · simp only [hms, hEph, Option.isSome, Option.map, Bool.true_or, Bool.false_eq_true, ↓reduceIte,
        eraseIdealCk1_0, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [bind_assoc, pure_bind]
      exact evalDist_sampleBytes32_bind_const _
    · simp only [hms, hEph, Option.isSome, Option.map, Bool.true_or, ↓reduceIte,
        eraseIdealCk1_0, ← hMk, ← hCk]
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [pure_bind]

theorem evalDist_recv_schedule_g3_7_eq_authCkRecvWith_end {S : Setup} (cutoff : Nat)
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (prep : PreparedAuthRecv S)
    (hWf : PreparedAuthRecvWf P msg hst.toAuthHybridState prep)
    (hCut : S.N_send_tot + hst.recvCount < cutoff)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[(do
        let res? ← evalAuthHybridRecvSchedule .g3_7 true P prep.hstDec
          prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        let (resp, hst') := prep.finish res?
        k (resp, { toAuthHybridState := eraseAuthCk1_0 hst', recvCount := hst.recvCount + 1 }))] =
      𝒟[authCkRecvWith S P (fun s => sampCkPair P (s < cutoff))
          msg (some (erasePreparedAuthRecv prep)) (eraseAuthFixedCk1_0 hst) >>= k] := by
  rw [evalAuthHybridRecvSchedule_g3_7_of_wf true P msg hst.toAuthHybridState prep hWf]
  have hCutD : decide (S.N_send_tot + hst.recvCount < cutoff) = true := decide_eq_true hCut
  unfold authCkRecvWith erasePreparedAuthRecv eraseAuthFixedCk1_0 finishAuthRecvCk sampCkPair
  dsimp only [eraseAuthCk1_0_base]
  simp only [hCutD, ↓reduceIte]
  rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · rcases bool_eq_false_or_eq_true prep.isUncorruptedHonestSender with hU | hU
    · simp only [hms, hU, Option.isSome, Option.map, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [pure_bind]
    · simp only [hms, hU, Option.isSome, Option.map, Bool.false_or, ↓reduceIte,
        bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun dk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      rcases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [bind_assoc, pure_bind]
      rw [evalDist_sampleBytes32_bind_const, evalDist_sampleBytes32_bind_const,
          evalDist_sampleBytes32_bind_const]
  · rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph
    · simp only [hms, hEph, Option.isSome, Option.map, Bool.true_or, Bool.false_eq_true, ↓reduceIte,
        eraseIdealCk1_0, bind_assoc, pure_bind]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [bind_assoc, pure_bind]
      rw [evalDist_sampleBytes32_bind_const, evalDist_sampleBytes32_bind_const,
          evalDist_sampleBytes32_bind_const]
    · simp only [hms, hEph, Option.isSome, Option.map, Bool.true_or, ↓reduceIte,
        eraseIdealCk1_0]
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [pure_bind]


def isAuthRecvQueryB {S : Setup} : (Nat ⊕ AuthQuery S) → Bool
  | .inr (.recvOPK _ _ _ _)   => true
  | .inr (.recvNoOPK _ _ _ _) => true
  | _                         => false

@[simp] theorem isAuthRecvQueryB_eq_true_iff {S : Setup} (q : Nat ⊕ AuthQuery S) :
    isAuthRecvQueryB q = true ↔ isAuthRecvQuery q := by
  rcases q with _ | q
  · simp [isAuthRecvQueryB, isAuthRecvQuery]
  · cases q <;> simp [isAuthRecvQueryB, isAuthRecvQuery]

theorem pqxdhAuthHybridFixedImpl_run_eq (stage : AuthHybridStage)
    (useRo checkAuth : Bool) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hStage : stage.idealMsgKeys = false := by rfl) :
    (pqxdhAuthHybridFixedImpl stage useRo checkAuth S P q).run hst =
      (do
        let (resp, hst') ←
          (pqxdhAuthHybridKoskImpl stage useRo checkAuth S P q).run hst.toAuthHybridState
        let recvCount' := if isAuthRecvQueryB (.inr q) then hst.recvCount + 1 else hst.recvCount
        pure
          (resp,
            { toAuthHybridState := hst', recvCount := recvCount',
              mkSaltCache := hst.mkSaltCache })) := by
  have h : (if isAuthRecvQuery (.inr q) then hst.recvCount + 1 else hst.recvCount) =
      (if isAuthRecvQueryB (.inr q) then hst.recvCount + 1 else hst.recvCount) := by
    cases q <;> simp [isAuthRecvQuery, isAuthRecvQueryB]
  simp [pqxdhAuthHybridFixedImpl, hStage, StateT.run_bind, h]

theorem liftAuthBase_other_eq_slots0 {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    (do
      let (resp, hst') ← (do
        let hst : AuthHybridState S ← get
        (if (true && hst.base.hasWonAuth) = true then pure AuthResponse.noneResp
         else liftAuthBase (pqxdhAuthImpl true true S P q))).run hst.toAuthHybridState
      pure
        (resp,
          { toAuthHybridState := hst', recvCount := hst.recvCount,
            mkSaltCache := hst.mkSaltCache })) =
    authCkOtherStep S P q { hst with slots := {} } := by
  unfold authCkOtherStep
  rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon <;>
    simp [hWon, liftAuthBase, StateT.run_bind]

theorem authCkOtherStep_eraseAuthFixedCk1_0 {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    (authCkOtherStep S P q hst >>= fun x => k (x.1, eraseAuthFixedCk1_0 x.2)) =
      (authCkOtherStep S P q (eraseAuthFixedCk1_0 hst) >>= k) := by
  unfold authCkOtherStep
  rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon <;>
    simp [hWon, eraseAuthFixedCk1_0, eraseAuthCk1_0]

theorem support_authCkOtherStep {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    {x : AuthResponse × AuthHybridStateFixed S}
    (hx : x ∈ support (authCkOtherStep S P q hst)) :
    x.2.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
    x.2.recvCount = hst.recvCount := by
  unfold authCkOtherStep at hx
  split at hx
  · simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨rfl, rfl⟩
  · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, base'⟩, _, rfl⟩
    exact ⟨rfl, rfl⟩

theorem step_g3_6_eq_authCkStepWith_zero {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hInv : InvCkG3_6 P hst.toAuthHybridState) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl .g3_6 true true S P q).run hst >>=
          fun x => k (x.1, eraseAuthFixedCk1_0 x.2)] =
        𝒟[authCkStepWith S P (fun s => sampCkPair P (s < 0)) q (eraseAuthFixedCk1_0 hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl .g3_6 true true S P q).run hst),
      InvCkG3_6 P x.2.toAuthHybridState) := by
  rw [pqxdhAuthHybridFixedImpl_run_eq .g3_6]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ?_⟩
        · exact evalDist_send_eq_authCkSendWith .g3_6 0 P (.sendOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl (by simp [AuthHybridStage.idealCk]) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
          exact invCkG3_6_runAuthHybridSendKosk P (.sendOPK u i) u bundle m0 m1
            hst.toAuthHybridState hInv (resp, hst') hmem
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        exact ⟨fun _ => rfl, fun x hx => hx ▸ hInv⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ?_⟩
        · exact evalDist_send_eq_authCkSendWith .g3_6 0 P (.sendNoOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl (by simp [AuthHybridStage.idealCk]) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
          exact invCkG3_6_runAuthHybridSendKosk P (.sendNoOPK u i) u bundle m0 m1
            hst.toAuthHybridState hInv (resp, hst') hmem
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        exact ⟨fun _ => rfl, fun x hx => hx ▸ hInv⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
  | recvOPK k' j o msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ?_⟩
      · exact evalDist_recv_schedule_g3_6_eq_authCkRecvWith_zero P msg hst prep hInv hWf k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        intro s hs
        rw [hWf.finish_idealSessions_eq res?] at hs
        exact hInv s hs
  | recvNoOPK k' j l msg =>
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvNoOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      exact ⟨fun _ => trivial, fun x hx => hx ▸ hInv⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ?_⟩
      · exact evalDist_recv_schedule_g3_6_eq_authCkRecvWith_zero P msg hst prep hInv hWf k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        intro s hs
        rw [hWf.finish_idealSessions_eq res?] at hs
        exact hInv s hs
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith,
      pqxdhAuthHybridKoskImpl]
    rw [liftAuthBase_other_eq_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_eraseAuthFixedCk1_0 P _ { hst with slots := {} } k),
      fun x hx => ?_⟩
    obtain ⟨hId, _⟩ := support_authCkOtherStep P _ { hst with slots := {} } hx
    intro s hs
    rw [hId] at hs
    exact hInv s hs

theorem step_g3_7_eq_authCkStepWith_end {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (_hInv : True)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl .g3_7 true true S P q).run hst >>=
          fun x => k (x.1, eraseAuthFixedCk1_0 x.2)] =
        𝒟[(StateT.mk
            (fun hst => authCkStepWith S P (fun s => sampCkPair P (s < S.N_sess_tot)) q hst)).run
            (eraseAuthFixedCk1_0 hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl .g3_7 true true S P q).run hst),
      True ∧ x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0)) := by
  dsimp only [StateT.run_mk]
  rw [pqxdhAuthHybridFixedImpl_run_eq .g3_7]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
        · exact evalDist_send_eq_authCkSendWith .g3_7 S.N_sess_tot P
            (.sendOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl
            (decide_eq_true (by
              have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt
                (.sendOPK u i) (h := trivial)
              unfold Setup.N_sess_tot; omega)) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, _, rfl⟩
          dsimp only
          omega
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ⟨trivial, ?_⟩⟩
        subst hx
        dsimp only
        omega
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩; subst hx; dsimp only; omega)
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith]
    unfold pqxdhAuthHybridKoskImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
        · exact evalDist_send_eq_authCkSendWith .g3_7 S.N_sess_tot P
            (.sendNoOPK u i) u bundle m0 m1 hst
            rfl rfl rfl rfl
            (decide_eq_true (by
              have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt
                (.sendNoOPK u i) (h := trivial)
              unfold Setup.N_sess_tot; omega)) hWon k
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
          rcases hx with ⟨⟨resp, hst'⟩, _, rfl⟩
          dsimp only
          omega
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
          Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ⟨trivial, ?_⟩⟩
        subst hx
        dsimp only
        omega
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authCkSendWith, eraseAuthFixedCk1_0, eraseAuthCk1_0_base,
          Bool.and_true, Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩; subst hx; dsimp only; omega)
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl
      unfold Setup.N_sess_tot
      omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvOPK_eq]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvOPK true P k' j o msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩
      subst hx
      dsimp only
      omega
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
      · exact evalDist_recv_schedule_g3_7_eq_authCkRecvWith_end S.N_sess_tot P
          msg hst prep hWf hLt k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        dsimp only
        omega
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl
      unfold Setup.N_sess_tot
      omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith]
    rw [pqxdhAuthHybridKoskImpl_recvNoOPK_eq]
    have hErase :
      (eraseAuthFixedCk1_0 hst).toAuthHybridState = eraseAuthCk1_0 hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvNoOPK_eraseAuthCk1_0]
    rcases option_eq_none_or_eq_some
        (prepareAuthHybridRecvNoOPK true P k' j l msg hst.toAuthHybridState)
        with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authCkRecvWith, eraseAuthFixedCk1_0, pure_bind,
        support_pure, Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ⟨trivial, ?_⟩⟩
      subst hx
      dsimp only
      omega
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => ?_, fun x hx => ⟨trivial, ?_⟩⟩
      · exact evalDist_recv_schedule_g3_7_eq_authCkRecvWith_end S.N_sess_tot P
          msg hst prep hWf hLt k
      · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨res?, _, rfl⟩
        dsimp only
        omega
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith,
      pqxdhAuthHybridKoskImpl]
    rw [liftAuthBase_other_eq_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m])
        (authCkOtherStep_eraseAuthFixedCk1_0 P _ { hst with slots := {} } k),
      fun x hx => ⟨trivial, ?_⟩⟩
    obtain ⟨_, hCnt⟩ := support_authCkOtherStep P _ { hst with slots := {} } hx
    exact Nat.le_trans (le_of_eq hCnt) (Nat.le_add_right _ _)

theorem evalDist_authCkCutoffExp_zero_eq_g3_6 (S : Setup) (P : Primitives)
    (A : AuthAdversary S) :
    𝒟[authCkCutoffExp S P 0 A] = 𝒟[authFixedExpAtStage .g3_6 S P A] := by
  symm
  unfold authFixedExpAtStage authCkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_proj_inv
    (eraseAuthFixedCk1_0 (S := S))
    (fun hst => InvCkG3_6 P hst.toAuthHybridState)
    (pqxdhAuthHybridFixedImpl .g3_6 true true S P)
    (fun q => StateT.mk (fun hst =>
      authCkStepWith S P (fun s => sampCkPair P (s < 0)) q hst))
    (fun q hst hInv => step_g3_6_eq_authCkStepWith_zero P q hst hInv)
    A.run
    (AuthHybridStateFixed.empty S secb)
    (invCkG3_6_empty S P secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

theorem evalDist_authCkCutoffExp_end_eq_g3_7 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authCkCutoffExp S P S.N_sess_tot A.1] = 𝒟[authFixedExpAtStage .g3_7 S P A.1] := by
  symm
  unfold authFixedExpAtStage authCkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound :
      OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (eraseAuthFixedCk1_0 (S := S))
    (fun _ => True)
    (fun hst => hst.recvCount)
    (isAuthRecvQueryB (S := S))
    (fun _ => rfl)
    S.N_recv_tot
    (pqxdhAuthHybridFixedImpl .g3_7 true true S P)
    (fun q => StateT.mk (fun hst =>
      authCkStepWith S P (fun s => sampCkPair P (s < S.N_sess_tot)) q hst))
    (fun q hst hInv hRecv => step_g3_7_eq_authCkStepWith_end P q hst hInv hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb)
    trivial
    (by simp [AuthHybridStateFixed.empty])
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)

end SignalPqxdh.Security
