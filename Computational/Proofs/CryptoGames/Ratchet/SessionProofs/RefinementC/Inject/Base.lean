/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.RecvCoins
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Coupling
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma11Aux

/-!
# Inject step: shared combinators

Shared invariant, non-stopping step, receive-panic, absorbing-win, and `CloseByStateC` combinators for `closeByStateC_inject_step`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## Monotonicity -/

theorem SimInvCX.mono_r {P : Params PQ PQC} {Inv : ℕ → PQ → Prop} {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} {lam : Pt} {qep q r r' : ℕ} {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))} {sC : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)} {ec : Party → BitVec 256}
    {winBefore : ℕ → Bool} {epExp : ℕ → BitVec 256}
    (h : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hle : r' ≤ r) :
    SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r' x₀ s_R sC s_fig8 ec winBefore epExp :=
  { h with
    hsim :=
      { h.hsim with
        hamb := by have := h.hsim.hamb; omega
        hamb_strict := fun h' => by have := h.hsim.hamb_strict h'; omega
        hidx_le := fun Q => by have := h.hsim.hidx_le Q; omega
        hhon_len := by have := h.hsim.hhon_len; omega
        hhon := h.hsim.hhon
        hpqInv := fun Q => InvB.mono hle (h.hsim.hpqInv Q) } }

/-! ## Non-stopping eager inject step -/

theorem simRecvStops_eq_false_of (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : (simRecvStep P ℓ Dh encPt encT decT idOf lam qep k Q w isDel 0 st).2.1.stopped = false) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w isDel st = false := by
  unfold simRecvStops
  rw [h, Bool.and_false]

theorem stepSimCEager_inject_of_not_stops_core (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (huse' : (simRecvUsesCoin P encT decT k Q w false x.sim && !recvPanicsW P Q w x.1.base) =
      false)
    (hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim = false)
    (hev : evictStopsC P encT decT k Q w false x = false) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec =
      (let res := simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false x
       updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
         pure (res.1, (res.2, ec'))) := by
  change stepSimCEagerInject P ℓ Dh encPt encT decT idOf lam qep k Q w x ec = _
  unfold stepSimCEagerInject
  simp only [huse', hev, Bool.false_eq_true, ↓reduceIte]
  change (if simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim then _
    else stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inr (Q, w))) x) >>= _ = _
  simp only [hstops, Bool.false_eq_true, ↓reduceIte]
  rw [stepSimCNone_inject_eq,
    simRecvStepC_eq_gen_false P ℓ Dh encPt encT decT idOf lam qep Q w false x (Or.inl rfl),
    pure_bind]

theorem stepSimCEager_inject_of_not_stops_gen (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (huse : simRecvUsesCoin P encT decT k Q w false x.sim = false)
    (hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim = false)
    (hev : evictStopsC P encT decT k Q w false x = false := by evict_stops_tac) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec =
      (let res := simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false x
       updateAllEagerCoins x.1.base.mir res.2.1.base.mir (fun _ => false) ec >>= fun ec' =>
         pure (res.1, (res.2, ec'))) :=
  stepSimCEager_inject_of_not_stops_core P ℓ Dh encPt encT decT idOf lam qep k Q w x ec
    (by rw [huse, Bool.false_and]) hstops hev


/-- At a receive that uses no coin, does not stop, and preserves both epochs, `stepSimCEager` on an inject query equals `pure` of `simRecvStepCGen … false` with unchanged eager coins. -/
theorem stepSimCEager_inject_of_not_stops (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hec : ValidEagerCoins x.1.base.mir ec)
    (huse : simRecvUsesCoin P encT decT k Q w false x.sim = false)
    (hstops : simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim = false)
    (res : Option (RecvResult (Plain ℓ)) × JointC PQ Pt ℓ)
    (hres : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false x = res)
    (hep : res.2.1.base.mir.epoch = x.1.base.mir.epoch)
    (hev : evictStopsC P encT decT k Q w false x = false := by evict_stops_tac) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec =
      pure (res.1, (res.2, ec)) := by
  rw [stepSimCEager_inject_of_not_stops_gen P ℓ Dh encPt encT decT idOf lam qep k Q w x ec huse
    hstops hev]
  dsimp only
  rw [hres]
  have hA : inReceiveOnlyEpoch res.2.1.base.mir .A = inReceiveOnlyEpoch x.1.base.mir .A := by simp [inReceiveOnlyEpoch, hep]
  have hB : inReceiveOnlyEpoch res.2.1.base.mir .B = inReceiveOnlyEpoch x.1.base.mir .B := by simp [inReceiveOnlyEpoch, hep]
  rw [updateAllEagerCoins_same_inWin x.1.base.mir res.2.1.base.mir ec hA hB hec, pure_bind]

/-! ## Receive panics -/

theorem recvPanicsW_eq_true_of (P : Params PQ PQC) (Q : Party) (w : List (BitVec 8))
    (s : SimState PQ Pt ℓ) (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    (hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = true) :
    recvPanicsW P Q w s = true := by
  unfold recvPanicsW
  simp [hlen, hparse, haddrs, hpan]

theorem recvPanicsW_eq_false_of (P : Params PQ PQC) (Q : Party) (w : List (BitVec 8))
    (s : SimState PQ Pt ℓ) (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hpan : P.spqr.recvPanics (s.pq Q) h.pqRatchet = false) :
    recvPanicsW P Q w s = false := by
  unfold recvPanicsW
  simp [hlen, hparse, hpan]

theorem simRecvStops_of_recvPanicsW (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (h : recvPanicsW P Q w st.1 = true) :
    simRecvStops P ℓ Dh encPt encT decT idOf lam qep k Q w isDel st = false := by
  unfold simRecvStops
  rw [h]
  rfl

theorem evictCaseC_of_recvPanicsW (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (s : SimState PQ Pt ℓ) (h : recvPanicsW P Q w s = true) :
    evictCaseC P encT decT Q w isDel s = false := by
  unfold recvPanicsW at h
  unfold evictCaseC
  by_cases hlen : w.length < 9
  · simp [hlen] at h
  cases hp : (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => simp [hlen, hp] at h
  | some hb =>
    rcases hb with ⟨hd, body⟩
    by_cases haddrs : addressCheckPasses hd.addresses (P.expectedAddrs Q) = true
    · have hpan : P.spqr.recvPanics (s.pq Q) hd.pqRatchet = true := by
        simpa [hlen, hp, haddrs] using h
      simp [hlen, hp, haddrs, hpan]
    · simp [hlen, hp, haddrs] at h

theorem evictStopsC_of_recvPanicsW (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (k : Option ℕ) (Q : Party) (w : List (BitVec 8))
    (isDel : Bool) (x : JointC PQ Pt ℓ) (h : recvPanicsW P Q w x.1.base = true) :
    evictStopsC P encT decT k Q w isDel x = false := by
  unfold evictStopsC
  rw [evictCaseC_of_recvPanicsW P encT decT Q w isDel x.1.base h, Bool.false_and]

theorem stepSimCEager_inject_of_recvPanics (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (w : List (BitVec 8)) (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256)
    (hec : ValidEagerCoins x.1.base.mir ec)
    (hpanW : recvPanicsW P Q w x.1.base = true)
    (hres : simRecvStepCGen P ℓ Dh encPt encT decT idOf lam qep false Q w false x =
      (some .rejected, x)) :
    stepSimCEager P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inr (Q, w))) x ec =
      pure (some .rejected, (x, ec)) := by
  rw [stepSimCEager_inject_of_not_stops_core P ℓ Dh encPt encT decT idOf lam qep k Q w x ec
    (by rw [hpanW, Bool.not_true, Bool.and_false])
    (simRecvStops_of_recvPanicsW P ℓ Dh encPt encT decT idOf lam qep k Q w false x.sim hpanW)
    (evictStopsC_of_recvPanicsW P encT decT k Q w false x hpanW)]
  dsimp only
  rw [hres]
  rw [updateAllEagerCoins_same_inWin x.1.base.mir x.1.base.mir ec rfl rfl hec, pure_bind]

/-- Libsignal `receive` returns `none` whenever `P.spqr.recvPanics` holds on the wire's SPQR ratchet payload. -/
theorem receive_eq_none_of_spqr_panic (P : Params PQ PQC)
    (Q : Party) (g_in : GhostState PQ) (hparty : g_in.party = Q)
    (w : List (BitVec 8)) (hw_len : ¬ w.length < 9)
    (h : SignalHeader) (body : List (BitVec 8))
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hpan : P.spqr.recvPanics g_in.session.pqRatchetState h.pqRatchet = true)
    (rc : BitVec 256) :
    P.receive g_in w rc = none := by
  have htry : SignalMessage.tryFrom P.codec w =
      .ok ⟨h.messageVersion, h.senderRatchetKey, h.counter, h.previousCounter, body,
        h.pqRatchet, h.addresses, w⟩ :=
    tryFrom_of_parse P.codec w h body hw_len hparse
  unfold Params.receive
  rw [htry, hparty]
  dsimp only
  unfold SessionState.tryDecryptFromRecord
  by_cases hver : g_in.session.version.toNat ≠ h.messageVersion.toNat
  · rw [ite_eq_left hver]
  · rw [ite_eq_right hver]
    unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
      SessionState.takeRatchetState SessionState.takePqRatchetState
      TripleRatchet.decrypt TripleRatchet.onRatchet zoom
    simp only [Mut.exec_bind, Mut.exec_modifyGet, Mut.exec_get, Mut.exec_set]
    cases g_in.session.remoteIdentity with
    | none => simp [Mut.exec_throw]
    | some remote =>
      dsimp only [Mut.exec_pure]
      rcases h_ens : Mut.exec (RatchetState.ensureReceiverChain P.C h.senderRatchetKey rc)
        { rootKey := g_in.session.rootKey, senderChain := g_in.session.senderChain,
          receiverChains := g_in.session.receiverChains,
          previousCounter := g_in.session.previousCounter,
          maxForwardJumps := maxForwardJumps } with ⟨r_ens, s_ens⟩
      cases r_ens with
      | error e => simp [h_ens, Mut.exec_liftE_error]
      | ok ck =>
        rcases h_con : Mut.exec (RatchetState.consumeMessageKey P.C.F h.senderRatchetKey ck h.counter .whisper)
          s_ens with ⟨r_con, s_con⟩
        cases r_con with
        | error e => simp [h_ens, h_con, Mut.exec_liftE_ok, Mut.exec_liftE_error]
        | ok mkGen =>
          simp [h_ens, h_con, hpan, Mut.exec_liftE_ok, Mut.exec_throw, Mut.exec_liftE_error]

private theorem skr_receive_eq {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {s st' : Fig8St Pt} {c' : Fig8C Pt} {res : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)}
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive s c' = some (st', res)) :
    s.id.sendsIn c'.1.1 = false ∧
    ((c'.1.1 = s.tcur + 1 ∧ st'.tcur = c'.1.1 ∧
        ∃ v', st'.vR = Function.update s.vR c'.1.1 (some v')) ∨
      (c'.1.1 ≤ s.tcur ∧ st'.tcur = s.tcur ∧
        ∃ v v' im, s.vR c'.1.1 = some v ∧
          (lFS P.C P.codec ℓ encT idOf 25000).receive v c'.1 c'.2 = some (v', im) ∧
          st'.vR = Function.update s.vR c'.1.1 (some v'))) := by
  change SM.Construction.receive (dhScheme Dh) (rootPRNG P.C.F encPt)
    (lFS P.C P.codec ℓ encT idOf 25000) s c' = some (st', res) at hfig
  unfold SM.Construction.receive at hfig
  dsimp only at hfig
  split_ifs at hfig with hcond hnew
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_lt] at hcond
    refine ⟨hcond.1, Or.inl ⟨hnew, ?_⟩⟩
    cases hT : c'.1.2 with
    | none => simp [hT] at hfig
    | some Tn =>
      simp only [hT, Function.update_self] at hfig
      rcases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive
          ((lFS P.C P.codec ℓ encT idOf 25000).initReceiver
            ((rootPRNG P.C.F encPt).up s.root ((dhScheme Dh).receive s.γ Tn).2).2)
          c'.1 c'.2 with _ | ⟨v', i, m⟩
      · simp [hfs] at hfig
      · simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
        rcases hfig with ⟨rfl, _⟩
        exact ⟨rfl, v', by funext t; by_cases ht : t = c'.1.1 <;> simp [ht]⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_lt] at hcond
    refine ⟨hcond.1, Or.inr ⟨by omega, ?_⟩⟩
    cases hv : s.vR c'.1.1 with
    | none => simp [hv] at hfig
    | some v =>
      simp only [hv] at hfig
      cases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c'.1 c'.2 with
      | none => simp [hfs] at hfig
      | some vim =>
        rcases vim with ⟨v', i, m⟩
        simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
        rcases hfig with ⟨rfl, _⟩
        exact ⟨rfl, v, v', (i, m), rfl, hfs, rfl⟩

/-- Preserves `KeptInv` when Fig. 8 accepts `c'` at `Q` and `Q`'s `kept` advances by `Kept.recv c'`. -/
theorem keptInv_recv_accept {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : KeptInv P Dh encPt encT idOf lam sC s_fig8)
    (Q : Party) (hid : (s_fig8.st Q).id = Q)
    (c' : Fig8C Pt) (st' : Fig8St Pt) (res : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
      some (st', res))
    (hst : s_fig8'.st = Function.update s_fig8.st Q st')
    (hkept : sC'.kept = Function.update sC.kept Q
      (Kept.recv (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q))) :
    KeptInv P Dh encPt encT idOf lam sC' s_fig8' where
  hfull R st hst' := by
    rw [hst]
    rw [hkept] at hst'
    by_cases hR : R = Q
    · subst hR
      simp only [Function.update_self, Kept.recv] at hst' ⊢
      cases hfull0 : (sC.kept R).full with
      | none => simp [hfull0] at hst'
      | some st0 =>
        have hst0 := h.hfull R st0 hfull0
        subst hst0
        simp [hfull0, hfig] at hst'
        exact hst'.symm
    · simp only [Function.update_of_ne hR] at hst' ⊢
      exact h.hfull R st hst'
  hrs R t v hfull' hrs' := by
    rw [hst]
    rw [hkept] at hfull' hrs'
    by_cases hR : R = Q
    · subst hR
      simp only [Function.update_self, Kept.recv] at hfull' hrs' ⊢
      cases hfull0 : (sC.kept R).full with
      | some st0 =>
        have hst0 := h.hfull R st0 hfull0
        subst hst0
        simp [hfull0, hfig] at hfull'
      | none =>
        simp only [hfull0] at hrs'
        obtain ⟨_, hcase⟩ := skr_receive_eq hfig
        by_cases ht : t = c'.1.1
        · subst ht
          simp only [Function.update_self, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrs'
          rcases hrs' with ⟨v₀, hrs0, ⟨v', im⟩, hfs, rfl⟩
          have hvR0 := h.hrs R c'.1.1 v₀ hfull0 hrs0
          have hle : c'.1.1 ≤ (s_fig8.st R).tcur :=
            ((h.hvR R c'.1.1).mp (by simp [hvR0])).1
          rcases hcase with ⟨hnew, _⟩ | ⟨_, _, v₁, v₁', im₁, hvR1, hfs1, hvR'⟩
          · omega
          · rw [hvR', Function.update_self]
            rw [hvR0] at hvR1
            cases hvR1
            rw [hfs] at hfs1
            cases hfs1
            rfl
        · simp only [Function.update_of_ne ht] at hrs'
          have hvR0 := h.hrs R t v hfull0 hrs'
          rcases hcase with ⟨_, _, v', hvR'⟩ | ⟨_, _, _, v', _, _, _, hvR'⟩ <;>
            simp [hvR', Function.update_of_ne ht, hvR0]
    · simp only [Function.update_of_ne hR] at hfull' hrs' ⊢
      exact h.hrs R t v hfull' hrs'
  hvR R t := by
    rw [hst]
    by_cases hR : R = Q
    · subst hR
      simp only [Function.update_self]
      obtain ⟨hsends, hcase⟩ := skr_receive_eq hfig
      rw [hid] at hsends
      rcases hcase with ⟨hnew, htcur', v', hvR'⟩ | ⟨hle, htcur', _, v', _, _, _, hvR'⟩
      · rw [hvR', htcur']
        by_cases ht : t = c'.1.1
        · subst ht
          simp [hsends]
        · have hle : (t ≤ (s_fig8.st R).tcur) ↔ (t ≤ c'.1.1) := by omega
          simp [Function.update_of_ne ht, h.hvR R t, hle]
      · rw [hvR', htcur']
        by_cases ht : t = c'.1.1
        · subst ht
          simp [hle, hsends]
        · simp [Function.update_of_ne ht, h.hvR R t]
    · simp only [Function.update_of_ne hR]
      exact h.hvR R t

/-! ## Absorbing win on eager runs -/

private def iwt_preserves {α : Type}
    (m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α) : Prop :=
  ∀ (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool),
    gh.1.win = true →
    ∀ r ∈ support ((m.run sC).run gh), r.2.1.win = true

private theorem iwt_preserves_pure {α : Type} (a : α) :
    iwt_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (pure a) := by
  intro sC gh hgh r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iwt_preserves_bind {α β : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    {k : α → StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) β}
    (hm : iwt_preserves m) (hk : ∀ a, iwt_preserves (k a)) :
    iwt_preserves (m >>= k) := by
  intro sC gh hgh r hr
  simp only [StateT.run_bind, MonadAttach.mem_support_bind] at hr
  rcases hr with ⟨r₁, hr₁, hr⟩
  exact hk r₁.1.1 r₁.1.2 r₁.2 (hm sC gh hgh r₁ hr₁) r hr

private theorem iwt_preserves_get :
    iwt_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) get := by
  intro sC gh hgh r hr
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iwt_preserves_set (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    iwt_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (set sC') := by
  intro sC gh hgh r hr
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iwt_preserves_modify (f : LibsignalToModularSchemeSimState PQ Pt ℓ → LibsignalToModularSchemeSimState PQ Pt ℓ) :
    iwt_preserves (PQ := PQ) (Pt := Pt) (ℓ := ℓ) (modify f) := by
  intro sC gh hgh r hr
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iwt_probeHook_lift_run {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (y : Fig8Comp Pt ℓ α)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift y).run gh =
      ((simulateQ (fig8ImplH1 fig qepF) y).run gh.1 >>= fun p => pure (p.1, (p.2, gh.2))) := rfl

private theorem iwt_fig8ImplH1_preserve {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (y : Fig8Comp Pt ℓ α)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (hg : g.win = true) :
    ∀ p ∈ support ((simulateQ (fig8ImplH1 fig qepF) y).run g), p.2.win = true :=
  simulateQ_run_preserve (SM.oracleImpl fig (2 + 1) qepF SM.Config.h1)
    (fun s => s.win = true)
    (fun q' s hs => oracleImpl_run_of_win_true fig (2 + 1) qepF SM.Config.h1 q' s hs)
    y g hg

private theorem iwt_preserves_ite {α : Type} {P_cond : Prop} [Decidable P_cond]
    {t e : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) α}
    (ht : iwt_preserves t) (he : iwt_preserves e) :
    iwt_preserves (if P_cond then t else e) := by
  by_cases h : P_cond <;> simp only [h, ↓reduceIte]
  · exact ht
  · exact he

private theorem iwt_preserves_zoomB {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) α) :
    iwt_preserves (PQ := PQ) (runOnBaseState (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).lift (x.run sC.base) >>= fun p =>
    pure (p.1, { sC with base := p.2 })) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, iwt_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨p, hp, rfl⟩
  exact iwt_fig8ImplH1_preserve fig qepF (x.run sC.base) gh.1 hgh p hp

private theorem iwt_preserves_liftC {α : Type}
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (x : Fig8Comp Pt ℓ α) :
    iwt_preserves (PQ := PQ) (LibsignalSimC.liftC (probeHook fig qepF) x) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).lift x >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, iwt_probeHook_lift_run] at hr
  simp only [bind_assoc, pure_bind, StateT.run_pure, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨p, hp, rfl⟩
  exact iwt_fig8ImplH1_preserve fig qepF x gh.1 hgh p hp

private theorem iwt_probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh =
      pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

private theorem iwt_preserves_probe
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt) :
    iwt_preserves (PQ := PQ)
      (StateT.lift ((probeHook fig qepF).probe Q c') :
        StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) Unit) := by
  intro sC gh hgh r hr
  change r ∈ support ((((probeHook fig qepF).probe Q c' >>= fun a =>
    pure (a, sC)) : ProbeM Pt ℓ _).run gh) at hr
  rw [StateT.run_bind, iwt_probeHook_probe_run] at hr
  simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact hgh

private theorem iwt_preserves_guardC {α : Type}
    {m : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (ProbeM Pt ℓ) (Option α)}
    (hm : iwt_preserves m) :
    iwt_preserves (guardC m) := by
  unfold guardC
  refine iwt_preserves_bind iwt_preserves_get fun sC => ?_
  exact iwt_preserves_ite (iwt_preserves_pure none) hm

private theorem iwt_preserves_simSendC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    iwt_preserves (simSendC P qep fig (probeHook fig qepF) Q m₀ chal r) := by
  unfold simSendC
  refine iwt_preserves_bind (iwt_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact iwt_preserves_pure none
  | some w =>
    refine iwt_preserves_bind iwt_preserves_get fun sC => ?_
    exact iwt_preserves_bind (iwt_preserves_set _) fun _ => iwt_preserves_pure (some w)

private theorem iwt_preserves_fwdAnswerC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    iwt_preserves (fwdAnswerC qep fig fs (probeHook fig qepF) Q w isDel ci? T pq' c') := by
  unfold fwdAnswerC
  refine iwt_preserves_bind (iwt_preserves_zoomB (PQ := PQ) fig qepF _) fun res => ?_
  cases res with
  | none => exact iwt_preserves_zoomB (PQ := PQ) fig qepF _
  | some r =>
    cases r <;>
      first
      | exact iwt_preserves_zoomB (PQ := PQ) fig qepF _
      | exact iwt_preserves_bind (iwt_preserves_modify _) fun _ =>
          iwt_preserves_zoomB (PQ := PQ) fig qepF _

private theorem iwt_preserves_resyncC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (c : Fig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    iwt_preserves (resyncC qep fig fs (probeHook fig qepF) Q w ci? T pq' c r) := by
  unfold resyncC
  cases r with
  | none => exact iwt_preserves_pure _
  | some tipm =>
    rcases tipm with ⟨t, i, pm⟩
    refine iwt_preserves_bind (iwt_preserves_liftC fig qepF _) fun res => ?_
    cases res with
    | none => exact iwt_preserves_pure _
    | some r' =>
      cases r' with
      | accepted _ _ _ =>
        exact iwt_preserves_bind (iwt_preserves_modify _) fun _ =>
          iwt_preserves_zoomB (PQ := PQ) fig qepF _
      | _ => exact iwt_preserves_pure _

private theorem iwt_preserves_fwdC (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (T : PublicKey) (pq' : PQ) (honestC : Option (Fig8C Pt)) (c' : Fig8C Pt) :
    iwt_preserves (fwdC P qep fig fs (probeHook fig qepF) Q w isDel ci? T pq'
      honestC c') := by
  unfold fwdC
  refine iwt_preserves_bind iwt_preserves_get fun sC => ?_
  cases honestC with
  | none => exact iwt_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c'
  | some c =>
    refine iwt_preserves_ite ?_ (iwt_preserves_fwdAnswerC qep fig fs qepF Q w isDel ci? T pq' c')
    cases predictReceiveWithSnapshots (fig := fig) (fs := fs) P sC Q w c c' with
    | some r => exact iwt_preserves_resyncC qep fig fs qepF Q w ci? T pq' c r
    | none =>
      exact iwt_preserves_bind (iwt_preserves_probe fig qepF Q c') fun _ =>
        iwt_preserves_pure _

private theorem iwt_preserves_fwdEvictC (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (T : PublicKey) (pq' : PQ) (c' : Fig8C Pt) :
    iwt_preserves (fwdEvictC qep fig fs (probeHook fig qepF) Q w isDel T pq' c') := by
  unfold fwdEvictC
  refine iwt_preserves_bind iwt_preserves_get fun sC => ?_
  refine iwt_preserves_ite ?_ (iwt_preserves_fwdAnswerC qep fig fs qepF Q w isDel none T pq' c')
  exact iwt_preserves_bind (iwt_preserves_probe fig qepF Q c') fun _ => iwt_preserves_pure _

private theorem iwt_preserves_simRecvC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (FSAEAD.RatchetSenderState (BitVec 256))
      (FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (ℕ × LibsignalCiphertextWithSalt32))
    (qepF : ℕ) (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    iwt_preserves (simRecvC P encT decT qep fig fs (probeHook fig qepF) Q w isDel) := by
  unfold simRecvC
  generalize (2 ^ 32 : ℕ) = maxI
  generalize (25000 : ℕ) = maxSkip
  refine iwt_preserves_bind iwt_preserves_get fun sC => ?_
  dsimp only
  refine iwt_preserves_ite (iwt_preserves_pure _) ?_
  refine iwt_preserves_ite (iwt_preserves_pure _) ?_
  refine iwt_preserves_ite (iwt_preserves_pure _) ?_
  refine iwt_preserves_ite (iwt_preserves_pure _) ?_
  cases (signalWireCodec P.codec).parse (w.take (w.length - 8)) with
  | none => exact iwt_preserves_pure _
  | some hb =>
    rcases hb with ⟨h, _⟩
    dsimp only
    refine iwt_preserves_ite (iwt_preserves_pure _) ?_
    refine iwt_preserves_ite (iwt_preserves_pure _) ?_
    cases P.spqr.recv (sC.base.pq Q) h.pqRatchet with
    | error _ => exact iwt_preserves_pure _
    | ok ps =>
      rcases ps with ⟨pq', salt⟩
      dsimp only
      cases List.findIdx? (fun g => g.key == some h.senderRatchetKey) (sC.base.chains Q) with
      | some ci =>
        dsimp only
        refine iwt_preserves_ite (iwt_preserves_pure _) ?_
        exact iwt_preserves_fwdC P qep fig fs qepF Q w isDel (some ci)
          h.senderRatchetKey pq' _ _
      | none =>
        dsimp only
        refine iwt_preserves_ite (iwt_preserves_pure _) ?_
        refine iwt_preserves_ite (iwt_preserves_pure _) ?_
        refine iwt_preserves_ite
          (iwt_preserves_bind (iwt_preserves_modify _) fun _ => ?_) ?_ <;>
        · refine iwt_preserves_ite (iwt_preserves_pure _) ?_
          cases decT h.senderRatchetKey with
          | none => exact iwt_preserves_pure _
          | some T =>
            exact iwt_preserves_ite
              (iwt_preserves_fwdEvictC qep fig fs qepF Q w isDel h.senderRatchetKey pq' _)
              (iwt_preserves_fwdC P qep fig fs qepF Q w isDel none
                h.senderRatchetKey pq' _ _)

private theorem iwt_preserves_simCorrC (P : Params PQ PQC) (encT : Pt → PublicKey)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Dh : DHFun (BitVec 256) Pt) (Q : Party) :
    iwt_preserves (simCorrC P encT (probeHook fig qepF) Dh Q) := by
  unfold simCorrC
  refine iwt_preserves_bind iwt_preserves_get fun sC => ?_
  refine iwt_preserves_ite (iwt_preserves_pure _) ?_
  refine iwt_preserves_bind (iwt_preserves_liftC fig qepF _) fun res => ?_
  cases res with
  | none => exact iwt_preserves_pure _
  | some st =>
    exact iwt_preserves_bind (iwt_preserves_set _) fun _ => iwt_preserves_pure _

private theorem iwt_stepSimCNone_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep q x), z.2.2.1.win = true := by
  intro z hz
  unfold stepSimCNone at hz
  rw [MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨r, hr, hz⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  have hpres : iwt_preserves
      (simImplC P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000)
        (probeHook (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (qep + 1)) Dh
        (.inr q)) := by
    rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
    · exact iwt_preserves_guardC (iwt_preserves_simSendC P qep _ (qep + 1) Q m₀ none r')
    · exact iwt_preserves_guardC (iwt_preserves_simSendC P qep _ (qep + 1) Q m₀ (some m₁) r')
    · exact iwt_preserves_guardC (iwt_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w true)
    · exact iwt_preserves_guardC (iwt_preserves_simRecvC P encT decT qep _ _ (qep + 1) Q w false)
    · exact iwt_preserves_guardC (iwt_preserves_simCorrC P encT _ (qep + 1) Dh Q)
  exact hpres x.1 x.2 hwin r hr

private theorem iwt_stepSimC_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimC P ℓ Dh encPt encT decT idOf lam qep none q x), z.2.2.1.win = true := by
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact iwt_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin
  · exact iwt_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, hr, rfl⟩
      exact stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none _ x.sim hwin rfl r hr
    · exact iwt_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin z hz
  · intro z hz
    simp only [stepSimC] at hz
    split at hz
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
      rcases hz with ⟨r, hr, rfl⟩
      exact stepSim_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none _ x.sim hwin rfl r hr
    · exact iwt_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin z hz
  · exact iwt_stepSimCNone_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin

theorem stepSimCEager_preserve_win_true (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (q : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hwin : x.2.1.win = true) :
    ∀ z ∈ support (stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q x ec),
      z.2.1.2.1.win = true := by
  intro z hz
  rcases q with ((((⟨Q, m₀, r'⟩ | ⟨Q, m₀, m₁, r'⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · simp only [stepSimCEager, stepSimCEagerTransmit, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inl (.inl (Q, m₀, r'))))) x.sim ec hwin rfl res hres
  · simp only [stepSimCEager, stepSimCEagerChall, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, rfl⟩
    exact stepSimEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep none
      (.inl (.inl (.inl (.inr (Q, m₀, m₁, r'))))) x.sim ec hwin rfl res hres
  · simp only [stepSimCEager, stepSimCEagerDeliver] at hz
    rw [simRecvUsesCoin_of_win_true P encT decT none Q w true x.sim hwin, evictStopsC_none] at hz
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iwt_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres
  · simp only [stepSimCEager, stepSimCEagerInject] at hz
    rw [simRecvUsesCoin_of_win_true P encT decT none Q w false x.sim hwin, evictStopsC_none] at hz
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iwt_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres
  · simp only [stepSimCEager, stepSimCEagerCorr, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨res, hres, _, _, rfl⟩
    exact iwt_stepSimC_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep _ x hwin res hres

/-- Fig. 8 `win = true` is preserved across any `runSimCEager` execution at `k = none`. -/
theorem evalDist_runSimCEager_win_true {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (oa : SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (x : JointC PQ Pt ℓ) (ec : Party → BitVec 256) (hwin : x.2.1.win = true)
    (F : α × (JointC PQ Pt ℓ × (Party → BitVec 256)) → ProbComp Bool)
    (hF : ∀ z, z.2.1.2.1.win = true → 𝒟[F z] {true} = 1) :
    𝒟[runSimCEager P ℓ Dh encPt encT decT idOf lam qep none oa x ec >>= F] {true} = 1 := by
  unfold runSimCEager
  refine Construction.AuthL11.evalDist_bind_eq_one _ F fun z hz => ?_
  refine hF z (simulateQ_run_preserve
    (simEagerImplC P ℓ Dh encPt encT decT idOf lam qep none)
    (fun s => s.1.2.1.win = true) ?_ oa (x, ec) hwin z hz)
  intro q s hs
  exact stepSimCEager_preserve_win_true P ℓ Dh encPt encT decT idOf lam qep q s.1 s.2 hs

/-! ## Unused receive-coin combinators -/

/-- Closes an R step that ignores its receive coin against a pure eager C step that preserves `amb`. -/
theorem closeByStateC_inr_const_rc_same_amb {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl fl' : Bool)
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R)
    (hR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')))
    (hSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hSimK : ∀ idx, ¬ idx < sC.base.amb →
      stepSimCEager P ℓ Dh encPt encT decT idOf lam qep (some idx) q_sm (sC, s_fig8, fl) ec =
        pure (ans, ((sC', s_fig8', fl'), ec')))
    (hamb : sC'.base.amb = sC.base.amb)
    (hrem : remWin qep sC'.base.mir ≤ remWin qep sC.base.mir)
    (hcont : CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (cont ans) s_R' sC' s_fig8' fl' ec' winBefore) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC at hcont ⊢
  refine closeByRefinesH_congr_all ?_ ?_ ?_ ?_ ?_
    (closeByRefinesH_mono_d (stepSlack_mono P encPt Dh q qep δ hrem) hcont)
  · rw [runRCont_inr_bind, hR]
    simp only [bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _
  · simp only [runSimCEager_inr_bind, hSim, pure_bind]
  · intro idx _
    exact evalDist_runWinAtC_inr_same_amb_bind P ℓ Dh encPt encT decT idOf lam qep q_sm cont
      (sC, s_fig8, fl) ec (pure ()) (fun _ => (ans, ((sC', s_fig8', fl'), ec'))) (fun _ => hamb)
      (fun idx h => by rw [hSimK idx h]; simp) winBefore idx |>.trans (by simp)
  · rw [runRCont_inr_bind, hD0, hR]
    simp only [bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_const _ _
  · simp only [runHidC, runSimCEager_inr_bind, hSim, pure_bind]

/-- Closes an R step that ignores its receive coin when both R and Fig. 8 have won after the step. -/
theorem closeByStateC_inr_both_win_const_rc {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl fl' : Bool)
    (ec ec' : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hR : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')))
    (hSim : stepSimCEager P ℓ Dh encPt encT decT idOf lam qep none q_sm (sC, s_fig8, fl) ec =
      pure (ans, ((sC', s_fig8', fl'), ec')))
    (hwin_R : s_R'.win = true)
    (hwin_fig8 : s_fig8'.win = true) :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_iff.mpr (closeByRefines_of_both_win_eq_one _ _ _ _ _ _ ?_ ?_)
  · rw [runRCont_inr_bind, hR]
    simp only [bind_assoc, pure_bind]
    rw [congrFun (congrArg DFunLike.coe (OracleComp.evalDist_bind_const ($ᵗ BitVec 256) _)) {true}]
    exact evalDist_runRCont_win_true (libsignalSessionScheme P ℓ encPt lam) 3 qep
      (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) (cont ans) s_R' hwin_R _
      (fun z hz => by simp [hz])
  · simp only [runSimCEager_inr_bind, hSim, pure_bind]
    exact evalDist_runSimCEager_win_true P ℓ Dh encPt encT decT idOf lam qep
      (cont ans) (sC', s_fig8', fl') ec' hwin_fig8 _
      (fun z hz => by simp [hz])

/-- Closes an R step that ignores its receive coin when `configEpoch0Distinguisher` triggers the `ε₀` event. -/
theorem closeByStateC_inr_eps0_const_rc {α : Type} (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (post : α → Bool)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (cont : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm →
      SM.AdversaryComp (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)) α)
    (s_R s_R' : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) (fl : Bool)
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool)
    (ans : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range q_sm)
    (hD0 : stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun _ => pure (ans, s_R')))
    (heps0 : eps0Cond s_R') :
    CloseByStateC P ℓ Dh encPt encT decT idOf lam qep q δ post
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) (.inr q_sm)) >>= cont)
      s_R sC s_fig8 fl ec winBefore := by
  unfold CloseByStateC
  refine closeByRefinesH_of_eps0_eq_one ?_
  rw [runRCont_inr_bind, hD0]
  simp only [bind_assoc, pure_bind]
  rw [congrFun (congrArg DFunLike.coe (OracleComp.evalDist_bind_const ($ᵗ BitVec 256) _)) {true}]
  exact evalDist_runRCont_eps0_true (libsignalSessionScheme P ℓ encPt lam) 3 qep
    (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) (cont ans) s_R' heps0 _
    (fun z hz => by
      rcases hz with ⟨h1, h2, _⟩ | ⟨h1, h2⟩ <;> simp [h1, h2])

end CryptoGames.LibsignalSM.Proofs.Refinement
