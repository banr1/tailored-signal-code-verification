/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Ratchet.LibsignalSimDF

/-!
# Read-Time Sanitized and Clamped Semantic Hooks

Defines read-time state sanitizers (`sanRS`, `sanGamma`, `sanAt`, `fig8San`, `fsSan`) and
`chainSeedAtB`-clamped snapshot key recovery (`snapshotMessageKeySeedB`), uses them to build
sanitized semantic hooks (`semHandleHookDedupS`) generic over `SemHook`, and proves `SimCStateInv`
preservation.
-/

@[expose] public section

set_option autoImplicit false

open Computational.Proofs.GameHop.CompDedup (afterCorrDedup countLe_dedupPrepend)
open CryptoGames (FSAEADScheme Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSession (GhostState Params PublicKey ShaCompress rootCreateChain)
open CryptoGames.Ratchet.LibsignalInst (LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart lFS lFig8 ratchetKeyAdmissible)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St GhostChain SemHook SimCStateInv SimFig8C SimState fig8Clamp fsClampSim inReceiveOnlyEpoch onAcceptPure onAcceptPure_preserves_inv onAnswerPure onAnswerPure_preserves_inv semSendHook semSendHook_preserves_sC_inv simKDecryptFig8 simParseRecvC toGhost)
open CryptoGames.Ratchet.LibsignalSimC (LibsignalToModularSchemeSimState chainSeedAt predictReceive)
open CryptoGames.SM (RecvResult noAliceCorrWhileAliceBelowEpoch10 partyEnc)
open CryptoGames.SM.Construction (Header)

namespace Computational.Proofs.Game.PromotedCostedReds.SanOracleCore

open OracleSpec OracleComp

/-! ## Read-time sanitizers -/

section Sanitizer

variable {Pt : Type} {ℓ : ℕ}

def sanRS (T : ℕ) (v : CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) :
    CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) :=
  { v with skippedKeys := v.skippedKeys.take T }

/-- Enforces the ping-pong CKA state shape (`.pub` before a sending epoch, `.exp` before a
receiving epoch); acts as the identity under `Fig8CkaInv`. -/
def sanGamma (lam : Pt) (st : Fig8St Pt) : CryptoGames.CKA.DDH.State (BitVec 256) Pt :=
  if st.id.sendsIn (st.tcur + 1) then
    match st.γ with
    | .pub h => .pub h
    | .exp _ => .pub lam
  else
    match st.γ with
    | .exp x => .exp x
    | .pub _ => .exp 0

/-- Truncates the receiving session at epoch `t` to `T` skipped keys and fixes `st.γ` via `sanGamma`. -/
def sanAt (T : ℕ) (lam : Pt) (t : ℕ) (st : Fig8St Pt) : Fig8St Pt :=
  { st with
    vR := fun j => if j = t then (st.vR t).map (sanRS T) else st.vR j
    γ := sanGamma lam st }

def fig8San {Key M Coins : Type} (T : ℕ) (lam : Pt)
    (fig : SMScheme Key (Fig8St Pt) M Coins (Fig8C Pt)) :
    SMScheme Key (Fig8St Pt) M Coins (Fig8C Pt) :=
  { fig with receive := fun st c => fig.receive (sanAt T lam c.1.1 st) c }

def fsSan {SS AD M C : Type} (T : ℕ)
    (fs : FSAEADScheme (BitVec 256) SS
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) AD M C) :
    FSAEADScheme (BitVec 256) SS
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) AD M C :=
  { fs with receive := fun v h c => fs.receive (sanRS T v) h c }

def fig8StTruncSkB (B_skip : ℕ) (st : Fig8St Pt) : Fig8St Pt :=
  { st with
    vR := fun t => (st.vR t).map fun v => { v with skippedKeys := v.skippedKeys.take B_skip } }

end Sanitizer

/-! ## Clamped snapshot seeds -/

section ClampedSeeds

/-- `chainSeedAt` clamped to return `none` when more than `K` chain steps are needed. -/
def chainSeedAtB (K : ℕ) (F : ShaCompress) (ck : CryptoGames.LibsignalSession.ChainKey) (counter : BitVec 32) :
    Option (List (BitVec 8)) :=
  if K < counter.toNat - ck.index.toNat then none else chainSeedAt F ck counter

def snapshotMessageKeySeedB {PQ PQC : Type} (K : ℕ) (P : Params PQ PQC)
    (snaps : List (Party × ℕ × GhostState PQ))
    (Q : Party) (t : ℕ) (w : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match CryptoGames.LibsignalSession.SignalMessage.tryFrom P.codec w with
  | .error _ => none
  | .ok msg =>
    let Y := msg.senderRatchetKey
    let n := msg.counter
    let k1 := snaps.findSome? fun e =>
      if e.1 = Q then
        (e.2.2.session.receiverChains.find? (·.senderRatchetKey == Y)).bind fun rc =>
          match rc.messageKeys.find? (·.counter == n) with
          | some mkg => some mkg.seed
          | none => rc.chainKey.bind fun ck => chainSeedAtB K P.C.F ck n
      else none
    let k3 := snaps.findSome? fun e =>
      if e.1 = Q.other then
        e.2.2.session.senderChain.bind fun sc =>
          if sc.ratchetKey.publicKey = Y then chainSeedAtB K P.C.F sc.chainKey n else none
      else none
    let k2 := snaps.findSome? fun e =>
      if e.1 = Q ∧ Q.sendsIn e.2.1 = true ∧ t = e.2.1 + 1 then
        e.2.2.session.senderChain.bind fun sc =>
          match rootCreateChain P.C e.2.2.session.rootKey Y sc.ratchetKey.privateKey with
          | .ok (_, ck) => chainSeedAtB K P.C.F ck n
          | .error _ => none
      else none
    let k4 := (snaps.findSome? fun e_cur =>
        if e_cur.1 = Q.other ∧ e_cur.2.1 = t then
          e_cur.2.2.session.senderChain.bind fun sc_cur =>
            if sc_cur.ratchetKey.publicKey = Y then
              e_cur.2.2.session.receiverChains.getLast?.map fun rc_last =>
                (rc_last.senderRatchetKey, sc_cur.ratchetKey.privateKey)
            else none
        else none).bind fun p =>
      snaps.findSome? fun e_prev =>
        if e_prev.1 = Q.other ∧ Q.other.sendsIn e_prev.2.1 = true ∧
            t = e_prev.2.1 + 2 then
          e_prev.2.2.session.senderChain.bind fun sc_prev =>
            match rootCreateChain P.C e_prev.2.2.session.rootKey
                p.1 sc_prev.ratchetKey.privateKey with
            | .ok (rk1, _) =>
              match rootCreateChain P.C rk1 p.1 p.2 with
              | .ok (_, ck0) => chainSeedAtB K P.C.F ck0 n
              | .error _ => none
            | .error _ => none
        else none
    k1 <|> k3 <|> k2 <|> k4

end ClampedSeeds

/-! ## Sanitized semantic hooks -/

section SanHooks

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

abbrev figS (T : ℕ) :
    SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt) :=
  fig8San T lam (lFig8 Dh encPt P.C P.codec ℓ encT
    (fun R => if R == CryptoGames.Party.A then P.idA else P.idB) 25000 lam)

abbrev fsS (T : ℕ) :
    FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
      (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32) :=
  fsSan T (lFS P.C P.codec ℓ encT (fun R => if R == CryptoGames.Party.A then P.idA else P.idB) 25000)

def evalCKS (T K B : ℕ) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party)
    (w : List (BitVec 8)) (c c' : SimFig8C Pt) :
    Option (Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :=
  (predictReceive (fig := fig8Clamp B (figS P Dh encPt encT lam T))
      (fs := fsClampSim B (fsS P encT T)) sC Q c c').orElse fun _ =>
    (snapshotMessageKeySeedB K P sC.snaps Q c.1.1 w).map (simKDecryptFig8 P ℓ B (partyEnc Q) w c')

def semFwdAnswerHookS {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    OracleComp T' (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  let inT := sC.base.honest.any fun wc =>
    decide (wc.2 = c') && (sC.base.mir.inTransit Q.other wc.1).isSome
  (if inT then sh.onDl Q c' ex else sh.onIj Q c' ex) >>= fun (res, ex₁) =>
    let sC₂ : LibsignalToModularSchemeSimState PQ Pt ℓ := match res with
      | some (.accepted _ _ _) =>
        { sC with
          kept := Function.update sC.kept Q
            (CryptoGames.Ratchet.LibsignalSimC.Kept.recv (ℓ := ℓ) (fig := figS (ℓ := ℓ) P Dh encPt encT lam T)
              (fs := fsS (ℓ := ℓ) P encT T) c' (sC.kept Q)) }
      | _ => sC
    let (rr, base') := onAnswerPure qep Q w isDel ci? Tpk pq' res sC.base
    pure (rr, ({ sC₂ with base := base' }, ex₁))

def semResyncHookS {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c : SimFig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))) :
    OracleComp T' (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  match r with
  | none => return (some .rejected, (sC, ex))
  | some (t, i, (_, m')) => do
    let (res, ex₁) ← sh.onDl Q c ex
    match res with
    | some (.accepted _ _ _) =>
      let sC₅ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        { sC with
          kept := Function.update sC.kept Q
            (CryptoGames.Ratchet.LibsignalSimC.Kept.recv (ℓ := ℓ) (fig := figS (ℓ := ℓ) P Dh encPt encT lam T)
              (fs := fsS (ℓ := ℓ) P encT T) c (sC.kept Q)) }
      let (rr, base') := onAcceptPure qep Q w true t i m' ci? Tpk pq' sC.base
      return (rr, ({ sC₅ with base := base' }, ex₁))
    | _ => return (some .rejected, (sC, ex₁))

def semFwdEvictHookS {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt) :
    OracleComp T' (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  if isDel && !(sC.base.mir.safeInj 3) then do
    let ex₁ ← sh.onProbe Q c' ex
    return (some .rejected, (sC, ex₁))
  else
    semFwdAnswerHookS P Dh encPt encT lam T sh qep sC ex Q w isDel none Tpk pq' c'

def semFwdHookS {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt) :
    OracleComp T' (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  match honestC with
  | none => semFwdAnswerHookS P Dh encPt encT lam T sh qep sC ex Q w isDel ci? Tpk pq' c'
  | some c =>
    if !(decide (c = c')) && (isDel && !(sC.base.mir.safeInj 3)) then
      match evalCKS P Dh encPt encT lam T K B sC Q w c c' with
      | none => do
        let ex₁ ← sh.onProbe Q c' ex
        return (some .rejected, (sC, ex₁))
      | some r =>
        semResyncHookS P Dh encPt encT lam T sh qep sC ex Q w ci? Tpk pq' c r
    else
      semFwdAnswerHookS P Dh encPt encT lam T sh qep sC ex Q w isDel ci? Tpk pq' c'

def semRecvHookS {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex)
    (Q : Party) (w : List (BitVec 8)) (isDel : Bool) :
    OracleComp T' (Option (RecvResult (Plain ℓ)) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) := do
  let refuse :=
    sC.base.stopped || sC.base.mir.win ||
      (isDel && (sC.base.mir.inTransit Q.other w).isNone) ||
      (!isDel && ((sC.base.mir.inTransit Q.other w).isSome || !(sC.base.mir.safeInj 3) ||
        !(ratchetKeyAdmissible P.codec decT encT w)))
  if refuse then
    return (none, (sC, ex))
  else
    match simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC.base.pq Q) w with
    | none => return (some .rejected, (sC, ex))
    | some (pq', (i, (pk, (T?, lct)))) =>
      let honestC := (sC.base.honest.find? fun wc =>
        wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      let mkC (t : ℕ) (T : Option Pt) : SimFig8C Pt :=
        match honestC with
        | some c => if c.2.2.2 = lct.2.2 then c else ((t, T), lct)
        | none => ((t, T), lct)
      match (sC.base.chains Q).findIdx? (fun g => g.key == some pk) with
      | none =>
        let evicted := (honestC.map fun c => decide (c.1.1 ≠ sC.base.mir.epoch Q + 1)) == some true
        let saltEq := (honestC.map fun c => decide (c.2.2.2 = lct.2.2)) == some true
        let amb := inReceiveOnlyEpoch sC.base.mir Q ||
          (Q == CryptoGames.Party.A && (sC.base.chains Q).any (·.key.isNone))
        let sCAmb : LibsignalToModularSchemeSimState PQ Pt ℓ :=
          { sC with base := if amb then { sC.base with amb := sC.base.amb + 1 } else sC.base }
        if evicted && saltEq then
          return (some .rejected, (sC, ex))
        else if T? == some 0 then
          return (some .rejected, (sC, ex))
        else if inReceiveOnlyEpoch sC.base.mir Q || decide (25000 < i - 1) || decide (2 ^ 32 ≤ i) then
          return (some .rejected, (sCAmb, ex))
        else
          match T? with
          | none => return (some .rejected, (sCAmb, ex))
          | some T₀ =>
            if evicted then
              semFwdEvictHookS P Dh encPt encT lam T sh qep sCAmb ex Q w isDel pk pq'
                ((sC.base.mir.epoch Q + 1, some T₀), lct)
            else
              semFwdHookS P Dh encPt encT lam T K sh qep B sCAmb ex Q w isDel none pk pq'
                honestC (mkC (sC.base.mir.epoch Q + 1) (some T₀))
      | some ci =>
        let g := (sC.base.chains Q).getD ci ⟨none, 0, 0, []⟩
        if g.rejects i then
          return (some .rejected, (sC, ex))
        else
          semFwdHookS P Dh encPt encT lam T K sh qep B sC ex Q w isDel (some ci) pk pq'
            honestC (mkC g.epoch T?)

/-- Deduplicated corruption hook passing `fig8StTruncSkB B_skip fig8st` to `toGhost` while storing
the untruncated `fig8st` in `Kept.ofSt`. -/
def semCorrHookTGB {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T' Ex) (B_skip : ℕ)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) (Q : Party) :
    OracleComp T' (Option (GhostState PQ) × (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) := do
  if sC.base.stopped || sC.base.mir.win || !(sC.base.mir.corrAllowed Q) ||
     inReceiveOnlyEpoch sC.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC.base.mir Q) then
    return (none, (sC, ex))
  else
    let (res, ex₁) ← sh.onCr Q ex
    match res with
    | none => return (none, (sC, ex₁))
    | some fig8st =>
      let chains' : Party → List GhostChain :=
        if Q == CryptoGames.Party.B && sC.base.mir.epoch CryptoGames.Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC.base.chains CryptoGames.Party.A
              ((sC.base.chains CryptoGames.Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC.base.chains
        else sC.base.chains
      let base' : SimState PQ Pt ℓ :=
        { sC.base with mir := afterCorrDedup sC.base.mir Q, chains := chains' }
      let ghostOut := toGhost P { sC.base with chains := chains' } Q (fig8StTruncSkB B_skip fig8st)
      let sC' : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        { base := base'
          kept := Function.update sC.kept Q (CryptoGames.Ratchet.LibsignalSimC.Kept.ofSt fig8st)
          sent := sC.sent
          snaps := (Q, sC.base.mir.epoch Q, ghostOut) :: sC.snaps }
      return (some ghostOut, (sC', ex₁))

def semHandleHookDedupS {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T K B_skip : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (qep B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex : Ex) :
    OracleComp T'
      ((CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Range t ×
        (LibsignalToModularSchemeSimState PQ Pt ℓ × Ex)) :=
  match t with
  | .inl (.inl (.inl (.inl (Q, m, r)))) =>
    semSendHook P Dh encPt encT lam sh qep sC ex Q m none r
  | .inl (.inl (.inl (.inr (Q, m₀, m₁, r)))) =>
    semSendHook P Dh encPt encT lam sh qep sC ex Q m₀ (some m₁) r
  | .inl (.inl (.inr (Q, w))) => do
    let j? := sC.base.honest.reverse.findIdx? (fun wc =>
      wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other)
    let (rr, (sC₁, ex₁)) ← semRecvHookS P Dh encPt encT decT lam T K sh qep B sC ex Q w true
    let ex₂ ← sh.onDeliverPost Q j? rr ex₁
    return (rr, (sC₁, ex₂))
  | .inl (.inr (Q, w)) =>
    semRecvHookS P Dh encPt encT decT lam T K sh qep B sC ex Q w false
  | .inr Q =>
    semCorrHookTGB P Dh encT sh B_skip sC ex Q

end SanHooks

/-! ## `SimCStateInv` preservation -/

section Preservation

variable {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
  (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (lam : Pt)

theorem semFwdAnswerHookS_preserves_sC_inv {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (L m qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support
        (semFwdAnswerHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel ci? Tpk pq' c'),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdAnswerHookS at hx
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨⟨res, ex'⟩, -, _, rfl, _⟩ := hx
  refine ⟨onAnswerPure_preserves_inv qep L m Q w isDel ci? Tpk pq' res sC₀.base hInv.1, ?_, ?_⟩
  · rcases res with _ | (_ | ⟨t, i, pm⟩) <;> exact hInv.2.1
  · rcases res with _ | (_ | ⟨t, i, pm⟩) <;> exact hInv.2.2

omit [DecidableEq Pt] in
theorem semResyncHookS_preserves_sC_inv {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (L m qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (ci? : Option ℕ) (Tpk : PublicKey) (pq' : PQ)
    (c : SimFig8C Pt) (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support (semResyncHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w ci? Tpk pq' c r),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semResyncHookS at hx
  rcases r with _ | ⟨t, i, _, m'⟩
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hInv
  · simp only [mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | (_ | ⟨t', i', pm'⟩) <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hInv
    · rcases hx with ⟨_, rfl, _⟩; exact hInv
    · rcases hx with ⟨_, rfl, _⟩
      exact ⟨onAcceptPure_preserves_inv qep L m Q w true t i m' ci? Tpk pq' sC₀.base hInv.1,
        hInv.2.1, hInv.2.2⟩

theorem semFwdEvictHookS_preserves_sC_inv {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (L m qep : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (Tpk : PublicKey) (pq' : PQ) (c' : SimFig8C Pt)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support (semFwdEvictHookS P Dh encPt encT lam T sh qep sC₀ ex₀ Q w isDel Tpk pq' c'),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdEvictHookS at hx
  split_ifs at hx
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨_, -, _, rfl, _⟩ := hx; exact hInv
  · exact semFwdAnswerHookS_preserves_sC_inv P Dh encPt encT lam T sh L m qep
      sC₀ ex₀ Q w isDel none Tpk pq' c' hInv _ hx

theorem semFwdHookS_preserves_sC_inv {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (L m qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool) (ci? : Option ℕ)
    (Tpk : PublicKey) (pq' : PQ)
    (honestC : Option (SimFig8C Pt)) (c' : SimFig8C Pt)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support
        (semFwdHookS P Dh encPt encT lam T K sh qep B sC₀ ex₀ Q w isDel ci? Tpk pq' honestC c'),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semFwdHookS at hx
  rcases honestC with _ | c
  · exact semFwdAnswerHookS_preserves_sC_inv P Dh encPt encT lam T sh L m qep
      sC₀ ex₀ Q w isDel ci? Tpk pq' c' hInv _ hx
  · dsimp only [] at hx
    split_ifs at hx
    · rcases hev : evalCKS P Dh encPt encT lam T K B sC₀ Q w c c' with _ | r <;>
        simp only [hev] at hx
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
        obtain ⟨_, -, _, rfl, _⟩ := hx; exact hInv
      · exact semResyncHookS_preserves_sC_inv P Dh encPt encT lam T sh L m qep
          sC₀ ex₀ Q w ci? Tpk pq' c r hInv _ hx
    · exact semFwdAnswerHookS_preserves_sC_inv P Dh encPt encT lam T sh L m qep
        sC₀ ex₀ Q w isDel ci? Tpk pq' c' hInv _ hx

theorem semRecvHookS_preserves_sC_inv {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T K : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (L m qep B : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (w : List (BitVec 8)) (isDel : Bool)
    (hInv : SimCStateInv L m sC₀) :
    ∀ x ∈ support (semRecvHookS P Dh encPt encT decT lam T K sh qep B sC₀ ex₀ Q w isDel),
      SimCStateInv L m x.2.1 := by
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semRecvHookS at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win ||
        (isDel && (sC₀.base.mir.inTransit Q.other w).isNone) ||
        (!isDel && ((sC₀.base.mir.inTransit Q.other w).isSome ||
          !(sC₀.base.mir.safeInj 3) || !(ratchetKeyAdmissible P.codec decT encT w)))) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hInv
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hx
    rcases hparse : simParseRecvC P decT (2 ^ 32) (partyEnc Q) (sC₀.base.pq Q) w with
      _ | ⟨pq', i, pk, T?, lct⟩ <;>
      simp only [hparse] at hx
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, _⟩; exact hInv
    · rcases hidx : (sC₀.base.chains Q).findIdx? (fun g => g.key == some pk) with _ | ci <;>
        simp only [hidx] at hx
      · have hInvAmb : SimCStateInv L m
            { sC₀ with base :=
                if inReceiveOnlyEpoch sC₀.base.mir Q ||
                  (Q == CryptoGames.Party.A && (sC₀.base.chains Q).any (·.key.isNone))
                then { sC₀.base with amb := sC₀.base.amb + 1 } else sC₀.base } := by
          refine ⟨?_, hInv.2.1, hInv.2.2⟩
          split_ifs <;> exact hInv.1
        by_cases hc1 :
            ((((sC₀.base.honest.find? fun wc =>
                wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true &&
             (((sC₀.base.honest.find? fun wc =>
                wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
              fun c => decide (c.2.2.2 = lct.2.2)) == some true) = true
        · simp only [hc1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hInv
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hx
          by_cases hz : (T? == some 0) = true
          · simp only [hz, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
            rcases hx with ⟨_, rfl, _⟩; exact hInv
          · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hx
            by_cases hc2 :
                (inReceiveOnlyEpoch sC₀.base.mir Q || decide (25000 < i - 1) ||
                  decide (2 ^ 32 ≤ i)) = true
            · simp only [hc2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
              rcases hx with ⟨_, rfl, _⟩; exact hInvAmb
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hT : T? with _ | T₀ <;>
                simp only [hT] at hx
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
                rcases hx with ⟨_, rfl, _⟩; exact hInvAmb
              · by_cases hev_b :
                    ((((sC₀.base.honest.find? fun wc =>
                        wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)).map
                      fun c => decide (c.1.1 ≠ sC₀.base.mir.epoch Q + 1)) == some true) = true
                · simp only [hev_b, ↓reduceIte] at hx
                  exact semFwdEvictHookS_preserves_sC_inv P Dh encPt encT lam T sh L m qep
                    _ ex₀ Q w isDel pk pq' _ hInvAmb _ hx
                · simp only [hev_b, Bool.false_eq_true, ↓reduceIte] at hx
                  exact semFwdHookS_preserves_sC_inv P Dh encPt encT lam T K sh L m qep B
                    _ ex₀ Q w isDel none pk pq' _ _ hInvAmb _ hx
      · by_cases hrej : ((sC₀.base.chains Q).getD ci ⟨none, 0, 0, []⟩).rejects i = true
        · simp only [hrej, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
          rcases hx with ⟨_, rfl, _⟩; exact hInv
        · simp only [hrej, Bool.false_eq_true, ↓reduceIte] at hx
          exact semFwdHookS_preserves_sC_inv P Dh encPt encT lam T K sh L m qep B
            sC₀ ex₀ Q w isDel (some ci) pk pq' _ _ hInv _ hx

omit [DecidableEq Pt] [Zero Pt] in
theorem semCorrHookTGB_preserves_sC_inv {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (sh : SemHook PQC Pt ℓ T' Ex) (B_skip L m : ℕ)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex) (Q : Party)
    (hInv : SimCStateInv L (m + 1) sC₀) :
    ∀ x ∈ support (semCorrHookTGB P Dh encT sh B_skip sC₀ ex₀ Q),
      SimCStateInv L m x.2.1 := by
  have hInv0 : SimCStateInv L m sC₀ := hInv.mono (Nat.le_succ m)
  rintro ⟨_, sC₁, ex₁⟩ hx
  unfold semCorrHookTGB at hx
  by_cases href :
      (sC₀.base.stopped || sC₀.base.mir.win || !(sC₀.base.mir.corrAllowed Q) ||
       inReceiveOnlyEpoch sC₀.base.mir Q || !(noAliceCorrWhileAliceBelowEpoch10 sC₀.base.mir Q)) = true
  · simp only [href, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    rcases hx with ⟨_, rfl, _⟩; exact hInv0
  · simp only [href, Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hx
    obtain ⟨⟨res, ex'⟩, -, hx⟩ := hx
    rcases res with _ | fig8st <;>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    · rcases hx with ⟨_, rfl, _⟩; exact hInv0
    · rcases hx with ⟨_, rfl, _⟩
      have hchA : ((if Q == CryptoGames.Party.B && sC₀.base.mir.epoch CryptoGames.Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC₀.base.chains CryptoGames.Party.A
              ((sC₀.base.chains CryptoGames.Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC₀.base.chains
        else sC₀.base.chains) .A).length ≤ 5 := by
        split_ifs
        · rcases fig8st.γ with _ | x <;> simp [Function.update, hInv0.1.2.2.2.2.1]
        · exact hInv0.1.2.2.2.2.1
      have hchB : ((if Q == CryptoGames.Party.B && sC₀.base.mir.epoch CryptoGames.Party.B == 0 then
          match fig8st.γ with
          | .exp x => Function.update sC₀.base.chains CryptoGames.Party.A
              ((sC₀.base.chains CryptoGames.Party.A).map fun g =>
                if g.key.isNone then { g with key := some (encT (Dh.dh x Dh.base)) } else g)
          | _ => sC₀.base.chains
        else sC₀.base.chains) .B).length ≤ 5 := by
        split_ifs
        · rcases fig8st.γ with _ | x <;> simp [Function.update, hInv0.1.2.2.2.2.2]
        · exact hInv0.1.2.2.2.2.2
      refine ⟨⟨hInv0.1.1, hInv0.1.2.1, hInv0.1.2.2.1, ?_, hchA, hchB⟩, hInv0.2.1, ?_⟩
      · rcases hInv0.1.2.2.2.1 with ⟨U, hUlen, hCU, htrU⟩
        refine ⟨U, hUlen, ?_, htrU⟩
        dsimp only [afterCorrDedup, CryptoGames.SM.GameState.leak]
        refine countLe_dedupPrepend hCU ?_
        intro x hx
        rcases List.mem_map.mp hx with ⟨r', hr', rfl⟩
        exact htrU r' (List.mem_of_mem_filter hr')
      · simp only [List.length_cons]; have := hInv.2.2; omega

theorem semHandleHookDedupS_preserves_sC_inv {ι : Type} {T' : OracleSpec ι} {Ex : Type}
    (T K B_skip : ℕ) (sh : SemHook PQC Pt ℓ T' Ex) (L m qep B : ℕ)
    (t : (CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ) (ex₀ : Ex)
    (hInv : SimCStateInv L (m + 1) sC₀) :
    ∀ x ∈ support (semHandleHookDedupS P Dh encPt encT decT lam T K B_skip sh qep B t sC₀ ex₀),
      SimCStateInv L m x.2.1 := by
  have hInv0 : SimCStateInv L m sC₀ := hInv.mono (Nat.le_succ m)
  rcases t with ((((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q)
  · exact semSendHook_preserves_sC_inv P Dh encPt encT lam sh L m qep sC₀ ex₀ Q m₀ none r hInv
  · exact semSendHook_preserves_sC_inv P Dh encPt encT lam sh L m qep sC₀ ex₀ Q m₀ (some m₁) r hInv
  · rintro ⟨_, sC₁, ex₁⟩ hx
    unfold semHandleHookDedupS at hx
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
    obtain ⟨⟨rr, sC', ex'⟩, hrec, ex₂, -, _, rfl, rfl⟩ := hx
    exact semRecvHookS_preserves_sC_inv P Dh encPt encT decT lam T K sh L m qep B
      sC₀ ex₀ Q w true hInv0 (rr, sC₁, ex') hrec
  · exact semRecvHookS_preserves_sC_inv P Dh encPt encT decT lam T K sh L m qep B
      sC₀ ex₀ Q w false hInv0
  · exact semCorrHookTGB_preserves_sC_inv P Dh encT sh B_skip L m sC₀ ex₀ Q hInv

end Preservation

end Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
