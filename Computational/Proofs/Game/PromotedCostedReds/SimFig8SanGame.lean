/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
public import Computational.Proofs.Game.PromotedCostedReds.SimFig8LoopAndCost

/-!
# Game-Side Invariants for the `simFig8` Sanitizer Coupling

Defines Fig. 8 party and `Kept` state invariants (`Fig8CkaInv`, `SkippedLenLe`, `Fig8PartyInv`,
`KeptInv`), read-time sanitizer identities, and the real-game invariant `GameSanInv` preserved by
`lFig8` oracle steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame

open OracleSpec OracleComp
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun dhScheme)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState skipKeys fromAEADPRG)
open CryptoGames.Ratchet (RootKey rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  lPubOf lChainPRG lAead lFS lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C fig8Clamp fsClampSim)
open CryptoGames.Ratchet.LibsignalSimC (Kept sentEval predictReceive LibsignalToModularSchemeSimState)
open CryptoGames.SM (GameState RecvResult)
open CryptoGames.SM.Construction (Header PartyState initParty)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec Params)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.SanOracleCore
  (sanRS sanGamma sanAt fig8San fsSan figS fsS)

/-! ## Party and `Kept` invariants -/

section PartyInvariants

/-- Ping-pong CKA state invariant on `Fig8St Pt`: `.pub` before a sending epoch and `.exp` before a
receiving epoch. -/
def Fig8CkaInv {Pt : Type} (st : Fig8St Pt) : Prop :=
  if st.id.sendsIn (st.tcur + 1) then ∃ h, st.γ = .pub h else ∃ x, st.γ = .exp x

def SkippedLenLe (B0 : ℕ) (v : RatchetReceiverState (BitVec 256) (BitVec 256)) : Prop :=
  v.skippedKeys.length ≤ B0

theorem SkippedLenLe.mono {B0 B0' : ℕ} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hle : B0 ≤ B0') (hv : SkippedLenLe B0 v) : SkippedLenLe B0' v :=
  Nat.le_trans hv hle

def Fig8PartyInv {Pt : Type} (B0 : ℕ) (st : Fig8St Pt) : Prop :=
  Fig8CkaInv st ∧ ∀ t v, st.vR t = some v → SkippedLenLe B0 v

theorem Fig8PartyInv.mono {Pt : Type} {B0 B0' : ℕ} {st : Fig8St Pt}
    (hle : B0 ≤ B0') (hst : Fig8PartyInv B0 st) : Fig8PartyInv B0' st :=
  ⟨hst.1, fun t v hv => (hst.2 t v hv).mono hle⟩

def KeptInv {Pt : Type} (B0 : ℕ) (k : Kept Pt) : Prop :=
  (∀ st, k.full = some st → Fig8PartyInv B0 st) ∧
  (∀ t v, k.rs t = some v → SkippedLenLe B0 v)

theorem KeptInv.mono {Pt : Type} {B0 B0' : ℕ} {k : Kept Pt}
    (hle : B0 ≤ B0') (hk : KeptInv B0 k) : KeptInv B0' k :=
  ⟨fun st hst => (hk.1 st hst).mono hle, fun t v hv => (hk.2 t v hv).mono hle⟩

private theorem sendsIn_succ_eq_not (p : Party) (t : ℕ) :
    p.sendsIn (t + 1) = !(p.sendsIn t) := by
  by_cases h : t % 2 = 1
  · have h1 : (t + 1) % 2 = 0 := by omega
    cases p <;> simp only [Party.sendsIn, h, h1] <;> rfl
  · have h0 : t % 2 = 0 := by omega
    have h1 : (t + 1) % 2 = 1 := by omega
    cases p <;> simp only [Party.sendsIn, h0, h1] <;> rfl

private theorem skipKeys_length {CK MK : Type}
    (G : ℕ → PRGScheme CK (CK × MK)) (n : ℕ) (w : CK) (p : ℕ) (acc : List (ℕ × MK)) :
    (skipKeys G n w p acc).2.length = acc.length + n := by
  induction n generalizing w p acc with
  | zero => simp only [skipKeys, Nat.add_zero]
  | succ n ih => simp only [skipKeys, ih, List.length_cons]; omega

theorem skippedLenLe_of_lFS_receive {Pt : Type} {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {B0 : ℕ}
    {v v' : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {a : Header Pt} {c : ℕ × LibsignalCiphertextWithSalt32}
    {i : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (hv : SkippedLenLe B0 v)
    (hrec : (lFS C codec ℓ encT idOf 25000).receive v a c = some (v', i, m)) :
    SkippedLenLe (B0 + 25000) v' := by
  rcases c with ⟨idx, wsc⟩
  dsimp only [lFS, fromAEADPRG, CryptoGames.AEADScheme.movePubPartToAD] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec with hbad
    have hnot : ¬ idx ≤ v.lastIndex ∧ ¬ 25000 < idx - v.lastIndex - 1 := not_or.mp hbad
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec
          ((lChainPRG C.F (idx - 1)).gen
            (skipKeys (lChainPRG C.F) (idx - v.lastIndex - 1)
              v.chainKey v.lastIndex v.skippedKeys).1).2
          ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl⟩
        unfold SkippedLenLe at hv ⊢
        dsimp only
        rw [skipKeys_length]
        omega
  · rw [hlk] at hrec
    dsimp only at hrec
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec key ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl⟩
        unfold SkippedLenLe at hv ⊢
        exact Nat.le_trans (List.length_filter_le _ _) (by omega)

theorem fig8PartyInv_init {Pt : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (P : Party) (k : BitVec 256 × BitVec 256) :
    Fig8PartyInv 0
      (initParty (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf 25000)
        lam P k) := by
  refine ⟨?_, ?_⟩
  · cases P <;> simp [Fig8CkaInv, initParty, Party.sendsIn, dhScheme]
  · intro t v hv
    cases P
    · simp only [initParty] at hv
      split_ifs at hv with ht
      · simp only [Option.some.injEq] at hv; subst hv
        simp [SkippedLenLe, lFS, fromAEADPRG]
    · simp [initParty] at hv

theorem fig8PartyInv_initA {Pt : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (k : BitVec 256 × BitVec 256) :
    Fig8PartyInv 0 ((lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).initA k) :=
  fig8PartyInv_init Dh encPt C codec ℓ encT idOf lam .A k

theorem fig8PartyInv_initB {Pt : Type} [Zero Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (k : BitVec 256 × BitVec 256) :
    Fig8PartyInv 0 ((lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).initB k) :=
  fig8PartyInv_init Dh encPt C codec ℓ encT idOf lam .B k

theorem fig8PartyInv_send {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {st : Fig8St Pt} (hst : Fig8PartyInv B0 st)
    (m : LibsignalMsgPublicPart × Plain ℓ) (r : BitVec 256) :
    Fig8PartyInv B0
      ((lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send st m r).1 := by
  rcases hst with ⟨hcka, hvr⟩
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · unfold Fig8CkaInv at hcka
    simp only [hs, ↓reduceIte] at hcka
    rcases hcka with ⟨h, hγ⟩
    simp only [hs, ↓reduceIte, hγ, dhScheme]
    have hs2 : st.id.sendsIn (st.tcur + 1 + 1) = false := by
      rw [sendsIn_succ_eq_not, hs]; rfl
    refine ⟨?_, hvr⟩
    simp [Fig8CkaInv, hs2]
  · have hs0 : st.id.sendsIn (st.tcur + 1) = false := Bool.eq_false_iff.mpr hs
    simp only [hs0, Bool.false_eq_true, ↓reduceIte]
    cases st.vS <;> exact ⟨hcka, hvr⟩

theorem fig8PartyInv_receive {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {st st' : Fig8St Pt} {c : Fig8C Pt} {t i : ℕ}
    {m : LibsignalMsgPublicPart × Plain ℓ}
    (hst : Fig8PartyInv B0 st)
    (hrec : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c =
      some (st', t, i, m)) :
    Fig8PartyInv (B0 + 25000) st' := by
  rcases hst with ⟨hcka, hvr⟩
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at hrec
  by_cases hbad : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · simp [hbad] at hrec
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hrec
    have hbad' : st.id.sendsIn c.1.1 = false ∧ ¬ st.tcur + 1 < c.1.1 := by
      simpa [Bool.or_eq_true] using hbad
    by_cases heq : c.1.1 = st.tcur + 1
    · simp only [heq, ↓reduceIte] at hrec
      rcases hc2 : c.1.2 with _ | Tn
      · rw [hc2] at hrec; cases hrec
      · rw [hc2] at hrec
        unfold Fig8CkaInv at hcka
        have hs0 : st.id.sendsIn (st.tcur + 1) = false := by rw [← heq]; exact hbad'.1
        simp only [hs0, Bool.false_eq_true, ↓reduceIte] at hcka
        rcases hcka with ⟨x, hγ⟩
        simp only [hγ, dhScheme, Function.update_self] at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive
            ((lFS C codec ℓ encT idOf 25000).initReceiver
              ((rootPRNG C.F encPt).up st.root (Dh.dh x Tn)).2)
            c.1 c.2 with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          have hs2 : st.id.sendsIn (st.tcur + 1 + 1) = true := by
            rw [sendsIn_succ_eq_not, hs0]; rfl
          refine ⟨by simp [Fig8CkaInv, hs2], ?_⟩
          intro t' v0 hv0
          dsimp only at hv0
          by_cases ht' : t' = st.tcur + 1
          · subst ht'
            simp only [Function.update_self, Option.some.injEq] at hv0; subst hv0
            have hinit : SkippedLenLe B0
                ((lFS C codec ℓ encT idOf 25000).initReceiver
                  ((rootPRNG C.F encPt).up st.root (Dh.dh x Tn)).2) := by
              simp [SkippedLenLe, lFS, fromAEADPRG]
            exact skippedLenLe_of_lFS_receive hinit hfs
          · simp only [Function.update_of_ne ht'] at hv0
            exact (hvr t' v0 hv0).mono (by omega)
    · simp only [heq, ↓reduceIte] at hrec
      rcases hvt : st.vR c.1.1 with _ | v
      · rw [hvt] at hrec; cases hrec
      · rw [hvt] at hrec
        dsimp only at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2
            with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨hcka, ?_⟩
          intro t' v0 hv0
          dsimp only at hv0
          by_cases ht' : t' = c.1.1
          · subst ht'
            simp only [Function.update_self, Option.some.injEq] at hv0; subst hv0
            exact skippedLenLe_of_lFS_receive (hvr c.1.1 v hvt) hfs
          · simp only [Function.update_of_ne ht'] at hv0
            exact (hvr t' v0 hv0).mono (by omega)

theorem keptInv_unknown {Pt : Type} (B0 : ℕ) : KeptInv B0 (Kept.unknown (Pt := Pt)) :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem keptInv_ofSt {Pt : Type} {B0 : ℕ} {st : Fig8St Pt} (hst : Fig8PartyInv B0 st) :
    KeptInv B0 (Kept.ofSt st) :=
  ⟨fun _ h => Option.some.inj h ▸ hst, hst.2⟩

theorem keptInv_send {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {k : Kept Pt} (hk : KeptInv B0 k) :
    KeptInv B0
      (Kept.send (ℓ := ℓ) (fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) k) := by
  unfold Kept.send
  rcases hfull : k.full with _ | st
  · exact hk
  · dsimp only
    have hst := hk.1 st hfull
    split_ifs with hs
    · exact ⟨fun _ h => (nomatch h), hst.2⟩
    · exact ⟨fun _ h => Option.some.inj h ▸ fig8PartyInv_send hst _ _, hk.2⟩

theorem keptInv_recv {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {B0 : ℕ} {c : Fig8C Pt} {k : Kept Pt} (hk : KeptInv B0 k) :
    KeptInv (B0 + 25000)
      (Kept.recv (fig := lFig8 Dh encPt C codec ℓ encT idOf 25000 lam)
        (fs := lFS C codec ℓ encT idOf 25000) c k) := by
  unfold Kept.recv
  rcases hfull : k.full with _ | st
  · dsimp only
    refine ⟨fun _ h => (nomatch h), ?_⟩
    intro t' v0 hv0
    dsimp only at hv0
    by_cases ht' : t' = c.1.1
    · subst ht'
      simp only [Function.update_self] at hv0
      rcases hrs : k.rs c.1.1 with _ | v
      · simp [hrs] at hv0
      · rw [hrs] at hv0
        dsimp only [Option.bind] at hv0
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2
            with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hv0; cases hv0
        · simp only [hfs, Option.map_some, Option.some.injEq] at hv0; subst hv0
          exact skippedLenLe_of_lFS_receive (hk.2 c.1.1 v hrs) hfs
    · simp only [Function.update_of_ne ht'] at hv0
      exact (hk.2 t' v0 hv0).mono (by omega)
  · dsimp only
    have hst := hk.1 st hfull
    rcases hrec : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c
        with _ | ⟨st', t, i, pm⟩
    · dsimp only
      exact ⟨fun _ h => (nomatch h), fun t' v hv => (hst.2 t' v hv).mono (by omega)⟩
    · dsimp only
      exact ⟨fun _ h => Option.some.inj h ▸ fig8PartyInv_receive hst hrec,
        fun t' v hv => (hk.2 t' v hv).mono (by omega)⟩

end PartyInvariants

/-! ## Read-time sanitizer identities -/

section SanIdentities

theorem sanRS_eq_self {B0 T : ℕ} {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hle : B0 ≤ T) (hv : SkippedLenLe B0 v) : sanRS T v = v := by
  cases v
  simp only [sanRS, List.take_of_length_le (Nat.le_trans hv hle)]

theorem sanRS_nil (T : ℕ) (ck : BitVec 256) (idx : ℕ) :
    sanRS T ⟨ck, idx, []⟩ = ⟨ck, idx, []⟩ := by
  simp [sanRS]

theorem sanGamma_eq_self {Pt : Type} [Zero Pt] (lam : Pt) {st : Fig8St Pt}
    (hcka : Fig8CkaInv st) : sanGamma lam st = st.γ := by
  unfold Fig8CkaInv at hcka
  unfold sanGamma
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte] at hcka ⊢
    rcases hcka with ⟨h, hγ⟩
    simp [hγ]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hcka ⊢
    rcases hcka with ⟨x, hγ⟩
    simp [hγ]

theorem sanAt_eq_self {Pt : Type} [Zero Pt] {B0 T : ℕ} (lam : Pt) (t : ℕ) {st : Fig8St Pt}
    (hle : B0 ≤ T) (hst : Fig8PartyInv B0 st) : sanAt T lam t st = st := by
  have hγ := sanGamma_eq_self lam hst.1
  have hvR : (fun j => if j = t then (st.vR t).map (sanRS T) else st.vR j) = st.vR := by
    funext j
    split_ifs with hj
    · subst hj
      rcases hv : st.vR j with _ | v
      · rfl
      · simp [sanRS_eq_self hle (hst.2 j v hv)]
    · rfl
  cases st
  dsimp only [sanAt] at hvR hγ ⊢
  rw [hvR, hγ]

theorem fig8San_receive_eq {Pt Key M Coins : Type} [Zero Pt] {B0 T : ℕ} (lam : Pt)
    (fig : CryptoGames.SMScheme Key (Fig8St Pt) M Coins (Fig8C Pt))
    {st : Fig8St Pt} (hle : B0 ≤ T) (hst : Fig8PartyInv B0 st) (c : Fig8C Pt) :
    (fig8San T lam fig).receive st c = fig.receive st c := by
  simp only [fig8San, sanAt_eq_self lam c.1.1 hle hst]

theorem fsSan_receive_eq {SS AD M C : Type} {B0 T : ℕ}
    (fs : CryptoGames.FSAEADScheme (BitVec 256) SS
      (RatchetReceiverState (BitVec 256) (BitVec 256)) AD M C)
    {v : RatchetReceiverState (BitVec 256) (BitVec 256)}
    (hle : B0 ≤ T) (hv : SkippedLenLe B0 v) (h : AD) (c : C) :
    (fsSan T fs).receive v h c = fs.receive v h c := by
  simp only [fsSan, sanRS_eq_self hle hv]

theorem kept_recv_congr_of_inv {Pt : Type} {ℓ B0 : ℕ}
    {fig₁ fig₂ : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {fs₁ fs₂ : CryptoGames.FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (hfig : ∀ st c, Fig8PartyInv B0 st → fig₁.receive st c = fig₂.receive st c)
    (hfs : ∀ v h c, SkippedLenLe B0 v → fs₁.receive v h c = fs₂.receive v h c)
    (c : Fig8C Pt) {k : Kept Pt} (hk : KeptInv B0 k) :
    Kept.recv (ℓ := ℓ) (fig := fig₁) (fs := fs₁) c k =
      Kept.recv (ℓ := ℓ) (fig := fig₂) (fs := fs₂) c k := by
  unfold Kept.recv
  rcases hfull : k.full with _ | st
  · dsimp only
    congr 1; funext j
    by_cases hj : j = c.1.1
    · subst hj
      simp only [Function.update_self]
      rcases hrs : k.rs c.1.1 with _ | v
      · rfl
      · simp only [Option.bind_some, hfs v c.1 c.2 (hk.2 c.1.1 v hrs)]
    · simp only [Function.update_of_ne hj]
  · dsimp only
    rw [hfig st c (hk.1 st hfull)]

theorem kept_eval_congr_of_inv {Pt : Type} {ℓ B0 : ℕ}
    {fig₁ fig₂ : CryptoGames.SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)}
    {fs₁ fs₂ : CryptoGames.FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (hfig : ∀ st c, Fig8PartyInv B0 st → fig₁.receive st c = fig₂.receive st c)
    (hfs : ∀ v h c, SkippedLenLe B0 v → fs₁.receive v h c = fs₂.receive v h c)
    (c : Fig8C Pt) {k : Kept Pt} (hk : KeptInv B0 k) :
    Kept.eval (ℓ := ℓ) (fig := fig₁) (fs := fs₁) c k =
      Kept.eval (ℓ := ℓ) (fig := fig₂) (fs := fs₂) c k := by
  unfold Kept.eval
  rcases hfull : k.full with _ | st
  · dsimp only
    rcases hrs : k.rs c.1.1 with _ | v
    · rfl
    · simp only [Option.map_some, hfs v c.1 c.2 (hk.2 c.1.1 v hrs)]
  · dsimp only
    rw [hfig st c (hk.1 st hfull)]

theorem sentEval_congr_of_nil {Pt : Type} [DecidableEq Pt] {ℓ : ℕ}
    {fs₁ fs₂ : CryptoGames.FSAEADScheme (BitVec 256) (RatchetSenderState (BitVec 256))
      (RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)}
    (hfs : ∀ ck idx h c, fs₁.receive ⟨ck, idx, []⟩ h c = fs₂.receive ⟨ck, idx, []⟩ h c)
    (sent : List (Fig8C Pt × RatchetSenderState (BitVec 256))) (c c' : Fig8C Pt) :
    sentEval (ℓ := ℓ) (fs := fs₁) sent c c' =
      sentEval (ℓ := ℓ) (fs := fs₂) sent c c' := by
  unfold sentEval
  congr 1; funext e
  rw [hfs e.2.chainKey e.2.lastIndex c'.1 c'.2]

theorem kept_recv_figS_eq {PQ PQC Pt : Type} [Zero Pt] {ℓ B0 T : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (hle : B0 ≤ T) (c : Fig8C Pt) {k : Kept Pt} (hk : KeptInv B0 k) :
    Kept.recv (ℓ := ℓ) (fig := figS (ℓ := ℓ) P Dh encPt encT lam T)
        (fs := fsS (ℓ := ℓ) P encT T) c k =
      Kept.recv (ℓ := ℓ)
        (fig := lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam)
        (fs := lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000) c k :=
  kept_recv_congr_of_inv
    (fun _ c₀ hst => fig8San_receive_eq lam _ hle hst c₀)
    (fun _ h₀ c₀ hv => fsSan_receive_eq _ hle hv h₀ c₀)
    c hk

theorem predictReceive_fig8Clamp_figS_eq {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt]
    {ℓ B B0 T : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    (hle : B0 ≤ T) {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {Q : Party}
    (hk : KeptInv B0 (sC.kept Q)) (c c' : Fig8C Pt) :
    predictReceive (fig := fig8Clamp B (figS (ℓ := ℓ) P Dh encPt encT lam T))
        (fs := fsClampSim B (fsS (ℓ := ℓ) P encT T)) sC Q c c' =
      predictReceive
        (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000)) sC Q c c' := by
  unfold predictReceive
  have hke :
      Kept.eval (fig := fig8Clamp B (figS (ℓ := ℓ) P Dh encPt encT lam T))
        (fs := fsClampSim B (fsS (ℓ := ℓ) P encT T)) c' (sC.kept Q) =
      Kept.eval
        (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
        (fs := fsClampSim B (lFS P.C P.codec ℓ encT
          (fun R => if R == Party.A then P.idA else P.idB) 25000)) c' (sC.kept Q) :=
    kept_eval_congr_of_inv
      (fun st c₀ hst => by
        dsimp only [fig8Clamp, figS]
        rw [fig8San_receive_eq lam _ hle hst c₀])
      (fun v h₀ c₀ hv => by
        dsimp only [fsClampSim, fsS]
        rw [fsSan_receive_eq _ hle hv h₀ c₀])
      c' hk
  rw [hke]
  rcases Kept.eval
      (fig := fig8Clamp B (lFig8 Dh encPt P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000 lam))
      (fs := fsClampSim B (lFS P.C P.codec ℓ encT
        (fun R => if R == Party.A then P.idA else P.idB) 25000)) c' (sC.kept Q) with _ | r
  · exact sentEval_congr_of_nil
      (fun ck idx h₀ c₀ => by
        simp only [fsClampSim, fsS, fsSan, sanRS_nil])
      sC.sent c c'
  · rfl

end SanIdentities

/-! ## Real-game invariant `GameSanInv` -/

section GameInvariant

theorem lFig8_send_vS_and_idx {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {Bvs : ℕ} {st : Fig8St Pt}
    (hvs : ∀ vs, st.vS = some vs → vs.lastIndex ≤ Bvs)
    (m : LibsignalMsgPublicPart × Plain ℓ) (r : BitVec 256) :
    let out := (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send st m r
    (∀ vs', out.1.vS = some vs' → vs'.lastIndex ≤ Bvs + 1) ∧ out.2.2.1 ≤ Bvs + 1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.send,
    lFS, fromAEADPRG]
  by_cases hs : st.id.sendsIn (st.tcur + 1) = true
  · simp only [hs, ↓reduceIte]
    refine ⟨?_, by omega⟩
    intro vs' hvs'
    simp only [Option.some.injEq] at hvs'
    subst hvs'
    dsimp only
    omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    rcases hst : st.vS with _ | v
    · simp only [hst]
      refine ⟨(fun _ h => by cases h), ?_⟩
      change 0 ≤ Bvs + 1
      omega
    · have hvle := hvs v hst
      refine ⟨?_, ?_⟩
      · intro vs' hvs'
        simp only [Option.some.injEq] at hvs'
        subst hvs'
        dsimp only
        omega
      · dsimp only
        omega

private theorem lFS_receive_idx_eq {Pt : Type} {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {v v' : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {a : Header Pt} {c : ℕ × LibsignalCiphertextWithSalt32}
    {i : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (hrec : (lFS C codec ℓ encT idOf 25000).receive v a c = some (v', i, m)) :
    i = c.1 := by
  rcases c with ⟨idx, wsc⟩
  dsimp only [lFS, fromAEADPRG, CryptoGames.AEADScheme.movePubPartToAD] at hrec
  rcases hlk : v.skippedKeys.lookup idx with _ | key
  · rw [hlk] at hrec
    split_ifs at hrec
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec _ ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        exact hrec.2.1.symm
  · rw [hlk] at hrec
    dsimp only at hrec
    rcases hpub : lPubOf codec wsc with _ | pub
    · rw [hpub] at hrec; cases hrec
    · rw [hpub] at hrec
      dsimp only at hrec
      rcases hdec : (lAead C codec ℓ encT idOf).dec key ((idx, a), pub) wsc with _ | pm
      · rw [hdec] at hrec; cases hrec
      · rw [hdec] at hrec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
        exact hrec.2.1.symm

theorem lFig8_receive_vS_and_idx {Pt : Type} [Zero Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {st st' : Fig8St Pt} {c : Fig8C Pt} {t i : ℕ}
    {m : LibsignalMsgPublicPart × Plain ℓ}
    (hrec : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive st c =
      some (st', t, i, m)) :
    st'.vS = st.vS ∧ i = c.2.1 := by
  dsimp only [lFig8, CryptoGames.SM.Construction.scheme, CryptoGames.SM.Construction.receive] at hrec
  by_cases hbad : (st.id.sendsIn c.1.1 || decide (st.tcur + 1 < c.1.1)) = true
  · simp [hbad] at hrec
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hrec
    by_cases heq : c.1.1 = st.tcur + 1
    · simp only [heq, ↓reduceIte] at hrec
      rcases hc2 : c.1.2 with _ | Tn
      · rw [hc2] at hrec; cases hrec
      · rw [hc2] at hrec
        dsimp only at hrec
        simp only [Function.update_self] at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive _ c.1 c.2 with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, lFS_receive_idx_eq hfs⟩
    · simp only [heq, ↓reduceIte] at hrec
      rcases hvt : st.vR c.1.1 with _ | v
      · rw [hvt] at hrec; cases hrec
      · rw [hvt] at hrec
        dsimp only at hrec
        rcases hfs : (lFS C codec ℓ encT idOf 25000).receive v c.1 c.2 with _ | ⟨v', idx, pm⟩
        · rw [hfs] at hrec; cases hrec
        · rw [hfs] at hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrec
          rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, lFS_receive_idx_eq hfs⟩

/-- Real-game state invariant at total query budget `q` with `m` remaining queries:
`m ≤ q`, each party satisfies `Fig8PartyInv (25000 * (q - m))`, and any active sender FS session
has `lastIndex ≤ q - m`. -/
structure GameSanInv {Pt : Type} {ℓ : ℕ} (q m : ℕ)
    (gs : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) : Prop where
  hm : m ≤ q
  hparty : ∀ Q : Party, Fig8PartyInv (25000 * (q - m)) (gs.st Q)
  hvs : ∀ Q : Party, ∀ vs, (gs.st Q).vS = some vs → vs.lastIndex ≤ q - m

theorem GameSanInv.mono {Pt : Type} {ℓ q m₁ m₂ : ℕ}
    {gs : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hle : m₁ ≤ m₂) (h : GameSanInv q m₂ gs) : GameSanInv q m₁ gs where
  hm := Nat.le_trans hle h.hm
  hparty Q := (h.hparty Q).mono (Nat.mul_le_mul_left 25000 (by omega))
  hvs Q vs hv := Nat.le_trans (h.hvs Q vs hv) (by omega)

theorem gameSanInv_init {Pt : Type} [Zero Pt] {ℓ : ℕ}
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto)
    (codec : SignalMessageProtoCodec) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (q : ℕ) (k : BitVec 256 × BitVec 256) (b : Bool) :
    GameSanInv (Pt := Pt) (ℓ := ℓ) q q
      (CryptoGames.SM.initState (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) k b) where
  hm := le_rfl
  hparty Q := by
    simp only [Nat.sub_self, Nat.mul_zero, CryptoGames.SM.initState]
    cases Q
    · exact fig8PartyInv_initA Dh encPt C codec ℓ encT idOf lam k
    · exact fig8PartyInv_initB Dh encPt C codec ℓ encT idOf lam k
  hvs Q vs hv := by
    simp only [Nat.sub_self]
    dsimp only [CryptoGames.SM.initState, lFig8, CryptoGames.SM.Construction.scheme,
      initParty, lFS, fromAEADPRG] at hv
    cases Q
    · cases hv
    · simp only [Option.some.injEq] at hv
      subst hv
      rfl

private theorem epMgmt_st_eq {St Msg C : Type}
    {gs s₁ : GameState St Msg C} {Δ qep : ℕ} {Q : Party} {bad : Bool}
    (h : gs.epMgmt Δ qep Q bad = some s₁) : s₁.st = gs.st := by
  unfold GameState.epMgmt at h
  split_ifs at h <;> injection h with h <;> subst h <;> rfl

private theorem stateT_liftProb_run {σ α : Type} (p : ProbComp α) (s : σ) :
    (liftM p : StateT σ ProbComp α).run s = (p >>= fun a => pure (a, s)) := rfl

private theorem gameSanInv_record {Pt : Type} [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ}
    {gs s₁ : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {bad isChall : Bool}
    (msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256)
    (hInv : GameSanInv q (m + 1) gs)
    (hep : gs.epMgmt 3 (qep + 1) Q bad = some s₁) :
    let out := (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).send (s₁.st Q) msg coins
    GameSanInv q m
      (s₁.record 3 Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, msg, out.2⟩ isChall) ∧
      out.2.2.1 ≤ q - m := by
  have hst := epMgmt_st_eq hep
  have hm1 : m + 1 ≤ q := hInv.hm
  have hInv0 := hInv.mono (Nat.le_succ m)
  have hsub : (q - (m + 1)) + 1 = q - m := by omega
  have hvsQ : ∀ vs, (s₁.st Q).vS = some vs → vs.lastIndex ≤ q - (m + 1) := by
    rw [hst]; exact hInv.hvs Q
  have hsend := lFig8_send_vS_and_idx (Dh := Dh) (encPt := encPt) (C := C) (codec := codec)
    (ℓ := ℓ) (encT := encT) (idOf := idOf) (lam := lam) hvsQ msg coins
  refine ⟨{
    hm := hInv0.hm
    hparty := fun R => by
      dsimp only [GameState.record]
      by_cases hR : R = Q
      · subst hR
        simp only [Function.update_self]
        have hpQ : Fig8PartyInv (25000 * (q - (m + 1))) (s₁.st R) := by
          rw [hst]; exact hInv.hparty R
        exact (fig8PartyInv_send hpQ msg coins).mono (Nat.mul_le_mul_left 25000 (by omega))
      · simp only [Function.update_of_ne hR, hst]; exact hInv0.hparty R
    hvs := fun R vs hv => by
      dsimp only [GameState.record] at hv
      by_cases hR : R = Q
      · subst hR
        simp only [Function.update_self] at hv
        exact (hsend.1 vs hv).trans_eq hsub
      · simp only [Function.update_of_ne hR, hst] at hv; exact hInv0.hvs R vs hv },
    hsend.2.trans_eq hsub⟩

private theorem gameSanInv_accept {Pt : Type} [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m : ℕ}
    {gs : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {c : Fig8C Pt} {st' : Fig8St Pt} {t i : ℕ}
    {pm : LibsignalMsgPublicPart × Plain ℓ} (pos : CryptoGames.SM.Pos)
    (hInv : GameSanInv q (m + 1) gs)
    (hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c =
      some (st', t, i, pm)) :
    GameSanInv q m (gs.accept Q st' pos) ∧ i = c.2.1 := by
  have hm1 : m + 1 ≤ q := hInv.hm
  have hInv0 := hInv.mono (Nat.le_succ m)
  obtain ⟨hvS_eq, hi_eq⟩ := lFig8_receive_vS_and_idx hrcv
  refine ⟨{
    hm := hInv0.hm
    hparty := fun R => by
      dsimp only [GameState.accept, GameState.delete]
      by_cases hR : R = Q
      · subst hR
        simp only [Function.update_self]
        exact (fig8PartyInv_receive (hInv.hparty R) hrcv).mono (by omega)
      · simp only [Function.update_of_ne hR]; exact hInv0.hparty R
    hvs := fun R vs hv => by
      dsimp only [GameState.accept, GameState.delete] at hv
      by_cases hR : R = Q
      · subst hR
        simp only [Function.update_self, hvS_eq] at hv
        exact hInv0.hvs R vs hv
      · simp only [Function.update_of_ne hR] at hv
        exact hInv0.hvs R vs hv }, hi_eq⟩

theorem gameSanInv_transmitImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {msg : LibsignalMsgPublicPart × Plain ℓ} {rc : Option (BitVec 256)}
    {res : Option (Fig8C Pt)}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.transmitImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 (qep + 1) (Q, msg, rc)).run gs)) :
    GameSanInv q m gs' ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  unfold CryptoGames.SM.transmitImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;>
      simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    · rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
    · rcases hmem with ⟨rfl, rfl⟩
      have hrec := gameSanInv_record (Dh := Dh) (encPt := encPt) (C := C) (codec := codec)
        (encT := encT) (idOf := idOf) (lam := lam) (isChall := false) msg coins hInv hep
      exact ⟨hrec.1, fun _ hc => Option.some.inj hc ▸ hrec.2⟩

theorem gameSanInv_challImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ}
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {m₀ m₁ : LibsignalMsgPublicPart × Plain ℓ} {rc : Option (BitVec 256)}
    {res : Option (Fig8C Pt)}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.challImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 (qep + 1) cfg (Q, m₀, m₁, rc)).run gs)) :
    GameSanInv q m gs' ∧ ∀ c, res = some c → c.2.1 ≤ q - m := by
  unfold CryptoGames.SM.challImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      stateT_liftProb_run, pure_bind, bind_assoc, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, bad⟩, -, hmem⟩ := hmem
    rcases hep : gs.epMgmt 3 (qep + 1) Q bad with _ | s₁ <;> simp only [hep] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
    · by_cases hch : (!(s₁.safeCh 3 Q) || !(cfg.challAllowedIn (s₁.epoch Q))) = true
      · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hInv.mono (Nat.le_succ m), fun _ hc => nomatch hc⟩
      · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        have hrec := gameSanInv_record (Dh := Dh) (encPt := encPt) (C := C) (codec := codec)
          (encT := encT) (idOf := idOf) (lam := lam) (isChall := true)
          ((cfg.challMsg (s₁.epoch Q)).getD (if gs.b then m₁ else m₀)) coins hInv hep
        exact ⟨hrec.1, fun _ hc => Option.some.inj hc ▸ hrec.2⟩

theorem gameSanInv_deliverImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m : ℕ}
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {c : Fig8C Pt}
    {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.deliverImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) cfg (Q, c)).run gs)) :
    GameSanInv q m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold CryptoGames.SM.deliverImpl at hmem
  by_cases hw : gs.win = true
  · simp only [hw, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      at hmem
    rcases htr : gs.inTransit Q.other c with _ | r <;> simp only [htr] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
    · rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
        _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
      · split_ifs at hmem <;>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
          rcases hmem with ⟨rfl, rfl⟩ <;>
          exact ⟨⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩, fun _ _ _ hc => nomatch hc⟩
      · obtain ⟨hacc, hi_eq⟩ := gameSanInv_accept r.pos hInv hrcv
        by_cases hbad :
            (cfg.deliverWin &&
              gs.mustBeCorrect (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).maxSkip Q r &&
              !decide (t' = r.pos.epoch ∧ i' = r.pos.idx ∧ m' = r.msg)) = true
        · simp only [hbad, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          exact ⟨⟨hacc.hm, hacc.hparty, hacc.hvs⟩, fun _ _ _ hc => by
            injection hc with hc; injection hc with _ hi _; exact hi.symm.trans hi_eq⟩
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          exact ⟨hacc, fun _ _ _ hc => by
            injection hc with hc; injection hc with _ hi _; exact hi.symm.trans hi_eq⟩

theorem gameSanInv_injectImpl {Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes} {C : Crypto}
    {codec : SignalMessageProtoCodec} {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {lam : Pt} {q m qep : ℕ}
    {cfg : CryptoGames.SM.Config (LibsignalMsgPublicPart × Plain ℓ)}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {c : Fig8C Pt}
    {res : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ))}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.injectImpl
      (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam) 3 qep cfg (Q, c)).run gs)) :
    GameSanInv q m gs' ∧ ∀ t i pm, res = some (.accepted t i pm) → i = c.2.1 := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold CryptoGames.SM.injectImpl at hmem
  by_cases href : (gs.win || (gs.inTransit Q.other c).isSome || !(gs.safeInj 3)) = true
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      at hmem
    rcases hrcv : (lFig8 Dh encPt C codec ℓ encT idOf 25000 lam).receive (gs.st Q) c with
      _ | ⟨st', t', i', m'⟩ <;> simp only [hrcv] at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
    · by_cases hcap : qep + 1 < t'
      · simp only [hcap, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨hInv0, fun _ _ _ hc => nomatch hc⟩
      · simp only [hcap, ↓reduceIte] at hmem
        by_cases htriv : gs.trivial 3 ⟨Q.other, t', i'⟩ = true
        · simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          obtain ⟨hacc, hi_eq⟩ := gameSanInv_accept ⟨Q.other, t', i'⟩ hInv hrcv
          exact ⟨hacc, fun _ _ _ hc => by
            injection hc with hc; injection hc with _ hi _; exact hi.symm.trans hi_eq⟩
        · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
          split_ifs at hmem <;>
            simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem <;>
            rcases hmem with ⟨rfl, rfl⟩ <;>
            exact ⟨⟨hInv0.hm, hInv0.hparty, hInv0.hvs⟩, fun _ _ _ hc => nomatch hc⟩

theorem gameSanInv_corrImpl {Pt : Type} [DecidableEq Pt] {ℓ : ℕ} {q m : ℕ}
    {gs gs' : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {Q : Party} {res : Option (Fig8St Pt)}
    (hInv : GameSanInv q (m + 1) gs)
    (hmem : (res, gs') ∈ support ((CryptoGames.SM.corrImpl Q).run gs)) :
    GameSanInv q m gs' ∧ ∀ fig8st, res = some fig8st → fig8st = gs.st Q := by
  have hInv0 := hInv.mono (Nat.le_succ m)
  unfold CryptoGames.SM.corrImpl at hmem
  by_cases href : (gs.win || !(gs.corrAllowed Q)) = true
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hInv0, fun _ hc => nomatch hc⟩
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    have hst : (gs.afterCorr Q).st = gs.st := rfl
    exact ⟨⟨hInv0.hm, fun R => hst ▸ hInv0.hparty R, fun R => hst ▸ hInv0.hvs R⟩,
      fun _ hc => (Option.some.inj hc).symm⟩

end GameInvariant

end Computational.Proofs.Game.PromotedCostedReds.SimFig8SanGame
