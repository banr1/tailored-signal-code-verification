/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.StepDeliverInject
import ProofLib.SepLogic.WP.StateNorm
import LibsignalBinary.Proofs.SpqrV1Sync.NoWrongSalt -- shake: keep

/-!
# Evicted salt-mismatch probe: bound and reduction

**Checked by Lean.** Connects the evicted salt-mismatch probe branch (`DeliverProbe`) to the SPQR salt-provenance invariants, the `DeliverForge` reduction, and the `spuriousStepTerm` coin-draw bound when `Q.other` is corrupted after the draw.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

/-! ## No-wrong-salt invariants -/

/-- Every honest wire sent by `Q.other` yields its own effective salt upon successful `P.spqr.recv`. -/
def NoWrongSaltOnHonestWire {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) : Prop :=
  ∀ w c h body pq' salt,
    (w, c) ∈ sC.base.honest →
    Party.senderOf c.1.1 = Q.other →
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
    P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt) →
    c.2.2.2 = effectiveHkdfSalt32 salt

/-- Restriction of `NoWrongSaltOnHonestWire` to honest wires of an evicted epoch. -/
def NoWrongSaltOnEvictedWire {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) : Prop :=
  ∀ w c h body pq' salt,
    (w, c) ∈ sC.base.honest →
    Party.senderOf c.1.1 = Q.other →
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
    (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none →
    c.1.1 ≠ sC.base.mir.epoch Q + 1 →
    P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt) →
    c.2.2.2 = effectiveHkdfSalt32 salt

theorem noWrongSaltOnEvictedWire_of_noWrongSaltOnHonestWire {Pt PQ PQC : Type} {ℓ : ℕ}
    {P : Params PQ PQC} {sC : LibsignalToModularSchemeSimState PQ Pt ℓ} {Q : Party}
    (hno : NoWrongSaltOnHonestWire P sC Q) :
    NoWrongSaltOnEvictedWire P sC Q :=
  fun w c h body pq' salt hc_mem hc_sender hparse _ _ hspqr =>
    hno w c h body pq' salt hc_mem hc_sender hparse hspqr

/-- Under `NoWrongSaltOnEvictedWire`, `simRecvStepC` on an evicted honest wire rejects without modifying state or the probe flag. -/
theorem simRecvStepC_deliver_evicted_of_noWrongSalt
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl : Bool)
    (hno : NoWrongSaltOnEvictedWire P sC Q)
    (hstop : sC.base.stopped = false)
    (hwin_mir : sC.base.mir.win = false)
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : sC.base.mir.inTransit Q.other w = some r_mir)
    (c : Fig8C Pt) (hc_mem : (w, c) ∈ sC.base.honest)
    (hc_sender : Party.senderOf c.1.1 = Q.other)
    (hhonC :
      (sC.base.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) =
        some c)
    (hlen : ¬ w.length < 9)
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (haddrs : addressCheckPasses h.addresses (P.expectedAddrs Q) = true)
    {pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv (sC.base.pq Q) h.pqRatchet = .ok (pq', salt))
    (hpan : P.spqr.recvPanics (sC.base.pq Q) h.pqRatchet = false)
    (hfind : (sC.base.chains Q).findIdx? (fun g => g.key == some h.senderRatchetKey) = none)
    (hepoch : c.1.1 ≠ sC.base.mir.epoch Q + 1) :
    simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, s_fig8, fl) =
      (some .rejected, (sC, s_fig8, fl)) := by
  have hsalt : c.2.2.2 = effectiveHkdfSalt32 salt :=
    hno w c h body pq' salt hc_mem hc_sender hparse hfind hepoch hspqr
  have hfind_hon :
      sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) =
        some (w, c) := by
    cases hf : sC.base.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
    | none => rw [hf] at hhonC; cases hhonC
    | some wc =>
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      rw [hf, Option.map_some] at hhonC
      have hc2 : wc.2 = c := Option.some.inj hhonC
      rcases wc with ⟨w', c'⟩
      dsimp only at hp hc2
      rw [hp.1, hc2]
  unfold simRecvStepC simRecvStepCGen
  simp [hstop, hwin_mir, htr_mir, hlen, hparse, haddrs, hspqr, hpan, hfind, hfind_hon,
    hepoch, hsalt]

/-! ## Reduction to `DeliverForge` -/

/-- Steered Fig. 8 record evaluated by `fwdEvictCPure` at `sC.base.mir.epoch Q + 1`. -/
def evictedProbeRecord {Pt PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (Q : Party) (Dh : DHFun (BitVec 256) Pt)
    (epExp : ℕ → BitVec 256) (c : Fig8C Pt) (w : List (BitVec 8))
    (h : SignalHeader) (salt : Salt) : Fig8C Pt :=
  ((sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)),
    (h.counter.toNat + 1,
      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt)))

def evictedEpochSeed {Pt PQ : Type} {ℓ : ℕ}
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) : Ratchet.RootKey × Pt :=
  ((s_fig8.st Q).root,
    Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))

def evictedEpochStep {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) : Ratchet.RootKey × BitVec 256 :=
  let seed := evictedEpochSeed sC s_fig8 Q Dh epExp c
  (rootPRNG P.C.F encPt).up seed.1 seed.2

def evictedMessageKey {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (h : SignalHeader) : BitVec 256 :=
  let p₁ := evictedEpochStep P encPt sC s_fig8 Q Dh epExp c
  let step := FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat p₁.2 0 []
  ((lChainPRG P.C.F h.counter.toNat).gen step.1).2

/-- Acceptance of `(ser, tag)` with steered salt `effectiveHkdfSalt32 salt` under `evictedMessageKey` at `sC.base.mir.epoch Q + 1`. -/
def EvictedDeliverForgeEvent {Pt PQ PQC : Type} [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt) : Bool :=
  let t := sC.base.mir.epoch Q + 1
  let i := h.counter.toNat + 1
  let T := Dh.dh (epExp c.1.1) Dh.base
  let ser := w.take (w.length - 8)
  let tag := bytesToWord64LE (w.drop (w.length - 8))
  let key := evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h
  (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
    key (i, (t, some T)) ((ser, tag), effectiveHkdfSalt32 salt)).isSome

/-- Outside `inReceiveOnlyEpoch` with counter within `maxForwardJumps`, Fig. 8 `receive` on `evictedProbeRecord` decrypts under `evictedMessageKey`. -/
theorem lFig8_receive_evictedProbeRecord_eq
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)) :
    let t := sC.base.mir.epoch Q + 1
    let i := h.counter.toNat + 1
    let T := Dh.dh (epExp c.1.1) Dh.base
    let ser := w.take (w.length - 8)
    let tag := bytesToWord64LE (w.drop (w.length - 8))
    let p₁ := evictedEpochStep P encPt sC s_fig8 Q Dh epExp c
    let step := FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat p₁.2 0 []
    let gen := (lChainPRG P.C.F h.counter.toNat).gen step.1
    let v' : RatchetReceiverState (BitVec 256) (BitVec 256) := ⟨gen.1, i, step.2⟩
    (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (evictedProbeRecord sC Q Dh epExp c w h salt) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h)
        (i, (t, some T)) ((ser, tag), effectiveHkdfSalt32 salt)).map
        (fun pm =>
          ({ (s_fig8.st Q) with
              root := p₁.1,
              vR := Function.update (s_fig8.st Q).vR t (some v'),
              γ := .pub T,
              tcur := t },
            t, i, pm)) := by
  dsimp only
  have hsim := hinv.hsim
  have hst_id : (s_fig8.st Q).id = Q := hsim.hst_id Q
  have htcur : (s_fig8.st Q).tcur = sC.base.mir.epoch Q := hsim.htcur Q
  have hQ_recv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
    sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  rcases hsim.hspur Q with ⟨_, _, _, hspur_notinw, _⟩
  rcases hspur_notinw hinw with ⟨hγ_Q, _, _, _, _⟩
  unfold lFig8 SM.Construction.scheme SM.Construction.receive lFS dhScheme
    evictedProbeRecord evictedMessageKey evictedEpochStep evictedEpochSeed
  dsimp only
  rw [htcur]
  have hcond1 :
      ((s_fig8.st Q).id.sendsIn (sC.base.mir.epoch Q + 1) ||
        decide (sC.base.mir.epoch Q + 1 < sC.base.mir.epoch Q + 1)) = false := by
    rw [hst_id, hQ_recv]
    simp
  simp only [hcond1, Bool.false_eq_true, ↓reduceIte, hγ_Q, Function.update_self]
  unfold FSAEAD.fromAEADPRG
  dsimp only
  have hlk : ([] : List (ℕ × BitVec 256)).lookup (h.counter.toNat + 1) = none := rfl
  have hcond_false :
      ¬ (h.counter.toNat + 1 ≤ 0 ∨ 25000 < h.counter.toNat + 1 - 0 - 1) := by
    intro hbad
    rcases hbad with hle | hgt
    · omega
    · exact hbound (Or.inl (by omega))
  have hsub1 : h.counter.toNat + 1 - 0 - 1 = h.counter.toNat := by omega
  have hsub2 : h.counter.toNat + 1 - 1 = h.counter.toNat := by omega
  rw [hlk, ite_eq_right hcond_false, hsub1, hsub2]
  cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
      ((lChainPRG P.C.F h.counter.toNat).gen
        (FSAEAD.skipKeys (lChainPRG P.C.F) h.counter.toNat
          ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root
            (Dh.dh (epExp (sC.base.mir.epoch Q)) (Dh.dh (epExp c.1.1) Dh.base))).2 0 []).1).2
      (h.counter.toNat + 1, (sC.base.mir.epoch Q + 1, some (Dh.dh (epExp c.1.1) Dh.base)))
      ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt) with
  | none => rfl
  | some pm =>
    simp [Function.update_idem]

/-- Fig. 8 `receive` accepts `evictedProbeRecord` iff `EvictedDeliverForgeEvent` holds. -/
theorem lFig8_receive_evictedProbeRecord_isSome_eq_deliverForgeEvent
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hbound : ¬ (25000 < h.counter.toNat + 1 - 1 ∨ 2 ^ 32 ≤ h.counter.toNat + 1)) :
    ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
      (evictedProbeRecord sC Q Dh epExp c w h salt)).isSome =
      EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h salt := by
  rw [lFig8_receive_evictedProbeRecord_eq P Inv Dh encPt encT idOf lam qep q r x₀
    s_R sC s_fig8 ec winBefore epExp hinv Q c w h salt hinw hbound]
  unfold EvictedDeliverForgeEvent
  exact Option.isSome_map

/-! ## Spurious-step coin bound -/

theorem skipKeys_lChainPRG_fst (F : ShaCompress) (k : ℕ) (w : BitVec 256) (p : ℕ)
    (dict : List (ℕ × BitVec 256)) :
    (FSAEAD.skipKeys (lChainPRG F) k w p dict).1 =
      (List.range k).foldl (fun key _ => (hmacPRF F).tag key Ratchet.chainKeySeed) w := by
  induction k generalizing w p dict with
  | zero => rfl
  | succ k ih =>
    dsimp only [FSAEAD.skipKeys, lChainPRG]
    rw [ih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

theorem evictedEpochStep_eq_spurPRG {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hrk : (s_fig8.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1) :
    evictedEpochStep P encPt sC s_fig8 Q Dh epExp c =
      (evictedKeySpuriousStepPrg P.C.F encPt Dh rk_base T_base (epExp c.1.1)).gen
        (epExp (sC.base.mir.epoch Q)) := by
  unfold evictedEpochStep evictedEpochSeed evictedKeySpuriousStepPrg Ratchet.rootPRNG
  dsimp only
  rw [hrk]

theorem evictedMessageKey_keyToBytes32_eq {Pt PQ PQC : Type} {ℓ : ℕ}
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (Dh : DHFun (BitVec 256) Pt) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (h : SignalHeader) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hrk : (s_fig8.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1) :
    let p₁ := (evictedKeySpuriousStepPrg P.C.F encPt Dh rk_base T_base (epExp c.1.1)).gen
      (epExp (sC.base.mir.epoch Q))
    let ck := (List.range h.counter.toNat).foldl
      (fun k _ => (hmacPRF P.C.F).tag k Ratchet.chainKeySeed) p₁.2
    keyToBytes32 (evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h) =
      Ratchet.chainHmac P.C.F ck Ratchet.messageKeySeed := by
  unfold evictedMessageKey
  dsimp only [lChainPRG]
  rw [evictedEpochStep_eq_spurPRG P encPt sC s_fig8 Q Dh epExp c rk_base T_base hrk,
    skipKeys_lChainPRG_fst]
  exact keyToBytes32_hmacPRF_tag P.C.F _ Ratchet.messageKeySeed

/-- Outside `inReceiveOnlyEpoch` with `(s_fig8.st Q).root` from `Q`'s eager step, `EvictedDeliverForgeEvent` implies `spurBadSingle`. -/
theorem evictedDeliverForgeEvent_implies_spurBadSingle
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [DecidableEq PQ]
    [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
    (salt : Salt) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hrk : (s_fig8.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hw32 : w.length < 2 ^ 32)
    (hevent : EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h salt = true) :
    spurBadSingle P encPt Dh Q rk_base T_base w salt (epExp c.1.1)
      (epExp (sC.base.mir.epoch Q)) = true := by
  have hrecv : Q.sendsIn (sC.base.mir.epoch Q + 1) = false :=
    sendsIn_succ_false_of_inWin_false sC.base.mir Q hinw
  have hlids : lIds idOf (sC.base.mir.epoch Q + 1) = macIds (idOfP P Q.other) (idOfP P Q) :=
    lIds_eq_macIds_of_not_sendsIn P idOf hid Q (sC.base.mir.epoch Q + 1) hrecv
  have hkey := evictedMessageKey_keyToBytes32_eq P encPt sC s_fig8 Q Dh epExp c h
    rk_base T_base hrk
  dsimp only at hkey
  unfold EvictedDeliverForgeEvent AEADScheme.movePubPartToAD lPubOf lAead lAeadK lWire
    libsignalWireAead libsignalReceiveWire at hevent
  simp only [hparse, Option.map_some, ne_eq, not_true_eq_false, ↓reduceIte] at hevent
  unfold spurBadSingle
  simp only [hparse, hw32, ↓reduceIte]
  rw [← hlids, ← hkey, msgKeys_effSalt]
  by_cases hmac :
      ((hmacScheme P.C.F).tag
        (deriveMessageKeys P.C.F (some (effectiveHkdfSalt32 salt))
          (keyToBytes32 (evictedMessageKey P encPt sC s_fig8 Q Dh epExp c h))).2
        ((lIds idOf (sC.base.mir.epoch Q + 1)).toList ++ w.take (w.length - 8)) ==
          bytesToWord64LE (w.drop (w.length - 8))) = true
  · exact hmac
  · simp [hmac] at hevent

/-- Bounds the probability of `spurBadList` over at most `q * qep` pre-fixed triples by `spuriousStepTerm`. -/
theorem spurBadList_prob_le_spuriousStepTerm
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
    [SampleableType PQC]
    (P : Params PQ PQC) (encPt : Pt → List (BitVec 8))
    (Dh : DHFun (BitVec 256) Pt) (Q : Party) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (q qep : ℕ) (L : List (List (BitVec 8) × Salt × BitVec 256))
    (hL : L.length ≤ q * qep) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {x | spurBadList P encPt Dh Q rk_base T_base L x = true} ≤
      spuriousStepTerm P.C.F encPt Dh q qep := by
  rw [spurBound_eq_mul_spurUnit]
  refine (spurBadList_prob_le P encPt Dh Q rk_base T_base L).trans ?_
  gcongr

theorem evictedDeliverForgeEvent_congr
    {Pt PQ PQC : Type} [DecidableEq Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (epExp : ℕ → BitVec 256) (c : Fig8C Pt)
    (w : List (BitVec 8)) (h : SignalHeader) (salt : Salt)
    (hepoch : sC'.base.mir.epoch Q = sC.base.mir.epoch Q)
    (hroot : (s_fig8'.st Q).root = (s_fig8.st Q).root) :
    EvictedDeliverForgeEvent P Dh encPt encT idOf sC' s_fig8' Q epExp c w h salt =
      EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h salt := by
  unfold EvictedDeliverForgeEvent evictedMessageKey evictedEpochStep evictedEpochSeed
  rw [hepoch, hroot]

/-- A post-draw corruption preserving `sC.base.mir.epoch Q` and `(s_fig8.st Q).root` transfers `EvictedDeliverForgeEvent` back to `spurBadSingle` on the pre-corruption coin. -/
theorem postDraw_corr_Q_evictedDeliverForgeEvent_implies_spurBadSingle
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [DecidableEq PQ]
    [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (epExp : ℕ → BitVec 256)
    (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
    (salt : Salt) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (hrk : (s_fig8.st Q).root =
      (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1)
    (hepoch : sC'.base.mir.epoch Q = sC.base.mir.epoch Q)
    (hroot : (s_fig8'.st Q).root = (s_fig8.st Q).root)
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hw32 : w.length < 2 ^ 32)
    (hevent : EvictedDeliverForgeEvent P Dh encPt encT idOf sC' s_fig8' Q epExp c w h salt =
      true) :
    spurBadSingle P encPt Dh Q rk_base T_base w salt (epExp c.1.1)
      (epExp (sC.base.mir.epoch Q)) = true := by
  have hev0 :
      EvictedDeliverForgeEvent P Dh encPt encT idOf sC s_fig8 Q epExp c w h salt = true := by
    rw [← evictedDeliverForgeEvent_congr P Dh encPt encT idOf sC sC' s_fig8 s_fig8'
      Q epExp c w h salt hepoch hroot]
    exact hevent
  exact evictedDeliverForgeEvent_implies_spurBadSingle P Dh encPt encT idOf hid sC s_fig8 Q epExp
    c w h body salt rk_base T_base hinw hrk hparse hw32 hev0

/-- Union bound by `spuriousStepTerm` for `spurBadList` over at most `q * qep` pre-fixed triples together with post-corruption transfer from `EvictedDeliverForgeEvent`. -/
theorem postDraw_corr_Q_evictedDeliverForgeEvent_prob_le_spuriousStepTerm
    {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [DecidableEq PQ]
    [Inhabited PQ] [SampleableType PQC] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (Q : Party) (rk_base : Ratchet.RootKey) (T_base : Pt)
    (hinw : inReceiveOnlyEpoch sC.base.mir Q = false)
    (q qep : ℕ) (L : List (List (BitVec 8) × Salt × BitVec 256))
    (hL : L.length ≤ q * qep) :
    𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))]
      {x | spurBadList P encPt Dh Q rk_base T_base L x = true} ≤
      spuriousStepTerm P.C.F encPt Dh q qep ∧
    ∀ (epExp : ℕ → BitVec 256) (sC' : LibsignalToModularSchemeSimState PQ Pt ℓ)
      (s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (c : Fig8C Pt) (w : List (BitVec 8)) (h : SignalHeader) (body : List (BitVec 8))
      (salt : Salt),
      (s_fig8.st Q).root =
        (rootKdf P.C.F rk_base (encPt (Dh.dh (epExp (sC.base.mir.epoch Q)) T_base))).1 →
      (w, salt, epExp c.1.1) ∈ L →
      sC'.base.mir.epoch Q = sC.base.mir.epoch Q →
      (s_fig8'.st Q).root = (s_fig8.st Q).root →
      (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) →
      w.length < 2 ^ 32 →
      EvictedDeliverForgeEvent P Dh encPt encT idOf sC' s_fig8' Q epExp c w h salt = true →
      spurBadList P encPt Dh Q rk_base T_base L (epExp (sC.base.mir.epoch Q)) = true := by
  refine ⟨spurBadList_prob_le_spuriousStepTerm P encPt Dh Q rk_base T_base q qep L hL, ?_⟩
  intro epExp sC' s_fig8' c w h body salt hrk hmem hepoch hroot hparse hw32 hevent
  have hsingle := postDraw_corr_Q_evictedDeliverForgeEvent_implies_spurBadSingle
    P Dh encPt encT idOf hid sC sC' s_fig8 s_fig8' Q epExp c w h body salt rk_base T_base
    hinw hrk hepoch hroot hparse hw32 hevent
  unfold spurBadList
  exact List.any_eq_true.mpr ⟨(w, salt, epExp c.1.1), hmem, hsingle⟩

end CryptoGames.LibsignalSM.Proofs.Refinement

