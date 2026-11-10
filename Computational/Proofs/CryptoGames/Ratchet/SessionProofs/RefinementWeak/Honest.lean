/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementWeak.Defs

/-!
# Honest entries and `SimInvW` helpers for the weak refinement

Proves uniqueness, raw-key agreement, and in-transit synchronization for `HonestEntryInvW`
and `SimInvW` under `SpqrWLocal`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

theorem HonestEntryInvW.congr_epExp {P : Params PQ PQC} (Inv : PQ → Prop) {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp epExp' : ℕ → BitVec 256}
    {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInvW P Inv Dh encT epExp wc)
    (heq : epExp' wc.2.1.1 = epExp wc.2.1.1) :
    HonestEntryInvW P Inv Dh encT epExp' wc := by
  unfold HonestEntryInvW at h ⊢
  dsimp only at h ⊢
  rw [heq]
  exact h

theorem honestEntryInvW_len_lt {P : Params PQ PQC} {Inv : PQ → Prop} {Dh : DHFun (BitVec 256) Pt}
    {encT : Pt → PublicKey} {epExp : ℕ → BitVec 256} {wc : List (BitVec 8) × Fig8C Pt}
    (h : HonestEntryInvW P Inv Dh encT epExp wc) : wc.1.length < 2 ^ 32 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
  exact h

theorem honestEntryInvW_eq_raw (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (epExp : ℕ → BitVec 256)
    {w : List (BitVec 8)} {c : Fig8C Pt}
    (hinv : HonestEntryInvW P Inv Dh encT epExp (w, c))
    {h : SignalHeader} {body : List (BitVec 8)}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    {pq_st pq' : PQ} {salt : Salt}
    (hspqr : P.spqr.recv pq_st h.pqRatchet = .ok (pq', salt))
    (hpqInv : Inv pq_st) :
    h.messageVersion = currentVersion ∧
    h.senderRatchetKey = encT (Dh.dh (epExp c.1.1) Dh.base) ∧
    h.counter.toNat + 1 = c.2.1 ∧
    effectiveHkdfSalt32 salt = c.2.2.2 ∧
    c = ((c.1.1, some (Dh.dh (epExp c.1.1) Dh.base)),
      (h.counter.toNat + 1,
        ((w.take (w.length - 8), bytesToWord64LE (w.drop (w.length - 8))), effectiveHkdfSalt32 salt))) := by
  rcases hinv with ⟨hw, hw_len, ht_ge1, hraw, hi1, hi32, hT, h₀, body₀, hparse₀, hver, hsrk, hctr, haddrs, hspqr₀, _⟩
  have hhb : (h, body) = (h₀, body₀) := Option.some.inj (hparse.symm.trans hparse₀)
  rcases Prod.mk.inj hhb with ⟨rfl, rfl⟩
  have hsalt : effectiveHkdfSalt32 salt = c.2.2.2 := hspqr₀ pq_st pq' salt hpqInv hspqr
  refine ⟨hver, hsrk, hctr, hsalt, ?_⟩
  rcases c with ⟨⟨t_c, T_c⟩, ⟨i_c, ⟨raw_c, salt_c⟩⟩⟩
  dsimp only at hT hctr hraw hsalt
  rw [hT, ← hctr, hraw, hsalt]

theorem honestEntryInvW_of_lAead_enc (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (hrt : RoundTrip.RtHyp P ℓ)
    (hS : SpqrWLocal P.spqr Inv)
    (epExp : ℕ → BitVec 256) (Q : Party) (t i : ℕ)
    (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hi1 : 1 ≤ i) (hi32 : i < 2 ^ 32)
    (seed : BitVec 256) (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt)
    (hpqInv : Inv pq_st) :
    let T := Dh.dh (epExp t) Dh.base
    let ct_aead := ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).enc
      seed (i, (t, some T)) (pub, m)
    let c : Fig8C Pt := ((t, some T), (i, ct_aead))
    HonestEntryInvW P Inv Dh encT epExp (LibsignalSim.toWire c, c) := by
  intro T ct_aead c
  have hsender : Party.senderOf t = Q := by
    cases Q <;> simp [Party.sendsIn, Party.senderOf] at hsends ⊢ <;> omega
  set h_hdr := lHeader encT i (t, some T) pub
  set mk := deriveMessageKeys P.C.F (some pub.salt) (keyToBytes32 seed)
  set body := ((cbcPkcs7EncryptOnly P.C.E ℓ).enc (mk.1.1, mk.1.2) m).toList.flatMap blockToBytesLE
  set ser := (signalWireCodec P.codec).encode h_hdr body
  set tag := (hmacScheme P.C.F).tag mk.2 ((lIds idOf t).toList ++ ser)
  have hct_eq : ct_aead = ((ser, tag), pub.salt) := rfl
  have hc_eq : c = ((t, some T), (i, ((ser, tag), pub.salt))) := rfl
  set w := LibsignalSim.toWire c
  have hw_eq : w = ser ++ tagBytes tag := rfl
  have hser_ge1 : 1 ≤ ser.length := length_signalWireCodec_encode_ge_one P.codec h_hdr body
  have htag_len : (tagBytes tag).length = 8 := length_tagBytes tag
  have hw_len : ¬ w.length < 9 := by
    rw [hw_eq, List.length_append, htag_len]
    omega
  have hw_sub : w.length - 8 = ser.length := by
    rw [hw_eq, List.length_append, htag_len]
    omega
  have htake : w.take (w.length - 8) = ser := by
    rw [hw_sub, hw_eq, List.take_left]
  have hdrop : bytesToWord64LE (w.drop (w.length - 8)) = tag := by
    rw [hw_sub, hw_eq, List.drop_left, tag8_tagBytes]
  have hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h_hdr, body) := by
    rw [htake]
    refine RoundTrip.RtHyp.parse hrt h_hdr body rfl
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (RoundTrip.length_cbcBody _)
    change RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
  have hctr : h_hdr.counter.toNat + 1 = i := by
    change (BitVec.ofNat 32 (i - 1)).toNat + 1 = i
    have hlt : i - 1 < 4294967296 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  refine ⟨rfl, hw_len, ht_ge1, ?_, hi1, hi32, rfl, h_hdr, body, hparse, rfl, rfl, hctr, ?_, ?_, ?_⟩
  · rw [htake, hdrop]; rfl
  · rw [hsender]
    change addressCheckPasses pub.addrs (P.expectedAddrs Q.other) = true
    rw [haddrs_pub]
    exact addrsOk_send_other P Q unackA
  · intro pq_st₂ pq₂' salt₂ hpqInv₂ hrecv
    have hsalt_eq : salt₂ = salt :=
      hS.2.2 pq_st rq pq' salt pub.pqmsg hpqInv hspqr_send pq_st₂ pq₂' salt₂ hpqInv₂ hrecv
    rw [hsalt_eq]
    exact hsalt.symm
  · rw [hw_eq, List.length_append, htag_len]
    refine RoundTrip.RtHyp.encode_length_lt hrt h_hdr body
      (Or.inr ⟨_, _, _, _, hspqr_send⟩) ?_ (RoundTrip.length_cbcBody _)
    change RoundTrip.SentAddrs P pub.addrs
    rw [haddrs_pub]
    cases Q <;> cases unackA
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)

theorem lFig8_send_step_not_inWinW (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hrt : RoundTrip.RtHyp P ℓ) (hS : SpqrWLocal P.spqr Inv)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ)
    (hst_id : st.id = Q) (htcur : st.tcur = t) (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .exp (epExp t)) (hTcur : st.curCkaMsg = some (Dh.dh (epExp t) Dh.base))
    (v : RatchetSenderState (BitVec 256)) (hvS : st.vS = some v) (hv_lt : v.lastIndex + 1 < 2 ^ 32)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt)
    (hpqInv : Inv pq_st) :
    let res := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka
    let st' := res.1
    let c := res.2
    st'.id = Q ∧ st'.root = st.root ∧ st'.tcur = t ∧ st'.γ = .exp (epExp t) ∧
    st'.curCkaMsg = some (Dh.dh (epExp t) Dh.base) ∧ st'.vR = st.vR ∧
    (∃ v', st'.vS = some v' ∧ v'.lastIndex = v.lastIndex + 1) ∧
    c.1 = (t, some (Dh.dh (epExp t) Dh.base)) ∧ c.2.1 = v.lastIndex + 1 ∧
    HonestEntryInvW P Inv Dh encT epExp (LibsignalSim.toWire c, c) := by
  have hnot_succ : st.id.sendsIn (st.tcur + 1) = false := by
    rw [hst_id, htcur]
    exact sendsIn_succ_of_sendsIn Q t hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG
  dsimp only
  rw [hnot_succ, ite_eq_right Bool.false_ne_true, hvS, htcur, hTcur]
  refine ⟨hst_id, rfl, rfl, hγ, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, ?_⟩
  exact honestEntryInvW_of_lAead_enc P Inv Dh encT idOf hrt hS epExp Q t (v.lastIndex + 1)
    ht_ge1 hsends (by omega) hv_lt _ pub m unackA haddrs_pub hspqr_send hsalt hpqInv

theorem lFig8_send_step_inWinW (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hrt : RoundTrip.RtHyp P ℓ) (hS : SpqrWLocal P.spqr Inv)
    (epExp : ℕ → BitVec 256) (Q : Party) (st : Fig8St Pt) (t : ℕ) (T_other : Pt)
    (hst_id : st.id = Q) (htcur : st.tcur + 1 = t) (ht_ge1 : 1 ≤ t) (hsends : Q.sendsIn t = true)
    (hγ : st.γ = .pub T_other)
    (pub : LibsignalMsgPublicPart) (m : Plain ℓ) (c_cka : BitVec 256) (hc_cka : c_cka = epExp t) (unackA : Bool)
    (haddrs_pub : pub.addrs = if Q == Party.A && unackA then P.addrAB else none)
    {pq_st : PQ} {rq : PQC} {pq' : PQ} {salt : HKDF.Salt}
    (hspqr_send : P.spqr.send pq_st rq = some (pq', salt, pub.pqmsg))
    (hsalt : pub.salt = effectiveHkdfSalt32 salt)
    (hpqInv : Inv pq_st) :
    let res := (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send st (pub, m) c_cka
    let st' := res.1
    let c := res.2
    st'.id = Q ∧
    st'.root = (rootKdf P.C.F st.root (encPt (Dh.dh (epExp t) T_other))).1 ∧
    st'.tcur = t ∧ st'.γ = .exp (epExp t) ∧
    st'.curCkaMsg = some (Dh.dh (epExp t) Dh.base) ∧ st'.vR = st.vR ∧
    (∃ v', st'.vS = some v' ∧ v'.lastIndex = 1) ∧
    c.1 = (t, some (Dh.dh (epExp t) Dh.base)) ∧ c.2.1 = 1 ∧
    HonestEntryInvW P Inv Dh encT epExp (LibsignalSim.toWire c, c) := by
  have hsends_succ : st.id.sendsIn (st.tcur + 1) = true := by
    rw [hst_id, htcur]; exact hsends
  unfold lFig8 SM.Construction.scheme SM.Construction.send lFS FSAEAD.fromAEADPRG dhScheme
  dsimp only
  rw [hsends_succ, ite_eq_left rfl, hγ, hc_cka, htcur]
  dsimp only
  rw [Nat.zero_add]
  refine ⟨hst_id, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩, rfl, rfl, ?_⟩
  exact honestEntryInvW_of_lAead_enc P Inv Dh encT idOf hrt hS epExp Q t 1
    ht_ge1 hsends (by decide) (by decide) _ pub m unackA haddrs_pub hspqr_send hsalt hpqInv

namespace WP2A.H3

theorem find_fig8_eq_of_map {ℓ : ℕ}
    {L_mir : List (SM.Record (Plain ℓ) (List (BitVec 8)))}
    {L_fig8 : List (SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))}
    (hmap : L_mir.map (fun r => (r.pos, r.ct)) =
      L_fig8.map (fun r => (r.pos, LibsignalSim.toWire r.ct)))
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hiff : ∀ r ∈ L_fig8, decide (r.ct = c) = decide (LibsignalSim.toWire r.ct = w)) :
    (L_mir.find? fun r => r.pos.sender == Q && decide (r.ct = w)).map (fun r => (r.pos, r.ct)) =
      (L_fig8.find? fun r => r.pos.sender == Q && decide (r.ct = c)).map
        (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
  induction L_mir generalizing L_fig8 with
  | nil =>
    cases L_fig8 with
    | nil => rfl
    | cons _ _ => cases hmap
  | cons r₁ L₁ ih =>
    cases L_fig8 with
    | nil => cases hmap
    | cons r₂ L₂ =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      rcases hmap with ⟨hhead, htail⟩
      have hpos : r₁.pos = r₂.pos := congrArg Prod.fst hhead
      have hct : r₁.ct = LibsignalSim.toWire r₂.ct := congrArg Prod.snd hhead
      have hr₂ := hiff r₂ List.mem_cons_self
      simp only [List.find?_cons, hpos, hr₂, ← hct]
      split
      · simp [hpos, hct]
      · exact ih htail (fun r hr => hiff r (List.mem_cons_of_mem r₂ hr))

end WP2A.H3

/-- Two `HonestEntryInvW` entries for the same wire coincide whenever some `Inv` state accepts the wire's SPQR message. -/
theorem honestEntryInvW_unique (P : Params PQ PQC) (Inv : PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (epExp : ℕ → BitVec 256)
    {w : List (BitVec 8)} {c₁ c₂ : Fig8C Pt}
    (h₁ : HonestEntryInvW P Inv Dh encT epExp (w, c₁))
    (h₂ : HonestEntryInvW P Inv Dh encT epExp (w, c₂))
    (hcoll : Dh.dh (epExp c₁.1.1) Dh.base = Dh.dh (epExp c₂.1.1) Dh.base → c₁.1.1 = c₂.1.1)
    {h : SignalHeader} {body : List (BitVec 8)} {pq_st pq₁ : PQ} {salt₁ : Salt}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hpqInv : Inv pq_st) (hacc : P.spqr.recv pq_st h.pqRatchet = .ok (pq₁, salt₁)) :
    c₁ = c₂ := by
  rcases honestEntryInvW_eq_raw P Inv Dh encT epExp h₁ hparse hacc hpqInv with ⟨_, hsrk₁, _, _, heq₁⟩
  rcases honestEntryInvW_eq_raw P Inv Dh encT epExp h₂ hparse hacc hpqInv with ⟨_, hsrk₂, _, _, heq₂⟩
  have hdh : Dh.dh (epExp c₁.1.1) Dh.base = Dh.dh (epExp c₂.1.1) Dh.base :=
    hinj (hsrk₁.symm.trans hsrk₂)
  have ht : c₁.1.1 = c₂.1.1 := hcoll hdh
  rw [heq₁, heq₂, ht]

theorem deliver_inTransit_mem {ℓ : ℕ}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hmeta : SameMeta s_R s s_fig8)
    (htrans_hon : ∀ r ∈ s_fig8.trans,
      (LibsignalSim.toWire r.ct, r.ct) ∈ s.honest ∧ r.pos.sender = Party.senderOf r.ct.1.1)
    (Q : Party) (w : List (BitVec 8))
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : s.mir.inTransit Q.other w = some r_mir) :
    ∃ c, (w, c) ∈ s.honest ∧ Party.senderOf c.1.1 = Q.other := by
  have hmir_mem : r_mir ∈ s.mir.trans := List.mem_of_find?_eq_some htr_mir
  have hmir_pred := List.find?_some htr_mir
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmir_pred
  have hmap_mem : (r_mir.pos, w) ∈ s_fig8.trans.map (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
    rw [← hmeta.htrans_fig8, ← hmir_pred.2]
    exact List.mem_map_of_mem hmir_mem
  rw [List.mem_map] at hmap_mem
  rcases hmap_mem with ⟨r₀, hr₀, hpair₀⟩
  have hpos₀ : r₀.pos = r_mir.pos := congrArg Prod.fst hpair₀
  have hw₀ : LibsignalSim.toWire r₀.ct = w := congrArg Prod.snd hpair₀
  refine ⟨r₀.ct, ?_, ?_⟩
  · rw [← hw₀]
    exact (htrans_hon r₀ hr₀).1
  · rw [← (htrans_hon r₀ hr₀).2, hpos₀, hmir_pred.1]

theorem honestC_eq_some_of_memW (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (M : ℕ)
    (s : SimState PQ Pt ℓ) (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hmem : (w, c) ∈ s.honest)
    (hsender : Party.senderOf c.1.1 = Q.other)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInvW P Inv Dh encT epExp wc ∧ wc.2.1.1 ≤ M)
    (hcoll : ∀ t₁ t₂, t₁ ≤ M → t₂ ≤ M →
      Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂)
    {h : SignalHeader} {body : List (BitVec 8)} {pq_st pq₁ : PQ} {salt₁ : Salt}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hpqInv : Inv pq_st) (hacc : P.spqr.recv pq_st h.pqRatchet = .ok (pq₁, salt₁)) :
    (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c := by
  cases hfind : s.honest.find? (fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other) with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hfind (w, c) hmem
    simp [hsender] at hnone
  | some wc' =>
    dsimp only [Option.map]
    congr 1
    have hmem' := List.mem_of_find?_eq_some hfind
    have hpred' := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred'
    rcases wc' with ⟨w', c'⟩
    dsimp only at hpred' ⊢
    rcases hpred' with ⟨rfl, _⟩
    exact honestEntryInvW_unique P Inv Dh encT hinj epExp (hhon (w', c') hmem').1 (hhon (w', c) hmem).1
      (hcoll c'.1.1 c.1.1 (hhon (w', c') hmem').2 (hhon (w', c) hmem).2) hparse hpqInv hacc

/-- Synchronizes an in-transit `deliver` wire with its unique `HonestEntryInvW` entry when an `Inv` state accepts its SPQR message. -/
theorem deliver_inTransit_syncW (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT)
    (epExp : ℕ → BitVec 256) (M : ℕ)
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hmeta : SameMeta s_R s s_fig8)
    (hhon : ∀ wc ∈ s.honest, HonestEntryInvW P Inv Dh encT epExp wc ∧ wc.2.1.1 ≤ M)
    (htrans_hon : ∀ r ∈ s_fig8.trans,
      (LibsignalSim.toWire r.ct, r.ct) ∈ s.honest ∧ r.pos.sender = Party.senderOf r.ct.1.1)
    (hcoll : ∀ t₁ t₂, t₁ ≤ M → t₂ ≤ M →
      Dh.dh (epExp t₁) Dh.base = Dh.dh (epExp t₂) Dh.base → t₁ = t₂)
    (Q : Party) (w : List (BitVec 8))
    {r_mir : SM.Record (Plain ℓ) (List (BitVec 8))}
    (htr_mir : s.mir.inTransit Q.other w = some r_mir)
    {h : SignalHeader} {body : List (BitVec 8)} {pq_st pq₁ : PQ} {salt₁ : Salt}
    (hparse : (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body))
    (hpqInv : Inv pq_st) (hacc : P.spqr.recv pq_st h.pqRatchet = .ok (pq₁, salt₁)) :
    (∃ r_R, s_R.inTransit Q.other w = some r_R ∧ r_R.pos = r_mir.pos) ∧
    ∃ c r_fig8,
      (w, c) ∈ s.honest ∧
      Party.senderOf c.1.1 = Q.other ∧
      s_fig8.inTransit Q.other c = some r_fig8 ∧
      r_fig8.pos = r_mir.pos ∧
      (s.honest.find? fun wc => wc.1 == w && Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c ∧
      ∀ {Key : Type} (sm : SMScheme Key (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
        (Δ qep : ℕ) (cfg : SM.Config (LibsignalMsgPublicPart × Plain ℓ)),
        fwdPure sm Δ qep cfg s Q c s_fig8 = deliverPure sm cfg Q c s_fig8 := by
  have hR_map := hmeta.inTransit_R_map Q.other w
  rw [htr_mir, Option.map_some] at hR_map
  rcases Option.map_eq_some_iff.mp hR_map with ⟨r_R, hr_R, hpair_R⟩
  have hpos_R : r_R.pos = r_mir.pos := congrArg Prod.fst hpair_R
  have hmir_mem : r_mir ∈ s.mir.trans := List.mem_of_find?_eq_some htr_mir
  have hmir_pred := List.find?_some htr_mir
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmir_pred
  have hmap_mem : (r_mir.pos, w) ∈ s_fig8.trans.map (fun r => (r.pos, LibsignalSim.toWire r.ct)) := by
    rw [← hmeta.htrans_fig8, ← hmir_pred.2]
    exact List.mem_map_of_mem hmir_mem
  rw [List.mem_map] at hmap_mem
  rcases hmap_mem with ⟨r₀, hr₀, hpair₀⟩
  have hpos₀ : r₀.pos = r_mir.pos := congrArg Prod.fst hpair₀
  have hw₀ : LibsignalSim.toWire r₀.ct = w := congrArg Prod.snd hpair₀
  set c := r₀.ct
  have hc_mem : (w, c) ∈ s.honest := by
    rw [← hw₀]
    exact (htrans_hon r₀ hr₀).1
  have hc_sender : Party.senderOf c.1.1 = Q.other := by
    rw [← (htrans_hon r₀ hr₀).2, hpos₀, hmir_pred.1]
  have hiff : ∀ r ∈ s_fig8.trans, decide (r.ct = c) = decide (LibsignalSim.toWire r.ct = w) := by
    intro r hr
    by_cases hrc : r.ct = c
    · simp [hrc, hw₀]
    · have hne_w : LibsignalSim.toWire r.ct ≠ w := by
        intro heq_w
        have hmem_r : (w, r.ct) ∈ s.honest := by
          rw [← heq_w]
          exact (htrans_hon r hr).1
        exact hrc (honestEntryInvW_unique P Inv Dh encT hinj epExp
          (hhon (w, r.ct) hmem_r).1 (hhon (w, c) hc_mem).1
          (hcoll r.ct.1.1 c.1.1 (hhon (w, r.ct) hmem_r).2 (hhon (w, c) hc_mem).2)
          hparse hpqInv hacc)
      simp [hrc, hne_w]
  have hfig8_map := (WP2A.H3.find_fig8_eq_of_map hmeta.htrans_fig8 Q.other w c hiff).symm
  change (s_fig8.inTransit Q.other c).map (fun r => (r.pos, LibsignalSim.toWire r.ct)) =
    (s.mir.inTransit Q.other w).map (fun r => (r.pos, r.ct)) at hfig8_map
  rw [htr_mir, Option.map_some] at hfig8_map
  rcases Option.map_eq_some_iff.mp hfig8_map with ⟨r_fig8, hr_fig8, hpair_fig8⟩
  have hpos_fig8 : r_fig8.pos = r_mir.pos := congrArg Prod.fst hpair_fig8
  refine ⟨⟨r_R, hr_R, hpos_R⟩, c, r_fig8, hc_mem, hc_sender, hr_fig8, hpos_fig8,
    honestC_eq_some_of_memW P Inv Dh encT hinj epExp M s Q w c hc_mem hc_sender hhon hcoll hparse hpqInv hacc, ?_⟩
  intro Key sm Δ qep cfg
  unfold fwdPure
  have hany : s.honest.any (fun wc => decide (wc.2 = c) && (s.mir.inTransit Q.other wc.1).isSome) = true := by
    rw [List.any_eq_true]
    exact ⟨(w, c), hc_mem, by simp [htr_mir]⟩
  rw [hany]
  rfl

theorem SimInvW.mono_r {P : Params PQ PQC} (Inv : PQ → Prop) {ℓ : ℕ} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {qep q r r' : ℕ}
    {x₀ : BitVec 256}
    {s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8))}
    {s : SimState PQ Pt ℓ}
    {s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    {ec : Party → BitVec 256}
    {winBefore : ℕ → Bool}
    {epExp : ℕ → BitVec 256}
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hle : r' ≤ r) :
    SimInvW P Inv ℓ Dh encPt encT qep q r' x₀ s_R s s_fig8 ec winBefore epExp :=
  { hinv with
    hamb := by have := hinv.hamb; omega
    hamb_strict := fun h => by have := hinv.hamb_strict h; omega
    hidx_le := fun Q => by have := hinv.hidx_le Q; omega
    hhon_len := by have := hinv.hhon_len; omega }

theorem simInvW_mono_r (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (qep q r₁ r₂ : ℕ)
    (hr : r₁ ≤ r₂) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r₂ x₀ s_R s s_fig8 ec winBefore epExp) :
    SimInvW P Inv ℓ Dh encPt encT qep q r₁ x₀ s_R s s_fig8 ec winBefore epExp :=
  hinv.mono_r Inv hr

theorem stepR_D0_eq_of_simInvW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (q_sm : (SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))).Domain)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (s : SimState PQ Pt ℓ)
    (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvW P Inv ℓ Dh encPt encT qep q r x₀ s_R s s_fig8 ec winBefore epExp)
    (hq : ∀ Qw, q_sm ≠ .inl (.inr Qw)) :
    stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configEpoch0Distinguisher (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R =
      stepR (libsignalSessionScheme P ℓ encPt lam) 3 qep (configR1OnCurve (ratchetKeyAdmissible P.codec decT encT)) q_sm s_R := by
  refine stepR_configD0_eq_configR1Inj P ℓ encPt lam (ratchetKeyAdmissible P.codec decT encT) qep q_sm s_R hq ?_
  intro h10
  rw [hinv.hmeta.hepoch_R] at h10
  rw [hinv.hst_R .A, expectedGhost_chainEpochs]
  exact chainsEpochInvA_contains_zero_false hinv.hchainsA h10

end CryptoGames.LibsignalSM.Proofs.Refinement
