/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs

/-!
# Public-message-to-AD reduction

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves `CryptoGames.LibsignalSM.PubRed.pubMsg_red`: `FSAEAD.pubRed` preserves query bounds and
associated-data classes, and reduces the FS-AEAD game of `fromAEADPRG (ae.movePubPartToAD pubOf) G maxSkip`
to `fromAEADPRG (reassoc ae) G maxSkip` for adversaries with equal public challenge parts.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Proofs.PubToAD

open FSAEAD AEADScheme

variable {MK CK AD Pub M C : Type}

def reassoc (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) : AEADScheme MK (ℕ × (AD × Pub)) M C where
  enc k a m := ae.enc k ((a.1, a.2.1), a.2.2) m
  dec k a c := ae.dec k ((a.1, a.2.1), a.2.2) c

local instance (priority := high) [DecidableEq C] : BEq (ℕ × C) := instBEqOfDecidableEq
local instance (priority := high) [DecidableEq Pub] [DecidableEq M] : BEq (Pub × M) :=
  instBEqOfDecidableEq

def mapRecord (r : Record (AD × Pub) M (ℕ × C)) : Record AD (Pub × M) (ℕ × C) :=
  { idx := r.idx, ad := r.ad.1, msg := (r.ad.2, r.msg), ct := r.ct }

def mapState {SS RS : Type} (st : State SS RS (AD × Pub) M (ℕ × C)) :
    State SS RS AD (Pub × M) (ℕ × C) :=
  { senderState := st.senderState
    receiverState := st.receiverState
    b := st.b
    lastSentIdx := st.lastSentIdx
    senderCorruptedAt := st.senderCorruptedAt
    receiverIdx := st.receiverIdx
    ended := st.ended
    win := st.win
    inTransit := st.inTransit.map mapRecord
    challengesInTransit := st.challengesInTransit }

/-- Simulation invariant relating `pubRedImpl`'s `ended` flag to the `(AD × Pub, M)` game state. -/
def Inv {SS RS : Type} (pubOf : C → Option Pub) (ended : Bool)
    (st : State SS RS (AD × Pub) M (ℕ × C)) : Prop :=
  ended = st.ended ∧ ∀ r ∈ st.inTransit, pubOf r.ct.2 = some r.ad.2

section StateLemmas

variable {SS RS : Type}

@[local simp]
theorem mapState_ended (st : State SS RS (AD × Pub) M (ℕ × C)) :
    (mapState st).ended = st.ended := rfl

@[local simp]
theorem mapState_challengesInTransit (st : State SS RS (AD × Pub) M (ℕ × C)) :
    (mapState st).challengesInTransit = st.challengesInTransit := rfl

theorem mapState_removeFromTransit (st : State SS RS (AD × Pub) M (ℕ × C)) (i : ℕ) :
    (mapState st).removeFromTransit i = mapState (st.removeFromTransit i) := by
  simp only [State.removeFromTransit, mapState, List.filter_map]
  rfl

theorem Inv.removeFromTransit {pubOf : C → Option Pub} {ended : Bool}
    {st : State SS RS (AD × Pub) M (ℕ × C)} (hI : Inv pubOf ended st) (i : ℕ) :
    Inv pubOf ended (st.removeFromTransit i) :=
  ⟨hI.1, fun r hr => hI.2 r (List.mem_filter.mp hr).1⟩

theorem match_record_eq [DecidableEq AD] [DecidableEq Pub] [DecidableEq C]
    {pubOf : C → Option Pub} {r : Record (AD × Pub) M (ℕ × C)}
    (hr : pubOf r.ct.2 = some r.ad.2) (a : AD) (p : Pub) (c : ℕ × C)
    (hc : pubOf c.2 = some p) :
    (r.ad.1 == a && r.ct == c) = (r.ad == (a, p) && r.ct == c) := by
  rcases r with ⟨idx, ⟨a', p'⟩, msg, ct⟩
  dsimp only at hr ⊢
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨rfl, rfl⟩
    rw [hc] at hr
    obtain rfl := Option.some.inj hr
    exact ⟨rfl, rfl⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, rfl⟩

theorem find?_inTransit_none [DecidableEq AD] [DecidableEq C]
    (pubOf : C → Option Pub) (l : List (Record (AD × Pub) M (ℕ × C)))
    (hl : ∀ r ∈ l, pubOf r.ct.2 = some r.ad.2) (a : AD) (c : ℕ × C)
    (hc : pubOf c.2 = none) :
    (l.map mapRecord).find? (fun r => r.ad == a && r.ct == c) = none := by
  rw [List.find?_eq_none]
  intro r hr
  rcases List.mem_map.mp hr with ⟨r₀, hr₀, rfl⟩
  simp only [mapRecord, Bool.and_eq_true, beq_iff_eq, not_and]
  intro _ hct
  have h := hl r₀ hr₀
  rw [hct, hc] at h
  cases h

theorem find?_inTransit_some [DecidableEq AD] [DecidableEq Pub] [DecidableEq C]
    (pubOf : C → Option Pub) (l : List (Record (AD × Pub) M (ℕ × C)))
    (hl : ∀ r ∈ l, pubOf r.ct.2 = some r.ad.2) (a : AD) (p : Pub) (c : ℕ × C)
    (hc : pubOf c.2 = some p) :
    (l.map mapRecord).find? (fun r => r.ad == a && r.ct == c) =
      (l.find? (fun r => r.ad == (a, p) && r.ct == c)).map mapRecord := by
  rw [List.find?_map]
  congr 1
  induction l with
  | nil => rfl
  | cons r rs ih =>
    have hr := match_record_eq (hl r List.mem_cons_self) a p c hc
    simp only [List.find?_cons, Function.comp_apply, mapRecord]
    rw [hr]
    split
    · rfl
    · exact ih (fun r' hr' => hl r' (List.mem_cons_of_mem r hr'))

theorem any_inTransit_none_eq_false [DecidableEq AD] [DecidableEq C]
    (pubOf : C → Option Pub) (l : List (Record (AD × Pub) M (ℕ × C)))
    (hl : ∀ r ∈ l, pubOf r.ct.2 = some r.ad.2) (a : AD) (c : ℕ × C)
    (hc : pubOf c.2 = none) :
    (l.map mapRecord).any (fun r => r.ad == a && r.ct == c) = false := by
  rw [List.any_map, List.any_eq_false]
  intro r hr
  simp only [Function.comp_apply, mapRecord, Bool.and_eq_true, beq_iff_eq, not_and]
  intro _ hct
  have h := hl r hr
  rw [hct, hc] at h
  cases h

theorem any_inTransit_some_eq [DecidableEq AD] [DecidableEq Pub] [DecidableEq C]
    (pubOf : C → Option Pub) (l : List (Record (AD × Pub) M (ℕ × C)))
    (hl : ∀ r ∈ l, pubOf r.ct.2 = some r.ad.2) (a : AD) (p : Pub) (c : ℕ × C)
    (hc : pubOf c.2 = some p) :
    (l.map mapRecord).any (fun r => r.ad == a && r.ct == c) =
      l.any (fun r => r.ad == (a, p) && r.ct == c) := by
  rw [List.any_map]
  induction l with
  | nil => rfl
  | cons r rs ih =>
    have hr := match_record_eq (hl r List.mem_cons_self) a p c hc
    simp only [List.any_cons, Function.comp_apply, mapRecord, hr,
      ih (fun r' hr' => hl r' (List.mem_cons_of_mem r hr'))]

end StateLemmas

section SchemeLemmas

variable (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) (pubOf : C → Option Pub)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

abbrev fsPubMsg := fromAEADPRG (ae.movePubPartToAD pubOf) G maxSkip
abbrev fsReassoc := fromAEADPRG (reassoc ae) G maxSkip

theorem mapState_initState (k : CK) (b : Bool) :
    mapState (initState (fsReassoc ae G maxSkip) k b) =
      initState (fsPubMsg ae pubOf G maxSkip) k b := rfl

theorem inv_initState (k : CK) (b : Bool) :
    Inv pubOf false (initState (fsReassoc ae G maxSkip) k b) :=
  ⟨rfl, fun _ h => nomatch h⟩

theorem receive_pubMsg_none (v : RatchetReceiverState CK MK) (a : AD) (c : ℕ × C)
    (hc : pubOf c.2 = none) :
    (fsPubMsg ae pubOf G maxSkip).receive v a c = none := by
  rcases c with ⟨i, e⟩
  dsimp only at hc
  simp only [fsPubMsg, fromAEADPRG, AEADScheme.movePubPartToAD, hc]
  cases v.skippedKeys.lookup i with
  | some key => rfl
  | none =>
    split_ifs <;> rfl

theorem receive_pubMsg_some (v : RatchetReceiverState CK MK) (a : AD) (p : Pub) (c : ℕ × C)
    (hc : pubOf c.2 = some p) :
    (fsPubMsg ae pubOf G maxSkip).receive v a c =
      ((fsReassoc ae G maxSkip).receive v (a, p) c).map
        (fun x => (x.1, x.2.1, (p, x.2.2))) := by
  rcases c with ⟨i, e⟩
  dsimp only at hc
  simp only [fsPubMsg, fsReassoc, fromAEADPRG, AEADScheme.movePubPartToAD, reassoc, hc]
  cases v.skippedKeys.lookup i with
  | some key =>
    simp only [Option.map_map]
    rfl
  | none =>
    split_ifs
    · rfl
    · simp only [Option.map_map]
      rfl

end SchemeLemmas

section PureTransitions

variable (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) (pubOf : C → Option Pub)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

abbrev RState (CK MK AD M C : Type) :=
  State (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M C

theorem transmit_mapState (st : RState CK MK (AD × Pub) M (ℕ × C)) (a : AD) (pm : Pub × M) :
    transmit (fsPubMsg ae pubOf G maxSkip) (mapState st) a pm =
      ((transmit (fsReassoc ae G maxSkip) st (a, pm.1) pm.2).1,
        mapState (transmit (fsReassoc ae G maxSkip) st (a, pm.1) pm.2).2) := by
  rcases pm with ⟨p, m⟩
  unfold transmit
  rw [mapState_ended]
  split <;> rfl

theorem challenge_mapState (st : RState CK MK (AD × Pub) M (ℕ × C))
    (a : AD) (pm₀ pm₁ : Pub × M) (hp : pm₀.1 = pm₁.1) :
    challenge (fsPubMsg ae pubOf G maxSkip) (mapState st) a pm₀ pm₁ =
      ((challenge (fsReassoc ae G maxSkip) st (a, pm₀.1) pm₀.2 pm₁.2).1,
        mapState (challenge (fsReassoc ae G maxSkip) st (a, pm₀.1) pm₀.2 pm₁.2).2) := by
  rcases pm₀ with ⟨p₀, m₀⟩
  rcases pm₁ with ⟨p₁, m₁⟩
  rcases st with ⟨ss, rs, b, lsi, sca, ri, ended, win, it, cit⟩
  dsimp only at hp
  subst hp
  unfold challenge
  cases b <;> cases ended <;> cases sca <;> rfl

theorem corruptSender_mapState (st : RState CK MK (AD × Pub) M (ℕ × C)) :
    corruptSender (mapState st) = ((corruptSender st).1, mapState (corruptSender st).2) := by
  unfold corruptSender
  rw [mapState_ended]
  split <;> rfl

theorem corruptSender_inv (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C))
    (hI : Inv pubOf ended st) : Inv pubOf ended (corruptSender st).2 := by
  unfold corruptSender
  split
  · exact hI
  · exact ⟨hI.1, hI.2⟩

theorem any_isCompromised_mapState (st : RState CK MK (AD × Pub) M (ℕ × C)) :
    (mapState st).inTransit.any (fun r => !(mapState st).isCompromised r.idx) =
      st.inTransit.any (fun r => !st.isCompromised r.idx) := by
  change (st.inTransit.map mapRecord).any (fun r => !st.isCompromised r.idx) = _
  rw [List.any_map]
  rfl

theorem corruptReceiver_mapState (st : RState CK MK (AD × Pub) M (ℕ × C)) :
    corruptReceiver (mapState st) = ((corruptReceiver st).1, mapState (corruptReceiver st).2) := by
  unfold corruptReceiver
  rw [any_isCompromised_mapState, mapState_ended, mapState_challengesInTransit]
  split <;> rfl

theorem corruptReceiver_inv (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C))
    (hI : Inv pubOf ended st) :
    Inv pubOf (if (corruptReceiver st).1.isSome then true else ended) (corruptReceiver st).2 := by
  unfold corruptReceiver
  split
  · exact hI
  · exact ⟨rfl, hI.2⟩

theorem deliver_mapState_none [DecidableEq AD] [DecidableEq Pub] [DecidableEq M] [DecidableEq C]
    (st : RState CK MK (AD × Pub) M (ℕ × C))
    (hI : ∀ r ∈ st.inTransit, pubOf r.ct.2 = some r.ad.2)
    (a : AD) (c : ℕ × C) (hc : pubOf c.2 = none) :
    deliver (fsPubMsg ae pubOf G maxSkip) (mapState st) a c = (none, mapState st) := by
  unfold deliver
  have hfind : (mapState st).inTransit.find? (fun r => r.ad == a && r.ct == c) = none :=
    find?_inTransit_none pubOf st.inTransit hI a c hc
  rw [hfind, mapState_ended]
  split <;> rfl

theorem find?_ad_eq [DecidableEq AD] [DecidableEq Pub] [DecidableEq C]
    {l : List (Record (AD × Pub) M (ℕ × C))} {a : AD} {p : Pub} {c : ℕ × C}
    {r : Record (AD × Pub) M (ℕ × C)}
    (hf : l.find? (fun r => r.ad == (a, p) && r.ct == c) = some r) :
    r.ad = (a, p) := by
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp.1

theorem deliver_mapState_some [DecidableEq AD] [DecidableEq Pub] [DecidableEq M] [DecidableEq C]
    (st : RState CK MK (AD × Pub) M (ℕ × C))
    (hI : ∀ r ∈ st.inTransit, pubOf r.ct.2 = some r.ad.2)
    (a : AD) (p : Pub) (c : ℕ × C) (hc : pubOf c.2 = some p) :
    deliver (fsPubMsg ae pubOf G maxSkip) (mapState st) a c =
      (((deliver (fsReassoc ae G maxSkip) st (a, p) c).1).map (withPub p),
        mapState (deliver (fsReassoc ae G maxSkip) st (a, p) c).2) := by
  unfold deliver
  have hfind : (mapState st).inTransit.find? (fun r => r.ad == a && r.ct == c) =
      (st.inTransit.find? (fun r => r.ad == (a, p) && r.ct == c)).map mapRecord :=
    find?_inTransit_some pubOf st.inTransit hI a p c hc
  simp only [hfind, mapState_ended]
  split
  · rfl
  · cases hf : st.inTransit.find? (fun r => r.ad == (a, p) && r.ct == c) with
    | none => rfl
    | some r =>
      have had : r.ad = (a, p) := find?_ad_eq hf
      rcases r with ⟨r_idx, ⟨r_a, r_p⟩, r_msg, r_ct⟩
      obtain ⟨ha, hp⟩ := Prod.mk.inj had
      subst r_a r_p
      dsimp only [Option.map, mapRecord]
      have hrec : (fsPubMsg ae pubOf G maxSkip).receive (mapState st).receiverState a c =
          ((fsReassoc ae G maxSkip).receive st.receiverState (a, p) c).map
            (fun x => (x.1, x.2.1, (p, x.2.2))) :=
        receive_pubMsg_some ae pubOf G maxSkip st.receiverState a p c hc
      rw [hrec]
      cases (fsReassoc ae G maxSkip).receive st.receiverState (a, p) c with
      | none => rfl
      | some res =>
        rcases res with ⟨rs', i', m'⟩
        dsimp only [Option.map, withPub]
        have hne : ((p, m') != (p, r_msg)) = (m' != r_msg) := by
          rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, Prod.mk.injEq, not_and]
          exact ⟨fun h => h rfl, fun h _ => h⟩
        rw [hne, ← mapState_removeFromTransit]
        change (some (ReceiveResult.accepted i'
            (if st.challengesInTransit.contains r_idx then none else some (p, m'))), _) = _
        cases st.challengesInTransit.contains r_idx <;> rfl

theorem deliver_inv [DecidableEq AD] [DecidableEq Pub] [DecidableEq M] [DecidableEq C]
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st)
    (ap : AD × Pub) (c : ℕ × C) :
    Inv pubOf ended (deliver (fsReassoc ae G maxSkip) st ap c).2 := by
  unfold deliver
  split
  · exact hI
  · split
    · exact hI
    · split
      · exact ⟨hI.1, hI.2⟩
      · exact Inv.removeFromTransit ⟨hI.1, hI.2⟩ _

theorem inject_mapState_none [DecidableEq AD] [DecidableEq C]
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st)
    (a : AD) (c : ℕ × C) (hc : pubOf c.2 = none) :
    inject (fsPubMsg ae pubOf G maxSkip) (mapState st) a c =
      (if ended then none else some ReceiveResult.rejected, mapState st) := by
  unfold inject
  have hany : (mapState st).inTransit.any (fun r => r.ad == a && r.ct == c) = false :=
    any_inTransit_none_eq_false pubOf st.inTransit hI.2 a c hc
  have hrec := receive_pubMsg_none ae pubOf G maxSkip (mapState st).receiverState a c hc
  simp only [hany, hrec, Bool.or_false, hI.1, mapState_ended]
  split <;> rfl

theorem inject_mapState_some [DecidableEq AD] [DecidableEq Pub] [DecidableEq C]
    (st : RState CK MK (AD × Pub) M (ℕ × C))
    (hI : ∀ r ∈ st.inTransit, pubOf r.ct.2 = some r.ad.2)
    (a : AD) (p : Pub) (c : ℕ × C) (hc : pubOf c.2 = some p) :
    inject (fsPubMsg ae pubOf G maxSkip) (mapState st) a c =
      (((inject (fsReassoc ae G maxSkip) st (a, p) c).1).map (withPub p),
        mapState (inject (fsReassoc ae G maxSkip) st (a, p) c).2) := by
  unfold inject
  have hany : (mapState st).inTransit.any (fun r => r.ad == a && r.ct == c) =
      st.inTransit.any (fun r => r.ad == (a, p) && r.ct == c) :=
    any_inTransit_some_eq pubOf st.inTransit hI a p c hc
  have hrec : (fsPubMsg ae pubOf G maxSkip).receive (mapState st).receiverState a c =
      ((fsReassoc ae G maxSkip).receive st.receiverState (a, p) c).map
        (fun x => (x.1, x.2.1, (p, x.2.2))) :=
    receive_pubMsg_some ae pubOf G maxSkip st.receiverState a p c hc
  simp only [hany, hrec, mapState_ended]
  split
  · rfl
  · cases (fsReassoc ae G maxSkip).receive st.receiverState (a, p) c with
    | none => rfl
    | some res =>
      rcases res with ⟨rs', i', m'⟩
      dsimp only [Option.map, withPub]
      rw [← mapState_removeFromTransit]
      rfl

theorem inject_inv [DecidableEq AD] [DecidableEq Pub] [DecidableEq C]
    (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st)
    (ap : AD × Pub) (c : ℕ × C) :
    Inv pubOf ended (inject (fsReassoc ae G maxSkip) st ap c).2 := by
  unfold inject
  split
  · exact hI
  · split
    · exact hI
    · exact Inv.removeFromTransit ⟨hI.1, hI.2⟩ _

end PureTransitions

section Sim

variable [DecidableEq AD] [DecidableEq Pub] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK ((ℕ × AD) × Pub) M C) (pubOf : C → Option Pub)
  (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

abbrev gameImpl {K SS RS AD' M' C' : Type} [DecidableEq AD'] [DecidableEq M'] [DecidableEq C']
    (fs : FSAEADScheme K SS RS AD' M' C') :
    QueryImpl (unifSpec + spec SS RS AD' M' C') (StateT (State SS RS AD' M' C') ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (State SS RS AD' M' C') ProbComp) +
    oracleImpl fs

theorem stateT_lift_run {m : Type → Type} [Monad m] {σ α : Type} (x : m α) (s : σ) :
    (StateT.lift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

abbrev pubOfPair (pubOf : C → Option Pub) (c : ℕ × C) : Option Pub := pubOf c.2

theorem step_corruptSender (u : Unit) (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C))
    (hI : Inv pubOf ended st) :
    ∃ ans ended' st',
      (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((pubRedImpl (pubOfPair pubOf) (.inr (.inl (.inl (.inl (.inr u)))))).run ended)).run st =
        pure ((ans, ended'), st') ∧
      (gameImpl (fsPubMsg ae pubOf G maxSkip)
        (.inr (.inl (.inl (.inl (.inr u)))))).run (mapState st) =
        pure (ans, mapState st') ∧
      Inv pubOf ended' st' := by
  refine ⟨(corruptSender st).1, ended, (corruptSender st).2, ?_, ?_,
    corruptSender_inv pubOf ended st hI⟩
  · simp [pubRedImpl, corruptSenderQuery, gameImpl, oracleImpl,
      corruptSenderImpl, StateT.run_modifyGet]
  · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, QueryImpl.add_apply_inl,
      corruptSenderImpl, StateT.run_modifyGet, corruptSender_mapState]

theorem step_corruptReceiver (u : Unit) (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C))
    (hI : Inv pubOf ended st) :
    ∃ ans ended' st',
      (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((pubRedImpl (pubOfPair pubOf) (.inr (.inl (.inl (.inr u))))).run ended)).run st =
        pure ((ans, ended'), st') ∧
      (gameImpl (fsPubMsg ae pubOf G maxSkip)
        (.inr (.inl (.inl (.inr u))))).run (mapState st) =
        pure (ans, mapState st') ∧
      Inv pubOf ended' st' := by
  refine ⟨(corruptReceiver st).1, if (corruptReceiver st).1.isSome then true else ended,
    (corruptReceiver st).2, ?_, ?_, corruptReceiver_inv pubOf ended st hI⟩
  · have hrun : (pubRedImpl (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (AD := AD) (M := M) (pubOfPair pubOf) (.inr (.inl (.inl (.inr u))))).run ended =
      (corruptReceiverQuery >>= fun r =>
        pure (r, if r.isSome then true else ended)) := by
      unfold pubRedImpl
      simp only [StateT.run_bind, stateT_lift_run, bind_assoc]
      refine bind_congr fun r => ?_
      cases r <;> simp
    rw [hrun]
    simp [corruptReceiverQuery, gameImpl, oracleImpl, corruptReceiverImpl, StateT.run_modifyGet]
  · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, QueryImpl.add_apply_inl,
      corruptReceiverImpl, StateT.run_modifyGet, corruptReceiver_mapState]

theorem step_deliver (a : AD) (c : ℕ × C) (ended : Bool)
    (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st) :
    ∃ ans ended' st',
      (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((pubRedImpl (pubOfPair pubOf) (.inr (.inl (.inr (a, c))))).run ended)).run st =
        pure ((ans, ended'), st') ∧
      (gameImpl (fsPubMsg ae pubOf G maxSkip)
        (.inr (.inl (.inr (a, c))))).run (mapState st) =
        pure (ans, mapState st') ∧
      Inv pubOf ended' st' := by
  cases hc : pubOf c.2 with
  | none =>
    refine ⟨none, ended, st, ?_, ?_, hI⟩
    · simp [pubRedImpl, pubOfPair, hc]
    · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, QueryImpl.add_apply_inl,
        deliverImpl, StateT.run_modifyGet, deliver_mapState_none ae pubOf G maxSkip st hI.2 a c hc]
  | some p =>
    refine ⟨((deliver (fsReassoc ae G maxSkip) st (a, p) c).1).map (withPub p), ended,
      (deliver (fsReassoc ae G maxSkip) st (a, p) c).2, ?_, ?_,
      deliver_inv ae pubOf G maxSkip ended st hI (a, p) c⟩
    · simp [pubRedImpl, pubOfPair, hc, deliverQuery, gameImpl, oracleImpl, deliverImpl,
        StateT.run_modifyGet]
    · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, QueryImpl.add_apply_inl,
        deliverImpl, StateT.run_modifyGet,
        deliver_mapState_some ae pubOf G maxSkip st hI.2 a p c hc]

theorem step_inject (a : AD) (c : ℕ × C) (ended : Bool)
    (st : RState CK MK (AD × Pub) M (ℕ × C)) (hI : Inv pubOf ended st) :
    ∃ ans ended' st',
      (simulateQ (gameImpl (fsReassoc ae G maxSkip))
        ((pubRedImpl (pubOfPair pubOf) (.inr (.inr (a, c)))).run ended)).run st =
        pure ((ans, ended'), st') ∧
      (gameImpl (fsPubMsg ae pubOf G maxSkip)
        (.inr (.inr (a, c)))).run (mapState st) =
        pure (ans, mapState st') ∧
      Inv pubOf ended' st' := by
  cases hc : pubOf c.2 with
  | none =>
    refine ⟨if ended then none else some .rejected, ended, st, ?_, ?_, hI⟩
    · simp [pubRedImpl, pubOfPair, hc]
    · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, injectImpl, StateT.run_modifyGet,
        inject_mapState_none ae pubOf G maxSkip ended st hI a c hc]
  | some p =>
    refine ⟨((inject (fsReassoc ae G maxSkip) st (a, p) c).1).map (withPub p), ended,
      (inject (fsReassoc ae G maxSkip) st (a, p) c).2, ?_, ?_,
      inject_inv ae pubOf G maxSkip ended st hI (a, p) c⟩
    · simp [pubRedImpl, pubOfPair, hc, injectQuery, gameImpl, oracleImpl, injectImpl,
        StateT.run_modifyGet]
    · simp only [gameImpl, QueryImpl.add_apply_inr, oracleImpl, injectImpl, StateT.run_modifyGet,
        inject_mapState_some ae pubOf G maxSkip st hI.2 a p c hc]

theorem step_inl (n : ℕ) (ended : Bool) (st : RState CK MK (AD × Pub) M (ℕ × C)) :
    (simulateQ (gameImpl (fsReassoc ae G maxSkip))
      ((pubRedImpl (SS := RatchetSenderState CK) (RS := RatchetReceiverState CK MK)
        (AD := AD) (M := M) (pubOfPair pubOf) (.inl n)).run ended)).run st =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure ((u, ended), st) := by
  simp [pubRedImpl, gameImpl]

theorem step_inl_pubMsg (n : ℕ) (st : RState CK MK (AD × Pub) M (ℕ × C)) :
    (gameImpl (fsPubMsg ae pubOf G maxSkip) (.inl n)).run (mapState st) =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
        fun u => pure (u, mapState st) := by
  simp [gameImpl]

end Sim

section QueryBounds

variable {SS RS : Type}

theorem query_eq_liftM (t : (unifSpec + spec SS RS (AD × Pub) M C).Domain) :
    (query (spec := unifSpec + spec SS RS (AD × Pub) M C) t :
      AdversaryComp SS RS (AD × Pub) M C _) =
      liftM ((unifSpec + spec SS RS (AD × Pub) M C).query t) := rfl

theorem pubRed_makesAtMostQueries (pubOf : C → Option Pub)
    (A : Adversary SS RS AD (Pub × M) C) {q : ℕ}
    (hq : MakesAtMostQueries A q) : MakesAtMostQueries (pubRed pubOf A) q := by
  unfold MakesAtMostQueries pubRed
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  refine IsQueryBoundP.simulateQ_run_of_step hq ?_ ?_ false
  · rintro (n | o) hp ended
    · cases hp
    · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [corruptSenderQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [StateT.run_bind, stateT_lift_run, bind_assoc]
        rw [corruptReceiverQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        refine ⟨Or.inr Nat.zero_lt_one, fun r => ?_⟩
        cases r <;> simp
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [deliverQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp [StateT.run_get]
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [injectQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
  · rintro (n | o) hnp ended
    · unfold pubRedImpl
      simp only [stateT_lift_run]
      rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by rintro ⟨⟩), fun _ => by simp⟩
    · exact absurd rfl hnp

theorem pubRed_adClassConst {κ : Type} [DecidableEq κ] (cls : AD → κ) (pubOf : C → Option Pub)
    (A : Adversary SS RS AD (Pub × M) C) (hcls : AllQueriesInOneADClass cls A) :
    AllQueriesInOneADClass (fun ap : AD × Pub => cls ap.1) (pubRed pubOf A) := by
  rcases hcls with ⟨k₀, hk₀⟩
  refine ⟨k₀, ?_⟩
  unfold pubRed
  rw [StateT.run'_eq]
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  refine IsQueryBoundP.simulateQ_run_of_step hk₀ ?_ ?_ false
  · rintro (n | o) hp ended
    · simp [queryADOutsideClass] at hp
    · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · simp [queryADOutsideClass] at hp
      · simp [queryADOutsideClass] at hp
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [deliverQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp [StateT.run_get]
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [injectQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inr Nat.zero_lt_one, fun _ => by simp⟩
  · rintro (n | o) hnp ended
    · unfold pubRedImpl
      simp only [stateT_lift_run]
      rw [query_eq_liftM, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [queryADOutsideClass]), fun _ => by simp⟩
    · rcases o with ((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, c⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [transmitQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simpa [queryADOutsideClass] using hnp), fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [challengeQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simpa [queryADOutsideClass] using hnp), fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [stateT_lift_run]
        rw [corruptSenderQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [queryADOutsideClass]), fun _ => by simp⟩
      · unfold pubRedImpl
        simp only [StateT.run_bind, stateT_lift_run, bind_assoc]
        rw [corruptReceiverQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl (by simp [queryADOutsideClass]), fun r => ?_⟩
        cases r <;> simp
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [deliverQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simpa [queryADOutsideClass] using hnp), fun _ => by simp⟩
      · unfold pubRedImpl
        dsimp only
        cases pubOf c with
        | none =>
          simp [StateT.run_get]
        | some p =>
          simp only [stateT_lift_run, bind_assoc]
          rw [injectQuery, query_eq_liftM, isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simpa [queryADOutsideClass] using hnp), fun _ => by simp⟩

end QueryBounds

end CryptoGames.LibsignalSM.Proofs.PubToAD
