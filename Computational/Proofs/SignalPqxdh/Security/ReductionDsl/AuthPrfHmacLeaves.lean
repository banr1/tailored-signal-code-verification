/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEnc
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaShallow
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaLeaves

/-!
# Leaf Invariants of the Shallow `PrfHmac` Step

Proves `hmPre_leaves`: starting from `HmInv n hst ms`, every leaf of `hmPre S jt q hst ms`
satisfies `HmPreLeaf n`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf SignalPqxdh.Security.ReductionDsl.AuthAead
open OracleSpec OracleComp

section Leaves

variable (S : Setup)

theorem AllLeaves.map' {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : α → Prop} {Q : β → Prop} {m : OracleComp spec α} (f : α → β)
    (hm : AllLeaves P m) (hf : ∀ a, P a → Q (f a)) : AllLeaves Q (f <$> m) := by
  rw [map_eq_bind_pure_comp]
  exact AllLeaves.bind hm (fun a ha => AllLeaves.pure (hf a ha))

/-! ### Multi-key game steps -/

theorem hmKeyP_leaves (n i : Nat) (st : PrfHmacMuState) (h : st.keys.length ≤ n) :
    AllLeaves (fun x : (Nat × MessageKeys) × PrfHmacMuState => x.2.keys.length ≤ n + 1 ∧
      x.2.chal = st.chal ∧ x.2.pending = st.pending) (hmKeyP i st) := by
  unfold hmKeyP
  split
  · exact AllLeaves.pure ⟨Nat.le_succ_of_le h, rfl, rfl⟩
  · exact AllLeaves.bind_const _ (fun _ =>
      AllLeaves.pure ⟨by simp only [List.length_cons]; omega, rfl, rfl⟩)

theorem hmForgeP_leaves (n jt i : Nat) (ad ct : Bytes) (st : PrfHmacMuState)
    (h : MuBounded n st) :
    AllLeaves (fun x : Bool × PrfHmacMuState => MuBounded (n + 1) x.2)
      (hmForgeP jt i ad ct st) := by
  unfold hmForgeP
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (h.mono (Nat.le_succ n))) (fun _ => ?_)
  refine AllLeaves.bind (hmKeyP_leaves n i st h.keys_le) (fun x hx => ?_)
  obtain ⟨⟨r, mk⟩, st'⟩ := x
  obtain ⟨hk, hc, hp⟩ := hx
  have hc' : st'.chal.length ≤ n + 1 := by rw [hc]; have := h.chal_le; omega
  have hp' : st'.pending.length ≤ n := by rw [hp]; exact h.pending_le
  dsimp only
  split_ifs
  · exact AllLeaves.pure ⟨hk, hc', by simp only [List.length_cons]; omega⟩
  · exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure ⟨hk, hc', Nat.le_succ_of_le hp'⟩)
  · exact AllLeaves.pure ⟨hk, hc', Nat.le_succ_of_le hp'⟩

def EncOk (n : Nat) : (Option Bytes × PrfHmacMuState) ⊕ HmEncCont → Prop
  | .inl r => MuBounded (n + 1) r.2
  | .inr c => c.st.keys.length ≤ n + 1 ∧ c.st.chal.length ≤ n ∧ c.st.pending.length ≤ n

theorem HmEncCont.post_bounded (n : Nat) (c : HmEncCont) (t : Bytes)
    (hk : c.st.keys.length ≤ n + 1) (hc : c.st.chal.length ≤ n) (hp : c.st.pending.length ≤ n) :
    MuBounded (n + 1) (c.post t).2 := by
  refine ⟨hk, ?_, ?_⟩
  · simp only [HmEncCont.post, List.length_cons]; omega
  · simp only [HmEncCont.post]
    exact Nat.le_trans (List.length_filter_le _ _) (by omega)

theorem hmEncPre_leaves (n jt i : Nat) (ad pt : Bytes) (st : PrfHmacMuState)
    (h : MuBounded n st) : AllLeaves (EncOk n) (hmEncPre jt i ad pt st) := by
  unfold hmEncPre
  split
  · exact AllLeaves.pure (h.mono (Nat.le_succ n))
  refine AllLeaves.bind (hmKeyP_leaves n i st h.keys_le) (fun x hx => ?_)
  obtain ⟨⟨r, mk⟩, st'⟩ := x
  obtain ⟨hk, hc, hp⟩ := hx
  have hc' : st'.chal.length ≤ n := by rw [hc]; exact h.chal_le
  have hp' : st'.pending.length ≤ n := by rw [hp]; exact h.pending_le
  dsimp only
  refine AllLeaves.bind_const _ (fun ct => ?_)
  split
  · exact AllLeaves.bind_const _ (fun t =>
      AllLeaves.pure (HmEncCont.post_bounded n _ t hk hc' hp'))
  split
  · exact AllLeaves.pure ⟨hk, hc', hp'⟩
  · exact AllLeaves.pure (show MuBounded (n + 1) _ from
      ⟨hk, by simp only [List.length_cons]; omega, Nat.le_succ_of_le hp'⟩)

/-! ### Send -/

def PrepIntOk {S : Setup} (n : Nat) : Option (AuthIntSendPrep S) → Prop
  | none => True
  | some p => p.roCache'.length ≤ n + 1 ∧ p.rootRoCache'.length ≤ n + 1

theorem prepAuthIntSendPrim_leaves (n : Nat) (sid : SessionId S)
    (u : Fin S.N_id) (b : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
    (hB : AuthListsBounded n hst) :
    AllLeaves (PrepIntOk n) (prepAuthIntSendPrim S sid u b m0 m1 hst) := by
  unfold prepAuthIntSendPrim
  dsimp only
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  split
  rotate_left
  · exact AllLeaves.pure trivial
  refine AllLeaves.bind_const _ (fun peer => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun kosk => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun kem => ?_)
  rcases kem with _ | ⟨ss, kemCt⟩
  · exact AllLeaves.pure trivial
  dsimp only
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun prov => ?_)
  refine AllLeaves.bind_const _ (fun spkHonIdeal => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun dr hdr => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact AllLeaves.bind_const _ (fun _ =>
        AllLeaves.pure (Nat.le_trans hB.roCache_le (Nat.le_succ n)))
    · exact AllLeaves.embedUnif (aeadHkdfRoPure_length_le _ _ hB.roCache_le)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun rr hrr => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.pure (Nat.le_trans hB.rootRoCache_le (Nat.le_succ n))))
    · exact AllLeaves.embedUnif (aeadRootKdfRoPure_length_le _ _ _ hB.rootRoCache_le)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun spqr => ?_)
  rcases spqr with _ | ⟨_, _, _⟩
  · exact AllLeaves.pure trivial
  · exact AllLeaves.pure ⟨hdr, hrr⟩

theorem finishAuthIntSendPure_inv (n : Nat) (sid : SessionId S) (b : PreKeyBundleInput)
    (m0 m1 : Bytes) (p : AuthIntSendPrep S) (mk : MessageKeys) (ct : Bytes)
    (hst : AuthHybridStateFixed S) (hI : CpaInv n hst) (hro : p.roCache'.length ≤ n + 1)
    (hroot : p.rootRoCache'.length ≤ n + 1) :
    CpaInv (n + 1) (finishAuthIntSendPure sid b m0 m1 p mk ct hst).2 := by
  try dsimp only
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩, h17⟩, hw⟩ := hI
  rcases hb : p.isIdealSend with _ | _ <;>
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩ <;>
    simp only [finishAuthIntSendPure, hb, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem hmSendPre_leaves (n jt : Nat) (sid : SessionId S) (u : Fin S.N_id)
    (b : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hI : HmInv n hst ms) :
    AllLeaves (HmPreLeaf n) (hmSendPre S jt sid u b m0 m1 hst ms) := by
  have hC : CpaInv n hst := ⟨hI.bnd, hI.won⟩
  unfold hmSendPre
  refine AllLeaves.bind (prepAuthIntSendPrim_leaves S n sid u b m0 m1 hst hI.bnd)
    (fun p? hp => ?_)
  rcases p? with _ | p
  · exact AllLeaves.pure (hI.mono (Nat.le_succ n))
  obtain ⟨hro, hroot⟩ := hp
  have hF := fun mk ct => finishAuthIntSendPure_inv S n sid b m0 m1 p mk ct hst hC hro hroot
  dsimp only
  unfold hmSendTail
  refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
  · refine AllLeaves.bind (hmEncPre_leaves n jt _ _ _ ms hI.mu) (fun e he => ?_)
    rcases e with ⟨ct?, ms'⟩ | c
    · exact AllLeaves.pure (show HmInv (n + 1) _ _ from
        ⟨(hF _ _).bnd, (hF _ _).won, he⟩)
    · obtain ⟨hk, hc, hp⟩ := he
      refine AllLeaves.pure (show HmSendCont.Bounded n _ from ⟨hp, fun t => ?_⟩)
      exact ⟨(hF _ _).bnd, (hF _ _).won, HmEncCont.post_bounded n c t hk hc hp⟩
  · refine AllLeaves.bind_const _ (fun mk => AllLeaves.bind_const _ (fun ct => ?_))
    exact AllLeaves.pure (show HmInv (n + 1) _ _ from
      ⟨(hF _ _).bnd, (hF _ _).won, hI.mu.mono (Nat.le_succ n)⟩)

/-! ### Receive -/

def RecvPrepOk {S : Setup} (n : Nat) (hst : AuthHybridState S) : Option (HmRecvData S) → Prop
  | none => True
  | some d => d.usedTriples'.length ≤ n + 1 ∧
      ∃ r : RecvKemRecord, d.hstDec = { hst with recvKemRecs := r :: hst.recvKemRecs }

theorem hmFinishPrepP_leaves (n kVal jVal : Nat) (kEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (opkSk? opkPk? : Option Bytes) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (hU : hst.base.seenKyberBaseKeys.length ≤ n) :
    AllLeaves (RecvPrepOk n hst)
      (hmFinishPrepP S kVal jVal kEntry bEntry opkSk? opkPk? msg hst) := by
  unfold hmFinishPrepP
  have hT := checkAndMarkKyberUsed_length_le hst.base.seenKyberBaseKeys kVal msg.hdr.pqspkId
    msg.hdr.spkId msg.hdr.ekAPk hU
  dsimp only
  generalize checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys kVal msg.hdr.pqspkId msg.hdr.spkId
    msg.hdr.ekAPk = rp at hT ⊢
  obtain ⟨replayOk, used'⟩ := rp
  dsimp only at hT ⊢
  refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun ss? => ?_)
  rcases ss? with _ | ss
  · exact AllLeaves.pure trivial
  dsimp only
  refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
    AllLeaves.bind_const _ (fun _ => ?_)))
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  exact AllLeaves.pure ⟨hT, _, rfl⟩

theorem hmRecvOPKPrepP_leaves (n : Nat) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) (hU : hst.base.seenKyberBaseKeys.length ≤ n) :
    AllLeaves (RecvPrepOk n hst) (hmRecvOPKPrepP S k j o msg hst) := by
  unfold hmRecvOPKPrepP
  dsimp only
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  split
  · refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
    exact hmFinishPrepP_leaves S n _ _ _ _ _ _ msg hst hU
  · exact AllLeaves.pure trivial

theorem hmRecvNoOPKPrepP_leaves (n : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (msg : PreKeyMsg) (hst : AuthHybridState S)
    (hU : hst.base.seenKyberBaseKeys.length ≤ n) :
    AllLeaves (RecvPrepOk n hst) (hmRecvNoOPKPrepP S k j l msg hst) := by
  unfold hmRecvNoOPKPrepP
  dsimp only
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure trivial) (fun _ => ?_)
  split
  · exact hmFinishPrepP_leaves S n _ _ _ _ _ _ msg hst hU
  · exact AllLeaves.pure trivial

def SchedPrepOk {S : Setup} (n : Nat) : Option (AuthIntRecvSchedPrep S) → Prop
  | none => True
  | some sp => sp.roCache'.length ≤ n + 1 ∧ sp.rootRoCache'.length ≤ n + 1

theorem prepAuthIntRecvSchedPrim_leaves (n : Nat) (hstDec : AuthHybridState S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes) (secrets : Bytes)
    (msg : PreKeyMsg) (hro : hstDec.base.roCache.length ≤ n)
    (hroot : hstDec.base.rootRoCache.length ≤ n) :
    AllLeaves (SchedPrepOk n)
      (prepAuthIntRecvSchedPrim S hstDec kEntry bEntry opkPk? secrets msg) := by
  unfold prepAuthIntRecvSchedPrim
  dsimp only
  refine AllLeaves.bind_const _ (fun sender => ?_)
  refine AllLeaves.bind_const _ (fun matched => ?_)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun dr hdr => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · rcases matched with _ | s
      · exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (Nat.le_trans hro (Nat.le_succ n)))
      · exact AllLeaves.pure (Nat.le_trans hro (Nat.le_succ n))
    · exact AllLeaves.embedUnif (aeadHkdfRoPure_length_le _ _ hro)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun sameEph => ?_)
  refine AllLeaves.bind (P := fun x => x.2.length ≤ n + 1) ?_ (fun rr hrr => ?_)
  · refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
    · rcases matched with _ | s
      · exact AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
          AllLeaves.pure (Nat.le_trans hroot (Nat.le_succ n))))
      · dsimp only
        refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
        · exact AllLeaves.pure (Nat.le_trans hroot (Nat.le_succ n))
        · exact AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
            AllLeaves.pure (Nat.le_trans hroot (Nat.le_succ n))))
    · exact AllLeaves.embedUnif (aeadRootKdfRoPure_length_le _ _ _ hroot)
  refine AllLeaves.bind_const _ (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun spqr => ?_)
  rcases spqr with _ | ⟨_, _⟩
  · exact AllLeaves.pure trivial
  · exact AllLeaves.pure ⟨hdr, hrr⟩

def SchedOk {S : Setup} (n : Nat) (x : (HmSchedOut × AuthMkSaltCache S) × PrfHmacMuState) :
    Prop :=
  x.1.2.length ≤ n + 1 ∧ MuBounded (n + 1) x.2 ∧
    ∀ dk rk1 ck pt ro root, x.1.1 = some (dk, rk1, ck, pt, ro, root) →
      ro.length ≤ n + 1 ∧ root.length ≤ n + 1

theorem hmSchedFinP_leaves (n jt : Nat) (kEntry : PrincipalEntry) (msg : PreKeyMsg)
    (recvCount : Nat) (cache : AuthMkSaltCache S) (sp : AuthIntRecvSchedPrep S)
    (ms : PrfHmacMuState) (hc : cache.length ≤ n) (hM : MuBounded n ms)
    (hsp : sp.roCache'.length ≤ n + 1 ∧ sp.rootRoCache'.length ≤ n + 1) :
    AllLeaves (SchedOk n) (hmSchedFinP jt kEntry msg recvCount cache sp ms) := by
  have hnone : ∀ (c : AuthMkSaltCache S) (m : PrfHmacMuState), c.length ≤ n + 1 →
      MuBounded (n + 1) m → SchedOk n ((none, c), m) :=
    fun _ _ h1 h2 => ⟨h1, h2, fun _ _ _ _ _ _ h => by cases h⟩
  have hsome : ∀ (dk : DRKey) (rk1 ck pt : Bytes), SchedOk n
      ((some (dk, rk1, ck, pt, sp.roCache', sp.rootRoCache'), cache), ms) :=
    fun _ _ _ _ => ⟨Nat.le_succ_of_le hc, hM.mono (Nat.le_succ n), fun _ _ _ _ _ _ h => by
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, -, -, rfl, rfl⟩ := h
      exact hsp⟩
  have hF : ∀ (i : Nat) (ad ct : Bytes) (c : AuthMkSaltCache S), c.length ≤ n + 1 →
      ∀ (k : Bool × PrfHmacMuState →
        OracleComp PrimBaseSpec ((HmSchedOut × AuthMkSaltCache S) × PrfHmacMuState)),
      (∀ x, MuBounded (n + 1) x.2 → k x = pure ((none, c), x.2)) →
      AllLeaves (SchedOk n) (hmForgeP jt i ad ct ms >>= k) := by
    intro i ad ct c hcl k hk
    refine AllLeaves.bind (hmForgeP_leaves n jt i ad ct ms hM) (fun x hx => ?_)
    rw [hk x hx]
    exact AllLeaves.pure (hnone _ _ hcl hx)
  have hc1 : cache.length ≤ n + 1 := Nat.le_succ_of_le hc
  unfold hmSchedFinP
  dsimp only
  refine AllLeaves.ite _ (fun _ => ?_) (fun _ => ?_)
  · rcases sp.matchedSess? with _ | s
    · exact hF _ _ _ _ hc1 _ (fun _ _ => rfl)
    · dsimp only
      split_ifs
      · exact AllLeaves.pure (hsome _ _ _ _)
      · exact hF _ _ _ _ hc1 _ (fun _ _ => rfl)
      · split
        · exact hF _ _ _ _ hc1 _ (fun _ _ => rfl)
        · exact hF _ _ _ _ (by simp only [List.length_cons]; omega) _ (fun _ _ => rfl)
      · exact hF _ _ _ _ hc1 _ (fun _ _ => rfl)
  · refine AllLeaves.bind_const _ (fun mk => AllLeaves.bind_const _ (fun pt? => ?_))
    rcases pt? with _ | pt
    · exact AllLeaves.pure (hnone _ _ hc1 (hM.mono (Nat.le_succ n)))
    · exact AllLeaves.pure (hsome _ _ _ _)

theorem hmSchedP_leaves (n jt : Nat) (hstDec : AuthHybridState S) (recvCount : Nat)
    (cache : AuthMkSaltCache S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) (ms : PrfHmacMuState)
    (hro : hstDec.base.roCache.length ≤ n) (hroot : hstDec.base.rootRoCache.length ≤ n)
    (hc : cache.length ≤ n) (hM : MuBounded n ms) :
    AllLeaves (SchedOk n)
      (hmSchedP S jt hstDec recvCount cache kEntry bEntry opkPk? secrets msg ms) := by
  unfold hmSchedP
  refine AllLeaves.bind (prepAuthIntRecvSchedPrim_leaves S n hstDec kEntry bEntry opkPk? secrets
    msg hro hroot) (fun sp? hsp => ?_)
  rcases sp? with _ | sp
  · exact AllLeaves.pure ⟨Nat.le_succ_of_le hc, hM.mono (Nat.le_succ n),
      fun _ _ _ _ _ _ h => by cases h⟩
  · exact hmSchedFinP_leaves S n jt kEntry msg recvCount cache sp ms hc hM hsp

theorem hmRecvTail_leaves (n jt : Nat) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (d : HmRecvData S)
    (fin : HmSchedOut → AuthResponse × AuthHybridState S)
    (hro : d.hstDec.base.roCache.length ≤ n) (hroot : d.hstDec.base.rootRoCache.length ≤ n)
    (hc : hst.mkSaltCache.length ≤ n) (hM : MuBounded n ms)
    (hfin : ∀ res?, (∀ dk rk1 ck pt ro root, res? = some (dk, rk1, ck, pt, ro, root) →
        ro.length ≤ n + 1 ∧ root.length ≤ n + 1) →
      AuthHybridListsBounded (n + 1) (fin res?).2 ∧ (fin res?).2.base.hasWonAuth = false) :
    AllLeaves (fun r : HmRes S => HmInv (n + 1) r.1.2 r.2) (hmRecvTail S jt msg hst ms d fin) := by
  unfold hmRecvTail
  refine AllLeaves.bind (hmSchedP_leaves S n jt d.hstDec hst.recvCount hst.mkSaltCache d.kEntry
    d.bEntry d.opkPk? d.secrets msg ms hro hroot hc hM) (fun x hx => ?_)
  obtain ⟨⟨res?, cache'⟩, ms'⟩ := x
  obtain ⟨hc', hM', hres⟩ := hx
  obtain ⟨hB, hw⟩ := hfin res? hres
  exact AllLeaves.pure ⟨⟨hB, hc'⟩, hw, hM'⟩

theorem finishErasedRecvOPK_inv (n : Nat) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (used' : List (Nat × KeyId × KeyId × Bytes)) (hon : Bool) (hst : AuthHybridState S)
    (r : RecvKemRecord) (hB : AuthHybridListsBounded n hst) (hw : hst.base.hasWonAuth = false)
    (hU : used'.length ≤ n + 1)
    (res? : HmSchedOut) (hres : ∀ dk rk1 ck pt ro root, res? = some (dk, rk1, ck, pt, ro, root) →
        ro.length ≤ n + 1 ∧ root.length ≤ n + 1) :
    AuthHybridListsBounded (n + 1) (finishErasedRecvOPK k j o used' hon
        { hst with recvKemRecs := r :: hst.recvKemRecs } res?).2 ∧
      (finishErasedRecvOPK k j o used' hon
        { hst with recvKemRecs := r :: hst.recvKemRecs } res?).2.base.hasWonAuth = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hB
  rcases res? with _ | ⟨dk, rk1, ck, pt, ro, root⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hw⟩ <;>
      simp only [finishErasedRecvOPK, List.length_cons] <;> omega
  · obtain ⟨hro, hroot⟩ := hres _ _ _ _ _ _ rfl
    cases hon <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hw⟩ <;>
      simp only [finishErasedRecvOPK, List.length_cons, List.length_map, Bool.false_eq_true,
        ite_true, ite_false] <;> omega

theorem finishErasedRecvNoOPK_inv (n : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk)
    (used' : List (Nat × KeyId × KeyId × Bytes)) (hon : Bool) (hst : AuthHybridState S)
    (r : RecvKemRecord) (hB : AuthHybridListsBounded n hst) (hw : hst.base.hasWonAuth = false)
    (hU : used'.length ≤ n + 1)
    (res? : HmSchedOut) (hres : ∀ dk rk1 ck pt ro root, res? = some (dk, rk1, ck, pt, ro, root) →
        ro.length ≤ n + 1 ∧ root.length ≤ n + 1) :
    AuthHybridListsBounded (n + 1) (finishErasedRecvNoOPK k j l used' hon
        { hst with recvKemRecs := r :: hst.recvKemRecs } res?).2 ∧
      (finishErasedRecvNoOPK k j l used' hon
        { hst with recvKemRecs := r :: hst.recvKemRecs } res?).2.base.hasWonAuth = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hB
  rcases res? with _ | ⟨dk, rk1, ck, pt, ro, root⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hw⟩ <;>
      simp only [finishErasedRecvNoOPK, List.length_cons] <;> omega
  · obtain ⟨hro, hroot⟩ := hres _ _ _ _ _ _ rfl
    cases hon <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hw⟩ <;>
      simp only [finishErasedRecvNoOPK, List.length_cons, Bool.false_eq_true,
        ite_true, ite_false] <;> omega

theorem hmPre_recvOPK_leaves (n jt : Nat) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState) (hI : HmInv n hst ms) :
    AllLeaves (HmPreLeaf n) (hmPre S jt (.recvOPK k j o msg) hst ms) := by
  unfold hmPre
  refine AllLeaves.bind (hmRecvOPKPrepP_leaves S n k j o msg hst.toAuthHybridState
    hI.bnd.usedKyberTriples_le) (fun d? hd => ?_)
  rcases d? with _ | d
  · have h : HmInv (n + 1) { hst with recvCount := hst.recvCount + 1 } ms :=
      ⟨⟨hI.bnd.toAuthHybridListsBounded.mono (Nat.le_succ n),
        Nat.le_succ_of_le hI.bnd.mkSaltCache_le⟩, hI.won, hI.mu.mono (Nat.le_succ n)⟩
    exact AllLeaves.pure h
  obtain ⟨hU, r, hdec⟩ := hd
  refine AllLeaves.map' _ (hmRecvTail_leaves S n jt msg hst ms d _ ?_ ?_ hI.bnd.mkSaltCache_le
    hI.mu ?_) (fun x hx => hx)
  · rw [hdec]; exact hI.bnd.roCache_le
  · rw [hdec]; exact hI.bnd.rootRoCache_le
  · intro res? hres
    rw [hdec]
    exact finishErasedRecvOPK_inv S n k j o _ _ _ r hI.bnd.toAuthHybridListsBounded hI.won hU
      res? hres

theorem hmPre_recvNoOPK_leaves (n jt : Nat) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState)
    (hI : HmInv n hst ms) :
    AllLeaves (HmPreLeaf n) (hmPre S jt (.recvNoOPK k j l msg) hst ms) := by
  unfold hmPre
  refine AllLeaves.bind (hmRecvNoOPKPrepP_leaves S n k j l msg hst.toAuthHybridState
    hI.bnd.usedKyberTriples_le) (fun d? hd => ?_)
  rcases d? with _ | d
  · have h : HmInv (n + 1) { hst with recvCount := hst.recvCount + 1 } ms :=
      ⟨⟨hI.bnd.toAuthHybridListsBounded.mono (Nat.le_succ n),
        Nat.le_succ_of_le hI.bnd.mkSaltCache_le⟩, hI.won, hI.mu.mono (Nat.le_succ n)⟩
    exact AllLeaves.pure h
  obtain ⟨hU, r, hdec⟩ := hd
  refine AllLeaves.map' _ (hmRecvTail_leaves S n jt msg hst ms d _ ?_ ?_ hI.bnd.mkSaltCache_le
    hI.mu ?_) (fun x hx => hx)
  · rw [hdec]; exact hI.bnd.roCache_le
  · rw [hdec]; exact hI.bnd.rootRoCache_le
  · intro res? hres
    rw [hdec]
    exact finishErasedRecvNoOPK_inv S n k j l _ _ _ r hI.bnd.toAuthHybridListsBounded hI.won hU
      res? hres

/-! ### The fused step -/

theorem hmPre_leaves (n jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hI : HmInv n hst ms) :
    AllLeaves (HmPreLeaf n) (hmPre S jt q hst ms) := by
  have hC : CpaInv n hst := ⟨hI.bnd, hI.won⟩
  cases q
  case sendOPK u i b m0 m1 =>
    unfold hmPre
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n)))
      (fun _ => hmSendPre_leaves S n jt _ u b m0 m1 hst ms hI)
  case sendNoOPK u i b m0 m1 =>
    unfold hmPre
    exact AllLeaves.ite _ (fun _ => AllLeaves.pure (hI.mono (Nat.le_succ n)))
      (fun _ => hmSendPre_leaves S n jt _ u b m0 m1 hst ms hI)
  case recvOPK k j o msg => exact hmPre_recvOPK_leaves S n jt k j o msg hst ms hI
  case recvNoOPK k j l msg => exact hmPre_recvNoOPK_leaves S n jt k j l msg hst ms hI
  all_goals
    unfold hmPre
    exact AllLeaves.map' _ (stepAuthOtherPrim_true_leaves S n _ hst hC)
      (fun x hx => (⟨hx.bnd, hx.won, hI.mu.mono (Nat.le_succ n)⟩ : HmInv (n + 1) _ _))

end Leaves

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
