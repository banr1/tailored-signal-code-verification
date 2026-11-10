/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyTR
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNonePure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.OooRpkPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNoneStepsPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Tie.AcceptFramePure
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonPath
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj

/-!
# Per-Call `PureCRel` and `CReadyPure` Preservation on Session Promotion

Proves `prom_accept_cRel` and `cEntry_recvPrekey_prom_call`, establishing `PureCRel` and
`CReadyPure` after a non-colliding accepting promote call from the four accept-branch obligations
(`PromExplainOK`, `PromNewRecOK`, `PromHistOK`, `PromOpkOK`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm
open Symbolic.Swarm.CREF.CliPure.RpkCli

/-! ## Accept-branch facts -/

section AcceptFacts
variable {interpretation : ExternInterpretation} {r : ProtocolSetup}
  {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
  {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
  {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
  {sess sess' : Session (List (BitVec 8))}
  {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}

theorem prom_accept_newOoo
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt) :
    SpqrOooBounded (pqStateOf sm.state) := by
  obtain ⟨hooo_in, hpqlen_in⟩ := ooo_of_cref_trRecordCanon_sess hC.entry.canon hC.out.hcan_in
  rw [pqStateOf_of_wireRecCanon_and_encodeRecord hC.out.hwrc hC.out.hstate]
  exact (spqrOooBounded_recvPrekey_promote
    (Proofs.libsignal.Hooks2.cryptoOf' interpretation)
    (Proofs.libsignal.SR.interpW interpretation)
    interpretation expected pf.inner .preKey coins sess sess'.state pt
    hC.out.hexec hooo_in hpqlen_in).1

/-- No move explaining the promote accept block is `BobStartBy r.bob`. -/
theorem prom_noBobStart
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt)
    (hB : XplBlock interpretation r S who g ms₀ (pre ++ m :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hbook : CBook interpretation r S g ms₀ e'.sent e'.accepted acc)
    (hpath : PathFaithful interpretation r S g (ms₀ ++ (pre ++ m :: post))
      (acc ++ promAccBlk b mid pt)) :
    ¬ BobStartBy r.bob m := by
  intro hbs
  have hm_path : m.prekeyPath? = some false := by
    unfold BobStartBy at hbs
    split at hbs
    · rfl
    · exact False.elim hbs
  have hi : (ms₀ ++ (pre ++ m :: post))[ms₀.length + pre.length]? = some m := by
    rw [← List.append_assoc, List.getElem?_append_right (by simp)]
    simp
  have htake : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
    rw [← List.append_assoc]
    exact List.take_left' (by simp)
  obtain ⟨hpreV, _⟩ := prom_invisible_nil pre (runTraceMoves r ms₀) hpre
  have hcc : callCount (runVis r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length))) =
      (callStarts acc).length := by
    rw [htake, TR.runVis_append, hpreV, List.append_nil]
    exact matchedPrefix_callCount_eq hB.pre
  have hcall : (callStarts (acc ++ promAccBlk b mid pt))[
      callCount (runVis r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length)))]? =
      some (.recv b) := by
    rw [hcc, callStarts_append, prom_accBlk_callStarts hC.hmid,
      List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hbk_acc : pf.baseKey.take 33 ∈ e'.accepted :=
    prom_baseKey_in_accepted hC.entry hC.out.hpf
  obtain ⟨ek, hek, heq⟩ := hbook.2.2.1 _ hbk_acc
  have hq1 : Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.QuietExt (runTraceMoves r ms₀) (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quietExt_of_movesFrom _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)
  have hdone : ∃ ek ∈ bobDoneBaseKeys
      (runTraceMoves r ((ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length))),
      ecKey (gamma interpretation S g ek) = pf.baseKey.take 33 := by
    rw [htake, Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_bobDoneBaseKeys hq1]
    exact ⟨ek, hek, heq.symm⟩
  exact TR.G1.Spine.not_bobStart_of_bobDone hpath hi hcall hC.out.hpf hdone hm_path

/-- Every explanation `δ` of the promote accept block is `DeltaFaithful r.bob`. -/
theorem prom_accept_faithful
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt)
    {g : Ghost} {ms₀ δ : List Move}
    (hB : XplBlock interpretation r S who g ms₀ δ acc (promAccBlk b mid pt))
    (hrf : RoleFaithful r who (ms₀ ++ δ)) :
    DeltaFaithful r.bob (runTraceMoves r ms₀) δ := by
  have hhead : ∀ e ∈ (promAccBlk b mid pt).head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he
    exact Or.inl rfl
  have htail : ∀ e ∈ (promAccBlk b mid pt).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    rcases (prom_accBlk_shape hC.hmid).tail e he with h | h <;> rw [h] <;> simp
  obtain ⟨pre, m, post, rfl, hpre, ⟨_, _, hm⟩, hpost⟩ :=
    xpl_oneMove hB hhead (List.cons_ne_nil _ _) htail
  obtain ⟨hpreV, hpreA⟩ := prom_invisible_nil pre (runTraceMoves r ms₀) hpre
  obtain ⟨_, hpostA⟩ := prom_invisible_nil post _ hpost
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm (e := .recv b) rfl
  have hrk := xpl_recvHeadKind m _ hv hvk
  have hact_eq : moveActor m = m.party? := by
    unfold RecvHeadKind at hrk
    cases m <;> first | rfl | exact False.elim hrk
  have hagree : ActorAgrees (moveActor m) (some r.bob) := by
    rw [hact_eq]
    rcases hp : m.party? with _ | p
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ?_)
      have hrf' := hrf (ms₀.length + pre.length) m p
        (by
          rw [← List.append_assoc, List.getElem?_append_right (by simp)]
          simp)
        hp
      have htake : (ms₀ ++ (pre ++ m :: post)).take (ms₀.length + pre.length) = ms₀ ++ pre := by
        rw [← List.append_assoc]
        exact List.take_left' (by simp)
      rw [htake, TR.runVis_append, hpreV, List.append_nil,
        matchedPrefix_callCount_eq hB.pre, hC.hj, hC.entry.who_at] at hrf'
      exact hrf'.symm
  unfold DeltaFaithful
  intro a ha
  rw [visActorsFrom_append, hpreA, List.nil_append] at ha
  simp only [visActorsFrom, hpostA, List.append_nil] at ha
  rw [List.eq_of_mem_replicate ha]
  exact hagree

end AcceptFacts

/-! ## `BobRecordBaseKeyInAccepted` and `PureBobKyberNone` preservation -/

private theorem prom2_flatten_lenField_ge {α : Type} (tag : Nat) (f : α → HwBytes)
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten.length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem prom2_encSession_length_le (s : Session HwBytes) :
    (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord
    CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField
  simp only [Option.map_some, List.length_append]
  omega

private theorem prom2_encReceiverChain_length_le (s : Session HwBytes)
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := prom2_flatten_lenField_ge 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession
  simp only [List.length_append]
  omega

private theorem prom2_seed_length_le_encReceiverChain (rc : ReceiverChain)
    (mk : MessageKeyGenerator) (hmk : mk ∈ rc.messageKeys) :
    mk.seed.length ≤ (CryptoVerification.E2E.Record.encReceiverChain rc).length := by
  have h1 := prom2_flatten_lenField_ge 4 CryptoVerification.E2E.Record.encMessageKey
    rc.messageKeys mk hmk
  have h2 : mk.seed.length ≤ (CryptoVerification.E2E.Record.encMessageKey mk).length := by
    unfold CryptoVerification.E2E.Record.encMessageKey
      CryptoVerification.E2E.Record.bytesField
      CryptoVerification.E2E.Record.lenField
    split <;> simp_all only [List.length_nil, List.length_append] <;> omega
  unfold CryptoVerification.E2E.Record.encReceiverChain
  simp only [List.length_append]
  omega

/-- Bob's record after an accepting promote call has the same `aliceBaseKey` as his entry record. -/
theorem prom_bks_rec_accept {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt) :
    ∀ rr, (fun q => if q = r.bob then some sm.state else e'.records q) r.bob = some (recordBytes rr) →
      ∃ rr₀, e'.records r.bob = some (recordBytes rr₀) ∧
        rr.current.aliceBaseKey = rr₀.current.aliceBaseKey := by
  intro rr hrr
  simp only [↓reduceIte, Option.some.injEq] at hrr
  have hrec_in : rec = recordBytes (sessionToRecordRecPending sess) :=
    (recordBytes_sessionToRecordRecPending_of_canonical_Q hC.out.hcan_in).2
  obtain ⟨_, _, hG_in⟩ := hC.out.hcan_in
  obtain ⟨_, _, _, halice_in, _, _, _⟩ := hG_in
  obtain ⟨sess₁, hrc₁, -, -, -, h62, -⟩ := hC.out.hwrc
  obtain ⟨hrc₁_bytes, _, hG₁⟩ := hrc₁
  obtain ⟨_, _, _, _, _, hpq₁, _⟩ := hG₁
  have hpq_eq : sess₁.state.pqRatchetState = sess'.state.pqRatchetState :=
    Symbolic.Swarm.TRREF.EncodeRecordPqInj.encodeRecord_pq_inj_of_eq hrc₁_bytes hC.out.hstate h62
  have hsess'_len : (CryptoVerification.E2E.Record.encSession sess').length < 2 ^ 62 := by
    have hle := prom2_encSession_length_le sess'
    rw [← hC.out.hstate] at hle
    omega
  have hsm_bytes : recordBytes (sessionToRecordRecPending sess') = sm.state := by
    rw [hC.out.hstate]
    exact recordBytes_sessionToRecordRecPending_eq_encodeRecord sess'
      (by rw [hC.out.halice]; omega)
      (by rw [← hpq_eq]; omega)
      (fun rc hrc mk hmk => Nat.lt_of_le_of_lt
        (Nat.le_trans (prom2_seed_length_le_encReceiverChain rc mk hmk)
          (prom2_encReceiverChain_length_le sess' rc hrc))
        (by omega))
      (fun rc hrc => Nat.lt_of_le_of_lt (prom2_encReceiverChain_length_le sess' rc hrc) (by omega))
      (by omega)
  have hnorm := TR.recordBytes_injective (hrr.symm.trans hsm_bytes.symm)
  have halice_rr : rr.current.aliceBaseKey = sess'.aliceBaseKey := by
    simpa [TR.normPending, TR.normPendingS, sessionToRecordRecPending,
      Swarm.Phase0WholeFunctionBridge.sessionToSessionRec] using
      congrArg (fun r : RecordRec => r.current.aliceBaseKey) hnorm
  refine ⟨sessionToRecordRecPending sess, hrec_in ▸ hC.entry.rec_lookup, ?_⟩
  rw [halice_rr, hC.out.halice]
  rfl

theorem prom_bka_accept {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt) :
    BobRecordBaseKeyInAccepted r
      (fun q => if q = r.bob then some sm.state else e'.records q) e'.accepted := by
  intro rr hrr
  obtain ⟨rr₀, hrr₀, heq⟩ := prom_bks_rec_accept hC rr hrr
  rw [heq]
  exact hC.entry.ready.2.1.bka rr₀ hrr₀

theorem prom_bkn_accept {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt) :
    PureBobKyberNone r (fun q => if q = r.bob then some sm.state else e'.records q) := by
  intro rr hrr
  simp only [↓reduceIte, Option.some.injEq] at hrr
  exact bobKyberNone_post_promoteWireRecCanon hC.entry.ready.2.1.bkn hC.entry.rec_lookup
    hC.out.hcan_in hC.out.hkyb hC.out.hstate hC.out.hwrc hrr

/-! ## `PureCRel` and `CReadyPure` after a promote-accept call -/

private theorem prom_bk_of_recvStep {r : ProtocolSetup} {blk : List MachineEvent} {tr : ExecTrace} {m : Move}
    (hm : RecvStep r.bob blk tr m) : NoSessionEffect tr m ∨ BkMoveKind r.bob m := by
  obtain ⟨_, hkind, _⟩ := hm
  rcases hkind with hrk | hlk
  · right; unfold RecvKind at hrk; cases m <;> simp_all [BkMoveKind]
  · exact Or.inl hlk

/-- Preserves `PureCRel` after an accepting promote call given `PromNewRec` and `PromHistStep`. -/
theorem prom_accept_cRel {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt)
    (hnew : PromNewRec interpretation r S who ok r.bob rec sm.state e'.sent acc (promAccBlk b mid pt))
    (hhist : PromHistStep interpretation r S who ok r.bob rec sm.state acc (promAccBlk b mid pt)) :
    PureCRel interpretation r S who ok
      (fun q => if q = r.bob then some sm.state else e'.records q) e'.sent e'.accepted
      (acc ++ promAccBlk b mid pt) := by
  have hhead : ∀ e ∈ (promAccBlk b mid pt).head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he
    exact Or.inl rfl
  have hrel := hC.entry.ready.2.1
  refine ⟨cOOO_step_update hrel.oooAll (prom_accept_newOoo hC),
    TR.sendsFit_append hrel.sendsFit (prom_accBlk_sendsFit hC.hmid),
    prom_bka_accept hC, prom_bkn_accept hC, fun g ms hc => ?_⟩
  have hmp := hc.matched
  obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ :=
    matchedPrefix_split hmp hhead (matchedPrefix_prefix_reachable hmp)
  have hc₀ : Clean interpretation r S who ok g ms₀ acc :=
    clean_prefix (matchedPrefix_length_eq hpre) hc
  obtain ⟨hrecs₀, hbook₀, hch₀, hrole₀⟩ := (hrel.clean g ms₀ hc₀).1
  have hB : XplBlock interpretation r S who g ms₀ δ acc (promAccBlk b mid pt) :=
    ⟨hpre, hmp.2.1, hmatch⟩
  have hdf : DeltaFaithful r.bob (runTraceMoves r ms₀) δ :=
    prom_accept_faithful hC hB hc.role
  have hrpk := xplInv_rpk hB hdf (prom_accBlk_shape hC.hmid)
  have h1 : OneMove (RecvStep r.bob (promAccBlk b mid pt)) (runTraceMoves r ms₀) δ :=
    prom_oneMove_recvStep hrpk (fun pre m post hδ hpreM =>
      prom_noBobStart hC (hδ ▸ hB) hpreM hbook₀ (hδ ▸ hc.path))
  obtain ⟨_, _, hrr₀H⟩ := hrecs₀ r.bob rec hC.entry.rec_lookup
  obtain ⟨rr₀, _, hrec_rr₀, hprev₀, _⟩ := hC.entry.pm
  have hrr₀ := pureCRecRelH_single hrr₀H ⟨rr₀, hrec_rr₀, hprev₀⟩
  obtain ⟨hst, hrel', hns'⟩ := hnew g ms₀ δ hc hB h1 ⟨hch₀, hrole₀⟩ hrr₀ hbook₀.2.1
  have hrole' : RoleSnapshots r (runTraceMoves r (ms₀ ++ δ)) := by
    rw [TR.runTrace_append]
    exact prom_roleSnapshots_of_oneMove_recv h1 hrole₀
  refine ⟨⟨fun q b' hb => ?_, prom_book h1 hC.hmid hbook₀ hns',
    hhist g ms₀ δ hc hB h1 ⟨hch₀, hrole₀⟩ hrr₀ hrel', hrole'⟩,
    bks_oneMove (fun _ _ hm => prom_bk_of_recvStep hm) hB.run h1 (prom_bks_rec_accept hC) (hrel.bks hc₀)⟩
  by_cases hq : q = r.bob
  · subst hq
    simp only [↓reduceIte, Option.some.injEq] at hb
    subst hb
    exact ⟨Or.inr rfl, hst, Or.inl hrel'⟩
  · simp only [hq, ↓reduceIte] at hb
    obtain ⟨hq', hb', hrq⟩ := hrecs₀ q b' hb
    exact ⟨hq', hb', pureCRecRelH_mono (fun _ => prom_rcv_frame_other h1 hq) hrq⟩

/-- Per-call accepting promote step under `CReadyPure` from the four accept-branch obligations. -/
theorem cEntry_recvPrekey_prom_call
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hxpl : PromExplainOK interpretation r S who ok)
    (hnew : PromNewRecOK interpretation r S who ok)
    (hhist : PromHistOK interpretation r S who ok)
    (hopk : PromOpkOK interpretation r S who ok)
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hcol : ¬ CollisionAt interpretation r S who ok (acc ++ promAccBlk b mid pt)) :
    (∃ g ms, MatchedPrefix interpretation r S who g ms (acc ++ promAccBlk b mid pt)) ∧
    (ok j = true →
      CReadyPure interpretation r S who ok
        (fun q => if q = r.bob then some sm.state else e'.records q)
        e'.sent e'.accepted e'.opkUsed (acc ++ promAccBlk b mid pt)) := by
  obtain ⟨hmp_ex, hclean_ex⟩ :=
    hxpl j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol
  refine ⟨hmp_ex, fun hok_j => ⟨hclean_ex hok_j,
    prom_accept_cRel hC
      (hnew j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol)
      (hhist j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol),
    hopk j e' mid acc rec b sm pf sess sess' coins expected pt hC hcol⟩⟩

end Symbolic.Swarm.CREF.CliPure
