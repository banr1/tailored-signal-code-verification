/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum
public import Symbolic.Proofs.Swarm.CREF.ModelBridge

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78b
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown hiding bytes_rec_gAll
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp Symbolic.BugInjection.Proofs.Common443.CompRX0Join Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop hiding compI0
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixReach Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixSteps Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def rng41Chars : List Char := chars_of_hex (rngAt 41)
theorem rngAt41_eq_hex : rngAt 41 = hexBytes (str_of_hex (rngAt 41)) := rfl
theorem rng41Str_eq : (str_of_hex (rngAt 41)) = String.ofList rng41Chars := rfl
theorem rngAt41_length : (rngAt 41).length = 32 := by
  have h : rngAt 41 = hexBytes.go SpecTop.hexDigit rng41Chars := by rw [rngAt41_eq_hex, rng41Str_eq, SpecTop.hexBytes_ofList]
  rw [h]; rfl
theorem seg38_eq_explicit : seg 38 2 = [.pt (ptAt 38), .send (sendAt 39)] := rfl
theorem seg40_eq_explicit : ∃ b_pt, seg 40 3 = [.recv (wireAt 40), .rng (rngAt 41), .accept b_pt] := ⟨_, rfl⟩
theorem seg43_eq_explicit : seg 43 35 = .recv (recvAt 43) :: PtDead78.call4Rng := rfl
theorem call4Rng_map_kind : PtDead78.call4Rng.map eventKind = List.replicate 34 .rng := by
  have h := seg43_kinds; rw [seg43_eq_explicit, List.map_cons, List.cons.injEq] at h; exact h.2
theorem call4Rng_length : PtDead78.call4Rng.length = 34 := by simpa using congrArg List.length call4Rng_map_kind
theorem call4Rng_kind : ∀ e ∈ PtDead78.call4Rng, eventKind e = .rng := fun _ he => List.eq_of_mem_replicate (call4Rng_map_kind ▸ List.mem_map_of_mem he)
def bundle43Chars : List Char := chars_of_hex (recvAt 43)
theorem recvAt43_eq_hex : recvAt 43 = hexBytes (str_of_hex (recvAt 43)) := rfl
theorem bundle43Str_eq : (str_of_hex (recvAt 43)) = String.ofList bundle43Chars := rfl
theorem bundle43_byte4_ne_one : (recvAt 43)[4]? ≠ some 1#8 := by
  have h : recvAt 43 = hexBytes.go SpecTop.hexDigit bundle43Chars := by rw [recvAt43_eq_hex, bundle43Str_eq, SpecTop.hexBytes_ofList]
  rw [h]; decide
attribute [local irreducible] bundle0 call0Rng ptAt rngAt sendAt setupPublic setupSecret
theorem encVis2_cl_zero_and_pt_pin {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₃ : ExecTrace} {me : Participant} {sIdx : Nat} {st : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wrap : Option (Nat × Nat)} {pt w : HwBytes} (hm₂ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .send w] (encVis tr₃ (encNextTr tr₃ me sIdx st cl pq) wrap true)) : cl = 0 ∧ gamma i S g (randTerm tr₃.length 32) = pt := by
  unfold encVis encDraws encSend at hm₂; rw [CompPrefixInvFresh.newRandoms_encNextTr, lastSent_encNextTr] at hm₂
  by_cases hcl : (cl != 0) = true
  · have hlen := hm₂.length_eq; cases wrap <;> simp [hcl] at hlen
  · have hcl0 : cl = 0 := by rcases Nat.eq_zero_or_pos cl with rfl | hpos; rfl; exfalso; apply hcl; simp [Nat.ne_of_gt hpos]
    obtain ⟨hem, -⟩ := List.forall₂_cons.mp hm₂; exact ⟨hcl0, gamma_of_single rfl rfl hem⟩
theorem mem_storedStates_of_at?_trSt {r : Records} {ms : List Move} {j : Nat} {me : Participant} {st : DY.Libsignal.TripleRatchet.TRState} (hat : ((runTraceMoves r ms).at? j : Option TRStEntry) = some (TRStE me st)) : (⟨me, st⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) ∈ storedStates r (runTraceMoves r ms) := by
  have hlt : j < (runTraceMoves r ms).length := XplSteps.xlt_of_at?_some hat
  have hge : (setupTrace r).length ≤ j := by
    by_contra hlt0
    have hle : setupTrace r ≤ runTraceMoves r ms := by rw [xpl_runTrace_eq]; exact Symbolic.Swarm.CREF.runMoves_le ms (setupTrace r)
    have hat0 : ((setupTrace r).at? j : Option TRStEntry) = some (TRStE me st) := by
      rw [← XplSteps.xat?_le_eq hle (Nat.lt_of_not_ge hlt0), hat]
    rw [noTRState_setupTrace r j] at hat0; cases hat0
  exact mem_storedStates_iff.mpr ⟨j, hge, hlt, hat⟩
theorem storedStates_step_encrypt {r : Records} {ms₀ pre₂ mid₃ : List Move} {m₂ : Move} {me₂ : Participant} {sIdx₂ cl₂ pq₂ : Nat} {st₂ : DY.Libsignal.TripleRatchet.TRState} (hpre₂ : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre₂) (henc₂ : m₂.next (runTraceMoves r (ms₀ ++ pre₂)) = encNextTr (runTraceMoves r (ms₀ ++ pre₂)) me₂ sIdx₂ st₂ cl₂ pq₂) (hmid₃ : MovesFrom InvisibleNoEffect (m₂.next (runTraceMoves r (ms₀ ++ pre₂))) mid₃) {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hls : ls ∈ storedStates r (runTraceMoves r (ms₀ ++ pre₂ ++ m₂ :: mid₃))) : ls ∈ storedStates r (runTraceMoves r ms₀) ∨ ls = ⟨me₂, encSt (runTraceMoves r (ms₀ ++ pre₂)) st₂ cl₂⟩ := by
  have htr : runTraceMoves r (ms₀ ++ pre₂ ++ m₂ :: mid₃) = (runMoves mid₃ (m₂.next (runTraceMoves r (ms₀ ++ pre₂)))).1 := by rw [CompPrefixInvStruct.runTrace_append]; rfl
  rw [htr] at hls; obtain ⟨j, _, _, hat⟩ := mem_storedStates_iff.mp hls
  rw [at?_trSt_of_movesFrom_invisibleNoEffect hmid₃ j, henc₂, at?_trSt_encNextTr] at hat
  split_ifs at hat with hj
  · cases hat; exact Or.inr rfl
  · rw [CompPrefixInvStruct.runTrace_append, at?_trSt_of_movesFrom_invisibleNoEffect hpre₂ j] at hat
    cases hat_eq : ((runTraceMoves r ms₀).at? j : Option TRStEntry) with
    | none => rw [hat_eq] at hat; cases hat
    | some e => rw [hat_eq] at hat; injection hat with he; subst e; rcases ls with ⟨p, st⟩; exact Or.inl (mem_storedStates_of_at?_trSt hat_eq)
theorem runVis_append_invisible_one_invisible {r : Records} {ms₀ pre post : List Move} {m : Move} (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) (hpost : MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₀ ++ pre))) post) : runVis r (ms₀ ++ pre ++ m :: post) = runVis r ms₀ ++ m.vis (runTraceMoves r (ms₀ ++ pre)) := by
  have h1 := runMoves_snd_of_movesFrom_invisibleNoEffect hpre; have h2 := runMoves_snd_of_movesFrom_invisibleNoEffect hpost
  have hassoc : ms₀ ++ pre ++ m :: post = ms₀ ++ (pre ++ m :: post) := by simp only [List.append_assoc]
  rw [hassoc, Symbolic.Swarm.CREF.runVis_append, runMoves_append_snd, runMoves_cons_snd, ← CompPrefixInvStruct.runTrace_append, h1, h2, List.nil_append, List.append_nil]
theorem aesSafe_pt78_pt38 : AesSafe (ptAt 78) (ptAt 38) := by
  refine ⟨?_, fun k iv => ?_⟩ <;> rw [PtDead78.ptAt38_eq_compAesPt2]
  · exact PtDead78.compAesPt2_ne_pt78
  · exact PtDead78.compAesPerm_compAesPt2_ne_pt78 k iv
theorem ptAvoidFull_encOut_iniAliceStartState_pt78 {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {tr₁ tr₃ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {cl₂ : Nat} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h)) (hrs_ek : ∀ e ∈ rs.take 1, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length) (hcoin₂ : PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₃.length + 1) cl₂)) (hpt_pin : gamma compI0 S g (randTerm tr₃.length 32) = ptAt 38) : PtAvoidFull compI0 r S g ms (ptAt 78) (encOut tr₃ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₂ (tr₃.length + 2)) := by
  have hb8 : (ptAt 78).length < 8 := (ptAt38_or_ptAt78_len (.inr rfl)).2.1; have hb32 : (ptAt 78).length < 32 := (ptAt38_or_ptAt78_len (.inr rfl)).2.2; obtain ⟨hikA, hikB, _, hspk_key, hrk, _, hpqr, hdhs⟩ := aliceOut_fields_memoInjGt hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
  have hmsg : PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm tr₃.length 32) := by
    refine ptAvoidFull_randTerm_ne (.inr ?_)
    rw [← gamma_randTerm_eq_σ (i := compI0) (S := S) tr₃.length 32 (by decide), hpt_pin, PtDead78.ptAt38_eq_compAesPt2]
    exact PtDead78.compAesPt2_ne_pt78
  refine ptAvoidFull_encOut_iniAliceStartState tr₁ tr₃ r.bob _ cl₂ hb8 hikA hikB hspk_key hrk hpqr hdhs
    hcoin₂ hmsg (fun k iv_b => ?_)
  rw [hpt_pin, PtDead78.ptAt38_eq_compAesPt2]; exact PtDead78.compAesPerm_compAesPt2_ne_pt78 k iv_b
def cliCoins2Fast : HwBytes :=
  hexBytes.go SpecTop.hexDigit
    ['6','7','6','9','f','5','a','2','6','b','9','7','2','f','f','c','b','5','e','c','b','c','d','b','5','c','b','2','5','7','7','3',
     'b','c','2','f','2','b','a','d','9','3','f','9','0','a','c','9','5','a','0','8','3','7','b','8','3','1','d','b','c','2','2','b',
     'f','d','0','8','6','e','b','7','3','1','e','0','6','5','6','9','7','7','e','4','8','1','5','9','f','2','7','3','3','5','9','c',
     'b','6','5','2','1','8','7','0','f','8','2','7','0','d','3','1','c','7','e','8','f','c','0','a','d','6','c','7','2','a','2','7']

theorem rep64_inits_not_mem_badAes38_78 : ∀ c ∈ cliCoins2Fast.inits, c ∉ badAes38_78 := by
  decide +kernel

theorem mem_rep64_inits_ne_and_perm_ne {b c : HwBytes} (hb : b = ptAt 38 ∨ b = ptAt 78)
    (hc : c ∈ cliCoins2Fast.inits) :
    c ≠ b ∧ ∀ k iv : HwBytes, compAesPerm k iv c ≠ b := by
  have hnot := rep64_inits_not_mem_badAes38_78 c hc
  refine ⟨fun heq => hnot (heq ▸ mem_badAes38_78 hb), fun k iv heq => ?_⟩
  have h16 := compAesPerm_length_ge_16 k iv c
  have hb6 := (ptAt38_or_ptAt78_len hb).1
  rw [heq] at h16; omega

theorem ptAvoidFull_randTerm_of_mem_rep64_inits {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {idx sz : Nat}
    (hb : b = ptAt 38 ∨ b = ptAt 78) (h : sz = 0 ∨ gamma compI0 S g (randTerm idx sz) ∈ cliCoins2Fast.inits) :
    PtAvoidFull compI0 r S g ms b (randTerm idx sz) := by
  by_cases hsz : sz = 0
  · exact ptAvoidFull_randTerm_ne (.inl hsz)
  · have hc := h.resolve_left hsz
    rw [gamma_randTerm_eq_σ idx sz hsz] at hc
    exact ptAvoidFull_randTerm_ne (.inr (mem_rep64_inits_ne_and_perm_ne hb hc).1)

private theorem noBrk_append_left {r : Records} {ms₁ ms₂ : List Move}
    (hnb : CompSetupSecrecy.NoBrk r (ms₁ ++ ms₂)) : CompSetupSecrecy.NoBrk r ms₁ :=
  CompSetupSecrecy.noBrk_of_le (by rw [CompPrefixInvStruct.runTrace_append]; exact Symbolic.Swarm.CREF.runMoves_le _ _) hnb

theorem step38_to_40_plus_invisible_rs
    {r : Records} {S : Sem} {g : Ghost} {ms₃₈ pre₂ mid₃ : List Move} {m₂ : Move}
    {rs₁ rs₂ : List MachineEvent} (hwf : RecordsWF r)
    (hnb' : CompSetupSecrecy.NoBrk r (ms₃₈ ++ pre₂ ++ m₂ :: mid₃))
    (hrs₁_kind : ∀ e ∈ rs₁, eventKind e = .rng)
    (hrs₁_inits : ∀ c, .rng c ∈ rs₁ → c ∈ (rngAt 36).inits)
    (hrs₂_kind : ∀ e ∈ rs₂, eventKind e = .rng)
    (hrs₂_inits : ∀ c, .rng c ∈ rs₂ → c ∈ cliCoins2Fast.inits)
    (hmp38 : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₃₈ ((.recv bundle0 :: call0Rng) ++ (.pt (ptAt 35) :: (rs₁ ++ [.send (sendAt 37)]))))
    (hpre₂ : MovesFrom InvisibleNoEffect (runTraceMoves r ms₃₈) pre₂)
    (hm₂_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.pt (ptAt 38) :: (rs₂ ++ [.send (sendAt 39)])) (m₂.vis (runTraceMoves r (ms₃₈ ++ pre₂))))
    (hmid₃ : MovesFrom InvisibleNoEffect (m₂.next (runTraceMoves r (ms₃₈ ++ pre₂))) mid₃)
    (hmr' : ModelRun r (ms₃₈ ++ pre₂ ++ m₂ :: mid₃)) :
    let ms' := ms₃₈ ++ pre₂ ++ m₂ :: mid₃
    (∀ ls ∈ storedStates r (runTraceMoves r ms'), PtAvoidFull compI0 r S g ms' (ptAt 78) (Comparse.serialize ls)) ∧
    (∀ u : DY.Bytes, (runTraceMoves r ms').BaseAttackerKnows u → PtAvoidFull compI0 r S g ms' (ptAt 78) u) ∧
    (∀ v ∈ runVis r ms', v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull compI0 r S g ms' (ptAt 78) u) ∧
    PtVisRandTermsInv (runVis r ms') ∧ (∀ v ∈ runVis r ms', v.kind ≠ .leak) := by
  dsimp only
  let ms' := ms₃₈ ++ pre₂ ++ m₂ :: mid₃
  let tr₃ := runTraceMoves r (ms₃₈ ++ pre₂)
  have hnb38 : CompSetupSecrecy.NoBrk r ms₃₈ := noBrk_append_left (noBrk_append_left hnb')
  have hc : Compat compI0 r S g := hmp38.1; obtain ⟨hb6, _, hb32⟩ := ptAt38_or_ptAt78_len (.inr rfl)
  have hrs_ek : ∀ ev ∈ call0Rng.take 1, (ptAt 78).length < (Census443Defs.eventBytes ev).length :=
    fun ev hev => Nat.lt_of_le_of_lt hb6 (call0Rng_take_1_gt_6 ev hev)
  have hrs_dhs : ∀ ev ∈ call0Rng.drop 33, (ptAt 78).length < (Census443Defs.eventBytes ev).length :=
    fun ev hev => Nat.lt_of_le_of_lt hb6 (call0Rng_drop_33_gt_6 ev hev)
  obtain ⟨hrs38, hsks38, hinv38, hnoleak38, _, _⟩ := take38_inv_cref_rs hwf hnb38 hrs₁_kind hrs₁_inits hmp38 (.inr rfl)
  obtain ⟨me₂, sIdx₂, cl₂, pq₂, wrap₂, rfl, hls₂, _, hm₂_enc⟩ := invert_send_rs_move_opt hm₂_vis
  obtain ⟨st₂, hat₂, hns₂⟩ := encrypt_state_of_lastSent_ne_none hls₂
  have hpq₂ : pq₂ = tr₃.length + 2 := by change pq₂ = (runTraceMoves r (ms₃₈ ++ pre₂)).length + 2; rw [xpl_runTrace_eq]; exact pq_eq_of_ownSaltsFrom_split hmr'.2.2.2.2.1 rfl
  have henc₂ := encrypt_next_eq_encNextTr_of_ownSalt (cl := cl₂) (wrap := wrap₂) hat₂ hns₂ hpq₂; rw [henc₂] at hm₂_enc
  obtain ⟨hpt₂, hcl₂_cases⟩ := encVis_rs_cases hrs₂_kind hm₂_enc
  have hcpin₂ : cl₂ = 0 ∨ gamma compI0 S g (randTerm (tr₃.length + 1) cl₂) ∈ cliCoins2Fast.inits := by
    rcases hcl₂_cases with ⟨hcl0, _⟩ | ⟨_, c, hrs₂_eq, hpin⟩
    · exact Or.inl hcl0
    · refine Or.inr ?_; rw [(List.cons.inj hpin).1]; exact hrs₂_inits c (by rw [hrs₂_eq]; simp)
  have hcoin₂ : PtAvoidFull compI0 r S g ms' (ptAt 78) (randTerm (tr₃.length + 1) cl₂) :=
    ptAvoidFull_randTerm_of_mem_rep64_inits (.inr rfl) hcpin₂
  have hat₂_38 : ((runTraceMoves r ms₃₈).at? sIdx₂ : Option TRStEntry) = some (TRStE me₂ st₂) := by
    have h := hat₂; change ((runTraceMoves r (ms₃₈ ++ pre₂)).at? sIdx₂ : Option TRStEntry) = _ at h
    rwa [CompPrefixInvStruct.runTrace_append, at?_trSt_of_movesFrom_invisibleNoEffect hpre₂ sIdx₂] at h
  have hst₂_mem := mem_storedStates_of_at?_trSt hat₂_38
  have hst38_ms' : ∀ ls ∈ storedStates r (runTraceMoves r ms₃₈), PtAvoidFull compI0 r S g ms' (ptAt 78) (Comparse.serialize ls) := by
    intro ls hls; obtain ⟨tr₁, a, ikA, hb_h, hid, hm₀_vis, hcases⟩ := hinv38.2.1 ls hls
    rcases hcases with rfl | ⟨tr₂, cl₁, hcpin, rfl⟩
    · exact ptAvoidFull_iniAliceStartState_of_aliceVis hc hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
    · exact ptAvoidFull_encSt_of_aliceVis hc hwf hb32 hid hm₀_vis hrs_ek hrs_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin)
  have hst' : ∀ ls ∈ storedStates r (runTraceMoves r ms'), PtAvoidFull compI0 r S g ms' (ptAt 78) (Comparse.serialize ls) := by
    intro ls hls; rcases storedStates_step_encrypt hpre₂ henc₂ hmid₃ hls with hls_old | rfl
    · exact hst38_ms' ls hls_old
    · obtain ⟨tr₁, a, ikA, hb_h, hid, hm₀_vis, hcases⟩ := hinv38.2.1 _ hst₂_mem
      rcases hcases with heq | ⟨tr₂, cl₁, hcpin₁, heq⟩ <;> (injection heq with hme_eq hst_eq; subst hme_eq hst_eq)
      · exact ptAvoidFull_encSt_of_aliceVis hc hwf hb32 hid hm₀_vis hrs_ek hrs_dhs hcoin₂
      · exact PtDead78.ptAvoidFull_encSt2_of_aliceVis hc hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
          (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin₁) hcoin₂
  have htr' : runTraceMoves r ms' = (runMoves mid₃ ((Move.encrypt me₂ sIdx₂ cl₂ pq₂ wrap₂).next tr₃)).1 := by change runTraceMoves r ((ms₃₈ ++ pre₂) ++ Move.encrypt me₂ sIdx₂ cl₂ pq₂ wrap₂ :: mid₃) = _; rw [CompPrefixInvStruct.runTrace_append]; rfl
  have hrs' : RunRandSafe g (ptAt 78) (runTraceMoves r ms') := by
    have hanc := hmr'.2.2.1.2.1; have hns := hmr'.2.1; obtain ⟨hanc38_pre₂, hanc_m₂⟩ := movesAnchored_append' (ms₃₈ ++ pre₂) _ _ hanc; obtain ⟨_, hanc_pre₂⟩ := movesAnchored_append' ms₃₈ pre₂ _ hanc38_pre₂; rw [← xpl_runTrace_eq] at hanc_pre₂ hanc_m₂
    have hanc_mid₃ : MovesAnchored mid₃ ((Move.encrypt me₂ sIdx₂ cl₂ pq₂ wrap₂).next tr₃) := hanc_m₂.2
    have hns_pre₂ : ∀ m ∈ pre₂, m.isSetup = false := fun m hm => hns m (by simp [hm])
    have hns_mid₃ : ∀ m ∈ mid₃, m.isSetup = false := fun m hm => hns m (by simp [hm])
    have hc₂_safe : ∀ c, .rng c ∈ rs₂ → AesSafe (ptAt 78) c := fun c hc => mem_rep64_inits_ne_and_perm_ne (.inr rfl) (hrs₂_inits c hc)
    have hE₂ := encDraws_aesSafe_rs hrs₂_kind hm₂_enc aesSafe_pt78_pt38 hc₂_safe
    intro j n hj hn; rw [htr'] at hj; have hj1 := randAt_of_runMoves mid₃ _ hmid₃ hanc_mid₃ hns_mid₃ hj
    rcases randAt_or_mem_next hj1 with hj2 | hmem
    · change RandAt (runTraceMoves r (ms₃₈ ++ pre₂)) j n at hj2; rw [CompPrefixInvStruct.runTrace_append] at hj2
      exact hrs38 j n (randAt_of_runMoves pre₂ _ hpre₂ hanc_pre₂ hns_pre₂ hj2) hn
    · rw [henc₂] at hmem; exact aesSafe_of_mem_newRandoms hE₂ hmem hn
  have hsks' : NoSKS (runTraceMoves r ms') := by
    have hsks_tr₃ : NoSKS tr₃ := by change NoSKS (runTraceMoves r (ms₃₈ ++ pre₂)); rw [CompPrefixInvStruct.runTrace_append]; exact noSKS_of_movesFrom_invisibleNoEffect hsks38 hpre₂
    rw [htr']; refine noSKS_of_movesFrom_invisibleNoEffect ?_ hmid₃; rw [henc₂]; exact noSKS_encNextTr hsks_tr₃ _ _ _ _ _
  have hnoleak' : ∀ v ∈ runVis r ms', v.kind ≠ .leak := by
    intro v hv; rw [runVis_append_invisible_one_invisible hpre₂ hmid₃, encrypt_vis_eq, List.mem_append] at hv
    rcases hv with hv38 | hv2
    · exact hnoleak38 v hv38
    · rcases xpl_encVis_kind hv2 with hk | hk | ⟨_, hk⟩ <;> rw [hk] <;> decide
  have hbase' := hbase_of_runFacts_no_leak hmr' hc hwf (.inr rfl) hst' hsks' hnoleak' hnb' hrs'
  have htr₃_le : tr₃ ≤ runTraceMoves r ms' := by rw [htr']; exact Trace.le_trans _ _ _ ((Move.encrypt me₂ sIdx₂ cl₂ pq₂ wrap₂).le_next tr₃) (Symbolic.Swarm.CREF.runMoves_le mid₃ _)
  have hsend' : ∀ v ∈ runVis r ms', v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull compI0 r S g ms' (ptAt 78) u := by
    intro v hv hk u hu; rw [runVis_append_invisible_one_invisible hpre₂ hmid₃, encrypt_vis_eq, henc₂, List.mem_append] at hv
    rcases hv with hv38 | hv2
    · have h38 : PtAvoidFull compI0 r S g ms₃₈ (ptAt 78) u := by
        rcases hinv38.2.2.1 v hv38 hk u hu with hav | ⟨tr₁, tr₂, a, ikA, hb_h, cl₁, hid, hm₀_vis, hpt_pin, hcpin, rfl⟩
        · exact hav
        · exact ptAvoidFull_encOut_of_aliceVis hc hwf (.inr rfl) hid hm₀_vis hrs_ek hrs_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin) hpt_pin
      have hassoc : ms' = ms₃₈ ++ (pre₂ ++ Move.encrypt me₂ sIdx₂ cl₂ pq₂ wrap₂ :: mid₃) := by simp only [ms', List.append_assoc]
      rw [hassoc]; exact ptAvoidFull_append _ h38
    · unfold encVis at hv2; rw [List.mem_append] at hv2; rcases hv2 with hv_draws | hv_send
      · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl <;> cases hk
      · have hu_cases : (∃ hs, u ∈ received tr₃ hs) ∨ u = encOut tr₃ st₂ cl₂ (tr₃.length + 2) := by
          rw [← hpq₂]
          cases wrap₂ with
          | none => rw [mem_encSend_encNextTr_none hv_send] at hu; exact Or.inr (List.mem_singleton.mp hu)
          | some ec =>
            rcases ec with ⟨e, c⟩; rw [mem_encSend_encNextTr_some hv_send] at hu; dsimp only at hu
            rw [List.mem_append, List.mem_singleton] at hu
            rcases hu with hrec | rfl <;> [exact Or.inl ⟨[e, c], hrec⟩; exact Or.inr rfl]
        rcases hu_cases with ⟨hs, hrec⟩ | rfl
        · exact ptAvoidFull_of_attackerKnows hbase' (attackerKnows_of_mem_received htr₃_le hrec)
        · obtain ⟨tr₁, a, ikA, hb_h, hid, hm₀_vis, hcases⟩ := hinv38.2.1 _ hst₂_mem
          rcases hcases with heq | ⟨tr₂, cl₁, hcpin₁, heq⟩ <;> (injection heq with hme_eq hst_eq; subst hme_eq hst_eq)
          · exact ptAvoidFull_encOut_iniAliceStartState_pt78 hc hwf hid hm₀_vis hrs_ek hrs_dhs hcoin₂ hpt₂
          · exact PtDead78.ptAvoidFull_encOut2_of_aliceVis_pt78 hc hwf hid hm₀_vis hrs_ek hrs_dhs
              (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin₁) hcoin₂ hpt₂
  have hpt' : PtVisRandTermsInv (runVis r ms') := by
    intro v hv hk u hu; rw [runVis_append_invisible_one_invisible hpre₂ hmid₃, encrypt_vis_eq, henc₂, List.mem_append] at hv
    rcases hv with hv38 | hv2
    · exact hinv38.2.2.2 v hv38 hk u hu
    · unfold encVis at hv2; rw [List.mem_append] at hv2; rcases hv2 with hv_draws | hv_send
      · rcases mem_encDraws_encNextTr hv_draws with rfl | rfl
        · exact ⟨tr₃.length, 32, List.mem_singleton.mp hu⟩
        · cases hk
      · cases wrap₂ with
        | none => rw [mem_encSend_encNextTr_none hv_send] at hk; cases hk
        | some ec => rcases ec with ⟨e, c⟩; rw [mem_encSend_encNextTr_some hv_send] at hk; cases hk
  exact ⟨hst', hbase', hsend', hpt', hnoleak'⟩
theorem bobStart_vis_eq (tr : ExecTrace) (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (shown : Nat) : (Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).vis tr = (bobVis tr ((Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown).next tr) mh (bobOpkPk b kh tr)).take shown := by
  have hex := exposures_nil_of_not_leakKind (tr := tr) (m := Move.bobStart b a kh regA mh pqIdx spqrMsgIdx shown) rfl (fun h => nomatch h)
  rw [xpl_vis_eq, hex, List.append_nil]; rfl
theorem step40_to_43_rs {r : Records} {S : Sem} {g : Ghost} {ms₄₃ : List Move} {rs₁ rs₂ : List MachineEvent} (hwf : RecordsWF r) (hnb : CompSetupSecrecy.NoBrk r ms₄₃) (hrs₁_kind : ∀ e ∈ rs₁, eventKind e = .rng) (hrs₁_inits : ∀ c, .rng c ∈ rs₁ → c ∈ (rngAt 36).inits) (hrs₂_kind : ∀ e ∈ rs₂, eventKind e = .rng) (hrs₂_inits : ∀ c, .rng c ∈ rs₂ → c ∈ cliCoins2Fast.inits) (hmp43 : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₃ ((((.recv bundle0 :: call0Rng) ++ (.pt (ptAt 35) :: (rs₁ ++ [.send (sendAt 37)]))) ++ (.pt (ptAt 38) :: (rs₂ ++ [.send (sendAt 39)]))) ++ seg 40 3)) : (∀ ls ∈ storedStates r (runTraceMoves r ms₄₃), PtAvoidFull compI0 r S g ms₄₃ (ptAt 78) (Comparse.serialize ls)) ∧ (∀ v ∈ runVis r ms₄₃, v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull compI0 r S g ms₄₃ (ptAt 78) u) ∧ PtVisRandTermsInv (runVis r ms₄₃) ∧ (∀ v ∈ runVis r ms₄₃, v.kind ≠ .leak) := by
  have hc : Compat compI0 r S g := hmp43.1; obtain ⟨_, _, hb32⟩ := ptAt38_or_ptAt78_len (.inr rfl); obtain ⟨b_pt, hseg40⟩ := seg40_eq_explicit; obtain ⟨p40, hp40⟩ := wireAt40_parses
  let τ₃₈ := (.recv bundle0 :: call0Rng) ++ (.pt (ptAt 35) :: (rs₁ ++ [.send (sendAt 37)]))
  let blk₂ := .pt (ptAt 38) :: (rs₂ ++ [.send (sendAt 39)])
  let τ₄₀ := τ₃₈ ++ blk₂
  have hmp43' : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₄₃ (τ₄₀ ++ [.recv (wireAt 40), .rng (rngAt 41), .accept b_pt]) := by rwa [← hseg40]
  have htail₁_bd : ∀ e ∈ rs₁ ++ [.send (sendAt 37)], eventKind e = .rng ∨ eventKind e = .send := by
    intro e he; rcases List.mem_append.mp he with he | he
    · exact Or.inl (hrs₁_kind e he)
    · rw [List.mem_singleton.mp he]; exact Or.inr rfl
  have htail₂_bd : ∀ e ∈ rs₂ ++ [.send (sendAt 39)], eventKind e = .rng ∨ eventKind e = .send := by
    intro e he; rcases List.mem_append.mp he with he | he
    · exact Or.inl (hrs₂_kind e he)
    · rw [List.mem_singleton.mp he]; exact Or.inr rfl
  have hunk40 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms₀ τ₄₀ → ¬ KnownBaseKey compI0 r S g ms₀ p40 := by
    intro ms₀ hmp₀
    refine not_knownBaseKey_of_allBobDone_false ?_
    exact BobDone.allBobDone_matchedPrefix_send_tail htail₂_bd
      (fun ms₁ hmp₁ => BobDone.allBobDone_matchedPrefix_send_tail htail₁_bd
        (fun ms₂ hmp₂ => BobDone.allBobDone_matchedPrefix_ini_rs (τ_pre := []) call0Rng_kind
          (fun _ => BobDone.allBobDone_matchedPrefix_nil) (by simpa using hmp₂)) hmp₁) hmp₀
  obtain ⟨ms₄₀, pre₃, post₃, b₃, a₃, kh₃, regA₃, mh₃, pqIdx₃, spqrMsgIdx₃, shown₃, hms₄₃, hmp40, hmr43, hpre₃, hpost₃, _, hm₃_vis⟩ := matchedPrefix_rpk_bobStart_only compI0 r S g τ₄₀ (wireAt 40) (rngAt 41) b_pt ms₄₃ p40 wireAt40_head? hp40 hunk40 hmp43'
  have hhead₂ : ∀ e ∈ blk₂.head?, eventKind e = .recv ∨ eventKind e = .pt := by intro e he; simp [blk₂] at he; subst he; exact Or.inr rfl
  obtain ⟨ms₃₈, δ₂, hms₄₀_δ, hmp38, hfor₂⟩ := matchedPrefix6_split hmp40 hhead₂ (matchedPrefix6_prefix_reachable hmp40)
  have hB₂ : XplBlock6 compI0 r S g ms₃₈ δ₂ τ₃₈ blk₂ := ⟨hmp38, hms₄₀_δ ▸ hmp40.2.1, hfor₂⟩
  have htail₂_xpl : ∀ e ∈ blk₂.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; rcases htail₂_bd e he with h | h <;> rw [h] <;> decide
  obtain ⟨pre₂, m₂, post₂, rfl, hpre₂, ⟨_, _, hm₂_vis⟩, hpost₂⟩ := xpl6_oneMove hB₂ hhead₂ (by simp [blk₂]) htail₂_xpl
  rw [← CompPrefixInvStruct.runTrace_append r ms₃₈ pre₂] at hm₂_vis hpost₂
  have hms₄₀ : ms₄₀ = ms₃₈ ++ pre₂ ++ m₂ :: post₂ := by simp [hms₄₀_δ, List.append_assoc]
  let mid₃ := post₂ ++ pre₃
  let ms' := ms₃₈ ++ pre₂ ++ m₂ :: mid₃
  have hms'_eq : ms₄₀ ++ pre₃ = ms' := by dsimp only [ms', mid₃]; rw [hms₄₀]; simp only [List.append_assoc, List.cons_append]
  have hmid₃ : MovesFrom InvisibleNoEffect (m₂.next (runTraceMoves r (ms₃₈ ++ pre₂))) mid₃ := by
    dsimp only [mid₃]; rw [movesFrom_append]; refine ⟨hpost₂, ?_⟩
    have htr40 : (runMoves post₂ (m₂.next (runTraceMoves r (ms₃₈ ++ pre₂)))).1 = runTraceMoves r ms₄₀ := by rw [hms₄₀, CompPrefixInvStruct.runTrace_append r (ms₃₈ ++ pre₂) (m₂ :: post₂), runMoves_cons_fst]
    rw [htr40]; exact hpre₃
  have hms₄₃_eq : ms₄₃ = ms' ++ Move.bobStart b₃ a₃ kh₃ regA₃ mh₃ pqIdx₃ spqrMsgIdx₃ shown₃ :: post₃ := by rw [hms₄₃, ← List.append_assoc, hms'_eq]
  have hmr' : ModelRun r ms' := modelRun_prefix_of_reachable (hms₄₃_eq ▸ hmr43) (CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp43 ms' _ hms₄₃_eq)
  have hnb' : CompSetupSecrecy.NoBrk r ms' := noBrk_append_left (hms₄₃_eq ▸ hnb)
  obtain ⟨hst', hbase', hsend', hpt', hnoleak'⟩ := step38_to_40_plus_invisible_rs hwf hnb' hrs₁_kind hrs₁_inits hrs₂_kind hrs₂_inits hmp38 hpre₂ hm₂_vis hmid₃ hmr'
  let m₃ := Move.bobStart b₃ a₃ kh₃ regA₃ mh₃ pqIdx₃ spqrMsgIdx₃ shown₃
  let tr₃' := runTraceMoves r ms'
  have htr₃'_eq : (runMoves pre₃ (runTraceMoves r ms₄₀)).1 = tr₃' := by rw [← CompPrefixInvStruct.runTrace_append, hms'_eq]
  rw [htr₃'_eq] at hm₃_vis hpost₃; obtain ⟨w₃, _, _⟩ := bobStartOk_of_rpk_forall2 hp40 hm₃_vis
  have hm₃_next : m₃.next tr₃' = bobStartTr tr₃' b₃ a₃ w₃ := bobStart_next_eq w₃
  have hsh₃ : 3 ≤ shown₃ := by have hlen := hm₃_vis.length_eq; rw [bobStart_vis_eq, List.length_take] at hlen; change 3 = min shown₃ _ at hlen; omega
  have hrnd₃ : ((bobStartTr tr₃' b₃ a₃ w₃).at? tr₃'.length : Option DY.Random.ExecEntryT) = some (Symbolic.Swarm.CREF.TR.RndE 32) := by
    rw [at?_rnd_bobStartTr w₃ tr₃'.length]; simp
  have hm₃_vis_bob : List.Forall₂ (EventMatchesEntry compI0 r S g) [.recv (wireAt 40), .rng (rngAt 41), .accept b_pt]
      ((bobVis tr₃' (bobStartTr tr₃' b₃ a₃ w₃) mh₃ (bobOpkPk b₃ kh₃ tr₃')).take shown₃) := by rwa [bobStart_vis_eq, hm₃_next] at hm₃_vis
  have hrng41_pin : [gamma compI0 S g (randTerm tr₃'.length 32)] = [rngAt 41] := by rw [gamma_rng_of_bobVis_forall2 hsh₃ (length_lt_bobStartTr w₃) hrnd₃ hm₃_vis_bob]
  have hrng41_gt : (ptAt 78).length < (rngAt 41).length := by rw [PtDead78.ptAt78_length, rngAt41_length]; decide
  have hdhs_bob := ptAvoidFull_randTerm_of_pin (r := r) (ms := ms') hrng41_pin hrng41_gt; have hbob_st := ptAvoidFull_bobFinalSt w₃ hc hwf hb32 hmr' (Trace.le_refl _) hbase' hdhs_bob
  have hst43 : ∀ ls ∈ storedStates r (runTraceMoves r ms₄₃), PtAvoidFull compI0 r S g ms₄₃ (ptAt 78) (Comparse.serialize ls) := by
    intro ls hls
    have htr43 : runTraceMoves r ms₄₃ = (runMoves post₃ (m₃.next tr₃')).1 := by rw [hms₄₃_eq, CompPrefixInvStruct.runTrace_append r ms' (m₃ :: post₃), runMoves_cons_fst]
    rw [htr43] at hls; obtain ⟨j, hge, _, hat⟩ := mem_storedStates_iff.mp hls
    rw [at?_trSt_of_movesFrom_invisibleNoEffect hpost₃ j, hm₃_next] at hat
    have hls_bob : ls ∈ storedStates r (bobStartTr tr₃' b₃ a₃ w₃) := mem_storedStates_iff.mpr ⟨j, hge, XplSteps.xlt_of_at?_some hat, hat⟩
    rw [hms₄₃_eq]; rcases storedStates_bobStartTr w₃ hls_bob with hls_old | rfl
    · exact ptAvoidFull_append _ (hst' ls hls_old)
    · exact ptAvoidFull_append _ hbob_st
  have hvis43 : runVis r ms₄₃ = runVis r ms' ++ m₃.vis tr₃' := by
    simpa [hms₄₃_eq] using runVis_append_invisible_one_invisible (ms₀ := ms') (pre := []) (m := m₃) (post := post₃) ⟨⟩ (by simpa using hpost₃)
  have hm₃_no_send_pt_leak : ∀ v ∈ m₃.vis tr₃', v.kind ≠ .send ∧ v.kind ≠ .pt ∧ v.kind ≠ .leak := by
    intro v hv; obtain ⟨ev, hev_mem, hem⟩ := forall2_exists_left' hm₃_vis hv; rw [← hem.1]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hev_mem
    rcases hev_mem with rfl | rfl | rfl <;> exact ⟨by nofun, by nofun, by nofun⟩
  have hsend43 : ∀ v ∈ runVis r ms₄₃, v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull compI0 r S g ms₄₃ (ptAt 78) u := by
    intro v hv hk u hu; rw [hvis43, List.mem_append] at hv; rcases hv with hv' | hv3
    · rw [hms₄₃_eq]; exact ptAvoidFull_append _ (hsend' v hv' hk u hu)
    · exact False.elim ((hm₃_no_send_pt_leak v hv3).1 hk)
  have hpt43 : PtVisRandTermsInv (runVis r ms₄₃) := by
    intro v hv hk u hu; rw [hvis43, List.mem_append] at hv; rcases hv with hv' | hv3
    · exact hpt' v hv' hk u hu
    · exact False.elim ((hm₃_no_send_pt_leak v hv3).2.1 hk)
  have hnoleak43 : ∀ v ∈ runVis r ms₄₃, v.kind ≠ .leak := by
    intro v hv; rw [hvis43, List.mem_append] at hv; rcases hv with hv' | hv3
    · exact hnoleak' v hv'
    · exact (hm₃_no_send_pt_leak v hv3).2.2
  exact ⟨hst43, hsend43, hpt43, hnoleak43⟩
theorem pre78PrefixInv_rs {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move} {rs₁ rs₂ : List MachineEvent} (hwf : RecordsWF r) (hnb : CompSetupSecrecy.NoBrk r ms) (hrs₁_kind : ∀ e ∈ rs₁, eventKind e = .rng) (hrs₁_inits : ∀ c, .rng c ∈ rs₁ → c ∈ (rngAt 36).inits) (hrs₂_kind : ∀ e ∈ rs₂, eventKind e = .rng) (hrs₂_inits : ∀ c, .rng c ∈ rs₂ → c ∈ cliCoins2Fast.inits) (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who₀ g ms (((((.recv bundle0 :: call0Rng) ++ (.pt (ptAt 35) :: (rs₁ ++ [.send (sendAt 37)]))) ++ (.pt (ptAt 38) :: (rs₂ ++ [.send (sendAt 39)]))) ++ seg 40 3) ++ seg 43 35)) : PtDead78.Pre78PrefixInv r S g ms := by
  have hmp78 := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp; have hmr78 : ModelRun r ms := hmp78.2.1; have hsec78 := storedSecrets_inv_of_no_setup hwf hmr78.2.1 hmr78.2.2.1.1
  obtain ⟨ms₄₃, pre₄, post₄, m₄, hms, hmp43, hpre₄, hm₄_vis, hpost₄⟩ :=
    matchedPrefix_split_seg hmp78 seg43_kinds (Or.inl rfl) (fun k hk => Or.inl (replicate_rng 34 k hk))
  have hnb_pre₄ : CompSetupSecrecy.NoBrk r (ms₄₃ ++ pre₄) := noBrk_append_left (hms ▸ hnb)
  have hnb43 : CompSetupSecrecy.NoBrk r ms₄₃ := noBrk_append_left hnb_pre₄
  rw [seg43_eq_explicit] at hm₄_vis; obtain ⟨hst43, hsend43, hpt43, hnoleak43⟩ := step40_to_43_rs hwf hnb43 hrs₁_kind hrs₁_inits hrs₂_kind hrs₂_inits hmp43
  let tr₄ := runTraceMoves r (ms₄₃ ++ pre₄)
  have htr₄_eq : (runMoves pre₄ (runTraceMoves r ms₄₃)).1 = tr₄ := (CompPrefixInvStruct.runTrace_append r ms₄₃ pre₄).symm
  have hs₄ : m₄.isSetup = false := hmr78.2.1 m₄ (by rw [hms]; simp)
  have ha₄ : m₄.Anchored tr₄ := by have hanc := hmr78.2.2.1.2.1; rw [hms, b5_movesAnchored_append] at hanc; exact hanc.2.1
  have hst_pre₄ : ∀ ls ∈ storedStates r tr₄, PtAvoidFull compI0 r S g (ms₄₃ ++ pre₄) (ptAt 78) (Comparse.serialize ls) := by
    intro ls hls; obtain ⟨j, hge, _, hat⟩ := mem_storedStates_iff.mp hls
    rw [← htr₄_eq, at?_trSt_of_movesFrom_invisibleNoEffect hpre₄ j] at hat
    exact ptAvoidFull_append _ (hst43 ls (mem_storedStates_iff.mpr ⟨j, hge, XplSteps.xlt_of_at?_some hat, hat⟩))
  have hvis78 : runVis r ms = runVis r ms₄₃ ++ m₄.vis tr₄ := by rw [hms, runVis_append_invisible_one_invisible hpre₄ hpost₄]
  have hm₄_no_send_pt : ∀ v ∈ m₄.vis tr₄, v.kind ≠ .send ∧ v.kind ≠ .pt := by
    intro v hv; obtain ⟨ev, hev_mem, hem⟩ := forall2_exists_left' hm₄_vis hv; rw [← hem.1]
    rcases List.mem_cons.mp hev_mem with rfl | hev_rng
    · exact ⟨by nofun, by nofun⟩
    · rw [call4Rng_kind ev hev_rng]; exact ⟨by nofun, by nofun⟩
  have hsend78 : ∀ v ∈ runVis r ms, v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull compI0 r S g ms (ptAt 78) u := by
    intro v hv hk u hu; rw [hvis78, List.mem_append] at hv; rcases hv with hv43 | hv4
    · rw [hms, List.append_assoc]; exact ptAvoidFull_append _ (hsend43 v hv43 hk u hu)
    · exact False.elim ((hm₄_no_send_pt v hv4).1 hk)
  have hpt78 : PtVisRandTermsInv (runVis r ms) := by
    intro v hv hk u hu; rw [hvis78, List.mem_append] at hv; rcases hv with hv43 | hv4
    · exact hpt43 v hv43 hk u hu
    · exact False.elim ((hm₄_no_send_pt v hv4).2 hk)
  refine ⟨hsec78, ?_, fun v hv hk u hu => .inl (hsend78 v hv hk u hu), hpt78⟩
  intro ls hls
  have htr78 : runTraceMoves r ms = (runMoves post₄ (m₄.next tr₄)).1 := by rw [hms, CompPrefixInvStruct.runTrace_append r (ms₄₃ ++ pre₄) (m₄ :: post₄), runMoves_cons_fst]
  rw [htr78] at hls; obtain ⟨j, hge, _, hat⟩ := mem_storedStates_iff.mp hls
  rw [at?_trSt_of_movesFrom_invisibleNoEffect hpost₄ j] at hat
  by_cases heff : NoSessionEffect tr₄ m₄
  · rw [at?_trSt_of_noSessionEffect heff j] at hat
    rw [hms]; exact .inl (ptAvoidFull_append _ (hst_pre₄ ls (mem_storedStates_iff.mpr ⟨j, hge, XplSteps.xlt_of_at?_some hat, hat⟩)))
  · obtain ⟨a₄, b₄, idS₄, regB₄, hb₄, shown₄, rfl, _, hdone₄, hm₄_alice⟩ :=
      invert_ini_move_of_not_noSessionEffect hs₄ ha₄ hm₄_vis call4Rng_length call4Rng_kind heff
    have hns_pre₄ : ∀ m ∈ ms₄₃ ++ pre₄, m.isSetup = false := fun m hm => hmr78.2.1 m (by rw [hms]; exact List.mem_append_left _ hm)
    have hreach_pre₄ := CompPrefixInvStruct.matchedPrefix6_prefix_reachable hmp78 (ms₄₃ ++ pre₄) _ hms
    have hnoleak_pre₄ : ∀ v ∈ runVis r (ms₄₃ ++ pre₄), v.kind ≠ .leak := by intro v hv; rw [Symbolic.Swarm.CREF.runVis_append, runMoves_snd_of_movesFrom_invisibleNoEffect hpre₄, List.append_nil] at hv; exact hnoleak43 v hv
    obtain ⟨rfl, rfl, _, _, ikA₄, hid₄, hm₄_next⟩ := pia_bundle_inv_of_reachable hwf.1 rfl hns_pre₄ hreach_pre₄ hnoleak_pre₄ hnb_pre₄ hdone₄ hm₄_alice bundle43_byte4_ne_one
    let o₄ := iniAliceOut tr₄ ikA₄ (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    have hm₄_next' : (Move.aliceStart a₄ r.bob idS₄ 6 hb₄ shown₄).next tr₄ = iniAliceStartTr tr₄ a₄ r.bob o₄ := hm₄_next
    rw [hm₄_next'] at hat hm₄_alice; rw [at?_trSt_iniAliceStartTr tr₄ a₄ r.bob o₄ j] at hat
    split_ifs at hat with hj
    · injection hat with hls_eq
      exact .inr ⟨tr₄, a₄, ikA₄, hb₄, recvAt 43, PtDead78.call4Rng, hid₄, .inr rfl, hm₄_alice,
        .inl (congrArg (fun e : TRStEntry => e.st) hls_eq.symm)⟩
    · rw [hms]; exact .inl (ptAvoidFull_append _ (hst_pre₄ ls (mem_storedStates_iff.mpr ⟨j, hge, XplSteps.xlt_of_at?_some hat, hat⟩)))
theorem trace_take_78_eq : trace.take 78 = ((((.recv bundle0 :: call0Rng) ++ [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)]) ++ [.pt (ptAt 38), .send (sendAt 39)]) ++ seg 40 3) ++ seg 43 35 := by
  rw [take78_eq, take43_eq, take40_eq, seg38_eq_explicit, trace_take_38_eq]
theorem pre78PrefixInv_ws {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move} (hwf : RecordsWF r) (hnb : CompSetupSecrecy.NoBrk r ms) (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who₀ g ms (trace.take 78)) : PtDead78.Pre78PrefixInv r S g ms := by
  rw [trace_take_78_eq] at hmp
  exact pre78PrefixInv_rs (rs₁ := [.rng (rngAt 36)]) (rs₂ := []) hwf hnb
    (fun e he => by simp at he; subst he; rfl)
    (fun c hc => by simp at hc; subst hc; exact self_mem_inits _)
    (fun _ he => by cases he) (fun _ hc => by cases hc) hmp
theorem ptDeadAt78 : SpecTop.PtDeadAt 78 := PtDead78.ptDeadAt78_of (fun _ _ _ _ hfits hexp hnb => pre78PrefixInv_ws hfits.1.1 hnb hexp.1)
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78b
