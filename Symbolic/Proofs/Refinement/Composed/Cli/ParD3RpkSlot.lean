/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.World.TopPure
public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.World.HeldRecPure
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.DirBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewAccept
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewTieBundle
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyOverModel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromAccept
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromReject
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromSlot
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlotsSend
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Shadow-Turn Simulation and Responder Pre-Key Receive Slot

Defines the shadow-turn simulation `PqTurnSim1A` coupling concrete turns to clean single-session
shadow turns and proves `slot_rpk_d3_pqModelRel` dispatching responder `recv` calls under
`PqModelRel`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace DY.Libsignal.Composed.Refinement.Cli.ParD3

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli

/-! ## Shadow-turn simulation -/

/-- Couples concrete turn `t` to a clean shadow turn `t_clean` (`t_clean.bobOff = false`) with
matching stripped session records. -/
structure PqTurnSim1A (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t t_clean : CliTurn) (accepted : List HwBytes) : Prop where
  dirInv : PqDirInv interp P r t_clean accepted
  clean_bobOff : t_clean.bobOff = false
  sent_eq : t_clean.sent = t.sent
  dirs_other : ∀ q, q ≠ r.bob → t_clean.dirs q = t.dirs q
  bobOff_false_eq : t.bobOff = false → t_clean = t
  bob_nonSession : ∀ path, SamePath path (sessionPathOf r r.bob) = false →
    t.dirs r.bob path = t_clean.dirs r.bob path
  strip_eq : pureStripPrev (t.records r) = pureStripPrev (t_clean.leakRecords r)

theorem pqTurnSim1A_refl {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t : CliTurn} {accepted : List HwBytes}
    (hDir : PqDirInv interp P r t accepted) (hoff : t.bobOff = false) :
    PqTurnSim1A interp P r t t accepted where
  dirInv := hDir
  clean_bobOff := hoff
  sent_eq := rfl
  dirs_other := fun _ _ => rfl
  bobOff_false_eq := fun _ => rfl
  bob_nonSession := fun _ _ => rfl
  strip_eq := by rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hoff]

theorem pqTurnSim1A_init {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    (hr : ProtocolSetupWF r) (hagree : ModelAgree interp P) :
    PqTurnSim1A (interpOfParams interp P) P r
      (CliTurn.init (initDirs (interpOfParams interp P) r))
      (CliTurn.init (initDirs (interpOfParams interp P) r)) [] :=
  pqTurnSim1A_refl (pqDirInv_init_interpOfParams hr hagree) rfl

theorem pqTurnSim1A_opkUsed_eq {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t t_clean : CliTurn} {accepted : List HwBytes}
    (hsim : PqTurnSim1A interp P r t t_clean accepted) :
    t.opkUsed r = t_clean.opkUsed r :=
  opkUsed_eq_of_bob_agree hsim.bob_nonSession

theorem keyInDirs_iff_keyInDirsV1_clean {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t_clean : CliTurn} {accepted : List HwBytes} {k : HwBytes}
    (hsim : PqTurnSim1A interp P r t t_clean accepted) :
    KeyInDirs r t k ↔ KeyInDirsV1 r t_clean k := by
  unfold KeyInDirs KeyInDirsV1
  rw [Symbolic.Swarm.CREF.CliPure.leakableSecret_pureStripPrev_iff r (t.records r),
      Symbolic.Swarm.CREF.CliPure.leakableSecret_pureStripPrev_iff r (t_clean.leakRecords r),
      hsim.strip_eq, pqTurnSim1A_opkUsed_eq hsim]

private theorem cliTurn_ext {a b : CliTurn}
    (hd : a.dirs = b.dirs) (hs : a.sent = b.sent) (hb : a.bobOff = b.bobOff) : a = b := by
  cases a; cases b; cases hd; cases hs; cases hb; rfl

theorem pqTurnSim1A_clearSession {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t t_clean : CliTurn} {accepted : List HwBytes} (p : Participant)
    (hr : ProtocolSetupWF r) (hsim : PqTurnSim1A interp P r t t_clean accepted) :
    PqTurnSim1A interp P r (t.clearSession r p) (t_clean.clearSession r p) accepted where
  dirInv := pqDirInv_clear p hr hsim.dirInv
  clean_bobOff := by simp [CliTurn.clearSession, hsim.clean_bobOff]
  sent_eq := by simp [CliTurn.clearSession, hsim.sent_eq]
  dirs_other := fun q hqb => by
    by_cases hqp : q = p
    · subst hqp
      funext path
      simp [CliTurn.clearSession, hsim.dirs_other q hqb]
    · simp [CliTurn.clearSession, hqp, hsim.dirs_other q hqb]
  bobOff_false_eq := fun hbo' => by
    by_cases hpb : p = r.bob
    · subst hpb
      refine cliTurn_ext ?_ hsim.sent_eq (by simp [CliTurn.clearSession])
      funext q
      by_cases hqb : q = r.bob
      · subst hqb
        funext path
        simp only [CliTurn.clearSession, ↓reduceIte]
        cases hsp : SamePath path (sessionPathOf r r.bob)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact (hsim.bob_nonSession path hsp).symm
        · simp only [↓reduceIte]
      · simp only [CliTurn.clearSession, hqb, ↓reduceIte]
        exact hsim.dirs_other q hqb
    · have hbo : t.bobOff = false := by simpa [CliTurn.clearSession, hpb] using hbo'
      rw [hsim.bobOff_false_eq hbo]
  bob_nonSession := fun path hsp => by
    by_cases hpb : r.bob = p
    · subst hpb
      simp only [CliTurn.clearSession, ↓reduceIte, hsp, Bool.false_eq_true]
      exact hsim.bob_nonSession path hsp
    · simp only [CliTurn.clearSession, hpb, ↓reduceIte]
      exact hsim.bob_nonSession path hsp
  strip_eq := by
    funext q
    unfold pureStripPrev
    rw [Symbolic.Swarm.CREF.CliPure.clearSession_records, Symbolic.Swarm.CREF.CliPure.clearSession_leakRecords]
    by_cases hqp : q = p
    · simp [hqp]
    · simp only [hqp, ↓reduceIte]
      exact congrFun hsim.strip_eq q

theorem pqTurnSim1A_nonBob_after {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t t_clean : CliTurn} {accepted accepted' : List HwBytes}
    {c : CliCall} {c1 : CliCall} {code : Nat} {out : HwBytes} {files files1 : DirectorySnapshot}
    (hsim : PqTurnSim1A interp P r t t_clean accepted)
    (hp_ne : c.party ≠ r.bob)
    (hp_eq : c1.party = c.party)
    (hcmd_eq : c1.cmd = c.cmd)
    (hscr_eq : scrub files = scrub files1)
    (hDir' : PqDirInv interp P r (t_clean.after r c1 code out files1) accepted') :
    PqTurnSim1A interp P r (CliTurn.after t r c code out files)
      (t_clean.after r c1 code out files1) accepted' := by
  have hnnm3 : ¬ PreKeyNoMatch r t c := fun h => hp_ne h.1
  have hnnm1 : ¬ PreKeyNoMatch r t_clean c1 := fun h => hp_ne (hp_eq ▸ h.1)
  have hbo_clean' : (t_clean.after r c1 code out files1).bobOff = false := by
    simp [CliTurn.after, hsim.clean_bobOff, hnnm1]
  have hbo_t' : (CliTurn.after t r c code out files).bobOff = t.bobOff := by
    simp [CliTurn.after, hnnm3]
  refine
    { dirInv := hDir'
      clean_bobOff := hbo_clean'
      sent_eq := by
        dsimp only [CliTurn.after]
        rw [hsim.sent_eq, hcmd_eq]
      dirs_other := fun q hqb => by
        by_cases hqc : q = c.party
        · subst hqc; simp [CliTurn.after, hp_eq, hscr_eq]
        · have hqc1 : q ≠ c1.party := hp_eq ▸ hqc
          simp [CliTurn.after, hqc, hqc1, hsim.dirs_other q hqb]
      bobOff_false_eq := fun hbo => by
        have ht_f : t.bobOff = false := hbo_t' ▸ hbo
        have htc := hsim.bobOff_false_eq ht_f
        subst htc
        refine cliTurn_ext ?_ ?_ (hbo_clean'.trans hbo.symm)
        · funext q
          by_cases hqc : q = c.party
          · subst hqc; simp [CliTurn.after, hp_eq, hscr_eq]
          · have hqc1 : q ≠ c1.party := hp_eq ▸ hqc
            simp [CliTurn.after, hqc, hqc1]
        · dsimp only [CliTurn.after]
          rw [hcmd_eq]
      bob_nonSession := fun path hsp => by
        have hbn : r.bob ≠ c.party := hp_ne.symm
        have hbn1 : r.bob ≠ c1.party := hp_eq ▸ hbn
        simp [CliTurn.after, CliTurn.after, hbn, hbn1, hsim.bob_nonSession path hsp]
      strip_eq := by
        rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hbo_clean']
        funext q
        by_cases hqc : q = c.party
        · subst hqc
          have hd_eq : (CliTurn.after t r c code out files).dirs c.party =
              (t_clean.after r c1 code out files1).dirs c.party := by
            simp [CliTurn.after, CliTurn.after, hp_eq, hscr_eq]
          unfold pureStripPrev CliTurn.records
          rw [hd_eq]
        · have hqc1 : q ≠ c1.party := hp_eq ▸ hqc
          have hrec_t : (CliTurn.after t r c code out files).records r q = t.records r q := by
            simp [CliTurn.records, CliTurn.after, hqc]
          have hrec_c : (t_clean.after r c1 code out files1).records r q =
              t_clean.leakRecords r q := by
            rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hsim.clean_bobOff]
            simp [CliTurn.records, CliTurn.after, hqc1]
          unfold pureStripPrev
          rw [hrec_t, hrec_c]
          exact congrFun hsim.strip_eq q }

/-! ## Call conversion and step helpers -/

def toCliCallNone (c : CliCall) : CliCall :=
  { party := c.party, cmd := c.cmd, bundle := [], stdin := c.stdin, coins := c.coins }

theorem inputsFor_toCliCallNone {c : CliCall} {d : DirectorySnapshot} {i : Inputs}
    (hbun : c.bundle = []) (hin : InputsFor c d i) :
    InputsFor (toCliCallNone c) d i := by
  have hextra : c.extra = (toCliCallNone c).extra := by
    simp [CliCall.extra, CliCall.extra, toCliCallNone, hbun]
  exact ⟨hin.1, hin.2.1, hin.2.2.1, fun p hp => hextra ▸ hin.2.2.2.1 p hp, hin.2.2.2.2⟩

theorem cliEntryEvents_eq_send {c : CliCall} {peer : Address} (hcmd : c.cmd = .send peer) :
    cliEntryEvents c = cliEntryEvents (toCliCallNone c) := by
  simp [cliEntryEvents, cliEntryEvents, toCliCallNone, hcmd]

theorem cliEntryEvents_eq_recv {c : CliCall} {peer : Address} (hcmd : c.cmd = .recv peer) :
    cliEntryEvents c = cliEntryEvents (toCliCallNone c) := by
  simp [cliEntryEvents, cliEntryEvents, toCliCallNone, hcmd]

theorem cliExitEvents_eq (c : CliCall) (code : Nat) (out : HwBytes) :
    cliExitEvents c code out = cliExitEvents (toCliCallNone c) code out :=
  rfl

theorem afterD3_eq_after_of_not_noMatch {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hn3 : ¬ PreKeyNoMatch r t c) (hn1 : ¬ PreKeyNoMatch r t (toCliCallNone c)) :
    CliTurn.after t r c code out files = t.after r (toCliCallNone c) code out files := by
  refine cliTurn_ext ?_ ?_ ?_
  · funext q; by_cases hq : q = c.party <;> simp [CliTurn.after, toCliCallNone, hq]
  · rfl
  · simp [CliTurn.after, hn3, hn1]

theorem clean_dirs_caller_eq {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t t_clean : CliTurn} {accepted : List HwBytes} {c : CliCall}
    (hr : ProtocolSetupWF r) (hsim : PqTurnSim1A interp P r t t_clean accepted)
    (hbca : BobCallAllowed r t c) (hp : c.party = r.alice ∨ c.party = r.bob) :
    t_clean.dirs c.party = t.dirs c.party ∧
    t_clean.records r c.party = t.records r c.party ∧
    BobCallAllowed r t_clean (toCliCallNone c) := by
  have hbca_clean : BobCallAllowed r t_clean (toCliCallNone c) := fun hbo =>
    absurd (hsim.clean_bobOff.symm.trans hbo) Bool.false_ne_true
  have hd_eq : t_clean.dirs c.party = t.dirs c.party := by
    rcases hp with ha | hb
    · rw [ha]; exact hsim.dirs_other r.alice hr.1
    · have hoff : t.bobOff = false := by
        cases hbo : t.bobOff
        · rfl
        · exact absurd hb (hbca hbo)
      rw [hsim.bobOff_false_eq hoff]
  exact ⟨hd_eq, by simp [CliTurn.records, hd_eq], hbca_clean⟩

theorem pqTurnSim1A_caller_after {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t t_clean : CliTurn} {accepted accepted' : List HwBytes}
    {c : CliCall} {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    (hr : ProtocolSetupWF r) (hsim : PqTurnSim1A interp P r t t_clean accepted)
    (hbca : BobCallAllowed r t c) (hp : c.party = r.alice ∨ c.party = r.bob)
    (hn3 : ¬ PreKeyNoMatch r t c) (hn1 : ¬ PreKeyNoMatch r t_clean (toCliCallNone c))
    (hDir' : PqDirInv interp P r (t_clean.after r (toCliCallNone c) code out files) accepted') :
    PqTurnSim1A interp P r (CliTurn.after t r c code out files)
      (t_clean.after r (toCliCallNone c) code out files) accepted' := by
  rcases hp with ha | hb
  · exact pqTurnSim1A_nonBob_after (c1 := toCliCallNone c) hsim (ha ▸ hr.1) rfl rfl rfl hDir'
  · have hoff : t.bobOff = false := by
      cases hbo : t.bobOff
      · rfl
      · exact absurd hb (hbca hbo)
    have htc : t_clean = t := hsim.bobOff_false_eq hoff
    subst t_clean
    have hafter_eq := afterD3_eq_after_of_not_noMatch hn3 hn1 (code := code) (out := out)
      (files := files)
    have hbo' : (t.after r (toCliCallNone c) code out files).bobOff = false := by
      simp [CliTurn.after, hoff, hn1]
    rw [hafter_eq]
    exact pqTurnSim1A_refl hDir' hbo'

theorem afterD3_eq_self_of_recv_exit1 {r : ProtocolSetup} {t : CliTurn} {c : CliCall}
    {peer : Address} {files : DirectorySnapshot}
    (hcmd : c.cmd = .recv peer) (hscr : scrub files = t.dirs c.party) :
    CliTurn.after t r c 1 [] files = t := by
  cases t
  dsimp only [CliTurn.after]
  congr 1
  · funext q
    split_ifs with hq
    · rw [hq, hscr]
    · rfl
  · simp [hcmd]
  · simp

private theorem bob_recv_d3_reject_step {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {peer : Address} {files : DirectorySnapshot}
    {accepted : List HwBytes} {acc_hw : List MachineEvent}
    (hDir : PqDirInv interp P r t accepted)
    (hoff : t.bobOff = false)
    (hcmd : c.cmd = .recv peer)
    (hscr : scrub files = t.dirs c.party) :
    ∃ (blk_hw : List MachineEvent) (t_clean' : CliTurn) (accepted' : List HwBytes),
      PqTurnSim1A interp P r (CliTurn.after t r c 1 [] files) t_clean' accepted' ∧
      CoinSplit (cliEntryEvents c ++ cliExitEvents c 1 []) blk_hw ∧
      ∀ (who : List Participant) (ok : Nat → Bool),
        who[(callStarts acc_hw).length]? = some c.party →
        CliLiveAt interp r (compSemOf interp r) who ok t accepted acc_hw →
        ((∃ g ms, MatchedPrefix interp r (compSemOf interp r) who g ms (acc_hw ++ blk_hw)) ∨
          CollisionAt interp r (compSemOf interp r) who ok (acc_hw ++ blk_hw)) ∧
        (¬ CollisionAt interp r (compSemOf interp r) who ok (acc_hw ++ blk_hw) →
          ok (callStarts acc_hw).length = decide (1 = 0) →
          CliLiveAt interp r (compSemOf interp r) who ok t_clean' accepted'
            (acc_hw ++ blk_hw)) := by
  let c1 := toCliCallNone c
  have hcmd1 : c1.cmd = .recv peer := hcmd
  have hscr1 : scrub files = t.dirs c1.party := hscr
  have hafter3 : CliTurn.after t r c 1 [] files = t :=
    afterD3_eq_self_of_recv_exit1 hcmd hscr
  have hafter1 : t.after r c1 1 [] files = t := by
    cases t
    dsimp only [CliTurn.after]
    congr 1
    · funext q; split_ifs with hq <;> [exact hq ▸ hscr1; rfl]
    · simp [hcmd1]
    · simp
  have hsess : files (sessionPathOf r c1.party) = t.dirs c1.party (sessionPathOf r c1.party) := by
    rw [← Symbolic.Swarm.CREF.CliPure.scrub_sessionPathOf files r c1.party, hscr1]
  have hopk : c1.party = r.bob →
      files (oneTimePreKeyFile r.opkId) = t.dirs r.bob (oneTimePreKeyFile r.opkId) := fun hb => by
    rw [← Symbolic.Swarm.CREF.CliPure.scrub_oneTimePreKeyFile files r.opkId, ← hb, hscr1]
  have hDir1' : PqDirInv interp P r (t.after r c1 1 [] files) accepted := by
    rw [hafter1]; exact hDir
  obtain ⟨blk_hw, accepted', hDir_out, hcs, hstep⟩ :=
    rpkProm_reject_step (S := compSemOf interp r) hcmd1 Nat.one_ne_zero hDir1' hsess hopk
  rw [hafter1] at hDir_out
  refine ⟨blk_hw, t, accepted', ?_, ?_, fun who ok hwho hlive => ?_⟩
  · rw [hafter3]; exact pqTurnSim1A_refl hDir_out hoff
  · rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq]
    exact hcs
  · have hp := hstep who ok hwho hlive
    rw [hafter1] at hp
    exact hp

private theorem opkUsed_clean_after_rpk_accept {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {t : CliTurn}
    {stB st1 st' : PqParty} {m : PreKeyMessageFields} {inner : SignalMessage}
    {k : ResponderPreKeySecrets} {x' : RecordExtras} {g' : GhostState HwBytes}
    {X : UnreachedPqxdhPrimitives} {rc : BitVec 256} {out : HwBytes}
    (hr : ProtocolSetupWF r)
    (hinvB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob))
    (hB₀ : PqPartyInv interp P r accepted r.bob { stB with session := none }
      (filesOf (encodeDir P { stB with session := none })))
    (hmod : pqRecvPrekeyModel X P { stB with session := none } m rc = some (some (st', out)))
    (hk : preKeysNamedBy { stB with session := none } m = some k)
    (hmk : markKyberUsed { stB with session := none } m = some st1)
    (hst' : st' = { removeOpk st1 m with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x', g') }) :
    let t_clean' : CliTurn :=
      { dirs := fun q => if q = r.bob then filesOf (encodeDir P st') else t.dirs q
        sent := t.sent
        bobOff := false }
    t_clean'.opkUsed r =
      (t.opkUsed r || (Slots.rpkNew_preKeyFieldsOf m inner).preKeyId.isSome) := by
  intro t_clean'
  obtain ⟨_, hst'_inv, _⟩ := pqPartyInv_of_pqRecvPrekeyModel_fresh hr.1 hinvB hmod
  have hst'_turn : PqPartyInv interp P r (accepted ++ [djbKey m.baseKey]) r.bob st'
      (t_clean'.dirs r.bob) := by
    simpa [t_clean'] using hst'_inv
  have hopk_B := opkUsed_of_pqPartyInv hr.1 hinvB
  have hopk_B' := opkUsed_of_pqPartyInv hr.1 hst'_turn
  let t₀ : CliTurn :=
    { dirs := fun q =>
        if q = r.bob then filesOf (encodeDir P { stB with session := none }) else t.dirs q
      sent := t.sent
      bobOff := false }
  have hB₀_turn : PqPartyInv interp P r accepted r.bob { stB with session := none }
      (t₀.dirs r.bob) := by simpa [t₀] using hB₀
  have hk_post := Slots.pqPartyInv_bob_keysFor_inv hr.1 hB₀_turn hk
  obtain ⟨_, _, _, _, h1_ot, _⟩ :=
    Slots.pqPartyInv_bob_markKyberUsed_inv hr.1 hB₀_turn hk_post.spkId_eq hk_post.kpkId_eq hmk
  obtain ⟨_, _, ho_B, _⟩ := hinvB.bob_stores hr.1.symm
  rcases hk_post.opk_cases with ⟨hnone, _⟩ | ⟨hyes, _, hopk_some, _⟩
  · have hp_false : (Slots.rpkNew_preKeyFieldsOf m inner).preKeyId.isSome = false := by
      simp [Slots.rpkNew_preKeyFieldsOf, hnone]
    rw [hp_false, Bool.or_false]
    have hot_eq : st'.oneTime = stB.oneTime := by
      rw [hst']; simp [removeOpk, hnone, h1_ot]
    cases hw : r.withOpk
    · rw [hopk_B'.1 hw, hopk_B.1 hw]
    · rcases ho_B with ⟨hno_w, _⟩ | ⟨_, hot_s | hot_n⟩
      · cases hno_w.symm.trans hw
      · rw [(hopk_B'.2 hw).1.mpr (hot_eq.trans hot_s), (hopk_B.2 hw).1.mpr hot_s]
      · rw [(hopk_B'.2 hw).2.mpr (hot_eq.trans hot_n), (hopk_B.2 hw).2.mpr hot_n]
  · have hp_true : (Slots.rpkNew_preKeyFieldsOf m inner).preKeyId.isSome = true := by
      simp [Slots.rpkNew_preKeyFieldsOf, hopk_some]
    rw [hp_true, Bool.or_true]
    have hot' : st'.oneTime = [(r.opkId, none)] := by
      rw [hst']; dsimp only
      simp only [removeOpk, hopk_some, h1_ot]
      rcases ho_B with ⟨hno_w, _⟩ | ⟨_, hot_s | hot_n⟩
      · cases hno_w.symm.trans hyes
      · simp [hot_s]
      · simp [hot_n]
    exact (hopk_B'.2 hyes).2.mpr hot'

private theorem encodeRecordX_lt_2_63_of_rpkAcceptBin {pf : PreKeyFields} {sm : StateAndMessage}
    (hb : RpkAcceptBin pf sm) : sm.state.length < 2 ^ 63 := by
  obtain ⟨_, _, _, _, hinv, _, hsm⟩ := hb.1
  have henc := hinv.2.2.2.2.2.2
  rw [hsm]; dsimp only [Record.encodeRecord, Option.map_some, Record.msgField]
  exact Nat.lt_of_le_of_lt (Symbolic.Swarm.CREF.CliPure.TR.Pure.lenField_length_le 1 _) (by omega)

private theorem bob_recv_d3_pqInputs_reject_step {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t : CliTurn} {c : CliCall} {peer : Address} {stB : PqParty}
    {accepted : List HwBytes} {acc_hw : List MachineEvent}
    (hDir : PqDirInv interp P r t accepted) (hoff : t.bobOff = false)
    (hbob : c.party = r.bob) (hcmd : c.cmd = .recv peer)
    (hinvB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob))
    (s_in : HwBytes) (rc : BitVec 256) :
    ∃ (blk_hw : List MachineEvent) (t_clean' : CliTurn) (accepted' : List HwBytes),
      PqTurnSim1A interp P r
        (CliTurn.after t r c 1 [] (filesOf (pqRecvInputs P stB s_in rc).files)) t_clean' accepted' ∧
      CoinSplit (cliEntryEvents c ++ cliExitEvents c 1 []) blk_hw ∧
      ∀ (who : List Participant) (ok : Nat → Bool),
        who[(callStarts acc_hw).length]? = some c.party →
        CliLiveAt interp r (compSemOf interp r) who ok t accepted acc_hw →
        ((∃ g ms, MatchedPrefix interp r (compSemOf interp r) who g ms (acc_hw ++ blk_hw)) ∨
          CollisionAt interp r (compSemOf interp r) who ok (acc_hw ++ blk_hw)) ∧
        (¬ CollisionAt interp r (compSemOf interp r) who ok (acc_hw ++ blk_hw) →
          ok (callStarts acc_hw).length = decide (1 = 0) →
          CliLiveAt interp r (compSemOf interp r) who ok t_clean' accepted' (acc_hw ++ blk_hw)) :=
  bob_recv_d3_reject_step hDir hoff hcmd <| by
    rw [hbob, hinvB.dir_eq]
    exact scrub_filesOf_pqInputs_reject P stB _ [] _ _ (fun _ h => nomatch h) (fun _ h => nomatch h)

private theorem rpk_d3_matching_live_step {interp' : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} (hr : ProtocolSetupWF r) (hext' : ExternContractsHoldCli interp')
    (hmb : ModelHookBridge interp' P) {t t' : CliTurn} {stB st' : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {s : SessionState HwBytes}
    {rec_ body c_coins out : HwBytes} {q : PreKeyFields}
    {accepted : List HwBytes} {acc_hw : List MachineEvent} {who : List Participant} {ok : Nat → Bool}
    (hbinv : BobPromDirInv interp' P r stB rec_) (hsess : stB.session = some (x, g))
    (hrec_eq : rec_ = encodeRecordUnderExtras (fun _ => x) g) (hlen_rec : rec_.length < 2 ^ 31)
    (hpm : EligibleForSessionPromotion rec_ (wirePrekey :: body)) (hleak_bob : t.leakRecords r r.bob = some rec_)
    (hcoins : c_coins.length = 32) (hq : parsePreKey body = some q)
    (hok_mod : pqRecvMatchingFieldsModel P stB x g q (HKDF.bytesToKey32 c_coins) =
      some (some (st', out)))
    (hst'_eq : st' = { stB with session := some (x, { g with session := s }) })
    (hpqh_b : ∀ q₀, parsePreKeyWire (wirePrekey :: body) = some q₀ → PqFromHonest t.sent q₀.message)
    (hwho : who[(callStarts acc_hw).length]? = some r.bob)
    (hlive : CliLiveAt interp' r (compSemOf interp' r) who ok t accepted acc_hw)
    (hleak_after : t'.leakRecords r = fun p =>
      if p = r.bob then some (encodeRecordUnderExtras (fun _ => x) { g with session := s })
      else t.leakRecords r p)
    (hsent_after : t'.sent = t.sent) (hopk_after : t'.opkUsed r = t.opkUsed r) :
    ((∃ g₀ ms₀, MatchedPrefix interp' r (compSemOf interp' r) who g₀ ms₀
        (acc_hw ++ promAccBlk (wirePrekey :: body) (rpkPromMid interp' x g q.inner c_coins) out)) ∨
      CollisionAt interp' r (compSemOf interp' r) who ok
        (acc_hw ++ promAccBlk (wirePrekey :: body) (rpkPromMid interp' x g q.inner c_coins) out)) ∧
    (¬ CollisionAt interp' r (compSemOf interp' r) who ok
        (acc_hw ++ promAccBlk (wirePrekey :: body) (rpkPromMid interp' x g q.inner c_coins) out) →
      ok (callStarts acc_hw).length = decide (0 = 0) →
      CliLiveAt interp' r (compSemOf interp' r) who ok t' accepted
        (acc_hw ++ promAccBlk (wirePrekey :: body) (rpkPromMid interp' x g q.inner c_coins) out)) := by
  obtain ⟨hclean, hrel, hopk⟩ := hlive
  obtain ⟨s', _, _, _, _, hst'_eq', _, _, _, hhon_wire, hout⟩ :=
    pqRecvMatchingFieldsModel_accept_eval hmb hbinv hsess hrec_eq hleak_bob
      hrel.oooAll hrel.bkn hcoins hq hok_mod
  have hs_eq : s' = s := by
    have h1 : st'.session = some (x, { g with session := s }) := by rw [hst'_eq]
    have h2 : st'.session = some (x, { g with session := s' }) := by rw [hst'_eq']
    exact congrArg GhostState.session (Prod.mk.inj (Option.some.inj (h2.symm.trans h1))).2
  have hstep := purePromAcceptStepSpec_proved interp' r (compSemOf interp' r)
    hr hext' rfl who ok (t.leakRecords r) t.sent accepted (t.opkUsed r)
    acc_hw _ _ _ _ _ _ _ _ _ _
    hwho hleak_bob (Nat.lt_trans hlen_rec (by decide)) hpm hhon_wire hpqh_b
    hclean hrel hopk hout
  refine ⟨hstep.1, fun hncol hok_b => ?_⟩
  obtain ⟨hclean', hrel', hopk'⟩ := hstep.2 hncol (by simpa using hok_b)
  rw [hs_eq] at hrel'
  rw [CliLiveAt, hleak_after, hsent_after, hopk_after]
  exact ⟨hclean', hrel', hopk'⟩

/-! ## Responder `recv` slot -/

set_option maxHeartbeats 600000 in
/-- Dispatches responder `recv` calls under `ValidCall` and `PqModelRel`, advancing `PqTurnSim1A`
and `CliLiveAt` at `compSemOf`. -/
theorem slot_rpk_d3_pqModelRel
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {acc_hw : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (hbob : c.party = r.bob)
    (hcmd : c.cmd = .recv (peerOf r r.bob))
    (hbun : c.bundle = [])
    (hcoins : c.coins.length = 32)
    (hsb : StdinBounded c)
    (hfb : FilesBounded (t.dirs c.party))
    (hbca : BobCallAllowed r t c)
    (hkind : c.stdin.head? ≠ some wireWhisperTag ∨ t.records r r.bob = none)
    (hpqh : ∀ q, parsePreKeyWire c.stdin = some q → PqFromHonest t.sent q.message)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    ∃ (blk_hw : List MachineEvent) (t_clean' : CliTurn) (accepted' : List HwBytes),
      PqTurnSim1A (interpOfParams interp P) P r
        (CliTurn.after t r c code out files) t_clean' accepted' ∧
      CoinSplit (cliEntryEvents c ++ cliExitEvents c code out) blk_hw ∧
      ∀ (who : List Participant) (ok : Nat → Bool),
        who[(callStarts acc_hw).length]? = some c.party →
        CliLiveAt (interpOfParams interp P) r (compSemOf (interpOfParams interp P) r)
          who ok t_clean accepted acc_hw →
        ((∃ g ms, MatchedPrefix (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) who g ms (acc_hw ++ blk_hw)) ∨
          CollisionAt (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) who ok (acc_hw ++ blk_hw)) ∧
        (¬ CollisionAt (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) who ok (acc_hw ++ blk_hw) →
          ok (callStarts acc_hw).length = decide (code = 0) →
          CliLiveAt (interpOfParams interp P) r
            (compSemOf (interpOfParams interp P) r) who ok t_clean' accepted'
            (acc_hw ++ blk_hw)) := by
  let interp' := interpOfParams interp P
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : ModelAgree interp' P := (modelAgree_interpOfParams interp P).mpr hagree
  have hBridge : Slots.RpkModelHookBridge interp' P := Slots.rpkModelHookBridge_interpOfParams hagree
  have hmlkem := mlkemOf_interpOfParams interp P
  have hhmac := hmacFnOf_interpOfParams interp P
  have hoff : t.bobOff = false := by
    cases hbo : t.bobOff
    · rfl
    · exact absurd hbob (hbca hbo)
  have htc_eq : t_clean = t := hsim.bobOff_false_eq hoff
  subst t_clean
  have hDir : PqDirInv interp' P r t accepted := hsim.dirInv
  have hfb_bob : FilesBounded (t.dirs r.bob) := hbob ▸ hfb
  obtain ⟨stB, hBobInv⟩ := hDir.2.1
  have hinvB : PqPartyInv interp' P r accepted r.bob stB (t.dirs r.bob) := by
    unfold PqBobInv at hBobInv; rwa [hoff] at hBobInv
  have hwfB : PqxdhPartyInSpecDomain P stB := wfPq_of_pqPartyInv hinvB hfb_bob
  let c1 := toCliCallNone c
  have hin1 : InputsFor c1 (t.dirs c1.party) i := inputsFor_toCliCallNone hbun hin
  have hi_enc : InputsFor c1 (filesOf (encodeDir P stB)) i := by
    rwa [show c1.party = r.bob from hbob, hinvB.dir_eq] at hin1
  let rc := HKDF.bytesToKey32 c.coins
  have hcoins_rc : c1.coins = HMAC.keyToBytes32 rc := (keyToBytes32_bytesToKey32 hcoins).symm
  have hcmd_stB : c1.cmd = .recv (partyAddress stB.party.other) := by
    change c.cmd = .recv (partyAddress stB.party.other)
    rw [hcmd, peerOf_eq_addrE_other, ← hinvB.party_eq]
  have heq_recv : InputsEquiv i (pqRecvInputs P stB c.stdin rc) :=
    inputsEquiv_pqRecvInputs (c := c1) hi_enc hcmd_stB rfl hcoins_rc
  have hp : PqModelPost interp P i (.exited code out files) :=
    PqModelRel.exited_iff.mp hRel
  unfold StdinBounded at hsb
  rw [hcmd] at hsb
  by_cases hw : ∃ body, c.stdin = wireWhisperTag :: body
  · obtain ⟨body, hstdin⟩ := hw
    have hrec_none : t.records r r.bob = none :=
      hkind.resolve_left (by simp [hstdin])
    have hsess_none : stB.session = none := by
      rw [records_of_pqPartyInv hinvB] at hrec_none
      cases hs : stB.session with
      | none => rfl
      | some _ => rw [hs] at hrec_none; cases hrec_none
    have hbody_lt : body.length < 2 ^ 32 := hsb.1 body hstdin
    have hstdin_w : c.stdin = wireWhisper :: body := by
      rwa [wireWhisper_eq_wireWhisperTag]
    have hmod_none : pqRecvWhisperModel P stB body rc = some none := by
      simp [pqRecvWhisperModel, hsess_none]
    have hobs := hp.recvWhisper stB body rc hwfB hbody_lt (hstdin_w ▸ heq_recv)
    rw [hmod_none] at hobs
    injection hobs with hcode hout hfiles
    subst hcode hout hfiles
    exact bob_recv_d3_pqInputs_reject_step hDir hoff hbob hcmd hinvB _ _
  · have hnw_tag : c.stdin.head? ≠ some wireWhisperTag := by
      intro hh
      cases hcs : c.stdin with
      | nil => simp [hcs] at hh
      | cons b tl =>
        simp only [hcs, List.head?_cons, Option.some.injEq] at hh
        exact hw ⟨tl, hh ▸ hcs⟩
    have hlen_lt : c.stdin.length < 2 ^ 32 := hsb.2.1 hnw_tag
    by_cases hpk : ∃ body, c.stdin = wirePrekey :: body
    · obtain ⟨body, hstdin⟩ := hpk
      have hbody_lt : body.length < 2 ^ 32 := by rw [hstdin, List.length_cons] at hlen_lt; omega
      have heq_body : InputsEquiv i (pqRecvInputs P stB (wirePrekey :: body) rc) :=
        hstdin ▸ heq_recv
      cases hq : parsePreKey body with
      | none =>
        have hobs := hp.recvPrekeyReject stB body rc hwfB hbody_lt hq heq_body
        injection hobs with hcode hout hfiles
        subst hcode hout hfiles
        exact bob_recv_d3_pqInputs_reject_step hDir hoff hbob hcmd hinvB _ _
      | some q =>
        by_cases hmatch_ex : ∃ x g, stB.session = some (x, g) ∧ PqFieldsMatch x g q
        · obtain ⟨x, g, hsess, hfm⟩ := hmatch_ex
          let rec_ := encodeRecordUnderExtras (fun _ => x) g
          have hrec_bob : t.records r r.bob = some rec_ := by
            rw [records_of_pqPartyInv hinvB, hsess]; rfl
          have hlen_rec : rec_.length < 2 ^ 31 := (hwfB.1 x g hsess).2.2
          have hpm : EligibleForSessionPromotion rec_ (wirePrekey :: body) :=
            promoteMatch_of_pqFieldsMatch hwfB hsess hq hfm
          have hpm_c : EligibleForSessionPromotion rec_ c.stdin := hstdin.symm ▸ hpm
          have hnnm3 : ¬ PreKeyNoMatch r t c := by
            rintro ⟨_, _, _, rec₁, hrec₁, hnprom⟩
            cases Option.some.inj (hrec_bob.symm.trans hrec₁); exact hnprom hpm_c
          have hnnm1 : ¬ PreKeyNoMatch r t c1 := by
            rintro ⟨_, _, _, rec₁, hrec₁, hnprom⟩
            cases Option.some.inj (hrec_bob.symm.trans hrec₁); exact hnprom hpm_c
          have hobs := hp.recvPrekeyMatching stB x g body q rc hwfB hsess hbody_lt hq hfm heq_body
          rcases exited_eq_pqObserve_iff.mp hobs with
              ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hok_mod, rfl, rfl, rfl⟩
          · exact bob_recv_d3_pqInputs_reject_step hDir hoff hbob hcmd hinvB _ _
          · have hbinv : BobPromDirInv interp' P r stB rec_ :=
              bobPromDirInv_of_pqPartyInv hr hagree' hinvB hfb_bob hrec_bob
            obtain ⟨s, htrusts, _, hdec, hst'_raw⟩ := pqRecvMatchingFieldsModel_ok_inv hok_mod
            obtain ⟨_, hpeer_eq⟩ := honestIdentity_of_matching_trusts hbinv hq htrusts
            have hst'_eq : st' = { stB with session := some (x, { g with session := s }) } := by
              rw [hst'_raw, ← hpeer_eq]
            obtain ⟨_, _, htry, _⟩ := parsePreKey_some_inv hq
            obtain ⟨g₁, hrpq₁, hp₁, hs₁⟩ := rpkProm_reachPq_promote hwfB hsess htry hdec
            have hg_pty : g.party = stB.party := (hinvB.session_reach x g hsess).2
            have hst'_inv : PqPartyInv interp' P r accepted r.bob st' (filesOf (encodeDir P st')) :=
              { party_eq := by rw [hst'_eq]; exact hinvB.party_eq
                me_eq := by rw [hst'_eq]; exact hinvB.me_eq
                peerId_eq := by rw [hst'_eq]; exact hinvB.peerId_eq
                alice_stores := fun h => absurd h.symm hr.1
                bob_stores := fun h => by rw [hst'_eq]; exact hinvB.bob_stores h
                session_reach := fun x₀ g₀ hs₀ => by
                  rw [hst'_eq] at hs₀ ⊢
                  rcases Prod.mk.inj (Option.some.inj hs₀) with ⟨rfl, rfl⟩
                  exact ⟨⟨g₁, hrpq₁, hp₁, hs₁⟩, hg_pty⟩
                dir_eq := rfl }
            have hkot : stB.kyberOneTime = [] := (hinvB.bob_stores hr.1.symm).2.1
            have hsub : ∀ f ∈ encodeDir P stB, ∃ g₀ ∈ encodeDir P st', f.1 = g₀.1 := by
              rw [hst'_eq]; exact encodeDir_sub_of_fields rfl rfl rfl rfl rfl hkot hkot rfl
            let files_acc :=
              filesOf ((pqRecvInputs P stB (wirePrekey :: body) rc).files ++ encodeDir P st')
            have hscr : scrub files_acc = filesOf (encodeDir P st') :=
              scrub_filesOf_pqInputs_accept P stB st' _ [] _ _
                (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
            have hDir' : PqDirInv interp' P r (t.after r c1 0 out files_acc) accepted :=
              pqDirInv_after_accept_same hr.1 hDir (Or.inr ⟨hbob, hoff⟩) hnnm1 hscr
                (by simpa [c1, toCliCallNone, hbob] using hst'_inv)
            have hbo_after : (t.after r c1 0 out files_acc).bobOff = false := by
              simp [CliTurn.after, hoff, hnnm1]
            have hafter_eq : CliTurn.after t r c 0 out files_acc =
                t.after r c1 0 out files_acc :=
              afterD3_eq_after_of_not_noMatch hnnm3 hnnm1
            let mid := rpkPromMid interp' x g q.inner c.coins
            have hcs : CoinSplit (cliEntryEvents c1 ++ cliExitEvents c1 0 out)
                (promAccBlk c1.stdin mid out) := by
              have hcmd1 : c1.cmd = .recv (peerOf r r.bob) := hcmd
              unfold mid rpkPromMid; split_ifs
              · exact coinSplit_rpkProm_accept_rng hcmd1 hcoins out
              · exact coinSplit_rpkProm_accept_nil hcmd1 out
            refine ⟨promAccBlk c.stdin mid out, t.after r c1 0 out files_acc, accepted,
              ?_, ?_, fun who ok hwho hlive => ?_⟩
            · change PqTurnSim1A interp' P r (CliTurn.after t r c 0 out files_acc) _ _
              rw [hafter_eq]; exact pqTurnSim1A_refl hDir' hbo_after
            · rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq]; exact hcs
            · have hleak_bob : t.leakRecords r r.bob = some rec_ := by
                rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hoff, hrec_bob]
              have hst'_after : PqPartyInv interp' P r accepted r.bob st'
                  ((t.after r c1 0 out files_acc).dirs r.bob) := by
                simpa [CliTurn.after, c1, toCliCallNone, hbob, hscr] using hst'_inv
              have hleak_after : (t.after r c1 0 out files_acc).leakRecords r =
                  fun p => if p = r.bob then
                    some (encodeRecordUnderExtras (fun _ => x) { g with session := s })
                  else t.leakRecords r p := by
                rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hbo_after,
                    Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hoff]
                funext p; by_cases hpb : p = r.bob
                · subst hpb; rw [records_of_pqPartyInv hst'_after, hst'_eq]; simp
                · have hpc1 : p ≠ c1.party := by simpa [c1, toCliCallNone, hbob] using hpb
                  simp [CliTurn.records, CliTurn.after, hpb, hpc1]
              have hsent_after : (t.after r c1 0 out files_acc).sent = t.sent := by
                simp [CliTurn.after, c1, toCliCallNone, hcmd]
              have hopk_after : (t.after r c1 0 out files_acc).opkUsed r = t.opkUsed r := by
                have hB_pre : PqBobInv interp' P r accepted t.bobOff stB (t.dirs r.bob) := by
                  unfold PqBobInv; rw [hoff]; exact hinvB
                have hB_post : PqBobInv interp' P r accepted
                    (t.after r c1 0 out files_acc).bobOff st'
                    ((t.after r c1 0 out files_acc).dirs r.bob) := by
                  unfold PqBobInv; rw [hbo_after]; exact hst'_after
                exact opkUsed_eq_of_pqBobInv_oneTime_eq hr.1 hB_post hB_pre (by rw [hst'_eq])
              rw [show promAccBlk c.stdin mid out = promAccBlk (wirePrekey :: body) mid out by
                rw [hstdin]]
              exact rpk_d3_matching_live_step hr hext' (modelHookBridge_interpOfParams hagree)
                hbinv hsess rfl hlen_rec hpm hleak_bob hcoins hq hok_mod hst'_eq (hstdin ▸ hpqh)
                (hbob ▸ hwho) hlive hleak_after hsent_after hopk_after
        · have hno_fm : ∀ x g, stB.session = some (x, g) → ¬ PqFieldsMatch x g q :=
            fun x g hs hfm => hmatch_ex ⟨x, g, hs, hfm⟩
          cases hm : preKeyOfBody? body with
          | none =>
            have hobs := hp.recvPrekeyUntyped stB body q rc hwfB hbody_lt hq hm hno_fm heq_body
            injection hobs with hcode hout hfiles
            subst hcode hout hfiles
            exact bob_recv_d3_pqInputs_reject_step hDir hoff hbob hcmd hinvB _ _
          | some m =>
            obtain ⟨q₁, hq₁, hv4, hminner, _, _, _, _, hbk_q, _, _⟩ := preKeyOfBody?_some_inv hm
            cases Option.some.inj (hq.symm.trans hq₁)
            have hp_b : parsePreKeyWire (wirePrekey :: body) = some q := by simpa using hq
            have hmlt : m.inner.length + 2048 < 2 ^ 32 := hminner ▸ hsb.2.2.1 q (hstdin ▸ hp_b)
            cases hsess : stB.session with
            | none =>
              have hvac : ∀ x g, stB.session = some (x, g) → PqSessionMatches x g m := by
                intro _ _ hs; rw [hsess] at hs; cases hs
              have hobs :=
                hp.recvPrekeyParsed (Xof interp' P) stB body m rc hwfB hbody_lt hm hmlt hvac
                  heq_body
              rcases exited_eq_pqObserve_iff.mp hobs with
                  ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hmod, rfl, rfl, rfl⟩
              · exact bob_recv_d3_pqInputs_reject_step hDir hoff hbob hcmd hinvB _ _
              · have hrec_none : t.records r r.bob = none := by
                  rw [records_of_pqPartyInv hinvB, hsess]; rfl
                have hnnm3 : ¬ PreKeyNoMatch r t c := by
                  rintro ⟨_, _, _, _, hsome, _⟩; rw [hrec_none] at hsome; cases hsome
                have hnnm1 : ¬ PreKeyNoMatch r t c1 := by
                  rintro ⟨_, _, _, _, hsome, _⟩; rw [hrec_none] at hsome; cases hsome
                have hstB_none_eq : ({ stB with session := none } : PqParty) = stB := by
                  cases stB; cases hsess; rfl
                have hmod' : pqRecvPrekeyModel (Xof interp' P) P { stB with session := none } m rc =
                    some (some (st', out)) := by rwa [hstB_none_eq]
                obtain ⟨_, hst'_inv, hsub⟩ :=
                  pqPartyInv_of_pqRecvPrekeyModel_fresh hr.1 hinvB hmod'
                let files_acc :=
                  filesOf ((pqRecvInputs P stB (wirePrekey :: body) rc).files ++ encodeDir P st')
                have hscr : scrub files_acc = filesOf (encodeDir P st') :=
                  scrub_filesOf_pqInputs_accept P stB st' _ [] _ _
                    (fun _ h => nomatch h) (fun _ h => nomatch h) hsub
                have hbo_after : (t.after r c1 0 out files_acc).bobOff = false := by
                  simp [CliTurn.after, hoff, hnnm1]
                have hafter_eq : CliTurn.after t r c 0 out files_acc =
                    t.after r c1 0 out files_acc :=
                  afterD3_eq_after_of_not_noMatch hnnm3 hnnm1
                obtain ⟨stA, hA⟩ := hDir.1
                have hDir' : PqDirInv interp' P r (t.after r c1 0 out files_acc)
                    (accepted ++ [q.baseKey.take 33]) := by
                  rw [hbk_q]
                  refine ⟨⟨stA, ?_⟩, ⟨st', ?_⟩, fun p ha hb => ?_⟩
                  · simpa only [CliTurn.after, c1, toCliCallNone, hbob, hr.1, ↓reduceIte] using
                      pqPartyInv_alice_accepted_iff.mp hA
                  · rw [hbo_after]; unfold PqBobInv
                    simpa only [Bool.false_eq_true, ↓reduceIte, CliTurn.after, c1, toCliCallNone,
                      hbob, hscr] using hst'_inv
                  · simpa only [CliTurn.after, c1, toCliCallNone, hbob, hb, ↓reduceIte] using
                      hDir.2.2 p ha hb
                obtain ⟨inner, k, x', g', st1, htf, htrust, hk, hdec, hmk, hst'⟩ :=
                  Slots.pqRecvPrekeyModel_none_ok_inv hsess hmod
                obtain ⟨_, hhon_m, hfresh_m, hst_lt, hopk_rem, hcontract_m, hBin_m, hTie_m⟩ :=
                  Slots.rpkNew_accept_tie_bundle hr hext' hagree' hBridge hmlkem hhmac hwfB hinvB
                    hcoins hmlt htf htrust hk hdec hmk
                have heq_pf := preKeyFieldsEquiv_rpkNew_of_preKeyOfBody? hm hq htf
                have hcontract := heq_pf.recvAcceptContractPure hp_b hcontract_m
                have hBin := heq_pf.rpkAcceptBin hBin_m
                have hTie := heq_pf.acceptTieD hTie_m
                have hhon := heq_pf.honestIdentity hcontract_m.parse hp_b hhon_m
                have hfresh := heq_pf.fresh hcontract_m.parse hp_b hfresh_m
                let sm : StateAndMessage := ⟨encodeRecordUnderExtras (fun _ => x') g', preKeyStoreEventsBytes m ++ out⟩
                have hB₀_dir : PqPartyInv interp' P r accepted r.bob
                    { stB with session := none }
                    (filesOf (encodeDir P { stB with session := none })) := by
                  rw [hstB_none_eq, ← hinvB.dir_eq]; exact hinvB
                have hopk_clean := opkUsed_clean_after_rpk_accept (inner := inner)
                  hr hinvB hB₀_dir hmod' (hstB_none_eq.symm ▸ hk) (hstB_none_eq.symm ▸ hmk) hst'
                have hcs : CoinSplit (cliEntryEvents c1 ++ cliExitEvents c1 0 out)
                    [.recv c.stdin, .rng c.coins, .accept out] :=
                  Slots.coinSplit_rpkNew_accept (c := c1) hcmd
                    (Slots.coins_ne_nil_of_len_32 hcoins) out
                refine ⟨[.recv c.stdin, .rng c.coins, .accept out],
                  t.after r c1 0 out files_acc, accepted ++ [q.baseKey.take 33],
                  ?_, ?_, fun who ok hwho hlive => ?_⟩
                · change PqTurnSim1A interp' P r (CliTurn.after t r c 0 out files_acc) _ _
                  rw [hafter_eq]; exact pqTurnSim1A_refl hDir' hbo_after
                · rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq]; exact hcs
                · rw [hstdin]
                  have hpqh_b : ∀ q₀, parsePreKeyWire (wirePrekey :: body) = some q₀ →
                      PqFromHonest t.sent q₀.message := hstdin ▸ hpqh
                  have hsent_eq : (t.after r c1 0 out files_acc).sent = t.sent := by
                    simp [CliTurn.after, c1, toCliCallNone, hcmd]
                  have hst'_after : PqPartyInv interp' P r (accepted ++ [djbKey m.baseKey]) r.bob
                      st' ((t.after r c1 0 out files_acc).dirs r.bob) := by
                    simpa [CliTurn.after, c1, toCliCallNone, hbob, hscr] using hst'_inv
                  have hleak_eq : (t.after r c1 0 out files_acc).leakRecords r =
                      fun p => if p = r.bob then some sm.state else t.leakRecords r p := by
                    rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hbo_after,
                        Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hoff]
                    funext p
                    by_cases hpb : p = r.bob
                    · subst hpb
                      rw [records_of_pqPartyInv hst'_after, hst']
                      simp [sm]
                    · have hpc1 : p ≠ c1.party := by simpa [c1, toCliCallNone, hbob] using hpb
                      simp [CliTurn.records, CliTurn.after, hpb, hpc1]
                  have hopk_eq : (t.after r c1 0 out files_acc).opkUsed r =
                      (t.opkUsed r || (sm.message[opkRemovedIdx]?).any (· != 0#8)) := by
                    have hdirs_eq : (t.after r c1 0 out files_acc).dirs r.bob =
                        filesOf (encodeDir P st') := by
                      simp [CliTurn.after, c1, toCliCallNone, hbob, hscr]
                    have hopk_a : (t.after r c1 0 out files_acc).opkUsed r =
                        ({ dirs := fun p => if p = r.bob then filesOf (encodeDir P st') else t.dirs p
                           sent := t.sent
                           bobOff := false } : CliTurn).opkUsed r :=
                      opkUsed_eq_of_bob_agree fun path _ => by simp [hdirs_eq]
                    rw [hopk_a, hopk_rem, hopk_clean]
                  have hstep := Slots.rpkNew_accept_cReady hext' hr rfl (hbob ▸ hwho) hlive
                    hhon hpqh_b hfresh hst_lt hcontract hBin hTie hsent_eq hleak_eq hopk_eq
                  exact ⟨hstep.1, fun hcol hok_b => hstep.2 hcol (by simpa using hok_b)⟩
            | some xg =>
              rcases xg with ⟨x, g⟩
              have hnomatch : ¬ PqSessionMatches x g m := fun hsm =>
                hno_fm x g hsess ((pqFieldsMatch_iff_pqSessionMatches x g hq hm).mpr hsm)
              have hrec_bob : t.records r r.bob = some (encodeRecordUnderExtras (fun _ => x) g) := by
                rw [records_of_pqPartyInv hinvB, hsess]; rfl
              have hlen_in : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 :=
                (hwfB.1 x g hsess).2.2
              have hnprom : ¬ EligibleForSessionPromotion (encodeRecordUnderExtras (fun _ => x) g) c.stdin := by
                rw [hstdin]
                exact fun hp_m => hno_fm x g hsess
                  (pqFieldsMatch_of_promoteMatch_v4 hwfB hsess hq hv4 hp_m)
              have hpknm3 : PreKeyNoMatch r t c :=
                ⟨hbob, ⟨peerOf r r.bob, hcmd⟩, hnw_tag,
                  encodeRecordUnderExtras (fun _ => x) g, hrec_bob, hnprom⟩
              obtain ⟨hob_ex, hnmsf⟩ :=
                hp.recvPrekeyParsedNoMatch (Xof interp' P) stB x g body m rc
                  hwfB hsess hbody_lt hm hmlt hnomatch heq_body
              rcases observedExcept_exited_iff.mp hob_ex with
                  ⟨_, rfl, rfl, rfl⟩ | ⟨st', _, hmod, rfl, rfl, hag⟩
              · exact bob_recv_d3_pqInputs_reject_step hDir hoff hbob hcmd hinvB _ _
              · obtain ⟨_, hst'_inv, hsub⟩ := pqPartyInv_of_pqRecvPrekeyModel_fresh hr.1 hinvB hmod
                have hag_scr := scrub_agreeExcept_pqInputs_accept P stB st'
                  (.recv (partyAddress stB.party.other)) [] (HMAC.keyToBytes32 rc)
                  (wirePrekey :: body) files hinvB.party_eq
                  (fun _ h => nomatch h) (fun _ h => nomatch h) hsub hag
                let stB₀ : PqParty := { stB with session := none }
                let t₀ : CliTurn :=
                  { dirs := fun p => if p = r.bob then filesOf (encodeDir P stB₀) else t.dirs p,
                    sent := t.sent, bobOff := false }
                have hwfB₀ : PqxdhPartyInSpecDomain P stB₀ := Slots.wfPq_clear_session P hwfB
                have hB₀_dir : PqPartyInv interp' P r accepted r.bob stB₀
                    (filesOf (encodeDir P stB₀)) :=
                  { party_eq := hinvB.party_eq, me_eq := hinvB.me_eq, peerId_eq := hinvB.peerId_eq,
                    alice_stores := fun h => absurd h.symm hr.1,
                    bob_stores := fun h => hinvB.bob_stores h,
                    session_reach := (fun _ _ hs => nomatch hs), dir_eq := rfl }
                have hB₀ : PqPartyInv interp' P r accepted r.bob stB₀ (t₀.dirs r.bob) := by
                  simpa [t₀] using hB₀_dir
                have hopk₀ : t₀.opkUsed r = t.opkUsed r := by
                  have ho₀ := opkUsed_of_pqPartyInv hr.1 hB₀
                  have hoB := opkUsed_of_pqPartyInv hr.1 hinvB
                  obtain ⟨_, _, ho_cases, _⟩ := hinvB.bob_stores hr.1.symm
                  cases hw_opk : r.withOpk
                  · rw [ho₀.1 hw_opk, hoB.1 hw_opk]
                  · rcases ho_cases with ⟨hno_w, _⟩ | ⟨_, hot_s | hot_n⟩
                    · cases hno_w.symm.trans hw_opk
                    · rw [(ho₀.2 hw_opk).1.mpr hot_s, (hoB.2 hw_opk).1.mpr hot_s]
                    · rw [(ho₀.2 hw_opk).2.mpr hot_n, (hoB.2 hw_opk).2.mpr hot_n]
                obtain ⟨inner, k, x', g', st1, htf, htrust, hk, hdec, hmk, hst'⟩ :=
                  Slots.pqRecvPrekeyModel_none_ok_inv (rfl : stB₀.session = none) hmod
                obtain ⟨_, hhon_m, hfresh_m, hst_lt, hopk_rem, hcontract₀, hBin_m, hTie_m⟩ :=
                  Slots.rpkNew_accept_tie_bundle hr hext' hagree' hBridge hmlkem hhmac hwfB₀ hB₀
                    hcoins hmlt htf htrust hk hdec hmk
                rw [hopk₀] at hcontract₀
                have heq_pf := preKeyFieldsEquiv_rpkNew_of_preKeyOfBody? hm hq htf
                have hcontract := heq_pf.recvAcceptContractPure hp_b hcontract₀
                have hBin := heq_pf.rpkAcceptBin hBin_m
                have hTie := heq_pf.acceptTieD hTie_m
                have hhon := heq_pf.honestIdentity hcontract₀.parse hp_b hhon_m
                have hfresh := heq_pf.fresh hcontract₀.parse hp_b hfresh_m
                let sm : StateAndMessage := ⟨encodeRecordUnderExtras (fun _ => x') g', preKeyStoreEventsBytes m ++ out⟩
                have hlen'_63 : (encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 63 :=
                  encodeRecordX_lt_2_63_of_rpkAcceptBin hBin_m
                let t_clean' : CliTurn :=
                  { dirs := fun p => if p = r.bob then filesOf (encodeDir P st') else t.dirs p,
                    sent := t.sent, bobOff := false }
                obtain ⟨stA, hA⟩ := hDir.1
                have hDir_clean' : PqDirInv interp' P r t_clean'
                    (accepted ++ [q.baseKey.take 33]) := by
                  rw [hbk_q]
                  refine ⟨⟨stA, ?_⟩, ⟨st', ?_⟩, fun p ha hb => ?_⟩
                  · simpa only [t_clean', hr.1, ↓reduceIte] using
                      pqPartyInv_alice_accepted_iff.mp hA
                  · unfold PqBobInv
                    simpa only [t_clean', Bool.false_eq_true, ↓reduceIte] using hst'_inv
                  · simpa only [t_clean', hb, ↓reduceIte] using hDir.2.2 p ha hb
                have hst'_sess : st'.session = some (x', g') := by rw [hst']
                have hsess_file_bob :
                    files (sessionPathOf r r.bob) = some (noMatchRecordBytes x g x' g') := by
                  rw [sessionPathOf_eq_sessionFile, ← hinvB.party_eq]
                  exact hnmsf st' out x' g' hmod hst'_sess 0 out files rfl
                have hrec_after_bob :
                    (CliTurn.after t r c 0 out files).records r r.bob =
                      some (noMatchRecordBytes x g x' g') := by
                  unfold CliTurn.records
                  simp only [CliTurn.after, hbob, ↓reduceIte,
                    Symbolic.Swarm.CREF.CliPure.scrub_sessionPathOf, hsess_file_bob,
                    noMatchRecordBytes_ne_nil]
                have hst'_turn : PqPartyInv interp' P r (accepted ++ [djbKey m.baseKey]) r.bob
                    st' (t_clean'.dirs r.bob) := by simpa [t_clean'] using hst'_inv
                have hrec_clean'_bob :
                    t_clean'.leakRecords r r.bob = some (encodeRecordUnderExtras (fun _ => x') g') := by
                  rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r rfl,
                      records_of_pqPartyInv hst'_turn, hst'_sess]; rfl
                have hsim' : PqTurnSim1A interp' P r (CliTurn.after t r c 0 out files)
                    t_clean' (accepted ++ [q.baseKey.take 33]) :=
                  { dirInv := hDir_clean'
                    clean_bobOff := rfl
                    sent_eq := by simp [t_clean', CliTurn.after, hcmd]
                    dirs_other := fun p hpb => by
                      have hpc : p ≠ c.party := hbob ▸ hpb
                      simp [t_clean', CliTurn.after, hpb, hpc]
                    bobOff_false_eq := fun hbo' => by
                      have hbo_t : (CliTurn.after t r c 0 out files).bobOff = true := by
                        simp [CliTurn.after, hpknm3]
                      cases hbo_t.symm.trans hbo'
                    bob_nonSession := fun path hsp => by
                      simpa [t_clean', CliTurn.after, hbob] using hag_scr path hsp
                    strip_eq := by
                      funext p; by_cases hpb : p = r.bob
                      · subst hpb; unfold pureStripPrev
                        rw [hrec_after_bob, hrec_clean'_bob, Option.map_some, Option.map_some,
                            pureStripBytes_noMatchRecordBytes hlen_in hlen'_63,
                            pureStripBytes_encodeRecordX hlen'_63]
                      · have hpc : p ≠ c.party := hbob ▸ hpb
                        unfold pureStripPrev
                        rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r
                            (rfl : t_clean'.bobOff = false)]
                        simp [CliTurn.records, CliTurn.after, t_clean', hpb, hpc] }
                have hopk_clean := opkUsed_clean_after_rpk_accept (inner := inner)
                  hr hinvB hB₀_dir hmod hk hmk hst'
                have hcs : CoinSplit (cliEntryEvents c1 ++ cliExitEvents c1 0 out)
                    [.recv c.stdin, .rng c.coins, .accept out] :=
                  Slots.coinSplit_rpkNew_accept (c := c1) hcmd
                    (Slots.coins_ne_nil_of_len_32 hcoins) out
                refine ⟨[.recv c.stdin, .rng c.coins, .accept out], t_clean',
                  accepted ++ [q.baseKey.take 33], hsim', ?_, fun who ok hwho hlive => ?_⟩
                · rw [cliEntryEvents_eq_recv hcmd, cliExitEvents_eq]; exact hcs
                · rw [hstdin]
                  have hpqh_b : ∀ q₀, parsePreKeyWire (wirePrekey :: body) = some q₀ →
                      PqFromHonest t.sent q₀.message := hstdin ▸ hpqh
                  have hleak_eq : t_clean'.leakRecords r =
                      fun p => if p = r.bob then some sm.state else t.leakRecords r p := by
                    funext p; by_cases hpb : p = r.bob
                    · subst hpb; simpa [sm] using hrec_clean'_bob
                    · rw [Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r
                          (rfl : t_clean'.bobOff = false),
                          Symbolic.Swarm.CREF.CliPure.leakRecords_eq_records_of_bobOff_false r hoff]
                      simp [CliTurn.records, t_clean', hpb]
                  have hopk_eq : t_clean'.opkUsed r =
                      (t.opkUsed r || (sm.message[opkRemovedIdx]?).any (· != 0#8)) := by
                    rw [hopk_rem]; exact hopk_clean
                  have hstep := Slots.rpkNew_accept_cReady hext' hr rfl (hbob ▸ hwho) hlive
                    hhon hpqh_b hfresh hst_lt hcontract hBin hTie (rfl : t_clean'.sent = t.sent)
                    hleak_eq hopk_eq
                  exact ⟨hstep.1, fun hcol hok_b => hstep.2 hcol (by simpa using hok_b)⟩
    · have hnw : c.stdin.head? ≠ some wireWhisper := by rwa [wireWhisper_eq_wireWhisperTag]
      have hnp : c.stdin.head? ≠ some wirePrekey := by
        intro hh; cases hcs : c.stdin with
        | nil => simp [hcs] at hh
        | cons b tl =>
          simp only [hcs, List.head?_cons, Option.some.injEq] at hh
          exact hpk ⟨tl, hh ▸ hcs⟩
      have hobs := hp.recvOther stB c.stdin rc hwfB hlen_lt hnw hnp heq_recv
      injection hobs with hcode hout hfiles
      subst hcode hout hfiles
      exact bob_recv_d3_pqInputs_reject_step hDir hoff hbob hcmd hinvB _ _

end DY.Libsignal.Composed.Refinement.Cli.ParD3
