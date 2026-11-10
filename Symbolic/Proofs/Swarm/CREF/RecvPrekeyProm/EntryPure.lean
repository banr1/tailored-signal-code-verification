/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.EntryPureB
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Opk
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.By2Pure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HistOpkPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTiePure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTieResidPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromDecTieResidPureA
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep

/-!
# Accepting Promote Step under `CReadyPure`

Discharges `PromNewRecByOK₂` (`prom_newRecByOK₂_of_noDraw`) and `PromOpkOK` (`prom_opkOK_proved`),
and assembles `cEntry_recvPrekey_prom_of_noDraw_and_ver` from `PromNoDrawOK` and `PromVersionOK`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain consumeMessageKey chainKeyAt kdfCk kdfRk computeMac
  createChain x25519LowOrder)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding kdfRk createChain x25519LowOrder
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3

theorem prom_rcvDecTie_at_clean
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r) (hSeq : S = compSemOf interpretation r)
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    (hsel : PromDecSelSkipped sess pf.inner mid coins ∨ PromDecSelNoRatchet sess pf.inner mid coins ∨
      PromDecSelRatchetDH sess pf.inner mid coins) :
    PromRcvDecTieAt interpretation r S who ok r.bob rec sm.state e'.sent acc
      (promAccBlk b mid pt) pf.message := by
  have hceh := hext.1
  have hik : TR.IkShape interpretation r :=
    ⟨hext.1.x25519_public_key_length (clamp (secretBytes r 0)),
     hext.1.x25519_public_key_length (clamp (secretBytes r 2))⟩
  intro g ms₀ pre m post hc hc₀ hB hpre hdec hpost hch₀ hnocol hcurR hrel hns
  have hfresh₀ : TR.TRRecvFreshAll r ms₀ := prom_fresh_of_matchedPrefix interpretation hc₀.matched
  have hRk : TR.RecvDecStep.A2bSeedRkAliasRes interpretation r S g (ms₀ ++ pre) acc :=
    prom_a2b_hrkAlias r S g ms₀ pre m post acc (promAccBlk b mid pt) hB hpre hch₀ hfresh₀
  obtain ⟨hfresh, habs, hX, hA, hRk⟩ :=
    prom_tieResid_at_clean interpretation hc.matched hc₀.matched hB hRk
  exact prom_rcvDecTie_at hext hceh hwf hik hSeq hC hsel g ms₀ pre m post hB hpre hdec hpost hch₀
    hnocol hcurR hrel hns hfresh habs hX hA hRk

/-- Discharges `PromNewRecByOK₂` from `PromNoDrawOK`. -/
theorem prom_newRecByOK₂_of_noDraw
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r) (hSeq : S = compSemOf interpretation r)
    (hND : PromNoDrawOK interpretation r S who ok) :
    PromNewRecByOK₂ interpretation r S who ok := by
  refine prom_newRecByOK₂_of_tieAt fun j e' mid acc rec b sm pf sess sess' coins expected pt hC _hcol _hcolBy => ?_
  have hsel :=
    prom_decSel_cases_out hC.out fun hnil =>
      hND j e' acc rec b sm pf sess sess' coins expected pt (hnil ▸ hC)
  exact prom_rcvDecTie_at_clean hext hwf hSeq hC hsel

theorem prom_opkUsedB_step {r : ProtocolSetup} {ms₀ δ : List Move} {p : Participant}
    {blk : List MachineEvent} (pk : DY.Bytes)
    (hδ : OneMove (RecvStep p blk) (runTraceMoves r ms₀) δ) :
    DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r (ms₀ ++ δ)) r.bob pk =
      DY.Libsignal.PQXDH.opkUsedB (runTraceMoves r ms₀) r.bob pk := by
  obtain ⟨pre, m, post, rfl, hpre, hm, hpost⟩ := hδ
  rw [runTrace_append, b5_runMoves_append_fst, runMoves_cons_fst,
    rpk_opkUsedB_movesFrom_quiet r.bob pk _ post (movesFrom_mono (fun _ _ h => h.2) _ _ hpost)]
  have hm_eq :
      DY.Libsignal.PQXDH.opkUsedB (m.next (runMoves pre (runTraceMoves r ms₀)).1) r.bob pk =
        DY.Libsignal.PQXDH.opkUsedB (runMoves pre (runTraceMoves r ms₀)).1 r.bob pk := by
    rcases hm.2.1 with hrk | hq
    · refine opkUsedB_next_of_not_bobStart _ r.bob pk m ?_
      rintro b a kh regIdxA mh pqIdx spqrMsgIdx shown rfl
      exact hrk
    · exact rpk_opkUsedB_quiet hq r.bob pk
  rw [hm_eq,
    rpk_opkUsedB_movesFrom_quiet r.bob pk _ pre (movesFrom_mono (fun _ _ h => h.2) _ _ hpre)]

theorem prom_opkUnused_of_cOpkRelC {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt) :
    COpkRelC interpretation r S who ok e'.opkUsed (acc ++ promAccBlk b mid pt) := by
  intro hw hu g ms hc
  have hhead : ∀ e ∈ (promAccBlk b mid pt).head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he
    exact Or.inl rfl
  have hmp := hc.matched
  obtain ⟨ms₀, δ, rfl, hpre, hmatch⟩ :=
    matchedPrefix_split hmp hhead (matchedPrefix_prefix_reachable hmp)
  have hc₀ : Clean interpretation r S who ok g ms₀ acc :=
    clean_prefix (matchedPrefix_length_eq hpre) hc
  have hbook₀ : CBook interpretation r S g ms₀ e'.sent e'.accepted acc :=
    hC.entry.ready.2.1.book hc₀
  have hB : XplBlock interpretation r S who g ms₀ δ acc (promAccBlk b mid pt) :=
    ⟨hpre, hmp.2.1, hmatch⟩
  have hdf : DeltaFaithful r.bob (runTraceMoves r ms₀) δ :=
    prom_accept_faithful hC hB hc.role
  have hrpk := xplInv_rpk hB hdf (prom_accBlk_shape hC.hmid)
  have h1 : OneMove (RecvStep r.bob (promAccBlk b mid pt)) (runTraceMoves r ms₀) δ :=
    prom_oneMove_recvStep hrpk (fun pre m post hδ hpreM =>
      prom_noBobStart hC (hδ ▸ hB) hpreM hbook₀ (hδ ▸ hc.path))
  rw [prom_opkUsedB_step _ h1]
  exact hC.entry.ready.2.2 hw hu g ms₀ hc₀

theorem prom_opkOK_proved {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} :
    PromOpkOK interpretation r S who ok := by
  intro j e' mid acc rec b sm pf sess sess' coins expected pt hC _hcol
  exact prom_opkUnused_of_cOpkRelC hC

/-- Accepting promote step under `CReadyPure`, parameterized by `PromNoDrawOK` and `PromVersionOK`. -/
theorem cEntry_recvPrekey_prom_of_noDraw_and_ver
    (interpretation : ExternInterpretation)
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (r : ProtocolSetup) (hwf : ProtocolSetupWF r) (S : OpaqueSymbolSemantics)
    (_hS : SemReady interpretation r S) (hSeq : S = compSemOf interpretation r)
    {who : List Participant} {ok : Nat → Bool}
    (hND : PromNoDrawOK interpretation r S who ok)
    (hVer : PromVersionOK interpretation r S who ok)
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
        e'.sent e'.accepted e'.opkUsed (acc ++ promAccBlk b mid pt)) :=
  cEntry_recvPrekey_prom_call
    (prom_explainOK_of_noDraw_and_ver interpretation hext hwf hSeq hND hVer)
    (prom_newRecByOK₂_of_noDraw hext hwf hSeq hND)
    (prom_histOK hext hwf)
    prom_opkOK_proved
    hC hcol

end Symbolic.Swarm.CREF.CliPure
