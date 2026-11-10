/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBadG2.Frame
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core

/-!
# Ghost Invariance of Whisper Decryption Trials

Proves that `whisperTrials` evaluates identically across ghosts satisfying `CBadGammaAgree` and
`CBadStamps` whenever the message or wire term is stamped below `n`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)
open Symbolic.Swarm.CREF.TR.FreshSigma (StampsLt TRSignalMsgStampsLt stampsLt_parseTrSignalMsg)

theorem cbadG2_whisperTrials_eq_of_msg {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {ms : List Move} {n : Nat} {msg : TRSignalMsg}
    (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n)
    (hmsg : TRSignalMsgStampsLt interpretation S g n msg) :
    whisperTrials interpretation r S g₁ (runTraceMoves r ms) msg =
      whisperTrials interpretation r S g (runTraceMoves r ms) msg :=
  Stage1Trials.whisperTrials_congr_gamma
    (cbadG2_gamma_eq hga hmsg.2.2.1)
    (fun st hst_mem c hc => cbadG2_gamma_eq hga ((hst.states st hst_mem).2.2.2.2.2.2 c hc).1)
    (fun idx hlt s pk ctr seed rIdx src hget =>
      cbadG2_gamma_eq hga (hst.skippedLogged idx s pk ctr seed rIdx src hlt hget).2)

theorem cbadG2_whisperTrials_eq {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g₁ : Ghost} {ms : List Move} {n : Nat} {t : DY.Bytes} {msg : TRSignalMsg}
    (hga : CBadGammaAgree interpretation S g g₁ n)
    (hst : CBadStamps interpretation r S g ms n)
    (ht : StampsLt interpretation S g n t)
    (hp : parseTrSignalMsg t = some msg) :
    whisperTrials interpretation r S g₁ (runTraceMoves r ms) msg =
      whisperTrials interpretation r S g (runTraceMoves r ms) msg :=
  cbadG2_whisperTrials_eq_of_msg hga hst (stampsLt_parseTrSignalMsg ht hp)

end Symbolic.Swarm.CREF
