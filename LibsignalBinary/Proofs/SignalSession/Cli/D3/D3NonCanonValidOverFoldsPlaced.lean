/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3StageP3Prev1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsA
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned

/-!
# Spatial Folds & Archived-Payload Scope Bridge for Non-Matching Overwrite

Stage P3 / `Prev1` Stage P4 stack spatial splits (`stageP3OverStackRemAt`,
`stageP3StackFrameAt_eq_overScratch`) and the `OverPrevEncInScopeV4 → OverPrevEncOK`
archived-session validation bridge.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `OverPrevEncOK` Bridge & Spatial Splits for `Prev1` Stage P3 / P4 -/

/-- `Slots.scopeIn` strengthened with `s.state.sessionVersion = 4#32` (guaranteed on every
`PqxdhPartyInSpecDomain`-reachable session via `reachPq_sessionVersion_placed`). -/
def ScopeOverIn (r : SessionRecord (List (BitVec 8))) : Prop :=
  Slots.scopeIn r ∧ ∀ s, r.currentSession = some s → s.state.sessionVersion = 4#32

/-- Archived session payloads `enc` produced when promoting over a `ScopeOverIn` record. -/
def OverPrevEncInScopeV4 (enc : List (BitVec 8)) : Prop :=
  ∃ r sess, ScopeOverIn r ∧ r.currentSession = some sess ∧
    enc = E2E.Record.encSession (Over.clearPending sess)

/-- Validated archived session payload invariant for `Prev1` Stage P3 / P4. -/
def OverPrevEncOK (enc : List (BitVec 8)) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    enc = E2E.Record.encSession sess ∧
    Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q
      ⟨some sess⟩ ∧
    sess.state.sessionVersion = 4#32 ∧
    sess.pendingPreKey = none ∧
    sess.pendingKyberPreKey = none

theorem overPrevEncOK_of_inScopeV4 {enc : List (BitVec 8)}
    (h : OverPrevEncInScopeV4 enc) : OverPrevEncOK enc := by
  rcases h with ⟨⟨curOpt⟩, s, ⟨hIn, hver4⟩, hcur, henc⟩
  have hv4 : s.state.sessionVersion = 4#32 := hver4 s hcur
  dsimp only at hcur; subst hcur
  rcases hIn with ⟨⟨hin, hpq, hrepr⟩, s', hs', hss⟩
  injection hs' with hs_eq; subst hs_eq
  have hin0 := hin s rfl
  refine ⟨Over.clearPending s, henc, ⟨⟨?_, ?_, ?_⟩, Over.clearPending s, rfl, ?_⟩,
    hv4, rfl, rfl⟩
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [Over.clearPending] at hk⟩
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    exact Nat.lt_trans (hpq s rfl).2 (by decide)
  · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
    obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr s rfl
    exact ⟨hr1, hr2, rfl, hr4⟩
  · exact ⟨hss.1, fun p hp => by simp [Over.clearPending] at hp,
      fun k hk => by simp [Over.clearPending] at hk, hss.2.2.2⟩

/-- Untouched gap bytes inside `[sp + 8 .. sp + 152)` (`[+32..36)`, `[+88..92)`, `[+120..124)`). -/
def spLowGapsAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 32#64) 4 ∗
  memRegion (sp + 88#64) 4 ∗
  memRegion (sp + 120#64) 4

/-- Untouched gap regions inside `[sp + 1360 .. sp + 3184)` around `[+2352..2448)` and
`[+2704..3048)`. -/
def spHighGapsAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 1360#64) 992 ∗
  memRegion (sp + 2448#64) 256 ∗
  memRegion (sp + 3048#64) 136

/-- Stack slots in `[sp .. sp + 3184)` framed untouched across Stage P3. -/
def stageP3StackFrameAt (sp remoteIkPtr remAddrPtr : BitVec 64) : SepProp :=
  (sp ↦₆₄ 0#64) ∗
  spLowGapsAt sp ∗
  ((sp + 144#64) ↦₆₄ remoteIkPtr) ∗
  ((sp + 168#64) ↦₆₄ remAddrPtr) ∗
  memRegion (sp + 188#64) 4 ∗
  memRegion (sp + 216#64) 376 ∗
  memRegion (sp + 612#64) 12 ∗
  memRegion (sp + 672#64) 16 ∗
  memRegion (sp + 688#64) 192 ∗
  memRegion (sp + 916#64) 12 ∗
  memRegion (sp + 936#64) 4 ∗
  memRegion (sp + 941#64) 27 ∗
  memRegion (sp + 1336#64) 24 ∗
  spHighGapsAt sp

/-- Closure-frame scratch slots `[+1336..+2352)`, `[+2448..+2704)`, `[+3048..+3184)` used by
the inlined `SessionStructure::decode` on the `VerNe` previous-session loop (`+7800`). -/
def overScratch (sp : BitVec 64) : SepProp :=
  memRegion (sp + 1336#64) 1016 ∗
  memRegion (sp + 2448#64) 256 ∗
  memRegion (sp + 3048#64) 136

/-- Caller stack slots of `stageP3StackFrameAt` outside `overScratch sp`. -/
def stageP3OverStackRemAt (sp remoteIkPtr remAddrPtr : BitVec 64) : SepProp :=
  (sp ↦₆₄ 0#64) ∗ spLowGapsAt sp ∗ ((sp + 144#64) ↦₆₄ remoteIkPtr) ∗
  ((sp + 168#64) ↦₆₄ remAddrPtr) ∗ memRegion (sp + 188#64) 4 ∗
  memRegion (sp + 216#64) 376 ∗ memRegion (sp + 612#64) 12 ∗
  memRegion (sp + 672#64) 16 ∗ memRegion (sp + 688#64) 192 ∗
  memRegion (sp + 916#64) 12 ∗ memRegion (sp + 936#64) 4 ∗
  memRegion (sp + 941#64) 27

theorem stageP3StackFrameAt_eq_overScratch (sp remoteIkPtr remAddrPtr : BitVec 64) :
    stageP3StackFrameAt sp remoteIkPtr remAddrPtr =
      overScratch sp ∗ stageP3OverStackRemAt sp remoteIkPtr remAddrPtr := by
  have hjoin :
      memRegion (sp + 1336#64) 24 ∗ memRegion (sp + 1360#64) 992 =
        memRegion (sp + 1336#64) 1016 := by
    simpa [BitVec.add_assoc] using (ProofLib.memRegion_split (sp + 1336#64) 24 992 (by decide)).symm
  unfold stageP3StackFrameAt spHighGapsAt overScratch stageP3OverStackRemAt
  rw [← hjoin]
  sep_ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.D3
