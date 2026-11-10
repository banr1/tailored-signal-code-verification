/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchPathAPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverAuxPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverFoldsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3StageP3Prev1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv

/-!
# Overwrite-Path (`Path C Over`) `slotOutTr` Packaging Helpers

Pure and frame-arithmetic `slotOutTr` packaging helpers on `decPkOverDef`
(`decPkOk0_of_d3_pkToE_aux`, `x29_eq_sp_add_c70_over_d3_placed`, `slotOutTr_over_of_reject`,
`slotOutTr_over_of_accept`) for non-matching version-4 sessions under arbitrary
`pm.serialized`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. `slotOutTr` & Postcondition Packaging Helpers on `decPkOverDef` -/

theorem decPkOk0_of_d3_pkToE_aux {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (hd3 : DecPkOkD3 W Scope F peer me pm) (hpk : pkToE? pm = some m) :
    DecPkOk₀ W Scope F peer me (pmOfE m pm.message) := by
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3
  cases Option.some.inj (hpk0.symm.trans hpk)
  exact hdec0

theorem x29_eq_sp_add_c70_over_d3_placed {s0 s2 : State}
    (hx29 : s2.readReg64 .x29 = s0.sp - 0x60#64)
    (hs2_sp : s2.sp = s0.sp - 0xcd0#64) :
    s2.readReg64 .x29 = s2.sp + 0xc70#64 := by
  rw [hx29, hs2_sp]; bv_omega

theorem slotOutTr_over_of_reject {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    (g' : StoresGhost) {err : ApiError AddrVal Unit} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkOverDef X W Scope)
    (hne_p : err ≠ .panic) (hne_s : err ≠ .store ())
    (hdec : decPkOverDef X W Scope F peer me pm coins = some none) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.error err) tr0 trf := by
  refine ⟨fun h => hne_p (Except.error.inj h), fun h => hne_s (Except.error.inj h), ?_⟩
  rw [hS, hdec]

theorem slotOutTr_over_of_accept {S : RunSem} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {pt : List (BitVec 8)} {tr0 trf : List TraceEvent}
    (hS : S.decryptPrekey = decPkOverDef X W Scope)
    (hdec : decPkOverDef X W Scope F peer me pm coins = some (some (g', pt)))
    (hwr : ∀ pw ∈ g'.writes, cliWrOk pw.1) :
    slotOutTr (S.decryptPrekey F peer me pm coins) g' (.ok pt) tr0 trf := by
  refine ⟨nofun, nofun, ?_⟩
  rw [hS, hdec]
  exact ⟨rfl, hwr⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3
