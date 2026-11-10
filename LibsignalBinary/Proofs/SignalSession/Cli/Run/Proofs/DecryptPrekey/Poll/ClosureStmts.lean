/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Poll Closure Stage Re-Exports and Stack Bounds

Re-exports `GenP3.stageP3Gen_vregs_ok`, `Kits.stageP4_v1_vregs_kits_ok`, and
`Kits.stageP4_kyber_refused_vregs_kits_ok`, and proves `CalleeSavedPreserved` bridges and
`stageP4CallStack_le_subStack` under `dpClosSubStack B`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `CalleeSavedPreserved` Bridges -/

theorem closureCalleeSavedP4_toCalleeSavedPreserved {s0 sf : State}
    (hcs : ClosureCalleeSavedP4 s0 sf)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf :=
  hcs.toCalleeSavedPreserved hvregs

theorem closureCalleeSaved_toCalleeSavedPreserved {s0 sf : State}
    (hcs : ClosureCalleeSaved s0 sf)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, _⟩
  exact ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩

/-! ## 2. Stage P4 Stack Budget Bound at CLI Kits -/

theorem stageP4CallStack_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (pid sid kid : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP4CallStack
      (cliPollSessKit A b F0 Scope peer (cliKitStk B))
      (cliPollIdKit A b F0 peer (cliKitStk B))
      (cliPollPkKit A b F0 pid (cliKitStk B))
      (cliPollKpkKit A b F0 kid sid kbk (cliKitStk B)) ≤ dpClosSubStack B := by
  have hall := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hall
  rcases hall with ⟨_, _, hss1, hss2, _, _, hid1, hid2, _, _, _, _, _, _, hpk1, hpk2, _, _, _, _,
    hkpk1, hkpk2⟩
  have herr : stageP4ErrUnwindStack ≤ dpClosSubStack B := by
    have heq : stageP4ErrUnwindStack = max allocHookStack dropSessionStructureLocal2Stack := rfl
    have ha : allocHookStack ≤ 262144 := by decide
    have hd : dropSessionStructureLocal2Stack ≤ 262144 := by decide
    dsimp only [dpClosSubStack]
    omega
  dsimp only [stageP4CallStack, saveIdCallStack, markKyberCallStack, removePreKeyCallStack,
    storeSessionCallStack, cliPollSessKit, cliPollIdKit, cliPollPkKit, cliPollKpkKit,
    CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpec,
    cliIdStoreSpecFull,
    CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpec,
    cliKpkStoreSpecFull]
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hid1, Nat.max_le.mpr ⟨hid2, herr⟩⟩,
    Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hkpk1, Nat.max_le.mpr ⟨hkpk2, herr⟩⟩,
      Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hpk1, Nat.max_le.mpr ⟨hpk2, herr⟩⟩,
        Nat.max_le.mpr ⟨hss1, Nat.max_le.mpr ⟨hss2, herr⟩⟩⟩⟩⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
