/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots

/-!
# Whole-`run` Binary-Kit Trace Envelope Membership

Specializes `CliSlotEnvelopeBridge.cliMainArmEnvs_runEnv_to_cliRunBinaryEnv` across all five CLI
callee slots (`W3` `init`, `W1` `send` and wire output caps, `W2` `recv` whisper, `PKSM` `3#8`, and
widened `W4` `recv-prekey`), bridging `RunOkPlacedBudget.RunEnv` at the binary store-kit polls into
`realCliRunBinaryKitEnvOf img S X W g`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMem

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PreKeyMessageFields UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliRunBudgets inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost Init2Data InitGhost PksmGhost RunSem addrValOf)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent RustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (decBinaryIdKitPlacedBudget decBinarySessKitPlacedBudget mkBinaryKitRealCalleeEnvs
   realCliRunBinaryKitEnvOf w1BinaryIdKitPlacedBudget w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (cliMainArmEnvs cliMainArmEnvs_runEnv_to_cliRunBinaryEnv cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec (SpqrSendTightCapEnv)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit (PksmCanonSliceEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (r3bDecPkGhost r3bPksmGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
  (CanonicalOrFallbackPksmEnv pksmCanonSlice_sub_binaryKit pksmCanonicalGuard_sub_binaryKit
   pksmCanonicalOrFallback_sub_binaryKit realCliDecPkBinaryWideSlotEnv realCliInitBinarySlotEnv
   w1_cliEncryptSlotEnv_sub_binaryKit w1_send_outPk_serialized_le_sessionCapBytes
   w1_send_out_serialized_le_sessionCapBytes w2_cliDecryptSignalSlotEnv_sub_binaryKit
   w3_realCliInitBinarySlotEnv_sub_binaryKit w4_realCliDecPkBinaryWideSlotEnv_sub_binaryKit)

/-- Binary-kit `RunSlotEnvs` bundle at `w1BinarySessKitPlacedBudget`, `w1BinaryIdKitPlacedBudget`,
`decBinarySessKitPlacedBudget`, `decBinaryIdKitPlacedBudget`, `SpqrSendTightCapEnv`,
`W2RealTdEnv W.C.F W.Q.K`, and caller-supplied `InitEnv` / `DecPkEnv`. -/
noncomputable def binaryKitRunSlotEnvs [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B SpqrSendTightCapEnv
    (w1BinarySessKitPlacedBudget A.repAlloc B)
    (w1BinaryIdKitPlacedBudget A.repAlloc B)
  decryptSignal := CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B (W2RealTdEnv W.C.F W.Q.K)
    (decBinarySessKitPlacedBudget A.repAlloc B)
    (decBinaryIdKitPlacedBudget A.repAlloc B)
  initiate := InitEnv
  decryptPrekey := DecPkEnv

/-- Parametric whole-`run` bridge turning `RunEnv` on `binaryKitRunSlotEnvs` into
`realCliRunBinaryKitEnvOf img S X W g` for any `S : RunSem` with `S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn`
(both `cliRunSem X W decPk decPkOk pksmParse` and `cliRunSemD2c_placed X W` satisfy this by `rfl`),
discharging `W1` (`send` + wire output caps) and `W2` (`recv` whisper) automatically and taking
`hinit3`, `hrecvP_pksm`, and `hrecvP_slot` for `W3`, `PKSM`, and `W4`. -/
theorem runEnv_sub_realCliRunBinaryKitEnvOf_of_slots [LibsignalPlacement] {M : AllocCostModel}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {g : RunCall}
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hinit3 : ∀ peerV dir d2 evs, g.c = .init peerV dir → d2.dir = dir →
      d2.peerV = peerV → d2.peerG.val = addrValOf peerV →
      d2.spkSigPtr ≠ 0 → d2.kpkSigPtr ≠ 0 → d2.kpkPtr ≠ 0 →
      InitEnv (r1cInitGhost g d2 0#64) evs →
      (mkBinaryKitRealCalleeEnvs img S X W g).initEnv evs)
    (hrecvP_pksm : ∀ peerV rest evs, g.c = .recv peerV → g.i.stdin = 3#8 :: rest →
      PksmTryFromEnv (r3bPksmGhost rest) evs →
      (mkBinaryKitRealCalleeEnvs img S X W g).pksmEnv rest evs)
    (hrecvP_slot : ∀ (meV : AddrV) (_meG : AddrGhost) peerV rest pm evs, g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      DecPkEnv (r3bDecPkGhost g meV peerV pm) evs →
      (mkBinaryKitRealCalleeEnvs img S X W g).decPkEnv evs)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
          (binaryKitRunSlotEnvs W A B InitEnv DecPkEnv)
          PksmTryFromEnv S)
        g evs →
      realCliRunBinaryKitEnvOf img S X W g evs :=
  cliMainArmEnvs_runEnv_to_cliRunBinaryEnv rfl
    hinit3
    (fun _ meG peerV _ hc he => w1_cliEncryptSlotEnv_sub_binaryKit img S X W A B g meG peerV hin hc he)
    (fun peerV meV f m hc heq =>
      w1_send_out_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc)
    (fun peerV meV f m hc heq =>
      w1_send_outPk_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc)
    (fun _ meG peerV rest m _ hc hst htr hd =>
      w2_cliDecryptSignalSlotEnv_sub_binaryKit img S X W A B g meG peerV rest m hin hc hst htr hd)
    hrecvP_pksm
    hrecvP_slot

/-- Concrete whole-`run` bridge under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i` at
`realCliInitBinarySlotEnv W`, `realCliDecPkBinaryWideSlotEnv X W`, and any `PksmTryFromEnv` that
reduces to `PksmCanonSliceEnv x.bytes` on canonical outer `PreKeyMessageFields`
(e.g. `CanonicalOrW8bPksmEnv` / `CanonicalOrFallbackPksmEnv`). -/
theorem runEnv_sub_realCliRunBinaryKitEnvOf [LibsignalPlacement] {M : AllocCostModel}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hpksm_canon : ∀ (x : PksmGhost) (evs : List AllocEvent),
      (∃ m : PreKeyMessageFields, x.bytes = m.bytes) →
      PksmTryFromEnv x evs → PksmCanonSliceEnv x.bytes evs)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
          (binaryKitRunSlotEnvs W A B (realCliInitBinarySlotEnv W)
            (realCliDecPkBinaryWideSlotEnv X W))
          PksmTryFromEnv
          S)
        g evs →
      realCliRunBinaryKitEnvOf img S X W g evs :=
  runEnv_sub_realCliRunBinaryKitEnvOf_of_slots img S X W A B hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ hi3 =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval hi3)
    (fun peerV rest _ hc hst hpk =>
      pksmCanonicalGuard_sub_binaryKit img S X W g peerV rest hi hparse hc hst rfl
        (hpksm_canon (r3bPksmGhost rest) _) hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      w4_realCliDecPkBinaryWideSlotEnv_sub_binaryKit img S X W g meV peerV rest pm
        hparse hin hc hst hpk hd hS_pksm)
    hS_enc

/-- Concrete whole-`run` bridge specialized to `CanonicalOrFallbackPksmEnv FallbackEnv` under
`CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
theorem runEnv_sub_realCliRunBinaryKitEnvOf_canonOrFallback [LibsignalPlacement] {M : AllocCostModel}
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
          (binaryKitRunSlotEnvs W A B (realCliInitBinarySlotEnv W)
            (realCliDecPkBinaryWideSlotEnv X W))
          (CanonicalOrFallbackPksmEnv FallbackEnv)
          S)
        g evs →
      realCliRunBinaryKitEnvOf img S X W g evs :=
  runEnv_sub_realCliRunBinaryKitEnvOf_of_slots img S X W A B hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ hi3 =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval hi3)
    (fun peerV rest _ hc hst hpk =>
      pksmCanonicalOrFallback_sub_binaryKit img S X W g peerV rest hi hparse hc hst rfl hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      w4_realCliDecPkBinaryWideSlotEnv_sub_binaryKit img S X W g meV peerV rest pm
        hparse hin hc hst hpk hd hS_pksm)
    hS_enc

/-- Companion concrete whole-`run` bridge at `PksmTryFromEnv := fun x => PksmCanonSliceEnv x.bytes`
(for callers that already lifted Block `111` via `WirePksmTightCredit.preKeyTryFrom_placed_ok_canonSlice`). -/
theorem runEnv_sub_realCliRunBinaryKitEnvOf_canonSlice [LibsignalPlacement] {M : AllocCostModel}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
          (binaryKitRunSlotEnvs W A B (realCliInitBinarySlotEnv W)
            (realCliDecPkBinaryWideSlotEnv X W))
          (fun x => PksmCanonSliceEnv x.bytes)
          S)
        g evs →
      realCliRunBinaryKitEnvOf img S X W g evs :=
  runEnv_sub_realCliRunBinaryKitEnvOf_of_slots img S X W A B hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ hi =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval hi)
    (fun _ rest _ _ _ hpk => pksmCanonSlice_sub_binaryKit img S X W g rest hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      w4_realCliDecPkBinaryWideSlotEnv_sub_binaryKit img S X W g meV peerV rest pm
        hparse hin hc hst hpk hd hS_pksm)
    hS_enc

end LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMem
