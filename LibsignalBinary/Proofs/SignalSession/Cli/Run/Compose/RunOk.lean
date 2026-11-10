/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.J
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1a
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1c
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3a
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3b
import ProofLib.SepLogic.WPp

/-!
# `signal_session::run` Meets `runSpec` at `runRel S`

Proves `run_ok'` by composing `run_hop_dropSpeOwned` (`Compose/Hops.lean`) with the nine arm hop
theorems (`Compose/Arms/*`) over `RunHooks`, `RunCallees` at `slotsOf A img S needs`, the
all-inputs `PreKeySignalMessage::try_from` contract (`hpksm`), and stack budget `RunSkeleton.runNeed`.
Each wrapper slot's domain side conditions (`RunBounds`, `RunFilesOk S`, `RunEncOk S`, `RunHsOk S`)
are supplied by `runRel S g.i g.a` in `runSpec.pre`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-- `signal_session::run` meets `runSpec` at `runRel S`. -/
theorem run_ok' {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr runName)
      ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img) := by
  apply subroutine_ok_of_sepWPp_init
  intro g R s0 hpc hrun hpre hsp
  have hspb : resStack ≤ s0.sp.toNat := by
    have hpre' := hpre
    simp only [Spec.inImage, runSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    rcases hpre' with ⟨_, ⟨_, _, _, _, _, _, _, _, _, hspb⟩, _⟩
    exact hspb
  rcases runEntry_of_inImage_pre hpc hrun hpre hsp with ⟨he, hmem⟩
  refine ⟨runEntryMem A img g s0 resStack, hmem, ?_⟩
  let Q : State → SepProp → Prop := fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img).post g s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp : State → SepProp → Prop := fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img).onPanic g s0 sf ∗ R)
  have hdrop : RunDrop.DropSpeOwnedOk img A ext := run_hop_dropSpeOwned himg hh.alloc
  have hpanic : PanicK g s0 Qp := fun _ _ hpan hmf => inImage_onPanic_of_runPanic hpan hmf
  have hpost_mono : ∀ {sf Pf}, runPost A img g resStack s0 sf Pf → Q sf Pf :=
    fun hp => ⟨fun hmf => (inImage_post_of_runPost he.fs he.stdout hp hmf).1, hp.2.1, hp.2.2.1⟩
  have hjoin : JoinK img ext A g s0 resStack Q Qp := fun s g' out hj =>
    sepWPp_mono_post (fun _ _ hp => hpost_mono hp)
      (run_hop_join_ok himg hh hres hres64 (Or.inl ⟨g', out, hj, rfl⟩))
  have hrej : RejectK img ext A g s0 resStack Q Qp := fun s g' rk hr =>
    sepWPp_mono_post (fun _ _ hp => hpost_mono hp)
      (run_hop_join_ok himg hh hres hres64 (Or.inr ⟨g', rk, hr, rfl⟩))
  rw [inImage_onOom_eq (S := S) (A := A) (img := img) g resStack s0]
  refine run_hop_pre_ok himg hh hc hdrop hres hres64 he hpanic hrej fun s me hd => ?_
  cases hcall : g.c with
  | keygen meK nK =>
    have htag : g.c.tag ≠ 0 := runRel_not_keygen he.rel he.parse
    rw [hcall] at htag
    exact absurd rfl htag
  | send peerV =>
    exact run_hop_send_ok himg hh hc hdrop hres hres64 hspb he hd hcall hpanic hrej hjoin
  | init peerV dir =>
    exact run_hop_init1_ok himg hh hc hdrop hres hres64 he hd hcall hpanic hrej fun s1 d1 hi1 =>
      run_hop_init2_ok himg hh hc hdrop hres hres64 he hi1 hpanic hrej fun s2 d2 hi2 =>
        run_hop_init3_ok himg hh hc hdrop hres hres64 hspb he hi2 hpanic hrej hjoin
  | recv peerV =>
    cases hstdin : g.i.stdin with
    | nil =>
      exact run_hop_recvBad_ok himg hh hres hres64 he hd hcall (Or.inl hstdin) hrej
    | cons t rest =>
      by_cases ht2 : t = 2#8
      · subst ht2
        exact run_hop_recvW_ok himg hh hc hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin
      · by_cases ht3 : t = 3#8
        · subst ht3
          exact run_hop_recvP_ok himg hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej
            hjoin
        · exact run_hop_recvBad_ok himg hh hres hres64 he hd hcall
            (Or.inr ⟨t, rest, hstdin, ht2, ht3⟩) hrej

/-- `run_ok'` stated at `runSpecTight` (`runSpecTight = runSpec`). -/
theorem run_ok'_tight {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr runName)
      ((runSpecTight A img uuidTryParse (runRel S) cliWrOk resStack).inImage img) :=
  run_ok' himg hh hc hpksm hres hres64

/-- `run_ok'` lifted from `mProg img ext` to `Cli.cliProg img ext` at `entryOf img runName`. -/
theorem run_ok'_cliProg {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A ext)
    (hc : RunCallees img A ext B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (Cli.cliProg img ext) (entryOf img runName)
      ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img) :=
  root_of_tripleRatchetProgAtExt himg (run_ok' himg hh hc hpksm hres hres64)

/-- Parameterized `Ext` specialization of `run_ok'` on `mProg img (cliExternsWith ext)`. -/
theorem run_ok_mProg_ext_of_callees {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExternsWith ext))
    (hc : RunCallees img A (cliExternsWith ext) B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr runName)
      ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img) :=
  run_ok' himg hh hc hpksm hres hres64

/-- Parameterized `Ext` specialization of `run_ok'` on `Cli.cliProg img (cliExternsWith ext)` at
`entryOf img runName`. -/
theorem run_ok_ext_of_callees {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExternsWith ext))
    (hc : RunCallees img A (cliExternsWith ext) B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img runName)
      ((runSpec A img uuidTryParse (runRel S) cliWrOk resStack).inImage img) :=
  run_ok'_cliProg himg hh hc hpksm hres hres64

/-- Tight (`runSpecTight`) counterpart of `run_ok_ext_of_callees` on
`Cli.cliProg img (cliExternsWith ext)`. -/
theorem run_ok_tight_ext_of_callees {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExternsWith ext))
    (hc : RunCallees img A (cliExternsWith ext) B (slotsOf A img S needs))
    (hpksm : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromName)
      (pksmSlotSpec A img S))
    (hres : runNeed B (slotsOf A img S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (Cli.cliProg img (cliExternsWith ext)) (entryOf img runName)
      ((runSpecTight A img uuidTryParse (runRel S) cliWrOk resStack).inImage img) :=
  root_of_tripleRatchetProgAtExt himg (run_ok'_tight himg hh hc hpksm hres hres64)

end CryptoVerification.SignalSession.Cli.RunCompose
