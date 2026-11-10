/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgePq
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessOom
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Binary PQXDH CLI Composition

Layout-generic composition from `MainOkCliPq`, non-matching pre-key `recv` (`MainOkOver`),
`Cli.muslHarness_ok`, and ELF `PT_LOAD` segment-slice witnesses (`CliElfFrozen`, `CliElfStatics`,
`CliElfTokenCells`, `patchElfTokens`) to `CliSpecPqxdhNoMatch`, `CliPqxdhElfCorrectUnderAllocOk elf`,
and `CliPqxdhBinaryCorrectUnderAllocOk bytes`. Also proves the decomposition
`CliPqxdhAllocNeverFails elf W ↔ CliPqFiveAllocOk elf W ∧ CliPqNoMatchAllocOk elf W`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.MuslElf

/-! ## 1. 5-Clause Whole-ELF & Bytes Helper Specifications (`CliBinaryCorrectPq5`) -/

/-- 5-clause PQXDH whole-ELF correctness: `CliElfCodeMatches elf` holds, and for every `W`
satisfying `CliPqFiveAllocOk elf W` and every `X : UnreachedPqxdhPrimitives`,
`cliRunAbortOnPanic elf W` meets `CliSpecPqxdh` at `⟨W.C, W.Q⟩`. -/
def CliBinaryCorrectPq5 (elf : ElfImage) : Prop :=
  CliElfCodeMatches elf ∧
  ∀ W : CliHooks, CliPqFiveAllocOk elf W →
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩

/-- 5-clause PQXDH binary bytes correctness: `bytes` parse as an ELF meeting `CliBinaryCorrectPq5`. -/
def LibsignalCliBinaryCorrectPq5 (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliBinaryCorrectPq5 elf

/-! ## 2. `OutcomeMatchesModelExceptPath`, `CliPqxdhInputs`, and `CliPqxdhAllocNeverFails` Lemmas -/

theorem Outcome.AgreeExcept.refl (p : String) (o : Outcome) : Outcome.AgreeExcept p o o := by
  cases o <;> simp [Outcome.AgreeExcept]

theorem OutcomeMatchesModelExceptPath.of_eq {W : PEParams} {i : Inputs} {p : String}
    {r : Option (Option (PqParty × List (BitVec 8)))} {o : Outcome}
    (h : o = pqxdhExpectedOutcome W i r) : OutcomeMatchesModelExceptPath W i p r o := by
  subst h
  unfold OutcomeMatchesModelExceptPath
  split
  · exact Outcome.AgreeExcept.refl p _
  · rfl

theorem cliPqInputs_init {W : PEParams} {st : PqParty} (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hst : PqxdhPartyInSpecDomain W st) (hnone : st.session = none) :
    CliPqxdhInputs W (pqInitInputs W st b t) :=
  ⟨st, hst, Or.inl ⟨hnone, b, t, rfl⟩⟩

theorem cliPqInputs_send {W : PEParams} {st : PqParty} (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (hst : PqxdhPartyInSpecDomain W st) (hm : m.length < 2 ^ 32) :
    CliPqxdhInputs W (pqSendInputs W st m r) :=
  ⟨st, hst, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩

theorem cliPqInputs_recvWhisper {W : PEParams} {st : PqParty} (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) (hc : c.length < 2 ^ 32) :
    CliPqxdhInputs W (pqRecvInputs W st (wireWhisper :: c) rc) :=
  ⟨st, hst, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩

theorem cliPqInputs_recvPrekey {W : PEParams} {st : PqParty} (m : PreKeyMessageFields)
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) (hm : m.inner.length + 2048 < 2 ^ 32) :
    CliPqxdhInputs W (pqRecvInputs W st (wirePrekey :: m.bytes) rc) :=
  ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩

theorem cliPqInputs_recvBad {W : PEParams} {st : PqParty} (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) (hc : c.length < 2 ^ 32)
    (h2 : c.head? ≠ some wireWhisper) (h3 : c.head? ≠ some wirePrekey) :
    CliPqxdhInputs W (pqRecvInputs W st c rc) :=
  ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2, h3, rfl⟩)))⟩

/-- Allocation-failure freedom on non-matching pre-key `recv` inputs. -/
def CliPqNoMatchAllocOk (elf : ElfImage) (W : CliHooks) : Prop :=
  ∀ st : PqParty, PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
    ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
    ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
      ¬ PqSessionMatches x g m →
      CliInputAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)

/-- Project `CliPqxdhAllocNeverFails` onto the 5 clauses of `CliSpecPqxdh` (`CliPqFiveAllocOk`). -/
theorem CliPqxdhAllocNeverFails.fiveAllocOk {elf : ElfImage} {W : CliHooks}
    (h : CliPqxdhAllocNeverFails elf W) : CliPqFiveAllocOk elf W where
  init := fun _ b t hst hnone => h _ (cliPqInputs_init b t hst hnone)
  send := fun _ m r hst hm => h _ (cliPqInputs_send m r hst hm)
  recvWhisper := fun _ c rc hst hc => h _ (cliPqInputs_recvWhisper c rc hst hc)
  recvPrekey := fun _ m rc hst hm _ => h _ (cliPqInputs_recvPrekey m rc hst hm)
  recvBad := fun _ c rc hst hc h2 h3 => h _ (cliPqInputs_recvBad c rc hst hc h2 h3)

/-- Project `CliPqxdhAllocNeverFails` onto non-matching pre-key `recv` inputs. -/
theorem CliPqxdhAllocNeverFails.noMatchAllocOk {elf : ElfImage} {W : CliHooks}
    (h : CliPqxdhAllocNeverFails elf W) : CliPqNoMatchAllocOk elf W :=
  fun _ hst _ _ _ m rc hm _ => h _ (cliPqInputs_recvPrekey m rc hst hm)

/-- `CliPqxdhAllocNeverFails` is equivalent to `CliPqFiveAllocOk` together with
`CliPqNoMatchAllocOk`. -/
theorem cliAllocNeverFailsPq_iff_five_and_noMatch {elf : ElfImage} {W : CliHooks} :
    CliPqxdhAllocNeverFails elf W ↔ CliPqFiveAllocOk elf W ∧ CliPqNoMatchAllocOk elf W := by
  constructor
  · exact fun h => ⟨h.fiveAllocOk, h.noMatchAllocOk⟩
  · rintro ⟨h5, hnm⟩ i ⟨st, hst, hi⟩
    rcases hi with ⟨hnone, b, t, rfl⟩ | ⟨m, r, hm, rfl⟩ | ⟨c, rc, hc, rfl⟩ |
      ⟨m, rc, hm, rfl⟩ | ⟨c, rc, hc, h2, h3, rfl⟩
    · exact h5.init st b t hst hnone
    · exact h5.send st m r hst hm
    · exact h5.recvWhisper st c rc hst hc
    · cases hsess : st.session with
      | none =>
        exact h5.recvPrekey st m rc hst hm (by intro _ _ hs; rw [hsess] at hs; cases hs)
      | some xg =>
        rcases xg with ⟨x, g⟩
        by_cases hmatch : PqSessionMatches x g m
        · exact h5.recvPrekey st m rc hst hm (by
            intro x' g' hs
            rw [hsess] at hs
            cases hs
            exact hmatch)
        · exact hnm st hst x g hsess m rc hm hmatch
    · exact h5.recvBad st c rc hst hc h2 h3

/-! ## 3. Non-Matching Pre-Key `MainOkOver` & `CliSpecPqxdhNoMatch` Composers -/

/-- `main`-level non-matching pre-key `recv` specification at `HooksE.A0`: on Bob's pre-key
`recv` over a session `(x, g)` with `¬ PqSessionMatches x g m`, `main` meets `Cli.mainSpec` for a
relation `Run` satisfying `Cli.CommitOk` and `OutcomeMatchesModelExceptPath` against
`pqRecvPrekeyModel X ⟨W.C, W.Q⟩ { st with session := none } m rc`. -/
def MainOkOver (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (Cli.mainSpec E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)

/-- Lifts `MainOkOver img`, `Cli.MuslHarness elf'`, and `CliPqNoMatchAllocOk elf W` to
`∀ X, CliSpecPqxdhNoMatch (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩`. -/
theorem cliSpecPqNoMatch_of_parts_observe {elf elf' : ElfImage} {img : Obj.Image} {Fr : SepProp}
    {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hover : MainOkOver img)
    (halloc : CliPqNoMatchAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdhNoMatch (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ := by
  intro X st hst x g hsess m rc hm hnomatch
  let WP : PEParams := ⟨W.C, W.Q⟩
  let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
  obtain ⟨Run, hmainW, hclause⟩ := hover X W
  by_cases hcap : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hcap, ↓reduceIte]
    exact cliRunSig_of_main_stdinOverCap himg hbase hE hH hmainW (hpatch inp)
      (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
      (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
      (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hcap)
      (halloc st hst x g hsess m rc hm hnomatch)
  · simp only [hcap, ↓reduceIte]
    obtain ⟨a, hrun, hobsEx, hcommit⟩ := hclause st hst x g hsess m rc hm hnomatch
    have hraw : CliRunsToRaw elf' W inp (observe inp.files a) :=
      cliRunsTo_of_main_call himg hbase hE hH hmainW
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun
        (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_lt hcap))
        (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        hcommit
        (cliInputAllocOkRaw_of_patch (hpatch inp) (halloc st hst x g hsess m rc hm hnomatch))
    exact ⟨observe inp.files a, cliRunSig_eq_some (cliRunsTo_of_raw (hpatch inp) hraw), hobsEx⟩

/-- Instantiates `cliSpecPqNoMatch_of_parts_observe` at `img := cliImg` and
`elf' := patchElfTokens elf`. -/
theorem cliSpecPqNoMatch_of_harness {elf : ElfImage} {Fr : SepProp} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
      (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hover : MainOkOver cliImg)
    (halloc : CliPqNoMatchAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdhNoMatch (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  cliSpecPqNoMatch_of_parts_observe loads_cliImg cliImg_base
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i))
    (elfStaticOk_patchElfTokens hE) hH hover halloc

/-- Combines `muslHarness_cliImg_of_elf`, `MainOkOver cliImg`, and `CliPqNoMatchAllocOk elf W`
to establish `CliSpecPqxdhNoMatch`. -/
theorem cliSpecPqNoMatch_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hover : MainOkOver cliImg)
    (halloc : CliPqNoMatchAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdhNoMatch (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  cliSpecPqNoMatch_of_harness hE htok
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat W) hover halloc

/-! ## 4. Whole-Binary & Bytes Composers (`CliBinaryCorrectPq5`, `CliPqxdhElfCorrectUnderAllocOk`, `CliPqxdhBinaryCorrectUnderAllocOk`) -/

theorem cliBinaryCorrectPq5_of_parts_observe {elf elf' : ElfImage} {img : Obj.Image} {Fr : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : MainOkCliPq img) :
    CliBinaryCorrectPq5 elf :=
  ⟨hcode, fun W halloc X =>
    cliSpecPq_of_parts_observe himg hbase hpatch hE (hH W) hmain halloc X⟩

theorem cliBinaryCorrectPq5_of_harness_main {elf : ElfImage} {Fr : SepProp}
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hmain : MainOkCliPq cliImg) :
    CliBinaryCorrectPq5 elf :=
  cliBinaryCorrectPq5_of_parts_observe loads_cliImg cliImg_base hcode
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i))
    (elfStaticOk_patchElfTokens hE) hH hmain

/-- Harness-generic 5-clause PQXDH whole-ELF composer discharging `MainOkCliPq cliImg` via
`main_ok_cli_pq_inst loads_cliImg`. -/
theorem cliBinaryCorrectPq5_of_harness {elf : ElfImage} {Fr : SepProp}
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg))) :
    CliBinaryCorrectPq5 elf :=
  cliBinaryCorrectPq5_of_harness_main hcode hE htok hH (main_ok_cli_pq_inst loads_cliImg)

theorem cliBinaryCorrectPq5_of_elf_main {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : MainOkCliPq cliImg) :
    CliBinaryCorrectPq5 elf :=
  cliBinaryCorrectPq5_of_harness_main (hfz.codeMatches cliImg_base hE) hE htok
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat) hmain

/-- Segment-slice 5-clause PQXDH whole-ELF composer discharging `MainOkCliPq cliImg` via
`main_ok_cli_pq_inst loads_cliImg`. -/
theorem cliBinaryCorrectPq5_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg) :
    CliBinaryCorrectPq5 elf :=
  cliBinaryCorrectPq5_of_elf_main hE htok hMusl hend hfS hfE hmainOff hfz hstat
    (main_ok_cli_pq_inst loads_cliImg)

theorem libsignalCliBinaryCorrectPq5_of_elf_main {bytes : List (BitVec 8)} {elf : ElfImage}
    {muslCode : List (BitVec 8)}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : MainOkCliPq cliImg) :
    LibsignalCliBinaryCorrectPq5 bytes :=
  ⟨elf, hparse, cliBinaryCorrectPq5_of_elf_main hE htok hMusl hend hfS hfE hmainOff hfz hstat hmain⟩

/-- Segment-slice 5-clause PQXDH bytes composer discharging `MainOkCliPq cliImg` via
`main_ok_cli_pq_inst loads_cliImg`. -/
theorem libsignalCliBinaryCorrectPq5_of_elf {bytes : List (BitVec 8)} {elf : ElfImage}
    {muslCode : List (BitVec 8)}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg) :
    LibsignalCliBinaryCorrectPq5 bytes :=
  ⟨elf, hparse, cliBinaryCorrectPq5_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat⟩

/-- Combine `CliBinaryCorrectPq5 elf` with `CliSpecPqxdhNoMatch` to conclude
`CliPqxdhElfCorrectUnderAllocOk elf`. -/
theorem cliPqBinaryCorrect_of_pq5_and_noMatch {elf : ElfImage}
    (hpq5 : CliBinaryCorrectPq5 elf)
    (hnm : ∀ W : CliHooks, CliPqNoMatchAllocOk elf W →
      ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdhNoMatch (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩) :
    CliPqxdhElfCorrectUnderAllocOk elf :=
  ⟨hpq5.1, fun W halloc X =>
    ⟨hpq5.2 W halloc.fiveAllocOk X, hnm W halloc.noMatchAllocOk X⟩⟩

/-- Whole-process PQXDH ELF composer from `CliElfCodeMatches elf`, `Cli.MuslHarness elf'`,
`MainOkCliPq img`, and `MainOkOver img`. -/
theorem cliPqBinaryCorrect_of_parts_observe {elf elf' : ElfImage} {img : Obj.Image} {Fr : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : MainOkCliPq img)
    (hover : MainOkOver img) :
    CliPqxdhElfCorrectUnderAllocOk elf :=
  ⟨hcode, fun W halloc X =>
    ⟨cliSpecPq_of_parts_observe himg hbase hpatch hE (hH W) hmain halloc.fiveAllocOk X,
     cliSpecPqNoMatch_of_parts_observe himg hbase hpatch hE (hH W) hover halloc.noMatchAllocOk X⟩⟩

theorem cliPqBinaryCorrect_of_harness_both {elf : ElfImage} {Fr : SepProp}
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hmain : MainOkCliPq cliImg)
    (hover : MainOkOver cliImg) :
    CliPqxdhElfCorrectUnderAllocOk elf :=
  cliPqBinaryCorrect_of_parts_observe loads_cliImg cliImg_base hcode
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i))
    (elfStaticOk_patchElfTokens hE) hH hmain hover

/-- Harness-generic whole-binary PQXDH composer discharging `MainOkCliPq cliImg` via
`main_ok_cli_pq_inst loads_cliImg`. -/
theorem cliPqBinaryCorrect_of_harness {elf : ElfImage} {Fr : SepProp}
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hover : MainOkOver cliImg) :
    CliPqxdhElfCorrectUnderAllocOk elf :=
  cliPqBinaryCorrect_of_harness_both hcode hE htok hH (main_ok_cli_pq_inst loads_cliImg) hover

theorem cliPqBinaryCorrect_of_elf_both {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : MainOkCliPq cliImg)
    (hover : MainOkOver cliImg) :
    CliPqxdhElfCorrectUnderAllocOk elf :=
  cliPqBinaryCorrect_of_harness_both (hfz.codeMatches cliImg_base hE) hE htok
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat) hmain hover

/-- Segment-slice whole-binary PQXDH composer combining `muslHarness_cliImg_of_elf`,
`main_ok_cli_pq_inst loads_cliImg`, and `MainOkOver cliImg`. -/
theorem cliPqBinaryCorrect_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hover : MainOkOver cliImg) :
    CliPqxdhElfCorrectUnderAllocOk elf :=
  cliPqBinaryCorrect_of_elf_both hE htok hMusl hend hfS hfE hmainOff hfz hstat
    (main_ok_cli_pq_inst loads_cliImg) hover

theorem libsignalCliPqBinaryCorrect_of_harness_both {bytes : List (BitVec 8)} {elf : ElfImage}
    {Fr : SepProp}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hmain : MainOkCliPq cliImg)
    (hover : MainOkOver cliImg) :
    CliPqxdhBinaryCorrectUnderAllocOk bytes :=
  ⟨elf, hparse, cliPqBinaryCorrect_of_harness_both hcode hE htok hH hmain hover⟩

/-- Harness-generic bytes composer (`ElfImage.parse` → `CliPqxdhBinaryCorrectUnderAllocOk bytes`). -/
theorem libsignalCliPqBinaryCorrect_of_harness {bytes : List (BitVec 8)} {elf : ElfImage}
    {Fr : SepProp}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hcode : CliElfCodeMatches elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : ∀ W : CliHooks,
      Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
        (entryOf cliImg Cli.mainName) Fr
        (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
        (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hover : MainOkOver cliImg) :
    CliPqxdhBinaryCorrectUnderAllocOk bytes :=
  ⟨elf, hparse, cliPqBinaryCorrect_of_harness hcode hE htok hH hover⟩

theorem libsignalCliPqBinaryCorrect_of_elf_both {bytes : List (BitVec 8)} {elf : ElfImage}
    {muslCode : List (BitVec 8)}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : MainOkCliPq cliImg)
    (hover : MainOkOver cliImg) :
    CliPqxdhBinaryCorrectUnderAllocOk bytes :=
  ⟨elf, hparse, cliPqBinaryCorrect_of_elf_both hE htok hMusl hend hfS hfE hmainOff hfz hstat hmain hover⟩

/-- Segment-slice bytes composer (`ElfImage.parse` → `CliPqxdhBinaryCorrectUnderAllocOk bytes`). -/
theorem libsignalCliPqBinaryCorrect_of_elf {bytes : List (BitVec 8)} {elf : ElfImage}
    {muslCode : List (BitVec 8)}
    (hparse : ElfImage.parse bytes = .ok elf)
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hover : MainOkOver cliImg) :
    CliPqxdhBinaryCorrectUnderAllocOk bytes :=
  ⟨elf, hparse, cliPqBinaryCorrect_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat hover⟩

/-! ## 5. Tightened `main`-Level PQXDH Hypotheses (`MainOkCliPqTight`, `MainOkOverTight`) -/

/-- Tight 5-clause PQXDH `main`-level specification (`MainOkCliPq` with `mainSpecTight`). -/
def MainOkCliPqTight (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
          ∃ a, Run (pqInitInputs WP st b t) a ∧
            observe (pqInitInputs WP st b t).files a =
              pqxdhExpectedOutcome WP (pqInitInputs WP st b t) (pqInitModel X WP st b t) ∧
            Cli.CommitOk (pqInitInputs WP st b t) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
          ∃ a, Run (pqSendInputs WP st m r) a ∧
            observe (pqSendInputs WP st m r).files a =
              pqxdhExpectedOutcome WP (pqSendInputs WP st m r) (pqSendModel WP st m r.toList) ∧
            Cli.CommitOk (pqSendInputs WP st m r) (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          ∃ a, Run (pqRecvInputs WP st (wireWhisper :: c) rc) a ∧
            observe (pqRecvInputs WP st (wireWhisper :: c) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wireWhisper :: c) rc)
                (pqRecvWhisperModel WP st c rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wireWhisper :: c) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a =
              pqxdhExpectedOutcome WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
                (pqRecvPrekeyModel X WP st m rc) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)) ∧
        (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
          c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
          ∃ a, Run (pqRecvInputs WP st c rc) a ∧
            observe (pqRecvInputs WP st c rc).files a =
              .exited 1 [] (filesOf (pqRecvInputs WP st c rc).files) ∧
            Cli.CommitOk (pqRecvInputs WP st c rc) (Cli.MainResult.ofAnswer a))

/-- Tight non-matching pre-key `main`-level specification (`MainOkOver` with `mainSpecTight`). -/
def MainOkOverTight (img : Obj.Image) : Prop :=
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → Cli.RunAnswer → Prop,
      subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
        (mainSpecTight E2E.HooksE.A0 img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run) ∧
      ∀ st : PqParty, PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState Bytes), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          ∃ a, Run (pqRecvInputs WP st (wirePrekey :: m.bytes) rc) a ∧
            OutcomeMatchesModelExceptPath WP (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (sessionFile (partyAddress st.party.other))
              (pqRecvPrekeyModel X WP { st with session := none } m rc)
              (observe (pqRecvInputs WP st (wirePrekey :: m.bytes) rc).files a) ∧
            Cli.CommitOk (pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
              (Cli.MainResult.ofAnswer a)

theorem MainOkCliPqTight.toMainOkCliPq {img : Obj.Image} (h : MainOkCliPqTight img) :
    MainOkCliPq img := by
  intro X W
  obtain ⟨Run, hmain, hclauses⟩ := h X W
  exact ⟨Run, subroutine_ok_mainSpec_of_tight hmain, hclauses⟩

theorem MainOkOverTight.toMainOkOver {img : Obj.Image} (h : MainOkOverTight img) :
    MainOkOver img := by
  intro X W
  obtain ⟨Run, hmain, hclause⟩ := h X W
  exact ⟨Run, subroutine_ok_mainSpec_of_tight hmain, hclause⟩

/-- Concrete tightened 5-clause PQXDH `main` witness from `Obj.Loads libsignalSessionImage cliImg`. -/
theorem main_ok_cli_pq_tight_inst
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkCliPqTight cliImg :=
  Cli.main_ok_cli_pq_tight_inst himg

/-- Concrete tightened SM `main` witness from `Obj.Loads libsignalSessionImage cliImg`. -/
theorem main_ok_cli_sm_tight_inst
    (himg : Obj.Loads libsignalSessionImage cliImg) :
    MainOkCliSmTight cliImg :=
  Cli.main_ok_cli_sm_tight_inst himg

end CryptoVerification.SignalSession
