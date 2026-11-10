/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.PqBundleInst
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge -- shake: keep
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run -- shake: keep

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Whole-Process Symbolic PQXDH Bridge

Composes `MainOkCliPq` and `ProcessBridge.cliRunsTo_of_main_call` into per-input (`CliSpecPqPerInput`)
and global-allocation (`CliSpecPqxdh`) 5-clause whole-process specifications on
`cliRunAbortOnPanic elf W`, together with unconditional OOM-disjunction counterparts.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.MuslElf CryptoVerification.SignalSession.ElfFrozen

/-! ## PQXDH Input Side Conditions -/

theorem inputsLoadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (hst : PqxdhPartyInSpecDomain W st) :
    Cli.InputsLoadable (pqInitInputs W st b t) := by
  refine ⟨(loadable_pqInitInputs W st b t).1, fun f hf =>
    ⟨(loadable_pqInitInputs W st b t).2 f hf, ?_⟩⟩
  simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hf
  rcases hf with h | h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · unfold publicBundleOf PublicBundle.files at h
    cases ho : b.opk with
    | none =>
      simp only [ho, Option.map_none, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [djbKey, kyberKey, le32, MAX_LFS_FILESIZE]
    | some ok =>
      obtain ⟨id, key⟩ := ok
      simp only [ho, Option.map_some, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        simp [djbKey, kyberKey, le32, MAX_LFS_FILESIZE]
  · simp [initiateTapeLen, MAX_LFS_FILESIZE]

theorem inputsLoadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) (hst : PqxdhPartyInSpecDomain W st) :
    Cli.InputsLoadable (pqSendInputs W st m r) := by
  refine ⟨(loadable_pqSendInputs W st m r).1, fun f hf =>
    ⟨(loadable_pqSendInputs W st m r).2 f hf, ?_⟩⟩
  simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [MAX_LFS_FILESIZE]

theorem inputsLoadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) (hst : PqxdhPartyInSpecDomain W st) :
    Cli.InputsLoadable (pqRecvInputs W st c rc) := by
  refine ⟨(loadable_pqRecvInputs W st c rc).1, fun f hf =>
    ⟨(loadable_pqRecvInputs W st c rc).2 f hf, ?_⟩⟩
  simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with h | rfl
  · have hlt := hst.2.1 f h; unfold MAX_LFS_FILESIZE; omega
  · simp [HMAC.keyToBytes32, MAX_LFS_FILESIZE]

theorem coinsReadable_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    Cli.CoinsReadable (pqInitInputs W st b t) :=
  Cli.coinsReadable_pqInputs W st _ _ _ _ (Or.inr ⟨b, rfl⟩)

theorem coinsReadable_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    Cli.CoinsReadable (pqSendInputs W st m r) :=
  Cli.coinsReadable_pqInputs W st _ _ _ _ (Or.inl rfl)

theorem coinsReadable_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CoinsReadable (pqRecvInputs W st c rc) :=
  Cli.coinsReadable_pqInputs W st _ _ _ _ (Or.inl rfl)

theorem cliInputsOk_pqInitInputs (W : PEParams) (st : PqParty) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    Cli.CliInputsOk (pqInitInputs W st b t) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack pqInitInputs pqInputs
  dsimp only
  cases st.party <;> decide

theorem cliInputsOk_pqSendInputs (W : PEParams) (st : PqParty) (m : List (BitVec 8))
    (r : List.Vector (BitVec 8) 64) :
    Cli.CliInputsOk (pqSendInputs W st m r) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack pqSendInputs pqInputs
  dsimp only
  cases st.party <;> decide

theorem cliInputsOk_pqRecvInputs (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (rc : BitVec 256) :
    Cli.CliInputsOk (pqRecvInputs W st c rc) := by
  unfold Cli.CliInputsOk PrintableAsciiArg ArgvFitsInitialStack pqRecvInputs pqInputs
  dsimp only
  cases st.party <;> decide

/-! ## Per-Input and 5-Clause Allocation-Failure Freedom -/

/-- Allocation-failure freedom on input `i` for `(elf, W)` starting from `cliTokenPatch s0` (`DEV-CLI10`). -/
def RunAllocOk (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  ∀ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 →
    Steps (cliProgAbortOnPanic W) (cliTokenPatch s0) s → RustHeap.allocFailedEvent ∉ s.trace

abbrev CliInputAllocOk : ElfImage → CliHooks → Inputs → Prop := RunAllocOk

/-- Unpatched allocation-failure freedom on input `i` starting directly at `s0`. -/
def CliInputAllocOkRaw (elf' : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  ∀ s0 s, elf'.loadState (cliProcessInputs i) = .ok s0 →
    Steps (cliProgAbortOnPanic W) s0 s → RustHeap.allocFailedEvent ∉ s.trace

theorem cliInputAllocOkRaw_of_patch {elf elf' : ElfImage} {W : CliHooks} {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hok : RunAllocOk elf W i) :
    CliInputAllocOkRaw elf' W i := by
  intro s0' s hload' hsteps
  rw [hpatch] at hload'
  cases hload : elf.loadState (cliProcessInputs i) with
  | error _ => rw [hload] at hload'; cases hload'
  | ok s0 =>
    rw [hload] at hload'
    simp only [Except.map, Except.ok.injEq] at hload'
    subst hload'
    exact hok s0 s hload hsteps

/-- Allocation-failure freedom across all five input families of `CliSpecPqxdh` (`init`, `send`, Whisper `recv`, PreKey `recv`, and malformed-prefix `recv`). -/
structure CliPqFiveAllocOk (elf : ElfImage) (W : CliHooks) : Prop where
  init : ∀ (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
    RunAllocOk elf W (pqInitInputs ⟨W.C, W.Q⟩ st b t)
  send : ∀ (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → m.length < 2 ^ 32 →
    RunAllocOk elf W (pqSendInputs ⟨W.C, W.Q⟩ st m r)
  recvWhisper : ∀ (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → c.length < 2 ^ 32 →
    RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc)
  recvPrekey : ∀ (st : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
  recvBad : ∀ (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256),
    PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → c.length < 2 ^ 32 →
    c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
    RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc)

/-- Weakens uniform `init`/`send`/`recv` (`c.length ≤ 2 ^ 32`) allocation-failure freedom to `CliPqFiveAllocOk`. -/
theorem CliPqFiveAllocOk.of_init_send_recv {elf : ElfImage} {W : CliHooks}
    (hInit : ∀ (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → st.session = none →
      RunAllocOk elf W (pqInitInputs ⟨W.C, W.Q⟩ st b t))
    (hSend : ∀ (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → m.length < 2 ^ 32 →
      RunAllocOk elf W (pqSendInputs ⟨W.C, W.Q⟩ st m r))
    (hRecv : ∀ (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256),
      PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st → c.length ≤ 2 ^ 32 →
      RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc)) :
    CliPqFiveAllocOk elf W where
  init := hInit
  send := hSend
  recvWhisper := fun st c rc hst hc =>
    hRecv st (wireWhisper :: c) rc hst (Nat.succ_le_of_lt hc)
  recvPrekey := fun st m rc hst hm _ =>
    hRecv st (wirePrekey :: m.bytes) rc hst (Nat.succ_le_of_lt (preKeyMsgE_bytes_lt_2_32 hm))
  recvBad := fun st c rc hst hc _ _ =>
    hRecv st c rc hst (Nat.le_of_lt hc)

theorem CliPqFiveAllocOk.of_uncond {elf : ElfImage} {W : CliHooks}
    (h : ∀ i : Inputs, RunAllocOk elf W i) :
    CliPqFiveAllocOk elf W :=
  CliPqFiveAllocOk.of_init_send_recv
    (fun st b t _ _ => h (pqInitInputs ⟨W.C, W.Q⟩ st b t))
    (fun st m r _ _ => h (pqSendInputs ⟨W.C, W.Q⟩ st m r))
    (fun st c rc _ _ => h (pqRecvInputs ⟨W.C, W.Q⟩ st c rc))

/-! ## Single-Input Whole-Process Call Bridges -/

theorem cliRunSig_of_main_stdinOverCap {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i)
    (halloc : RunAllocOk elf W i) :
    cliRunAbortOnPanic elf W i = some (.exited 2 [] (filesOf i.files)) := by
  have hraw : CliRunsToRaw elf' W i (.exited 2 [] (filesOf i.files)) :=
    cliRunsTo_of_main_stdinOverCap himg hbase hE hH hmain hi hl hstin
      (cliInputAllocOkRaw_of_patch hpatch halloc)
  exact cliRunSig_eq_some (cliRunsTo_of_raw hpatch hraw)

theorem cliRunSig_of_main_sendOverCap {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (halloc : RunAllocOk elf W i) :
    cliRunAbortOnPanic elf W i = some (observe i.files (some none)) := by
  have hraw : CliRunsToRaw elf' W i (observe i.files (some none)) :=
    cliRunsTo_of_main_sendOverCap himg hbase hE hH hmain hi hl hover hnstin hcoins
      (cliInputAllocOkRaw_of_patch hpatch halloc)
  exact cliRunSig_eq_some (cliRunsTo_of_raw hpatch hraw)

/-- Lifts `mainSpec`, `Run i a`, `observe i.files a = o`, and `RunAllocOk elf W i` across a token-patched `elf'` to `cliRunAbortOnPanic elf W i = some o`. -/
theorem cliRunSig_of_main_call_obs {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer} {o : Outcome}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W i) :
    cliRunAbortOnPanic elf W i = some o := by
  have hraw : CliRunsToRaw elf' W i o := by
    rw [← hobs]
    exact cliRunsTo_of_main_call himg hbase hE hH hmain hi hl hrun hnover hnstin hcoins hcommit
      (cliInputAllocOkRaw_of_patch hpatch halloc)
  exact cliRunSig_eq_some (cliRunsTo_of_raw hpatch hraw)

theorem cliRunSig_of_main_call {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W i) :
    cliRunAbortOnPanic elf W i = some (observe i.files a) :=
  cliRunSig_of_main_call_obs himg hbase hE hH hmain hpatch hi hl hrun hnover hnstin rfl hcoins hcommit halloc

/-- Relational outcome-predicate specialization of `cliRunSig_of_main_call` yielding `∃ o, cliRunAbortOnPanic elf W i = some o ∧ P o`. -/
theorem cliRunSig_of_main_call_pred {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop} {P : Outcome → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpec A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W i) :
    ∃ o, cliRunAbortOnPanic elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunSig_of_main_call himg hbase hE hH hmain hpatch hi hl hrun hnover hnstin hcoins hcommit halloc, hp⟩

theorem cliRunSig_of_harness_call_obs {elf : ElfImage} {Fr : SepProp} {W : CliHooks}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
      (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run))
    {i : Inputs} {a : Cli.RunAnswer} {o : Outcome}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W i) :
    cliRunAbortOnPanic elf W i = some o :=
  cliRunSig_of_main_call_obs loads_cliImg cliImg_base (elfStaticOk_patchElfTokens hE) hH hmain
    (loadState_patchElfTokens hE htok (cliProcessInputs i)) hi hl hrun hnover hnstin hobs hcoins hcommit halloc

theorem cliRunSig_of_harness_call_pred {elf : ElfImage} {Fr : SepProp} {W : CliHooks}
    {Run : Inputs → Cli.RunAnswer → Prop} {P : Outcome → Prop}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
      (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W i) :
    ∃ o, cliRunAbortOnPanic elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunSig_of_harness_call_obs hE htok hH hmain hi hl hrun hnover hnstin rfl hcoins hcommit halloc, hp⟩

/-- Segment-slice ELF-level single-input whole-process bridge at `cliImg`. -/
theorem cliRunSig_of_elf_call_obs {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run))
    {i : Inputs} {a : Cli.RunAnswer} {o : Outcome}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W i) :
    cliRunAbortOnPanic elf W i = some o :=
  cliRunSig_of_harness_call_obs hE htok
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat W)
    hmain hi hl hrun hnover hnstin hobs hcoins hcommit halloc

/-- Segment-slice ELF-level single-input relational outcome bridge at `cliImg`. -/
theorem cliRunSig_of_elf_call_pred {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    {Run : Inputs → Cli.RunAnswer → Prop} {P : Outcome → Prop}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W i) :
    ∃ o, cliRunAbortOnPanic elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunSig_of_elf_call_obs hE htok hMusl hend hfS hfE hmainOff hfz hstat hmain
      hi hl hrun hnover hnstin rfl hcoins hcommit halloc, hp⟩

/-- Specialization of `cliRunSig_of_elf_call_obs` to `pqRecvInputs`, discharging input side conditions automatically. -/
theorem cliRunSig_pqRecv_of_elf_call_obs {elf : ElfImage} {muslCode : List (BitVec 8)}
    {W : CliHooks} {Run : Inputs → Cli.RunAnswer → Prop}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {a : Cli.RunAnswer} {o : Outcome}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hc : c.length ≤ stdinCapBytes)
    (hrun : Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a)
    (hobs : observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a = o)
    (hcommit : Cli.CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc)) :
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) = some o :=
  cliRunSig_of_elf_call_obs hE htok hMusl hend hfS hfE hmainOff hfz hstat hmain
    (cliInputsOk_pqRecvInputs ⟨W.C, W.Q⟩ st c rc)
    (inputsLoadable_pqRecvInputs ⟨W.C, W.Q⟩ st c rc hst)
    hrun (not_isSendOverCap_pqRecvInputs ⟨W.C, W.Q⟩ st c rc)
    (not_isStdinOverCap_of_stdin_le hc) hobs
    (coinsReadable_pqRecvInputs ⟨W.C, W.Q⟩ st c rc)
    hcommit halloc

/-- Specialization of `cliRunSig_of_elf_call_pred` to `pqRecvInputs`. -/
theorem cliRunSig_pqRecv_of_elf_call_pred {elf : ElfImage} {muslCode : List (BitVec 8)}
    {W : CliHooks} {Run : Inputs → Cli.RunAnswer → Prop} {P : Outcome → Prop}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (hmain : subroutine_ok (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName)
      (Cli.mainSpec E2E.HooksE.A0 cliImg Cli.MainHops.cliMainStk (Cli.cliStatics cliImg) Run))
    {st : PqParty} {c : List (BitVec 8)} {rc : BitVec 256} {a : Cli.RunAnswer}
    (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (hc : c.length ≤ stdinCapBytes)
    (hrun : Run (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) a)
    (hp : P (observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a))
    (hcommit : Cli.CommitOk (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) (Cli.MainResult.ofAnswer a))
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc)) :
    ∃ o, cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) = some o ∧ P o :=
  ⟨observe (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files a,
    cliRunSig_pqRecv_of_elf_call_obs hE htok hMusl hend hfS hfE hmainOff hfz hstat hmain
      hst hc hrun rfl hcommit halloc, hp⟩

/-! ## Per-Input 5-Clause PQXDH Specification (`CliSpecPqPerInput`) -/

/-- Per-input 5-clause PQXDH specification where each clause assumes `RunAllocOk elf W` only on its own input rather than globally. -/
structure CliSpecPqPerInput (elf : ElfImage) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop where
  init : ∀ st : PqParty, PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
    ∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
    RunAllocOk elf W (pqInitInputs ⟨W.C, W.Q⟩ st b t) →
    cliRunAbortOnPanic elf W (pqInitInputs ⟨W.C, W.Q⟩ st b t) =
      some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputs ⟨W.C, W.Q⟩ st b t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t))
  send : ∀ st : PqParty, PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
    ∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
    RunAllocOk elf W (pqSendInputs ⟨W.C, W.Q⟩ st m r) →
    cliRunAbortOnPanic elf W (pqSendInputs ⟨W.C, W.Q⟩ st m r) =
      if m.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqSendInputs ⟨W.C, W.Q⟩ st m r).files))
      else if m.length > maxPlaintextBytes then
        some (.exited 1 [] (filesOf (pqSendInputs ⟨W.C, W.Q⟩ st m r).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqSendInputs ⟨W.C, W.Q⟩ st m r)
          (pqSendModel ⟨W.C, W.Q⟩ st m r.toList))
  recvWhisper : ∀ st : PqParty, PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
    ∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
    RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc) →
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc) =
      if (wireWhisper :: c).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc)
          (pqRecvWhisperModel ⟨W.C, W.Q⟩ st c rc))
  recvPrekey : ∀ st : PqParty, PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
    ∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
    RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) →
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
      if (wirePrekey :: m.bytes).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc))
  recvBad : ∀ st : PqParty, PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
    ∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
    c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
    RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) →
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) =
      if c.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files))
      else
        some (.exited 1 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files))

/-- Combines `CliSpecPqPerInput` and `CliPqFiveAllocOk` to establish `CliSpecPqxdh`. -/
theorem cliSpecPq_of_perInput {elf : ElfImage} {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (h : CliSpecPqPerInput elf X W)
    (halloc : CliPqFiveAllocOk elf W) :
    CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  fun st hst =>
    ⟨fun b t hnone => h.init st hst b t hnone (halloc.init st b t hst hnone),
     fun m r hm => h.send st hst m r hm (halloc.send st m r hst hm),
     fun c rc hc => h.recvWhisper st hst c rc hc (halloc.recvWhisper st c rc hst hc),
     fun m rc hm hmatch =>
       h.recvPrekey st hst m rc hm hmatch (halloc.recvPrekey st m rc hst hm hmatch),
     fun c rc hc h2 h3 =>
       h.recvBad st hst c rc hc h2 h3 (halloc.recvBad st c rc hst hc h2 h3)⟩

/-- Parameterized per-input 5-clause PQXDH composer from `MainOkCliPq img` and `Cli.MuslHarness`. -/
theorem cliSpecPqPerInput_of_parts_observe {elf elf' : ElfImage} {img : Obj.Image} {Fr : SepProp}
    {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : MainOkCliPq img) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqPerInput elf X W := by
  intro X
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain X W
  refine
    { init := fun st hst b t hnone halloc => ?_
      send := fun st hst m r hm halloc => ?_
      recvWhisper := fun st hst c rc hc halloc => ?_
      recvPrekey := fun st hst m rc hm hmatch halloc => ?_
      recvBad := fun st hst c rc hc h2 h3 halloc => ?_ }
  · obtain ⟨hInit, _, _, _, _⟩ := hclauses st hst
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunSig_of_main_call_obs himg hbase hE hH hmainW (hpatch _)
      (cliInputsOk_pqInitInputs WP st b t)
      (inputsLoadable_pqInitInputs WP st b t hst)
      hrun (not_isSendOverCap_pqInitInputs WP st b t)
      (not_isStdinOverCap_pqInitInputs WP st b t) hobs
      (coinsReadable_pqInitInputs WP st b t) hcommit halloc
  · by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_of_main_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqSendInputs WP st m r)
        (inputsLoadable_pqSendInputs WP st m r hst)
        (isStdinOverCap_pqSendInputs WP st m r hstin) halloc
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ Cli.IsStdinOverCap (pqSendInputs WP st m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunSig_of_main_sendOverCap himg hbase hE hH hmainW (hpatch _)
          (cliInputsOk_pqSendInputs WP st m r)
          (inputsLoadable_pqSendInputs WP st m r hst)
          (isSendOverCap_pqSendInputs WP st m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin
          (coinsReadable_pqSendInputs WP st m r) halloc
      · simp only [hover, ↓reduceIte]
        obtain ⟨_, hSend, _, _, _⟩ := hclauses st hst
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunSig_of_main_call_obs himg hbase hE hH hmainW (hpatch _)
          (cliInputsOk_pqSendInputs WP st m r)
          (inputsLoadable_pqSendInputs WP st m r hst)
          hrun (not_isSendOverCap_of_stdin_le (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs
          (coinsReadable_pqSendInputs WP st m r) hcommit halloc
  · by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_of_main_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP st (wireWhisper :: c) rc hst)
        (isStdinOverCap_pqRecvInputs WP st (wireWhisper :: c) rc hstin) halloc
    · simp only [hstin, ↓reduceIte]
      obtain ⟨_, _, hWhisper, _, _⟩ := hclauses st hst
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunSig_of_main_call_obs himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP st (wireWhisper :: c) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP st (wireWhisper :: c) rc) hcommit halloc
  · by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_of_main_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin) halloc
    · simp only [hstin, ↓reduceIte]
      obtain ⟨_, _, _, hPrekey, _⟩ := hclauses st hst
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunSig_of_main_call_obs himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit halloc
  · by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_of_main_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st c rc)
        (inputsLoadable_pqRecvInputs WP st c rc hst)
        (isStdinOverCap_pqRecvInputs WP st c rc hstin) halloc
    · simp only [hstin, ↓reduceIte]
      obtain ⟨_, _, _, _, hBad⟩ := hclauses st hst
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunSig_of_main_call_obs himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st c rc)
        (inputsLoadable_pqRecvInputs WP st c rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP st c rc) hcommit halloc

theorem cliSpecPqPerInput_of_slots {elf elf' : ElfImage} {Fr : SepProp}
    {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (_hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg))) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqPerInput elf X W :=
  cliSpecPqPerInput_of_parts_observe himg cliImg_base hpatch hE hH (main_ok_cli_pq_inst himg)

theorem cliSpecPqPerInput_of_harness {elf : ElfImage} {Fr : SepProp} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
      (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg))) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqPerInput elf X W :=
  cliSpecPqPerInput_of_parts_observe loads_cliImg cliImg_base
    (fun i => loadState_patchElfTokens hE htok (cliProcessInputs i))
    (elfStaticOk_patchElfTokens hE) hH (main_ok_cli_pq_inst loads_cliImg)

/-- Segment-slice ELF-level per-input 5-clause PQXDH composer. -/
theorem cliSpecPqPerInput_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqPerInput elf X W :=
  cliSpecPqPerInput_of_harness hE htok
    (muslHarness_cliImg_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat W)

/-! ## Individual Per-Input Clause Theorems -/

theorem cliSpecPq_init_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) (hnone : st.session = none)
    (halloc : RunAllocOk elf W (pqInitInputs ⟨W.C, W.Q⟩ st b t)) :
    cliRunAbortOnPanic elf W (pqInitInputs ⟨W.C, W.Q⟩ st b t) =
      some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqInitInputs ⟨W.C, W.Q⟩ st b t)
        (pqInitModel X ⟨W.C, W.Q⟩ st b t)) :=
  (cliSpecPqPerInput_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat X).init
    st hst b t hnone halloc

theorem cliSpecPq_send_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64) (hm : m.length < 2 ^ 32)
    (halloc : RunAllocOk elf W (pqSendInputs ⟨W.C, W.Q⟩ st m r)) :
    cliRunAbortOnPanic elf W (pqSendInputs ⟨W.C, W.Q⟩ st m r) =
      if m.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqSendInputs ⟨W.C, W.Q⟩ st m r).files))
      else if m.length > maxPlaintextBytes then
        some (.exited 1 [] (filesOf (pqSendInputs ⟨W.C, W.Q⟩ st m r).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqSendInputs ⟨W.C, W.Q⟩ st m r)
          (pqSendModel ⟨W.C, W.Q⟩ st m r.toList)) :=
  (cliSpecPqPerInput_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat
    Cli.MainHops.defaultModelExtras).send st hst m r hm halloc

theorem cliSpecPq_recvWhisper_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (c : List (BitVec 8)) (rc : BitVec 256) (hc : c.length < 2 ^ 32)
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc)) :
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc) =
      if (wireWhisper :: c).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wireWhisper :: c) rc)
          (pqRecvWhisperModel ⟨W.C, W.Q⟩ st c rc)) :=
  (cliSpecPqPerInput_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat
    Cli.MainHops.defaultModelExtras).recvWhisper st hst c rc hc halloc

theorem cliSpecPq_recvPrekey_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (m : PreKeyMessageFields) (rc : BitVec 256) (hm : m.inner.length + 2048 < 2 ^ 32)
    (hmatch : ∀ x g, st.session = some (x, g) → PqSessionMatches x g m)
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)) :
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc) =
      if (wirePrekey :: m.bytes).length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc).files))
      else
        some (pqxdhExpectedOutcome ⟨W.C, W.Q⟩ (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc)
          (pqRecvPrekeyModel X ⟨W.C, W.Q⟩ st m rc)) :=
  (cliSpecPqPerInput_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat X).recvPrekey
    st hst m rc hm hmatch halloc

theorem cliSpecPq_recvBad_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    {st : PqParty} (hst : PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st)
    (c : List (BitVec 8)) (rc : BitVec 256) (hc : c.length < 2 ^ 32)
    (h2 : c.head? ≠ some wireWhisper) (h3 : c.head? ≠ some wirePrekey)
    (halloc : RunAllocOk elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc)) :
    cliRunAbortOnPanic elf W (pqRecvInputs ⟨W.C, W.Q⟩ st c rc) =
      if c.length > stdinCapBytes then
        some (.exited 2 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files))
      else
        some (.exited 1 [] (filesOf (pqRecvInputs ⟨W.C, W.Q⟩ st c rc).files)) :=
  (cliSpecPqPerInput_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat
    Cli.MainHops.defaultModelExtras).recvBad st hst c rc hc h2 h3 halloc

/-! ## Global-Allocation `CliSpecPqxdh` Corollaries -/

/-- Parameterized 5-clause `CliSpecPqxdh` composer from `MainOkCliPq img`, `Cli.MuslHarness`, and `CliPqFiveAllocOk`. -/
theorem cliSpecPq_of_parts_observe {elf elf' : ElfImage} {img : Obj.Image} {Fr : SepProp}
    {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : MainOkCliPq img)
    (halloc : CliPqFiveAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  fun X => cliSpecPq_of_perInput
    (cliSpecPqPerInput_of_parts_observe himg hbase hpatch hE hH hmain X) halloc

theorem cliSpecPq_of_slots {elf elf' : ElfImage} {Fr : SepProp}
    {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (halloc : CliPqFiveAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  fun X => cliSpecPq_of_perInput
    (cliSpecPqPerInput_of_slots himg hcode hpatch hE hH X) halloc

theorem cliProcess_ok_pq {elf elf' : ElfImage} {Fr : SepProp}
    {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage cliImg)
    (hcode : CliElfCodeMatches elf)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg cliImg (cliExterns W)) (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (halloc : CliPqFiveAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  cliSpecPq_of_slots himg hcode hpatch hE hH halloc

theorem cliSpecPq_of_harness {elf : ElfImage} {Fr : SepProp} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hH : Cli.MuslHarness (patchElfTokens elf) (Cli.cliProg cliImg (cliExterns W))
      (entryOf cliImg Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre cliImg E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics cliImg)))
    (halloc : CliPqFiveAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  fun X => cliSpecPq_of_perInput (cliSpecPqPerInput_of_harness hE htok hH X) halloc

/-- Segment-slice ELF-level 5-clause `CliSpecPqxdh` composer. -/
theorem cliSpecPq_of_elf {elf : ElfImage} {muslCode : List (BitVec 8)} {W : CliHooks}
    (hE : Cli.ElfStaticOk elf)
    (htok : CliElfTokenCells elf)
    (hMusl : CliElfMusl elf muslCode)
    (hend : cliBase.toNat + libsignalSessionImage.code.length ≤ elf.entry.toNat)
    (hfS : MuslStart.MuslStartFetch ({ code := muslCode } : Program) 0#64)
    (hfE : MuslExit.MuslExitFetch ({ code := muslCode } : Program) 0#64)
    (hmainOff : entryOf cliImg Cli.mainName = elf.entry - muslMainDelta)
    (hfz : CliElfFrozen elf cliImg)
    (hstat : CliElfStatics (patchElfTokens elf) cliImg)
    (halloc : CliPqFiveAllocOk elf W) :
    ∀ X : UnreachedPqxdhPrimitives, CliSpecPqxdh (cliRunAbortOnPanic elf W) X ⟨W.C, W.Q⟩ :=
  fun X => cliSpecPq_of_perInput
    (cliSpecPqPerInput_of_elf hE htok hMusl hend hfS hfE hmainOff hfz hstat X) halloc

/-! ## Unconditional OOM-Disjunction PQXDH Bridge -/

theorem cliInputAllocFails_iff_not_allocOk {elf : ElfImage} {W : CliHooks} {i : Inputs} :
    CliInputAllocFails elf W i ↔ ¬ CliInputAllocOk elf W i := by
  unfold CliInputAllocFails CliInputAllocOk RunAllocOk
  constructor
  · rintro ⟨s0, s, hload, hsteps, hmem⟩ hok
    exact hok s0 s hload hsteps hmem
  · intro hnot
    exact Classical.byContradiction fun hno =>
      hnot fun s0 s hload hsteps hmem => hno ⟨s0, s, hload, hsteps, hmem⟩

theorem cliRunSig_eq_or_aborted_stdinOverCap {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hstin : Cli.IsStdinOverCap i) :
    cliRunAbortOnPanic elf W i = some (.exited 2 [] (filesOf i.files)) ∨
      (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i) := by
  rcases cliRunsTo_or_aborted_of_main_stdinOverCap_patch himg hbase hE hH hmain hpatch
      hi hl hstin with hruns | ⟨habort, hfail⟩
  · exact Or.inl (cliRunSig_eq_some hruns)
  · exact Or.inr ⟨cliRunSig_eq_some habort, cliInputAllocFails_iff_not_allocOk.mp hfail⟩

theorem cliRunSig_eq_or_aborted_sendOverCap {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hover : Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i) :
    cliRunAbortOnPanic elf W i = some (observe i.files (some none)) ∨
      (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i) := by
  rcases cliRunsTo_or_aborted_of_main_sendOverCap_patch himg hbase hE hH hmain hpatch
      hi hl hover hnstin hcoins with hruns | ⟨habort, hfail⟩
  · exact Or.inl (cliRunSig_eq_some hruns)
  · exact Or.inr ⟨cliRunSig_eq_some habort, cliInputAllocFails_iff_not_allocOk.mp hfail⟩

/-- Under `Cli.mainSpecTight`, either `cliRunAbortOnPanic elf W i = some (observe i.files a)` or the process aborts on an allocation failure (`¬ CliInputAllocOk elf W i`). -/
theorem cliRunSig_eq_or_aborted {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    cliRunAbortOnPanic elf W i = some (observe i.files a) ∨
      (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i) := by
  rcases cliRunsTo_or_aborted_of_main_call_patch himg hbase hE hH hmain hpatch
      hi hl hrun hnover hnstin hcoins hcommit with hruns | ⟨habort, hfail⟩
  · exact Or.inl (cliRunSig_eq_some hruns)
  · exact Or.inr ⟨cliRunSig_eq_some habort, cliInputAllocFails_iff_not_allocOk.mp hfail⟩

theorem cliRunSig_eq_or_aborted_obs {elf elf' : ElfImage} {img : Obj.Image}
    {W : CliHooks} {A : RustHeap.RustAlloc} {Fr : SepProp}
    {Run : Inputs → Cli.RunAnswer → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img A Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : subroutine_ok (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName)
      (Cli.mainSpecTight A img Cli.MainHops.cliMainStk (Cli.cliStatics img) Run))
    {i : Inputs} {a : Cli.RunAnswer} {o : Outcome}
    (hpatch : elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hi : Cli.CliInputsOk i)
    (hl : Cli.InputsLoadable i)
    (hrun : Run i a)
    (hnover : ¬ Cli.IsSendOverCap i)
    (hnstin : ¬ Cli.IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : Cli.CoinsReadable i)
    (hcommit : Cli.CommitOk i (Cli.MainResult.ofAnswer a)) :
    cliRunAbortOnPanic elf W i = some o ∨
      (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i) := by
  rw [← hobs]
  exact cliRunSig_eq_or_aborted himg hbase hE hH hmain hpatch hi hl hrun hnover hnstin hcoins hcommit

/-- Unconditional 5-clause PQXDH OOM-disjunction composer requiring no allocation-freedom hypothesis. -/
theorem cliSpecPq_or_aborted_of_parts_observe {elf elf' : ElfImage} {img : Obj.Image}
    {Fr : SepProp} {W : CliHooks}
    (himg : Obj.Loads libsignalSessionImage img)
    (hbase : img.base = cliBase)
    (hpatch : ∀ i, elf'.loadState (cliProcessInputs i) =
      (elf.loadState (cliProcessInputs i)).map cliTokenPatch)
    (hE : Cli.ElfStaticOk elf')
    (hH : Cli.MuslHarness elf' (Cli.cliProg img (cliExterns W)) (entryOf img Cli.mainName) Fr
      (fun i => Cli.CliInputsOk i ∧ Cli.InputsLoadable i)
      (Cli.mainEntryPre img E2E.HooksE.A0 Cli.MainHops.cliMainStk (Cli.cliStatics img)))
    (hmain : Cli.MainOkCliPqTight img) :
    ∀ (X : UnreachedPqxdhPrimitives) (st : PqParty), PqxdhPartyInSpecDomain ⟨W.C, W.Q⟩ st →
      let WP : PEParams := ⟨W.C, W.Q⟩
      (∀ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none →
        let i := pqInitInputs WP st b t
        cliRunAbortOnPanic elf W i = some (pqxdhExpectedOutcome WP i (pqInitModel X WP st b t)) ∨
          (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i)) ∧
      (∀ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 →
        let i := pqSendInputs WP st m r
        cliRunAbortOnPanic elf W i = some (if m.length > stdinCapBytes then
            .exited 2 [] (filesOf i.files)
          else if m.length > maxPlaintextBytes then
            .exited 1 [] (filesOf i.files)
          else
            pqxdhExpectedOutcome WP i (pqSendModel WP st m r.toList)) ∨
          (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        let i := pqRecvInputs WP st (wireWhisper :: c) rc
        cliRunAbortOnPanic elf W i = some (if (wireWhisper :: c).length > stdinCapBytes then
            .exited 2 [] (filesOf i.files)
          else
            pqxdhExpectedOutcome WP i (pqRecvWhisperModel WP st c rc)) ∨
          (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i)) ∧
      (∀ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 →
        (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
        let i := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
        cliRunAbortOnPanic elf W i = some (if (wirePrekey :: m.bytes).length > stdinCapBytes then
            .exited 2 [] (filesOf i.files)
          else
            pqxdhExpectedOutcome WP i (pqRecvPrekeyModel X WP st m rc)) ∨
          (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i)) ∧
      (∀ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 →
        c.head? ≠ some wireWhisper → c.head? ≠ some wirePrekey →
        let i := pqRecvInputs WP st c rc
        cliRunAbortOnPanic elf W i = some (if c.length > stdinCapBytes then
            .exited 2 [] (filesOf i.files)
          else
            .exited 1 [] (filesOf i.files)) ∨
          (cliRunAbortOnPanic elf W i = some .aborted ∧ ¬ CliInputAllocOk elf W i)) := by
  intro X st hst
  dsimp only
  let WP : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨Run, hmainW, hclauses⟩ := hmain X W
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hBad⟩ := hclauses st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    obtain ⟨a, hrun, hobs, hcommit⟩ := hInit b t hnone
    exact cliRunSig_eq_or_aborted_obs himg hbase hE hH hmainW (hpatch _)
      (cliInputsOk_pqInitInputs WP st b t)
      (inputsLoadable_pqInitInputs WP st b t hst)
      hrun (not_isSendOverCap_pqInitInputs WP st b t)
      (not_isStdinOverCap_pqInitInputs WP st b t) hobs
      (coinsReadable_pqInitInputs WP st b t) hcommit
  · intro m r hm
    by_cases hstin : m.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_eq_or_aborted_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqSendInputs WP st m r)
        (inputsLoadable_pqSendInputs WP st m r hst)
        (isStdinOverCap_pqSendInputs WP st m r hstin)
    · simp only [hstin, ↓reduceIte]
      have hnstin : ¬ Cli.IsStdinOverCap (pqSendInputs WP st m r) :=
        not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)
      by_cases hover : m.length > maxPlaintextBytes
      · simp only [hover, ↓reduceIte]
        exact cliRunSig_eq_or_aborted_sendOverCap himg hbase hE hH hmainW (hpatch _)
          (cliInputsOk_pqSendInputs WP st m r)
          (inputsLoadable_pqSendInputs WP st m r hst)
          (isSendOverCap_pqSendInputs WP st m r (by unfold maxPlaintextBytes at hover; exact hover))
          hnstin
          (coinsReadable_pqSendInputs WP st m r)
      · simp only [hover, ↓reduceIte]
        obtain ⟨a, hrun, hobs, hcommit⟩ := hSend m r hm
        exact cliRunSig_eq_or_aborted_obs himg hbase hE hH hmainW (hpatch _)
          (cliInputsOk_pqSendInputs WP st m r)
          (inputsLoadable_pqSendInputs WP st m r hst)
          hrun (not_isSendOverCap_of_stdin_le (by simp only [pqSendInputs, pqInputs]; unfold maxPlaintextBytes at hover; omega))
          hnstin hobs
          (coinsReadable_pqSendInputs WP st m r) hcommit
  · intro c rc hc
    by_cases hstin : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_eq_or_aborted_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP st (wireWhisper :: c) rc hst)
        (isStdinOverCap_pqRecvInputs WP st (wireWhisper :: c) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hWhisper c rc hc
      exact cliRunSig_eq_or_aborted_obs himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wireWhisper :: c) rc)
        (inputsLoadable_pqRecvInputs WP st (wireWhisper :: c) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wireWhisper :: c) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP st (wireWhisper :: c) rc) hcommit
  · intro m rc hm hmatch
    by_cases hstin : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_eq_or_aborted_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        (isStdinOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hPrekey m rc hm hmatch
      exact cliRunSig_eq_or_aborted_obs himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (inputsLoadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st (wirePrekey :: m.bytes) rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP st (wirePrekey :: m.bytes) rc) hcommit
  · intro c rc hc h2 h3
    by_cases hstin : c.length > stdinCapBytes
    · simp only [hstin, ↓reduceIte]
      exact cliRunSig_eq_or_aborted_stdinOverCap himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st c rc)
        (inputsLoadable_pqRecvInputs WP st c rc hst)
        (isStdinOverCap_pqRecvInputs WP st c rc hstin)
    · simp only [hstin, ↓reduceIte]
      obtain ⟨a, hrun, hobs, hcommit⟩ := hBad c rc hc h2 h3
      exact cliRunSig_eq_or_aborted_obs himg hbase hE hH hmainW (hpatch _)
        (cliInputsOk_pqRecvInputs WP st c rc)
        (inputsLoadable_pqRecvInputs WP st c rc hst)
        hrun (not_isSendOverCap_pqRecvInputs WP st c rc)
        (not_isStdinOverCap_of_stdin_le (Nat.le_of_not_gt hstin)) hobs
        (coinsReadable_pqRecvInputs WP st c rc) hcommit


end CryptoVerification.SignalSession
