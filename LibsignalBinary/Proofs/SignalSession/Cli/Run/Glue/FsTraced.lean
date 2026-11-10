/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees

@[expose] public section

set_option autoImplicit false

/-!
# Filesystem Trace Soundness (`TraceFsSound`) for the CLI Extern Table

Proves `TraceFsSound` at `cliExterns W` and under `CliExternsOk` (`traceFsSound_cli`,
`traceFsSound_cliExternsWith`), along with non-I/O `State.fs` preservation (`FsKept`):
1. Every row of `cliHookTable W` and `Rust.panicked` satisfies `HookFsTraced IsFsC`
   (`IsFsC := TraceEvent.isFsChange`), modifying `fs.files` only when appending `fileChanged p`.
2. Every `IsFsC` event is non-quiet (`¬ QuietEv`), so `Steps.files_eq_of_noFs` yields
   `TraceFsSound` across arbitrary base addresses and panic wrappers.
-/

namespace CryptoVerification.SignalSession.Cli.RunGlue

open Arm64 ProofLib
open CryptoVerification.LibsignalPublicApi.StoreKit

set_option linter.unusedSimpArgs false

/-! ## Events -/

/-- The engine's file-change events (`TraceEvent.isFsChange`) as a predicate. -/
def IsFsC (e : TraceEvent) : Prop := e.isFsChange = true

/-- An `isFsChange` event (bytes written to a file descriptor, `fileChanged`) is not quiet. -/
theorem isFsC_not_quiet (e : TraceEvent) (h : IsFsC e) : ¬ QuietEv e := by
  intro hq
  unfold IsFsC at h
  unfold QuietEv at hq
  cases e with
  | writeByte st b => cases st <;> simp [TraceEvent.isFsChange, quietEv] at h hq
  | userDefined tag p => simp [TraceEvent.isFsChange] at h
  | fileChanged p => simp [quietEv] at hq

/-- `FsTraced` at `IsFsC`. -/
abbrev FsT (s s' : State) : Prop := FsTraced IsFsC s s'

/-! ## Allocation and fresh vectors -/

/-- `bumpThen` is traced from `s0` when both continuations are. -/
theorem bumpThen_fsT {s0 s : State} {size align : Nat} {ok : State → BitVec 64 → State}
    {fail : State → State}
    (hok : ∀ p, FsT s0 (ok (s.setMem (s.mem.mapFresh p size Perm.rw)) p))
    (hfail : FsT s0 (fail s)) : FsT s0 (E2E.bumpThen size align ok fail s) := by
  unfold E2E.bumpThen
  split
  · exact hok _
  · exact hfail

/-- `vecOk bs` preserves `FsT s0` when `s` has the trace and files of `s0` (the out-of-memory
branch `allocPanicHook` appends `allocFailedEvent` and leaves `files` unchanged). -/
theorem vecOk_fsT {s0 s : State} (bs : List (BitVec 8)) (ht : s.trace = s0.trace)
    (hf : s.fs.files = s0.fs.files) : FsT s0 (vecOk bs s) := by
  unfold vecOk
  split
  · exact FsTraced.of_eq ht hf
  · exact bumpThen_fsT (fun _ => FsTraced.of_eq ht hf)
      (FsTraced.of_files [CryptoVerification.RustHeap.allocFailedEvent]
        (congrArg (· ++ [CryptoVerification.RustHeap.allocFailedEvent]) ht) hf)

theorem vecOutThen_fsT (bs : List (BitVec 8)) (s : State) : FsT s (E2E.returnFreshVecU8 bs s) := by
  unfold E2E.returnFreshVecU8
  exact bumpThen_fsT (fun _ => FsTraced.of_eq rfl rfl) (FsTraced.of_files _ rfl rfl)

/-- Close one leaf: the trace and the files are those of the start; or the trace grows and the
files stay; or a fresh vector; or the trace grows by one `isFsChange` event. -/
macro "fsT_leaf" : tactic => `(tactic| first
  | exact FsTraced.of_eq rfl rfl
  | exact FsTraced.of_files _ rfl rfl
  | exact CryptoVerification.SignalSession.Cli.RunGlue.vecOk_fsT _ rfl rfl
  | exact CryptoVerification.SignalSession.Cli.RunGlue.vecOutThen_fsT _ _
  | exact FsTraced.of_fsEvent _ rfl _ (List.mem_singleton_self _) rfl
  | (refine CryptoVerification.SignalSession.Cli.RunGlue.bumpThen_fsT (fun _ => ?_) ?_ <;>
      (try dsimp only) <;>
      first | exact FsTraced.of_eq rfl rfl | exact FsTraced.of_files _ rfl rfl))

/-- Zeta-reduce, split every `if` and `match`, close each leaf with `fsT_leaf`. -/
macro "fsT_close" : tactic => `(tactic| (
  try dsimp only
  repeat' split
  all_goals fsT_leaf))

/-! ## The hooks -/

theorem hookNoop_fsT : HookFsTraced IsFsC hookNoop := fun _ => FsTraced.of_eq rfl rfl

theorem panicked_fsT : HookFsTraced IsFsC Rust.panicked := fun _ => FsTraced.of_eq rfl rfl

theorem allocHook0_fsT : HookFsTraced IsFsC E2E.allocHook0 := by
  intro s; unfold E2E.allocHook0; fsT_close

theorem reallocHook0_fsT : HookFsTraced IsFsC E2E.reallocHook0 := by
  intro s; unfold E2E.reallocHook0; fsT_close

theorem allocZeroedHook0_fsT : HookFsTraced IsFsC E2E.allocZeroedHook0 := by
  intro s; unfold E2E.allocZeroedHook0; fsT_close

theorem deallocHook_fsT : HookFsTraced IsFsC E2E.deallocHook := hookNoop_fsT

theorem stringCloneHook0_fsT : HookFsTraced IsFsC E2E.stringCloneHook0 := by
  intro s; unfold E2E.stringCloneHook0; exact vecOutThen_fsT _ s

theorem hookMemset_fsT : HookFsTraced IsFsC hookMemset := fun _ => FsTraced.of_eq rfl rfl

theorem hookMemcpy_fsT : HookFsTraced IsFsC hookMemcpy := fun _ => FsTraced.of_eq rfl rfl

theorem hookMemmove_fsT : HookFsTraced IsFsC hookMemmove := hookMemcpy_fsT

/-! ### The I/O functions -/

theorem readFileHook_fsT : HookFsTraced IsFsC readFileHook := by
  intro s; unfold readFileHook; fsT_close

/-- The only hook that changes the files: after appending `fileChanged p`. -/
theorem writeFileHook_fsT : HookFsTraced IsFsC writeFileHook := by
  intro s; unfold writeFileHook; fsT_close

theorem readStdinHook_fsT : HookFsTraced IsFsC readStdinHook := by
  intro s; unfold readStdinHook; fsT_close

theorem writeStdoutHook_fsT : HookFsTraced IsFsC writeStdoutHook := by
  intro s; unfold writeStdoutHook; fsT_close

/-! ### libc, `core`, `std` -/

theorem strlenHook_fsT : HookFsTraced IsFsC strlenHook := by
  intro s; unfold strlenHook; fsT_close

theorem memrchrHook_fsT : HookFsTraced IsFsC memrchrHook := by
  intro s; unfold memrchrHook; fsT_close

theorem fromUtf8Hook_fsT (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    HookFsTraced IsFsC (fromUtf8Hook err) := by
  intro s; unfold fromUtf8Hook; fsT_close

theorem durationSinceExactHook_fsT : HookFsTraced IsFsC durationSinceExactHook := by
  intro s; unfold durationSinceExactHook; fsT_close

theorem cliBcmpHook_fsT (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64) :
    HookFsTraced IsFsC (cliBcmpHook bcmp) := fun _ => FsTraced.of_eq rfl rfl

theorem fmtWriteHook0_fsT : HookFsTraced IsFsC E2E.fmtWriteHook0 :=
  fun _ => FsTraced.of_eq rfl rfl

theorem formatInnerHook0_fsT : HookFsTraced IsFsC E2E.formatInnerHook0 :=
  fun _ => FsTraced.of_eq rfl rfl

theorem timeAddHook_fsT : HookFsTraced IsFsC E2E.timeAddHook := by
  intro s; unfold E2E.timeAddHook; fsT_close

theorem blackBoxHook_fsT : HookFsTraced IsFsC LibsignalSession.blackBoxHook := by
  intro s; unfold LibsignalSession.blackBoxHook; fsT_close

/-! ### The primitives -/

theorem compress256Hook_fsT (F : CryptoGames.HMAC.ShaState → List (BitVec 8) →
    CryptoGames.HMAC.ShaState) : HookFsTraced IsFsC (LibsignalHmac.compress256Hook F) := by
  intro s; unfold LibsignalHmac.compress256Hook; fsT_close

theorem aesEncHook0_fsT (E : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    HookFsTraced IsFsC (E2E.aesEncHook0 E) := by
  intro s; unfold E2E.aesEncHook0; fsT_close

theorem aesDecHook0_fsT (D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block) :
    HookFsTraced IsFsC (E2E.aesDecHook0 D) := by
  intro s; unfold E2E.aesDecHook0; fsT_close

theorem pubFromSecretHook_fsT (pubKey : CryptoGames.LibsignalSession.PubKeyFn) :
    HookFsTraced IsFsC (LibsignalTripleRatchet.pubFromSecretHook pubKey) := by
  intro s; unfold LibsignalTripleRatchet.pubFromSecretHook; fsT_close

theorem diffieHellmanHook_fsT (X : CryptoGames.Ratchet.X25519Fn) :
    HookFsTraced IsFsC (LibsignalTripleRatchet.diffieHellmanHook X) := by
  intro s; unfold LibsignalTripleRatchet.diffieHellmanHook; fsT_close

theorem zeroizeSecretHook_fsT : HookFsTraced IsFsC LibsignalTripleRatchet.zeroizeSecretHook := by
  intro s; unfold LibsignalTripleRatchet.zeroizeSecretHook; fsT_close

/-! ### PQXDH and SPQR -/

theorem compress512Hook_fsT (F512 : E2E.Sha512State → List (BitVec 8) → E2E.Sha512State) :
    HookFsTraced IsFsC (E2E.compress512Hook F512) := by
  intro s; unfold E2E.compress512Hook; fsT_close

theorem toEdwardsHook_fsT
    (montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160)) :
    HookFsTraced IsFsC (E2E.toEdwardsHook montToEd) := by
  intro s; unfold E2E.toEdwardsHook; fsT_close

theorem compressHook_fsT (compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32) :
    HookFsTraced IsFsC (E2E.compressHook compress) := by
  intro s; unfold E2E.compressHook; fsT_close

theorem edNegHook_fsT (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160) :
    HookFsTraced IsFsC (E2E.edNegHook edNeg) := by
  intro s; unfold E2E.edNegHook; fsT_close

theorem torsionFreeHook_fsT (isTorsionFree : List.Vector (BitVec 8) 160 → Bool) :
    HookFsTraced IsFsC (E2E.torsionFreeHook isTorsionFree) := by
  intro s; unfold E2E.torsionFreeHook; fsT_close

theorem dsmbHook_fsT (dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160) :
    HookFsTraced IsFsC (E2E.dsmbHook dsmb) := by
  intro s; unfold E2E.dsmbHook; fsT_close

theorem scalarModHook_fsT (scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32) :
    HookFsTraced IsFsC (E2E.scalarModHook scalarMod) := by
  intro s; unfold E2E.scalarModHook; fsT_close

theorem scalarWideHook_fsT
    (scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32) :
    HookFsTraced IsFsC (E2E.scalarWideHook scalarWide) := by
  intro s; unfold E2E.scalarWideHook; fsT_close

theorem kemEncapsHook_fsT (encaps : List.Vector (BitVec 8) 1568 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32) :
    HookFsTraced IsFsC (E2E.kemEncapsHook encaps) := by
  intro s; unfold E2E.kemEncapsHook; fsT_close

theorem kemDecapsHook_fsT (decaps : List.Vector (BitVec 8) 3168 →
    List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32) :
    HookFsTraced IsFsC (E2E.kemDecapsHook decaps) := by
  intro s; unfold E2E.kemDecapsHook; fsT_close

theorem mlkemFromSeedHook_fsT (K : LibsignalSpqrV1.MlKem) :
    HookFsTraced IsFsC (E2E.mlkemFromSeedHook K) := fun _ => FsTraced.of_eq rfl rfl

theorem mlkemPk1Hook_fsT : HookFsTraced IsFsC E2E.mlkemPk1Hook := fun _ => FsTraced.of_eq rfl rfl

theorem mlkemPk2Hook_fsT : HookFsTraced IsFsC E2E.mlkemPk2Hook := fun _ => FsTraced.of_eq rfl rfl

theorem mlkemEncaps1Hook_fsT (K : LibsignalSpqrV1.MlKem) :
    HookFsTraced IsFsC (E2E.mlkemEncaps1Hook K) := by
  intro s; unfold E2E.mlkemEncaps1Hook retHook; fsT_close

theorem mlkemEncaps2Hook_fsT (K : LibsignalSpqrV1.MlKem) :
    HookFsTraced IsFsC (E2E.mlkemEncaps2Hook K) := fun _ => FsTraced.of_eq rfl rfl

theorem mlkemDecapsHook_fsT (K : LibsignalSpqrV1.MlKem) :
    HookFsTraced IsFsC (E2E.mlkemDecapsHook K) := fun _ => FsTraced.of_eq rfl rfl

theorem mlkemValidatePkHook_fsT (K : LibsignalSpqrV1.MlKem) :
    HookFsTraced IsFsC (E2E.mlkemValidatePkHook K) := fun _ => FsTraced.of_eq rfl rfl

theorem libcruxHmacHook_fsT
    (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState) :
    HookFsTraced IsFsC (E2E.libcruxHmacHook F) := by
  intro s
  unfold E2E.libcruxHmacHook
  dsimp only
  by_cases h1 : ((s.readReg64 .x0).setWidth 32 != 0#32) = true
  · simp only [h1, ↓reduceIte]; exact FsTraced.of_eq rfl rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (s.readReg64 .x2).toNat < 2 ^ 32 ∧ (s.readReg64 .x4).toNat < 2 ^ 32
    · simp only [h2, and_self, ↓reduceIte]
      exact bumpThen_fsT (fun _ => FsTraced.of_eq rfl rfl) (FsTraced.of_files _ rfl rfl)
    · simp only [h2, ↓reduceIte]; exact FsTraced.of_eq rfl rfl

/-! ## The table and the program -/

/-- Every row of `cliHookTable W` satisfies `HookFsTraced IsFsC`. -/
theorem cliHookTable_fsT (W : CliHooks) : ∀ p ∈ cliHookTable W, HookFsTraced IsFsC p.2 := by
  simp only [cliHookTable, E2E.pqxdhHookTable, E2E.spqrHookTable, List.cons_append,
    List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, compress512Hook_fsT, toEdwardsHook_fsT, compressHook_fsT, edNegHook_fsT,
    torsionFreeHook_fsT, dsmbHook_fsT, scalarModHook_fsT, scalarWideHook_fsT,
    kemEncapsHook_fsT, kemDecapsHook_fsT, mlkemFromSeedHook_fsT, mlkemPk1Hook_fsT,
    mlkemPk2Hook_fsT, mlkemEncaps1Hook_fsT, mlkemEncaps2Hook_fsT, mlkemDecapsHook_fsT,
    mlkemValidatePkHook_fsT, libcruxHmacHook_fsT,
    hookNoop_fsT, allocHook0_fsT, deallocHook_fsT, reallocHook0_fsT, allocZeroedHook0_fsT,
    hookMemset_fsT, hookMemmove_fsT, hookMemcpy_fsT, cliBcmpHook_fsT, strlenHook_fsT,
    readFileHook_fsT, writeFileHook_fsT, readStdinHook_fsT, writeStdoutHook_fsT,
    memrchrHook_fsT, fromUtf8Hook_fsT, fmtWriteHook0_fsT,
    formatInnerHook0_fsT, durationSinceExactHook_fsT, timeAddHook_fsT, blackBoxHook_fsT,
    compress256Hook_fsT, aesEncHook0_fsT, aesDecHook0_fsT, pubFromSecretHook_fsT,
    diffieHellmanHook_fsT, zeroizeSecretHook_fsT]

/-- Every hook of the table `X` is `HookFsTraced IsFsC`. -/
def FsTHooks (X : String → Option (State → State)) : Prop :=
  ∀ n f, X n = some f → HookFsTraced IsFsC f

theorem fsTHooks_none : FsTHooks fun _ => none := by
  intro _ _ h
  cases h

/-- A table given by a list of rows, each `HookFsTraced IsFsC`. -/
theorem fsTHooks_lookup {L : List (String × (State → State))}
    (hL : ∀ p ∈ L, HookFsTraced IsFsC p.2) : FsTHooks fun n => L.lookup n := by
  intro n f h
  induction L with
  | nil => cases h
  | cons p L ih =>
    obtain ⟨m, g⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · cases h
      exact hL _ List.mem_cons_self
    · exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) h

/-- `E2E.withImagePanics` keeps a table traced (`Rust.panicked` is). -/
theorem fsTHooks_withPanicsE {X : String → Option (State → State)} (hX : FsTHooks X) :
    FsTHooks (E2E.withImagePanics X) := by
  intro n f h
  unfold E2E.withImagePanics at h
  split at h
  · cases h
    exact panicked_fsT
  · exact hX n f h

/-- `withCliPanics` keeps a table traced (`Rust.panicked` is). -/
theorem fsTHooks_withCliPanics {X : String → Option (State → State)} (hX : FsTHooks X) :
    FsTHooks (withCliPanics X) := by
  intro n f h
  unfold withCliPanics at h
  split at h
  · cases h
    exact panicked_fsT
  · exact hX n f h

/-- `Rust.withPanics` keeps a table traced. -/
theorem fsTHooks_withPanics {X : String → Option (State → State)} (hX : FsTHooks X) :
    FsTHooks (Rust.withPanics X) := by
  intro n f h
  unfold Rust.withPanics at h
  split at h
  · cases h
    exact panicked_fsT
  · exact hX n f h

/-- Every extern hook of `cliExterns W` satisfies `HookFsTraced IsFsC`. -/
theorem fsTHooks_cliExterns (W : CliHooks) : FsTHooks (cliExterns W) :=
  fsTHooks_withCliPanics (fsTHooks_lookup (cliHookTable_fsT W))

/-- The hook at any PC of a program whose externs and overrides are traced is traced. -/
theorem fsT_externAt {P : Program} (hX : FsTHooks P.externs) (hO : FsTHooks P.overrides)
    {pc : BitVec 64} {f : State → State} (h : P.externAt? pc = some f) :
    HookFsTraced IsFsC f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hX n f hno
    · cases hno
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hO n f hno
    · cases hno

/-- `TraceFsSound` of a program whose externs and overrides are traced. -/
theorem traceFsSound_of_fsTHooks {P : Program} (hX : FsTHooks P.externs)
    (hO : FsTHooks P.overrides) (hsvc : P.svc = Syscall.standard := by rfl) : TraceFsSound P :=
  TraceFsSound.of_isFs isFsC_not_quiet fun _ _ hst =>
    Steps.files_eq_of_noFs (fun _ h => h) (fun _ _ h => fsT_externAt hX hO h) hst hsvc

/-- `TraceFsSound` at `cliExterns W` for arbitrary base address `b`. -/
theorem traceFsSound_cli (W : CliHooks) (b : BitVec 64) :
    TraceFsSound (LibsignalTripleRatchet.tripleRatchetProgAtExt b (cliExterns W)) :=
  traceFsSound_of_fsTHooks (fsTHooks_withPanics (fsTHooks_cliExterns W)) fsTHooks_none

/-- `TraceFsSound` for `mProg img (cliExterns W)`. -/
theorem traceFsSound_mProg (W : CliHooks) (img : Obj.Image) :
    TraceFsSound (MainHops.mProg img (cliExterns W)) :=
  traceFsSound_cli W img.base

/-- `TraceFsSound` for `cliProg W`. -/
theorem traceFsSound_cliProg (W : CliHooks) :
    TraceFsSound (CryptoVerification.SignalSession.cliProg W) :=
  traceFsSound_of_fsTHooks (fsTHooks_cliExterns W) fsTHooks_none

/-! ## Contract-backed `TraceFsSound` (`CliExternsOk.fsTraced`) -/

/-- `CliExternsOk.fsTraced` is definitionally `FsTHooks ext`. -/
theorem fsTHooks_of_ok {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    FsTHooks ext :=
  hOk.fsTraced

theorem fsTHooks_of_externsOk {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    FsTHooks ext :=
  hOk.fsTraced

/-- Every hook of `cliExternsWith ext` is `HookFsTraced IsFsC`. -/
theorem fsTHooks_cliExternsWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    FsTHooks (cliExternsWith ext) :=
  fsTHooks_withCliPanics hOk.fsTraced

/-- `abortOnPanic` preserves `HookFsTraced IsFsC` (it only maps `.Panicked` status to
`.Signaled 6`, leaving `trace` and `fs` untouched). -/
theorem abortOnPanic_fsT {f : State → State} (hf : HookFsTraced IsFsC f) :
    HookFsTraced IsFsC (abortOnPanic f) := by
  intro s
  unfold abortOnPanic
  dsimp only
  split
  · rcases hf s with ⟨δ, htr, hfs⟩
    exact ⟨δ, htr, hfs⟩
  · exact hf s

/-- Every hook of `cliExternsSigWith ext` is `HookFsTraced IsFsC`. -/
theorem fsTHooks_cliExternsSigWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    FsTHooks (cliExternsSigWith ext) := by
  intro n g hg
  simp only [cliExternsSigWith, Option.map_eq_some_iff] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  exact abortOnPanic_fsT (fsTHooks_cliExternsWith hOk n f hf)

/-- `TraceFsSound (tripleRatchetProgAtExt b ext)` from `hOk.fsTraced`. -/
theorem traceFsSound_of_ok {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    TraceFsSound (LibsignalTripleRatchet.tripleRatchetProgAtExt b ext) :=
  traceFsSound_of_fsTHooks (fsTHooks_withPanics hOk.fsTraced) fsTHooks_none

/-- `TraceFsSound` at `cliExternsWith ext` from `hOk.fsTraced`. -/
theorem traceFsSound_cliExternsWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    TraceFsSound (LibsignalTripleRatchet.tripleRatchetProgAtExt b (cliExternsWith ext)) :=
  traceFsSound_of_fsTHooks (fsTHooks_withPanics (fsTHooks_cliExternsWith hOk)) fsTHooks_none

theorem traceFsSound_of_externsOk {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (b : BitVec 64) :
    TraceFsSound (LibsignalTripleRatchet.tripleRatchetProgAtExt b (cliExternsWith ext)) :=
  traceFsSound_cliExternsWith hOk b

/-- `TraceFsSound` for `MainHops.mProg img (cliExternsWith ext)`. -/
theorem traceFsSound_mProg_cliExternsWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    TraceFsSound (MainHops.mProg img (cliExternsWith ext)) :=
  traceFsSound_cliExternsWith hOk img.base

/-- `TraceFsSound` for `libsignalSessionImage.toProgram.rebase cliBase (cliExternsWith ext)`. -/
theorem traceFsSound_cliProgWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    TraceFsSound (libsignalSessionImage.toProgram.rebase cliBase (cliExternsWith ext)) :=
  traceFsSound_of_fsTHooks (fsTHooks_cliExternsWith hOk) fsTHooks_none

/-- `TraceFsSound` for `cliProgAbortOnPanicUnderExterns ext`. -/
theorem traceFsSound_cliProgSigWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    TraceFsSound (cliProgAbortOnPanicUnderExterns ext) :=
  traceFsSound_of_fsTHooks (fsTHooks_cliExternsSigWith hOk) fsTHooks_none

/-! ## Contract-backed `fsKept` (`CliExternsOk.fsKept`) -/

/-- Every non-I/O hook in `X` leaves the entire `State.fs` unchanged. -/
def FsKept (X : String → Option (State → State)) : Prop :=
  ∀ n f, X n = some f → n ∉ CliExt.ioNames → ∀ s, (f s).fs = s.fs

/-- `Rust.panicked` leaves `State.fs` unchanged. -/
theorem panicked_fs : ∀ s, (Rust.panicked s).fs = s.fs := fun _ => rfl

/-- `abortOnPanic` preserves `fs` invariance. -/
theorem abortOnPanic_fs {f : State → State} (hf : ∀ s, (f s).fs = s.fs) :
    ∀ s : State, (abortOnPanic f s).fs = s.fs := by
  intro s
  unfold abortOnPanic
  dsimp only
  split <;> exact hf s

/-- `CliExternsOk.fsKept` is definitionally `FsKept ext`. -/
theorem fsKept_of_ok {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    FsKept ext :=
  hOk.fsKept

/-- `E2E.withImagePanics` preserves `FsKept`. -/
theorem fsKept_withPanicsE {X : String → Option (State → State)} (hX : FsKept X) :
    FsKept (E2E.withImagePanics X) := by
  intro n f h hn s
  unfold E2E.withImagePanics at h
  split at h
  · cases h
    exact panicked_fs s
  · exact hX n f h hn s

/-- `withCliPanics` preserves `FsKept`. -/
theorem fsKept_withCliPanics {X : String → Option (State → State)} (hX : FsKept X) :
    FsKept (withCliPanics X) := by
  intro n f h hn s
  unfold withCliPanics at h
  split at h
  · cases h
    exact panicked_fs s
  · exact hX n f h hn s

/-- `Rust.withPanics` preserves `FsKept`. -/
theorem fsKept_withPanics {X : String → Option (State → State)} (hX : FsKept X) :
    FsKept (Rust.withPanics X) := by
  intro n f h hn s
  unfold Rust.withPanics at h
  split at h
  · cases h
    exact panicked_fs s
  · exact hX n f h hn s

/-- Every non-I/O hook of `cliExternsWith ext` leaves `State.fs` unchanged. -/
theorem fsKept_cliExternsWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    FsKept (cliExternsWith ext) :=
  fsKept_withCliPanics hOk.fsKept

/-- Every non-I/O hook of `cliExternsSigWith ext` leaves `State.fs` unchanged. -/
theorem fsKept_cliExternsSigWith {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    FsKept (cliExternsSigWith ext) := by
  intro n g hg hn s
  simp only [cliExternsSigWith, Option.map_eq_some_iff] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  exact abortOnPanic_fs (fsKept_cliExternsWith hOk n f hf hn) s

/-- Upgrade `HookSat X n spec` to `HookSat X n spec.keepsFs` for any `n ∉ CliExt.ioNames` under `FsKept X`. -/
theorem hookSat_keepsFs_of_fsKept {α : Type} {X : String → Option (State → State)}
    (hFs : FsKept X) {n : String} {spec : Spec α} (hn : n ∉ CliExt.ioNames)
    (hsat : HookSat X n spec) : HookSat X n spec.keepsFs := by
  obtain ⟨f, hf, hok⟩ := hsat
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  obtain ⟨hkf, hsym, hout⟩ := hok x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hFs n f hf hn s0, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Upgrade `HookSat ext n spec` to `HookSat ext n spec.keepsFs` for `n ∉ CliExt.ioNames`. -/
theorem hookSat_keepsFs_ext {α : Type} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {n : String} {spec : Spec α} (hn : n ∉ CliExt.ioNames) (hsat : HookSat ext n spec) :
    HookSat ext n spec.keepsFs :=
  hookSat_keepsFs_of_fsKept hOk.fsKept hn hsat

/-- Upgrade `HookSat (cliExternsWith ext) n spec` to `HookSat (cliExternsWith ext) n spec.keepsFs`
for `n ∉ CliExt.ioNames`. -/
theorem hookSat_keepsFs_cliExternsWith {α : Type} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    {n : String} {spec : Spec α} (hn : n ∉ CliExt.ioNames)
    (hsat : HookSat (cliExternsWith ext) n spec) :
    HookSat (cliExternsWith ext) n spec.keepsFs :=
  hookSat_keepsFs_of_fsKept (fsKept_cliExternsWith hOk) hn hsat

end CryptoVerification.SignalSession.Cli.RunGlue
