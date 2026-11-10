/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import ProofLib.ProgramReflection.Variant.TrapTransfer

/-!
# Trap-at-RNG Program Variant (`trTrapProgAt`)

Defines `trTrapProgAt b C abs`, replacing the `libsignal_session_rng_fill` stub of
`tripleRatchetProgAt b C ctl abs` with an unconditional exception trap (`rngTrap`), eliminating the
`ctl` parameter on paths that never invoke RNG fill. Because `TrapsOnly (trTrapProgAt b C abs)
(tripleRatchetProgAt b C ctl abs)` holds for every `ctl`, any `subroutine_ok` proved on `trTrapProgAt`
transfers immediately to `tripleRatchetProgAt` (`subroutine_ok_kit_of_trTrap`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.Variant CryptoGames.LibsignalSession

/-- The trap the rng stub gets: an `.Exception` (never an `OutcomeStatus`). -/
def rngTrap (s : State) : State := { s with status := .Exception "rng_fill: unreachable" }

theorem rngTrap_isTrap : IsTrap rngTrap := by
  intro s
  exact not_outcomeStatus_exception _

/-- The kit externs with `libsignal_session_rng_fill` trapping (`ctl` is irrelevant: only the rng
row uses it). -/
def trTrapExterns (C : Crypto) (abs : String → Option (State → State)) :
    String → Option (State → State) :=
  trapAt (· == rngFillName) rngTrap (tripleRatchetExterns C 0#64 abs)

/-- Session program rebased at `b` with `libsignal_session_rng_fill` trapping. -/
noncomputable abbrev trTrapProgAt (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (trTrapExterns C abs))

/-- The names `tripleRatchetExterns` answers itself, other than the rng stub (the rows of
`sessionExterns` other than the allocator, dh / pubFromSecret / the two drops, `noHookNames`).
Every other name goes to `abs`. -/
def kitOwnNames : List String :=
  ["sha2::sha256::compress256", "memcpy", "memmove", "memset",
   "__rustc::__rust_no_alloc_shim_is_unstable_v2", "subtle::black_box::<u8>",
   "<alloc::vec::Vec<_, _>>::remove::assert_failed",
   dhName, pubFromSecretName, staticDropName, sharedDropName,
   "__aarch64_ldadd8_rel", "__aarch64_ldadd8_relax", "__aarch64_cas8_acq_rel",
   "<log::__private_api::GlobalLogger as log::Log>::log"]

/-- Away from `kitOwnNames` and the rng stub, `tripleRatchetExterns` is `abs` (the allocator
names too: `sessionExterns` runs with no allocator here). -/
theorem tripleRatchetExterns_of_not_mem (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) {n : String} (hk : n ∉ kitOwnNames)
    (hr : n ≠ rngFillName) : tripleRatchetExterns C ctl abs n = abs n := by
  simp only [kitOwnNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hk
  have hs : CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) n = none := by
    simp [CryptoVerification.LibsignalSession.sessionExterns, h1, h2, h3, h4, h5, h6, h7]
  simp [tripleRatchetExterns, hs, h8, h9, h10, h11, hr, noHookNames, h12, h13, h14, h15]

/-- `ctl` only matters at the rng stub. -/
theorem tripleRatchetExterns_ctl (C : Crypto) (ctl ctl' : BitVec 64)
    (abs : String → Option (State → State)) {n : String} (hr : n ≠ rngFillName) :
    tripleRatchetExterns C ctl abs n = tripleRatchetExterns C ctl' abs n := by
  unfold tripleRatchetExterns
  split <;> simp [*]

/-- Away from the rng stub, the panic-wrapped trap-at-rng externs are the panic-wrapped kit
externs. -/
theorem withPanics_trTrap_ne (C : Crypto) (abs : String → Option (State → State)) {n : String}
    (hr : n ≠ rngFillName) :
    Rust.withPanics (trTrapExterns C abs) n = Rust.withPanics (tripleRatchetExterns C 0#64 abs) n := by
  have hb : (n == rngFillName) = false := beq_false_of_ne hr
  simp only [Rust.withPanics, trTrapExterns, ProofLib.Variant.trapAt, hb, Bool.false_eq_true,
    ↓reduceIte]

/-- `trTrapProgAt` refines `tripleRatchetProgAt` via `TrapsOnly` for every `ctl`. -/
theorem trapsOnly_trTrap_kit (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    TrapsOnly (trTrapProgAt b C abs) (tripleRatchetProgAt b C ctl abs) := by
  refine TrapsOnly.rebase libsignalSessionCode b ?_
  intro n
  by_cases hr : n = rngFillName
  · subst hr
    by_cases hp : Rust.isPanicSymbol rngFillName = true
    · left; simp [Rust.withPanics, hp]
    · right
      refine ⟨rngTrap, ?_, rngTrap_isTrap⟩
      simp [Rust.withPanics, trTrapExterns, ProofLib.Variant.trapAt, hp]
  · left
    rw [withPanics_trTrap_ne C abs hr]
    simp only [Rust.withPanics, tripleRatchetExterns_ctl C 0#64 ctl abs hr]

/-- Transfers `subroutine_ok` from `trTrapProgAt` to `tripleRatchetProgAt` for arbitrary `ctl`. -/
theorem subroutine_ok_kit_of_trTrap {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok (trTrapProgAt b C abs) entry spec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) entry spec :=
  subroutine_ok.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

/-- Away from `rngFillName`, `trTrapExterns` agrees with `tripleRatchetExterns` for any `ctl`. -/
theorem trTrapExterns_eq_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) {n : String} (hr : n ≠ rngFillName) :
    trTrapExterns C abs n = tripleRatchetExterns C ctl abs n := by
  have hb : (n == rngFillName) = false := beq_false_of_ne hr
  simp only [trTrapExterns, ProofLib.Variant.trapAt, hb, Bool.false_eq_true, ↓reduceIte]
  exact tripleRatchetExterns_ctl C 0#64 ctl abs hr

/-- Away from `kitOwnNames` and `rngFillName`, `trTrapExterns` passes straight through to `abs`. -/
theorem trTrapExterns_of_not_mem (C : Crypto) (abs : String → Option (State → State))
    {n : String} (hk : n ∉ kitOwnNames) (hr : n ≠ rngFillName) :
    trTrapExterns C abs n = abs n := by
  rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 abs hr]
  exact tripleRatchetExterns_of_not_mem C 0#64 abs hk hr

/-- Away from `rngFillName`, the panic-wrapped trap-at-rng externs agree with the kit externs for
any `ctl`. -/
theorem withPanics_trTrap_eq_kit (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) {n : String} (hr : n ≠ rngFillName) :
    Rust.withPanics (trTrapExterns C abs) n = Rust.withPanics (tripleRatchetExterns C ctl abs) n := by
  rw [withPanics_trTrap_ne C abs hr]
  simp only [Rust.withPanics, tripleRatchetExterns_ctl C 0#64 ctl abs hr]

/-- Lift a user `HookSat` contract on `abs` to `trTrapExterns C abs`. -/
theorem hookSat_trTrapExterns {α : Type} {C : Crypto}
    {abs : String → Option (State → State)} {sym : String} {spec : Spec α}
    (hk : sym ∉ kitOwnNames) (hr : sym ≠ rngFillName) (h : HookSat abs sym spec) :
    HookSat (trTrapExterns C abs) sym spec := by
  rcases h with ⟨fn, hfn, hok⟩
  exact ⟨fn, (trTrapExterns_of_not_mem C abs hk hr).trans hfn, hok⟩

theorem trTrapExterns_idem (C : Crypto) (abs : String → Option (State → State)) :
    trTrapExterns C (trTrapExterns C abs) = trTrapExterns C abs := by
  funext n
  by_cases hr : n = rngFillName
  · subst hr
    simp [trTrapExterns, ProofLib.Variant.trapAt]
  · rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 (trTrapExterns C abs) hr,
      trTrapExterns_eq_tripleRatchetExterns C 0#64 abs hr]
    unfold tripleRatchetExterns
    cases hse : CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) n with
    | some _ => rfl
    | none =>
      dsimp only
      split_ifs
      · rfl
      · rfl
      · rfl
      · rfl
      · rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 abs hr]
        unfold tripleRatchetExterns
        rw [hse]
        dsimp only
        split_ifs
        rfl

theorem trTrapProgAt_base_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).base = (tripleRatchetProgAt b C ctl abs).base :=
  rfl

theorem trTrapProgAt_fnOff_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) :
    (trTrapProgAt b C abs).fnOff name = (tripleRatchetProgAt b C ctl abs).fnOff name :=
  rfl

theorem trTrapProgAt_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) :
    (trTrapProgAt b C abs).fnAddr name = (tripleRatchetProgAt b C ctl abs).fnAddr name :=
  rfl

theorem trTrapProgAt_codeLoaded_iff (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (m : Memory) :
    (trTrapProgAt b C abs).CodeLoaded m ↔ (tripleRatchetProgAt b C ctl abs).CodeLoaded m := by
  simp only [Program.codeLoaded_iff]
  rfl

theorem raw_subroutine_ok_kit_of_trTrap {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64} {spec : Spec α}
    (h : raw_subroutine_ok (trTrapProgAt b C abs) entry spec) :
    raw_subroutine_ok (tripleRatchetProgAt b C ctl abs) entry spec :=
  raw_subroutine_ok.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem code_ok_kit_of_trTrap {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry exit : BitVec 64} {spec : Spec α}
    (h : code_ok (trTrapProgAt b C abs) entry exit spec) :
    code_ok (tripleRatchetProgAt b C ctl abs) entry exit spec :=
  code_ok.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem exit_ok_kit_of_trTrap {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry : BitVec 64} {code : α → BitVec 64}
    {spec : Spec α} (h : exit_ok (trTrapProgAt b C abs) entry code spec) :
    exit_ok (tripleRatchetProgAt b C ctl abs) entry code spec :=
  exit_ok.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem Steps_kit_of_trTrap {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {s sf : State}
    (h : Steps (trTrapProgAt b C abs) s sf) (hout : OutcomeStatus sf.status) :
    Steps (tripleRatchetProgAt b C ctl abs) s sf :=
  Steps.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h hout

theorem reaches_outcome_kit_of_trTrap {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {spec : Spec α} {x : α} {R : SepProp} {s0 s : State}
    (h : reaches_outcome (trTrapProgAt b C abs) spec x R s0 s) :
    reaches_outcome (tripleRatchetProgAt b C ctl abs) spec x R s0 s :=
  reaches_outcome.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem reaches_pc_kit_of_trTrap {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {target : BitVec 64} {s0 : State}
    {post oom : State → Prop}
    (h : reaches_pc (trTrapProgAt b C abs) target s0 post oom) :
    reaches_pc (tripleRatchetProgAt b C ctl abs) target s0 post oom :=
  reaches_pc.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem exits_with_kit_of_trTrap {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {code : BitVec 64} {s0 : State}
    {post oom : State → Prop}
    (h : exits_with (trTrapProgAt b C abs) code s0 post oom) :
    exits_with (tripleRatchetProgAt b C ctl abs) code s0 post oom :=
  exits_with.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem SepWP_kit_of_trTrap {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP (trTrapProgAt b C abs) target s P post oom) :
    SepWP (tripleRatchetProgAt b C ctl abs) target s P post oom :=
  SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem SepWPp_kit_of_trTrap {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp (trTrapProgAt b C abs) ret s P Q Qp oom) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp oom :=
  SepWPp.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

/-- The image-based trap-at-rng program, matching `tripleRatchetProg`. -/
noncomputable def tripleRatchetProg_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State)) : Program :=
  Program.ofImage img (Rust.withPanics (trTrapExterns C abs))

theorem tripleRatchetProg_eq_tripleRatchetProgAt_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    tripleRatchetProg_trap img C abs = trTrapProgAt img.base C abs :=
  libsignalSessionCode_ofImage himg

theorem tripleRatchetProgAt_eq_tripleRatchetProg_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    trTrapProgAt img.base C (trTrapExterns C abs) = tripleRatchetProg_trap img C abs := by
  unfold trTrapProgAt tripleRatchetProg_trap
  rw [trTrapExterns_idem]
  exact (libsignalSessionCode_ofImage himg).symm

theorem entryOf_eq_tripleRatchetProgAt_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (name : String) :
    entryOf img name = (trTrapProgAt img.base C abs).fnAddr name := by
  unfold entryOf trTrapProgAt
  rw [libsignalSessionCode_ofImage himg, Program.fnAddr_rebase, Program.fnAddr_rebase]

theorem root_of_tripleRatchetProgAt_trap {α : Type} {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)} {name : String}
    {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : subroutine_ok (trTrapProgAt img.base C abs) ((trTrapProgAt img.base C abs).fnAddr name) spec) :
    subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img name) spec := by
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap (abs := abs) himg,
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) himg name]
  exact h

theorem trapsOnly_tripleRatchetProg_trap_kit {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    TrapsOnly (tripleRatchetProg_trap img C abs) (tripleRatchetProg img C ctl abs) := by
  rw [tripleRatchetProg_eq_tripleRatchetProgAt_trap (abs := abs) himg,
    tripleRatchetProg_eq_tripleRatchetProgAt himg]
  exact trapsOnly_trTrap_kit img.base C ctl abs

theorem subroutine_ok_prog_kit_of_trTrap {α : Type} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {entry : BitVec 64}
    {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : subroutine_ok (tripleRatchetProg_trap img C abs) entry spec) :
    subroutine_ok (tripleRatchetProg img C ctl abs) entry spec :=
  subroutine_ok.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem raw_subroutine_ok_prog_kit_of_trTrap {α : Type} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {entry : BitVec 64}
    {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : raw_subroutine_ok (tripleRatchetProg_trap img C abs) entry spec) :
    raw_subroutine_ok (tripleRatchetProg img C ctl abs) entry spec :=
  raw_subroutine_ok.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem code_ok_prog_kit_of_trTrap {α : Type} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {entry exit : BitVec 64}
    {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : code_ok (tripleRatchetProg_trap img C abs) entry exit spec) :
    code_ok (tripleRatchetProg img C ctl abs) entry exit spec :=
  code_ok.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem exit_ok_prog_kit_of_trTrap {α : Type} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {entry : BitVec 64}
    {code : α → BitVec 64} {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : exit_ok (tripleRatchetProg_trap img C abs) entry code spec) :
    exit_ok (tripleRatchetProg img C ctl abs) entry code spec :=
  exit_ok.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem Steps_prog_kit_of_trTrap {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {s sf : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (h : Steps (tripleRatchetProg_trap img C abs) s sf) (hout : OutcomeStatus sf.status) :
    Steps (tripleRatchetProg img C ctl abs) s sf :=
  Steps.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h hout

theorem reaches_outcome_prog_kit_of_trTrap {α : Type} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {spec : Spec α} {x : α}
    {R : SepProp} {s0 s : State} (himg : Obj.Loads libsignalSessionImage img)
    (h : reaches_outcome (tripleRatchetProg_trap img C abs) spec x R s0 s) :
    reaches_outcome (tripleRatchetProg img C ctl abs) spec x R s0 s :=
  reaches_outcome.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem reaches_pc_prog_kit_of_trTrap {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {target : BitVec 64} {s0 : State}
    {post oom : State → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (h : reaches_pc (tripleRatchetProg_trap img C abs) target s0 post oom) :
    reaches_pc (tripleRatchetProg img C ctl abs) target s0 post oom :=
  reaches_pc.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem exits_with_prog_kit_of_trTrap {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {code : BitVec 64} {s0 : State}
    {post oom : State → Prop} (himg : Obj.Loads libsignalSessionImage img)
    (h : exits_with (tripleRatchetProg_trap img C abs) code s0 post oom) :
    exits_with (tripleRatchetProg img C ctl abs) code s0 post oom :=
  exits_with.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem SepWP_prog_kit_of_trTrap {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (h : SepWP (tripleRatchetProg_trap img C abs) target s P post oom) :
    SepWP (tripleRatchetProg img C ctl abs) target s P post oom :=
  SepWP.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem SepWPp_prog_kit_of_trTrap {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    (h : SepWPp (tripleRatchetProg_trap img C abs) ret s P Q Qp oom) :
    SepWPp (tripleRatchetProg img C ctl abs) ret s P Q Qp oom :=
  SepWPp.of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

theorem region_ok_of_trapsOnly {P₁ P₂ : Program} (hT : TrapsOnly P₁ P₂) {α : Type}
    {entry exit : BitVec 64} {spec : Spec α} (h : region_ok P₁ entry exit spec) :
    region_ok P₂ entry exit spec := by
  intro x R s0 hpc hrun hpre hL
  obtain ⟨sf, hs, hout⟩ := h x R s0 hpc hrun hpre (CodeLoaded_of_trapsOnly hT hL)
  refine ⟨sf, Steps.of_trapsOnly hT hs ?_, hout⟩
  rcases hout with ⟨_, hr, _⟩ | ⟨hp, _⟩
  · exact .of_running hr
  · exact .of_panicked hp

theorem region_ok_kit_of_trTrap {α : Type} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {entry exit : BitVec 64} {spec : Spec α}
    (h : region_ok (trTrapProgAt b C abs) entry exit spec) :
    region_ok (tripleRatchetProgAt b C ctl abs) entry exit spec :=
  region_ok_of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) h

theorem region_ok_prog_kit_of_trTrap {α : Type} {img : Obj.Image} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)} {entry exit : BitVec 64}
    {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : region_ok (tripleRatchetProg_trap img C abs) entry exit spec) :
    region_ok (tripleRatchetProg img C ctl abs) entry exit spec :=
  region_ok_of_trapsOnly (trapsOnly_tripleRatchetProg_trap_kit himg) h

end CryptoVerification.LibsignalTripleRatchet
