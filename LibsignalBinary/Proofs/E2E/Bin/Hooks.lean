/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.HooksNames
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Defs
public import LibsignalBinary.Proofs.E2E.Record.Support.Hooks

/-!
# Shared Hook Contracts for the E2E Wrapper Binary

Extends `PublicApiHooksNoStores` and `HashbrownBinHooks` with the external hooks reached by
`libsignal_e2e` (`open`, `session_send`, `session_recv`) and its in-memory stores:
`bcmp` (`0x51b50`) and `hashmap_random_keys` (`0x51b3c`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
export CryptoVerification.E2E (bcmpName randomKeysName)

/-- Ghost state for a `bcmp(a = x0, b = x1, n = x2)` call on two byte slices of equal length `n`. -/
structure BcmpCall where
  a : BitVec 64
  b : BitVec 64
  bsA : List (BitVec 8)
  bsB : List (BitVec 8)

/-- `bcmp(a = x0, b = x1, n = x2) -> w0`: compares `n` bytes at `a` and `b` without modifying them;
    returns `w0 = 0` iff `bsA = bsB`. -/
def e2eBcmpSpec : Spec BcmpCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ s.readReg64 .x1 = x.b ∧
      (s.readReg64 .x2).toNat = x.bsA.length ∧ x.bsB.length = x.bsA.length⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 32 = 0#32 ↔ x.bsA = x.bsB) ∧ sf.trace = s0.trace⌝ ∗
      (x.a ↦ₛ x.bsA) ∗ (x.b ↦ₛ x.bsB) ∗ stackAt s0.sp extHookStack

/-- `RandomState::new` key-generation hook (`x0, x1` returned as two `u64` SipHash keys;
    no constraint on `x0`/`x1` in the postcondition so any deterministic hook satisfies `HookOk`). -/
def randomKeysSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp extHookStack

def witnessBcmpHook : State → State :=
  retHook fun s =>
    let n := (s.readReg64 .x2).toNat
    let bsA := s.mem.readBytes (s.readReg64 .x0) n
    let bsB := s.mem.readBytes (s.readReg64 .x1) n
    s.writeReg64 .x0 (if bsA = bsB then 0#64 else 1#64)

theorem randomKeysSpec_nonvac : HookOk hookNoop randomKeysSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  simp only [randomKeysSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨rfl, hpre⟩

theorem e2eBcmpSpec_nonvac : HookOk witnessBcmpHook e2eBcmpSpec := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  simp only [e2eBcmpSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hrA : s0.mem.readBytes x.a x.bsA.length = x.bsA :=
    ((IsBlock.pointsToBytes x.a x.bsA).read hmem).2
  have hmemB : s0.mem ⊨ (x.b ↦ₛ x.bsB) ∗ ((x.a ↦ₛ x.bsA) ∗ (stackAt s0.sp extHookStack ∗ R)) := by
    have heq :
        ((x.a ↦ₛ x.bsA) ∗ ((x.b ↦ₛ x.bsB) ∗ (stackAt s0.sp extHookStack ∗ R))) =
        ((x.b ↦ₛ x.bsB) ∗ ((x.a ↦ₛ x.bsA) ∗ (stackAt s0.sp extHookStack ∗ R))) := by ac_rfl
    exact heq ▸ hmem
  have hrB : s0.mem.readBytes x.b x.bsA.length = x.bsB := by
    rw [← hlen]
    exact ((IsBlock.pointsToBytes x.b x.bsB).read hmemB).2
  unfold retHook
  dsimp only
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [e2eBcmpSpec]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, rfl⟩, hmem⟩
  rw [hx0, hx1, hx2, hrA, hrB]
  by_cases h : x.bsA = x.bsB <;> simp [h, State.setPC, State.writeReg64, State.readReg64]

/-- Shared hook bundle for the E2E wrapper binary: `PublicApiHooksNoStores` extended with `bcmp`,
`randomKeys`, `HashbrownBinHooks`, `S.SendEmptyOk`, `A = Record.A0`, and `tpidrSafe`. -/
structure BinHooks (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop extends PublicApiHooksNoStores C A S abs where
  bcmp : HookSat abs bcmpName e2eBcmpSpec
  randomKeys : HookSat abs randomKeysName randomKeysSpec
  hashbrownBin : ∀ ctl,
    CryptoVerification.E2E.InMem.HashbrownBin.HashbrownBinHooks A (Rust.withPanics (tripleRatchetExterns C ctl abs))
  emptyOk : S.SendEmptyOk
  alloc_eq : A = CryptoVerification.E2E.Record.A0
  tpidrSafe : ∀ n f, abs n = some f → ∀ s,
    (f s).tpidrEl0 = s.tpidrEl0 ∧ ∀ a, ((f s).mem.perm a).x → (s.mem.perm a).x

end CryptoVerification.E2E.Bin
