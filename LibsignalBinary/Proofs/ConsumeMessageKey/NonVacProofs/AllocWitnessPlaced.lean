/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.AllocWitness
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession.NonVacuityWitness

open Arm64 ProofLib CryptoVerification.RustHeap

/-! ## Relocatable `[LibsignalPlacement]` Allocator and Hook Witness -/

abbrev lsHandleAllocErrorSymNonVac : String :=
  "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error"

abbrev lsVecRemoveAssertFailedSymNonVac : String :=
  "_RNvMNtCs69KKACWg7bl_5alloc3vecINtB2_3VecpE6remove13assert_failed"

def witnessMemcmpHook : State → State :=
  retHook fun s =>
    let p1 := s.readReg64 .x0
    let p2 := s.readReg64 .x1
    let n := (s.readReg64 .x2).toNat
    s.writeReg64 .x0 (if s.mem.readBytes p1 n = s.mem.readBytes p2 n then 0#64 else 1#64)

/-- Witness hook table over mangled `libsignalSessionExterns` symbol names. -/
noncomputable def witnessHooksPlaced : LibsignalHooks := fun sym =>
  if sym = lsRustAllocSym then some witnessAllocHook
  else if sym = lsRustDeallocSym then some witnessDeallocHook
  else if sym = lsRustReallocSym then some witnessReallocHook
  else if sym = lsRustNoAllocShimSym then some hookNoop
  else if sym = lsBlackBoxU8Sym then some CryptoVerification.LibsignalSession.blackBoxHook
  else if sym = "memcpy" then some hookMemcpy
  else if sym = "memcmp" then some witnessMemcmpHook
  else if sym = "memset" then some hookMemset
  else if sym = "memmove" then some hookMemmove
  else if sym = lsHandleErrorSym then some Rust.panicked
  else if sym = lsHandleAllocErrorSymNonVac then some Rust.panicked
  else if sym = lsVecRemoveAssertFailedSymNonVac then some Rust.panicked
  else if sym = cmkExpectFailedSym then some Rust.panicked
  else if sym = cmkPanicAddOverflowSym then some Rust.panicked
  else if Rust.isPanicSymbol sym then some Rust.panicked
  else none

/-- Placed counterpart of `AllocSucceedsWithRoom`. -/
def AllocSucceedsWithRoomPlaced (A : RustAlloc) (hooks : LibsignalHooks) : Prop :=
  (∀ f, hooks lsRustAllocSym = some f →
    ∀ size align R (s : State), s.status = .Running → s.spAligned = true →
      (s.mem ⊨ (rustAllocSpec A).pre (size, align) s ∗ R) →
      (∃ p : BitVec 64, p ≠ 0 ∧ p.toNat % align = 0 ∧ Unmapped s.mem p size) →
      (f s).readReg64 .x0 ≠ 0) ∧
  (∀ f, hooks lsRustReallocSym = some f →
    ∀ p old align new bs R (s : State), s.status = .Running → s.spAligned = true →
      (s.mem ⊨ (rustReallocSpec A).pre (p, old, align, new, bs) s ∗ R) →
      (∃ q : BitVec 64, q ≠ 0 ∧ q.toNat % align = 0 ∧ Unmapped s.mem q new) →
      (f s).readReg64 .x0 ≠ 0)

theorem witnessHooksPlaced_rustAlloc :
    HookSat witnessHooksPlaced lsRustAllocSym (rustAllocSpec A₀) :=
  ⟨witnessAllocHook, rfl, witnessAllocHook_ok⟩

theorem witnessHooksPlaced_rustDealloc :
    HookSat witnessHooksPlaced lsRustDeallocSym (rustDeallocSpec A₀) :=
  ⟨witnessDeallocHook, rfl, witnessDeallocHook_ok⟩

theorem witnessHooksPlaced_rustRealloc :
    HookSat witnessHooksPlaced lsRustReallocSym (rustReallocSpec A₀) :=
  ⟨witnessReallocHook, rfl, witnessReallocHook_ok⟩

theorem witnessHooksPlaced_noAllocShim :
    HookSat witnessHooksPlaced lsRustNoAllocShimSym LibsignalTripleRatchet.noAllocShimSpec :=
  ⟨hookNoop, rfl, LibsignalTripleRatchet.noAllocShim_hookOk⟩

theorem witnessHooksPlaced_cmkShim :
    HookSat witnessHooksPlaced cmkRustNoAllocShimSym cmkShimSpec := by
  refine ⟨hookNoop, rfl, hookNoop_ok fun _ R s0 hpre => ?_⟩
  dsimp only [cmkShimSpec] at hpre ⊢
  rw [emp_sepConj] at hpre
  rw [satisfies_pure_sepConj]
  exact ⟨rfl, hpre⟩

theorem witnessHooksPlaced_blackBox :
    witnessHooksPlaced lsBlackBoxU8Sym = some CryptoVerification.LibsignalSession.blackBoxHook :=
  rfl

theorem witnessHooksPlaced_noAllocShim_eq :
    witnessHooksPlaced lsRustNoAllocShimSym = some hookNoop :=
  rfl

theorem witnessHooksPlaced_memcpy_eq :
    witnessHooksPlaced "memcpy" = some hookMemcpy :=
  rfl

theorem witnessHooksPlaced_memcmp_eq :
    witnessHooksPlaced "memcmp" = some witnessMemcmpHook :=
  rfl

theorem witnessHooksPlaced_memset_eq :
    witnessHooksPlaced "memset" = some hookMemset :=
  rfl

theorem witnessHooksPlaced_memmove_eq :
    witnessHooksPlaced "memmove" = some hookMemmove :=
  rfl

theorem witnessHooksPlaced_handleError_eq :
    witnessHooksPlaced lsHandleErrorSym = some Rust.panicked :=
  rfl

theorem witnessHooksPlaced_handleAllocError_eq :
    witnessHooksPlaced lsHandleAllocErrorSymNonVac = some Rust.panicked :=
  rfl

theorem witnessHooksPlaced_cmkAllocHooks :
    CmkAllocHooks A₀ witnessHooksPlaced :=
  ⟨witnessHooksPlaced_rustAlloc, witnessHooksPlaced_rustDealloc, witnessHooksPlaced_cmkShim,
    rfl, rfl, rfl⟩

theorem witnessHooksPlaced_succeedsWithRoom :
    AllocSucceedsWithRoomPlaced A₀ witnessHooksPlaced := by
  refine ⟨?_, ?_⟩
  · intro f hf size align R s _hrun _hsp hpre hroom
    have hf' : witnessAllocHook = f := by
      simpa [witnessHooksPlaced, lsRustAllocSym] using hf
    subst hf'
    simp only [rustAllocSpec, A₀, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, _⟩, _⟩
    have hroom' : HasRoom s.mem (s.readReg64 .x0).toNat (s.readReg64 .x1).toNat := by
      rw [hx0, hx1]; exact hroom
    simp only [witnessAllocHook, retHook, allocBody, hroom', ↓reduceDIte,
      readReg64_setPC_writeReg64_x0]
    exact (Classical.choose_spec hroom').1
  · intro f hf p old align new bs R s _hrun _hsp hpre hroom
    have hf' : witnessReallocHook = f := by
      simpa [witnessHooksPlaced, lsRustReallocSym, lsRustAllocSym, lsRustDeallocSym] using hf
    subst hf'
    simp only [rustReallocSpec, A₀, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, _, hx2, hx3, _⟩, _⟩
    have hroom' : HasRoom s.mem (s.readReg64 .x3).toNat (s.readReg64 .x2).toNat := by
      rw [hx2, hx3]; exact hroom
    simp only [witnessReallocHook, retHook, reallocBody, hroom', ↓reduceDIte,
      readReg64_setPC_writeReg64_x0]
    exact (Classical.choose_spec hroom').1

end CryptoVerification.LibsignalSession.NonVacuityWitness
