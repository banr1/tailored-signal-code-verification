/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.MuslMemOpsRunsToPlaced -- proof-setup: allow-public-import

/-!
# Lightweight `HookExactMemcpy` Predicate & Placed `RunsToFrom` Steppers (`HooksDehook.MemcpyExactCore`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; #1255 H3 / mc2 L0 core).
- **Overview:**
  Factors the CLI-independent `HookExactMemcpy` / `HookSatExactMemcpy` definitions, `hookMemcpy` /
  `memcpyHook` exactness witnesses, and placed `RunsToFrom` step wrappers
  (`s2_memcpy_step_placed_of_exact`, `placed_memcpy_step_of_exact`) out of
  `HooksDehook.MemcpyGhostExact` so `CommonSat`, `DefsSat`, and downstream `*Sat` modules can
  `public import` them without pulling in the 601-module `MemcpyGhostReplaysOn` CLI/allocator
  `@[simp, arm64_norm]` environment. `HooksDehook.MemcpyGhostExact` re-exports all declarations
  from this module.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore

open Arm64 ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsρ
)
open CryptoVerification.LibsignalAesCbc (memcpyHook)
open CryptoVerification.LibsignalTripleRatchet (lsMemcpySym ls_externAt?_of_mem)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (MemcpyClobber applyMemcpyClobber)

/-! ## 1. `HookExactMemcpy` & `HookSatExactMemcpy` -/

/-- Pointwise exactness predicate for a `memcpy` hook `f`: under the standard `memcpy(dst, src, len)`
    register, alignment (`u.spAligned = true`), `RW`/`Readable`, and non-overlap (`len = 0 ∨
    DisjointRegions dst len src len`) preconditions, `f u` equals
    `applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c` for some `c : MemcpyClobber`
    (`{x1..x17, pstate}`). -/
@[expose] def HookExactMemcpy (f : State → State) : Prop :=
  ∀ {u : State} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)},
    u.status = .Running →
    u.spAligned = true →
    u.readReg64 .x0 = dst →
    u.readReg64 .x1 = src →
    (u.readReg64 .x2).toNat = len →
    u.readReg64 .lr = lr →
    u.mem.readBytes src len = bs →
    u.mem.RW dst len →
    u.mem.Readable src len →
    (len = 0 ∨ DisjointRegions dst len src len) →
    ∃ c : MemcpyClobber, f u = applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c

/-- Extern-map witness that `H name` resolves to a `HookExactMemcpy` function. -/
@[expose] def HookSatExactMemcpy (H : String → Option (State → State)) (name : String) : Prop :=
  ∃ f, H name = some f ∧ HookExactMemcpy f

theorem hookSatExactMemcpy_of_eq {H : String → Option (State → State)} {name : String}
    {f : State → State} (hh : H name = some f) (hex : HookExactMemcpy f) :
    HookSatExactMemcpy H name :=
  ⟨f, hh, hex⟩

/-! ## 2. Fallback Exactness (`hookMemcpy` / `memcpyHook`) -/

/-- `applyMemcpyClobber` at `c := MemcpyClobber.ofState u` writes back `u`'s own `{x1..x17, pstate}`
    and reduces to `(u.setMem m').setPC pc'`. -/
theorem applyMemcpyClobber_ofState_eq (u : State) (m' : Memory) (pc' : BitVec 64) :
    applyMemcpyClobber u m' pc' (MemcpyClobber.ofState u) = (u.setMem m').setPC pc' := by
  cases u
  dsimp only [applyMemcpyClobber, MemcpyClobber.ofState, State.writeReg64, State.setPState,
    State.setMem, State.setPC]
  simp only [State.mk.injEq, RegFile.ext_iff, and_true]
  funext idx
  dsimp only [RegFile.write]
  by_cases h1 : idx = 17#5; · subst h1; rfl
  by_cases h2 : idx = 16#5; · subst h2; simp [h1]
  by_cases h3 : idx = 15#5; · subst h3; simp [h1, h2]
  by_cases h4 : idx = 14#5; · subst h4; simp [h1, h2, h3]
  by_cases h5 : idx = 13#5; · subst h5; simp [h1, h2, h3, h4]
  by_cases h6 : idx = 12#5; · subst h6; simp [h1, h2, h3, h4, h5]
  by_cases h7 : idx = 11#5; · subst h7; simp [h1, h2, h3, h4, h5, h6]
  by_cases h8 : idx = 10#5; · subst h8; simp [h1, h2, h3, h4, h5, h6, h7]
  by_cases h9 : idx = 9#5; · subst h9; simp [h1, h2, h3, h4, h5, h6, h7, h8]
  by_cases h10 : idx = 8#5; · subst h10; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  by_cases h11 : idx = 7#5; · subst h11; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  by_cases h12 : idx = 6#5; · subst h12; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  by_cases h13 : idx = 5#5; · subst h13; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  by_cases h14 : idx = 4#5; · subst h14; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  by_cases h15 : idx = 3#5; · subst h15; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  by_cases h16 : idx = 2#5; · subst h16; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  by_cases h17 : idx = 1#5; · subst h17; simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

theorem hookMemcpy_eq_applyMemcpyClobber {u : State} {dst src lr : BitVec 64} {len : Nat}
    {bs : List (BitVec 8)}
    (hx0 : u.readReg64 .x0 = dst)
    (hx1 : u.readReg64 .x1 = src)
    (hx2 : (u.readReg64 .x2).toNat = len)
    (hlr : u.readReg64 .lr = lr)
    (hread : u.mem.readBytes src len = bs) :
    hookMemcpy u = applyMemcpyClobber u (u.mem.writeBytes dst bs) lr (MemcpyClobber.ofState u) := by
  rw [applyMemcpyClobber_ofState_eq]
  simp [hookMemcpy, retHook, hx0, hx1, hx2, hlr, hread]

theorem hookMemcpy_exact : HookExactMemcpy hookMemcpy := by
  intro u dst src lr len bs _ _ hx0 hx1 hx2 hlr hread _ _ _
  exact ⟨MemcpyClobber.ofState u, hookMemcpy_eq_applyMemcpyClobber hx0 hx1 hx2 hlr hread⟩

theorem memcpyHook_exact : HookExactMemcpy memcpyHook :=
  hookMemcpy_exact

/-! ## 3. Placed `RunsToFrom` Step Wrappers (`∀ c : MemcpyClobber`) -/

/-- `HookSatExactMemcpy` counterpart to `Common.s2_memcpy_step_placed` (and drop-in twin of
    `MuslMemOpsRunsToPlaced.s2_memcpy_step_placed_stock` without `MallocngMemOpsLoaded` threading):
    steps 1 extern step at `lsρ lsMemcpySym` into `applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c`
    with exact memory `s.mem.writeBytes dst bs`. -/
theorem s2_memcpy_step_placed_of_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    (H : LibsignalHooks) [hprog : IsLsBlockProg prog i H]
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (hreadable : s.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀
        (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀ s Q := by
  obtain ⟨f, hfH, hfEx⟩ := h_mc
  obtain ⟨c, hf_eq⟩ := hfEx hrun hsp hx0 hx1 hx2 hlr hread hrw hreadable hdisj
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; exact Nat.le_of_lt (s.readReg64 .x2).isLt
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  have hkeep : s.mem.KeepsFrozen (f s).mem := by
    rw [hf_eq]; exact Memory.keepsFrozen_writeBytes bs hcan
  have hsym : (f s).symtab = s.symtab := by rw [hf_eq]; rfl
  refine CryptoVerification.LibsignalTripleRatchet.RunsTo.hook hrun hhook hkeep hsym ?_
  rw [hf_eq]
  exact h c

/-- `HookSatExactMemcpy` counterpart to `ConsumeMessageKey.HmacProofs.Defs.placed_memcpy_step`
    for `CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom`. -/
theorem placed_memcpy_step_of_exact [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hread : m₀.readBytes src len = bs)
    (hrw : m₀.RW dst len)
    (hreadable : m₀.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len)
    (h : ∀ c : MemcpyClobber,
      CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom prog s₀
        (applyMemcpyClobber s (m₀.writeBytes dst bs) lr c) P_post)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom prog s₀ s P_post := by
  obtain ⟨f, hfH, hfEx⟩ := h_mc
  obtain ⟨c, hf_eq⟩ := hfEx hrun hsp hx0 hx1 hx2 hlr
    (hmem ▸ hread) (hmem ▸ hrw) (hmem ▸ hreadable) hdisj
  rw [hmem] at hf_eq
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; exact Nat.le_of_lt (s.readReg64 .x2).isLt
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hmem, hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some f := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, hfH]
  have hkeep : s.mem.KeepsFrozen (f s).mem := by
    rw [hf_eq, ← hmem]; exact Memory.keepsFrozen_writeBytes bs hcan
  have hsym : (f s).symtab = s.symtab := by rw [hf_eq]; rfl
  refine CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.hook hrun hhook hkeep hsym ?_
  rw [hf_eq]
  exact h c

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
