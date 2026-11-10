/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.MuslMemOpsRunsTo
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Common
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs

/-!
# Placed `RunsToFrom` Step Wrappers for Stock `blk20`/`blk21` (`LibsignalBinary.Heap.MuslMemOpsRunsToPlaced`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; Plan W6 enabler, Card `S2P-B`).
- **Overview:**
  Provides drop-in stock-ELF `RunsToFrom` step lemmas replacing the 1-step hook lemmas
  `s2_memcpy_step_placed` / `s2_memset_step_placed` (`TripleRatchet/Hkdf/Common.lean`) and
  `placed_memcpy_step` / `placed_memset_step` (`ConsumeMessageKey/HmacProofs/Defs.lean`), using
  the register-exact raw-state `Steps` theorems in `LibsignalBinary.Heap.MuslMemOpsRunsTo`:
  - `blk20` (`memcpy`): exact clobber witness `c : MemcpyClobber` (`{x1..x17, pstate}`);
  - `blk21` (`memset`): exact clobber witness `c : MemsetClobber` (`{x1..x5, v0, pstate}`;
    `x6..x8` are preserved, NOT clobbered, vs the coarser `{x1..x8, v0, nzcv}` superset).
  - Threads `MallocngMemOpsLoaded mmpl` automatically across `writeBytes` / `KeepsFrozen` /
    `Expand.KeepsFrozenNoAnon`, and never hardcodes block count `619` so it applies unchanged
    on the 624-block stock ELF.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.MuslMemOpsRunsToPlaced

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries.Mallocng (mallocngBlockProg)
open CryptoGames.HMAC (ShaState)
open CryptoVerification (LibsignalPlacement lsρ LibsignalHooks)
open CryptoVerification.LibsignalTripleRatchet (lsMemcpySym lsMemsetSym lsCompress256Sym)
open CryptoVerification.LibsignalHmac (compress256Hook)
open LibsignalBinary.Heap.MuslMemOpsRunsTo

/-! ## 1. `arm64_norm` Normalization Lemmas for `setPState` and `writeVReg128` -/

-- 10 exact engine duplicates deleted (`ProofLib/Lemmas.lean:395,411,435,443` `State.{sp,mem,status,pc}_setPState`
-- and `:1744,1749,1754,1764,1819` `State.{pc,sp,mem,status,readReg64}_writeVReg128` already carry `@[simp, arm64_norm]`;
-- `ProofLib/CoreLemmas.lean:1670` `Arm64.State.readReg64_setPState` already carries `@[simp]` and gains
-- `scoped arm64_norm` below). Only the 2 `spAligned_*` public theorems are absent from `arm64-semantics`
-- and remain here under `@[scoped simp, scoped arm64_norm]`.
attribute [scoped arm64_norm] State.readReg64_setPState

@[scoped simp, scoped arm64_norm] theorem spAligned_setPState (s : State) (f : PState) :
    (s.setPState f).spAligned = s.spAligned := rfl

@[scoped simp, scoped arm64_norm] theorem spAligned_writeVReg128 (s : State) (k : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 k v).spAligned = s.spAligned := rfl

/-! ## 2. `MallocngMemOpsLoaded` & `StockMemOpsHyp` -/

/-- Both `mallocngLib` block `20` (`memcpy`) and block `21` (`memset`) are loaded in memory `m`. -/
def MallocngMemOpsLoaded (mmpl : Obj.MultiPlacement) (m : Memory) : Prop :=
  (mallocngBlockProg mmpl 20 Syscall.standard).CodeLoaded m ∧
  (mallocngBlockProg mmpl 21 Syscall.standard).CodeLoaded m

theorem MallocngMemOpsLoaded.of_keepsFrozen {mmpl : Obj.MultiPlacement} {m m' : Memory}
    (h : MallocngMemOpsLoaded mmpl m) (hkf : m.KeepsFrozen m') :
    MallocngMemOpsLoaded mmpl m' :=
  ⟨h.1.of_keepsFrozen hkf, h.2.of_keepsFrozen hkf⟩

theorem MallocngMemOpsLoaded.of_keepsFrozenNoAnon {mmpl : Obj.MultiPlacement} {m m' : Memory}
    (h : MallocngMemOpsLoaded mmpl m)
    (hkf : CryptoVerification.LibsignalTripleRatchet.Expand.KeepsFrozenNoAnon m m') :
    MallocngMemOpsLoaded mmpl m' :=
  ⟨CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h.1 hkf,
   CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h.2 hkf⟩

theorem MallocngMemOpsLoaded.writeBytes {mmpl : Obj.MultiPlacement} {m : Memory}
    {dst : BitVec 64} {bs : List (BitVec 8)}
    (h : MallocngMemOpsLoaded mmpl m) (hrw : m.RW dst bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    MallocngMemOpsLoaded mmpl (m.writeBytes dst bs) :=
  h.of_keepsFrozen (Memory.keepsFrozen_writeBytes bs (hrw.canWrite_sub (by simp) hlen))

theorem MallocngMemOpsLoaded.write8 {mmpl : Obj.MultiPlacement} {m : Memory}
    {addr : BitVec 64} {v : BitVec 8}
    (h : MallocngMemOpsLoaded mmpl m) (hcw : m.canWrite addr 1 = true) :
    MallocngMemOpsLoaded mmpl (m.write8 addr v) :=
  h.of_keepsFrozen (Memory.keepsFrozen_write8 hcw v)

theorem MallocngMemOpsLoaded.write64 {mmpl : Obj.MultiPlacement} {m : Memory}
    {addr v : BitVec 64}
    (h : MallocngMemOpsLoaded mmpl m) (hcw : m.canWrite addr 8 = true) :
    MallocngMemOpsLoaded mmpl (m.write64 addr v) :=
  h.of_keepsFrozen (Memory.keepsFrozen_write64 hcw v)

/-- Stock-ELF hook hypothesis for `compress256` alone (replacing `HkdfPlacedHooks` when `memset` and
    `memcpy` are unhooked to real `mallocngLib` blocks `21` and `20`). -/
class HkdfCompressHook (F : ShaState → List (BitVec 8) → ShaState) (H : LibsignalHooks) : Prop where
  compress256 : H lsCompress256Sym = some (compress256Hook F)

/-- Placement and block-local hook-freedom hypotheses tying `lsMemcpySym` / `lsMemsetSym` to
    `VerifiedLibraries.mallocngLib` blocks `20` and `21` on `prog` (layout-generic, block-count-generic). -/
structure StockMemOpsHyp [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (prog : Program) : Prop where
  placeable : VerifiedLibraries.mallocngLib.Placeable mmpl
  memcpy_eq : lsρ lsMemcpySym = mmpl.base 20
  memset_eq : lsρ lsMemsetSym = mmpl.base 21
  memcpy_ext_free : BlockExternFree prog (mmpl.base 20) 396
  memset_ext_free : BlockExternFree prog (mmpl.base 21) 260

/-! ## 3. Placed `RunsToFrom` Step Wrappers -/

/-- Stock-ELF `RunsToFrom` step through `memcpy` (`mallocngLib` block `20`, exact clobber
    `{x1..x17, pstate}`) for `CryptoVerification.LibsignalTripleRatchet.RunsToFrom`
    (HKDF / SPQR KDF / ResponderCore / Hashbrown consumers). -/
theorem s2_memcpy_step_placed_stock [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {prog : Program}
    (hhyp : StockMemOpsHyp mmpl prog)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hcl : MallocngMemOpsLoaded mmpl s.mem)
    (hrun : s.status = .Running)
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
      MallocngMemOpsLoaded mmpl (s.mem.writeBytes dst bs) →
      CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀
        (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c) Q) :
    CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀ s Q := by
  intro hL
  have hbs_len : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : bs.length ≤ 2 ^ 64 := by
    rw [hbs_len, ← hx2]; exact Nat.le_of_lt (s.readReg64 .x2).isLt
  obtain ⟨c, hsteps1⟩ := mallocngBlock20_memcpy_steps_exact
    hhyp.placeable hcl.1 hhyp.memcpy_ext_free hrun (hpc.trans hhyp.memcpy_eq)
    hx0 hx1 hx2 hlr hread hrw hreadable hdisj
  have hcl' : MallocngMemOpsLoaded mmpl (s.mem.writeBytes dst bs) :=
    hcl.writeBytes (hbs_len.symm ▸ hrw) hlen_le
  have hL1 : prog.CodeLoaded (applyMemcpyClobber s (s.mem.writeBytes dst bs) lr c).mem :=
    hsteps1.codeLoaded hL
  obtain ⟨s', hsteps2, htr, hQ, hL'⟩ := h c hcl' hL1
  exact ⟨s', hsteps1.trans hsteps2, htr, hQ, hL'⟩

/-- Stock-ELF `RunsToFrom` step through `memset` (`mallocngLib` block `21`, exact clobber
    `{x1..x5, v0, pstate}`; `x6..x8` preserved) for arbitrary fill byte `val : BitVec 8` in
    `CryptoVerification.LibsignalTripleRatchet.RunsToFrom`. -/
theorem s2_memset_step_placed_stock [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {prog : Program}
    (hhyp : StockMemOpsHyp mmpl prog)
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hcl : MallocngMemOpsLoaded mmpl s.mem)
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hrw : s.mem.RW dst len)
    (h : ∀ c : MemsetClobber,
      MallocngMemOpsLoaded mmpl (s.mem.writeBytes dst (List.replicate len val)) →
      CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀
        (applyMemsetClobber s (s.mem.writeBytes dst (List.replicate len val)) lr c) Q) :
    CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀ s Q := by
  intro hL
  have hlen_le : (List.replicate len val).length ≤ 2 ^ 64 := by
    rw [List.length_replicate, ← hx2]; exact Nat.le_of_lt (s.readReg64 .x2).isLt
  obtain ⟨c, hsteps1⟩ := mallocngBlock21_memset_steps_exact
    hhyp.placeable hcl.2 hhyp.memset_ext_free hrun (hpc.trans hhyp.memset_eq)
    hx0 hx1 hx2 hlr hrw
  have hcl' : MallocngMemOpsLoaded mmpl (s.mem.writeBytes dst (List.replicate len val)) :=
    hcl.writeBytes (by simpa [List.length_replicate] using hrw) hlen_le
  have hL1 : prog.CodeLoaded
      (applyMemsetClobber s (s.mem.writeBytes dst (List.replicate len val)) lr c).mem :=
    hsteps1.codeLoaded hL
  obtain ⟨s', hsteps2, htr, hQ, hL'⟩ := h c hcl' hL1
  exact ⟨s', hsteps1.trans hsteps2, htr, hQ, hL'⟩

/-- Zero-fill specialization (`val = 0#8`) matching `s2_memset_step_placed` in
    `LibsignalBinary/Proofs/TripleRatchet/Hkdf/Common.lean`. -/
theorem s2_memset_zero_step_placed_stock [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {prog : Program}
    (hhyp : StockMemOpsHyp mmpl prog)
    {s₀ s : State} {Q : State → Prop}
    {dst lr : BitVec 64} {len : Nat}
    (hcl : MallocngMemOpsLoaded mmpl s.mem)
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hrw : s.mem.RW dst len)
    (h : ∀ c : MemsetClobber,
      MallocngMemOpsLoaded mmpl (s.mem.writeBytes dst (List.replicate len 0#8)) →
      CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀
        (applyMemsetClobber s (s.mem.writeBytes dst (List.replicate len 0#8)) lr c) Q) :
    CryptoVerification.LibsignalTripleRatchet.RunsToFrom prog s₀ s Q :=
  s2_memset_step_placed_stock hhyp hcl hrun hpc hx0 hx1 hx2 hlr hrw h

/-- Stock-ELF `RunsToFrom` step through `memcpy` (`mallocngLib` block `20`, exact clobber
    `{x1..x17, pstate}`) for `CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom`
    (`ConsumeMessageKey/HmacProofs/*` consumers). -/
theorem placed_memcpy_step_stock [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {prog : Program}
    (hhyp : StockMemOpsHyp mmpl prog)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hcl : MallocngMemOpsLoaded mmpl m₀)
    (hrun : s.status = .Running)
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
      MallocngMemOpsLoaded mmpl (m₀.writeBytes dst bs) →
      CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom prog s₀
        (applyMemcpyClobber s (m₀.writeBytes dst bs) lr c) P_post) :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom prog s₀ s P_post := by
  intro hL
  have hbs_len : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : bs.length ≤ 2 ^ 64 := by
    rw [hbs_len, ← hx2]; exact Nat.le_of_lt (s.readReg64 .x2).isLt
  obtain ⟨c, hsteps1⟩ := mallocngBlock20_memcpy_steps_exact
    hhyp.placeable (hmem ▸ hcl.1) hhyp.memcpy_ext_free hrun (hpc.trans hhyp.memcpy_eq)
    hx0 hx1 hx2 hlr (hmem ▸ hread) (hmem ▸ hrw) (hmem ▸ hreadable) hdisj
  rw [hmem] at hsteps1
  have hcl' : MallocngMemOpsLoaded mmpl (m₀.writeBytes dst bs) :=
    hcl.writeBytes (hbs_len.symm ▸ hrw) hlen_le
  have hL1 : prog.CodeLoaded (applyMemcpyClobber s (m₀.writeBytes dst bs) lr c).mem :=
    hsteps1.codeLoaded hL
  obtain ⟨s', hsteps2, htr, hvregs, hP, hL'⟩ := h c hcl' hL1
  exact ⟨s', hsteps1.trans hsteps2, htr, hvregs, hP, hL'⟩

/-- Stock-ELF `RunsToFrom` step through `memset` (`mallocngLib` block `21`, exact clobber
    `{x1..x5, v0, pstate}`; `x6..x8` preserved) for
    `CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom`. -/
theorem placed_memset_step_stock [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {prog : Program}
    (hhyp : StockMemOpsHyp mmpl prog)
    {s₀ s : State} {P_post : State → Prop}
    {m₀ : Memory} {dst lr : BitVec 64} {val : BitVec 8} {len : Nat}
    (hcl : MallocngMemOpsLoaded mmpl m₀)
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemsetSym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : (s.readReg64 .x1).truncate 8 = val)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hmem : s.mem = m₀)
    (hrw : m₀.RW dst len)
    (h : ∀ c : MemsetClobber,
      MallocngMemOpsLoaded mmpl (m₀.writeBytes dst (List.replicate len val)) →
      CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom prog s₀
        (applyMemsetClobber s (m₀.writeBytes dst (List.replicate len val)) lr c) P_post) :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsToFrom prog s₀ s P_post := by
  intro hL
  have hlen_le : (List.replicate len val).length ≤ 2 ^ 64 := by
    rw [List.length_replicate, ← hx2]; exact Nat.le_of_lt (s.readReg64 .x2).isLt
  obtain ⟨c, hsteps1⟩ := mallocngBlock21_memset_steps_exact
    hhyp.placeable (hmem ▸ hcl.2) hhyp.memset_ext_free hrun (hpc.trans hhyp.memset_eq)
    hx0 hx1 hx2 hlr (hmem ▸ hrw)
  rw [hmem] at hsteps1
  have hcl' : MallocngMemOpsLoaded mmpl (m₀.writeBytes dst (List.replicate len val)) :=
    hcl.writeBytes (by simpa [List.length_replicate] using hrw) hlen_le
  have hL1 : prog.CodeLoaded
      (applyMemsetClobber s (m₀.writeBytes dst (List.replicate len val)) lr c).mem :=
    hsteps1.codeLoaded hL
  obtain ⟨s', hsteps2, htr, hvregs, hP, hL'⟩ := h c hcl' hL1
  exact ⟨s', hsteps1.trans hsteps2, htr, hvregs, hP, hL'⟩

end LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
