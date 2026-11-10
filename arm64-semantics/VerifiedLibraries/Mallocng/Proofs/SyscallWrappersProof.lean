/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Internal
public import ProofLib.SepLogic.WP.SyscallsMmap

/-!
# Syscall `SepWP` Step Rules and `MallocngMappedDelta` Lemmas

Program-generic `SepWP` syscall step rules for `munmap`, `mprotect`, `mmap`, and `mremap`,
together with `MallocngMappedDelta` preservation lemmas and `satisfies_remapRw_bytes_mapped`.
-/

@[expose] public section

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Pointwise `evalSvc`, `MallocngMappedDelta`, and Arithmetic Lemmas -/

private theorem evalSvc_eq_of_keepsFrozen {svc : State → State} {s : State}
    (hk : s.mem.KeepsFrozen (svc s).mem)
    (ht : (svc s).tpidrEl0 = s.tpidrEl0)
    (hs : (svc s).symtab = s.symtab) :
    evalSvc svc s = svc s := by
  have hmem :
      ({ cells := fun a => if (s.mem.perm a).frozen then s.mem.cells a else (svc s).mem.cells a } :
        Memory) = (svc s).mem := by
    congr 1; funext a
    by_cases hf : (s.mem.perm a).frozen = true
    · obtain ⟨hr, hp, hlf, han⟩ := hk a hf
      cases hca : s.mem.cells a with
      | none => simp [Memory.perm, hca] at hf
      | some cell =>
        rcases cell with ⟨po, b⟩
        cases po with
        | none => simp [Memory.perm, hca] at hf
        | some p =>
          cases hcb : (svc s).mem.cells a with
          | none => simp [Memory.perm, hca, hcb] at hp
          | some cell' =>
            rcases cell' with ⟨po', b'⟩
            cases po' with
            | none => simp [Memory.perm, hca, hcb] at hp
            | some p' =>
              rcases p with ⟨r, w, x, lf, an⟩
              rcases p' with ⟨r', w', x', lf', an'⟩
              simp only [Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon,
                Perm.rwx, hca, hcb] at hr hp hlf han
              injection hp with hp'
              injection hp' with hr_eq hw_eq hx_eq _ _
              subst hr hr_eq hw_eq hx_eq hlf han
              simp [hf]
    · simp [hf]
  unfold evalSvc
  dsimp only
  rw [hmem, ← ht, ← hs]

theorem evalInst_svc0_prog {prog : Program} {svc : State → State} {s : State}
    (hProgSvc : prog.svc = svc)
    (hk : s.mem.KeepsFrozen (svc s).mem)
    (ht : (svc s).tpidrEl0 = s.tpidrEl0)
    (hs : (svc s).symtab = s.symtab) :
    prog.evalInst (.system false 0#16) s = svc s := by
  rw [Arm64.Program.evalInst_svc0, hProgSvc]
  exact evalSvc_eq_of_keepsFrozen hk ht hs

theorem mappedDelta_of_perm_le {m0 mf : Memory}
    (h : ∀ a, (mf.perm a).mapped = true → (m0.perm a).mapped = true) :
    MallocngMappedDelta 0 0 m0 mf :=
  ⟨[], Nat.le_refl _, Nat.le_refl _, fun a ha => Or.inl (h a ha)⟩

theorem mappedDelta_of_perm_eq {m0 mf : Memory} (h : mf.perm = m0.perm) :
    MallocngMappedDelta 0 0 m0 mf :=
  mappedDelta_of_perm_le (fun a ha => by rwa [← h])

theorem mappedDelta_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    MallocngMappedDelta 0 0 m (m.unmapNonFrozen base len) := by
  apply mappedDelta_of_perm_le
  intro a ha
  rw [Memory.perm_unmapNonFrozen] at ha
  split at ha
  · contradiction
  · exact ha

theorem mappedDelta_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    MallocngMappedDelta 0 0 m (m.setPermNonFrozen base len p) := by
  apply mappedDelta_of_perm_le
  intro a ha
  rw [Memory.perm_setPermNonFrozen] at ha
  split at ha
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    exact hcond.1.2
  · exact ha

theorem mappedDelta_mmapFixedProtNone {m : Memory} {base : BitVec 64} {len : Nat}
    (hmap : m.allPerm (·.mapped) base len = true) :
    MallocngMappedDelta 0 0 m (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen
      base len Perm.protNone) := by
  apply mappedDelta_of_perm_le
  intro a ha
  by_cases hin : (a - base).toNat < len
  · have h1 := (Memory.allPerm_iff m (·.mapped) base len).mp hmap (a - base).toNat hin
    have hab : base + BitVec.ofNat 64 (a - base).toNat = a := by bv_arith
    rwa [hab] at h1
  · rw [Memory.perm_setPermNonFrozen, Memory.perm_mapZero, Memory.perm_unmapNonFrozen] at ha
    simp only [decide_eq_false hin, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at ha
    exact ha

theorem mappedDelta_mapZero (m : Memory) (base : BitVec 64) (len : Nat) :
    MallocngMappedDelta 1 len m (m.mapZero base len) := by
  refine ⟨[(base, len)], Nat.le_refl _, by simp, fun a ha => ?_⟩
  rw [Memory.perm_mapZero] at ha
  split at ha
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact Or.inr ⟨(base, len), List.Mem.head _, hc.1⟩
  · exact Or.inl ha

theorem mappedDelta_mapZeroProtNone (m : Memory) (base : BitVec 64) (len : Nat) :
    MallocngMappedDelta 1 len m ((m.mapZero base len).setPermNonFrozen base len Perm.protNone) := by
  simpa using MallocngMappedDelta.trans (mappedDelta_mapZero m base len)
    (mappedDelta_setPermNonFrozen (m.mapZero base len) base len Perm.protNone)

theorem mappedDelta_remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) :
    MallocngMappedDelta 1 newSize m (m.remapRw oldBase oldSize newBase newSize) := by
  refine ⟨[(newBase, newSize)], Nat.le_refl _, by simp, fun a ha => ?_⟩
  rw [Memory.perm_remapRw_raw] at ha
  split at ha
  · exact Or.inl ha
  · split at ha
    · rename_i hin; exact Or.inr ⟨(newBase, newSize), List.Mem.head _, hin⟩
    · split at ha
      · contradiction
      · exact Or.inl ha

private theorem mask_page_eq_shift (x : BitVec 64) :
    x &&& (-4096#64) = (x >>> 12) <<< 12 := by bv_bits

theorem mprotect_align_addr (addr : BitVec 64) (h : 4096 ∣ addr.toNat) :
    addr &&& (-4096#64) = addr := by
  rw [mask_page_eq_shift]; apply BitVec.eq_of_toNat_eq
  have ha := addr.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow _ 12, Nat.shiftLeft_eq]
  show (addr.toNat / 4096 * 4096) % 2 ^ 64 = addr.toNat; omega

theorem mprotect_align_len (addr x1 : BitVec 64) (len : Nat)
    (hx1 : x1.toNat = len) (ha_al : 4096 ∣ addr.toNat) (hl_al : 4096 ∣ len)
    (hfit : addr.toNat + len ≤ 2 ^ 48) :
    ((addr + (4095#64 + x1)) &&& (-4096#64)) - (addr &&& (-4096#64)) = x1 := by
  rw [mprotect_align_addr addr ha_al, mask_page_eq_shift]; apply BitVec.eq_of_toNat_eq
  have hsum_toNat : (addr + (4095#64 + x1)).toNat = addr.toNat + len + 4095 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hx1]; omega
  have hdiv : ((addr + (4095#64 + x1)).toNat >>> 12) <<< 12 = addr.toNat + len := by
    rw [hsum_toNat, Nat.shiftRight_eq_div_pow _ 12, Nat.shiftLeft_eq]
    show (addr.toNat + len + 4095) / 4096 * 4096 = addr.toNat + len; omega
  rw [BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, hdiv, Nat.mod_eq_of_lt (by omega), hx1]; omega
  · rw [BitVec.le_def, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, hdiv, Nat.mod_eq_of_lt (by omega)]; omega

/-! ## `munmap` Step Rule -/

theorem step_svc_munmap_rawLen {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc addr : BitVec 64} {rawLen : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 215#64) (haddr : s.readReg64 .x0 = addr)
    (hlen : (s.readReg64 .x1).toNat = rawLen) (hpos : 0 < rawLen)
    (hal : 4096 ∣ addr.toNat) (hfit : addr.toNat + pageAlignUp rawLen ≤ 2 ^ 48)
    (hok : SepWP prog target_pc
      ((((s.writeReg64 .x0 0#64).setPC (pc + 4#64)).setMem
        (s.mem.unmapNonFrozen addr (pageAlignUp rawLen))).setPhysMemAvail
        (s.physMemAvail + s.mem.countRw addr (pageAlignUp rawLen)))
      P post oom)
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s
      (memRegion addr (pageAlignUp rawLen) ∗ memMapped addr (pageAlignUp rawLen) ∗ P) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hsvc_eq : svc s = execMunmap s := (hSvc s).2.1 hx8
  have hal_mod : (s.readReg64 .x0).toNat % PAGE_SIZE = 0 := by
    rw [haddr]; unfold PAGE_SIZE; exact Nat.mod_eq_zero_of_dvd hal
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := fun hz => by rw [hz, BitVec.toNat_ofNat] at hlen; omega
  have hm_assoc : s.mem ⊨ memRegion addr (pageAlignUp rawLen) ∗
      (memMapped addr (pageAlignUp rawLen) ∗ (P ∗ R)) := by simpa [sepConj_assoc] using hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true := by
    rw [haddr, hlen]; exact Satisfies.allPerm_not_frozen_of_memRegion hm_assoc
  have hexec : execMunmap s =
      (((s.setMem (s.mem.unmapNonFrozen addr (pageAlignUp rawLen))).setPhysMemAvail
        (s.physMemAvail + s.mem.countRw addr (pageAlignUp rawLen))).writeReg64 .x0 0#64).advancePC := by
    simpa [haddr, hlen] using execMunmap_ok s hal_mod hlen_ne (by rwa [haddr, hlen]) hfrz
  have heval : prog.evalInst (.system false 0#16) s = execMunmap s := by
    rw [evalInst_svc0_prog hProgSvc]
    · exact hsvc_eq
    · rw [hsvc_eq, hexec]; simp only [arm64_norm]; exact fun a ha => Memory.keepsFrozen_unmapNonFrozen _ _ _ a ha
    · rw [hsvc_eq, hexec]; simp [arm64_norm]
    · rw [hsvc_eq, hexec]; simp [arm64_norm]
  rw [heval, hexec]
  have hst : (((s.setMem (s.mem.unmapNonFrozen addr (pageAlignUp rawLen))).setPhysMemAvail
        (s.physMemAvail + s.mem.countRw addr (pageAlignUp rawLen))).writeReg64 .x0 0#64).advancePC =
      ((((s.writeReg64 .x0 0#64).setPC (pc + 4#64)).setMem
        (s.mem.unmapNonFrozen addr (pageAlignUp rawLen))).setPhysMemAvail
        (s.physMemAvail + s.mem.countRw addr (pageAlignUp rawLen))) := by
    cases s; simp [State.setMem, State.setPhysMemAvail, State.writeReg64, State.advancePC, State.setPC] at hpc ⊢
    exact hpc
  rw [hst]; exact SepWP.to_reaches_pc hok (Satisfies.unmapNonFrozen hm_assoc)

theorem mappedDelta_zero_step {m0 m1 m2 m3 : Memory}
    (h01 : m1.perm = m0.perm) (h12 : MallocngMappedDelta 0 0 m1 m2) (h23 : m3.perm = m2.perm) :
    MallocngMappedDelta 0 0 m0 m3 := by
  simpa using MallocngMappedDelta.trans
    (MallocngMappedDelta.trans (mappedDelta_of_perm_eq h01) h12) (mappedDelta_of_perm_eq h23)

theorem mappedDelta_one_step {len : Nat} {m0 m1 m2 m3 : Memory}
    (h01 : m1.perm = m0.perm) (h12 : MallocngMappedDelta 1 len m1 m2) (h23 : m3.perm = m2.perm) :
    MallocngMappedDelta 1 len m0 m3 := by
  simpa using MallocngMappedDelta.trans
    (MallocngMappedDelta.trans (mappedDelta_of_perm_eq h01) h12) (mappedDelta_of_perm_eq h23)

/-! ## `mprotect` Step Rule -/

theorem step_svc_mprotect_rw {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc addr : BitVec 64} {bs : List (BitVec 8)} {len : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 226#64) (haddr : s.readReg64 .x0 = addr)
    (hlen : (s.readReg64 .x1).toNat = len) (hprot : s.readReg64 .x2 = 3#64)
    (hbs : bs.length = len) (hpos : 0 < len) (hl_al : 4096 ∣ len) (ha_al : 4096 ∣ addr.toNat)
    (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hok : SepWP prog target_pc
      ((((s.writeReg64 .x0 0#64).setPC (pc + 4#64)).setMem
        (s.mem.setPermNonFrozen addr len Perm.rw)).setPhysMemAvail
        (s.physMemAvail - (len - s.mem.countRw addr len)))
      ((addr ↦ₛ bs) ∗ P) post oom)
    (hoom : s.physMemAvail < len →
      ∀ R, (s.mem ⊨ ((addr ↦ₙ bs) ∗ P) ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s ((addr ↦ₙ bs) ∗ P) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hsvc_eq : svc s = execMprotect s := (hSvc s).2.2.2.1 hx8 hprot
  have hal_mod : (s.readReg64 .x0).toNat % PAGE_SIZE = 0 := by
    rw [haddr]; unfold PAGE_SIZE; exact Nat.mod_eq_zero_of_dvd ha_al
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := fun hz => by rw [hz, BitVec.toNat_ofNat] at hlen; omega
  have halign : pageAlignUp (s.readReg64 .x1).toNat = len := by
    rw [hlen]; exact pageAlignUp_of_dvd hl_al
  have hm_assoc : s.mem ⊨ (addr ↦ₙ bs) ∗ (P ∗ R) := by simpa [sepConj_assoc] using hm
  have hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true := by
    rw [haddr, halign, ← hbs]; exact Satisfies.allPerm_not_frozen_of_pointsToBytesProtNone hm_assoc
  have hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true := by
    rw [haddr, halign, ← hbs]; exact Satisfies.allPerm_mapped_of_pointsToBytesProtNone hm_assoc
  by_cases hphys : pageAlignUp (s.readReg64 .x1).toNat -
      s.mem.countRw (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat) ≤ s.physMemAvail
  · have hexec : execMprotect s =
        (((s.setMem (s.mem.setPermNonFrozen addr len Perm.rw)).setPhysMemAvail
          (s.physMemAvail - (len - s.mem.countRw addr len))).writeReg64 .x0 0#64).advancePC := by
      simpa [haddr, halign, hprot] using
        execMprotect_ok s (Or.inr hprot) hal_mod hlen_ne (by rwa [haddr, halign]) hfrz hmap
          (fun _ => hphys)
    have heval : prog.evalInst (.system false 0#16) s = execMprotect s := by
      rw [evalInst_svc0_prog hProgSvc]
      · exact hsvc_eq
      · rw [hsvc_eq, hexec]; simp only [arm64_norm]
        exact fun a ha => Memory.keepsFrozen_setPermNonFrozen _ _ _ _ a ha
      · rw [hsvc_eq, hexec]; simp [arm64_norm]
      · rw [hsvc_eq, hexec]; simp [arm64_norm]
    rw [heval, hexec]
    have hm' : s.mem.setPermNonFrozen addr len Perm.rw ⊨ ((addr ↦ₛ bs) ∗ P) ∗ R := by
      have hm1 := Satisfies.setPermRw_of_pointsToBytesProtNone hm_assoc
      rw [hbs] at hm1; simpa [sepConj_assoc] using hm1
    have hst : (((s.setMem (s.mem.setPermNonFrozen addr len Perm.rw)).setPhysMemAvail
          (s.physMemAvail - (len - s.mem.countRw addr len))).writeReg64 .x0 0#64).advancePC =
        ((((s.writeReg64 .x0 0#64).setPC (pc + 4#64)).setMem
          (s.mem.setPermNonFrozen addr len Perm.rw)).setPhysMemAvail
          (s.physMemAvail - (len - s.mem.countRw addr len))) := by
      cases s; simp [State.setMem, State.setPhysMemAvail, State.writeReg64, State.advancePC, State.setPC] at hpc ⊢
      exact hpc
    rw [hst]; exact SepWP.to_reaches_pc hok hm'
  · have hexec : execMprotect s = s.setStatus .OutOfMemory :=
      execMprotect_rw_oom s hprot hal_mod hlen_ne (by rwa [haddr, halign]) hfrz hmap hphys
    have heval : prog.evalInst (.system false 0#16) s = execMprotect s := by
      rw [evalInst_svc0_prog hProgSvc]
      · exact hsvc_eq
      · rw [hsvc_eq, hexec]; exact Memory.KeepsFrozen.refl _
      · rw [hsvc_eq, hexec]; rfl
      · rw [hsvc_eq, hexec]; rfl
    rw [heval, hexec]
    rw [haddr, halign] at hphys
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom (by omega) R hm)

/-! ## `MAP_FIXED` `PROT_NONE` `__mmap` Step Rule -/

private theorem evalInst_svc0_execMmap {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {s : State} (hx8 : s.readReg64 .x8 = 222#64)
    (hProgSvc : prog.svc = svc) :
    prog.evalInst (.system false 0#16) s = execMmap s := by
  have hx8' : s.readReg64 Reg.x8 = SYS_MMAP := hx8
  have h1 : svc s = execMmap s := (hSvc s).2.2.1 hx8'
  have h2 : Syscall.standard s = execMmap s := by
    unfold Syscall.standard Syscall.dispatch; rw [hx8']; rfl
  rw [Arm64.Program.evalInst_svc0, hProgSvc, ← h2, ← evalSvc_standard]
  simp only [evalSvc, h1, h2]

private theorem state_setPhysMemAvail_comm (s : State) (n : Nat) (v pc : BitVec 64) (m : Memory) :
    (((s.setPhysMemAvail n).writeReg64 .x0 v).setPC pc).setMem m =
      (((s.writeReg64 .x0 v).setPC pc).setMem m).setPhysMemAvail n := by
  cases s; rfl

private theorem state_setPhysMemAvail_nextOracle_comm (s : State) (n : Nat) (v pc : BitVec 64)
    (m : Memory) :
    (((s.setPhysMemAvail n).nextOracle.writeReg64 .x0 v).setPC pc).setMem m =
      (((s.nextOracle.writeReg64 .x0 v).setPC pc).setMem m).setPhysMemAvail n := by
  cases s; rfl

theorem step_svc_mmap_fixed_protNone {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc addr : BitVec 64} {bs : List (BitVec 8)} {len : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (haddr : s.readReg64 .x0 = addr)
    (hlen : (s.readReg64 .x1).toNat = len) (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x32#64) (hoff : s.readReg64 .x5 = 0#64)
    (hbs : bs.length = len) (hpos : 0 < len) (hl_al : 4096 ∣ len)
    (hmin : 65536 ≤ addr.toNat) (ha_al : 4096 ∣ addr.toNat) (hfit : addr.toNat + len ≤ 2 ^ 48)
    (hok : s.mem.allPerm (·.mapped) addr len = true →
      SepWP prog target_pc
        ((((s.writeReg64 .x0 addr).setPC (pc + 4#64)).setMem
          (((s.mem.unmapNonFrozen addr len).mapZero addr len).setPermNonFrozen
            addr len Perm.protNone)).setPhysMemAvail
          (s.physMemAvail + s.mem.countRw addr len))
        ((addr ↦ₙ List.replicate len 0#8) ∗ P) post oom)
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s ((addr ↦ₛ bs) ∗ P) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm_assoc : s.mem ⊨ (addr ↦ₛ bs) ∗ (P ∗ R) := by simpa [sepConj_assoc] using hm
  have hmap : s.mem.allPerm (·.mapped) addr len = true := by
    rw [← hbs]; exact Satisfies.allPerm_mapped_of_pointsToBytes hm_assoc
  have hreg : s.mem ⊨ memRegion addr len ∗ (P ∗ R) := by
    have h1 := Satisfies.mono (sepConj_mono_left
      ((IsBlock.pointsToBytes addr bs).entails (IsBlock.memRegion addr _) fun _ _ => trivial)) hm_assoc
    rwa [hbs] at h1
  have hcnt : s.mem.countRw addr len = len := Satisfies.countRw_eq_of_memRegion hreg
  refine SepWP.to_reaches_pc ?_ (by rw [← sepConj_assoc] at hreg; exact hreg)
  refine SepWP.step_svc_mmap_fixed_decommit hpc hrun hfetch hx8 haddr hprot hflags hoff hlen hpos
    hl_al ha_al hmin hfit (fun m' hm' => ?_) (evalInst_svc0_execMmap hSvc hx8 hProgSvc)
  subst hm'
  rw [state_setPhysMemAvail_comm]
  have h := hok hmap
  rwa [hcnt] at h

/-! ## Anonymous `__mmap` Step Rules -/

theorem step_svc_mmap_rw_rawLen {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rawLen : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = rawLen) (hpos : 0 < rawLen)
    (hok : ∀ (mb : BitVec 64),
      mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + pageAlignUp rawLen ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem
          (s.mem.mapZero mb (pageAlignUp rawLen))).setPhysMemAvail
          (s.physMemAvail - pageAlignUp rawLen))
        ((mb ↦ₛ List.replicate (pageAlignUp rawLen) 0#8) ∗
          memMapped mb (pageAlignUp rawLen) ∗ P) post oom)
    (hoom : (MallocngSanitizedSvc svc → MallocngNoGapOrPhys s (pageAlignUp rawLen)) →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s P post oom := by
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := fun hz => by rw [hz, BitVec.toNat_ofNat] at hlen; omega
  refine SepWP.step_svc_mmap_anon_rw hpc hrun hfetch hx8 hprot (Or.inl hflags) hoff
    (by rw [hlen]) (pageAlignUp_pos_of_ne_zero (by omega))
    (fun mb m' _ hne hdvd hfit _ hm' => ?_) (fun hcase => hoom fun hSan => ?_)
    (evalInst_svc0_execMmap hSvc hx8 hProgSvc)
  · subst hm'
    rw [state_setPhysMemAvail_nextOracle_comm]
    exact hok mb hne hdvd hfit
  · rcases hcase with hsan | hphys
    · have hsan' : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
          (pageAlignUp (s.readReg64 .x1).toNat) = none := by rw [hlen]; exact hsan
      have h := hSan s hrun hx8 (Or.inr hprot) hflags hoff hlen_ne (by
        rw [(hSvc s).2.2.1 hx8, execMmap_anon_oom s hprot (Or.inl hflags) hoff hlen_ne hsan']; rfl)
      rwa [hlen] at h
    · exact Or.inr hphys

theorem step_svc_mmap_protNone_rawLen {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rawLen : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 222#64) (hprot : s.readReg64 .x2 = 0#64)
    (hflags : s.readReg64 .x3 = 0x22#64) (hoff : s.readReg64 .x5 = 0#64)
    (hlen : (s.readReg64 .x1).toNat = rawLen) (hpos : 0 < rawLen)
    (hok : ∀ (mb : BitVec 64),
      mb ≠ 0#64 → 4096 ∣ mb.toNat → mb.toNat + pageAlignUp rawLen ≤ 2 ^ 48 →
      SepWP prog target_pc
        (((s.nextOracle.writeReg64 .x0 mb).setPC (pc + 4#64)).setMem
          ((s.mem.mapZero mb (pageAlignUp rawLen)).setPermNonFrozen
            mb (pageAlignUp rawLen) Perm.protNone))
        ((mb ↦ₙ List.replicate (pageAlignUp rawLen) 0#8) ∗
          memMapped mb (pageAlignUp rawLen) ∗ P) post oom)
    (hoom : (MallocngSanitizedSvc svc → MallocngNoGapOrPhys s (pageAlignUp rawLen)) →
      ∀ R, (s.mem ⊨ P ∗ R) → (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s P post oom := by
  have hlen_ne : s.readReg64 .x1 ≠ 0#64 := fun hz => by rw [hz, BitVec.toNat_ofNat] at hlen; omega
  refine SepWP.step_svc_mmap_anon_reserve hpc hrun hfetch hx8 hprot (Or.inl hflags) hoff
    (by rw [hlen]) (pageAlignUp_pos_of_ne_zero (by omega))
    (fun mb m' _ hne hdvd hfit hm' => ?_) (fun hsan => hoom fun hSan => ?_)
    (evalInst_svc0_execMmap hSvc hx8 hProgSvc)
  · subst hm'
    exact hok mb hne hdvd hfit
  · have hsan' : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
        (pageAlignUp (s.readReg64 .x1).toNat) = none := by rw [hlen]; exact hsan
    have h := hSan s hrun hx8 (Or.inl hprot) hflags hoff hlen_ne (by
      rw [(hSvc s).2.2.1 hx8, execMmap_anon_protNone_oom s hprot (Or.inl hflags) hoff hlen_ne hsan']
      rfl)
    rwa [hlen] at h

/-! ## `__mremap` Step Rules -/

private theorem readBytes_getElem? (m : Memory) (base : BitVec 64) (n i : Nat) (hi : i < n) :
    (m.readBytes base n)[i]? = some (m.read8 (base + BitVec.ofNat 64 i)) := by
  induction n generalizing base i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [Memory.readBytes_succ]
    | succ i =>
      simp only [Memory.readBytes_succ, List.getElem?_cons_succ]
      rw [ih (base + 1#64) i (by omega)]; congr 2; bv_arith

theorem satisfies_remapRw_bytes_mapped {m : Memory} {Q : SepProp}
    {oldAddr newBase : BitVec 64} {oldBs : List (BitVec 8)} {oldLen newLen : Nat}
    (hm : m ⊨ (oldAddr ↦ₛ oldBs) ∗ (memMapped oldAddr oldLen ∗ Q))
    (hbs : oldBs.length = oldLen) (hnewFit : newBase.toNat + newLen ≤ 2 ^ 48)
    (hcanMap : (m.unmapNonFrozen oldAddr oldLen).canMap newBase newLen = true) :
    m.remapRw oldAddr oldLen newBase newLen ⊨
      (newBase ↦ₛ (oldBs.take newLen ++ List.replicate (newLen - oldLen) 0#8)) ∗
        (memMapped newBase newLen ∗ Q) := by
  have hread : m.readBytes oldAddr oldLen = oldBs := by
    rw [← hbs]; exact ((IsBlock.pointsToBytes oldAddr oldBs).read hm).2
  have hOld : m.allPerm (fun p => !p.frozen) oldAddr oldLen = true := by
    rw [← hbs]; exact Satisfies.allPerm_not_frozen_of_pointsToBytes hm
  have hNew : m.allPerm (fun p => !p.frozen) newBase newLen = true :=
    Memory.allPerm_not_frozen_of_canMap_unmapNonFrozen hcanMap
  have hOldFrz : ∀ a, (a - oldAddr).toNat < oldLen → (m.perm a).frozen = false := by
    intro a ho
    have hi := (Memory.allPerm_iff m (fun p => !p.frozen) oldAddr oldLen).mp hOld (a - oldAddr).toNat ho
    have hab : oldAddr + BitVec.ofNat 64 (a - oldAddr).toNat = a := by bv_arith
    rw [hab, Bool.not_eq_true'] at hi; exact hi
  have hreg : m ⊨ memRegion oldAddr oldLen ∗ memMapped oldAddr oldLen ∗ Q := by
    have h1 := Satisfies.mono (sepConj_mono_left
      ((IsBlock.pointsToBytes oldAddr oldBs).entails (IsBlock.memRegion oldAddr _) fun _ _ => trivial)) hm
    rwa [hbs] at h1
  have hm0 : (m.unmapNonFrozen oldAddr oldLen).mapZero newBase newLen ⊨
      memRegion newBase newLen ∗ (memMapped newBase newLen ∗ Q) := by
    simpa [sepConj_assoc] using Satisfies.mapZero_mapped (Satisfies.unmapNonFrozen hreg) hcanMap
  have hlf_eq : ∀ a, (m.remapRw oldAddr oldLen newBase newLen).isLazyFree a =
      ((m.unmapNonFrozen oldAddr oldLen).mapZero newBase newLen).isLazyFree a := by
    intro a
    rw [Memory.isLazyFree_remapRw m oldAddr oldLen newBase newLen hOld hNew, Memory.isLazyFree_mapZero]
    by_cases hn : (a - newBase).toNat < newLen
    · have hcm := (Memory.allPerm_iff (m.unmapNonFrozen oldAddr oldLen)
        (fun p => !p.mapped) newBase newLen).mp hcanMap (a - newBase).toNat hn
      have hab : newBase + BitVec.ofNat 64 (a - newBase).toNat = a := by bv_arith
      rw [hab, Bool.not_eq_true'] at hcm
      rw [Memory.isLazyFree_eq_false_of_unmapped hcm]
      simp only [hn, ↓reduceIte]
      split
      · rename_i hio
        have hin : InRegion oldAddr oldBs.length (oldAddr + BitVec.ofNat 64 (a - newBase).toNat) := by
          rw [hbs]; simp only [InRegion]
          have hs : oldAddr + BitVec.ofNat 64 (a - newBase).toNat - oldAddr =
              BitVec.ofNat 64 (a - newBase).toNat := by bv_arith
          rw [hs, BitVec.toNat_ofNat]
          exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hio
        exact (IsBlock.pointsToBytes oldAddr oldBs).isLazyFree_false hm hin
      · rfl
    · rw [Memory.isLazyFree_unmapNonFrozen]
      simp only [hn, ↓reduceIte]
      by_cases ho : (a - oldAddr).toNat < oldLen
      · simp only [ho, hOldFrz a ho, decide_true, Bool.not_false, Bool.true_and, ↓reduceIte,
          Option.frozen]
      · simp only [ho, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have han_eq : ∀ a, (m.remapRw oldAddr oldLen newBase newLen).isAnon a =
      ((m.unmapNonFrozen oldAddr oldLen).mapZero newBase newLen).isAnon a := by
    intro a
    rw [Memory.isAnon_remapRw m oldAddr oldLen newBase newLen hOld hNew, Memory.isAnon_mapZero]
    by_cases hn : (a - newBase).toNat < newLen
    · have hcm := (Memory.allPerm_iff (m.unmapNonFrozen oldAddr oldLen)
        (fun p => !p.mapped) newBase newLen).mp hcanMap (a - newBase).toNat hn
      have hab : newBase + BitVec.ofNat 64 (a - newBase).toNat = a := by bv_arith
      rw [hab] at hcm
      simp only [hn, hcm, ↓reduceIte, Bool.and_true]
      split
      · rename_i hio
        have hm_map : m ⊨ memMapped oldAddr oldLen ∗ ((oldAddr ↦ₛ oldBs) ∗ Q) := by
          rw [← sepConj_assoc, sepConj_comm (memMapped oldAddr oldLen), sepConj_assoc]; exact hm
        have hin : InRegion oldAddr oldLen (oldAddr + BitVec.ofNat 64 (a - newBase).toNat) := by
          simp only [InRegion]
          have hs : oldAddr + BitVec.ofNat 64 (a - newBase).toNat - oldAddr =
              BitVec.ofNat 64 (a - newBase).toNat := by bv_arith
          rw [hs, BitVec.toNat_ofNat]
          exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hio
        exact Satisfies.isAnon_of_memMapped hm_map hin
      · rfl
    · rw [Memory.isAnon_unmapNonFrozen]
      simp only [hn, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      by_cases ho : (a - oldAddr).toNat < oldLen
      · simp only [ho, hOldFrz a ho, decide_true, Bool.not_false, Bool.true_and, ↓reduceIte,
          Option.frozen]
      · simp only [ho, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hag : AgreesOutside ((m.unmapNonFrozen oldAddr oldLen).mapZero newBase newLen)
      (m.remapRw oldAddr oldLen newBase newLen) newBase newLen := by
    refine ⟨fun a hout => ?_, funext fun a => ?_, fun a _ => hlf_eq a,
      fun a h => (hlf_eq a).trans h, fun a h => (han_eq a).trans h⟩
    · have hnot_new : ¬ (a - newBase).toNat < newLen := by
        rw [outsideRegion_iff_not_inRegion] at hout; exact hout
      rw [Memory.read8_remapRw m oldAddr oldLen newBase newLen hOld hNew,
        Memory.read8_mapZero, Memory.read8_unmapNonFrozen]
      simp only [hnot_new, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      by_cases ho : (a - oldAddr).toNat < oldLen
      · simp only [ho, hOldFrz a ho, decide_true, Bool.not_false, Bool.true_and, ↓reduceIte]
      · simp only [ho, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · rw [Memory.perm_remapRw m oldAddr oldLen newBase newLen hOld hNew, Memory.perm_mapZero]
      by_cases hn : (a - newBase).toNat < newLen
      · have hcm := (Memory.allPerm_iff (m.unmapNonFrozen oldAddr oldLen)
          (fun p => !p.mapped) newBase newLen).mp hcanMap (a - newBase).toNat hn
        have hab : newBase + BitVec.ofNat 64 (a - newBase).toNat = a := by bv_arith
        rw [hab] at hcm; simp only [hn, hcm, decide_true, Bool.true_and, ↓reduceIte]
      · rw [Memory.perm_unmapNonFrozen]
        simp only [hn, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        by_cases ho : (a - oldAddr).toNat < oldLen
        · simp only [ho, hOldFrz a ho, decide_true, Bool.not_false, Bool.true_and, ↓reduceIte]
        · simp only [ho, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  let newBs := oldBs.take newLen ++ List.replicate (newLen - oldLen) 0#8
  have hnewBs_len : newBs.length = newLen := by simp [newBs, hbs]; omega
  have hread_new : (m.remapRw oldAddr oldLen newBase newLen).readBytes newBase newBs.length = newBs := by
    rw [hnewBs_len]; apply List.ext_getElem?
    intro i; by_cases hi : i < newLen
    · rw [readBytes_getElem? _ _ _ _ hi, Memory.read8_remapRw m oldAddr oldLen newBase newLen hOld hNew]
      have hsub : (newBase + BitVec.ofNat 64 i - newBase).toNat = i := by
        have h1 : newBase + BitVec.ofNat 64 i - newBase = BitVec.ofNat 64 i := by bv_arith
        rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hsub]; simp only [hi, ↓reduceIte]
      by_cases hio : i < oldLen
      · simp only [hio, ↓reduceIte, newBs]
        rw [List.getElem?_append_left (by simp [hbs]; omega), List.getElem?_take_of_lt hi,
          ← hread, readBytes_getElem? _ _ _ _ hio]
      · simp only [hio, ↓reduceIte, newBs]
        have htl : (oldBs.take newLen).length = oldLen := by simp [hbs]; omega
        rw [List.getElem?_append_right (by omega), htl, List.getElem?_replicate]
        simp only [show i - oldLen < newLen - oldLen by omega, ↓reduceIte]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
  exact (IsBlock.memRegion newBase newLen).update (IsBlock.pointsToBytes newBase newBs)
    (by omega) hm0 hag ⟨by omega, hread_new⟩

theorem step_svc_mremap_tight {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc oldAddr : BitVec 64} {oldBs : List (BitVec 8)} {oldLen newRawLen : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 216#64) (holdAddr : s.readReg64 .x0 = oldAddr)
    (holdLen : (s.readReg64 .x1).toNat = oldLen) (hnewRaw : (s.readReg64 .x2).toNat = newRawLen)
    (hflags : s.readReg64 .x3 = 1#64) (hbs : oldBs.length = oldLen)
    (hposOld : 0 < oldLen) (hdvdOld : 4096 ∣ oldLen) (hdvdAddr : 4096 ∣ oldAddr.toNat)
    (holdFit : oldAddr.toNat + oldLen ≤ 2 ^ 48)
    (hposNew : 0 < newRawLen) (hmaxNew : newRawLen ≤ 2 ^ 64 - 4096)
    (hfail : SepWP prog target_pc
      ((s.nextOracle.writeReg64 .x0 (-12#64)).setPC (pc + 4#64))
      ((oldAddr ↦ₛ oldBs) ∗ memMapped oldAddr oldLen ∗ P) post oom)
    (hok : ∀ (newBase : BitVec 64),
      newBase ≠ 0#64 → 4096 ∣ newBase.toNat → newBase.toNat + pageAlignUp newRawLen ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.nextOracle.writeReg64 .x0 newBase).setPC (pc + 4#64)).setMem
          (s.mem.remapRw oldAddr oldLen newBase (pageAlignUp newRawLen))).setPhysMemAvail
          (s.physMemAvail + oldLen - pageAlignUp newRawLen))
        ((newBase ↦ₛ (oldBs.take (pageAlignUp newRawLen) ++
            List.replicate (pageAlignUp newRawLen - oldLen) 0#8)) ∗
          memMapped newBase (pageAlignUp newRawLen) ∗ P) post oom)
    (hoom : s.physMemAvail + oldLen < pageAlignUp newRawLen →
      ∀ R, (s.mem ⊨ ((oldAddr ↦ₛ oldBs) ∗ memMapped oldAddr oldLen ∗ P) ∗ R) →
        (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s
      ((oldAddr ↦ₛ oldBs) ∗ memMapped oldAddr oldLen ∗ P) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have halOld : pageAlignUp (s.readReg64 .x1).toNat = oldLen := by
    rw [holdLen]; exact pageAlignUp_of_dvd hdvdOld
  have halMod : (s.readReg64 .x0).toNat % PAGE_SIZE = 0 := by
    rw [holdAddr]; unfold PAGE_SIZE; exact Nat.mod_eq_zero_of_dvd hdvdAddr
  have hm_assoc : s.mem ⊨ (oldAddr ↦ₛ oldBs) ∗ (memMapped oldAddr oldLen ∗ (P ∗ R)) := by
    simpa [sepConj_assoc] using hm
  have hrw : s.mem.allPerm (· == some Perm.rw) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true := by
    rw [holdAddr, halOld, Memory.allPerm_iff]; intro i hi
    have hin : InRegion oldAddr oldBs.length (oldAddr + BitVec.ofNat 64 i) := by
      simpa [InRegion, hbs] using IsBlock.inRegion_sub_range (a := oldAddr) (b := oldAddr)
        (k := oldLen) (n := oldLen) (by simp) (by omega) hi
    rw [(IsBlock.pointsToBytes oldAddr oldBs).perm_rw hm_assoc hin]; rfl
  have hanon : s.mem.allAnon (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat) = true := by
    rw [holdAddr, halOld]
    have hm_map : s.mem ⊨ memMapped oldAddr oldLen ∗ ((oldAddr ↦ₛ oldBs) ∗ (P ∗ R)) := by
      rw [← sepConj_assoc, sepConj_comm (memMapped oldAddr oldLen), sepConj_assoc]
      exact hm_assoc
    exact Satisfies.allAnon_of_memMapped hm_map
  have hstep := (hSvc s).2.2.2.2 hx8 hflags halMod (by omega) (by omega)
    (by unfold PAGE_SIZE; omega) (by rwa [holdAddr, halOld]) hrw hanon
  rcases hstep with hsvc_fail | ⟨hphysLt, hsvc_oom⟩ | ⟨newBase, hne, hnbMod, hnbFit, hnbMap, hsvc_ok⟩
  · have heval : prog.evalInst (.system false 0#16) s = svc s := by
      rw [evalInst_svc0_prog hProgSvc]
      · rw [hsvc_fail]; exact Memory.KeepsFrozen.refl _
      · rw [hsvc_fail]; simp [arm64_norm]
      · rw [hsvc_fail]; simp [arm64_norm]
    rw [heval, hsvc_fail]
    have hst : ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC =
        (s.nextOracle.writeReg64 .x0 (-12#64)).setPC (pc + 4#64) := by
      cases s; simp [ENOMEM, State.nextOracle, State.writeReg64, State.advancePC, State.setPC] at hpc ⊢
      exact hpc
    rw [hst]; exact SepWP.to_reaches_pc hfail hm
  · have heval : prog.evalInst (.system false 0#16) s = svc s := by
      rw [evalInst_svc0_prog hProgSvc]
      · rw [hsvc_oom]; exact Memory.KeepsFrozen.refl _
      · rw [hsvc_oom]; rfl
      · rw [hsvc_oom]; rfl
    rw [heval, hsvc_oom]
    rw [halOld, hnewRaw] at hphysLt
    exact reaches_pc_oom rfl (by simpa [State.setStatus] using hoom (by omega) R hm)
  · rw [hnewRaw] at hnbFit
    rw [holdAddr, halOld, hnewRaw] at hnbMap
    rw [holdAddr, halOld, hnewRaw, mallocngRemapRw_eq_remapRw] at hsvc_ok
    have heval : prog.evalInst (.system false 0#16) s = svc s := by
      rw [evalInst_svc0_prog hProgSvc]
      · rw [hsvc_ok]; simp only [arm64_norm]; exact Memory.keepsFrozen_remapRw _ _ _ _ _
      · rw [hsvc_ok]; simp [arm64_norm]
      · rw [hsvc_ok]; simp [arm64_norm]
    rw [heval, hsvc_ok]
    have hdvdNew : 4096 ∣ newBase.toNat := by unfold PAGE_SIZE at hnbMod; exact Nat.dvd_of_mod_eq_zero hnbMod
    have hm' : s.mem.remapRw oldAddr oldLen newBase (pageAlignUp newRawLen) ⊨
        ((newBase ↦ₛ (oldBs.take (pageAlignUp newRawLen) ++
            List.replicate (pageAlignUp newRawLen - oldLen) 0#8)) ∗
          memMapped newBase (pageAlignUp newRawLen) ∗ P) ∗ R := by
      simpa [sepConj_assoc] using satisfies_remapRw_bytes_mapped hm_assoc hbs hnbFit hnbMap
    have hst : ((((s.setMem (s.mem.remapRw oldAddr oldLen newBase
            (pageAlignUp newRawLen))).setPhysMemAvail
            (s.physMemAvail + oldLen - pageAlignUp newRawLen)).nextOracle).writeReg64
            Reg.x0 newBase).advancePC =
        ((((s.nextOracle.writeReg64 .x0 newBase).setPC (pc + 4#64)).setMem
          (s.mem.remapRw oldAddr oldLen newBase (pageAlignUp newRawLen))).setPhysMemAvail
          (s.physMemAvail + oldLen - pageAlignUp newRawLen)) := by
      cases s; simp [State.setMem, State.setPhysMemAvail, State.nextOracle, State.writeReg64,
        State.advancePC, State.setPC] at hpc ⊢
      exact hpc
    rw [hst]; exact SepWP.to_reaches_pc (hok newBase hne hdvdNew hnbFit) hm'

theorem step_svc_mremap {prog : Program} {svc : State → State}
    (hSvc : MallocngSvcValid svc) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc oldAddr : BitVec 64} {oldBs : List (BitVec 8)} {oldLen newRawLen : Nat}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.system false 0#16))
    (hx8 : s.readReg64 .x8 = 216#64) (holdAddr : s.readReg64 .x0 = oldAddr)
    (holdLen : (s.readReg64 .x1).toNat = oldLen) (hnewRaw : (s.readReg64 .x2).toNat = newRawLen)
    (hflags : s.readReg64 .x3 = 1#64) (hbs : oldBs.length = oldLen)
    (hposOld : 0 < oldLen) (hdvdOld : 4096 ∣ oldLen) (hdvdAddr : 4096 ∣ oldAddr.toNat)
    (holdFit : oldAddr.toNat + oldLen ≤ 2 ^ 48)
    (hposNew : 0 < newRawLen) (hmaxNew : newRawLen ≤ 2 ^ 64 - 4096)
    (hfail : SepWP prog target_pc
      ((s.nextOracle.writeReg64 .x0 (-12#64)).setPC (pc + 4#64))
      ((oldAddr ↦ₛ oldBs) ∗ memMapped oldAddr oldLen ∗ P) post oom)
    (hok : ∀ (newBase : BitVec 64),
      newBase ≠ 0#64 → 4096 ∣ newBase.toNat → newBase.toNat + pageAlignUp newRawLen ≤ 2 ^ 48 →
      SepWP prog target_pc
        ((((s.nextOracle.writeReg64 .x0 newBase).setPC (pc + 4#64)).setMem
          (s.mem.remapRw oldAddr oldLen newBase (pageAlignUp newRawLen))).setPhysMemAvail
          (s.physMemAvail + oldLen - pageAlignUp newRawLen))
        ((newBase ↦ₛ (oldBs.take (pageAlignUp newRawLen) ++
            List.replicate (pageAlignUp newRawLen - oldLen) 0#8)) ∗
          memMapped newBase (pageAlignUp newRawLen) ∗ P) post oom)
    (hoom : s.physMemAvail < pageAlignUp newRawLen →
      ∀ R, (s.mem ⊨ ((oldAddr ↦ₛ oldBs) ∗ memMapped oldAddr oldLen ∗ P) ∗ R) →
        (s.mem ⊨ oom (s.setStatus .OutOfMemory) ∗ R))
    (hProgSvc : prog.svc = svc := by rfl) :
    SepWP prog target_pc s
      ((oldAddr ↦ₛ oldBs) ∗ memMapped oldAddr oldLen ∗ P) post oom :=
  step_svc_mremap_tight hSvc hpc hrun hfetch hx8 holdAddr holdLen hnewRaw hflags hbs
    hposOld hdvdOld hdvdAddr holdFit hposNew hmaxNew hfail hok (fun hlt => hoom (by omega)) hProgSvc

end VerifiedLibraries.Mallocng.Proofs
