/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process
public import ProofLib.Process.Assumptions
public import ProofLib.MallocngIface
public import ProofLib.SepLogic.Basic
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.CFG
public import ProofLib.SepLogic.Exists
public import ProofLib.SepLogic.Region
public import ProofLib.SepLogic.WP

/-!
# Initial Stack and Process-Load Helpers

Separation-logic read-only freezing, interval-based `SupportedOn` composition, `Program.pureMem`
lowering, and initial-stack unpacking for `ElfImage.loadState`.
-/

@[expose] public section
set_option autoImplicit false

namespace ProofLib.StdStartup
open Arm64 Arm64.Obj Arm64.Process Arm64.Snapshot ProofLib

/-! ## Separation-logic freezing, `SupportedOn` interval glue, and `pureMem` lowering -/
theorem pointsToBytes_freeze_ro (a : BitVec 64) (bs : List (BitVec 8)) : (a ↦ₛ bs) ⊢ |==> (a ↦ᵣ bs) := by
  induction bs generalizing a with | nil => rw [pointsToBytes_nil, pointsToBytesRO_nil]; exact bupd_intro emp | cons b rest ih => rw [pointsToBytes_cons, pointsToBytesRO_cons]; exact bupd_sep (ProofLib.pointsTo8_freeze_ro a b) (ih (a + 1#64))
theorem pointsToWords64_freeze_ro (a : BitVec 64) (ws : List (BitVec 64)) : (a ↦₆₄* ws) ⊢ |==> (a ↦₆₄ᵣ* ws) := by
  induction ws generalizing a with | nil => rw [pointsToWords64_nil, pointsToWords64RO_nil]; exact bupd_intro emp | cons w rest ih => rw [pointsToWords64_cons, pointsToWords64RO_cons]; exact bupd_sep (ProofLib.pointsTo64_freeze_ro a w) (ih (a + 8#64))
theorem pointsToWords64_eq_pointsToBytesLE (a : BitVec 64) (ws : List (BitVec 64)) : (a ↦₆₄* ws) = (a ↦ₛ ws.flatMap (Obj.bytesLE 8)) := by
  induction ws generalizing a with | nil => simp | cons w rest ih =>
    have h_eq : unpack64 w = Obj.bytesLE 8 w := rfl; have h8 : (Obj.bytesLE 8 w).length = 8 := (by simp [Obj.bytesLE])
    rw [pointsToWords64_cons, pointsTo64_eq_pointsToBytes, h_eq, ih (a + 8#64), List.flatMap_cons, pointsToBytes_append, h8]
theorem pointsToWords64RO_eq_pointsToBytesRO (a : BitVec 64) (ws : List (BitVec 64)) : (a ↦₆₄ᵣ* ws) = (a ↦ᵣ ws.flatMap (Obj.bytesLE 8)) := by
  induction ws generalizing a with | nil => simp | cons w rest ih =>
    have h_eq : unpack64 w = Obj.bytesLE 8 w := rfl; have h8 : (Obj.bytesLE 8 w).length = 8 := (by simp [Obj.bytesLE])
    rw [pointsToWords64RO_cons, pointsTo64RO_eq_pointsToBytesRO, h_eq, ih (a + 8#64), List.flatMap_cons, pointsToBytesRO_append, h8]
/-- Duplicate any read-only subslice `[off, off + len)` out of `base ↦ᵣ buf` as an equality. -/
theorem pointsToBytesRO_dup_slice (base : BitVec 64) (buf : List (BitVec 8)) (off len : Nat) (hle : off + len ≤ buf.length) :
    ((base ↦ᵣ buf) ∗ ((base + BitVec.ofNat 64 off) ↦ᵣ (buf.drop off).take len)) = (base ↦ᵣ buf) := by
  let sl := ((base + BitVec.ofNat 64 off) ↦ᵣ (buf.drop off).take len); have hsplit := pointsToBytesRO_split3 base buf off len hle
  calc (base ↦ᵣ buf) ∗ sl = sl ∗ (sl ∗ ((base ↦ᵣ buf.take off) ∗ ((base + BitVec.ofNat 64 (off + len)) ↦ᵣ buf.drop (off + len)))) := by rw [sepConj_comm, hsplit]
    _ = (sl ∗ sl) ∗ ((base ↦ᵣ buf.take off) ∗ ((base + BitVec.ofNat 64 (off + len)) ↦ᵣ buf.drop (off + len))) := (sepConj_assoc _ _ _).symm
    _ = (base ↦ᵣ buf) := by dsimp only [sl]; rw [pointsToBytesRO_dup, ← hsplit]
theorem holdsBytes_append {m : Memory} {addr : BitVec 64} {b1 b2 : List (BitVec 8)} {perm : Perm} :
    Obj.HoldsBytes m addr (b1 ++ b2) (fun _ => perm) ↔ Obj.HoldsBytes m addr b1 (fun _ => perm) ∧ Obj.HoldsBytes m (addr + BitVec.ofNat 64 b1.length) b2 (fun _ => perm) := by
  refine ⟨fun h => ⟨fun i hi => ?_, fun i hi => ?_⟩, fun ⟨h1, h2⟩ i hi => ?_⟩
  · have hcell := h i (by simp; omega); rwa [List.getElem_append_left hi] at hcell
  · have hcell := h (b1.length + i) (by simp; omega); rw [List.getElem_append_right (Nat.le_add_right _ _)] at hcell; simpa [BitVec.add_assoc, ← BitVec.ofNat_add] using hcell
  · by_cases hlt : i < b1.length
    · simpa [List.getElem_append_left hlt] using h1 i hlt
    · have hge := Nat.le_of_not_lt hlt; have hlt2 : i - b1.length < b2.length := (by simp at hi; omega)
      have haddr : addr + BitVec.ofNat 64 b1.length + BitVec.ofNat 64 (i - b1.length) = addr + BitVec.ofNat 64 i := by rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le hge]
      simpa [haddr, List.getElem_append_right hge] using h2 (i - b1.length) hlt2
/-- Lower any hook-free `SepWP prog target s P (sepPost R Q)` directly to `Steps Program.pureMem`. -/
theorem sepWP_to_pureMem_steps {prog : Program} {target : BitVec 64} {s : State} {P Q F : SepProp} {R : State → Prop}
    (hwp : SepWP prog target s P (sepPost R Q)) (hm : s.mem ⊨ P ∗ F) (hcode : prog.CodeLoaded s.mem)
    (hno_ext : ∀ pc, prog.externAt? pc = none) (h_svc : prog.svc = Syscall.standard := by rfl) :
    ∃ sf : State, Steps Program.pureMem s sf ∧ s.mem.KeepsFrozen sf.mem ∧ sf.pc = target ∧ sf.status = .Running ∧ R sf ∧ (sf.mem ⊨ Q ∗ F) := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hR, hent⟩ | ⟨_, hoom⟩⟩ := SepWP.elim hwp hm hcode
  · exact ⟨sf, Steps.toPureMem_of_no_extern hno_ext hsteps hrun h_svc, hsteps.keepsFrozen, hpc, hrun, hR, Satisfies.mono (sepConj_mono_left hent) hmf⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)
theorem SupportedOn.of_holdsBytes_rw0 {addr : BitVec 64} {bs : List (BitVec 8)} {m : Memory} (hbnd : addr.toNat + bs.length < 2 ^ 64) (h : Obj.HoldsBytes m addr bs (fun _ => .rw)) :
    SupportedOn 0#64 (fun k => addr.toNat ≤ k ∧ k < addr.toNat + bs.length) m (addr ↦ₛ bs) := by
  simpa [BitVec.zero_add, BitVec.ofNat_toNat] using ProofLib.SupportedOn.of_holdsBytes_rw (b := 0#64) (off := addr.toNat) hbnd (by simpa [BitVec.zero_add, BitVec.ofNat_toNat] using h)
theorem SupportedOn.of_holdsBytes_ro0 {addr : BitVec 64} {bs : List (BitVec 8)} {m : Memory} (hbnd : addr.toNat + bs.length < 2 ^ 64) (h : Obj.HoldsBytes m addr bs (fun _ => .rw)) :
    SupportedOn 0#64 (fun k => addr.toNat ≤ k ∧ k < addr.toNat + bs.length) m (|==> (addr ↦ᵣ bs)) := ProofLib.SupportedOn.mono (pointsToBytes_freeze_ro addr bs) (SupportedOn.of_holdsBytes_rw0 hbnd h)
theorem SupportedOn.of_holdsBytes_u64_0 {addr : BitVec 64} {w : BitVec 64} {m : Memory} (hbnd : addr.toNat + 8 < 2 ^ 64) (h : Obj.HoldsBytes m addr (Obj.bytesLE 8 w) (fun _ => .rw)) :
    SupportedOn 0#64 (fun k => addr.toNat ≤ k ∧ k < addr.toNat + 8) m (addr ↦₆₄ w) := by
  have h_eq : Obj.bytesLE 8 w = unpack64 w := rfl; rw [h_eq] at h
  have h0 := SupportedOn.of_holdsBytes_rw0 (by simpa [unpack64_length] using hbnd) h; rwa [unpack64_length, ← pointsTo64_eq_pointsToBytes addr w] at h0
theorem SupportedOn.of_holdsBytes_u64_ro0 {addr : BitVec 64} {w : BitVec 64} {m : Memory} (hbnd : addr.toNat + 8 < 2 ^ 64) (h : Obj.HoldsBytes m addr (Obj.bytesLE 8 w) (fun _ => .rw)) :
    SupportedOn 0#64 (fun k => addr.toNat ≤ k ∧ k < addr.toNat + 8) m (|==> (addr ↦₆₄ᵣ w)) := ProofLib.SupportedOn.mono (pointsTo64_freeze_ro addr w) (SupportedOn.of_holdsBytes_u64_0 hbnd h)
theorem SupportedOn.of_memRegion_rw0 {addr : BitVec 64} {len : Nat} {m : Memory}
    (hbnd : addr.toNat + len < 2 ^ 64)
    (hperm : ∀ a, InRegion addr len a → m.perm a = some .rw)
    (hnolf : ∀ a, InRegion addr len a → m.isLazyFree a = false) :
    SupportedOn 0#64 (fun k => addr.toNat ≤ k ∧ k < addr.toNat + len) m (memRegion addr len) := by
  have hrw : m.RW addr len := fun a ha =>
    Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hperm a ha, hnolf a ha⟩
  have hm : m ⊨ memRegion addr len := satisfies_memRegion m addr len hrw; rw [memRegion_eq_exists_bytes addr len (by omega), satisfies_sepExists] at hm
  obtain ⟨bs, hbs⟩ := hm; obtain ⟨rfl, hbs_sat⟩ := (satisfies_pure_sepConj _ _ _).mp hbs
  refine ProofLib.SupportedOn.mono (pointsToBytes_entails_memRegion addr bs) (ProofLib.SupportedOn.of_pointsToBytes hbs_sat fun a ha => ?_)
  unfold InRegion at ha; have := a.isLt; rw [BitVec.sub_zero]; rw [BitVec.toNat_sub] at ha; omega
theorem SupportedOn.sepConj_interval {lo1 hi1 lo2 hi2 lo hi : Nat} {m : Memory} {P Q : SepProp}
    (h1 : SupportedOn 0#64 (fun k => lo1 ≤ k ∧ k < hi1) m P) (h2 : SupportedOn 0#64 (fun k => lo2 ≤ k ∧ k < hi2) m Q)
    (hdisj : hi1 ≤ lo2 ∨ hi2 ≤ lo1) (hlo : lo ≤ lo1 ∧ lo ≤ lo2) (hhi : hi1 ≤ hi ∧ hi2 ≤ hi) : SupportedOn 0#64 (fun k => lo ≤ k ∧ k < hi) m (P ∗ Q) :=
  (ProofLib.SupportedOn.sepConj h1 h2 (by intro k hk1 hk2; omega)).widen (by intro k hk; omega)
theorem SupportedOn.bupd_intro {b : BitVec 64} {S : Nat → Prop} {m : Memory} {P : SepProp} (h : SupportedOn b S m P) : SupportedOn b S m (|==> P) := ProofLib.SupportedOn.mono (ProofLib.bupd_intro P) h
theorem SupportedOn.sepConj_bupd_interval {lo1 hi1 lo2 hi2 lo hi : Nat} {m : Memory} {P Q : SepProp}
    (h1 : SupportedOn 0#64 (fun k => lo1 ≤ k ∧ k < hi1) m (|==> P)) (h2 : SupportedOn 0#64 (fun k => lo2 ≤ k ∧ k < hi2) m (|==> Q))
    (hdisj : hi1 ≤ lo2 ∨ hi2 ≤ lo1) (hlo : lo ≤ lo1 ∧ lo ≤ lo2) (hhi : hi1 ≤ hi ∧ hi2 ≤ hi) : SupportedOn 0#64 (fun k => lo ≤ k ∧ k < hi) m (|==> (P ∗ Q)) :=
  ProofLib.SupportedOn.mono (bupd_sep (Entails.refl _) (Entails.refl _)) (SupportedOn.sepConj_interval h1 h2 hdisj hlo hhi)
theorem SupportedOn.satisfies_bupd {b : BitVec 64} {S : Nat → Prop} {m : Memory} {P : SepProp} (h : SupportedOn b S m (|==> P)) : m ⊨ P := (ProofLib.satisfies_bupd P m).mp h.satisfies
theorem SupportedOn.of_holdsBytes_words64_0 {addr : BitVec 64} {ws : List (BitVec 64)} {m : Memory}
    (hbnd : addr.toNat + 8 * ws.length < 2 ^ 64) (h : Obj.HoldsBytes m addr (ws.flatMap (Obj.bytesLE 8)) (fun _ => .rw)) :
    SupportedOn 0#64 (fun k => addr.toNat ≤ k ∧ k < addr.toNat + 8 * ws.length) m (addr ↦₆₄* ws) := by
  induction ws generalizing addr with
  | nil => simpa [pointsToWords64_nil] using SupportedOn.of_holdsBytes_rw0 (bs := []) (by simpa using hbnd) (fun _ hi => nomatch hi)
  | cons w rest ih =>
    simp only [List.flatMap_cons] at h; obtain ⟨hw, hrest⟩ := holdsBytes_append.mp h; have h8 : (Obj.bytesLE 8 w).length = 8 := (by simp [Obj.bytesLE])
    rw [h8] at hrest; simp only [List.length_cons] at hbnd; have hnext : (addr + 8#64).toNat = addr.toNat + 8 := (by have := addr.isLt; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    rw [pointsToWords64_cons]; exact SupportedOn.sepConj_interval (SupportedOn.of_holdsBytes_u64_0 (by omega) hw) (ih (addr := addr + 8#64) (by omega) hrest) (by omega) (by omega) (by simp only [List.length_cons]; omega)
theorem SupportedOn.of_holdsBytes_words64_ro0 {addr : BitVec 64} {ws : List (BitVec 64)} {m : Memory} (hbnd : addr.toNat + 8 * ws.length < 2 ^ 64) (h : Obj.HoldsBytes m addr (ws.flatMap (Obj.bytesLE 8)) (fun _ => .rw)) :
    SupportedOn 0#64 (fun k => addr.toNat ≤ k ∧ k < addr.toNat + 8 * ws.length) m (|==> (addr ↦₆₄ᵣ* ws)) := ProofLib.SupportedOn.mono (pointsToWords64_freeze_ro addr ws) (SupportedOn.of_holdsBytes_words64_0 hbnd h)
/-! ## Packed C-string table and auxiliary-vector lookup helpers -/
def cstrPrefixOff (strs : List (List (BitVec 8))) (k : Nat) : Nat := ((strs.take k).flatMap (· ++ [0#8])).length
private theorem foldl_cstr_len_eq_flatMap (strs : List (List (BitVec 8))) (acc : Nat) : strs.foldl (fun n s => n + s.length + 1) acc = acc + (strs.flatMap (· ++ [0#8])).length := by
  induction strs generalizing acc with | nil => simp | cons s rest ih => simp only [List.foldl_cons, List.flatMap_cons, List.length_append, List.length_singleton]; rw [ih]; omega
private theorem packCStringList_aux (base : BitVec 64) (l : List (List (BitVec 8))) (off : Nat) (accB : List (BitVec 8)) (accA : List (BitVec 64)) :
    l.foldl (fun (o, b, a) s => let entry := s ++ [0#8]; (o + entry.length, b ++ entry, a ++ [base + BitVec.ofNat 64 o])) (off, accB, accA) =
    (off + (l.flatMap (· ++ [0#8])).length, accB ++ l.flatMap (· ++ [0#8]), accA ++ List.ofFn (fun i : Fin l.length => base + BitVec.ofNat 64 (off + cstrPrefixOff l i.1))) := by
  induction l generalizing off accB accA with | nil => simp | cons s rest ih =>
    simp only [List.foldl_cons]; rw [ih (off + (s ++ [0#8]).length) (accB ++ (s ++ [0#8])) (accA ++ [base + BitVec.ofNat 64 off])]
    refine Prod.ext (by simp; omega) (Prod.ext (by simp [List.append_assoc]) ?_); dsimp only; rw [List.ofFn_succ, List.append_assoc]
    congr 1; simp only [List.singleton_append, List.cons.injEq]; exact ⟨by simp [cstrPrefixOff], by congr 1; funext j; congr 2; simp [cstrPrefixOff]; omega⟩
/-- Exact characterization of `packCStringList`: end offset, flat byte payload, and `List.ofFn` pointer array. -/
theorem packCStringList_spec (base : BitVec 64) (strs : List (List (BitVec 8))) :
    packCStringList base strs = ((strs.flatMap (· ++ [0#8])).length, strs.flatMap (· ++ [0#8]), List.ofFn (fun i : Fin strs.length => base + BitVec.ofNat 64 (cstrPrefixOff strs i.1))) := by
  simpa [packCStringList] using packCStringList_aux base strs 0 [] []
theorem flatMap_cstr_drop_prefix (strs : List (List (BitVec 8))) {k : Nat} (hk : k < strs.length) :
    (strs.flatMap (· ++ [0#8])).drop (cstrPrefixOff strs k) = (strs[k] ++ [0#8]) ++ (strs.drop (k + 1)).flatMap (· ++ [0#8]) := by
  have hsplit : strs = strs.take k ++ strs[k] :: strs.drop (k + 1) := (by rw [List.getElem_cons_drop, List.take_append_drop])
  have hfm := congrArg (fun l : List (List (BitVec 8)) => l.flatMap (· ++ [0#8])) hsplit
  simp only [List.flatMap_append, List.flatMap_cons] at hfm; rw [hfm]; unfold cstrPrefixOff; rw [List.drop_left' rfl, List.append_assoc]
def mkFixedAuxvEntries (img : ElfImage) (inputs : ProcessInputs) (platformAddr randomAddr execfnAddr : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(AuxvTag.phdr, img.phdrVaddr), (AuxvTag.phent, BitVec.ofNat 64 img.phent), (AuxvTag.phnum, BitVec.ofNat 64 img.phnum), (AuxvTag.pagesz, 4096#64), (AuxvTag.base, 0#64), (AuxvTag.flags, 0#64),
   (AuxvTag.entry, img.entry), (AuxvTag.uid, inputs.init.auxv.uid), (AuxvTag.euid, inputs.init.auxv.euid), (AuxvTag.gid, inputs.init.auxv.gid), (AuxvTag.egid, inputs.init.auxv.egid), (AuxvTag.platform, platformAddr),
   (AuxvTag.hwcap, inputs.init.auxv.hwcap), (AuxvTag.clktck, 100#64), (AuxvTag.secure, inputs.init.auxv.secure), (AuxvTag.random, randomAddr), (AuxvTag.hwcap2, inputs.init.auxv.hwcap2), (AuxvTag.execfn, execfnAddr)]
def mkAuxvEntries (img : ElfImage) (inputs : ProcessInputs) (platformAddr randomAddr execfnAddr : BitVec 64) : List (BitVec 64 × BitVec 64) := mkFixedAuxvEntries img inputs platformAddr randomAddr execfnAddr ++ inputs.init.auxv.extra
theorem encodeAuxvBytes_eq_flatMap_bytesLE (pairs : List (BitVec 64 × BitVec 64)) : encodeAuxvBytes pairs = ((pairs ++ [(AuxvTag.null, 0#64)]).flatMap fun (t, v) => [t, v]).flatMap (Obj.bytesLE 8) := rfl
theorem flatMap_bytesLE8_length (ws : List (BitVec 64)) : (ws.flatMap (Obj.bytesLE 8)).length = 8 * ws.length := by
  induction ws with | nil => rfl | cons w rest ih => have h8 : (Obj.bytesLE 8 w).length = 8 := (by simp [Obj.bytesLE]); simp only [List.flatMap_cons, List.length_append, List.length_cons, ih, h8]; omega
theorem encodeAuxvBytes_length (pairs : List (BitVec 64 × BitVec 64)) : (encodeAuxvBytes pairs).length = 16 * (pairs.length + 1) := by
  rw [encodeAuxvBytes_eq_flatMap_bytesLE, flatMap_bytesLE8_length]
  have hp : ∀ ps : List (BitVec 64 × BitVec 64), (ps.flatMap fun (t, v) => [t, v]).length = 2 * ps.length := (by intro ps; induction ps with | nil => rfl | cons p rs ih => rcases p with ⟨t, v⟩; simp [ih]; omega); rw [hp]; simp; omega
theorem mkAuxvEntries_wf (img : ElfImage) {inputs : ProcessInputs} (hx : AuxvValid inputs.init.auxv) (platformAddr randomAddr execfnAddr : BitVec 64) :
    let entries := mkAuxvEntries img inputs platformAddr randomAddr execfnAddr
    entries.length = 18 + inputs.init.auxv.extra.length ∧ entries.length ≤ 24 ∧ (∀ t v, (t, v) ∈ entries → t ≠ AuxvTag.null ∧ (t = AuxvTag.random → v = randomAddr)) := by
  dsimp only; have hextra := hx.extra_le; have hfresh := hx.extra_fresh.2
  refine ⟨by simp [mkAuxvEntries, mkFixedAuxvEntries]; omega, by simp [mkAuxvEntries, mkFixedAuxvEntries]; omega, fun t v hmem => ?_⟩
  simp only [mkAuxvEntries, mkFixedAuxvEntries, List.mem_append] at hmem; rcases hmem with hfix | hext
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hfix
    rcases hfix with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, fun h => by cases h; try rfl⟩
  · obtain ⟨hnotfix, hnonull⟩ := hfresh (t, v) hext; exact ⟨hnonull, fun hr => False.elim (hnotfix (by subst hr; dsimp only; decide))⟩
/-- Split `mkAuxvEntries` around `(AuxvTag.random, randomAddr)` for `MallocngStartupInputs`. -/
theorem mkAuxvEntries_split_random (img : ElfImage) {inputs : ProcessInputs} (hx : AuxvValid inputs.auxv)
    (platformAddr randomAddr execfnAddr : BitVec 64) :
    ∃ prePairs sufPairs : List (BitVec 64 × BitVec 64),
      mkAuxvEntries img inputs platformAddr randomAddr execfnAddr =
        prePairs ++ [(AuxvTag.random, randomAddr)] ++ sufPairs ∧
      prePairs.length + sufPairs.length = 17 + inputs.auxv.extra.length ∧
      prePairs.length + sufPairs.length ≤ 64 ∧
      (∀ e ∈ prePairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random) ∧
      (∀ e ∈ sufPairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random) := by
  let prePairs : List (BitVec 64 × BitVec 64) :=
    [(AuxvTag.phdr, img.phdrVaddr), (AuxvTag.phent, BitVec.ofNat 64 img.phent),
     (AuxvTag.phnum, BitVec.ofNat 64 img.phnum), (AuxvTag.pagesz, 4096#64),
     (AuxvTag.base, 0#64), (AuxvTag.flags, 0#64), (AuxvTag.entry, img.entry),
     (AuxvTag.uid, inputs.auxv.uid), (AuxvTag.euid, inputs.auxv.euid),
     (AuxvTag.gid, inputs.auxv.gid), (AuxvTag.egid, inputs.auxv.egid),
     (AuxvTag.platform, platformAddr), (AuxvTag.hwcap, inputs.auxv.hwcap),
     (AuxvTag.clktck, 100#64), (AuxvTag.secure, inputs.auxv.secure)]
  let sufPairs : List (BitVec 64 × BitVec 64) :=
    [(AuxvTag.hwcap2, inputs.auxv.hwcap2), (AuxvTag.execfn, execfnAddr)] ++ inputs.auxv.extra
  have hextra := hx.extra_le
  have hfresh := hx.extra_fresh.2
  refine ⟨prePairs, sufPairs, rfl, by simp [prePairs, sufPairs]; omega,
    by simp [prePairs, sufPairs]; omega, ?_, ?_⟩
  · intro e he
    simp only [prePairs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only; decide)
  · intro e he
    simp only [sufPairs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with (rfl | rfl) | hext
    · dsimp only; decide
    · dsimp only; decide
    · obtain ⟨hnotfix, hnonull⟩ := hfresh e hext
      exact ⟨hnonull, fun hr => hnotfix (by rw [hr]; decide)⟩
/-- First-match `AT_*` lookup on `mkAuxvEntries ++ tail` under `AuxvValid`. -/
theorem mkAuxvEntries_find? (img : ElfImage) {inputs : ProcessInputs} (hx : AuxvValid inputs.init.auxv) (platformAddr randomAddr execfnAddr : BitVec 64) (tail : List (BitVec 64 × BitVec 64) := []) :
    let xs := mkAuxvEntries img inputs platformAddr randomAddr execfnAddr ++ tail
    xs.find? (·.1 == AuxvTag.phdr) = some (AuxvTag.phdr, img.phdrVaddr) ∧ xs.find? (·.1 == AuxvTag.phent) = some (AuxvTag.phent, BitVec.ofNat 64 img.phent) ∧ xs.find? (·.1 == AuxvTag.phnum) = some (AuxvTag.phnum, BitVec.ofNat 64 img.phnum) ∧
    xs.find? (·.1 == AuxvTag.pagesz) = some (AuxvTag.pagesz, 4096#64) ∧ xs.find? (·.1 == AuxvTag.entry) = some (AuxvTag.entry, img.entry) ∧ xs.find? (·.1 == AuxvTag.uid) = some (AuxvTag.uid, inputs.init.auxv.uid) ∧
    xs.find? (·.1 == AuxvTag.euid) = some (AuxvTag.euid, inputs.init.auxv.uid) ∧ xs.find? (·.1 == AuxvTag.gid) = some (AuxvTag.gid, inputs.init.auxv.gid) ∧ xs.find? (·.1 == AuxvTag.egid) = some (AuxvTag.egid, inputs.init.auxv.gid) ∧
    xs.find? (·.1 == AuxvTag.platform) = some (AuxvTag.platform, platformAddr) ∧ xs.find? (·.1 == AuxvTag.hwcap) = some (AuxvTag.hwcap, inputs.init.auxv.hwcap) ∧ xs.find? (·.1 == AuxvTag.secure) = some (AuxvTag.secure, 0#64) ∧
    xs.find? (·.1 == AuxvTag.random) = some (AuxvTag.random, randomAddr) ∧ xs.find? (·.1 == AuxvTag.hwcap2) = some (AuxvTag.hwcap2, inputs.init.auxv.hwcap2) ∧ xs.find? (·.1 == AuxvTag.execfn) = some (AuxvTag.execfn, execfnAddr) := by
  dsimp only [mkAuxvEntries, mkFixedAuxvEntries]; rw [← hx.no_setugid.1, ← hx.no_setugid.2, hx.nonsecure]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
def auxvScan38 (entries : List (BitVec 64 × BitVec 64)) : List (BitVec 64) := entries.foldl (fun acc (t, v) => if t.toNat < 38 then acc.set t.toNat v else acc) (List.replicate 38 0#64)
private theorem foldl_auxvScan38_preserve (extra : List (BitVec 64 × BitVec 64)) (acc : List (BitVec 64)) {k : Nat} (hk : k < 38) (hne : ∀ e ∈ extra, e.1 ≠ BitVec.ofNat 64 k) :
    (extra.foldl (fun a (t, v) => if t.toNat < 38 then a.set t.toNat v else a) acc)[k]? = acc[k]? := by
  induction extra generalizing acc with | nil => rfl | cons e rest ih =>
    rcases e with ⟨t, v⟩; simp only [List.foldl_cons]; rw [ih _ (fun x hx => hne x (List.mem_cons_of_mem _ hx))]; split
    · exact List.getElem?_set_ne fun heq => hne (t, v) (List.mem_cons_self ..) (BitVec.eq_of_toNat_eq (by dsimp only; rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]))
    · rfl
/-- Exact 38-word `aux[0..37]` array values produced by scanning `mkAuxvEntries` under `AuxvValid`. -/
theorem auxvScan38_mkAuxvEntries (img : ElfImage) {inputs : ProcessInputs} (hx : AuxvValid inputs.init.auxv) (platformAddr randomAddr execfnAddr : BitVec 64) :
    let aux := auxvScan38 (mkAuxvEntries img inputs platformAddr randomAddr execfnAddr)
    aux.length = 38 ∧ aux[3]? = some img.phdrVaddr ∧ aux[4]? = some (BitVec.ofNat 64 img.phent) ∧ aux[5]? = some (BitVec.ofNat 64 img.phnum) ∧ aux[6]? = some 4096#64 ∧
    aux[9]? = some img.entry ∧ aux[11]? = some inputs.init.auxv.uid ∧ aux[12]? = some inputs.init.auxv.uid ∧ aux[13]? = some inputs.init.auxv.gid ∧ aux[14]? = some inputs.init.auxv.gid ∧
    aux[15]? = some platformAddr ∧ aux[16]? = some inputs.init.auxv.hwcap ∧ aux[23]? = some 0#64 ∧ aux[25]? = some randomAddr ∧ aux[26]? = some inputs.init.auxv.hwcap2 ∧ aux[31]? = some execfnAddr := by
  dsimp only; have hlen : ∀ (l : List (BitVec 64 × BitVec 64)) (a : List (BitVec 64)), (l.foldl (fun acc (t, v) => if t.toNat < 38 then acc.set t.toNat v else acc) a).length = a.length := by
    intro l; induction l with | nil => simp | cons e rs ih => intro a; rcases e with ⟨t, v⟩; simp only [List.foldl_cons]; split <;> simp [ih]
  let fixed := auxvScan38 (mkFixedAuxvEntries img inputs platformAddr randomAddr execfnAddr)
  have hfixed : fixed = [0#64, 0#64, 0#64, img.phdrVaddr, BitVec.ofNat 64 img.phent, BitVec.ofNat 64 img.phnum, 4096#64, 0#64, 0#64, img.entry,
      0#64, inputs.init.auxv.uid, inputs.init.auxv.euid, inputs.init.auxv.gid, inputs.init.auxv.egid, platformAddr, inputs.init.auxv.hwcap, 100#64, 0#64, 0#64, 0#64, 0#64,
      0#64, inputs.init.auxv.secure, 0#64, randomAddr, inputs.init.auxv.hwcap2, 0#64, 0#64, 0#64, 0#64, execfnAddr, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] := by
    simp [fixed, auxvScan38, mkFixedAuxvEntries, AuxvTag.phdr, AuxvTag.phent, AuxvTag.phnum, AuxvTag.pagesz, AuxvTag.base, AuxvTag.flags, AuxvTag.entry,
      AuxvTag.uid, AuxvTag.euid, AuxvTag.gid, AuxvTag.egid, AuxvTag.platform, AuxvTag.hwcap, AuxvTag.clktck, AuxvTag.secure, AuxvTag.random, AuxvTag.hwcap2, AuxvTag.execfn]
  have hpres : ∀ (k : Nat), k < 38 → BitVec.ofNat 64 k ∈ AuxvTag.fixedTags → (auxvScan38 (mkAuxvEntries img inputs platformAddr randomAddr execfnAddr))[k]? = fixed[k]? :=
    fun k hk hfix => by unfold auxvScan38 mkAuxvEntries; rw [List.foldl_append]; exact foldl_auxvScan38_preserve inputs.init.auxv.extra _ hk fun e he heq => (hx.extra_fresh.2 e he).1 (heq ▸ hfix)
  refine ⟨by unfold auxvScan38; rw [hlen]; simp, ?_⟩
  rw [hpres 3 (by omega) (by decide), hpres 4 (by omega) (by decide), hpres 5 (by omega) (by decide), hpres 6 (by omega) (by decide), hpres 9 (by omega) (by decide), hpres 11 (by omega) (by decide),
      hpres 12 (by omega) (by decide), hpres 13 (by omega) (by decide), hpres 14 (by omega) (by decide), hpres 15 (by omega) (by decide), hpres 16 (by omega) (by decide),
      hpres 23 (by omega) (by decide), hpres 25 (by omega) (by decide), hpres 26 (by omega) (by decide), hpres 31 (by omega) (by decide), hfixed, ← hx.no_setugid.1, ← hx.no_setugid.2, hx.nonsecure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
/-! ## Initial stack and `ElfImage.loadState` unpacking -/
private theorem regionsDisjointAndAligned_valid : ∀ {rs : List Snapshot.Region}, regionsDisjointAndAligned rs = true → ∀ r ∈ rs, regionAlignedValid r = true
  | [], _, _, hr => nomatch hr
  | [r0], h, r, hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  | r1 :: r2 :: rest, h, r, hr => by simp only [regionsDisjointAndAligned, Bool.and_eq_true] at h; exact (List.mem_cons.mp hr).elim (· ▸ h.1.1) (regionsDisjointAndAligned_valid h.2 r)
/-- Segment bounds, `phent = 56`, and `brkStart` alignment implied by `ElfImage.WellFormed`. -/
theorem wellFormed_segments_bounds {img : ElfImage} (hwf : img.WellFormed = true) :
    img.phent = 56 ∧ img.brkStart.toNat % 4096 = 0 ∧ 4096 ≤ img.brkStart.toNat ∧ img.segments.all (Snapshot.Below img.brkStart) = true ∧
    ∀ r ∈ img.segments, 4096 ≤ r.start.toNat ∧ 0 < r.bytes.length ∧ r.start.toNat + r.bytes.length ≤ img.brkStart.toNat := by
  unfold ElfImage.WellFormed at hwf; simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hwf
  rcases hwf with ⟨⟨⟨⟨⟨hne, hphent⟩, hdisj⟩, _⟩, hbrkmod⟩, hall⟩
  have hseg : ∀ r ∈ img.segments, 4096 ≤ r.start.toNat ∧ 0 < r.bytes.length ∧ r.start.toNat + r.bytes.length ≤ img.brkStart.toNat := fun r hr => by
    have hrv := regionsDisjointAndAligned_valid hdisj r hr; unfold regionAlignedValid at hrv; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hrv
    exact ⟨by have := hrv.1.1.1.1.1.1; dsimp [Obj.pageSize] at this; omega, hrv.1.1.1.1.2, hall r hr⟩
  have hbrk4096 : 4096 ≤ img.brkStart.toNat := by cases hs : img.segments with | nil => exact absurd hs hne | cons r0 _ => have ⟨h1, h2, h3⟩ := hseg r0 (hs ▸ List.mem_cons_self ..); omega
  exact ⟨hphent, hbrkmod, hbrk4096, List.all_eq_true.mpr fun r hr => by simp [Snapshot.Below, hall r hr], hseg⟩
private theorem cellAt_eq_none_of_disjoint {rs : List Snapshot.Region} {a : BitVec 64}
    (h : ∀ r ∈ rs, r.start.toNat + r.bytes.length ≤ 2 ^ 64 ∧ ¬ (r.start.toNat ≤ a.toNat ∧ a.toNat < r.start.toNat + r.bytes.length)) : Snapshot.cellAt rs a = none := by
  unfold Snapshot.cellAt; rw [List.findSome?_eq_none_iff]; intro r hr; obtain ⟨hw, hnot⟩ := h r hr; dsimp only; split
  · rename_i hlt; exfalso; apply hnot; have := a.isLt; have := r.start.isLt; rw [BitVec.toNat_sub] at hlt; omega
  · rfl
abbrev platformCStringBytes : List (BitVec 8) := [0x61#8, 0x61#8, 0x72#8, 0x63#8, 0x68#8, 0x36#8, 0x34#8, 0x00#8]
/-- Deterministic initial stack layout computed by `buildInitialStack` for `(img, inputs)`. -/
structure StackLayout where
  sp0           : BitVec 64
  infoPadLen    : Nat
  randomAddr    : BitVec 64
  platformAddr  : BitVec 64
  argvBase      : BitVec 64
  argvAddrs     : List (BitVec 64)
  envpBase      : BitVec 64
  envpAddrs     : List (BitVec 64)
  execfnAddr    : BitVec 64
  upperStrBytes : List (BitVec 8)
  auxvEntries   : List (BitVec 64 × BitVec 64)

namespace StackLayout
def of (img : ElfImage) (inputs : ProcessInputs) : StackLayout :=
  let execfnBytes := inputs.execfn ++ [0#8]; let topSentinelBytes := List.replicate 8 0#8
  let upperRawLen := platformCStringBytes.length + inputs.argv.foldl (fun n s => n + s.length + 1) 0 +
    inputs.envp.foldl (fun n s => n + s.length + 1) 0 + execfnBytes.length + topSentinelBytes.length
  let upperAlignedLen := alignUp16 upperRawLen; let infoPadLen := upperAlignedLen - upperRawLen
  let infoBaseNat := inputs.init.stackTop.toNat - (16 + upperAlignedLen)
  let randomAddr := BitVec.ofNat 64 infoBaseNat; let platformAddr := randomAddr + BitVec.ofNat 64 (16 + infoPadLen)
  let argvBase := platformAddr + BitVec.ofNat 64 platformCStringBytes.length; let p1 := packCStringList argvBase inputs.argv
  let envpBase := argvBase + BitVec.ofNat 64 p1.1; let p2 := packCStringList envpBase inputs.envp
  let execfnAddr := envpBase + BitVec.ofNat 64 p2.1; let auxvEntries := mkAuxvEntries img inputs platformAddr randomAddr execfnAddr
  let unpaddedWords := ([BitVec.ofNat 64 inputs.argv.length] ++ p1.2.2 ++ [0#64] ++ p2.2.2 ++ [0#64]) ++
    ((auxvEntries ++ [(AuxvTag.null, 0#64)]).flatMap fun (t, v) => [t, v])
  let tableWords := if unpaddedWords.length % 2 == 0 then unpaddedWords else unpaddedWords ++ [0#64]
  let sp0 := BitVec.ofNat 64 (infoBaseNat - (tableWords.flatMap (Obj.bytesLE 8)).length)
  { sp0, infoPadLen, randomAddr, platformAddr, argvBase, argvAddrs := p1.2.2, envpBase, envpAddrs := p2.2.2,
    execfnAddr, upperStrBytes := p1.2.1 ++ p2.2.1 ++ execfnBytes ++ topSentinelBytes, auxvEntries }
abbrev argc (L : StackLayout) : Nat := L.argvAddrs.length
abbrev envc (L : StackLayout) : Nat := L.envpAddrs.length
abbrev argvTableAddr (L : StackLayout) : BitVec 64 := L.sp0 + 8#64
abbrev envpTableAddr (L : StackLayout) : BitVec 64 := L.sp0 + BitVec.ofNat 64 (8 * (L.argc + 2))
abbrev auxvTableAddr (L : StackLayout) : BitVec 64 := L.sp0 + BitVec.ofNat 64 (8 * (L.argc + L.envc + 3))
abbrev auxvPairs (L : StackLayout) : List (BitVec 64 × BitVec 64) := L.auxvEntries ++ [(AuxvTag.null, 0#64)]
end StackLayout
/-- Complete initial-state and initial-stack characterization for `img.loadState inputs = .ok s0`. -/
structure InitialStackInfo (img : ElfImage) (inputs : ProcessInputs) (s0 : State) : Prop where
  s0_regs       : s0.regs = RegFile.empty
  s0_vregs      : s0.vregs = VRegFile.empty
  s0_sp         : s0.sp = (StackLayout.of img inputs).sp0
  s0_pc         : s0.pc = img.entry
  s0_pstate     : s0.pstate = PState.zero
  s0_status     : s0.status = .Running
  s0_tpidrEl0   : s0.tpidrEl0 = 0#64
  s0_brk        : s0.brk = img.brkStart
  s0_brkStart   : s0.brkStart = img.brkStart
  s0_fs         : s0.fs = initFsState inputs
  s0_trace      : s0.trace = []
  s0_oracle     : s0.oracle = inputs.init.oracle
  s0_oracleIdx    : s0.oracleIdx = 0
  s0_exclFails    : s0.exclFails = inputs.init.oracle.exclFails
  s0_sigActions   : s0.sigActions = fun _ => {}
  s0_sigAltStack  : s0.sigAltStack = {}
  s0_physMemAvail : s0.physMemAvail = inputs.init.physMemAvail
  sp0_align16     : (StackLayout.of img inputs).sp0.toNat % 16 = 0
  random_align16  : (StackLayout.of img inputs).randomAddr.toNat % 16 = 0
  stackTop_align  : inputs.init.stackTop.toNat % Obj.pageSize = 0 ∧ inputs.init.stackTop.toNat % 16 = 0 ∧ inputs.init.stackTop.toNat ≤ TASK_SIZE
  stackBase_floor : STACK_BASE_MIN ≤ inputs.init.stackTop.toNat - inputs.init.stackSize
  sp0_headroom    : inputs.init.stackTop.toNat - inputs.init.stackSize + inputs.init.stackSize / 2 ≤ (StackLayout.of img inputs).sp0.toNat ∧ inputs.init.stackTop.toNat - inputs.init.stackSize + 262144 ≤ (StackLayout.of img inputs).sp0.toNat
  argc_bounds     : 1 ≤ inputs.argv.length ∧ inputs.argv.length < 2 ^ 31 ∧ inputs.envp.length < 2 ^ 31
  argvAddrs_eq    : (StackLayout.of img inputs).argvAddrs = List.ofFn (fun i : Fin inputs.argv.length => (StackLayout.of img inputs).argvBase + BitVec.ofNat 64 (cstrPrefixOff inputs.argv i.1))
  envpAddrs_eq    : (StackLayout.of img inputs).envpAddrs = List.ofFn (fun i : Fin inputs.envp.length => (StackLayout.of img inputs).envpBase + BitVec.ofNat 64 (cstrPrefixOff inputs.envp i.1))
  upperStr_eq     : (StackLayout.of img inputs).upperStrBytes = inputs.argv.flatMap (· ++ [0#8]) ++ inputs.envp.flatMap (· ++ [0#8]) ++ (inputs.execfn ++ [0#8]) ++ List.replicate 8 0#8
  auxvEntries_eq  : (StackLayout.of img inputs).auxvEntries = mkAuxvEntries img inputs (StackLayout.of img inputs).platformAddr (StackLayout.of img inputs).randomAddr (StackLayout.of img inputs).execfnAddr
  addrs_nat       : let L := StackLayout.of img inputs
    L.argvTableAddr.toNat = L.sp0.toNat + 8 ∧ L.envpTableAddr.toNat = L.sp0.toNat + 8 * (inputs.argv.length + 2) ∧ L.auxvTableAddr.toNat = L.sp0.toNat + 8 * (inputs.argv.length + inputs.envp.length + 3) ∧
    L.auxvTableAddr.toNat + 16 * (L.auxvEntries.length + 1) ≤ L.randomAddr.toNat ∧ L.platformAddr.toNat = L.randomAddr.toNat + 16 + L.infoPadLen ∧ L.argvBase.toNat = L.platformAddr.toNat + 8 ∧
    L.envpBase.toNat = L.argvBase.toNat + (inputs.argv.flatMap (· ++ [0#8])).length ∧ L.execfnAddr.toNat = L.envpBase.toNat + (inputs.envp.flatMap (· ++ [0#8])).length ∧ L.argvBase.toNat + L.upperStrBytes.length = inputs.init.stackTop.toNat
  s0_perm_rw_below_sp0 : ∀ a : BitVec 64, inputs.init.stackTop.toNat - inputs.init.stackSize ≤ a.toNat → a.toNat < (StackLayout.of img inputs).sp0.toNat → s0.mem.perm a = some .rw
  s0_isLazyFree : ∀ a : BitVec 64, s0.mem.isLazyFree a = false
  s0_unmapped_heap : ∀ a : BitVec 64, img.brkStart.toNat ≤ a.toNat → a.toNat < inputs.init.stackTop.toNat - inputs.init.stackSize → s0.mem.perm a = none
  s0_mapped_iff : ∀ a : BitVec 64, (s0.mem.perm a).mapped = true → (4096 ≤ a.toNat ∧ a.toNat < img.brkStart.toNat) ∨ (inputs.init.stackTop.toNat - inputs.init.stackSize ≤ a.toNat ∧ a.toNat < inputs.init.stackTop.toNat)
  holds_argc     : Obj.HoldsBytes s0.mem (StackLayout.of img inputs).sp0 (Obj.bytesLE 8 (BitVec.ofNat 64 inputs.argv.length)) (fun _ => .rw)
  holds_argv     : Obj.HoldsBytes s0.mem (StackLayout.of img inputs).argvTableAddr (((StackLayout.of img inputs).argvAddrs ++ [0#64]).flatMap (Obj.bytesLE 8)) (fun _ => .rw)
  holds_envp     : Obj.HoldsBytes s0.mem (StackLayout.of img inputs).envpTableAddr (((StackLayout.of img inputs).envpAddrs ++ [0#64]).flatMap (Obj.bytesLE 8)) (fun _ => .rw)
  holds_auxv     : Obj.HoldsBytes s0.mem (StackLayout.of img inputs).auxvTableAddr (encodeAuxvBytes (StackLayout.of img inputs).auxvEntries) (fun _ => .rw)
  holds_random   : Obj.HoldsBytes s0.mem (StackLayout.of img inputs).randomAddr inputs.init.auxv.randomBytes (fun _ => .rw)
  holds_platform : Obj.HoldsBytes s0.mem (StackLayout.of img inputs).platformAddr platformCStringBytes (fun _ => .rw)
  holds_upperStr : Obj.HoldsBytes s0.mem (StackLayout.of img inputs).argvBase (StackLayout.of img inputs).upperStrBytes (fun _ => .rw)
private theorem mapZero_perm (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.mapZero base len).perm a = if (a - base).toNat < len && !(m.perm a).mapped then some Perm.rw else m.perm a := by
  conv => lhs; unfold Memory.perm Memory.mapZero; dsimp only
  cases ((a - base).toNat < len && !(m.perm a).mapped) <;> rfl
private theorem stackRegion_mem_props {img : ElfImage} {sp0 stackTop : BitVec 64} {stackSize : Nat} {stackBytes : List (BitVec 8)}
    (hwf : img.WellFormed = true) (hbrk : img.brkStart.toNat ≤ stackTop.toNat - stackSize) (hlo : stackTop.toNat - stackSize ≤ sp0.toNat)
    (hhi : sp0.toNat + stackBytes.length = stackTop.toNat) (htop : stackTop.toNat ≤ TASK_SIZE) :
    let sr : Snapshot.Region := { start := sp0, perm := Perm.rw, bytes := stackBytes }
    let m0 := (Memory.mk (Snapshot.loadCellAt (img.segments ++ [sr]))).mapZero (BitVec.ofNat 64 (stackTop.toNat - stackSize)) stackSize
    (∀ a : BitVec 64, stackTop.toNat - stackSize ≤ a.toNat → a.toNat < sp0.toNat → m0.perm a = some .rw) ∧
    (∀ a : BitVec 64, img.brkStart.toNat ≤ a.toNat → a.toNat < stackTop.toNat - stackSize → m0.perm a = none) ∧
    (∀ a : BitVec 64, (m0.perm a).mapped = true → (4096 ≤ a.toNat ∧ a.toNat < img.brkStart.toNat) ∨ (stackTop.toNat - stackSize ≤ a.toNat ∧ a.toNat < stackTop.toNat)) ∧
    Obj.HoldsBytes m0 sp0 stackBytes (fun _ => .rw) := by
  have ⟨_, _, hbrk_lo, _, hseg_all⟩ := wellFormed_segments_bounds hwf; have htop48 : stackTop.toNat ≤ 2 ^ 48 := htop; let sr : Snapshot.Region := { start := sp0, perm := Perm.rw, bytes := stackBytes }
  have hbase_none : ∀ a : BitVec 64, ¬ (4096 ≤ a.toNat ∧ a.toNat < img.brkStart.toNat) → ¬ (sp0.toNat ≤ a.toNat ∧ a.toNat < stackTop.toNat) →
      (Memory.mk (Snapshot.loadCellAt (img.segments ++ [sr]))).perm a = none := fun a hni hns => by
    rw [Snapshot.perm_loadCellAt]
    have hc : Snapshot.cellAt (img.segments ++ [sr]) a = none := cellAt_eq_none_of_disjoint fun r hr => by
      rcases List.mem_append.mp hr with hseg | hsr
      · have ⟨h1, _, h3⟩ := hseg_all r hseg; exact ⟨by omega, by omega⟩
      · simp only [List.mem_singleton] at hsr; subst hsr; dsimp only [sr]; exact ⟨by omega, by omega⟩
    simp [Memory.perm, hc]
  refine ⟨fun a ha1 ha2 => ?_, fun a ha1 ha2 => ?_, fun a hmap => ?_, ?_⟩
  · rw [mapZero_perm, hbase_none a (by omega) (by omega)]; have := a.isLt; simp [Option.mapped]; omega
  · rw [mapZero_perm, hbase_none a (by omega) (by omega)]; have := a.isLt; simp; omega
  · rw [mapZero_perm] at hmap; split at hmap
    · rename_i hcond; simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond; have hlt := hcond.1; have := a.isLt; rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at hlt; right; omega
    · by_cases h1 : 4096 ≤ a.toNat ∧ a.toNat < img.brkStart.toNat
      · exact Or.inl h1
      · by_cases h2 : sp0.toNat ≤ a.toNat ∧ a.toNat < stackTop.toNat; · right; omega
        · rw [hbase_none a h1 h2] at hmap; cases hmap
  · have hk : img.segments.length < (img.segments ++ [sr]).length := by simp
    have hpre : ((img.segments ++ [sr]).take img.segments.length).all (Snapshot.Below (img.segments ++ [sr])[img.segments.length].start) = true := by
      rw [List.take_left, List.getElem_append_right (Nat.le_refl _)]; simp only [Nat.sub_self, List.getElem_cons_zero, sr, List.all_eq_true, Snapshot.Below, decide_eq_true_eq]
      intro r hr; have ⟨_, _, h3⟩ := hseg_all r hr; omega
    have hwrap : (img.segments ++ [sr])[img.segments.length].start.toNat + (img.segments ++ [sr])[img.segments.length].bytes.length ≤ 2 ^ 64 := by
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero, sr]; omega
    have hbs : ((img.segments ++ [sr])[img.segments.length].bytes.drop 0).take stackBytes.length = stackBytes := by simp [List.getElem_append_right (Nat.le_refl _), sr]
    have hreg := Snapshot.holdsBytes_of_loadRegion_slice (img.segments ++ [sr]) img.segments.length hk hpre hwrap 0 stackBytes hbs
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero, sr] at hreg
    rw [show sp0 + BitVec.ofNat 64 0 = sp0 from BitVec.add_zero sp0] at hreg; exact holdsBytes_mapZero hreg
/-- Unpack `img.loadState inputs = .ok s0` into `InitialStackInfo img inputs s0`. -/
theorem loadState_initialStackInfo {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (hwf : img.WellFormed = true) (hvalid : inputs.Valid) (hbrk : img.brkStart.toNat ≤ inputs.init.stackTop.toNat - inputs.init.stackSize)
    (hload : img.loadState inputs = .ok s0) : InitialStackInfo img inputs s0 := by
  rcases hvalid with ⟨ha, ⟨hx, hs⟩, hfs⟩; let L := StackLayout.of img inputs
  have hr16 : (inputs.init.auxv.randomBytes.length != 16) = false := bne_eq_false_iff_eq.mpr hx.random16
  have hanul : (inputs.argv.any (·.contains 0#8)) = false := Bool.eq_false_iff.mpr fun h => by
    obtain ⟨s, hm, hc⟩ := List.any_eq_true.mp h; exact ha.no_nul.1 s hm (List.contains_iff_mem.mp hc)
  have henul : (inputs.envp.any (·.contains 0#8)) = false := Bool.eq_false_iff.mpr fun h => by
    obtain ⟨s, hm, hc⟩ := List.any_eq_true.mp h; exact ha.no_nul.2.1 s hm (List.contains_iff_mem.mp hc)
  have hxnul : inputs.execfn.contains 0#8 = false := Bool.eq_false_iff.mpr fun hc => ha.no_nul.2.2 (List.contains_iff_mem.mp hc)
  have hpage : Obj.pageSize = 4096 := rfl; have hfloor : 524288 ≤ inputs.init.stackSize := by have := hs.size_floor; unfold STK_LIM at this; omega
  have halign_chk : (inputs.init.stackTop.toNat % Obj.pageSize != 0 || inputs.init.stackSize == 0 || inputs.init.stackSize % Obj.pageSize != 0) = false := by
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne]; exact ⟨⟨hs.top_aligned.1, by omega⟩, hs.size_aligned.1⟩
  have hfold_eq : ∀ l : List (List (BitVec 8)), l.foldl (fun n s => n + (s.length + 1)) 0 = (l.flatMap (· ++ [0#8])).length := fun l => by
    simp only [← Nat.add_assoc, foldl_cstr_len_eq_flatMap, Nat.zero_add]
  have harg_lim := hs.argLimit_le_quarter; have harg_cap : argLimit inputs.init.stackSize ≤ 6291456 := by unfold argLimit ARG_MAX STK_LIM; omega
  have harg_tot := ha.total; unfold argBytes at harg_tot; rw [hfold_eq inputs.argv, hfold_eq inputs.envp] at harg_tot
  let upperRaw := platformCStringBytes.length + inputs.argv.foldl (fun n s => n + s.length + 1) 0 +
    inputs.envp.foldl (fun n s => n + s.length + 1) 0 + (inputs.execfn ++ [0#8]).length + (List.replicate 8 0#8).length
  have hraw_len : upperRaw = 16 + (inputs.argv.flatMap (· ++ [0#8])).length + (inputs.envp.flatMap (· ++ [0#8])).length + (inputs.execfn.length + 1) := by
    dsimp only [upperRaw]; rw [foldl_cstr_len_eq_flatMap inputs.argv 0, foldl_cstr_len_eq_flatMap inputs.envp 0]
    simp only [platformCStringBytes, List.length_cons, List.length_nil, List.length_append, List.length_replicate, Nat.zero_add]; omega
  have halign16 : upperRaw ≤ alignUp16 upperRaw ∧ alignUp16 upperRaw ≤ upperRaw + 15 ∧ alignUp16 upperRaw % 16 = 0 := by unfold alignUp16; omega
  let infoLen := 16 + alignUp16 upperRaw; let infoBaseNat := inputs.init.stackTop.toNat - infoLen
  have hp1 := packCStringList_spec L.argvBase inputs.argv; have hp2 := packCStringList_spec L.envpBase inputs.envp
  have hargv_eq : L.argvAddrs = List.ofFn (fun i : Fin inputs.argv.length => L.argvBase + BitVec.ofNat 64 (cstrPrefixOff inputs.argv i.1)) := by change (packCStringList L.argvBase inputs.argv).2.2 = _; rw [hp1]
  have henvp_eq : L.envpAddrs = List.ofFn (fun i : Fin inputs.envp.length => L.envpBase + BitVec.ofNat 64 (cstrPrefixOff inputs.envp i.1)) := by change (packCStringList L.envpBase inputs.envp).2.2 = _; rw [hp2]
  have hupper_eq : L.upperStrBytes = inputs.argv.flatMap (· ++ [0#8]) ++ inputs.envp.flatMap (· ++ [0#8]) ++ (inputs.execfn ++ [0#8]) ++ List.replicate 8 0#8 := by
    change (packCStringList L.argvBase inputs.argv).2.1 ++ (packCStringList L.envpBase inputs.envp).2.1 ++ _ ++ _ = _; rw [hp1, hp2]
  have hargc_len : L.argvAddrs.length = inputs.argv.length := (by rw [hargv_eq, List.length_ofFn]); have henvc_len : L.envpAddrs.length = inputs.envp.length := by rw [henvp_eq, List.length_ofFn]
  have hauxv_wf := mkAuxvEntries_wf img hx L.platformAddr L.randomAddr L.execfnAddr
  let unpaddedWords := ([BitVec.ofNat 64 inputs.argv.length] ++ L.argvAddrs ++ [0#64] ++ L.envpAddrs ++ [0#64]) ++ (L.auxvPairs.flatMap fun (t, v) => [t, v])
  let padWords : List (BitVec 64) := if unpaddedWords.length % 2 == 0 then [] else [0#64]; let tableWords := if unpaddedWords.length % 2 == 0 then unpaddedWords else unpaddedWords ++ [0#64]
  have htw_split : tableWords = unpaddedWords ++ padWords := by dsimp only [tableWords, padWords]; split <;> simp
  have htw_len : tableWords.length % 2 = 0 ∧ unpaddedWords.length ≤ tableWords.length ∧ tableWords.length ≤ unpaddedWords.length + 1 := by
    dsimp only [tableWords]; split; · rename_i he; rw [beq_iff_eq] at he; exact ⟨he, by omega, by omega⟩
    · rename_i ho; rw [Bool.not_eq_true, beq_eq_false_iff_ne] at ho; simp; omega
  have hunpad_len : unpaddedWords.length = 3 + inputs.argv.length + inputs.envp.length + 2 * (L.auxvEntries.length + 1) := by
    dsimp only [unpaddedWords, StackLayout.auxvPairs]
    have hp : ∀ ps : List (BitVec 64 × BitVec 64), (ps.flatMap fun (t, v) => [t, v]).length = 2 * ps.length := by intro ps; induction ps with | nil => rfl | cons p rs ih => rcases p with ⟨t, v⟩; simp [ih]; omega
    simp only [List.length_append, List.length_cons, List.length_nil, hargc_len, henvc_len, hp]; omega
  let tableBytes := tableWords.flatMap (Obj.bytesLE 8); have htb_len : tableBytes.length = 8 * tableWords.length := flatMap_bytesLE8_length tableWords
  let infoBytes := inputs.init.auxv.randomBytes ++ List.replicate L.infoPadLen 0#8 ++ platformCStringBytes ++ L.upperStrBytes
  have hinfo_len : infoBytes.length = infoLen := by
    dsimp only [infoBytes, infoLen]; rw [hupper_eq]; have hpad_def : L.infoPadLen = alignUp16 upperRaw - upperRaw := rfl
    simp only [List.length_append, List.length_replicate, hx.random16, platformCStringBytes, List.length_cons, List.length_nil, hpad_def]; omega
  let stackRegion : Snapshot.Region := { start := L.sp0, perm := Perm.rw, bytes := tableBytes ++ infoBytes }
  have htop_lt : inputs.init.stackTop.toNat < 2 ^ 64 := inputs.init.stackTop.isLt; have htop_le : inputs.init.stackTop.toNat ≤ TASK_SIZE := hs.top_aligned.2; have hsize_le : inputs.init.stackSize ≤ inputs.init.stackTop.toNat := hs.size_aligned.2
  have htop_mod16 : inputs.init.stackTop.toNat % 16 = 0 := (by have := hs.top_aligned.1; rw [hpage] at this; omega); have haux_len_eq : L.auxvEntries.length = 18 + inputs.init.auxv.extra.length := hauxv_wf.1; have hextra_le := hx.extra_le
  have hargc_pos : 1 ≤ inputs.argv.length := (by cases h : inputs.argv with | nil => exact absurd h ha.argc_pos | cons _ _ => simp); have hfit : tableBytes.length + infoLen ≤ inputs.init.stackSize / 4 + 480 := by dsimp only [infoLen]; omega
  have henvpB_eq : L.argvBase + BitVec.ofNat 64 (inputs.argv.flatMap (· ++ [0#8])).length = L.envpBase := by change _ = L.argvBase + BitVec.ofNat 64 (packCStringList L.argvBase inputs.argv).1; rw [hp1]
  have hexecA_eq : L.envpBase + BitVec.ofNat 64 (inputs.envp.flatMap (· ++ [0#8])).length = L.execfnAddr := by change _ = L.envpBase + BitVec.ofNat 64 (packCStringList L.envpBase inputs.envp).1; rw [hp2]
  have hsp0_def : BitVec.ofNat 64 (infoBaseNat - tableBytes.length) = L.sp0 := rfl; have hunder : ¬ (inputs.init.stackSize > inputs.init.stackTop.toNat) := (by omega)
  have hoverlap : ¬ (img.brkStart.toNat > inputs.init.stackTop.toNat - inputs.init.stackSize) := (by omega); have hinfo_gt : ¬ (16 + alignUp16 upperRaw > inputs.init.stackSize) := by omega
  let infoBytesRaw := inputs.init.auxv.randomBytes ++ List.replicate L.infoPadLen 0#8 ++ platformCStringBytes ++
    (packCStringList L.argvBase inputs.argv).2.1 ++ (packCStringList L.envpBase inputs.envp).2.1 ++ (inputs.execfn ++ [0#8]) ++ List.replicate 8 0#8
  have hinfo_raw : infoBytesRaw = infoBytes := by dsimp only [infoBytesRaw, infoBytes]; rw [hp1, hp2, hupper_eq]; simp only [List.append_assoc]
  have hbuild : buildInitialStack img inputs = .ok (L.sp0, stackRegion) := by
    unfold buildInitialStack; simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, hr16, hanul, henul, hxnul, halign_chk, hunder, hoverlap, Bool.false_eq_true, ↓reduceIte]
    change (if 16 + alignUp16 upperRaw > inputs.init.stackSize then _ else _) = _; rw [ite_eq_right_iff.mpr fun h => (hinfo_gt h).elim]
    change (if tableBytes.length + infoBytesRaw.length > inputs.init.stackSize then _ else Except.ok (L.sp0, ({ start := L.sp0, perm := Perm.rw, bytes := tableBytes ++ infoBytesRaw } : Snapshot.Region))) = _
    rw [hinfo_raw, ite_eq_right_iff.mpr (by rw [hinfo_len]; omega)]
  have hwf' : (!img.WellFormed) = false := by rw [hwf]; rfl
  have hdirs : (inputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d)) = false := Bool.eq_false_iff.mpr fun h => by
    obtain ⟨d, hdm, hbad⟩ := List.any_eq_true.mp h; have hd := hfs.paths.1 d hdm; rw [hd.1, hd.not_hasDotDot] at hbad; cases hbad
  have hfiles : (inputs.files.any (fun (p, bs) => hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE))) = false := Bool.eq_false_iff.mpr fun h => by
    obtain ⟨⟨p, bs⟩, hfm, hbad⟩ := List.any_eq_true.mp h; dsimp only at hbad; have hf := hfs.paths.2 (p, bs) hfm; have hsz : decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE) = true := decide_eq_true (hfs.file_size (p, bs) hfm); rw [hf.1, hf.not_hasDotDot, hsz] at hbad; cases hbad
  unfold ElfImage.loadState at hload; simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, hwf', hdirs, hfiles, hbuild, Bool.false_eq_true, ↓reduceIte] at hload
  injection hload with hs0; symm at hs0; dsimp only [stackRegion] at hs0
  have h_tb_split : tableBytes = Obj.bytesLE 8 (BitVec.ofNat 64 inputs.argv.length) ++ ((L.argvAddrs ++ [0#64]).flatMap (Obj.bytesLE 8) ++
      ((L.envpAddrs ++ [0#64]).flatMap (Obj.bytesLE 8) ++ (encodeAuxvBytes L.auxvEntries ++ padWords.flatMap (Obj.bytesLE 8)))) := by
    dsimp only [tableBytes]; rw [htw_split, encodeAuxvBytes_eq_flatMap_bytesLE]; dsimp only [unpaddedWords, StackLayout.auxvPairs]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_assoc, List.nil_append, List.cons_append]
  have h_ib_split : infoBytes = (inputs.init.auxv.randomBytes ++ List.replicate L.infoPadLen 0#8) ++ (platformCStringBytes ++ L.upperStrBytes) := by dsimp only [infoBytes]; simp only [List.append_assoc]
  have hpad_def : L.infoPadLen = alignUp16 upperRaw - upperRaw := rfl; have hrand_def : L.randomAddr = BitVec.ofNat 64 infoBaseNat := rfl
  have hplat_def : L.platformAddr = L.randomAddr + BitVec.ofNat 64 (16 + L.infoPadLen) := rfl; have hargvB_def : L.argvBase = L.platformAddr + 8#64 := rfl
  have hauxE_def : L.auxvEntries = mkAuxvEntries img inputs L.platformAddr L.randomAddr L.execfnAddr := rfl; have hL_eq : StackLayout.of img inputs = L := rfl
  have hib_def : infoBaseNat = inputs.init.stackTop.toNat - (16 + alignUp16 upperRaw) := rfl; have il_def : infoLen = 16 + alignUp16 upperRaw := rfl
  clear hr16 hanul henul hxnul halign_chk hfold_eq hunder hoverlap hinfo_gt hwf' hdirs hfiles hauxv_wf hp1 hp2 hbuild hinfo_raw infoBytesRaw stackRegion
  generalize htb_gen : tableBytes = tb at *; generalize hib_gen : infoBytes = ib at *; generalize htw_gen : tableWords.length = twLen at *
  generalize hun_gen : unpaddedWords.length = unLen at *; generalize hpw_gen : padWords.flatMap (Obj.bytesLE 8) = padBytes at *
  generalize hL_gen : (L : StackLayout) = L0 at *; generalize hur_gen : upperRaw = ur at *; generalize hil_gen : infoLen = il at *; generalize hibn_gen : infoBaseNat = ibn at *
  clear htb_gen tableBytes hib_gen infoBytes htw_gen htw_split tableWords hun_gen unpaddedWords hpw_gen padWords hL_gen L hur_gen upperRaw hil_gen infoLen hibn_gen infoBaseNat
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := htop_le
  have hrand_nat : L0.randomAddr.toNat = ibn := (by rw [hrand_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hsp_nat : L0.sp0.toNat = ibn - tb.length := by rw [← hsp0_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hplat_nat : L0.platformAddr.toNat = L0.randomAddr.toNat + 16 + L0.infoPadLen := by
    rw [hplat_def, BitVec.toNat_add, hrand_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hargvB_nat : L0.argvBase.toNat = L0.platformAddr.toNat + 8 := by rw [hargvB_def, BitVec.toNat_add, hplat_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have henvpB_nat : L0.envpBase.toNat = L0.argvBase.toNat + (inputs.argv.flatMap (· ++ [0#8])).length := by
    rw [← henvpB_eq, BitVec.toNat_add, hargvB_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hexec_nat : L0.execfnAddr.toNat = L0.envpBase.toNat + (inputs.envp.flatMap (· ++ [0#8])).length := by
    rw [← hexecA_eq, BitVec.toNat_add, henvpB_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hupper_top : L0.argvBase.toNat + L0.upperStrBytes.length = inputs.init.stackTop.toNat := by
    rw [hargvB_nat, hplat_nat, hrand_nat, hupper_eq]; simp only [List.length_append, List.length_singleton, List.length_replicate, hpad_def]; omega
  have hargvT_nat : L0.argvTableAddr.toNat = L0.sp0.toNat + 8 := by change (L0.sp0 + 8#64).toNat = _; rw [BitVec.toNat_add, hsp_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have henvpT_nat : L0.envpTableAddr.toNat = L0.sp0.toNat + 8 * (inputs.argv.length + 2) := by
    change (L0.sp0 + BitVec.ofNat 64 (8 * (L0.argvAddrs.length + 2))).toNat = _; rw [hargc_len, BitVec.toNat_add, hsp_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hauxvT_nat : L0.auxvTableAddr.toNat = L0.sp0.toNat + 8 * (inputs.argv.length + inputs.envp.length + 3) := by
    change (L0.sp0 + BitVec.ofNat 64 (8 * (L0.argvAddrs.length + L0.envpAddrs.length + 3))).toNat = _; rw [hargc_len, henvc_len, BitVec.toNat_add, hsp_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hsp_plus_tb : L0.sp0 + BitVec.ofNat 64 tb.length = L0.randomAddr := BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, hsp_nat, hrand_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
  have h_envp_addr : L0.sp0 + 8#64 + BitVec.ofNat 64 (((L0.argvAddrs ++ [0#64]).flatMap (Obj.bytesLE 8)).length) = L0.envpTableAddr := by
    rw [flatMap_bytesLE8_length]; simp only [List.length_append, List.length_singleton, hargc_len]
    change L0.sp0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * (inputs.argv.length + 1)) = L0.sp0 + BitVec.ofNat 64 (8 * (L0.argvAddrs.length + 2))
    rw [hargc_len, BitVec.add_assoc, ← BitVec.ofNat_add, show 8 + 8 * (inputs.argv.length + 1) = 8 * (inputs.argv.length + 2) by omega]
  have h_auxv_addr : L0.envpTableAddr + BitVec.ofNat 64 (((L0.envpAddrs ++ [0#64]).flatMap (Obj.bytesLE 8)).length) = L0.auxvTableAddr := by
    rw [flatMap_bytesLE8_length]; simp only [List.length_append, List.length_singleton, henvc_len]
    change L0.sp0 + BitVec.ofNat 64 (8 * (L0.argvAddrs.length + 2)) + BitVec.ofNat 64 (8 * (inputs.envp.length + 1)) = L0.sp0 + BitVec.ofNat 64 (8 * (L0.argvAddrs.length + L0.envpAddrs.length + 3))
    rw [hargc_len, henvc_len, BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (inputs.argv.length + 2) + 8 * (inputs.envp.length + 1) = 8 * (inputs.argv.length + inputs.envp.length + 3) by omega]
  have h_sp0_16 : L0.sp0.toNat % 16 = 0 := (by omega); have h_rand_16 : L0.randomAddr.toNat % 16 = 0 := (by omega); have h_aux_le : L0.auxvTableAddr.toNat + 16 * (L0.auxvEntries.length + 1) ≤ L0.randomAddr.toNat := by omega
  have h_hr : inputs.init.stackTop.toNat - inputs.init.stackSize + inputs.init.stackSize / 2 ≤ L0.sp0.toNat ∧ inputs.init.stackTop.toNat - inputs.init.stackSize + 262144 ≤ L0.sp0.toNat := ⟨by omega, by omega⟩
  have h_ab : 1 ≤ inputs.argv.length ∧ inputs.argv.length < 2 ^ 31 ∧ inputs.envp.length < 2 ^ 31 := ⟨hargc_pos, by omega, by omega⟩
  have ⟨h_p1, h_p2, h_p3, h_stack_all⟩ := stackRegion_mem_props hwf hbrk (sp0 := L0.sp0) (stackBytes := tb ++ ib) (by omega) (by rw [List.length_append, hinfo_len]; omega) htop_le
  have ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hrsas, hr16, hs0_mem⟩ :
      s0.regs = RegFile.empty ∧ s0.vregs = VRegFile.empty ∧ s0.sp = L0.sp0 ∧ s0.pc = img.entry ∧ s0.pstate = PState.zero ∧ s0.status = .Running ∧
      s0.tpidrEl0 = 0#64 ∧ s0.brk = img.brkStart ∧ s0.brkStart = img.brkStart ∧ s0.fs = initFsState inputs ∧ s0.trace = [] ∧ s0.oracle = inputs.init.oracle ∧
      s0.oracleIdx = 0 ∧ s0.exclFails = inputs.init.oracle.exclFails ∧ s0.sigActions = (fun _ => {}) ∧ s0.sigAltStack = {} ∧ s0.physMemAvail = inputs.init.physMemAvail ∧
      s0.mem = (Memory.mk (Snapshot.loadCellAt (img.segments ++ [{ start := L0.sp0, perm := Perm.rw, bytes := tb ++ ib }]))).mapZero (BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)) inputs.init.stackSize := by
    rw [hs0]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have h_nolf : ∀ a : BitVec 64, s0.mem.isLazyFree a = false := fun a => by
    rw [hs0_mem, Memory.isLazyFree_mapZero]
    exact Snapshot.isLazyFree_loadCellAt _ a
  clear hs0; rw [← hs0_mem] at h_p1 h_p2 h_p3 h_stack_all; clear hs0_mem; obtain ⟨h_tb, h_ib⟩ := holdsBytes_append.mp h_stack_all
  rw [hsp_plus_tb, h_ib_split] at h_ib; rw [h_tb_split] at h_tb; obtain ⟨h_argc, h_tb1⟩ := holdsBytes_append.mp h_tb
  rw [show (Obj.bytesLE 8 (BitVec.ofNat 64 inputs.argv.length)).length = 8 by simp [Obj.bytesLE]] at h_tb1
  obtain ⟨h_argv, h_tb2⟩ := holdsBytes_append.mp h_tb1; rw [h_envp_addr] at h_tb2; obtain ⟨h_envp, h_tb3⟩ := holdsBytes_append.mp h_tb2
  rw [h_auxv_addr] at h_tb3; obtain ⟨h_auxv, _⟩ := holdsBytes_append.mp h_tb3; obtain ⟨h_rp, h_pu⟩ := holdsBytes_append.mp h_ib; obtain ⟨h_rand, _⟩ := holdsBytes_append.mp h_rp
  have h_plat_addr : L0.randomAddr + BitVec.ofNat 64 ((inputs.init.auxv.randomBytes ++ List.replicate L0.infoPadLen 0#8).length) = L0.platformAddr := by simp only [List.length_append, List.length_replicate, hx.random16, hplat_def]
  rw [h_plat_addr] at h_pu; obtain ⟨h_plat, h_ustr⟩ := holdsBytes_append.mp h_pu
  clear h_stack_all h_tb h_ib h_tb1 h_tb2 h_tb3 h_rp h_pu h_tb_split h_ib_split hsp_plus_tb h_envp_addr h_auxv_addr h_plat_addr; subst hL_eq
  exact ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hrsas, hr16,
    h_sp0_16, h_rand_16, ⟨hs.top_aligned.1, htop_mod16, htop_le⟩, hs.base_floor, h_hr, h_ab, hargv_eq, henvp_eq, hupper_eq, hauxE_def,
    ⟨hargvT_nat, henvpT_nat, hauxvT_nat, h_aux_le, hplat_nat, hargvB_nat, henvpB_nat, hexec_nat, hupper_top⟩, h_p1, h_nolf, h_p2, h_p3, h_argc, h_argv, h_envp, h_auxv, h_rand, h_plat, h_ustr⟩
/-- Total loader + `InitialStackInfo` unpacking when `img.brkStart.toNat ≤ STACK_BASE_MIN`. -/
theorem loadState_ok_initialStackInfo (img : ElfImage) {inputs : ProcessInputs} (hwf : img.WellFormed = true) (hvalid : inputs.Valid) (hbrk : img.brkStart.toNat ≤ STACK_BASE_MIN) :
    ∃ s0, img.loadState inputs = .ok s0 ∧ InitialStackInfo img inputs s0 := by
  have hbrk' := Nat.le_trans hbrk hvalid.stack.base_floor; obtain ⟨s0, hload⟩ := loadState_ok_of_valid img hvalid hwf hbrk'; exact ⟨s0, hload, loadState_initialStackInfo hwf hvalid hbrk' hload⟩
/-- Every address in `[img.brkStart, STACK_BASE_MIN)` is unmapped in `s0.mem`. -/
theorem InitialStackInfo.unmapped_below_stackBaseMin {img : ElfImage} {inputs : ProcessInputs} {s0 : State} (h : InitialStackInfo img inputs s0) {a : BitVec 64}
    (hlo : img.brkStart.toNat ≤ a.toNat) (hhi : a.toNat < STACK_BASE_MIN) : s0.mem.perm a = none :=
  h.s0_unmapped_heap a hlo (Nat.lt_of_lt_of_le hhi h.stackBase_floor)
/-- Every address in `[img.brkStart, stackTop - stackSize)` is unmapped in `s0.mem`. -/
theorem _root_.ProofLib.UnmappedBetween.of_initialStackInfo {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : InitialStackInfo img inputs s0) :
    UnmappedBetween img.brkStart.toNat (inputs.init.stackTop.toNat - inputs.init.stackSize) s0.mem :=
  h.s0_unmapped_heap
/-- Establish `MallocngInitialMemWf` on `s0` from `InitialStackInfo`. -/
theorem InitialStackInfo.mallocngInitialMemWf {img : ElfImage} {inputs : ProcessInputs} {s0 : State} (h : InitialStackInfo img inputs s0)
    {addrs : MallocngAddrs} (hbrkBase : addrs.brkBase = img.brkStart)
    (hbrkMin : 0x10000 ≤ img.brkStart.toNat) (hbrk1G : img.brkStart.toNat ≤ 2 ^ 30)
    (hsize_le : inputs.init.stackSize ≤ inputs.init.stackTop.toNat)
    (hstackCeil : inputs.init.stackSize ≤ 128 * 2 ^ 20)
    (hwf : img.WellFormed = true) :
    MallocngInitialMemWf addrs 4096 (inputs.init.stackTop.toNat - inputs.init.stackSize) inputs.init.stackTop.toNat s0 := by
  have ⟨_, hmod, hlo, _, _⟩ := wellFormed_segments_bounds hwf
  exact ⟨h.s0_brk.trans hbrkBase.symm, h.s0_brkStart.trans hbrkBase.symm, hbrkBase ▸ hmod,
    hbrkBase ▸ hbrkMin, hbrkBase ▸ hlo, hbrkBase ▸ hbrk1G,
    h.stackBase_floor, Nat.sub_le _ _, by omega, h.stackTop_align.2.2,
    fun a hmap => hbrkBase ▸ h.s0_mapped_iff a hmap⟩
theorem MallocngInitialMemWf.transport {addrs : MallocngAddrs} {imgLo stackBase stackTop : Nat} {s0 sf : State}
    (hwf : MallocngInitialMemWf addrs imgLo stackBase stackTop s0) (hbrk : sf.brk = s0.brk) (hbrkS : sf.brkStart = s0.brkStart)
    (hmap : ∀ a : BitVec 64, (sf.mem.perm a).mapped = true → (s0.mem.perm a).mapped = true) : MallocngInitialMemWf addrs imgLo stackBase stackTop sf :=
  ⟨hbrk.trans hwf.1, hbrkS.trans hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1,
    hwf.2.2.2.2.2.1, hwf.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.1, hwf.2.2.2.2.2.2.2.2.1,
    hwf.2.2.2.2.2.2.2.2.2.1, fun a ha => hwf.2.2.2.2.2.2.2.2.2.2 a (hmap a ha)⟩
theorem split_random_hi8 (addr : BitVec 64) {bs : List (BitVec 8)} (h16 : bs.length = 16) :
    (addr ↦ₛ bs) = (addr ↦ₛ bs.take 8) ∗ ((addr + 8#64) ↦ₛ bs.drop 8) := by
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, show (bs.take 8).length = 8 by simp [h16]]
theorem dup_random_hi8 (addr : BitVec 64) {bs : List (BitVec 8)} (h16 : bs.length = 16) : ((addr ↦ᵣ bs) ∗ ((addr + 8#64) ↦ᵣ bs.drop 8)) = (addr ↦ᵣ bs) := by
  simpa [List.take_of_length_le (by simp [h16] : (bs.drop 8).length ≤ 8)] using pointsToBytesRO_dup_slice addr bs 8 8 (by omega)
theorem InitialStackInfo.argvAddrs_length {img : ElfImage} {inputs : ProcessInputs} {s0 : State} (h : InitialStackInfo img inputs s0) :
    (StackLayout.of img inputs).argvAddrs.length = inputs.argv.length := by rw [h.argvAddrs_eq, List.length_ofFn]
theorem InitialStackInfo.envpAddrs_length {img : ElfImage} {inputs : ProcessInputs} {s0 : State} (h : InitialStackInfo img inputs s0) :
    (StackLayout.of img inputs).envpAddrs.length = inputs.envp.length := by rw [h.envpAddrs_eq, List.length_ofFn]
theorem InitialStackInfo.scratch_supportedOn {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : InitialStackInfo img inputs s0) {K : Nat} (hK : K ≤ max 262144 (inputs.init.stackSize / 2)) :
    let L := StackLayout.of img inputs; SupportedOn 0#64 (fun k => L.sp0.toNat - K ≤ k ∧ k < L.sp0.toNat) s0.mem (memRegion (L.sp0 - BitVec.ofNat 64 K) K) := by
  have hhr := h.sp0_headroom; have hperm := h.s0_perm_rw_below_sp0; have hnolf := h.s0_isLazyFree; clear h; dsimp only; generalize hsp : (StackLayout.of img inputs).sp0 = sp0 at *; clear hsp
  have hlt := sp0.isLt; have hbase : (sp0 - BitVec.ofNat 64 K).toNat = sp0.toNat - K := by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsup := SupportedOn.of_memRegion_rw0 (addr := sp0 - BitVec.ofNat 64 K) (len := K) (m := s0.mem) (by rw [hbase]; omega)
    (fun a ha => by unfold InRegion at ha; have := a.isLt; rw [BitVec.toNat_sub, hbase] at ha; exact hperm a (by omega) (by omega))
    (fun a _ => hnolf a)
  rwa [hbase, show sp0.toNat - K + K = sp0.toNat by omega] at hsup
/-- Full initial-stack `SupportedOn 0#64` bundle (scratch below `sp0`, writable `auxv`/`random`, and frozen stack tables/strings). -/
theorem InitialStackInfo.stack_supportedOn_bupd {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : InitialStackInfo img inputs s0) (hrand16 : inputs.init.auxv.randomBytes.length = 16) {K : Nat} (hK : K ≤ max 262144 (inputs.init.stackSize / 2)) :
    let L := StackLayout.of img inputs
    SupportedOn 0#64 (fun k => L.sp0.toNat - K ≤ k ∧ k < inputs.init.stackTop.toNat) s0.mem
      (|==> (memRegion (L.sp0 - BitVec.ofNat 64 K) K ∗ (L.sp0 ↦₆₄ᵣ BitVec.ofNat 64 inputs.argv.length) ∗
        (L.argvTableAddr ↦₆₄ᵣ* (L.argvAddrs ++ [0#64])) ∗ (L.envpTableAddr ↦₆₄ᵣ* (L.envpAddrs ++ [0#64])) ∗
        (L.auxvTableAddr ↦ₛ encodeAuxvBytes L.auxvEntries) ∗ (L.randomAddr ↦ₛ inputs.init.auxv.randomBytes) ∗
        (L.platformAddr ↦ᵣ platformCStringBytes) ∗ (L.argvBase ↦ᵣ L.upperStrBytes))) := by
  have s0_sc := SupportedOn.bupd_intro (h.scratch_supportedOn hK); have hav_len := h.argvAddrs_length; have hev_len := h.envpAddrs_length
  have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := h.stackTop_align.2.2; have hhr := h.sp0_headroom; have han := h.addrs_nat; dsimp only at han
  have hc1 := h.holds_argc; have hc2 := h.holds_argv; have hc3 := h.holds_envp; have hc4 := h.holds_auxv; have hc5 := h.holds_random; have hc6 := h.holds_platform; have hc7 := h.holds_upperStr
  clear h; dsimp only; generalize hL : StackLayout.of img inputs = L0 at *; clear hL; have h48_lt : (2 ^ 48 : Nat) < 2 ^ 64 := by decide
  have hav1 : (L0.argvAddrs ++ [0#64]).length = inputs.argv.length + 1 := (by simp [hav_len]); have hev1 : (L0.envpAddrs ++ [0#64]).length = inputs.envp.length + 1 := by simp [hev_len]
  have hax_len := encodeAuxvBytes_length L0.auxvEntries; have hpl_len : platformCStringBytes.length = 8 := rfl; have s7 := SupportedOn.of_holdsBytes_ro0 (by omega) hc7
  have s1 := SupportedOn.of_holdsBytes_u64_ro0 (by omega) hc1; have s2 := SupportedOn.of_holdsBytes_words64_ro0 (by rw [hav1]; omega) hc2
  have s3 := SupportedOn.of_holdsBytes_words64_ro0 (by rw [hev1]; omega) hc3
  have s4 := SupportedOn.bupd_intro (SupportedOn.of_holdsBytes_rw0 (by rw [hax_len]; omega) hc4)
  have s5 := SupportedOn.bupd_intro (SupportedOn.of_holdsBytes_rw0 (by rw [hrand16]; omega) hc5)
  have s6 := SupportedOn.of_holdsBytes_ro0 (by rw [hpl_len]; omega) hc6
  have s67 := SupportedOn.sepConj_bupd_interval (lo := L0.platformAddr.toNat) (hi := inputs.init.stackTop.toNat) s6 s7 (by rw [hpl_len]; omega) (by omega) (by rw [hpl_len]; omega)
  have s57 := SupportedOn.sepConj_bupd_interval (lo := L0.randomAddr.toNat) (hi := inputs.init.stackTop.toNat) s5 s67 (by rw [hrand16]; omega) (by omega) (by rw [hrand16]; omega)
  have s47 := SupportedOn.sepConj_bupd_interval (lo := L0.auxvTableAddr.toNat) (hi := inputs.init.stackTop.toNat) s4 s57 (by rw [hax_len]; omega) (by omega) (by rw [hax_len]; omega)
  have s37 := SupportedOn.sepConj_bupd_interval (lo := L0.envpTableAddr.toNat) (hi := inputs.init.stackTop.toNat) s3 s47 (by rw [hev1]; omega) (by omega) (by rw [hev1]; omega)
  have s27 := SupportedOn.sepConj_bupd_interval (lo := L0.argvTableAddr.toNat) (hi := inputs.init.stackTop.toNat) s2 s37 (by rw [hav1]; omega) (by omega) (by rw [hav1]; omega)
  exact SupportedOn.sepConj_bupd_interval s0_sc (SupportedOn.sepConj_bupd_interval (lo := L0.sp0.toNat) (hi := inputs.init.stackTop.toNat) s1 s27 (by omega) (by omega) (by omega)) (by omega) (by omega) (by omega)
theorem cstrPrefixOff_le_flatMap_length (strs : List (List (BitVec 8))) (k : Nat) : cstrPrefixOff strs k ≤ (strs.flatMap (· ++ [0#8])).length := by
  have h := congrArg (fun l : List (List (BitVec 8)) => (l.flatMap (· ++ [0#8])).length) (List.take_append_drop k strs).symm
  simp only [List.flatMap_append, List.length_append] at h; unfold cstrPrefixOff; omega
theorem InitialStackInfo.argvAddr_toNat {img : ElfImage} {inputs : ProcessInputs} {s0 : State} (h : InitialStackInfo img inputs s0) {i : Nat} (hi : i < inputs.argv.length) :
    let L := StackLayout.of img inputs; let addr := L.argvAddrs[i]'(h.argvAddrs_length ▸ hi); addr.toNat = L.argvBase.toNat + cstrPrefixOff inputs.argv i ∧ 0 < addr.toNat := by
  dsimp only; have heq : (StackLayout.of img inputs).argvAddrs[i]'(h.argvAddrs_length ▸ hi) = (StackLayout.of img inputs).argvBase + BitVec.ofNat 64 (cstrPrefixOff inputs.argv i) := by simp [h.argvAddrs_eq]
  have hfl := h.stackBase_floor; have hhr := h.sp0_headroom.1; have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := h.stackTop_align.2.2; have han := h.addrs_nat; dsimp only at han; have hu := h.upperStr_eq
  generalize ha_gen : ((StackLayout.of img inputs).argvAddrs[i]'(h.argvAddrs_length ▸ hi)) = a0 at heq ⊢; clear h ha_gen; generalize hL : StackLayout.of img inputs = L0 at *; clear hL
  have hsbm : 0 < STACK_BASE_MIN := (by unfold STACK_BASE_MIN; decide); have h48 : (2 ^ 48 : Nat) < 2 ^ 64 := (by decide); have hoff := cstrPrefixOff_le_flatMap_length inputs.argv i
  have : (inputs.argv.flatMap (· ++ [0#8])).length ≤ L0.upperStrBytes.length := by rw [hu]; simp only [List.length_append]; omega
  have ha_nat : a0.toNat = L0.argvBase.toNat + cstrPrefixOff inputs.argv i := (by rw [heq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]); exact ⟨ha_nat, by omega⟩
theorem InitialStackInfo.argvAddr_ne_zero {img : ElfImage} {inputs : ProcessInputs} {s0 : State} (h : InitialStackInfo img inputs s0) {i : Nat} (hi : i < inputs.argv.length) :
    (StackLayout.of img inputs).argvAddrs[i]'(h.argvAddrs_length ▸ hi) ≠ 0#64 := by have hpos := (h.argvAddr_toNat hi).2; intro hz; rw [hz] at hpos; simp at hpos
theorem InitialStackInfo.envpAddr_ne_zero {img : ElfImage} {inputs : ProcessInputs} {s0 : State} (h : InitialStackInfo img inputs s0) {i : Nat} (hi : i < inputs.envp.length) :
    (StackLayout.of img inputs).envpAddrs[i]'(h.envpAddrs_length ▸ hi) ≠ 0#64 := by
  have heq : (StackLayout.of img inputs).envpAddrs[i]'(h.envpAddrs_length ▸ hi) = (StackLayout.of img inputs).envpBase + BitVec.ofNat 64 (cstrPrefixOff inputs.envp i) := by simp [h.envpAddrs_eq]
  have hfl := h.stackBase_floor; have hhr := h.sp0_headroom.1; have htop48 : inputs.init.stackTop.toNat ≤ 2 ^ 48 := h.stackTop_align.2.2; have han := h.addrs_nat; dsimp only at han; have hu := h.upperStr_eq
  generalize ha_gen : ((StackLayout.of img inputs).envpAddrs[i]'(h.envpAddrs_length ▸ hi)) = a0 at heq ⊢; clear h ha_gen; generalize hL : StackLayout.of img inputs = L0 at *; clear hL
  have hsbm : 0 < STACK_BASE_MIN := (by unfold STACK_BASE_MIN; decide); have h48 : (2 ^ 48 : Nat) < 2 ^ 64 := (by decide); have hoff := cstrPrefixOff_le_flatMap_length inputs.envp i
  have : (inputs.argv.flatMap (· ++ [0#8])).length + (inputs.envp.flatMap (· ++ [0#8])).length ≤ L0.upperStrBytes.length := by rw [hu]; simp only [List.length_append]; omega
  have ha_nat : a0.toNat = L0.envpBase.toNat + cstrPrefixOff inputs.envp i := by rw [heq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  intro hz; rw [hz] at ha_nat; simp at ha_nat; omega
/-- Duplicate a NUL-terminated `argv[i]` C-string with `≥ 8` trailing readable padding bytes. -/
theorem InitialStackInfo.dup_argv_cstr_padded {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : InitialStackInfo img inputs s0) (ha : ArgsValid inputs) {i : Nat} (hi : i < inputs.argv.length) :
    let L := StackLayout.of img inputs; let addr := L.argvAddrs[i]'(h.argvAddrs_length ▸ hi)
    ∃ pad : List (BitVec 8), 0#8 ∉ inputs.argv[i] ∧ 8 ≤ pad.length ∧ 8 ≤ (addr.toNat + inputs.argv[i].length) % 8 + 1 + pad.length ∧
      addr.toNat + (inputs.argv[i].length + 1 + pad.length) = inputs.init.stackTop.toNat ∧ ((L.argvBase ↦ᵣ L.upperStrBytes) ∗ (addr ↦ᵣ (inputs.argv[i] ++ [0#8] ++ pad))) = (L.argvBase ↦ᵣ L.upperStrBytes) := by
  dsimp only; have hno_nul := ha.no_nul.1 inputs.argv[i] (List.getElem_mem hi); let off := cstrPrefixOff inputs.argv i
  let tailRest := inputs.envp.flatMap (· ++ [0#8]) ++ (inputs.execfn ++ [0#8]) ++ List.replicate 8 0#8; let pad := (inputs.argv.drop (i + 1)).flatMap (· ++ [0#8]) ++ tailRest
  have hpad8 : 8 ≤ pad.length := (by dsimp only [pad, tailRest]; simp only [List.length_append, List.length_replicate]; omega)
  have ha_nat := (h.argvAddr_toNat hi).1; have hu := h.upperStr_eq; have htop_eq := h.addrs_nat.2.2.2.2.2.2.2.2
  have ha_eq : (StackLayout.of img inputs).argvBase + BitVec.ofNat 64 off = (StackLayout.of img inputs).argvAddrs[i]'(h.argvAddrs_length ▸ hi) := by dsimp only [off]; simp [h.argvAddrs_eq]
  generalize had_gen : ((StackLayout.of img inputs).argvAddrs[i]'(h.argvAddrs_length ▸ hi)) = a0 at ha_nat ha_eq ⊢; clear h ha had_gen; generalize hL : StackLayout.of img inputs = L0 at *; clear hL
  have hu' : L0.upperStrBytes = inputs.argv.flatMap (· ++ [0#8]) ++ tailRest := (by rw [hu]; dsimp only [tailRest]; simp only [List.append_assoc])
  have hoff_le := cstrPrefixOff_le_flatMap_length inputs.argv i; have hoff_u : off ≤ L0.upperStrBytes.length := by rw [hu', List.length_append]; omega
  have hdrop : L0.upperStrBytes.drop off = inputs.argv[i] ++ [0#8] ++ pad := by
    rw [hu', List.drop_append_of_le_length hoff_le, flatMap_cstr_drop_prefix inputs.argv hi]; simp [pad, List.append_assoc]
  have hlen_drop : inputs.argv[i].length + 1 + pad.length = L0.upperStrBytes.length - off := by
    have := congrArg List.length hdrop; rw [List.length_drop] at this; simp only [List.length_append, List.length_singleton] at this; omega
  have hdup := pointsToBytesRO_dup_slice L0.argvBase L0.upperStrBytes off (L0.upperStrBytes.length - off) (by omega)
  rw [ha_eq, List.take_of_length_le (by simp), hdrop] at hdup; exact ⟨pad, hno_nul, hpad8, by omega, by omega, hdup⟩
end ProofLib.StdStartup
