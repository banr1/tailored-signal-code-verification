/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.CoreLemmas
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.SepLogic.WP.Structural
import Arm64.Trusted.Spec.SepLogic

/-!
# Indirect Call Rules and Relocated Function Pointers

Provides `SepWP` composition rules for indirect subroutine calls (`BLR`) via `FnPtrSpec`
(`wp_blr_of_fnPtrSpec`), together with decidable `R_AARCH64_ABS64` relocation reflection
(`checkRodataReloc`, `rodataPtr_eq_fnAddr_of_loads`, `SepWP.rodataPtr_intro`) for
read-only `.rodata` and `.data.rel.ro` pointer slots.
-/

@[expose] public section

/-- Runtime address of function or stub symbol `name` in loaded image `img`. -/
abbrev Arm64.Obj.Image.fnAddr (img : Arm64.Obj.Image) (name : String) : BitVec 64 :=
  (Arm64.Program.ofImage img).fnAddr name

namespace ProofLib

open Arm64

/-- Read a 64-bit little-endian word from byte list `bs` starting at index `idx`. -/
def word64LE (bs : List (BitVec 8)) (idx : Nat) : BitVec 64 :=
  (bs.getD idx 0#8).zeroExtend 64 |||
  ((bs.getD (idx + 1) 0#8).zeroExtend 64 <<< 8) |||
  ((bs.getD (idx + 2) 0#8).zeroExtend 64 <<< 16) |||
  ((bs.getD (idx + 3) 0#8).zeroExtend 64 <<< 24) |||
  ((bs.getD (idx + 4) 0#8).zeroExtend 64 <<< 32) |||
  ((bs.getD (idx + 5) 0#8).zeroExtend 64 <<< 40) |||
  ((bs.getD (idx + 6) 0#8).zeroExtend 64 <<< 48) |||
  ((bs.getD (idx + 7) 0#8).zeroExtend 64 <<< 56)

/-- Relocated 64-bit little-endian pointer word stored at image-relative byte offset `off`
    (`img.base + BitVec.ofNat 64 off`) in `img`. -/
def rodataPtr (img : Obj.Image) (off : Nat) : BitVec 64 :=
  word64LE img.data (off - (img.dataAddr - img.base).toNat)

/-- Scan `rs` for an 8-byte `DataReloc` writing `[k, k + 8)` within `[0, dataLen)` whose
    subsequent relocations in `rs` are disjoint from `[k, k + 8)`. -/
def findRelocWordTarget (rs : List Obj.DataReloc) (dataLen k : Nat) : Option Nat :=
  match rs with
  | [] => none
  | r :: rs' =>
    if r.off + r.width ≤ dataLen then
      match findRelocWordTarget rs' dataLen k with
      | some t => some t
      | none =>
        if r.off == k && r.width == 8 && noRelocInRange rs' dataLen k 8 then
          some r.target
        else
          none
    else
      none

/-- Decidable check that image-relative offset `off` in `li` lies in a `.rodata`/`.data.rel.ro`
    range and is initialized by an 8-byte `DataReloc` targeting symbol `target`. -/
def checkRodataReloc (li : Obj.LinkedImage) (off : Nat) (target : String) : Bool :=
  li.dataOff < 2 ^ 64 &&
  li.dataOff ≤ off &&
  inLiRoData li off 8 &&
  match findRelocWordTarget li.relocs (li.data.length + li.bss) (off - li.dataOff) with
  | some t => t == li.toProgram.fnOff target
  | none => false

private theorem bytesLE_length (n : Nat) (w : BitVec 64) :
    (Obj.bytesLE n w).length = n := by
  simp [Obj.bytesLE]

private theorem dataReloc_apply_writes_word64 {base : BitVec 64} {d d' : List (BitVec 8)}
    {r : Obj.DataReloc} {dataLen : Nat}
    (hlen : d.length = dataLen) (hr : r.off + 8 ≤ dataLen) (hw : r.width = 8)
    (happ : Obj.DataReloc.apply base d r = .ok d') :
    d'.length = dataLen ∧ (d'.drop r.off).take 8 = Obj.bytesLE 8 (base + BitVec.ofNat 64 r.target) := by
  simp only [Obj.DataReloc.apply] at happ
  split at happ
  · contradiction
  · injection happ with hd'
    subst hd'
    have hbw : (Obj.bytesLE 8 (base + BitVec.ofNat 64 r.target)).length = 8 :=
      bytesLE_length 8 _
    have htake_len : (d.take r.off).length = r.off := by
      simp [List.length_take]; omega
    have hdrop_len : (d.drop (r.off + 8)).length = dataLen - (r.off + 8) := by
      simp [List.length_drop, hlen]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, List.length_append, htake_len, hw, hbw, hdrop_len]
      omega
    · rw [List.append_assoc, List.drop_append_of_le_length (by omega),
        List.drop_eq_nil_of_le (by omega), List.nil_append,
        List.take_append_of_le_length (by rw [hw, hbw]; omega)]
      rw [hw]
      exact List.take_of_length_le (by rw [hbw]; omega)

private theorem foldlM_dataReloc_writes_word64 {base : BitVec 64} :
    ∀ (rs : List Obj.DataReloc) (d d' : List (BitVec 8)) (dataLen k t : Nat),
      d.length = dataLen →
      findRelocWordTarget rs dataLen k = some t →
      rs.foldlM (Obj.DataReloc.apply base) d = .ok d' →
      d'.length = dataLen ∧ (d'.drop k).take 8 = Obj.bytesLE 8 (base + BitVec.ofNat 64 t)
  | [], _, _, _, _, _, _, hfind, _ => by simp [findRelocWordTarget] at hfind
  | r :: rs, d, d', dataLen, k, t, hlen, hfind, hfold => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    split at hfold
    · contradiction
    · rename_i d1 happ
      simp only [findRelocWordTarget] at hfind
      split at hfind
      · rename_i hbound
        have hlen1 : d1.length = dataLen := by
          simp only [Obj.DataReloc.apply] at happ
          split at happ
          · contradiction
          · injection happ with hd1
            subst hd1
            have htake1 : (d.take r.off).length = r.off := by
              simp [List.length_take]; omega
            rw [List.length_append, List.length_append, htake1, bytesLE_length, List.length_drop]
            omega
        split at hfind
        · rename_i t' hrec
          injection hfind with ht; subst ht
          exact foldlM_dataReloc_writes_word64 rs d1 d' dataLen k t' hlen1 hrec hfold
        · split at hfind
          · rename_i hhit
            injection hfind with ht; subst ht
            simp only [Bool.and_eq_true, beq_iff_eq] at hhit
            obtain ⟨⟨hoff, hw⟩, hno⟩ := hhit
            subst hoff
            obtain ⟨_, hw1⟩ := dataReloc_apply_writes_word64 hlen (by omega) hw happ
            obtain ⟨hlen2, hsl2⟩ := foldlM_dataReloc_preserves_slice rs d1 d' dataLen r.off 8 hlen1 hno hfold
            exact ⟨hlen2, hsl2.trans hw1⟩
          · contradiction
      · contradiction

private theorem word64LE_bytesLE_8 (v : BitVec 64) :
    word64LE (Obj.bytesLE 8 v) 0 = v := by
  have h : word64LE (Obj.bytesLE 8 v) 0 =
    ((v >>> 0).truncate 8).zeroExtend 64 |||
    (((v >>> 8).truncate 8).zeroExtend 64 <<< 8) |||
    (((v >>> 16).truncate 8).zeroExtend 64 <<< 16) |||
    (((v >>> 24).truncate 8).zeroExtend 64 <<< 24) |||
    (((v >>> 32).truncate 8).zeroExtend 64 <<< 32) |||
    (((v >>> 40).truncate 8).zeroExtend 64 <<< 40) |||
    (((v >>> 48).truncate 8).zeroExtend 64 <<< 48) |||
    (((v >>> 56).truncate 8).zeroExtend 64 <<< 56) := rfl
  rw [h]
  bv_bits

private theorem word64LE_eq_of_drop_take {bs bs' : List (BitVec 8)} {k : Nat}
    (hsl : (bs.drop k).take 8 = bs') (hlen' : bs'.length = 8) :
    word64LE bs k = word64LE bs' 0 := by
  have hlen_dt : ((bs.drop k).take 8).length = 8 := by rw [hsl, hlen']
  have hk : k + 8 ≤ bs.length := by simp [List.length_take, List.length_drop] at hlen_dt; omega
  have hget : ∀ j : Nat, j < 8 → bs.getD (k + j) 0#8 = bs'.getD j 0#8 := fun j hj => by
    have h1 : ((bs.drop k).take 8)[j]'(by omega) = bs'[j]'(by omega) := by simp only [hsl]
    rw [List.getElem_take, List.getElem_drop] at h1
    have hj_k : k + j < bs.length := by omega
    have hj_b : j < bs'.length := by omega
    simp only [List.getD, List.getElem?_eq_getElem hj_k, List.getElem?_eq_getElem hj_b]
    exact h1
  have h0 : bs.getD k 0#8 = bs'.getD 0 0#8 := by simpa using hget 0 (by omega)
  simp only [word64LE, h0,
    hget 1 (by omega), hget 2 (by omega), hget 3 (by omega),
    hget 4 (by omega), hget 5 (by omega), hget 6 (by omega), hget 7 (by omega)]

/-- Kernel-reflection bridge for `.rodata`/`.data.rel.ro` `R_AARCH64_ABS64` pointer relocations:
    whenever `checkRodataReloc li off target = true` (discharged by `rfl_kernel`), any loaded
    image `img` (`Obj.Loads li img`) satisfies `rodataPtr img off = img.fnAddr target`. -/
theorem rodataPtr_eq_fnAddr_of_loads {li : Obj.LinkedImage} {img : Obj.Image}
    {off : Nat} {target : String}
    (himg : Obj.Loads li img)
    (hcheck : checkRodataReloc li off target = true) :
    rodataPtr img off = img.fnAddr target := by
  simp only [checkRodataReloc, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨hdo_lt, hoff⟩, hro⟩, hrel⟩ := hcheck
  split at hrel
  · rename_i t hfind
    simp only [beq_iff_eq] at hrel
    obtain ⟨data, hfold, _, _, _, himg_eq⟩ := ProofLib.ObjectLoad.load_eq_ok himg
    have haddr : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff :=
      congrArg Obj.Image.dataAddr himg_eq
    have hcode : img.code = li.code := congrArg Obj.Image.code himg_eq
    have hdata : img.data = data := congrArg Obj.Image.data himg_eq
    have hsyms : img.symbols = li.symbols := congrArg Obj.Image.symbols himg_eq
    have hstubs : img.stubs = li.stubs := congrArg Obj.Image.stubs himg_eq
    have hlen0 : (li.data ++ List.replicate li.bss 0).length = li.data.length + li.bss := by simp
    obtain ⟨_, hsl⟩ :=
      foldlM_dataReloc_writes_word64 li.relocs (li.data ++ List.replicate li.bss 0) data
        (li.data.length + li.bss) (off - li.dataOff) t hlen0 hfind hfold
    have hidx : (img.dataAddr - img.base).toNat = li.dataOff := by
      rw [haddr, show img.base + BitVec.ofNat 64 li.dataOff - img.base =
        BitVec.ofNat 64 li.dataOff from by bv_lin, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdo_lt]
    rw [rodataPtr, hidx, hdata,
      word64LE_eq_of_drop_take hsl (bytesLE_length 8 _),
      word64LE_bytesLE_8, hrel]
    simp [Arm64.Obj.Image.fnAddr, Program.ofImage, Obj.LinkedImage.toProgram,
      Program.fnAddr, Program.fnOff, Program.findSymbol?, hcode, hsyms, hstubs]
  · contradiction

/-- Every relocated `.rodata`/`.data.rel.ro` pointer slot verified by `checkRodataReloc` is mapped
    read-only (`Perm.ro`) with bytes `bytesLE 8 (rodataPtr img off)` under `img.RoDataLoaded`. -/
theorem holdsBytes_ro_rodataPtr {li : Obj.LinkedImage} {img : Obj.Image} {m : Memory}
    {off : Nat} {target : String}
    (himg : Obj.Loads li img)
    (hcheck : checkRodataReloc li off target = true)
    (hro_mem : img.RoDataLoaded m) :
    Obj.HoldsBytes m (img.base + BitVec.ofNat 64 off)
      (Obj.bytesLE 8 (rodataPtr img off)) (fun _ => .ro) := by
  have heq := rodataPtr_eq_fnAddr_of_loads himg hcheck
  simp only [checkRodataReloc, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨_, hoff⟩, hro⟩, hrel⟩ := hcheck
  split at hrel
  · rename_i t hfind
    simp only [beq_iff_eq] at hrel
    obtain ⟨data, hfold, _, _, _, himg_eq⟩ := ProofLib.ObjectLoad.load_eq_ok himg
    have haddr : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff :=
      congrArg Obj.Image.dataAddr himg_eq
    have hcode : img.code = li.code := congrArg Obj.Image.code himg_eq
    have hdata : img.data = data := congrArg Obj.Image.data himg_eq
    have hro_map : img.roData = li.roData.map (fun (o, m) => (img.base + BitVec.ofNat 64 o, m)) :=
      congrArg Obj.Image.roData himg_eq
    have hsyms : img.symbols = li.symbols := congrArg Obj.Image.symbols himg_eq
    have hstubs : img.stubs = li.stubs := congrArg Obj.Image.stubs himg_eq
    have hlen0 : (li.data ++ List.replicate li.bss 0).length = li.data.length + li.bss := by simp
    obtain ⟨hd_len, hsl⟩ :=
      foldlM_dataReloc_writes_word64 li.relocs (li.data ++ List.replicate li.bss 0) data
        (li.data.length + li.bss) (off - li.dataOff) t hlen0 hfind hfold
    simp only [inLiRoData, List.any_eq_true, decide_eq_true_eq] at hro
    obtain ⟨⟨rOff, rLen⟩, hr_mem, hr_le1, hr_le2, hr_lt⟩ := hro
    intro j hj
    rw [bytesLE_length] at hj
    have hv_eq : rodataPtr img off = img.base + BitVec.ofNat 64 t := by
      rw [heq, hrel]
      simp [Arm64.Obj.Image.fnAddr, Program.ofImage, Obj.LinkedImage.toProgram,
        Program.fnAddr, Program.fnOff, Program.findSymbol?, hcode, hsyms, hstubs]
    have hsl_len : ((img.data.drop (off - li.dataOff)).take 8).length = 8 := by
      rw [hdata, hsl, bytesLE_length]
    have hsl' : j < ((img.data.drop (off - li.dataOff)).take 8).length := by omega
    have hi : (off - li.dataOff) + j < img.data.length := by
      simp [List.length_take, List.length_drop] at hsl_len; omega
    have ha_eq : img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j) =
        img.base + BitVec.ofNat 64 off + BitVec.ofNat 64 j := by
      rw [haddr, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 2; omega
    have hisRo : img.isRoData (img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j)) = true := by
      simp only [Obj.Image.isRoData, hro_map, List.any_map, List.any_eq_true]
      refine ⟨(rOff, rLen), hr_mem, ?_⟩
      simp only [Function.comp_apply, decide_eq_true_eq,
        show img.dataAddr + BitVec.ofNat 64 ((off - li.dataOff) + j) =
          img.base + BitVec.ofNat 64 (off + j) from by
          rw [ha_eq, BitVec.add_assoc, ← BitVec.ofNat_add]]
      rw [bv_add_sub_add_of_le img.base (by omega) (by omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨hread, hperm, hlf⟩ := hro_mem ((off - li.dataOff) + j) hi hisRo
    have hbyte : (Obj.bytesLE 8 (rodataPtr img off))[j]'(by rw [bytesLE_length]; exact hj) =
        img.data[(off - li.dataOff) + j] := by
      have h1 : ((img.data.drop (off - li.dataOff)).take 8)[j]'hsl' =
          (Obj.bytesLE 8 (rodataPtr img off))[j]'(by rw [bytesLE_length]; exact hj) := by
        simp only [hdata, hsl, hv_eq]
      rw [← h1, List.getElem_take, List.getElem_drop]
    rw [← ha_eq, hbyte]
    exact ⟨hread, hperm, hlf⟩
  · contradiction

/-- Introduce a read-only 64-bit pointer assertion `(img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ rodataPtr img off`
    into the `SepWP` spatial context `P` for any relocation verified by `checkRodataReloc`. -/
theorem SepWP.rodataPtr_intro {prog : Program} {target_pc : BitVec 64}
    {li : Obj.LinkedImage} {img : Obj.Image} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    {off : Nat} {target : String}
    (himg : Obj.Loads li img)
    (hcheck : checkRodataReloc li off target = true)
    (hro : img.RoDataLoaded s.mem)
    (h : SepWP prog target_pc s (((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ rodataPtr img off) ∗ P) post) :
    SepWP prog target_pc s P post := by
  have hb := holdsBytes_ro_rodataPtr himg hcheck hro
  rw [bytesLE_eight_eq_unpack64] at hb
  exact SepWP.holdsBytes_ro_intro hb (by simp [unpack64])
    (by simpa [pointsTo64RO_eq_pointsToBytesRO] using h)

private theorem calleeSavedPreserved_of_blr_step {s sf : State} {lrVal pcVal : BitVec 64}
    (hcs : CalleeSavedPreserved ((s.writeReg64 Reg.lr lrVal).setPC pcVal) sf) :
    CalleeSavedPreserved s sf := by
  simpa [CalleeSavedPreserved, State.setPC, State.writeReg64, State.readReg64] using hcs

/-- Compositional `SepWP` rule for an indirect subroutine call (`BLR rn`) discharged via
    `FnPtrSpec prog (s.readReg64 rn) spec`. Advances from `pc` to `pc + 4#64`,
    preserving the caller frame `F`, stack pointer `s.sp`, and `CalleeSavedPreserved s sf`. -/
theorem wp_blr_of_fnPtrSpec {α : Type} {prog : Program} {pc target_pc : BitVec 64}
    {rn : Reg} {spec : Spec α} {s : State}
    (hfn : FnPtrSpec prog (s.readReg64 rn) spec)
    {x : α} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hfetch : prog.fetch pc = some (.blr rn))
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) →
      (s.mem ⊨ spec.pre x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked →
      ¬(sf.mem ⊨ spec.onPanic x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code →
      ¬(sf.mem ⊨ spec.onExit x code ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = pc + 4#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (spec.post x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ F) post oom)
    (h_oom : ∀ R sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x ((s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn)) sf ∗ (F ∗ R)) →
      (sf.mem ⊨ oom sf ∗ R) := by
      intro _ _ _ ho
      try simp only [wp_unfold, Spec.noPanic, Spec.allowPanicWhen, Spec.allowPanic, Spec.panicsOr, Spec.allowOom] at ho ⊢
      first | exact ho | exact False.elim (not_satisfies_false_sepConj ho) | exact satisfies_true_sepConj_frame ho | exact Satisfies.drop_mid ho) :
    SepWP prog target_pc s P post oom := by
  have hs_pc : s.setPC pc = s := by
    cases s; simp [State.setPC] at hpc ⊢; exact hpc.symm
  have hexec : prog.evalInst (.blr rn) (s.setPC pc) =
      (s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn) := by
    rw [hs_pc]; simp only [Program.evalInst, execInstWithSvc, hpc]
  refine SepWP.step_pure (s' := (s.writeReg64 Reg.lr (pc + 4#64)).setPC (s.readReg64 rn))
    hpc hrun hfetch hexec rfl ?_
  refine SepWP.call_subroutine_frame (entry := s.readReg64 rn) (ret_pc := pc + 4#64)
    hfn rfl hrun hsp_align (by simp [State.setPC, State.writeReg64, State.readReg64])
    hpre h_no_panic h_no_exit ?_ h_oom
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  exact hnext sf hpc_sf hrun_sf hsp_sf (calleeSavedPreserved_of_blr_step hcs_sf)

end ProofLib
