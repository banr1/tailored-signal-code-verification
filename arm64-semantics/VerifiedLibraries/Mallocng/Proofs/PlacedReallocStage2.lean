/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocSizeToClass

/-!
# Placed `__libc_realloc` Stage 2: In-Place `set_size`

Verifies `+0x2cc` to `ret` (`realloc_stage2_inplace_ok`, `realloc_s2_finish_ok`) across all three
residual-slack branches (`res = 0`, `1 ≤ res ≤ 4`, `5 ≤ res`), absorbing the `.liveUser` slot
update into `MallocngPostEnv`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

theorem realloc_step_str8_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write8 ea val
  have htrunc : (s.readReg64 rt).truncate 8 = val := by
    rw [← hval]; dsimp only [State.readReg32]; bv_bits
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, htrunc, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write8 _ _ _) (Memory.keepsFrozen_write8 hcan val)) hm'

theorem sepWP_bupd_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hb : P ⊢ |==> Q) (hwp : SepWP prog target_pc s Q post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm' : s.mem ⊨ Q ∗ R :=
    (satisfies_bupd (Q ∗ R) s.mem).mp
      (Satisfies.mono (Entails.trans (sepConj_mono_left hb) (bupd_frame_r Q R)) hm)
  exact SepWP.to_reaches_pc hwp hm'

theorem sepStore8_byteSlice {base ea : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {val val' : BitVec 8} {Rest : SepProp}
    (hval : val = val') (hea : ea = base + BitVec.ofNat 64 off) (hoff : off + 1 ≤ bs.length) :
    SepStore8 ea val ((base ↦ₛ bs) ∗ Rest) ((base ↦ₛ ByteSlice.write8 bs off val') ∗ Rest) := by
  subst hval hea
  rw [pointsToBytes_focus8 base bs off (by omega), ← pointsToBytes_update8 base bs off val hoff]
  wp_sep_access

theorem sepStore32_byteSlice {base ea : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {val val' : BitVec 32} {Rest : SepProp}
    (hval : val = val') (hea : ea = base + BitVec.ofNat 64 off) (hoff : off + 4 ≤ bs.length) :
    SepStore32 ea val ((base ↦ₛ bs) ∗ Rest) ((base ↦ₛ ByteSlice.write32 bs off val') ∗ Rest) := by
  subst hval hea
  rw [pointsToBytes_focus32 base bs off hoff, ← pointsToBytes_update32 base bs off val hoff]
  wp_sep_access

theorem sepStore64_byteSlice {base ea : BitVec 64} {bs : List (BitVec 8)} {off : Nat}
    {val val' : BitVec 64} {Rest : SepProp}
    (hval : val = val') (hea : ea = base + BitVec.ofNat 64 off) (hoff : off + 8 ≤ bs.length) :
    SepStore64 ea val ((base ↦ₛ bs) ∗ Rest) ((base ↦ₛ ByteSlice.write64 bs off val') ∗ Rest) := by
  subst hval hea
  rw [pointsToBytes_focus64 base bs off hoff, ← pointsToBytes_update64 base bs off val hoff]
  wp_sep_access

theorem mallocngPostEnv_congr_state {J : MallocngIface} {γ : GhostName} {A : MallocngAddrs}
    {tp brkStart : BitVec 64} {bf : MallocngBudget} {ivs0 : List (BitVec 64 × Nat)}
    {s0 s1 s2 : State}
    (hmem : s2.mem = s1.mem) (hbrk : s2.brk = s1.brk)
    (htp : s2.tpidrEl0 = s1.tpidrEl0) (hbrks : s2.brkStart = s1.brkStart) :
    MallocngPostEnv J γ A tp brkStart bf ivs0 s0 s1 =
      MallocngPostEnv J γ A tp brkStart bf ivs0 s0 s2 := by
  unfold MallocngPostEnv MallocngEnv
  simp only [hmem, hbrk, htp, hbrks]

theorem reallocSavedHi_eq (s0 : State) :
    ReallocSavedHi s0 (s0.sp - 80#64) =
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x26)) := by
  unfold ReallocSavedHi
  rw [show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
      show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin,
      show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
      show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]

theorem inPlace_oldCap_bounds {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    (userBs : List (BitVec 8)) :
    let start := g.slotStart idx
    let hdrOff := p.toNat - start.toNat + 1
    let bs0 := mkLiveUserSlotBs st.byteVal g idx oldSz p userBs
    start.toNat ≤ p.toNat ∧
    p.toNat + oldSz ≤ (g.slotEnd idx).toNat ∧
    4 ≤ start.toNat ∧
    (start - 4#64).toNat = start.toNat - 4 ∧
    (g.slotEnd idx).toNat = (start - 4#64).toNat + g.stride ∧
    (start - 4#64).toNat + g.stride ≤ 2 ^ 48 ∧
    (g.slotEnd idx).toNat - p.toNat ≤ 1048576 ∧
    idx ≤ 31 ∧
    ((bs0.getD hdrOff 0#8).zeroExtend 32 &&& 0x1f#32) = BitVec.ofNat 32 idx := by
  intro start hdrOff bs0
  have hgw := hwf.groups_wf g hg
  have hLast31 : g.lastIdx ≤ 31 := hgw.2.1
  have hSlotsCnt : g.slots.length = g.cnt := hgw.2.2.1
  have hIdx31 : idx ≤ 31 := by dsimp only [GroupDesc.cnt] at hSlotsCnt; omega
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  rw [hSlot] at hsw
  obtain ⟨_, _, _, _, _, hULo, hUHi, _, _, _, _, _, hHdrP3, _, _, _⟩ := hsw
  have ⟨_, _, hSt, hSub4, hEn, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  obtain ⟨hSc48, _⟩ := inPlace_sc_eff_bound (extraEff := oldEff - max oldSz MallocngMinBlockCost)
    hNewMax hgw.1 hScLe
  have hTotSmall : g.totalBytes ≤ 1048576 := by
    by_cases hMp : 0 < g.maplen
    · have hM := ((hgw.2.2.2.2.2.2.2.2.2.2.2.1 hMp).2.2.2 hSc48).1
      simp [GroupDesc.totalBytes, hMp, hM]
    · have hM0 : g.maplen = 0 := by omega
      obtain ⟨_, pg, _, _, _, _, hPg48, _, _, _, _, _, hNCap⟩ := hgw.2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
      obtain ⟨_, hPgHi, _, _⟩ := sizeClass_bounds hPg48
      simp only [GroupDesc.totalBytes, hM0, Nat.lt_irrefl, ↓reduceIte, hNCap, slotStride]
      omega
  dsimp only [start, hdrOff, bs0]
  refine ⟨hULo, hUHi, by omega, by omega, by omega, by omega, by omega, hIdx31, ?_⟩
  have hGetHdr : (mkLiveUserSlotBs st.byteVal g idx oldSz p userBs).getD
      (p.toNat - (g.slotStart idx).toNat + 1) 0#8 = st.byteVal (p - 3#64) := by
    dsimp only [mkLiveUserSlotBs]
    rw [List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_left (by rw [readBytesFromMap_length]; omega),
      List.getElem?_eq_getElem (by rw [readBytesFromMap_length]; omega),
      Option.getD_some, readBytesFromMap_getElem]
    congr 1
    exact (fun (s q : BitVec 64) (_ : 4 ≤ s.toNat) (_ : s.toNat ≤ q.toNat) (_ : q.toNat < 2 ^ 48) =>
      (by bv_omega : s - 4#64 + BitVec.ofNat 64 (q.toNat - s.toNat + 1) = q - 3#64))
      (g.slotStart idx) p (by omega) hULo (by omega)
  rw [hGetHdr, hHdrP3]
  exact (hdrByte_extract _ idx (Nat.min_le_right _ _) hIdx31).1

theorem bupd_frame_mid {A B C D E : SepProp} :
    A ∗ B ∗ C ∗ ((|==> D) ∗ E) ⊢ |==> (A ∗ B ∗ C ∗ (D ∗ E)) :=
  Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (bupd_frame_r D E))))
    (Entails.trans (sepConj_mono_right (sepConj_mono_right (bupd_frame_l C (D ∗ E))))
      (Entails.trans (sepConj_mono_right (bupd_frame_l B (C ∗ (D ∗ E))))
        (bupd_frame_l A (B ∗ (C ∗ (D ∗ E))))))

theorem sp_sub80_align16 {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 80#64) &&& 15#64 = 0#64 := by revert h; bv_robdd

theorem subs32_cap_newSz {cap newSz : Nat}
    (hFit : newSz ≤ cap) (hCap64 : cap < 2 ^ 64) (hRes31 : cap - newSz < 2 ^ 31) :
    (BitVec.ofNat 64 cap).truncate 32 - (BitVec.ofNat 64 newSz).truncate 32 =
      BitVec.ofNat 32 (cap - newSz) ∧
    ((BitVec.ofNat 64 cap).truncate 32 = (BitVec.ofNat 64 newSz).truncate 32 ↔
      cap - newSz = 0) := by
  have hSplit : BitVec.ofNat 64 cap = BitVec.ofNat 64 newSz + BitVec.ofNat 64 (cap - newSz) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hCap64, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hSubId : ∀ a d : BitVec 64, (a + d).truncate 32 - a.truncate 32 = d.truncate 32 := by
    intro a d; bv_robdd
  have hEqId : ∀ a d : BitVec 64, ((a + d).truncate 32 = a.truncate 32) ↔ d.truncate 32 = 0#32 := by
    intro a d; bv_robdd
  have hTrRes : (BitVec.ofNat 64 (cap - newSz)).truncate 32 = BitVec.ofNat 32 (cap - newSz) := by
    generalize cap - newSz = r at hRes31 ⊢; bv_omega
  rw [hSplit, hSubId, hEqId, hTrRes]
  refine ⟨rfl, ⟨fun h0 => ?_, fun h0 => by rw [h0]⟩⟩
  have ht := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  exact ht

theorem idx_trunc8_eq_hdr0 {idx res : Nat} (hRes0 : res = 0) (_hIdx31 : idx ≤ 31) :
    (BitVec.ofNat 32 idx).truncate 8 =
      BitVec.ofNat 8 (((min res 5) <<< 5) ||| idx) := by
  subst hRes0
  have hMin : ((min 0 5) <<< 5) ||| idx = idx := by simp
  rw [hMin]
  bv_omega

theorem slot_set_size_addrs {start slotEnd p : BitVec 64} {stride newSz : Nat}
    (hLo : start.toNat ≤ p.toNat) (hSt4 : 4 ≤ start.toNat)
    (hEn : slotEnd.toNat = (start - 4#64).toNat + stride)
    (h48 : (start - 4#64).toNat + stride ≤ 2 ^ 48)
    (hFit : p.toNat + newSz ≤ slotEnd.toNat) :
    let base := start - 4#64
    let hdrOff := p.toNat - start.toNat + 1
    let res := slotEnd.toNat - (p.toNat + newSz)
    p - 3#64 = base + BitVec.ofNat 64 hdrOff ∧
    p + (-3#64) = base + BitVec.ofNat 64 hdrOff ∧
    (1 ≤ res → res < 2 ^ 31 → slotEnd + (-BitVec.ofNat 32 res).signExtend 64 =
      base + BitVec.ofNat 64 (hdrOff + 3 + newSz)) ∧
    (5 ≤ res → slotEnd + (-5#64) = base + BitVec.ofNat 64 (stride - 5) ∧
      slotEnd + (-4#64) = base + BitVec.ofNat 64 (stride - 4)) := by
  intro base hdrOff res
  have hSub4 : base.toNat = start.toNat - 4 := by dsimp only [base]; bv_omega
  have h1 : p - 3#64 = base + BitVec.ofNat 64 hdrOff := by
    dsimp only [base, hdrOff] at hSub4 ⊢; bv_omega
  refine ⟨h1, (by bv_lin : p + (-3#64) = p - 3#64).trans h1, fun hR1 hR31 => ?_, fun hR5 => ⟨?_, ?_⟩⟩
  · rw [neg32_sxtw_of_pos_lt31 hR1 hR31,
        show slotEnd + (-BitVec.ofNat 64 res) = slotEnd - BitVec.ofNat 64 res by bv_lin]
    dsimp only [base, hdrOff, res] at hSub4 hEn h48 ⊢; bv_omega
  · rw [show slotEnd + (-5#64) = slotEnd - 5#64 by bv_lin]
    dsimp only [base, res] at hSub4 hEn h48 hR5 ⊢; bv_omega
  · rw [show slotEnd + (-4#64) = slotEnd - 4#64 by bv_lin]
    dsimp only [base, res] at hSub4 hEn h48 hR5 ⊢; bv_omega

theorem satisfies_readRest_wf {m : Memory} {γ : GhostName} {A : MallocngAddrs}
    {tp brkStart brk : BitVec 64} {b : MallocngBudget} {ivs : List (BitVec 64 × Nat)}
    {st : MallocngSt} {Rest : SepProp}
    (hm : m ⊨ MallocngReadRest γ A tp brkStart brk b ivs st ∗ Rest) :
    MallocngCountIvsWF b ivs st ∧ MallocngWF A.base brkStart brk b.liveCost b.peakCost st := by
  unfold MallocngReadRest at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1

theorem sepWP_pure_of_sat {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : SepProp} {φ : Prop} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hsat : ∀ R, (s.mem ⊨ P ∗ R) → φ)
    (h : φ → SepWP prog target_pc s P post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  exact SepWP.to_reaches_pc (h (hsat R hm)) hm

theorem sepWP_abstract_env {prog : Program} {target_pc : BitVec 64} {s : State}
    {A Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ (Rest' : SepProp) (post' : State → SepProp → Prop),
      Rest' = Rest → post' = post → SepWP prog target_pc s (A ∗ Rest') post' oom) :
    SepWP prog target_pc s (A ∗ Rest) post oom :=
  h Rest post rfl rfl

scoped macro "wp_str8_slice" m:ident hm:ident off:term:max val:term:max hVal:term:max hAddr:term:max hOff:term:max : tactic => `(tactic| (
  apply realloc_step_str8_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs)
  (wp_focus_close (apply sepStore8_byteSlice (off := $off) (val' := $val); { exact $hVal }; { exact $hAddr }; { exact $hOff }))
  (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str32_slice" m:ident hm:ident off:term:max val:term:max hVal:term:max hAddr:term:max hOff:term:max : tactic => `(tactic| (
  apply step_str32_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs)
  (wp_focus_close (apply sepStore32_byteSlice (off := $off) (val' := $val); { exact $hVal }; { exact $hAddr }; { exact $hOff }))
  (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str64_slice" m:ident hm:ident off:term:max val:term:max hVal:term:max hAddr:term:max hOff:term:max : tactic => `(tactic| (
  apply step_str64_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs)
  (wp_focus_close (apply sepStore64_byteSlice (off := $off) (val' := $val); { exact $hVal }; { exact $hAddr }; { exact $hOff }))
  (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

set_option maxHeartbeats 400000 in
/-- Shared reconvergence tail (`+0x2fc` to `ret`) for all three branches of in-place `set_size`. -/
theorem realloc_s2_finish_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz al : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {bsCur : List (BitVec 8)} {Frame : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2fc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = p)
    (hw4 : (s.readReg32 .x4).truncate 8 =
      BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (hcs : ReallocUntouchedCS s0 s)
    (hBs0Len : (mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs)).length = g.stride)
    (hCurLen : bsCur.length = g.stride)
    (hLo : (g.slotStart idx).toNat ≤ p.toNat) (hSt4 : 4 ≤ (g.slotStart idx).toNat)
    (hEn : (g.slotEnd idx).toNat = (g.slotStart idx - 4#64).toNat + g.stride)
    (h48 : (g.slotStart idx - 4#64).toNat + g.stride ≤ 2 ^ 48)
    (hPost : SetSizeSlicePost (mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs))
      (p.toNat - (g.slotStart idx).toNat + 1) g.stride newSz
      (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
      (ByteSlice.write8 bsCur (p.toNat - (g.slotStart idx).toNat + 1)
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx)))) :
    let sp1 := s0.sp - 80#64
    let base := g.slotStart idx - 4#64
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((base ↦ₛ bsCur) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
        MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
        MallocngTightBlock γ p oldSz al ∗ Frame))
      (fun sf Pf => sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
          ⌜(MallocngTightInitBlock γ al).pureWf p (newSz, keptBs)⌝ ∗
          (MallocngTightInitBlock γ al).interp p (newSz, keptBs) ∗
          Frame)) oom := by
  intro sp1 base bf keptBs
  have _ := hb
  let hdrOff := p.toNat - (g.slotStart idx).toNat + 1
  obtain ⟨hAddrP3Sub, _, _, _⟩ := slot_set_size_addrs hLo hSt4 hEn h48 hFit
  have hspAlign1 : (s0.sp - 80#64) &&& 15#64 = 0#64 := sp_sub80_align16 hsp0
  let bsFinal := ByteSlice.write8 bsCur hdrOff
    (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
  have hTail : ∀ {m1 : Memory} {s2 : State},
      m1.perm = s.mem.perm →
      s2.pc = b + 0x294#64 → s2.status = .Running → s2.mem = m1 → s2.brk = s0.brk →
      MallocngProcPreserved s0 s2 → s2.sp = s0.sp - 80#64 → s2.spAligned = true →
      s2.readReg64 .x20 = p →
      s2.readReg64 .x23 = s0.readReg64 .x23 → s2.readReg64 .x24 = s0.readReg64 .x24 →
      s2.readReg64 .x25 = s0.readReg64 .x25 → s2.readReg64 .x26 = s0.readReg64 .x26 →
      ReallocUntouchedCS s0 s2 →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s2
        ((base ↦ₛ bsFinal) ∗
         (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 720 ∗
          (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
           ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
           MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
           MallocngTightBlock γ p oldSz al ∗ Frame)))
        (fun sf Pf => sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngTightInitBlock γ al).pureWf p (newSz, keptBs)⌝ ∗
            (MallocngTightInitBlock γ al).interp p (newSz, keptBs) ∗ Frame)) oom := by
    intro m1 s2 hm1Perm hpc2 hrun2 hmem2 hbrk2 hproc2 hsp2 hal2 hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
    have hm1Perm0 : m1.perm = s0.mem.perm := hm1Perm.trans hPerm
    refine SepWP.weaken_pre (P' :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
         (base ↦ₛ bsFinal) ∗ MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
         MallocngTightBlock γ p oldSz al) ∗ Frame)
      (Entails.of_eq (by
        dsimp only [base]
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
        ac_rfl)) ?_
    apply sepWP_bupd_pre (Q :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗
        (memRegion (s0.sp - 80#64 + 48#64) 8 ∗ memRegion (s0.sp - 80#64 + 56#64) 8 ∗
         memRegion (s0.sp - 80#64 + 64#64) 8 ∗ memRegion (s0.sp - 80#64 + 72#64) 8) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 s2 ∗
         ⌜(MallocngTightInitBlock γ al).pureWf p (newSz, keptBs)⌝ ∗
         (MallocngTightInitBlock γ al).interp p (newSz, keptBs) ∗ Frame))
    · have hSub4 : (g.slotStart idx - 4#64).toNat = (g.slotStart idx).toNat - 4 :=
        bv64_sub_toNat (by omega)
      have hAbs := reallocInPlace_absorb (al := al) γ maddrs tp brkStart bgt ivs0 s0 s2
        st hg hIdx origBs tailBs hOrigLen hTailLen hSlot hNewMax hFit hScLe
        (hproc2.2.2.1.trans htp0) (hproc2.2.2.2.1.trans hbrks0)
        (mallocngMappedDelta_of_perm_eq (hmem2 ▸ hm1Perm0))
        bsFinal (hPost.1.trans hBs0Len)
        (fun i hi hiNe => hPost.2.1 i (by omega) hiNe)
        hPost.2.2.1
        (fun h1 => by
          have h1' : bsFinal.getD (p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz) 0#8 = 0#8 :=
            hPost.2.2.2.1 (by omega)
          rwa [show p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz =
            p.toNat - (g.slotStart idx).toNat + 4 + newSz by omega] at h1')
        (fun h5 => by
          obtain ⟨h5a, h5b⟩ := hPost.2.2.2.2.1 (by omega)
          refine ⟨h5a, fun j hj => ?_⟩
          have h5bj : bsFinal.getD (g.stride - 4 + j) 0#8 = _ := h5b j hj
          rwa [show g.stride - (p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz) =
            (g.slotEnd idx).toNat - (p.toNat + newSz) by omega] at h5bj)
      rw [hbrk2] at hAbs
      refine Entails.trans (sepConj_mono_right (sepConj_mono (reallocSavedHi_entails_memRegions s0 _)
        (sepConj_mono_right (sepConj_mono_left hAbs)))) ?_
      exact Entails.trans bupd_frame_mid (bupd_mono (Entails.of_eq (by ac_rfl)))
    · refine SepWP.mono (realloc_epilogue_ok hb hpc2 hrun2 hsp2 hal2 hsp0
        hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2) ?_
      intro sf Pf _ _ ⟨hsfMem, hsfBrk, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
      have hMemM1 : sf.mem = m1 := hsfMem.trans hmem2
      have hBrk0 : sf.brk = s0.brk := hsfBrk.trans hbrk2
      have hProc0 : MallocngProcPreserved s0 sf := by
        obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hproc2
        obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hsfProc
        exact ⟨q1.trans p1, q2.trans p2, q3.trans p3, q4.trans p4, q5.trans p5, q6.trans p6, q7.trans p7⟩
      refine ⟨hMemM1 ▸ hm1Perm0, hBrk0, hProc0, hsfSp, hsfCS, hsfX0, Entails.trans hPf ?_⟩
      rw [mallocngPostEnv_congr_state (s2 := sf) hsfMem hsfBrk hsfProc.2.2.1 hsfProc.2.2.2.1]
      exact Entails.of_eq (by ac_rfl)
  conv => arg 4; dsimp only [sp1]
  generalize hRestEnv : (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
    ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
    MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
    MallocngTightBlock γ p oldSz al ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post' = post →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  wp_str8_slice m1 hm1Perm hdrOff
    (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (by have hw4' := hw4; try dsimp only [Reg.x4] at hw4'; try simp only [wp_norm, arm64_norm] at hw4' ⊢; first | rfl | exact hw4')
    (by first | rfl | (try simp only [wp_norm, arm64_norm, hx19]; exact (by bv_lin : p + (-3#64) = p - 3#64).trans hAddrP3Sub))
    (by have := bv64_sub_toNat hSt4; rw [hCurLen]; dsimp only [hdrOff]; omega)
  conv => arg 4; rw [reallocSavedHi_eq s0]
  wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← reallocSavedHi_eq s0]
  subst hPostGoal; rw [← hRestEnv]
  exact hTail hm1Perm (by simp) (by simp [hrun]) (by simp) (by simp [hbrk])
    ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
     by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
    (by simp [hsp]) (by simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩

@[simp, arm64_norm, wp_norm] theorem zx32_zx64_and_0x1f (b8 : BitVec 8) :
    BitVec.zeroExtend 32 (BitVec.zeroExtend 64 b8 &&& 0x1f0000001f#64) =
      BitVec.zeroExtend 32 b8 &&& 0x1f#32 := by
  bv_robdd

@[simp, arm64_norm, wp_norm] theorem zx8_zx64_and_0xff (w : BitVec 32) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 w &&& 255#64) =
      BitVec.zeroExtend 8 (w &&& 0xff#32) := by
  bv_robdd

@[simp, arm64_norm, wp_norm] theorem zx8_zx32_zx64_and_0xff (w : BitVec 32) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 32 (BitVec.zeroExtend 64 w &&& 255#64)) =
      BitVec.zeroExtend 8 (w &&& 0xff#32) := by
  bv_robdd

theorem focus_hdr_byteSlice {base p : BitVec 64} {bs : List (BitVec 8)} {hdrOff : Nat}
    (hAddr : p - 3#64 = base + BitVec.ofNat 64 hdrOff) (hLt : hdrOff < bs.length) :
    (base ↦ₛ bs) = (((p - 3#64) ↦₈ bs.getD hdrOff 0#8) ∗
      ((base ↦ₛ bs.take hdrOff) ∗ ((base + BitVec.ofNat 64 (hdrOff + 1)) ↦ₛ bs.drop (hdrOff + 1)))) := by
  rw [pointsToBytes_focus8 base bs hdrOff hLt, ← hAddr]

set_option maxHeartbeats 400000 in
/-- Executes Stage 2 (`+0x2cc` to `ret`): updates `set_size(p, end, newSz)` in place across all
    three residual-slack cases (`res = 0`, `1 ≤ res ≤ 4`, `5 ≤ res`), absorbs the `.liveUser` slot
    update into `MallocngPostEnv`, and returns `p` via `realloc_epilogue_ok`. -/
theorem realloc_stage2_inplace_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz al : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {Frame : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2cc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4 : s.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s.readReg64 .x5 = g.slotEnd idx)
    (hx19 : s.readReg64 .x19 = p)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
       MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf => sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngPostEnv mallocngIface γ maddrs tp brkStart bf ivs0 s0 sf ∗
          ⌜(MallocngTightInitBlock γ al).pureWf p (newSz, keptBs)⌝ ∗
          (MallocngTightInitBlock γ al).interp p (newSz, keptBs) ∗
          Frame)) oom := by
  intro sp1 bf keptBs
  have _ := hb
  apply sepWP_pure_of_sat (fun R hm =>
    satisfies_readRest_wf (Rest := ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      stackFrameAt sp1 720 ∗ MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame ∗ R)
      (Satisfies.mono (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
        ac_rfl)) hm))
  rintro ⟨_, hwf⟩
  obtain ⟨hLo, _, hSt4, _hSub4, hEn, h48, hCapMax, hIdx31, hBs0Hdr⟩ :=
    inPlace_oldCap_bounds hwf hg hIdx hSlot hNewMax hScLe (origBs ++ tailBs)
  obtain ⟨hBs0Len, hSliceEq⟩ := liveUser_slotSlice_split hwf hg hIdx hSlot (origBs ++ tailBs)
    (by rw [List.length_append, hTailLen]; omega)
  let base := g.slotStart idx - 4#64
  let hdrOff := p.toNat - (g.slotStart idx).toNat + 1
  generalize hbs0 : mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs) = bs0 at hBs0Hdr hBs0Len hSliceEq
  let oldCap := (g.slotEnd idx).toNat - p.toNat
  let res := (g.slotEnd idx).toNat - (p.toNat + newSz)
  have hResEq : oldCap - newSz = res := by dsimp only [oldCap, res]; omega
  obtain ⟨hSub32, hEq32⟩ := subs32_cap_newSz (cap := oldCap) (newSz := newSz)
    (by dsimp only [oldCap]; omega) (by dsimp only [oldCap]; omega) (by dsimp only [oldCap]; omega)
  rw [hResEq] at hSub32 hEq32
  obtain ⟨hAddrP3Sub, _, hAddrZeroOf, hAddrEndOf⟩ := slot_set_size_addrs hLo hSt4 hEn h48 hFit
  refine SepWP.weaken_pre (P' :=
      (base ↦ₛ bs0) ∗
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
       MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
       MallocngTightBlock γ p oldSz al ∗ Frame))
    (Entails.of_eq (by
      have hAssoc : (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
           MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)) =
        ((ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
          MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st ∗
          MallocngTightBlock γ p oldSz al ∗ Frame) := by
        generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
        ac_rfl
      rw [hAssoc, hSliceEq]
      dsimp only [base]
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngReadRest γ maddrs tp brkStart s0.brk bgt ivs0 st) = PRest
      ac_rfl)) ?_
  have hCapFold : (g.slotStart idx).toNat - 4 + g.stride - p.toNat = oldCap := by
    dsimp only [oldCap]; omega
  have halOf : ∀ s' : State, s'.sp = s.sp → s'.spAligned = true := fun s' hsp' => by
    simp only [State.spAligned, hsp'] at hal ⊢; exact hal
  apply sepWP_abstract_env; intro RestS2 postGoal hRestS2 hPostGoal
  wp_step; wp_step
  wp_if heq
  ·
    have hRes0 : res = 0 := by
      try rw [hx3] at heq
      try rw [hx21] at heq
      try rw [hCapFold] at heq
      exact hEq32.mp heq
    subst hPostGoal hRestS2 hbs0
    exact realloc_s2_finish_ok hb γ tp brkStart bgt ivs0 s0 _ st hg hIdx origBs tailBs
      hOrigLen hTailLen hSlot hNewMax hFit hScLe (bsCur := mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs))
      (by simp) (by simp [hrun]) (by simpa using hPerm) (by simpa using hbrk)
      ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
       by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      htp0 hbrks0 (by simp [hsp]) (halOf _ (by simp)) hsp0 (by simp [hx19])
      (by try simp only [wp_norm, arm64_norm]; try rw [hx4]; exact idx_trunc8_eq_hdr0 hRes0 hIdx31)
      ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      hBs0Len hBs0Len hLo hSt4 hEn h48
      (setSize_case0 _ hdrOff g.stride newSz _ (by dsimp only [hdrOff, res] at hRes0 ⊢; omega)
        (by omega))
  ·
    have hResPos : 1 ≤ res := by
      have hNe0 : res ≠ 0 := fun h0 => heq (by
        try rw [hx3]
        try rw [hx21]
        try rw [hCapFold]
        exact hEq32.mpr h0)
      omega
    wp_step; wp_step
    have hSub32z : BitVec.zeroExtend 32 (BitVec.ofNat 64 oldCap) -
        BitVec.zeroExtend 32 (BitVec.ofNat 64 newSz) = BitVec.ofNat 32 res := hSub32
    have hAddrZero := hAddrZeroOf hResPos (by omega)
    wp_str8_slice m1 hm1Perm (hdrOff + 3 + newSz) 0#8 rfl
      (by try simp only [wp_norm, arm64_norm]
          try rw [hx5]
          try rw [hx3]
          try rw [hx21]
          try rw [hCapFold]
          try rw [hSub32]
          try rw [hSub32z]
          try rw [BitVec.zero_sub]
          try rw [BitVec.shiftLeft_zero]
          first | rfl | exact hAddrZero)
      (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)
    let bs1 := ByteSlice.write8 bs0 (hdrOff + 3 + newSz) 0#8
    have hBs1Len : bs1.length = g.stride :=
      (ByteSlice.write8_length _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)).trans hBs0Len
    wp_step
    wp_if hle4
    ·
      have hRes4 : res ≤ 4 := by
        try rw [hx3] at hle4
        try rw [hx21] at hle4
        try rw [hCapFold] at hle4
        try rw [hSub32] at hle4
        try rw [hSub32z] at hle4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            bv32_sle_iff_of_lt31 (by dsimp only [res]; omega) (by decide),
            decide_eq_true_eq] at hle4
        exact hle4
      have hBs1Hdr : bs1.getD hdrOff 0#8 = bs0.getD hdrOff 0#8 := by
        dsimp only [bs1]
        rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)]
        simp only [show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
      conv => arg 4; arg 1; rw [pointsToBytes_focus8 base bs1 hdrOff (by rw [hBs1Len]; dsimp only [hdrOff]; omega)]
      wp_step; wp_step; wp_step; wp_step; wp_step
      conv => arg 4; arg 1; rw [← pointsToBytes_focus8 base bs1 hdrOff (by rw [hBs1Len]; dsimp only [hdrOff]; omega)]
      have hPost1 := setSize_case1to4 bs0 hdrOff g.stride newSz
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
        (by dsimp only [hdrOff, res] at hResPos ⊢; omega)
        (by dsimp only [hdrOff, res] at hRes4 ⊢; omega) (by omega)
      refine (fun {sFin P post} (h : ∀ s', s' = sFin →
          SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s' P post oom) => h sFin rfl) ?_
      intro sFin hsFin
      have hpcF : sFin.pc = b + 0x2fc#64 := by subst hsFin; simp
      have hrunF : sFin.status = .Running := by subst hsFin; simp [hrun]
      have hPermF : sFin.mem.perm = s0.mem.perm := by subst hsFin; exact hm1Perm.trans hPerm
      have hbrkF : sFin.brk = s0.brk := by subst hsFin; simpa using hbrk
      have hprocF : MallocngProcPreserved s0 sFin := by
        subst hsFin
        exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
               by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by subst hsFin; simp [hsp]
      have halF : sFin.spAligned = true := halOf _ (by subst hsFin; simp)
      have hx19F : sFin.readReg64 .x19 = p := by subst hsFin; simp [hx19]
      have hw4F : (sFin.readReg32 .x4).truncate 8 =
          BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx) := by
        subst hsFin
        try simp only [wp_norm, arm64_norm]
        try rw [hx3]; try rw [hx21]; try rw [hCapFold]; try rw [hSub32]; try rw [hSub32z]
        try rw [hBs1Hdr]
        exact hdrByte_res1to4 hBs0Hdr hIdx31 hRes4
      have hcsF : ReallocUntouchedCS s0 sFin := by
        subst hsFin
        exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin
      subst hPostGoal hRestS2 hbs0
      exact realloc_s2_finish_ok hb γ tp brkStart bgt ivs0 s0 sFin st hg hIdx origBs tailBs
        hOrigLen hTailLen hSlot hNewMax hFit hScLe (bsCur := bs1)
        hpcF hrunF hPermF hbrkF hprocF htp0 hbrks0 hspF halF hsp0 hx19F hw4F hcsF
        hBs0Len hBs1Len hLo hSt4 hEn h48 hPost1
    ·
      have hRes5 : 5 ≤ res := by
        try rw [hx3] at hle4
        try rw [hx21] at hle4
        try rw [hCapFold] at hle4
        try rw [hSub32] at hle4
        try rw [hSub32z] at hle4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            bv32_sle_iff_of_lt31 (by dsimp only [res]; omega) (by decide),
            decide_eq_true_eq] at hle4
        omega
      obtain ⟨hAddrEnd5, hAddrEnd4⟩ := hAddrEndOf hRes5
      wp_str8_slice m2 hm2Perm (g.stride - 5) 0#8 rfl
        (by rw [← hAddrEnd5]; try simp only [wp_norm, arm64_norm, hx5]; bv_lin)
        (by rw [hBs1Len]; omega)
      let bs2 := ByteSlice.write8 bs1 (g.stride - 5) 0#8
      have hBs2Len : bs2.length = g.stride :=
        (ByteSlice.write8_length _ _ _ (by rw [hBs1Len]; omega)).trans hBs1Len
      wp_str32_slice m3 hm3Perm (g.stride - 4) (BitVec.ofNat 32 res)
        (by first | exact hSub32 | (first | exact hSub32z | (try simp only [wp_norm, arm64_norm]; try rw [hx3]; try rw [hx21]; try rw [hCapFold]; first | exact hSub32 | (first | exact hSub32z | rfl))))
        (by rw [← hAddrEnd4]; try simp only [wp_norm, arm64_norm, hx5]; bv_lin)
        (by rw [hBs2Len]; omega)
      let bs3 := ByteSlice.write32 bs2 (g.stride - 4) (BitVec.ofNat 32 res)
      have hBs3Len : bs3.length = g.stride :=
        (ByteSlice.write32_length _ _ _ (by rw [hBs2Len]; omega)).trans hBs2Len
      have hBs3Hdr : bs3.getD hdrOff 0#8 = bs0.getD hdrOff 0#8 := by
        dsimp only [bs3, bs2, bs1]
        rw [ByteSlice.getD_write32 _ _ _ _ _ (by rw [hBs2Len]; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs1Len]; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hRes5 ⊢; omega)]
        simp only [show ¬ (g.stride - 4 ≤ hdrOff ∧ hdrOff < g.stride - 4 + 4) by dsimp only [hdrOff, res] at hRes5 ⊢; omega,
          show hdrOff ≠ g.stride - 5 by dsimp only [hdrOff, res] at hRes5 ⊢; omega,
          show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
      conv => arg 4; arg 1; rw [pointsToBytes_focus8 base bs3 hdrOff (by rw [hBs3Len]; dsimp only [hdrOff]; omega)]
      wp_step; wp_step; wp_step; wp_step
      conv => arg 4; arg 1; rw [← pointsToBytes_focus8 base bs3 hdrOff (by rw [hBs3Len]; dsimp only [hdrOff]; omega)]
      have hResStride : g.stride - (hdrOff + 3 + newSz) = res := by
        dsimp only [hdrOff, res]; omega
      have hPost5 := setSize_case5up bs0 hdrOff g.stride newSz
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
        (BitVec.ofNat 32 res) (by rw [hResStride]; exact hRes5) (by rw [hResStride]) (by omega)
      refine (fun {sFin P post} (h : ∀ s', s' = sFin →
          SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s' P post oom) => h sFin rfl) ?_
      intro sFin hsFin
      have hpcF : sFin.pc = b + 0x2fc#64 := by subst hsFin; simp
      have hrunF : sFin.status = .Running := by subst hsFin; simp [hrun]
      have hPermF : sFin.mem.perm = s0.mem.perm := by
        subst hsFin; exact hm3Perm.trans (hm2Perm.trans (hm1Perm.trans hPerm))
      have hbrkF : sFin.brk = s0.brk := by subst hsFin; simpa using hbrk
      have hprocF : MallocngProcPreserved s0 sFin := by
        subst hsFin
        exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
               by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by subst hsFin; simp [hsp]
      have halF : sFin.spAligned = true := halOf _ (by subst hsFin; simp)
      have hx19F : sFin.readReg64 .x19 = p := by subst hsFin; simp [hx19]
      have hw4F : (sFin.readReg32 .x4).truncate 8 =
          BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx) := by
        subst hsFin
        try simp only [wp_norm, arm64_norm]
        try rw [hBs3Hdr]
        exact hdrByte_res5up hBs0Hdr hIdx31 hRes5
      have hcsF : ReallocUntouchedCS s0 sFin := by
        subst hsFin
        exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin
      subst hPostGoal hRestS2 hbs0
      exact realloc_s2_finish_ok hb γ tp brkStart bgt ivs0 s0 sFin st hg hIdx origBs tailBs
        hOrigLen hTailLen hSlot hNewMax hFit hScLe (bsCur := bs3)
        hpcF hrunF hPermF hbrkF hprocF htp0 hbrks0 hspF halF hsp0 hx19F hw4F hcsF
        hBs0Len hBs3Len hLo hSt4 hEn h48 hPost5

end VerifiedLibraries.Mallocng.Proofs

