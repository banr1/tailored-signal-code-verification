/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.InternalTop
public import ProofLib.SepLogic.Entry
public import ProofLib.SepLogic.WPFrozen

/-!
# Placement-Generic Proofs of Basic `hashbrown` Operations

Placement-generic correctness proofs for `hashbrown_len`, `hashbrown_is_empty`, `hashbrown_new`,
`hashbrown_drop`, and `hashbrown_clear`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

/-! ## Shared representation helpers -/

private theorem withCodeInv_subroutine_ok_of_plain {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (A : HbAlloc)
    (hok : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withCodeInv A spec) := by
  refine subroutine_ok_mono_entails hok (fun x s0 => ?_) (fun x s0 sf => Entails.refl _)
  unfold withCodeInv
  exact Entails.pure_left fun _ => Entails.refl _

private theorem map64_length_lt_pow64 {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots m) :
    m.length < 2 ^ 64 := by
  have hcb := hinv.validMask.capacity_bounds
  have hcons := hinv.conservation
  have hbm := bm.isLt
  omega

private theorem items_beq_zero_eq_isEmpty {m : Map64} (hlt : m.length < 2 ^ 64) :
    (BitVec.ofNat 64 m.length == 0#64) = m.isEmpty := by
  cases m with
  | nil => rfl
  | cons kv rest =>
    simp only [List.length_cons, List.isEmpty_cons, Bool.beq_eq_decide_eq]
    rw [decide_eq_false_iff_not]
    intro hz
    have h0 := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ofNat] at h0
    simp only [List.length_cons] at hlt
    omega

private theorem cset_items_zero_eq_isEmpty {m : Map64} (hlt : m.length < 2 ^ 64) :
    (if (BitVec.ofNat 64 m.length != 0#64) = true then 0#64 else (1#64 : BitVec 64)) =
      (if m.isEmpty = true then 1#64 else 0#64) := by
  have hbeq := items_beq_zero_eq_isEmpty hlt
  have hbne : (BitVec.ofNat 64 m.length != 0#64) = !m.isEmpty := by
    rw [bne, hbeq]
  rw [hbne]
  cases m.isEmpty <;> rfl

private theorem u64MapRep_focus_items (pl : Obj.Placement) (A : HbAlloc)
    (mapPtr : BitVec 64) (m : Map64) (bm : BitVec 64) (u : Nat) :
    U64MapRep pl A mapPtr m bm u ⊢
      ⌜m.length < 2 ^ 64⌝ ∗
      ∃∗ F : SepProp,
        ⌜((mapPtr + 24#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ F ⊢ U64MapRep pl A mapPtr m bm u⌝ ∗
        (((mapPtr + 24#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ F) := by
  unfold U64MapRep
  apply Entails.pure_left; rintro ⟨hal, hnw, hwf⟩
  by_cases hbm : bm = 0#64
  · subst hbm
    simp only [↓reduceIte]
    conv => lhs; rw [sepConj_comm (hbRodata pl), sepConj_assoc]
    apply Entails.pure_left; rintro rfl
    refine Entails.pure_right (by decide : ([] : Map64).length < 2 ^ 64) ?_
    unfold U64MapStruct
    refine Entails.sepExists_right
      (hbRodata pl ∗ (mapPtr ↦₆₄ pl.ρ hbEmptyCtrlSym) ∗
        ((mapPtr + 8#64) ↦₆₄ 0#64) ∗ ((mapPtr + 16#64) ↦₆₄ 0#64)) ?_
    refine Entails.pure_right ?_ (Entails.of_eq (by dsimp; ac_rfl))
    refine Entails.pure_right ⟨hal, hnw, hwf⟩ ?_
    have hcomm :
        ((mapPtr + 24#64) ↦₆₄ (0#64 : BitVec 64)) ∗
          (hbRodata pl ∗ (mapPtr ↦₆₄ pl.ρ hbEmptyCtrlSym) ∗
            ((mapPtr + 8#64) ↦₆₄ 0#64) ∗ ((mapPtr + 16#64) ↦₆₄ 0#64)) =
        hbRodata pl ∗
          ((mapPtr ↦₆₄ pl.ρ hbEmptyCtrlSym) ∗ ((mapPtr + 8#64) ↦₆₄ 0#64) ∗
            ((mapPtr + 16#64) ↦₆₄ 0#64) ∗ ((mapPtr + 24#64) ↦₆₄ 0#64)) := by ac_rfl
    dsimp only [List.length_nil]
    change (((mapPtr + 24#64) ↦₆₄ 0#64) ∗ _) ⊢ _
    rw [hcomm]
    refine sepConj_mono_right ?_
    exact Entails.pure_right rfl (Entails.refl _)
  · simp only [hbm, ↓reduceIte]
    conv => lhs; rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w
    conv => lhs; rw [sepConj_comm (hbRodata pl), sepConj_assoc, sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hinv, hu, ha_ne, ha_al, ha_nw, hctrl⟩
    refine Entails.pure_right (map64_length_lt_pow64 hinv) ?_
    unfold U64MapStruct
    rw [hinv.items_eq]
    refine Entails.sepExists_right
      (hbRodata pl ∗ (mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
        ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗
        A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
        slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ?_
    refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
    refine Entails.pure_right ⟨hal, hnw, hwf⟩ ?_
    have hcomm :
        ((mapPtr + 24#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
          (hbRodata pl ∗ (mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
            ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗
            A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
            slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) =
        hbRodata pl ∗
          (((mapPtr ↦₆₄ w.ctrlPtr) ∗ ((mapPtr + 8#64) ↦₆₄ bm) ∗
            ((mapPtr + 16#64) ↦₆₄ w.growthLeft) ∗
            ((mapPtr + 24#64) ↦₆₄ BitVec.ofNat 64 m.length)) ∗
           A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
           slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) := by ac_rfl
    rw [hcomm]
    refine sepConj_mono_right ?_
    refine Entails.sepExists_right w ?_
    rw [← hinv.items_eq]
    exact Entails.pure_right ⟨hinv, hu, ha_ne, ha_al, ha_nw, hctrl⟩ (Entails.of_eq (by ac_rfl))

/-! ## `hashbrown_len` -/

theorem hashbrown_len_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg7 P).rebase P.pl7.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_len") (hashbrownLenSpec P.pl A) := by
  dsimp only
  wp_entry
  clear hpre
  refine SepWP.weaken_pre (u64MapRep_focus_items P.pl A _ _ _ _) ?_
  wp_focus_pure; intro _hlt
  apply SepWP.exists_elim; intro F
  wp_focus_pure; intro hrestore
  wp_steps
  refine SepWP.weaken_pre hrestore ?_
  have hperm : ∀ addr,
      ((s0.writeReg64 (Reg.gpr 0#5) (BitVec.ofNat 64 a.length)).setPC
        (s0.readReg64 (Reg.gpr 30#5))).mem.perm addr = s0.mem.perm addr :=
    fun _ => rfl
  wp_done

theorem hashbrown_len_codeInv_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg7 P).rebase P.pl7.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_len")
      (withCodeInv A (hashbrownLenSpec P.pl A)) :=
  withCodeInv_subroutine_ok_of_plain A (hashbrown_len_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_len_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_len" (fun mpl => hashbrownLenSpec (mplAsPl mpl) A) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_len" 7 (off := 0) (fun P X' => hbProg7_rebase P X')
    (fun mpl => hashbrownLenSpec (mplAsPl mpl) A) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_len_ok P A X)

/-! ## `hashbrown_is_empty` -/

theorem hashbrown_is_empty_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg6 P).rebase P.pl6.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_is_empty") (hashbrownIsEmptySpec P.pl A) := by
  dsimp only
  wp_entry
  clear hpre
  refine SepWP.weaken_pre (u64MapRep_focus_items P.pl A _ _ _ _) ?_
  wp_focus_pure; intro hlt
  apply SepWP.exists_elim; intro F
  wp_focus_pure; intro hrestore
  wp_steps
  refine SepWP.weaken_pre hrestore ?_
  have hcset := cset_items_zero_eq_isEmpty hlt
  have hperm : ∀ addr,
      ((((s0.writeReg64 (Reg.gpr 8#5) (BitVec.ofNat 64 a.length)).writeReg64 (Reg.gpr 0#5)
        (if a.isEmpty = true then 1#64 else 0#64)).setPState
          (subsPState64 (BitVec.ofNat 64 a.length) 0#64)).setPC
            (s0.readReg64 (Reg.gpr 30#5))).mem.perm addr = s0.mem.perm addr :=
    fun _ => rfl
  wp_done

theorem hashbrown_is_empty_codeInv_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg6 P).rebase P.pl6.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_is_empty")
      (withCodeInv A (hashbrownIsEmptySpec P.pl A)) :=
  withCodeInv_subroutine_ok_of_plain A (hashbrown_is_empty_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_is_empty_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_is_empty"
      (fun mpl => hashbrownIsEmptySpec (mplAsPl mpl) A) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_is_empty" 6 (off := 0) (fun P X' => hbProg6_rebase P X')
    (fun mpl => hashbrownIsEmptySpec (mplAsPl mpl) A) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_is_empty_ok P A X)

/-! ## `hashbrown_new` -/

private theorem step_stpSimd128_perm {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P1 P2 P3 P4 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 ea3 ea4 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 v3 v4 : BitVec 64}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2) (hea3 : ea + 16#64 = ea3) (hea4 : ea3 + 8#64 = ea4)
    (hv1 : (s.readVReg128 vt1).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt1).extractLsb' 64 64 = v2)
    (hv3 : (s.readVReg128 vt2).extractLsb' 0 64 = v3)
    (hv4 : (s.readVReg128 vt2).extractLsb' 64 64 = v4)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hstore3 : SepStore64 ea3 v3 P2 P3)
    (hstore4 : SepStore64 ea4 v4 P3 P4)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') P4 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  let m3 := m2.write64 ea3 v3
  let m4 := m3.write64 ea4 v4
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hm3 : m3 ⊨ P3 ∗ R := hstore3.store hm2
  have hm4 : m4 ⊨ P4 ∗ R := hstore4.store hm3
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  have hcan3 : m2.canWrite ea3 8 = true := hstore3.writable hm2
  have hcan4 : m3.canWrite ea4 8 = true := hstore4.writable hm3
  have hp1 : m1.perm = s.mem.perm := Memory.perm_write64 _ _ _
  have hp2 : m2.perm = m1.perm := Memory.perm_write64 _ _ _
  have hp3 : m3.perm = m2.perm := Memory.perm_write64 _ _ _
  have hp4 : m4.perm = m3.perm := Memory.perm_write64 _ _ _
  have hkf : s.mem.KeepsFrozen m4 :=
    (((Memory.keepsFrozen_write64 hcan1 v1).trans (Memory.keepsFrozen_write64 hcan2 v2)).trans
      (Memory.keepsFrozen_write64 hcan3 v3)).trans (Memory.keepsFrozen_write64 hcan4 v4)
  rw [Memory.canWrite_congr hp1] at hcan2
  rw [Memory.canWrite_congr hp2, Memory.canWrite_congr hp1] at hcan3
  rw [Memory.canWrite_congr hp3, Memory.canWrite_congr hp2, Memory.canWrite_congr hp1] at hcan4
  have hcan_lo : s.mem.canWrite ea 16 = true :=
    Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_hi : s.mem.canWrite ea3 16 = true :=
    Memory.canWrite_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stpSimd .Q128 vt1 vt2 addr) s =
      ((applyWriteback s wb).setPC (pc + 4#64)).setMem m4 := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hea3, hea4, hv1, hv2, hv3, hv4, hcan_lo, hcan_hi,
      SimdMemSize.bytes, hpc, m1, m2, m3, m4]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m4 (hp4.trans (hp3.trans (hp2.trans hp1))) hkf) hm4

private theorem hbEmptyMap_words_eq (pl : Obj.Placement) :
    pointsToBytesRO (pl.ρ hbEmptyMapSym)
      (Obj.bytesLE 8 (pl.ρ hbEmptyCtrlSym) ++ List.replicate 24 0#8) =
    ((pl.ρ hbEmptyMapSym) ↦₆₄ᵣ (pl.ρ hbEmptyCtrlSym)) ∗
    ((pl.ρ hbEmptyMapSym + 8#64) ↦₆₄ᵣ 0#64) ∗
    ((pl.ρ hbEmptyMapSym + 16#64) ↦₆₄ᵣ 0#64) ∗
    ((pl.ρ hbEmptyMapSym + 24#64) ↦₆₄ᵣ 0#64) := by
  have hrep : List.replicate 24 (0#8 : BitVec 8) =
      unpack64 0#64 ++ (unpack64 0#64 ++ unpack64 0#64) := rfl
  rw [bytesLE_eight_eq_unpack64, hrep,
      pointsToBytesRO_append, unpack64_length,
      pointsToBytesRO_append, unpack64_length,
      pointsToBytesRO_append, unpack64_length]
  have h16 : pl.ρ hbEmptyMapSym + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 =
      pl.ρ hbEmptyMapSym + 16#64 := by bv_lin
  have h24 : pl.ρ hbEmptyMapSym + 16#64 + BitVec.ofNat 64 8 =
      pl.ρ hbEmptyMapSym + 24#64 := by bv_lin
  rw [h16, h24]
  simp only [← pointsTo64RO_eq_pointsToBytesRO]

private theorem memRegion32_entails_u64MapStruct (mapPtr : BitVec 64) :
    memRegion mapPtr 32 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (mapPtr ↦₆₄ w0) ∗ ((mapPtr + 8#64) ↦₆₄ w1) ∗
        ((mapPtr + 16#64) ↦₆₄ w2) ∗ ((mapPtr + 24#64) ↦₆₄ w3) := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) by rfl,
      memRegion_split mapPtr 8 24 (by decide),
      memRegion_split (mapPtr + 8#64) 8 16 (by decide),
      memRegion_split (mapPtr + 8#64 + 8#64) 8 8 (by decide)]
  have h16 : mapPtr + 8#64 + 8#64 = mapPtr + 16#64 := by bv_lin
  have h24 : mapPtr + 16#64 + 8#64 = mapPtr + 24#64 := by bv_lin
  rw [h16, h24, memRegion_eight mapPtr, memRegion_eight (mapPtr + 8#64),
      memRegion_eight (mapPtr + 16#64), memRegion_eight (mapPtr + 24#64)]
  conv => lhs; rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  conv => lhs; rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  conv => lhs; rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  conv => lhs; rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  exact Entails.sepExists_right w0
    (Entails.sepExists_right w1
      (Entails.sepExists_right w2
        (Entails.sepExists_right w3 (Entails.of_eq (by ac_rfl)))))

theorem hashbrown_new_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg8 P).rebase P.pl8.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_new") (hashbrownNewSpec P.pl A) := by
  dsimp only
  wp_entry
  clear hpre
  refine SepWP.weaken_pre
    (sepConj_mono_right (memRegion32_entails_u64MapStruct _)) ?_
  rw [sepExists_sepConj_right]; apply SepWP.exists_elim; intro w0
  rw [sepExists_sepConj_right]; apply SepWP.exists_elim; intro w1
  rw [sepExists_sepConj_right]; apply SepWP.exists_elim; intro w2
  rw [sepExists_sepConj_right]; apply SepWP.exists_elim; intro w3
  wp_conv_pre => rw [hbRodata, hbEmptyMap_words_eq]
  apply hbProg8_pairStep_0x0 P P.pl8.base X rfl (by simpa using hpc) hrun
  wp_step
  have hv1 : ((0#64 : BitVec 64) ++ P.pl.ρ hbEmptyCtrlSym).extractLsb' 0 64 =
      P.pl.ρ hbEmptyCtrlSym := by bv_bits
  have hv2 : ((0#64 : BitVec 64) ++ P.pl.ρ hbEmptyCtrlSym).extractLsb' 64 64 = 0#64 := by bv_bits
  refine step_stpSimd128_perm (pc := P.pl8.base + 12#64)
    (ea := a) (ea2 := a + 8#64) (ea3 := a + 16#64) (ea4 := a + 24#64)
    (wb := none) (v1 := P.pl.ρ hbEmptyCtrlSym) (v2 := 0#64) (v3 := 0#64) (v4 := 0#64)
    rfl (by simp [hrun]) (hbProg8_rebase_fetch_0xc P P.pl8.base X)
    rfl (by simp [evalAddrMode, h_1]) rfl rfl (by bv_lin)
    (by simp [hv1]) (by simp [hv2]) (by simp) (by simp)
    (by wp_sep_access) (by wp_sep_access) (by wp_sep_access) (by wp_sep_access) ?_
  intro m' hperm' hkf
  simp only [State.mem_setPC, State.mem_writeVReg128, State.mem_writeReg64] at hperm' hkf
  dsimp only [applyWriteback]
  rw [show P.pl8.base + 12#64 + 4#64 = P.pl8.base + 16#64 by bv_lin]
  wp_steps
  wp_conv_pre =>
    rw [← sepConj_assoc, ← hbEmptyMap_words_eq, sepConj_assoc]
    change hbRodata P.pl ∗ U64MapStruct a (P.pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64
  refine SepWP.weaken_pre (U64MapRep_init P.pl A a h_2 (by omega)) ?_
  apply SepWP.done (by simp) (by simp [hrun])
  refine ⟨fun hm => Satisfies.mono
    (sepConj_mono_left (Entails.pure_right ?_ (Entails.of_eq rfl))) hm,
    by simp, by simp (disch := decide)⟩
  exact ⟨by simp [h_1], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, congrFun hperm'⟩, hkf⟩

theorem hashbrown_new_codeInv_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    let prog := (hbProg8 P).rebase P.pl8.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_new")
      (withCodeInv A (hashbrownNewSpec P.pl A)) :=
  withCodeInv_subroutine_ok_of_plain A (hashbrown_new_ok P A X)

set_option maxRecDepth 200000 in
theorem hashbrown_new_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_new" (fun mpl => hashbrownNewSpec (mplAsPl mpl) A) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_new" 8 (off := 0) (fun P X' => hbProg8_rebase P X')
    (fun mpl => hashbrownNewSpec (mplAsPl mpl) A) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_new_ok P A X)

/-! ## `hashbrown_drop` -/

private theorem drop_ptr_size_eq {bm allocPtr ctrlPtr : BitVec 64}
    (hv : ValidBucketMask bm)
    (hctrl : ctrlPtr = allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) :
    ctrlPtr - (bm <<< 4) - 16#64 = allocPtr ∧
    (bm <<< 4) + bm + 25#64 = BitVec.ofNat 64 (17 * (bm.toNat + 1) + 8) ∧
    (BitVec.ofNat 64 (17 * (bm.toNat + 1) + 8)).toNat = 17 * (bm.toNat + 1) + 8 := by
  obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hv
  have hbkt : bm.toNat + 1 = 2 ^ exp := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hle58 : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi
  have hpow58 : 17 * 2 ^ 58 + 8 < 2 ^ 64 := by decide
  have hlsl : bm <<< 4 = BitVec.ofNat 64 (16 * bm.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have h16 : BitVec.ofNat 64 (16 * (bm.toNat + 1)) = (bm <<< 4) + 16#64 := by
    rw [hlsl, show 16 * (bm.toNat + 1) = 16 * bm.toNat + 16 by omega, BitVec.ofNat_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [hctrl, h16]
    bv_lin
  · apply BitVec.eq_of_toNat_eq
    simp only [hlsl, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem drop_table_collapse {mapPtr bm : BitVec 64} {w : HbHeapMapWitness} {m : Map64}
    (hinv : SwissTableInv bm w.growthLeft w.items w.ctrl w.slots m)
    (hnw : w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) :
    U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
      slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ⊢
      memRegion mapPtr 32 ∗ memRegion w.allocPtr (17 * (bm.toNat + 1) + 8) := by
  refine sepConj_mono (U64MapStruct_entails_memRegion ..) ?_
  have hsl : w.slots.length = bm.toNat + 1 := hinv.slots_len
  have hcl : w.ctrl.length = bm.toNat + 1 + 8 := hinv.mirror.1
  have hslots : slotsDownFrom w.ctrlPtr w.slots ⊢
      memRegion w.allocPtr (16 * (bm.toNat + 1)) := by
    rw [hctrl, ← hsl]
    exact slotsDownFrom_to_memRegion w.slots w.allocPtr (by omega)
  have hctrl_reg : (w.ctrlPtr ↦ₛ w.ctrl) ⊢
      memRegion (w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) (bm.toNat + 1 + 8) := by
    rw [← hctrl, ← hcl]
    exact pointsToBytes_entails_memRegion w.ctrlPtr w.ctrl
  refine Entails.trans (sepConj_mono hslots hctrl_reg) ?_
  rw [← memRegion_split w.allocPtr (16 * (bm.toNat + 1)) (bm.toNat + 1 + 8) (by omega),
    show 16 * (bm.toNat + 1) + (bm.toNat + 1 + 8) = 17 * (bm.toNat + 1) + 8 by omega]
  exact Entails.of_eq rfl

theorem hashbrown_drop_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : HbExterns ((hbProg3 P).rebase P.pl3.base X) P.pl3 A) :
    let prog := (hbProg3 P).rebase P.pl3.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_drop")
      (withCodeInv A (hashbrownDropSpec P.pl A)) := by
  dsimp only
  wp_entry
  clear hpre
  revert a_1 a a_2 a_3 a_4 a_rest h_1 h
  intro mapPtr m bm u lc blk hci hx0
  wp_conv_pre => rw [U64MapRep]
  rw [sepConj_assoc, sepConj_assoc]
  wp_focus_pure; rintro ⟨hmap_al, hmap_nw, hwf⟩
  by_cases hbm : bm = 0#64
  · subst hbm
    wp_conv_pre => simp only [↓reduceIte]
    rw [← sepConj_assoc, sepConj_comm (hbRodata P.pl), sepConj_assoc, sepConj_assoc]
    wp_focus_pure; intro hm_nil
    wp_conv_pre => unfold U64MapStruct
    wp_steps
    wp_conv_pre =>
      change U64MapStruct mapPtr (P.pl.ρ hbEmptyCtrlSym) 0#64 0#64 0#64 ∗
        (hbRodata P.pl ∗ (A.Heap lc blk s0 ∗ stackAt s0.sp A.stackBytes))
    have hvm : HbVmPreserved s0
        (((s0.writeReg64 (Reg.gpr 8#5) 0#64).setPC (s0.readReg64 (Reg.gpr 30#5)))) :=
      ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩
    refine SepWP.weaken_pre
      (sepConj_mono (U64MapStruct_entails_memRegion ..)
        (sepConj_mono_right (sepConj_mono_left (A.heap_transport hvm)))) ?_
    apply SepWP.done (by simp) (by simp [hrun])
    refine ⟨fun hm => Satisfies.mono ?_ hm, by simp, by simp (disch := decide)⟩
    simp only [hbMapCost_zero, tableAllocBlocks, ↓reduceIte, Nat.sub_zero]
    refine sepConj_mono_left (Entails.pure_right ?_ (Entails.of_eq (by ac_rfl)))
    exact ⟨rfl, rfl, rfl, rfl, Memory.KeepsFrozen.refl _⟩
  · wp_conv_pre => simp only [hbm, ↓reduceIte]
    have hbm_beq : (bm == 0#64) = false := beq_false_of_ne hbm
    rw [← sepConj_assoc, sepConj_comm (hbRodata P.pl), sepConj_assoc]
    rw [sepExists_sepConj_left]; apply SepWP.exists_elim; intro w
    rw [sepConj_assoc]
    wp_focus_pure; rintro ⟨hinv, _hu, halloc_nz, halloc_al, halloc_nw, hctrl⟩
    wp_conv_pre => unfold U64MapStruct
    wp_steps
    obtain ⟨hptr_eq, hsz_eq, hsz_nat⟩ := drop_ptr_size_eq hinv.validMask hctrl
    have hlayout : LayoutOk (BitVec.ofNat 64 (17 * (bm.toNat + 1) + 8)) 8#64 :=
      (ValidBucketMask.tableLayoutOk hinv.validMask)
    let szBV := BitVec.ofNat 64 (17 * (bm.toNat + 1) + 8)
    refine SepWP.call_subroutine_frame hext.dealloc_ok
      (x := (w.allocPtr, szBV, 8#64, lc, blk))
      (F := memRegion mapPtr 32 ∗ hbRodata P.pl)
      (ret_pc := s0.readReg64 Reg.lr)
      (by simp; bv_lin) (by simp [hrun]) (by simpa [State.spAligned] using hsp_align) (by simp)
      ?_ (fun _ _ _ => not_satisfies_false_sepConj) (fun _ _ _ _ => not_satisfies_false_sepConj)
      ?_ (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
    · intro R' hm
      rw [← sepConj_assoc]
      refine Satisfies.mono (sepConj_mono_left ?_) hm
      dsimp only [withCodeInv, hbDeallocSpec]
      rw [hsz_nat]
      refine Entails.trans ?_
        (sepConj_mono_left (Entails.pure_right hci
          (Entails.pure_right ⟨?_, ?_, ?_, hlayout⟩ (Entails.of_eq rfl))))
      · have hcol := drop_table_collapse (mapPtr := mapPtr) hinv halloc_nw hctrl
        have hrearr :
            ((mapPtr ↦₆₄ w.ctrlPtr ∗ (mapPtr + 8#64) ↦₆₄ bm ∗
                (mapPtr + 16#64) ↦₆₄ w.growthLeft ∗ (mapPtr + 24#64) ↦₆₄ w.items) ∗
              A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
              slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl) ∗
              hbRodata P.pl ∗ A.Heap lc blk s0 ∗ stackAt s0.sp A.stackBytes) =
            (U64MapStruct mapPtr w.ctrlPtr bm w.growthLeft w.items ∗
              slotsDownFrom w.ctrlPtr w.slots ∗ (w.ctrlPtr ↦ₛ w.ctrl)) ∗
            A.Heap lc blk s0 ∗
            (A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
             stackAt s0.sp A.stackBytes ∗ hbRodata P.pl) := by
          dsimp only [U64MapStruct]
          ac_rfl
        rw [hrearr]
        conv => rhs; arg 1; arg 2; arg 2; arg 2; arg 1; simp
        have hrhs : ∀ H B M S M32 R0 : SepProp,
            (H ∗ B ∗ M ∗ S) ∗ (M32 ∗ R0) = (M32 ∗ M) ∗ H ∗ (B ∗ S ∗ R0) := by
          intros; ac_rfl
        rw [hrhs]
        exact sepConj_mono hcol
          (sepConj_mono_left (A.heap_transport ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩))
      · rw [← hctrl]; simp [hptr_eq]
      · simp [szBV, hsz_eq]
      · simp
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      apply SepWP.done hpc_sf hrun_sf
      refine ⟨fun hm => ?_, by simpa using hsp_sf, by simpa (disch := decide) using hcs_sf⟩
      dsimp only [withCodeInv, hbDeallocSpec] at hm
      simp only [hbMapCost, tableAllocBlocks, tableAllocBytes, hbm, ↓reduceIte, szBV, hsz_nat] at hm ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm

set_option maxRecDepth 200000 in
theorem hashbrown_drop_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X A) :
    hashbrownLib.subroutineOk "hashbrown_drop"
      (fun mpl => withCodeInv A (hashbrownDropSpec (mplAsPl mpl) A)) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_drop" 3 (off := 0) (fun P X' => hbProg3_rebase P X')
    (fun mpl => withCodeInv A (hashbrownDropSpec (mplAsPl mpl) A)) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_drop_ok P A X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg3_rebase P X) (hbPl3_eq P)))

/-! ## `hashbrown_clear` -/

private theorem step_stp64_perm {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc' : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc) (hpc' : pc + 4#64 = pc')
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1)
    (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((applyWriteback s wb).setPC pc').setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W64 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  have hp1 : m1.perm = s.mem.perm := Memory.perm_write64 _ _ _
  have hp2 : m2.perm = m1.perm := Memory.perm_write64 _ _ _
  rw [Memory.canWrite_congr hp1] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s =
      ((applyWriteback s wb).setPC pc').setMem m2 := by
    rw [← hpc']
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized,
      applyWriteback, State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m2 (hp2.trans hp1)) hm2

private theorem items_zero_imp_nil {bm growthLeft items : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)} {m : Map64}
    (hinv : SwissTableInv bm growthLeft items ctrl slots m) (h0 : items = 0#64) :
    m = [] := by
  have hlt : m.length < 2 ^ 64 := map64_length_lt_pow64 hinv
  have heq : BitVec.ofNat 64 m.length = 0#64 := hinv.items_eq.symm.trans h0
  have hlen0 : m.length = 0 := by
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
    exact this
  exact List.eq_nil_of_length_eq_zero hlen0

private theorem clear_size_eq {bm : BitVec 64} (hv : ValidBucketMask bm) :
    bm + 9#64 = BitVec.ofNat 64 (bm.toNat + 1 + 8) ∧
    bm.toNat + 1 + 8 < 2 ^ 64 := by
  obtain ⟨exp, hlo, hhi, hbm_eq⟩ := hv
  have hbkt : bm.toNat + 1 = 2 ^ exp := ValidBucketMask.buckets_eq hlo hhi hbm_eq
  have hle58 : 2 ^ exp ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hhi
  have hpow58 : 2 ^ 58 + 8 < 2 ^ 64 := by decide
  refine ⟨?_, by omega⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]

private theorem shift3_sub_self (q : BitVec 64) : (q <<< 3) - q = q * 7#64 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change q * 8#64 - q = q * 7#64
  bv_lin

private theorem clear_csel_eq_capacityBV (bm : BitVec 64) :
    (if bm.ult 8#64 = true then bm else (bm + 1#64) >>> 3 <<< 3 - (bm + 1#64) >>> 3) =
      bucketMaskToCapacityBV bm := by
  rw [shift3_sub_self]
  unfold bucketMaskToCapacityBV
  by_cases h : bm < 8#64
  · have hu : bm.ult 8#64 = true := by simpa [BitVec.ult, BitVec.lt_def] using h
    simp [h, hu]
  · have hu : bm.ult 8#64 = false := by
      cases hlt : bm.ult 8#64
      · rfl
      · exact False.elim (h (by simpa [BitVec.ult, BitVec.lt_def] using hlt))
    simp [h, hu]

theorem hashbrown_clear_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : HbExterns ((hbProg1 P).rebase P.pl1.base X) P.pl1 A) :
    let prog := (hbProg1 P).rebase P.pl1.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_clear")
      (withCodeInv A (hashbrownClearSpec P.pl A)) := by
  dsimp only
  wp_entry
  clear hpre
  revert a_1 a a_2 a_rest h_1 h
  intro mapPtr m bm u hci hx0
  refine SepWP.mono_frozen (Φ := fun mem => s0.mem.KeepsFrozen mem)
    (post := fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ (⌜StdStatePreserved s0 sf⌝ ∗ U64MapRep P.pl A mapPtr [] bm u ∗ stackAt s0.sp 32) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    (fun _ _ h1 h2 => h1.trans h2) (Memory.KeepsFrozen.refl s0.mem) ?_ ?_
  · wp_conv_pre => rw [U64MapRep]
    rw [sepConj_assoc]
    wp_focus_pure; rintro ⟨hmap_al, hmap_nw, hwf⟩
    by_cases hbm : bm = 0#64
    · subst hbm
      wp_conv_pre => simp only [↓reduceIte]
      rw [← sepConj_assoc, sepConj_comm (hbRodata P.pl), sepConj_assoc]
      wp_focus_pure; intro hm_nil
      wp_conv_pre => unfold U64MapStruct
      wp_steps
      have hent_rep :
          ((mapPtr ↦₆₄ P.pl.ρ hbEmptyCtrlSym ∗ (mapPtr + 8#64) ↦₆₄ 0#64 ∗
            (mapPtr + 16#64) ↦₆₄ 0#64 ∗ (mapPtr + 24#64) ↦₆₄ 0#64) ∗
           (hbRodata P.pl ∗ stackAt s0.sp 32)) ⊢
          U64MapRep P.pl A mapPtr [] 0#64 u ∗ stackAt s0.sp 32 := by
        rw [U64MapRep]
        simp only [↓reduceIte]
        refine Entails.trans ?_
          (sepConj_mono_left
            (Entails.pure_right ⟨hmap_al, hmap_nw, Map64Wf.nil⟩
              (sepConj_mono_right (Entails.pure_right trivial (Entails.of_eq rfl)))))
        dsimp only [U64MapStruct]
        exact Entails.of_eq (by ac_rfl)
      refine SepWP.weaken_pre hent_rep ?_
      apply SepWP.done (by simp) (by simp [hrun])
      refine ⟨fun hm => Satisfies.mono
        (sepConj_mono_left (Entails.pure_right ?_ (Entails.of_eq rfl))) hm,
        by simp, by simp (disch := decide)⟩
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · wp_conv_pre => simp only [hbm, ↓reduceIte]
      have hbm_beq : (bm == 0#64) = false := beq_false_of_ne hbm
      rw [← sepConj_assoc, sepConj_comm (hbRodata P.pl), sepConj_assoc]
      rw [sepExists_sepConj_left]; apply SepWP.exists_elim; intro w
      rw [sepConj_assoc]
      wp_focus_pure; rintro ⟨hinv, hu, halloc_nz, halloc_al, halloc_nw, hctrl⟩
      wp_conv_pre => unfold U64MapStruct
      by_cases hitems : w.items = 0#64
      · have hm_nil : m = [] := items_zero_imp_nil hinv hitems
        subst hm_nil
        rw [hitems]
        wp_steps
        refine SepWP.weaken_pre (P' := U64MapRep P.pl A mapPtr [] bm u ∗ stackAt s0.sp 32) ?_ ?_
        · rw [U64MapRep]
          simp only [hbm, ↓reduceIte]
          refine Entails.trans ?_
            (sepConj_mono_left
              (Entails.pure_right ⟨hmap_al, hmap_nw, Map64Wf.nil⟩
                (sepConj_mono_right
                  (Entails.sepExists_right w
                    (Entails.pure_right ⟨hinv, hu, halloc_nz, halloc_al, halloc_nw, hctrl⟩
                      (Entails.of_eq rfl))))))
          dsimp only [U64MapStruct]
          rw [hitems]
          exact Entails.of_eq (by ac_rfl)
        · apply SepWP.done (by simp) (by simp [hrun])
          refine ⟨fun hm => Satisfies.mono
            (sepConj_mono_left (Entails.pure_right ?_ (Entails.of_eq rfl))) hm,
            by simp, by simp (disch := decide)⟩
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
      · have hitems_beq : (w.items == 0#64) = false := beq_false_of_ne hitems
        have hsp_sub_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
          spAligned_sub s0.sp 32#64 hsp_align
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (memRegion32_entails_u64MapStruct (s0.sp - 32#64))))))) ?_
        wp_conv_pre => simp only [sepExists_sepConj_right]
        apply SepWP.exists_elim; intro sw0
        wp_conv_pre => simp only [sepExists_sepConj_right]
        apply SepWP.exists_elim; intro sw1
        wp_conv_pre => simp only [sepExists_sepConj_right]
        apply SepWP.exists_elim; intro sw2
        wp_conv_pre => simp only [sepExists_sepConj_right]
        apply SepWP.exists_elim; intro sw3
        refine SepWP.seq_frozen (mid := P.pl1.ρ hbMemsetSym) (Φ := fun mem => s0.mem.KeepsFrozen mem)
          (fun _ _ h1 h2 => h1.trans h2) (Memory.KeepsFrozen.refl s0.mem) ?_
        wp_step
        wp_step
        refine step_stp64_perm (pc := P.pl1.base + 8#64) (pc' := P.pl1.base + 12#64)
          (ea := s0.sp - 32#64) (ea2 := s0.sp - 32#64 + 8#64)
          (wb := some (.sp, s0.sp - 32#64))
          (v1 := s0.readReg64 (.gpr 29#5)) (v2 := s0.readReg64 (.gpr 30#5))
          rfl (by bv_lin) (by simp [hrun]) (hbProg1_rebase_fetch_0x8 P P.pl1.base X)
          (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_align])
          (by simp [evalAddrMode]; bv_lin) rfl (by simp) (by simp)
          (by wp_sep_access) (by wp_sep_access) ?_
        intro m1 hp1
        simp only [State.mem_setPC, State.mem_writeReg64] at hp1
        dsimp only [applyWriteback]
        refine step_stp64_perm (pc := P.pl1.base + 12#64) (pc' := P.pl1.base + 16#64)
          (ea := s0.sp - 32#64 + 16#64) (ea2 := s0.sp - 32#64 + 24#64)
          (wb := none)
          (v1 := s0.readReg64 (.gpr 20#5)) (v2 := s0.readReg64 (.gpr 19#5))
          rfl (by bv_lin) (by simp [hrun]) (hbProg1_rebase_fetch_0xc P P.pl1.base X)
          (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_align])
          (by simp [evalAddrMode]) (by bv_lin) (by simp) (by simp)
          (by wp_sep_access) (by wp_sep_access) ?_
        intro m2 hp2
        simp only [State.mem_setMem] at hp2
        dsimp only [applyWriteback]
        wp_steps
        apply SepWP.done (by simp; bv_lin) (by simp [hrun])
        intro hkf_sm
        have hci_sm : A.CodeInv m2 := A.codeInv_keepsFrozen (by simpa using hkf_sm) hci
        obtain ⟨hbm9_eq, hclen_lt⟩ := clear_size_eq hinv.validMask
        let clen := bm.toNat + 1 + 8
        refine SepWP.call_subroutine_frame hext.memset_ok
          (x := (w.ctrlPtr, tagEmpty, clen))
          (F := ((mapPtr ↦₆₄ w.ctrlPtr ∗ (mapPtr + 8#64) ↦₆₄ bm ∗
                  (mapPtr + 16#64) ↦₆₄ w.growthLeft ∗ (mapPtr + 24#64) ↦₆₄ w.items) ∗
                 A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
                 slotsDownFrom w.ctrlPtr w.slots) ∗
                (hbRodata P.pl ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5) ∗
                  (s0.sp - 32#64 + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5) ∗
                  (s0.sp - 32#64 + 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5) ∗
                  (s0.sp - 32#64 + 24#64) ↦₆₄ s0.readReg64 (.gpr 19#5))))
          (ret_pc := P.pl1.base + 48#64)
          (by simp; bv_lin) (by simp [hrun])
          (by simp [State.spAligned, hsp_align]) (by simp)
          ?_ (fun _ _ _ => not_satisfies_false_sepConj) (fun _ _ _ _ => not_satisfies_false_sepConj)
          ?_ (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
        · intro R' hm
          rw [← sepConj_assoc]
          refine Satisfies.mono (sepConj_mono_left ?_) hm
          dsimp only [withCodeInv, stdMemsetSpec]
          have hctrl_reg : (w.ctrlPtr ↦ₛ w.ctrl) ⊢ memRegion w.ctrlPtr clen := by
            have hcl : w.ctrl.length = clen := hinv.mirror.1
            rw [← hcl]
            exact pointsToBytes_entails_memRegion w.ctrlPtr w.ctrl
          refine Entails.trans ?_
            (sepConj_mono_left (Entails.pure_right (by simpa using hci_sm)
              (Entails.pure_right
                ⟨by simp [hctrl], by simp [State.readReg32, Reg.x1, tagEmpty],
                 by simp [clen, hbm9_eq], hclen_lt⟩
                (Entails.of_eq rfl))))
          refine Entails.trans ?_ (sepConj_mono_left hctrl_reg)
          exact Entails.of_eq (by ac_rfl)
        · intro sf_mem hpc_sf hrun_sf hsp_sf hcs_sf
          dsimp only [withCodeInv, stdMemsetSpec]
          rw [sepConj_assoc]
          wp_focus_pure; rintro ⟨_, hstd_sf⟩
          have hx19 : sf_mem.readReg64 (.gpr 19#5) = mapPtr := by simpa using hcs_sf.1
          have hx20 : sf_mem.readReg64 (.gpr 20#5) = bm := by simpa using hcs_sf.2.1
          have hsp_mem : sf_mem.sp = s0.sp - 32#64 := by simpa using hsp_sf
          wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
          refine step_stp64_perm (pc := P.pl1.base + 80#64) (pc' := P.pl1.base + 84#64)
            (ea := mapPtr + 16#64) (ea2 := mapPtr + 24#64)
            (wb := none)
            (v1 := bucketMaskToCapacityBV bm) (v2 := 0#64)
            (by simp <;> bv_lin) (by bv_lin) (by simp [hrun_sf])
            (hbProg1_rebase_fetch_0x50 P P.pl1.base X)
            (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
            (by simp [evalAddrMode, hx19]) (by bv_lin)
            (by simp [clear_csel_eq_capacityBV]) (by simp)
            (by wp_sep_access) (by wp_sep_access) ?_
          intro m3 hp3
          simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64] at hp3
          dsimp only [applyWriteback]
          have hsp_mem_align : (sf_mem.sp &&& 15#64 == 0#64) = true := hsp_mem ▸ hsp_sub_align
          wp_steps
          let w' : HbHeapMapWitness :=
            { w with
              growthLeft := bucketMaskToCapacityBV bm
              items := 0#64
              ctrl := List.replicate clen tagEmpty }
          have hinv' : SwissTableInv bm w'.growthLeft w'.items w'.ctrl w'.slots [] :=
            SwissTableInv_init_of_mask hinv.validMask hinv.slots_len
          refine SepWP.weaken_pre (P' := U64MapRep P.pl A mapPtr [] bm u ∗ stackAt s0.sp 32) ?_ ?_
          · have hstk :
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5) ∗
                 (s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5) ∗
                 (s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ⊢
                stackAt s0.sp 32 := by
              have ha1 : s0.sp - 24#64 = s0.sp - 32#64 + 8#64 := by bv_lin
              have ha2 : s0.sp - 16#64 = s0.sp - 32#64 + 16#64 := by bv_lin
              have ha3 : s0.sp - 8#64 = s0.sp - 32#64 + 24#64 := by bv_lin
              rw [ha1, ha2, ha3]
              exact U64MapStruct_entails_memRegion (s0.sp - 32#64) _ _ _ _
            have hmap' :
                hbRodata P.pl ∗
                ((mapPtr ↦₆₄ w.ctrlPtr ∗ (mapPtr + 8#64) ↦₆₄ bm ∗
                  (mapPtr + 16#64) ↦₆₄ bucketMaskToCapacityBV bm ∗ (mapPtr + 24#64) ↦₆₄ 0#64) ∗
                 A.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
                 slotsDownFrom w.ctrlPtr w.slots ∗
                 (w.ctrlPtr ↦ₛ List.replicate clen tagEmpty)) ⊢
                U64MapRep P.pl A mapPtr [] bm u := by
              rw [U64MapRep]
              simp only [hbm, ↓reduceIte]
              refine Entails.pure_right ⟨hmap_al, hmap_nw, Map64Wf.nil⟩
                (sepConj_mono_right
                  (Entails.sepExists_right w'
                    (Entails.pure_right ⟨hinv', by simp [w', bucketMaskToCapacity], halloc_nz, halloc_al, halloc_nw, hctrl⟩
                      (Entails.of_eq rfl))))
            refine Entails.trans ?_ (sepConj_mono hmap' hstk)
            exact Entails.of_eq (by ac_rfl)
          · apply SepWP.done (by simp) (by simp [hrun_sf])
            refine ⟨fun hm => Satisfies.mono
              (sepConj_mono_left (Entails.pure_right ?_ (Entails.of_eq rfl))) hm,
              by simp, ?_⟩
            · refine ⟨by simpa using hstd_sf.1,
                      by simpa using hstd_sf.2.1,
                      by simpa using hstd_sf.2.2.1,
                      by simpa using hstd_sf.2.2.2.1,
                      by simpa using hstd_sf.2.2.2.2.1,
                      by simpa using hstd_sf.2.2.2.2.2.1,
                      by simpa using hstd_sf.2.2.2.2.2.2.1,
                      fun addr => ?_⟩
              simp only [State.mem_setMem]
              rw [congrFun hp3 addr, hstd_sf.2.2.2.2.2.2.2 addr]
              simp [hp2, hp1]
            · unfold CalleeSavedPreserved at hcs_sf ⊢
              rcases hcs_sf with ⟨_, _, h21, h22, h23, h24, h25, h26, h27, h28, _, hv⟩
              refine ⟨by simp, by simp,
                by simpa using h21, by simpa using h22, by simpa using h23, by simpa using h24,
                by simpa using h25, by simpa using h26, by simpa using h27, by simpa using h28,
                by simp, by simpa [calleeSavedVRegs] using hv⟩
  · intro sf Pf _ _ hkf_sf hp
    refine ⟨fun hm => ?_, hp.2⟩
    have hm' := hp.1 hm
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm' ⊢
    exact ⟨⟨hm'.1, hkf_sf⟩, hm'.2⟩

set_option maxRecDepth 200000 in
theorem hashbrown_clear_subroutineOk (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X A) :
    hashbrownLib.subroutineOk "hashbrown_clear"
      (fun mpl => withCodeInv A (hashbrownClearSpec (mplAsPl mpl) A)) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_clear" 1 (off := 0) (fun P X' => hbProg1_rebase P X')
    (fun mpl => withCodeInv A (hashbrownClearSpec (mplAsPl mpl) A)) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_clear_ok P A X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg1_rebase P X) (hbPl1_eq P)))

end CaseStudies.Hashbrown.Proofs
