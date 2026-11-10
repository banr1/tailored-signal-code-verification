/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Hit
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Miss
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.PutStr.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

private theorem entails_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem ite_false_eq {α : Sort _} (t e : α) : (if false = true then t else e) = e :=
  rfl

private theorem bv_sub_eq_add_neg64 (a b : BitVec 64) : a - b = a + (-b) :=
  BitVec.sub_eq_add_neg a b

private theorem sub48_latch (n : Nat) (hlt : (n + 1) * 48 < 2 ^ 64) :
    BitVec.ofNat 64 ((n + 1) * 48) - 48#64 = BitVec.ofNat 64 (n * 48) := by
  have h1 := ofNat_toNat_of_lt hlt
  have h2 := ofNat_toNat_of_lt (show n * 48 < 2 ^ 64 by omega)
  have h48 : (48#64 : BitVec 64).toNat = 48 := rfl
  have hle : (48#64 : BitVec 64) ≤ BitVec.ofNat 64 ((n + 1) * 48) := by
    rw [BitVec.le_def, h48, h1]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le hle, h1, h2, h48]
  omega

private theorem setOrPush_hit_middle (name bs ev : List (BitVec 8))
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (hpre : ∀ p ∈ pre, p.1 ≠ name) :
    DirGhost.setOrPush name bs (pre ++ (name, ev) :: rest) =
      pre ++ (name, bs) :: rest := by
  rw [setOrPush_append_of_forall_ne name bs pre ((name, ev) :: rest) hpre]
  simp [DirGhost.setOrPush]

private theorem w0_cbnz_zero {w : BitVec 64} (h : w.setWidth 32 = 0#32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 w) == 0#64) = true := by
  have h1 : BitVec.truncate 32 w = 0#32 := h
  rw [h1]
  rfl

private theorem w0_cbnz_nonzero {w : BitVec 64} (h : w.setWidth 32 ≠ 0#32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 w) == 0#64) = false := by
  apply beq_false_of_ne
  intro hz
  apply h
  have h2 := congrArg (BitVec.setWidth 32) hz
  have h3 : (BitVec.zeroExtend 64 (BitVec.truncate 32 w)).setWidth 32 = w.setWidth 32 := by
    bv_omega
  rw [h3] at h2
  exact h2

/-- Loop invariant and induction over `suf` starting at `+132`:
    given `x.dir.changed = pre ++ suf`, `suf ≠ []`, and `∀ p ∈ pre, p.1 ≠ x.name`,
    either finds the unique entry matching `x.name` (`step_hit`) or exhausts `suf` (`step_miss`). -/
theorem step_loop {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk))
    (x : DirPutStrGhost) (R : SepProp) (s0 : State)
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hsp_align0 : s0.spAligned = true) :
    let cal := max growStk extHookStack
    ∀ (suf pre : List (List (BitVec 8) × List (BitVec 8))) (s : State),
      suf ≠ [] →
      x.dir.changed = pre ++ suf →
      (∀ p ∈ pre, p.1 ≠ x.name) →
      ImgCallInv img s →
      s.pc = atOff ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName) 132 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = s0.sp - 80#64 →
      s.trace = s0.trace →
      PresHigh s0 s →
      s.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x20 = x.bytesV →
      s.readReg64 .x21 = namePtr →
      s.readReg64 .x22 = x.self →
      s.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
      s.readReg64 .x24 = ptr →
      s.readReg64 .x25 = ptr + BitVec.ofNat 64 (pre.length * 48) + 32#64 →
      s.readReg64 .x26 = BitVec.ofNat 64 (suf.length * 48) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) s
        ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          stackAt (s0.sp - 80#64) cal ∗
          savedSlots s0 ∗
          A.pool)
        (DirPutStrPost A img x s0 stk R)
        (DirPutStrPanic A img x s0 stk R) := by
  intro cal suf
  induction suf with
  | nil =>
    intro _ _ hsuf
    exact (hsuf rfl).elim
  | cons e rest ih =>
    intro pre s _hsuf hsplit hpre_ne hinv hpc hrun hsp_align hsp htr hhigh
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26
    have hbcmp := bcmp_inImage_ok_at_dirPutStr img ext hBcmp
    have hfn : libsignalSessionCode.fnOff dirPutStrName =
        num% (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") := dirPutStr_fnOff
    let fnBase := (tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName
    generalize hcur_raw : ptr + BitVec.ofNat 64 (pre.length * 48) = curBase at hx25
    have hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)) := ⟨hcur_raw.symm⟩
    clear hcur_raw
    have hlen_split : x.dir.changed.length = pre.length + (rest.length + 1) := by
      rw [hsplit, List.length_append, List.length_cons]
    let _ := hlen_split
    have hlatch : ∀ (sl : State),
        e.1 ≠ x.name →
        ImgCallInv img sl →
        sl.pc = atOff fnBase 120 →
        sl.status = .Running →
        sl.spAligned = true →
        sl.sp = s0.sp - 80#64 →
        sl.trace = s0.trace →
        PresHigh s0 sl →
        sl.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
        sl.readReg64 .x20 = x.bytesV →
        sl.readReg64 .x21 = namePtr →
        sl.readReg64 .x22 = x.self →
        sl.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
        sl.readReg64 .x24 = ptr →
        sl.readReg64 .x25 = curBase + 32#64 →
        sl.readReg64 .x26 = BitVec.ofNat 64 ((rest.length + 1) * 48) →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sl
          ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            nameBuf A namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            stackAt (s0.sp - 80#64) cal ∗
            savedSlots s0 ∗
            A.pool)
          (DirPutStrPost A img x s0 stk R)
          (DirPutStrPanic A img x s0 stk R) := by
      intro sl he_ne hinv_l hpcl hrunl hspal hspl htrl hhighl
        hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26
      have hpre_next : ∀ p ∈ pre ++ [e], p.1 ≠ x.name := by
        intro p hp
        rcases List.mem_append.mp hp with hp0 | hp1
        · exact hpre_ne p hp0
        · rw [List.mem_singleton.mp hp1]; exact he_ne
      cases rest with
      | nil =>
        have hr26_48 : sl.readReg64 .x26 = 48#64 := hr26
        have hmiss_all : ∀ p ∈ x.dir.changed, p.1 ≠ x.name := by
          rw [hsplit]
          exact hpre_next
        code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
          img.base (Rust.withPanics ext) hfn
          (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 120 12
        apply sepWPp_cut_rebase (mid := atOff fnBase 244) hinv_l
        dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcl
        dsimp +zetaDelta only [fnBase, atOff]
        set fnBase' := (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr dirPutStrName
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)) = prog
          reverting [Program.fetch]
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro s2 P2 hinv_s2 ⟨hs2, hP2⟩
        · subst hP2
          let _ := hr25
          let _ := hr26_48
          apply sepWPp_eq_pre
          · exact step_miss hGrow x R s0 s2 cap ptr namePtr bCap bPtr
              hstk hstk_max hlen32 hmiss_all hinv_s2
              (by rw [hs2]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunl)
              (by
                have hsp_eq : s2.sp = sl.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
                simpa only [State.spAligned, hsp_eq] using hspal)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspl)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htrl)
              ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.1,
               by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.1,
               by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.2⟩
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr19)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr20)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr21)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr22)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr23)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr24)
          · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl
      | cons e' rest' =>
        have hsub_len : rest'.length + 2 ≤ x.dir.changed.length := by
          rw [hsplit, List.length_append, List.length_cons, List.length_cons]
          omega
        have hmul_lt : ((e' :: rest').length + 1) * 48 < 2 ^ 64 := by
          let _ := hsub_len
          rw [List.length_cons]
          omega
        have hne_48 : (BitVec.ofNat 64 (((e' :: rest').length + 1) * 48) == 48#64) = false := by
          apply beq_false_of_ne
          intro heq
          have h1 := congrArg BitVec.toNat heq
          rw [ofNat_toNat_of_lt hmul_lt, List.length_cons] at h1
          have h48 : (48#64 : BitVec 64).toNat = 48 := rfl
          rw [h48] at h1
          omega
        have hx26_sub :
            BitVec.ofNat 64 (((e' :: rest').length + 1) * 48) - 48#64 =
              BitVec.ofNat 64 ((e' :: rest').length * 48) :=
          sub48_latch (e' :: rest').length hmul_lt
        have hx25_add :
            curBase + 80#64 =
              ptr + BitVec.ofNat 64 ((pre ++ [e]).length * 48) + 32#64 := by
          have hm : (pre ++ [e]).length * 48 = pre.length * 48 + 48 := by
            simp only [List.length_append, List.length_singleton]; omega
          rw [hcur'.out, hm, BitVec.ofNat_add]
          bv_omega
        code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
          img.base (Rust.withPanics ext) hfn
          (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 120 12
        apply sepWPp_cut_rebase (mid := atOff fnBase 132) hinv_l
        dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcl
        dsimp +zetaDelta only [fnBase, atOff]
        set fnBase' := (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr dirPutStrName
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)) = prog
          reverting [Program.fetch]
        examples_hide_fetches
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro s2 P2 hinv_s2 ⟨hs2, hP2⟩
        · subst hP2
          let _ := hne_48
          let _ := hx25_add
          let _ := hx26_sub
          let _ := hr25
          let _ := hr26
          apply sepWPp_eq_pre
          · exact ih (pre ++ [e]) s2 (List.cons_ne_nil _ _)
              (by rw [hsplit, List.append_assoc, List.singleton_append])
              hpre_next hinv_s2
              (by rw [hs2]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunl)
              (by
                have hsp_eq : s2.sp = sl.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
                simpa only [State.spAligned, hsp_eq] using hspal)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspl)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htrl)
              ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.1,
               by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.1,
               by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhighl.2.2⟩
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr19)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr20)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr21)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr22)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr23)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hr24)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx25_add)
              (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx26_sub)
          · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl
    have hcap_ne : ∀ (h : x.dir.changed.length ≤ cap.toNat), cap ≠ 0 := by
      intro h h0
      subst h0
      have hz : (0 : BitVec 64).toNat = 0 := rfl
      omega
    have hvbuf_open :
        vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ⊢
          ⌜x.dir.changed.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0 ∧ cap ≠ 0⌝ ∗
            (∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
              (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
              ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
              vecU8Heap A eCap ePtr e.1 ∗
              vecU8 A (curBase + 24#64) e.2 ∗
              A.live ptr (cap.toNat * 48) 8 ∗
              arrayAt (dirEntryAt A) 48 ptr pre ∗
              arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
              memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                ((cap.toNat - x.dir.changed.length) * 48)) := by
      unfold vecBuf
      refine Entails.pure_left fun ⟨hle_c, hbnd_c, hptr_c⟩ => ?_
      have hcn := hcap_ne hle_c
      simp only [hcn, ↓reduceIte]
      refine Entails.pure_right ⟨hle_c, hbnd_c, hptr_c, hcn⟩ ?_
      have happ : arrayAt (dirEntryAt A) 48 ptr x.dir.changed =
          arrayAt (dirEntryAt A) 48 ptr pre ∗
            dirEntryAt A e curBase ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest := by
        rw [hcur'.out, hsplit, arrayAt_append, arrayAt]
      rw [happ]
      unfold dirEntryAt
      have hv1 : vecU8 A curBase e.1 =
          ∃∗ eCap : BitVec 64, ∃∗ ePtr : BitVec 64,
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A eCap ePtr e.1 := by
        unfold vecU8
        simp only [vecU8At_eq_header_heap]
      rw [hv1]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_elim fun eCap => Entails.trans ?_ (Entails.sepExists_intro eCap)
      refine Entails.sepExists_elim fun ePtr => Entails.trans ?_ (Entails.sepExists_intro ePtr)
      exact entails_eq (by ac_rfl)
    apply sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvbuf_open))))
    rw [show ∀ (A1 A2 A3 P0 E1 Z : SepProp),
          A1 ∗ A2 ∗ A3 ∗ (P0 ∗ E1) ∗ Z =
            P0 ∗ E1 ∗ A1 ∗ A2 ∗ A3 ∗ Z from
          fun _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun ⟨hle_c, hbnd_c, hptr_c, hcap_c⟩ => ?_
    refine sepWPp_exists_left fun eCap => ?_
    try simp only [sepConj_assoc]
    refine sepWPp_exists_left fun ePtr => ?_
    try simp only [sepConj_assoc]
    have he_len_pull :
        vecU8Heap A eCap ePtr e.1 =
          ⌜e.1.length < 2 ^ 63⌝ ∗ vecU8Heap A eCap ePtr e.1 := by
      apply Entails.antisymm
      · unfold vecU8Heap
        refine Entails.pure_left fun ⟨h1, h2, h3⟩ => ?_
        exact Entails.pure_right (by omega) (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))
      · exact Entails.pure_left fun _ => Entails.refl _
    rw [he_len_pull]
    rw [show ∀ (C0 C1 C2 P0 H1 Z : SepProp),
          C0 ∗ C1 ∗ C2 ∗ (P0 ∗ H1) ∗ Z = P0 ∗ C0 ∗ C1 ∗ C2 ∗ H1 ∗ Z from
          fun _ _ _ _ _ _ => by ac_rfl]
    refine sepWPp_pure_left fun he_len63 => ?_
    let _ := he_len63
    have hvbuf_close :
        (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
          ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
          vecU8Heap A eCap ePtr e.1 ∗
          vecU8 A (curBase + 24#64) e.2 ∗
          A.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A) 48 ptr pre ∗
          arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
            ((cap.toNat - x.dir.changed.length) * 48) ⊢
          vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed := by
      have he1 := vecU8_of_header_heap A curBase eCap ePtr e.1
      unfold vecBuf
      simp only [hcap_c, ↓reduceIte]
      have happ : arrayAt (dirEntryAt A) 48 ptr x.dir.changed =
          arrayAt (dirEntryAt A) 48 ptr pre ∗
            (vecU8 A curBase e.1 ∗ vecU8 A (curBase + 24#64) e.2) ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest := by
        rw [hcur'.out, hsplit, arrayAt_append, arrayAt]
        unfold dirEntryAt
        ac_rfl
      rw [happ]
      refine Entails.pure_right ⟨hle_c, hbnd_c, hptr_c⟩ ?_
      rw [show (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A eCap ePtr e.1 ∗
            vecU8 A (curBase + 24#64) e.2 ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) =
          ((curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Heap A eCap ePtr e.1) ∗
          (A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            vecU8 A (curBase + 24#64) e.2 ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48)) by ac_rfl]
      exact Entails.trans (sepConj_mono_left he1) (entails_eq (by ac_rfl))
    by_cases hlen_eq : e.1.length = x.name.length
    · -- Equal lengths: compare via `bcmp`
      have hlen_beq :
          (BitVec.ofNat 64 e.1.length == BitVec.ofNat 64 x.name.length) = true := by
        rw [hlen_eq]; exact beq_self_eq_true _
      code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
        img.base (Rust.withPanics ext) hfn
        (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 132 28
      apply sepWPp_cut_rebase (mid := atOff fnBase
        (ls_rel% "<libsignal_cli::stores::Dir>::put::<&str>" "bcmp")) hinv
      dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpc
      dsimp +zetaDelta only [fnBase, atOff]
      set fnBase' := (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr dirPutStrName
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog
        reverting [Program.fetch]
      examples_hide_fetches
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
      · subst hP1
        let _ := hlen_beq
        have hsp_s1 : s1.sp = s0.sp - 80#64 := by
          rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hsp
        have htr_s1 : s1.trace = s0.trace := by
          rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact htr
        have hx19_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
          ofNat_toNat_of_lt (by omega)
        rw [vecU8Heap_expose_bytes A eCap ePtr e.1, nameBuf_expose_bytes A namePtr x.name,
          stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
        apply call_inImage_wpp hbcmp ⟨ePtr, false, e.1, namePtr, false, x.name⟩
          (ret_pc := atOff fnBase 160)
          (F := (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
            ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
            vecU8Rest A eCap ePtr e.1 ∗
            vecU8 A (curBase + 24#64) e.2 ∗
            A.live ptr (cap.toNat * 48) 8 ∗
            arrayAt (dirEntryAt A) 48 ptr pre ∗
            arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
            memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
              ((cap.toNat - x.dir.changed.length) * 48) ∗
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
            ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
            strRefAt (x.self + 0x18#64) x.dir.path ∗
            SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
            nameBufRest A namePtr x.name ∗
            (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
            ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
            vecU8Heap A bCap bPtr x.bytes ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
            memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            savedSlots s0 ∗
            A.pool)
          (hinv := hinv_s1)
          (hpc := by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
          (hrun := by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
          (hsp_align := by
            have hsp_eq : s1.sp = s.sp := by rw [hs1]; try simp only [wp_norm, arm64_norm]
            simpa only [State.spAligned, hsp_eq] using hsp_align)
          (hlr := by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
          (hspec := rfl)
          (hφ := ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21,
                  by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21,
                  by rw [hs1]; simp only [wp_norm, arm64_norm]; omega,
                  hlen_eq.symm⟩)
          (hP := by
            try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
            repeat rw [ite_false_eq]
            repeat rw [bv_sub_eq_add_neg64]
            try rw [emp_sepConj]
            try rw [sepConj_emp]
            try simp only [wp_norm, arm64_norm]
            try rw [Nat.mul_comm 48]
            try ac_rfl)
          (hpan := fun _ => panic_false_wpp)
          (hexit := fun _ _ => rfl)
          (hoom := fun _ => rfl)
        intro sm hpcm hrunm hspm hcsm hinvm
        dsimp only [cliBcmpSpec, SpqrV1.ChainProofs.bytesAt]
        try simp only [sepConj_assoc]
        refine sepWPp_pure_left fun ⟨hbcmp_iff, htr_sm0⟩ => ?_
        have hstk_back :
            memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
              stackAt s1.sp extHookStack =
              stackAt (s0.sp - 80#64) cal := by
          rw [← stackAt_split_sub s1.sp (Nat.le_max_right growStk extHookStack) (by omega), hsp_s1]
        have hhigh_s1 : PresHigh s0 s1 :=
          ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.1,
           by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
           by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
        have hhigh_sm : PresHigh s0 sm := hhigh_s1.of_callee hcsm
        have hx19_sm : sm.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
          hcsm.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx19)
        have hx20_sm : sm.readReg64 .x20 = x.bytesV :=
          hcsm.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx20)
        have hx21_sm : sm.readReg64 .x21 = namePtr :=
          hcsm.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21)
        have hx22_sm : sm.readReg64 .x22 = x.self :=
          hcsm.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx22)
        have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length :=
          hcsm.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx23)
        have hx24_sm : sm.readReg64 .x24 = ptr :=
          hcsm.2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx24)
        have hx25_sm : sm.readReg64 .x25 = curBase + 32#64 :=
          hcsm.2.2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx25)
        have hx26_sm : sm.readReg64 .x26 = BitVec.ofNat 64 ((rest.length + 1) * 48) :=
          hcsm.2.2.2.2.2.2.2.1.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx26)
        by_cases heq_name : e.1 = x.name
        · -- Match (`w0 = 0`): jump to `step_hit` (`+164`)
          have hw0_z :
              (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = true :=
            w0_cbnz_zero (hbcmp_iff.mpr heq_name)
          have hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest := by
            unfold DirGhost.put
            dsimp only
            rw [hsplit]
            rcases e with ⟨ek, ev⟩
            dsimp only at heq_name
            subst heq_name
            exact setOrPush_hit_middle x.name x.bytes ev pre rest hpre_ne
          have hlen_hit : x.dir.changed.length = (pre ++ (x.name, x.bytes) :: rest).length := by
            simp only [hsplit, List.length_append, List.length_cons]
          code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
            img.base (Rust.withPanics ext) hfn
            (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 160 4
          apply sepWPp_cut_rebase (mid := atOff fnBase 164) hinvm
          dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcm
          dsimp +zetaDelta only [fnBase, atOff]
          set fnBase' := (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)).fnAddr dirPutStrName
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)) = prog
            reverting [Program.fetch]
          examples_hide_fetches
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s2 P2 hinv_s2 ⟨hs2, hP2⟩
          · subst hP2
            let _ := hw0_z
            let _ := hx22_sm
            let _ := hx23_sm
            let _ := hx24_sm
            let _ := hx26_sm
            let _ := hvbuf_close
            let _ := hlatch
            have hprep_hit :
                (ePtr ↦ₛ e.1) ∗ (namePtr ↦ₛ x.name) ∗ stackAt s1.sp extHookStack ∗
                  (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
                  ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
                  vecU8Rest A eCap ePtr e.1 ∗
                  vecU8 A (curBase + 24#64) e.2 ∗
                  A.live ptr (cap.toNat * 48) 8 ∗
                  arrayAt (dirEntryAt A) 48 ptr pre ∗
                  arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
                  memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                    ((cap.toNat - x.dir.changed.length) * 48) ∗
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBufRest A namePtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                  savedSlots s0 ∗
                  A.pool ⊢
                ∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                    ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
                    A.live ptr (cap.toNat * 48) 8 ∗
                    arrayAt (dirEntryAt A) 48 ptr pre ∗
                    vecU8 A curBase x.name ∗
                    ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
                    ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 e.2.length) ∗
                    vecU8Heap A oldCap oldPtr e.2 ∗
                    arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
                    memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
                      ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
                    strRefAt (x.self + 0x18#64) x.dir.path ∗
                    SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                    nameBuf A namePtr x.name ∗
                    (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                    ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                    vecU8Heap A bCap bPtr x.bytes ∗
                    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                    stackAt (s0.sp - 80#64) cal ∗
                    savedSlots s0 ∗
                    A.pool := by
              have ha32 : curBase + 24#64 + 8#64 = curBase + 32#64 := by bv_omega
              have ha40 : curBase + 24#64 + 16#64 = curBase + 40#64 := by bv_omega
              have hv2 : vecU8 A (curBase + 24#64) e.2 =
                  ∃∗ oldCap : BitVec 64, ∃∗ oldPtr : BitVec 64,
                    ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
                    ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 e.2.length) ∗
                    vecU8Heap A oldCap oldPtr e.2 := by
                unfold vecU8
                simp only [vecU8At_eq_header_heap, ha32, ha40]
              rw [hv2]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              refine Entails.sepExists_elim fun oldCap =>
                Entails.trans ?_ (Entails.sepExists_intro oldCap)
              refine Entails.sepExists_elim fun oldPtr =>
                Entails.trans ?_ (Entails.sepExists_intro oldPtr)
              have he_assemble :
                  (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
                    ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
                    ((ePtr ↦ₛ e.1) ∗ vecU8Rest A eCap ePtr e.1) ⊢
                    vecU8 A curBase x.name := by
                rw [← vecU8Heap_expose_bytes, heq_name]
                exact vecU8_of_header_heap A curBase eCap ePtr x.name
              rw [← hstk_back, ← hlen_hit, nameBuf_expose_bytes A namePtr x.name]
              rw [show ∀ (B1 B2 StkE C0 C1 C2 ER O0 O1 O2 OH L0 P0 R0 M0 S0 S1 S2 Path NB NR BC BP BL BH StkM StkC Sav Pool : SepProp),
                    B1 ∗ B2 ∗ StkE ∗ C0 ∗ C1 ∗ C2 ∗ ER ∗ (O0 ∗ O1 ∗ O2 ∗ OH) ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗
                      S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ NR ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ StkC ∗ Sav ∗ Pool =
                    (C0 ∗ C1 ∗ C2 ∗ (B1 ∗ ER)) ∗
                    (S0 ∗ S1 ∗ S2 ∗ L0 ∗ P0 ∗ O0 ∗ O1 ∗ O2 ∗ OH ∗ R0 ∗ M0 ∗
                      Path ∗ NB ∗ (B2 ∗ NR) ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ (StkC ∗ StkE) ∗ Sav ∗ Pool) by
                    intros; ac_rfl]
              exact Entails.trans (sepConj_mono_left he_assemble) (entails_eq (by ac_rfl))
            apply sepWPp_eq_pre
            · apply sepWPp_weaken_pre hprep_hit
              have hpull_ex1 : ∀ (Φ : BitVec 64 → SepProp), (∃∗ a, Φ a) = (∃∗ a, Φ a) ∗ emp :=
                fun _ => (sepConj_emp _).symm
              rw [hpull_ex1]
              refine sepWPp_exists_left fun oldCap => ?_
              rw [sepConj_emp, hpull_ex1]
              refine sepWPp_exists_left fun oldPtr => ?_
              rw [sepConj_emp]
              exact step_hit hC x R s0 s2 pre rest e.2 cap ptr curBase namePtr bCap bPtr oldCap oldPtr
                hstk hstk_max hname32 hput_eq hcur'.out (by rw [← hlen_hit]; exact hle_c) hbnd_c hptr_c hcap_c
                hsp_align0 hinv_s2
                (by rw [hs2]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunm)
                (by
                  have hsp_eq : s2.sp = sm.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
                  have hsp_eq' : sm.sp = s.sp := hspm.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm])
                  simpa only [State.spAligned, hsp_eq, hsp_eq'] using hsp_align)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspm.trans hsp_s1)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htr_sm0.trans htr_s1)
                ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.1,
                 by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.1,
                 by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.2⟩
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx19_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx20_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx21_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx25_sm)
            · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
              repeat rw [ite_false_eq]
              repeat rw [bv_sub_eq_add_neg64]
              try rw [emp_sepConj]
              try rw [sepConj_emp]
              try simp only [wp_norm, arm64_norm]
              try rw [Nat.mul_comm 48]
              try ac_rfl
        · -- Content mismatch (`w0 ≠ 0`): jump to `hlatch` (`+120`)
          have hw0_nz :
              (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false :=
            w0_cbnz_nonzero (fun hz => heq_name (hbcmp_iff.mp hz))
          code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
            img.base (Rust.withPanics ext) hfn
            (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 160 4
          apply sepWPp_cut_rebase (mid := atOff fnBase 120) hinvm
          dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpcm
          dsimp +zetaDelta only [fnBase, atOff]
          set fnBase' := (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)).fnAddr dirPutStrName
          generalize_entry (libsignalSessionCode.rebase img.base
            (Rust.withPanics ext)) = prog
            reverting [Program.fetch]
          examples_hide_fetches
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          intro s2 P2 hinv_s2 ⟨hs2, hP2⟩
          · subst hP2
            let _ := hw0_nz
            have hclose_miss :
                (ePtr ↦ₛ e.1) ∗ (namePtr ↦ₛ x.name) ∗ stackAt s1.sp extHookStack ∗
                  (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
                  ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
                  vecU8Rest A eCap ePtr e.1 ∗
                  vecU8 A (curBase + 24#64) e.2 ∗
                  A.live ptr (cap.toNat * 48) 8 ∗
                  arrayAt (dirEntryAt A) 48 ptr pre ∗
                  arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
                  memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                    ((cap.toNat - x.dir.changed.length) * 48) ∗
                  (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  (x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBufRest A namePtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
                  savedSlots s0 ∗
                  A.pool ⊢
                (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
                  ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
                  vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
                  strRefAt (x.self + 0x18#64) x.dir.path ∗
                  SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
                  nameBuf A namePtr x.name ∗
                  (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
                  ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
                  vecU8Heap A bCap bPtr x.bytes ∗
                  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
                  stackAt (s0.sp - 80#64) cal ∗
                  savedSlots s0 ∗
                  A.pool := by
              rw [← hstk_back, nameBuf_expose_bytes A namePtr x.name]
              rw [show ∀ (B1 B2 StkE C0 C1 C2 ER VO L0 P0 R0 M0 S0 S1 S2 Path NB NR BC BP BL BH StkM StkC Sav Pool : SepProp),
                    B1 ∗ B2 ∗ StkE ∗ C0 ∗ C1 ∗ C2 ∗ ER ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗
                      S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ NR ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ StkC ∗ Sav ∗ Pool =
                    (C0 ∗ C1 ∗ C2 ∗ (B1 ∗ ER) ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0) ∗
                    (S0 ∗ S1 ∗ S2 ∗ Path ∗ NB ∗ (B2 ∗ NR) ∗ BC ∗ BP ∗ BL ∗ BH ∗ StkM ∗ (StkC ∗ StkE) ∗ Sav ∗ Pool) by
                    intros; ac_rfl]
              rw [← vecU8Heap_expose_bytes]
              exact Entails.trans (sepConj_mono_left hvbuf_close) (entails_eq (by ac_rfl))
            apply sepWPp_eq_pre
            · apply sepWPp_weaken_pre hclose_miss
              exact hlatch s2 heq_name hinv_s2
                (by rw [hs2]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hrunm)
                (by
                  have hsp_eq : s2.sp = sm.sp := by rw [hs2]; try simp only [wp_norm, arm64_norm]
                  have hsp_eq' : sm.sp = s.sp := hspm.trans (by rw [hs1]; try simp only [wp_norm, arm64_norm])
                  simpa only [State.spAligned, hsp_eq, hsp_eq'] using hsp_align)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hspm.trans hsp_s1)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact htr_sm0.trans htr_s1)
                ⟨by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.1,
                 by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.1,
                 by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hhigh_sm.2.2⟩
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx19_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx20_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx21_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx22_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx23_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx24_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx25_sm)
                (by rw [hs2]; try simp only [wp_norm, arm64_norm]; try exact hx26_sm)
            · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
              repeat rw [ite_false_eq]
              repeat rw [bv_sub_eq_add_neg64]
              try rw [emp_sepConj]
              try rw [sepConj_emp]
              try simp only [wp_norm, arm64_norm]
              try rw [Nat.mul_comm 48]
              try ac_rfl
    · -- Distinct lengths: jump to `hlatch` (`+120`)
      have he_ne_name : e.1 ≠ x.name := fun h => hlen_eq (congrArg List.length h)
      have hlen_beq :
          (BitVec.ofNat 64 e.1.length == BitVec.ofNat 64 x.name.length) = false := by
        apply beq_false_of_ne
        intro heq_bv
        have h1 := congrArg BitVec.toNat heq_bv
        rw [ofNat_toNat_of_lt (by omega), ofNat_toNat_of_lt (by omega)] at h1
        exact hlen_eq h1
      code_fetches_range CryptoVerification.libsignalSessionCode dirPutStrBin
        img.base (Rust.withPanics ext) hfn
        (ls_off% "<libsignal_cli::stores::Dir>::put::<&str>") 132 12
      apply sepWPp_cut_rebase (mid := atOff fnBase 120) hinv
      dsimp +zetaDelta only [fnBase, tripleRatchetProgAtExt, atOff] at hpc
      dsimp +zetaDelta only [fnBase, atOff]
      set fnBase' := (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr dirPutStrName
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog
        reverting [Program.fetch]
      examples_hide_fetches
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro s1 P1 hinv_s1 ⟨hs1, hP1⟩
      · subst hP1
        let _ := hlen_beq
        let _ := hbcmp
        have hclose_len :
            (curBase ↦₆₄ eCap) ∗ ((curBase + 8#64) ↦₆₄ ePtr) ∗
              ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 e.1.length) ∗
              vecU8Heap A eCap ePtr e.1 ∗
              vecU8 A (curBase + 24#64) e.2 ∗
              A.live ptr (cap.toNat * 48) 8 ∗
              arrayAt (dirEntryAt A) 48 ptr pre ∗
              arrayAt (dirEntryAt A) 48 (curBase + 48#64) rest ∗
              memRegion (ptr + BitVec.ofNat 64 (x.dir.changed.length * 48))
                ((cap.toNat - x.dir.changed.length) * 48) ∗
              (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              nameBuf A namePtr x.name ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              stackAt (s0.sp - 80#64) cal ∗
              savedSlots s0 ∗
              A.pool ⊢
            (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
              ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
              vecBuf A 48 8 (dirEntryAt A) cap ptr x.dir.changed ∗
              strRefAt (x.self + 0x18#64) x.dir.path ∗
              SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
              nameBuf A namePtr x.name ∗
              (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
              ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
              vecU8Heap A bCap bPtr x.bytes ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
              stackAt (s0.sp - 80#64) cal ∗
              savedSlots s0 ∗
              A.pool := by
          rw [show ∀ (C0 C1 C2 EH VO L0 P0 R0 M0 Z : SepProp),
                C0 ∗ C1 ∗ C2 ∗ EH ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0 ∗ Z =
                  (C0 ∗ C1 ∗ C2 ∗ EH ∗ VO ∗ L0 ∗ P0 ∗ R0 ∗ M0) ∗ Z from
                fun _ _ _ _ _ _ _ _ _ _ => by ac_rfl]
          exact Entails.trans (sepConj_mono_left hvbuf_close) (entails_eq (by ac_rfl))
        apply sepWPp_eq_pre
        · apply sepWPp_weaken_pre hclose_len
          exact hlatch s1 he_ne_name hinv_s1
            (by rw [hs1]; try dsimp +zetaDelta only [fnBase, atOff, tripleRatchetProgAtExt]; try simp only [wp_norm, arm64_norm])
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hrun)
            (by
              have hsp_eq : s1.sp = s.sp := by rw [hs1]; try simp only [wp_norm, arm64_norm]
              simpa only [State.spAligned, hsp_eq] using hsp_align)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hsp)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact htr)
            ⟨by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.1,
             by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
             by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx19)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx20)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx21)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx22)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx23)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx24)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx25)
            (by rw [hs1]; try simp only [wp_norm, arm64_norm]; try exact hx26)
        · try dsimp +zetaDelta only [savedSlots, SpqrV1.ChainProofs.bytesAt]
          repeat rw [bv_sub_eq_add_neg64]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try ac_rfl

end CryptoVerification.SignalSession.Cli.PutStr.Helpers
