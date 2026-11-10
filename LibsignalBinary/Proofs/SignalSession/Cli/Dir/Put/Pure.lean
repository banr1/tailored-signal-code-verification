/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Pure, memory, stack, epilogue, and callee-bridge helpers for `Dir::put::<String>`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Put.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SignalSession.Cli

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Layout-independent instruction decodes (`0 .. 288`, 73 instructions) -/

gen_decodes CryptoVerification.libsignalSessionCode_tree dirPutBin
  [(ls_off% "<libsignal_cli::stores::Dir>::put::<alloc::string::String>") →
   (ls_off% "<libsignal_cli::stores::Dir>::put::<alloc::string::String>" + 288)]

/-! ## 2. Pure `DirGhost.setOrPush` lemmas -/

theorem setOrPush_append_of_forall_ne {name bs : List (BitVec 8)}
    {pre suf : List (List (BitVec 8) × List (BitVec 8))}
    (hpre : ∀ e ∈ pre, e.1 ≠ name) :
    DirGhost.setOrPush name bs (pre ++ suf) = pre ++ DirGhost.setOrPush name bs suf := by
  induction pre with
  | nil => rfl
  | cons e es ih =>
    have he : e.1 ≠ name := hpre e (List.Mem.head _)
    have hes : ∀ x ∈ es, x.1 ≠ name := fun x hx => hpre x (List.Mem.tail _ hx)
    simp only [List.cons_append, DirGhost.setOrPush, he, ↓reduceIte, ih hes]

theorem setOrPush_miss {name bs : List (BitVec 8)}
    {xs : List (List (BitVec 8) × List (BitVec 8))}
    (hxs : ∀ e ∈ xs, e.1 ≠ name) :
    DirGhost.setOrPush name bs xs = xs ++ [(name, bs)] := by
  simpa only [List.append_nil, DirGhost.setOrPush] using
    setOrPush_append_of_forall_ne (name := name) (bs := bs) (pre := xs) (suf := []) hxs

theorem setOrPush_hit {name bs oldBs : List (BitVec 8)}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    (hpre : ∀ e ∈ pre, e.1 ≠ name) :
    DirGhost.setOrPush name bs (pre ++ (name, oldBs) :: rest) =
      pre ++ (name, bs) :: rest := by
  rw [setOrPush_append_of_forall_ne hpre]
  simp only [DirGhost.setOrPush, ↓reduceIte]

/-! ## 3. Callee-saved / `ImgCallInv` invariant across basic blocks and calls -/

/-- Untouched callee-saved state across `Dir::put::<String>` (`x28`, `v8..v15`, and `StepInv`),
while `x19..x27` and `x29, x30` live in the `0x60`-byte stack frame. -/
def PutCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInv s0 s

theorem PutCalleeSaved.refl (s0 : State) : PutCalleeSaved s0 s0 :=
  ⟨rfl, rfl, StepInv.refl s0⟩

theorem PutCalleeSaved.trans {s0 s1 s2 : State}
    (h01 : PutCalleeSaved s0 s1) (h12 : PutCalleeSaved s1 s2) :
    PutCalleeSaved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h01.2.2.trans h12.2.2⟩

theorem PutCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : PutCalleeSaved s1 s2 := by
  rcases hcs with ⟨_, _, _, _, _, _, _, _, _, hx28, _, hv⟩
  exact ⟨hx28, hv, hinv⟩

theorem calleeSavedPreserved_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  simp only [CalleeSavedPreserved] at h01 h12 ⊢
  simp_all

theorem PutCalleeSaved.step {s0 s1 s2 : State}
    (h01 : PutCalleeSaved s0 s1)
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInv s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    PutCalleeSaved s0 s2 :=
  h01.trans ⟨hx28, hvregs, hinv⟩

/-- Wrap a `Spec α` with `⌜PutCalleeSaved s0 s⌝` so `ImgCallInv img s` propagates automatically. -/
def withPutCS {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜PutCalleeSaved s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withPutCS {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withPutCS s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withPutCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withPutCS_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withPutCS s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withPutCS, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.2.2 img hinv0, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

/-- Raw (pre-`inImage`) `grow_one` specification matching `growOneDirSpec A img growStk`. -/
def growOneDirRawSpec (A : RustAlloc) (stk : Nat) : Spec GrowOneDirGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.cap.toNat < 2 ^ 32⌝ ∗
      RustHeap.vecAt A 48 8 (dirEntryAt A) x.v x.cap x.ptr x.xs ∗ stackAt s.sp stk ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ ptr' : BitVec 64, RustHeap.vecAt A 48 8 (dirEntryAt A) x.v
        (BitVec.ofNat 64 (max (2 * x.cap.toNat) 4)) ptr' x.xs) ∗
      stackAt s0.sp stk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 4. Layout-independent callee resolution via `ls_rel%` -/

theorem bcmp_ok_at {b : BitVec 64} {ext : String → Option (State → State)}
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName cliBcmpName))
      cliBcmpSpec :=
  hook_ok_at (hname := cliBcmpName) dirPut_fnOff
    (by decide)
    (by decide)
    (fun _ => (ls_hook% "bcmp") _)
    (by decide +kernel)
    hBcmp

theorem dealloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hC.dealloc_ok_at dirPutName (ls_rel% dirPutName deallocName)
    (by rw [dirPut_fnOff, (ls_stub% "__rustc::__rust_dealloc")])

theorem grow_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk : Nat}
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneDirName)
      (growOneDirSpec A img growStk)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName growOneDirName))
      (growOneDirSpec A img growStk) :=
  sub_ok_at_of_fnAddr hGrow dirPutName (ls_rel% dirPutName growOneDirName)
    (by rw [dirPut_fnOff, growOneDir_fnOff])

/-! ## 5. Stack, 128-bit header, and heap-block helpers -/

/-- Heap allocation payload of `vecU8At A v cap ptr bs` without its 24-byte header or pure invariant. -/
def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8At_eq_header_rest' (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
        vecU8Rest A cap ptr bs := by
  unfold vecU8At vecU8Rest
  ac_rfl

/-- Any state simultaneously owning a 64-bit word `a ↦₆₄ v` and positive `stackAt sp stk`
has `stk < 2 ^ 64`. -/
theorem stk_lt_two_pow_64 {m : Memory} {a v sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hpos : 0 < stk) (hm : m ⊨ (a ↦₆₄ v) ∗ (stackAt sp stk ∗ R)) :
    stk < 2 ^ 64 := by
  have hdisj := (IsBlock.pointsTo64 a v).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) (by decide) hpos hm
  have h2 := hdisj.2
  have hlt := (a - (sp - BitVec.ofNat 64 stk)).isLt
  omega

/-- Split `stackAt sp stk` (`96 ≤ stk ≤ 2 ^ 64`) into `stackAt (sp - 96#64) (stk - 96)` and the
12 saved frame slots of `Dir::put::<String>`. -/
theorem stackAt_put_frame {stk : Nat} (h96 : 0x60 ≤ stk) (hle : stk ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp stk =
      stackAt (sp - 96#64) (stk - 96) ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp (stk - 96) 12 (by omega)
  have heq : (stk - 96) + 8 * 12 = stk := by omega
  rw [heq] at h1
  change stackAt sp stk =
    stackAt (sp - 96#64) (stk - 96) ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

theorem stackAt_sub_split {sub N : Nat} (hsub : sub ≤ N) (hN : N ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp N =
      stackAt sp sub ∗ memRegion (sp - BitVec.ofNat 64 N) (N - sub) := by
  have hsum : (N - sub) + sub = N := by omega
  have hsplit := ProofLib.memRegion_split (sp - BitVec.ofNat 64 N) (N - sub) sub (by omega)
  have hadj : sp - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - sub) = sp - BitVec.ofNat 64 sub := by
    have hN_eq : BitVec.ofNat 64 N = BitVec.ofNat 64 sub + BitVec.ofNat 64 (N - sub) := by
      rw [← BitVec.ofNat_add]; congr 1; omega
    rw [hN_eq, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [hsum, hadj, sepConj_comm] at hsplit
  exact hsplit

theorem sp_sub_96_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 96#64) &&& 15#64 = 0#64 := by
  bv_bits

theorem pointsTo64_pair_eq_128 (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  unfold pointsTo128
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by
    ext i hi
    simp
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := by
    ext i hi
    simp
  rw [h0, h1]

theorem vecHeader_eq_q128 (v cap ptr len : BitVec 64) :
    vecHeader v cap ptr len = (v ↦₁₂₈ (ptr ++ cap)) ∗ ((v + 16#64) ↦₆₄ len) := by
  unfold vecHeader
  rw [← sepConj_assoc, pointsTo64_pair_eq_128 v cap ptr]

theorem q128_word_entails_memRegion_24 (v : BitVec 64) (q : BitVec 128) (w : BitVec 64) :
    ((v ↦₁₂₈ q) ∗ ((v + 16#64) ↦₆₄ w)) ⊢ memRegion v 24 := by
  unfold pointsTo128
  rw [sepConj_assoc]
  exact vecHeader_entails_memRegion v (q.extractLsb' 0 64) (q.extractLsb' 64 64) w

theorem vecU8At_eq_q128_rest (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (v ↦₁₂₈ (ptr ++ cap)) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Rest A cap ptr bs := by
  rw [vecU8At_eq_header_rest' A v cap ptr bs, vecHeader_eq_q128, sepConj_assoc]

theorem vecU8_of_vecU8At (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs :=
  Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem vecU8_intro_header_rest {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Rest A cap ptr bs) ⊢ vecU8 A v bs := by
  refine Entails.trans ?_ (vecU8_of_vecU8At A v cap ptr bs)
  rw [vecU8At_eq_header_rest' A v cap ptr bs, pure_sepConj_of_true ⟨hle, hlt, hptr⟩]
  exact Entails.refl _

theorem vecU8_intro_q128_rest {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₁₂₈ (ptr ++ cap)) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Rest A cap ptr bs) ⊢ vecU8 A v bs := by
  rw [← sepConj_assoc, ← vecHeader_eq_q128 v cap ptr (BitVec.ofNat 64 bs.length)]
  exact vecU8_intro_header_rest hle hlt hptr

theorem dirAt_of_vecAt (A : RustAlloc) (d cap ptr : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8))) (path : List (BitVec 8)) :
    (RustHeap.vecAt A 48 8 (dirEntryAt A) d cap ptr xs ∗ strRefAt (d + 0x18#64) path) ⊢
      dirAt A d { changed := xs, path := path } :=
  sepConj_mono_left
    (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _)))

/-- Convert a non-empty-capacity `vecU8Rest` heap allocation into the exact deallocator input
`A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat` together with `LayoutOk cap.toNat 1`. -/
theorem vecU8Rest_dealloc {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hcap0 : cap ≠ 0) (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 ∧
      (vecU8Rest A cap ptr bs ⊢ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  have hpos : 0 < cap.toNat := by
    by_contra h0
    apply hcap0
    apply BitVec.eq_of_toNat_eq
    change cap.toNat = 0
    omega
  refine ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, ?_⟩
  simp only [vecU8Rest, hcap0, ↓reduceIte]
  have hsplit := ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
  rw [show bs.length + (cap.toNat - bs.length) = cap.toNat by omega] at hsplit
  rw [hsplit]
  exact sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs))

/-- Expose `(ptr ↦ₛ bs)` out of `vecU8Rest` for any `cap` (including `cap = 0` when `bs = []`). -/
theorem vecU8Rest_expose_bytes {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hle : bs.length ≤ cap.toNat) :
    vecU8Rest A cap ptr bs =
      (ptr ↦ₛ bs) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs
    simp only [vecU8Rest, ↓reduceIte, pointsToBytes_nil, emp_sepConj]
  · simp only [vecU8Rest, hcap, ↓reduceIte]
    ac_rfl

/-- Split a 48-byte uninitialized slot into the exact cells written by `step_miss` (`+232..+244`). -/
theorem memRegion_48_split_entry (p : BitVec 64) :
    memRegion p 48 =
      (∃∗ l1 : BitVec 64, ∃∗ q1 : BitVec 128, ∃∗ l0 : BitVec 64,
       ∃∗ p0 : BitVec 64, ∃∗ c0 : BitVec 64,
        (p ↦₆₄ c0) ∗ ((p + 8#64) ↦₆₄ p0) ∗ ((p + 16#64) ↦₆₄ l0) ∗
        ((p + 24#64) ↦₁₂₈ q1) ∗ ((p + 40#64) ↦₆₄ l1)) := by
  have hs1 := ProofLib.memRegion_split p 8 40 (by decide)
  have hs2 := ProofLib.memRegion_split (p + 8#64) 8 32 (by decide)
  have hs3 := ProofLib.memRegion_split (p + 8#64 + 8#64) 8 24 (by decide)
  have hs4 := ProofLib.memRegion_split (p + 8#64 + 8#64 + 8#64) 16 8 (by decide)
  change memRegion p 48 = memRegion p 8 ∗ memRegion (p + 8#64) 40 at hs1
  change memRegion (p + 8#64) 40 = memRegion (p + 8#64) 8 ∗ memRegion (p + 8#64 + 8#64) 32 at hs2
  change memRegion (p + 8#64 + 8#64) 32 =
    memRegion (p + 8#64 + 8#64) 8 ∗ memRegion (p + 8#64 + 8#64 + 8#64) 24 at hs3
  change memRegion (p + 8#64 + 8#64 + 8#64) 24 =
    memRegion (p + 8#64 + 8#64 + 8#64) 16 ∗ memRegion (p + 8#64 + 8#64 + 8#64 + 16#64) 8 at hs4
  have h16 : p + 8#64 + 8#64 = p + 16#64 := by bv_arith
  have h24 : p + 16#64 + 8#64 = p + 24#64 := by bv_arith
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_arith
  rw [hs1, hs2, hs3, hs4, h16, h24, h40,
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64),
      ProofLib.memRegion_eight (p + 16#64), ProofLib.memRegion_sixteen (p + 24#64),
      ProofLib.memRegion_eight (p + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

/-! ## 6. Saved-frame bundle and reusable `SepWPp` combinators -/

/-- Saved callee-saved registers in `Dir::put::<String>`'s `0x60`-byte stack frame. -/
def putSavedCells (s0 : State) (v3 : BitVec 64) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ v3) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem putSavedCells_pack {stk : Nat} (h96 : 0x60 ≤ stk) (hle : stk ≤ 2 ^ 64)
    (s0 : State) (v3 : BitVec 64) :
    stackAt (s0.sp - 96#64) (stk - 96) ∗ putSavedCells s0 v3 ⊢ stackAt s0.sp stk := by
  rw [stackAt_put_frame h96 hle s0.sp, putSavedCells]
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.refl _))))))))))))

/-- Execute `bl bcmp` (`aRo = false, bRo = false`) inside `Dir::put::<String>`'s stack frame. -/
theorem step_bcmp_call {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {x0 : DirPutGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hbcmp : subroutine_ok (tripleRatchetProgAtExt img.base ext) call_pc (withPutCS s0 cliBcmpSpec))
    (hsub : extHookStack ≤ stk - 96)
    (hle : stk ≤ 2 ^ 64)
    (a b ret_pc : BitVec 64) (bsA bsB : List (BitVec 8))
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hx1 : s.readReg64 .x1 = b)
    (hx2 : (s.readReg64 .x2).toNat = bsA.length)
    (hlen : bsB.length = bsA.length)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = ((a ↦ₛ bsA) ∗ (b ↦ₛ bsB) ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      ((sm.readReg64 .x0).setWidth 32 = 0#32 ↔ bsA = bsB) →
      CalleeSavedPreserved s sm →
      PutCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        (((a ↦ₛ bsA) ∗ (b ↦ₛ bsB) ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPp.call_cs (x := CliBcmpCall.mk a false bsA b false bsB)
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - extHookStack) ∗ F)
    hbcmp hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    simp only [withPutCS, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true,
      ↓reduceIte, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withPutCS, cliBcmpSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withPutCS, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true,
      ↓reduceIte, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨heq_iff, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' heq_iff hcsm
        (hcs.trans (PutCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by ac_rfl)

/-- Execute `bl __rust_dealloc(ptr, cap.toNat, 1)` on `vecU8Rest A cap ptr bs` (`cap ≠ 0`)
inside `Dir::put::<String>`'s stack frame. -/
theorem step_dealloc_call {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {x0 : DirPutGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext) call_pc
      (withPutCS s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (hsub : extHookStack ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hcap0 : cap ≠ 0)
    (hbs_le : bs.length ≤ cap.toNat)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = (vecU8Rest A cap ptr bs ∗ A.pool ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PutCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        ((A.pool ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hlayout, hrest⟩ := vecU8Rest_dealloc (A := A) (ptr := ptr) hcap0 hbs_le hcap_lt
  refine SepWPp.call_cs (x := (ptr, cap.toNat, 1))
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - extHookStack) ∗ F)
    hdealloc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    have hm' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left hrest))) hm
    simp only [withPutCS, rustDeallocExternSpecWithStack, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, by simp [hx1], by simp [hx2], hlayout⟩, ?_⟩
    convert hm' using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withPutCS, rustDeallocExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [withPutCS, rustDeallocExternSpecWithStack, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm hpcm hrunm hspm htrm' hcsm
        (hcs.trans (PutCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by ac_rfl)

/-- Execute `bl grow_one` inside `Dir::put::<String>`'s stack frame. -/
theorem step_grow_call {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {growStk stk : Nat}
    {call_pc : BitVec 64} {s0 s : State} {x0 : DirPutGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hgrow : subroutine_ok (tripleRatchetProgAtExt img.base ext) call_pc
      (withPutCS s0 (growOneDirRawSpec A growStk)))
    (hsub : growStk ≤ stk - 96)
    (hle_stk : stk ≤ 2 ^ 64)
    (v cap ptr ret_pc : BitVec 64) (xs : List (List (BitVec 8) × List (BitVec 8)))
    (hcap_lt : cap.toNat < 2 ^ 32)
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = (RustHeap.vecAt A 48 8 (dirEntryAt A) v cap ptr xs ∗ A.pool ∗
        stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      PutCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        ((RustHeap.vecAt A 48 8 (dirEntryAt A) v
            (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) newPtr xs ∗
          A.pool ∗ stackAt (s0.sp - 96#64) (stk - 96)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x0 s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPp.call_cs (x := GrowOneDirGhost.mk v cap ptr xs)
    (F := memRegion (s0.sp - 96#64 - BitVec.ofNat 64 (stk - 96)) (stk - 96 - growStk) ∗ F)
    hgrow hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_split hsub (by omega) (s0.sp - 96#64)] at hm
    simp only [withPutCS, growOneDirRawSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hx0, hcap_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withPutCS, growOneDirRawSpec, dirPutSpec, Spec.inImage, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withPutCS, growOneDirRawSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm htrm' hcsm
        (hcs.trans (PutCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_sub_split hsub (by omega) (s0.sp - 96#64)]
    exact Entails.of_eq (by ac_rfl)

/-- Normal-return `SepWPp` postcondition expected by `subroutine_ok_of_sepWPp` for `dirPutSpec`. -/
abbrev putRetQ (A : RustAlloc) (img : Obj.Image) (stk : Nat)
    (x : DirPutGhost) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev stepDst {a b : State} (_ : StepInv a b) : State := b

/-- Execute shared epilogue `+248 .. +272` (`LDP .. RET`) and discharge `dirPutSpec`'s postcondition. -/
theorem step_epilogue_ret {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {v3 : BitVec 64} {P R : SepProp}
    (h96 : 0x60 ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        dirAt A x.self (x.dir.put x.name x.bytes) ∗
        memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ A.pool) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 248 28
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  unfold putSavedCells
  have hsp_align : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_ep
  let sf := stepDst hinv_ep
  have htr_sf : sf.trace = s0.trace := by simp only [sf, stepDst, arm64_norm, htr]
  dsimp only [sf, stepDst] at htr_sf
  refine SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm,
      by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, hcs.1, hcs.2.1]⟩
  dsimp only [dirPutSpec, Spec.inImage]
  rw [htr_sf, pure_sepConj_of_true rfl]
  refine Entails.trans (Entails.of_eq (show _ =
    dirAt A x.self (x.dir.put x.name x.bytes) ∗
      memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗
      (stackAt (s0.sp - 96#64) (stk - 96) ∗ putSavedCells s0 v3) ∗ A.pool by
    unfold putSavedCells; ac_rfl))
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (putSavedCells_pack h96 hle_stk s0 v3)))))

/-- Execute hit-branch tail-dealloc epilogue `+156 .. +192` (`MOV X0..X2`, pop frame,
`B __rust_dealloc`) when `nameCap ≠ 0` and discharge `dirPutSpec`'s postcondition. -/
theorem step_epilogue_tail_dealloc {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    {s0 s : State} {x : DirPutGhost} {v3 nameCap namePtr : BitVec 64} {P R : SepProp}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName +
        BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
      (withPutCS s0 (rustDeallocExternSpecWithStack A extHookStack)))
    (h96 : 0x60 ≤ stk)
    (hhook : extHookStack ≤ stk)
    (hle_stk : stk ≤ 2 ^ 64)
    (hcap0 : nameCap ≠ 0)
    (hna_le : x.name.length ≤ nameCap.toNat)
    (hna_lt : nameCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = namePtr)
    (hx20 : s.readReg64 .x20 = nameCap)
    (hcs : PutCalleeSaved s0 s)
    (hP : P = putSavedCells s0 v3 ∗ stackAt (s0.sp - 96#64) (stk - 96) ∗
        vecU8Rest A nameCap namePtr x.name ∗
        dirAt A x.self (x.dir.put x.name x.bytes) ∗
        memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ A.pool) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P
      (putRetQ A img stk x s0 R)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (dirPutSpec A img stk).onPanic x s0 sf ∗ R)) := by
  code_fetches_range libsignalSessionCode dirPutBin img.base (Rust.withPanics ext)
    (ls_lemma% fnOff dirPutName) (ls_off% dirPutName) 156 40
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr dirPutName = entry
  examples_hide_fetches
  subst hP
  unfold putSavedCells
  have hsp_align : (s0.sp - 96#64) &&& 15#64 = 0#64 := sp_sub_96_aligned halign
  apply SepWPp.of_sepWP_cs
    (mid := entry + BitVec.ofNat 64 (ls_rel% dirPutName deallocName))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_ep
  let s1 := stepDst hinv_ep
  obtain ⟨hlayout, hrest⟩ := vecU8Rest_dealloc (A := A) (ptr := namePtr) hcap0 hna_le hna_lt
  have hcs1 : CalleeSavedPreserved s0 s1 := by
    simp only [s1, stepDst, CalleeSavedPreserved, arm64_norm, hcs.1, hcs.2.1]
  have hput_cs1 : PutCalleeSaved s0 s1 :=
    ⟨by simp only [s1, stepDst, arm64_norm, hcs.1],
     by simp only [s1, stepDst, arm64_norm, hcs.2.1],
     hcs.2.2.trans hinv_ep⟩
  have hsp1 : s1.sp = s0.sp := by simp only [s1, stepDst, arm64_norm, *]
  have hsp_aligned1 : s1.spAligned = true := by
    simp only [State.spAligned, hsp1, beq_iff_eq]
    exact halign
  dsimp only [s1, stepDst] at hcs1 hput_cs1 hsp1 hsp_aligned1
  refine SepWPp.call_cs (ret_pc := s0.readReg64 .lr) (x := (namePtr, nameCap.toNat, 1))
    (F := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
      dirAt A x.self (x.dir.put x.name x.bytes) ∗
      memRegion x.nameV 24 ∗ memRegion x.bytesV 24)
    hdealloc
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_aligned1
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    have hpack :
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
         ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
         ((s0.sp - 72#64) ↦₆₄ v3) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
         ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) ∗
        stackAt (s0.sp - 96#64) (stk - 96) ⊢ stackAt s0.sp stk := by
      rw [sepConj_comm]
      exact putSavedCells_pack h96 hle_stk s0 v3
    have hm1 := Satisfies.mono
      (sepConj_mono_left (Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono hpack
          (sepConj_mono_left (Q := dirAt A x.self (x.dir.put x.name x.bytes) ∗
            memRegion x.nameV 24 ∗ memRegion x.bytesV 24 ∗ A.pool) hrest)))) hm
    rw [stackAt_sub_split hhook hle_stk s0.sp] at hm1
    simp only [withPutCS, rustDeallocExternSpecWithStack, hsp1, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨hput_cs1, ⟨by simp only [arm64_norm, *], by simp [arm64_norm],
      by simp [arm64_norm], hlayout⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withPutCS, rustDeallocExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sf hpcsf hrunsf hspsf hcsm _
    rw [hsp1] at hspsf
    simp only [withPutCS, rustDeallocExternSpecWithStack, hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun htrsf => ?_
    have htr_final : sf.trace = s0.trace := htrsf.trans (by simp only [arm64_norm, htr])
    refine SepWPp.done hpcsf hrunsf ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm,
      hspsf, calleeSavedPreserved_trans hcs1 hcsm⟩
    dsimp only [dirPutSpec, Spec.inImage]
    rw [htr_final, pure_sepConj_of_true rfl, stackAt_sub_split hhook hle_stk s0.sp]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.Put.Helpers
