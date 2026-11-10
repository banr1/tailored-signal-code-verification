/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun

/-!
# `strlen` and `from_utf8` Callee Contracts for `main`

Subroutine contracts for `strlen` and `core::str::converts::from_utf8` (ASCII) from `strlenHook`,
`fromUtf8Hook`, and `CliExternsOk`, together with `utf8Ok_of_ascii`. Length bounds `< 2 ^ 64`
follow unconditionally from address-space disjointness (`cStrAt` and `pointsToBytes`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## ASCII to UTF-8 -/

private theorem utf8EncodeChar_ascii {b : BitVec 8} (hb : b.toNat < 128) :
    (String.utf8EncodeChar (Char.ofNat b.toNat)).map UInt8.toBitVec = [b] := by
  have hv : b.toNat.isValidChar := Or.inl (by omega)
  have hval : (Char.ofNat b.toNat).val.toNat = b.toNat := by
    simp only [Char.ofNat, Char.ofNatAux, hv, ↓reduceDIte]
    rfl
  have hle : b.toNat ≤ 127 := by omega
  simp only [String.utf8EncodeChar, hval, hle, ↓reduceIte, List.map_cons, List.map_nil]
  exact congrArg (· :: []) (BitVec.eq_of_toNat_eq (by simp))

/-- Every byte list with all bytes `< 128` is valid UTF-8 (`Utf8Ok`). -/
theorem utf8Ok_of_ascii {bs : List (BitVec 8)} (h : ∀ b ∈ bs, b.toNat < 128) : Utf8Ok bs := by
  refine ⟨bs.map fun b => Char.ofNat b.toNat, ?_⟩
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.toNat < 128 := h b List.mem_cons_self
    have hbs : ∀ x ∈ bs, x.toNat < 128 := fun x hx => h x (List.mem_cons_of_mem b hx)
    simp only [List.map_cons, List.flatMap_cons, List.map_append, utf8EncodeChar_ascii hb,
      List.singleton_append, ih hbs]

private theorem hookOk_of_eq_retHook {α : Type} {h : State → State} {spec : Spec α}
    (f : α → State → State)
    (heq : ∀ x R s0, s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) →
      h s0 = retHook (f x) s0)
    (hok : ∀ x, HookOk (retHook (f x))
      { pre := fun (_ : Unit) => spec.pre x
        post := fun _ => spec.post x
        onPanic := fun _ => spec.onPanic x
        onExit := fun _ => spec.onExit x
        onOom := fun _ => spec.onOom x }) :
    HookOk h spec := by
  intro x R s0 hrun hpre hsp
  rw [heq x R s0 hrun hpre]
  exact hok x () R s0 hrun hpre hsp

private theorem memRegion_24_words (r : BitVec 64) :
    memRegion r 24 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗
      ((∃∗ w1 : BitVec 64, (r + 8#64) ↦₆₄ w1) ∗
       (∃∗ w2 : BitVec 64, (r + 16#64) ↦₆₄ w2)) := by
  rw [memRegion_split' (n := 8) (k := 16) rfl rfl (by decide),
    ProofLib.memRegion_eight r,
    memRegion_split' (b := r + 8#64) (n := 8) (k := 8) (b' := r + 16#64)
      rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (r + 8#64),
    ProofLib.memRegion_eight (r + 16#64)]

private theorem getD_append_right_zero (s : List (BitVec 8)) :
    (s ++ [0#8]).getD s.length 0#8 = 0#8 := by
  simp [List.getD]

private theorem getD_append_left {s : List (BitVec 8)} {m : Nat} (hm : m < s.length) :
    (s ++ [0#8]).getD m 0#8 = s[m] := by
  simp [List.getD, List.getElem?_append_left hm, hm]

/-! ## Hook Contracts -/

theorem strlenHook_ok (hookStack : Nat) : HookOk strlenHook (strlenSpec hookStack) := by
  refine hookOk_of_eq_retHook (fun (_, s) st => st.writeReg64 .x0 (BitVec.ofNat 64 s.length))
    (fun ⟨p, s⟩ R s0 _hrun hpre => ?_) (fun ⟨p, s⟩ => ?_)
  · simp only [strlenSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hno0⟩, hmem⟩
    have hmem' : s0.mem ⊨ (p ↦ₛ (s ++ [0#8])) ∗ (stackAt s0.sp hookStack ∗ R) := hmem
    obtain ⟨hlen, hread⟩ := (IsBlock.pointsToBytes p (s ++ [0#8])).read hmem'
    have hcan0 : s0.mem.canRead p (s ++ [0#8]).length = true :=
      (IsBlock.pointsToBytes p (s ++ [0#8])).canRead hlen hmem'
    have hcan : s0.mem.canRead p (s.length + 1) = true := by simpa using hcan0
    have hnul : s0.mem.read8 (p + BitVec.ofNat 64 s.length) = 0#8 := by
      rw [Memory.read8_of_readBytes s0.mem p (s ++ [0#8]) hread s.length (by simp)]
      exact getD_append_right_zero s
    have hex : ∃ n, s0.mem.canRead p (n + 1) = true ∧
        s0.mem.read8 (p + BitVec.ofNat 64 n) = 0#8 :=
      ⟨s.length, hcan, hnul⟩
    have hfind : Nat.find hex = s.length := by
      refine (Nat.find_eq_iff hex).mpr ⟨⟨hcan, hnul⟩, fun m hm ⟨_, hm0⟩ => ?_⟩
      rw [Memory.read8_of_readBytes s0.mem p (s ++ [0#8]) hread m (by simp; omega),
        getD_append_left hm] at hm0
      exact hno0 s[m] (List.getElem_mem hm) hm0
    unfold strlenHook
    dsimp only
    simp only [hx0, hex, ↓reduceDIte, hfind]
  · refine retHook_ok fun _ R s0 hrun hpre _hsp => ?_
    simp only [strlenSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hmem⟩
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    simp only [strlenSpec, retHook, State.setPC, State.writeReg64, State.readReg64,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, trivial, trivial⟩, hmem⟩

theorem fromUtf8Hook_ok (hookStack : Nat) (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    HookOk (fromUtf8Hook err) (fromUtf8AsciiSpec hookStack) := by
  refine hookOk_of_eq_retHook
    (fun (r, p, bs) st =>
      st.setMem (((st.mem.write64 r 0#64).write64 (r + 8#64) p).write64
        (r + 16#64) (BitVec.ofNat 64 bs.length)))
    (fun ⟨r, p, bs⟩ R s0 _hrun hpre => ?_) (fun ⟨r, p, bs⟩ => ?_)
  · simp only [fromUtf8AsciiSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx8, hascii⟩, hmem⟩
    obtain ⟨hbs_le, hread⟩ := (IsBlock.pointsToBytes p bs).read hmem
    have hcanR : s0.mem.canRead p bs.length = true :=
      (IsBlock.pointsToBytes p bs).canRead hbs_le hmem
    have hmemR : s0.mem ⊨ memRegion r 24 ∗ ((p ↦ₛ bs) ∗ (stackAt s0.sp hookStack ∗ R)) := by
      ac_nf at hmem ⊢
    have hcanW : s0.mem.canWrite r 24 = true :=
      (IsBlock.memRegion r 24).canWrite (by decide) hmemR
    have hbs_ne : bs.length ≠ 2 ^ 64 := by
      intro heq
      rw [memRegion_24_words r] at hmem
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        satisfies_sepExists] at hmem
      rcases hmem with ⟨w2, w1, w0, hw⟩
      exact pointsToBytes_full_false heq hw
    have hbs_lt : bs.length < 2 ^ 64 := by omega
    have hlen_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs_lt]
    have hutf8 : Utf8Ok bs := utf8Ok_of_ascii hascii
    change fromUtf8Hook err s0 = _
    unfold fromUtf8Hook
    have hx8' : s0.readReg64 .x8 = r := hx8
    dsimp only
    rw [hx0, hx1, hx8', hlen_nat, hcanR, hcanW, hread]
    simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hutf8]
  · refine retHook_ok fun _ R s0 hrun hpre _hsp => ?_
    simp only [fromUtf8AsciiSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hmem⟩
    rw [memRegion_24_words r] at hmem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      satisfies_sepExists] at hmem
    rcases hmem with ⟨w2, w1, w0, hw⟩
    let F : SepProp := (p ↦ₛ bs) ∗ (stackAt s0.sp hookStack ∗ R)
    have h0 : s0.mem ⊨ (r ↦₆₄ w0) ∗ (((r + 8#64) ↦₆₄ w1) ∗ (((r + 16#64) ↦₆₄ w2) ∗ F)) := by
      dsimp only [F]; ac_nf at hw ⊢
    have hkf1 : s0.mem.KeepsFrozen (s0.mem.write64 r 0#64) :=
      Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 r w0).canWrite (by decide) h0) 0#64
    have hw1 := IsBlock.write64 (IsBlock.pointsTo64 r w0) h0 0#64
    have h1 : s0.mem.write64 r 0#64 ⊨
        ((r + 8#64) ↦₆₄ w1) ∗ (((r + 16#64) ↦₆₄ w2) ∗ ((r ↦₆₄ 0#64) ∗ F)) := by
      ac_nf at hw1 ⊢
    have hkf2 : s0.mem.KeepsFrozen ((s0.mem.write64 r 0#64).write64 (r + 8#64) p) :=
      hkf1.trans
        (Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 (r + 8#64) w1).canWrite (by decide) h1) p)
    have hw2 := IsBlock.write64 (IsBlock.pointsTo64 (r + 8#64) w1) h1 p
    have h2 : (s0.mem.write64 r 0#64).write64 (r + 8#64) p ⊨
        ((r + 16#64) ↦₆₄ w2) ∗ ((r ↦₆₄ 0#64) ∗ (((r + 8#64) ↦₆₄ p) ∗ F)) := by
      ac_nf at hw2 ⊢
    have hkf3 : s0.mem.KeepsFrozen
        (((s0.mem.write64 r 0#64).write64 (r + 8#64) p).write64
          (r + 16#64) (BitVec.ofNat 64 bs.length)) :=
      hkf2.trans (Memory.keepsFrozen_write64
        ((IsBlock.pointsTo64 (r + 16#64) w2).canWrite (by decide) h2)
        (BitVec.ofNat 64 bs.length))
    have hw3 := IsBlock.write64 (IsBlock.pointsTo64 (r + 16#64) w2) h2 (BitVec.ofNat 64 bs.length)
    refine ⟨hkf3, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [fromUtf8AsciiSpec, State.setMem]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    dsimp only [F] at hw3
    ac_nf at hw3 ⊢

/-! ## Subroutine Contracts at Stub Entries -/

/-- `strlen` satisfies `(strlenSpec hookStack).inImage img` at its stub entry in `mProg img ext`. -/
theorem strlen_ok {img : Obj.Image} {ext : String → Option (State → State)} {hookStack : Nat}
    (hext : ext "strlen" = some strlenHook) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr "strlen")
      ((strlenSpec hookStack).inImage img) := by
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (k := 0)
    (ls_stub% "strlen") (Nat.add_zero _) (by decide) (ls_hook% "strlen")
    (by simp [Rust.isPanicSymbol]) ⟨strlenHook, hext, strlenHook_ok hookStack⟩
  simpa only [BitVec.add_zero] using h

/-- `core::str::converts::from_utf8` satisfies `(fromUtf8AsciiSpec hookStack).inImage img` at its stub entry in `mProg img ext`. -/
theorem fromUtf8Ascii_ok {img : Obj.Image} {ext : String → Option (State → State)}
    {hookStack : Nat} {err : List (BitVec 8) → BitVec 64 × BitVec 16}
    (hext : ext "core::str::converts::from_utf8" = some (fromUtf8Hook err)) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) := by
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (k := 0)
    (ls_stub% "core::str::converts::from_utf8") (Nat.add_zero _) (by decide)
    (ls_hook% "core::str::converts::from_utf8")
    (by simp [Rust.isPanicSymbol]) ⟨fromUtf8Hook err, hext, fromUtf8Hook_ok hookStack err⟩
  simpa only [BitVec.add_zero] using h

theorem strlen_ok_cliExterns {img : Obj.Image} {hookStack : Nat} (W : CliHooks) :
    subroutine_ok (mProg img (cliExterns W)) ((mProg img (cliExterns W)).fnAddr "strlen")
      ((strlenSpec hookStack).inImage img) :=
  strlen_ok (cliExterns_row W (List.mem_append_right _ (by simp)))

theorem fromUtf8Ascii_ok_cliExterns {img : Obj.Image} {hookStack : Nat} (W : CliHooks) :
    subroutine_ok (mProg img (cliExterns W))
      ((mProg img (cliExterns W)).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) :=
  fromUtf8Ascii_ok (err := W.utf8Err) (cliExterns_row W (List.mem_append_right _ (by simp)))

section MainCalleesCheck
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

private example (img : Obj.Image) (A : RustAlloc) (uuidParse : UuidParser)
    (hookStack resStack : Nat) (W : CliHooks)
    (halloc : AllocContractsX img A (cliExterns W))
    (hallocFs : AllocContractsFs img A (cliExterns W))
    (haddr : subroutine_ok (mProg img (cliExterns W))
      ((mProg img (cliExterns W)).fnAddr addressName)
      ((addressSpec A uuidParse resStack).inImage img))
    (hres16 : subroutine_ok (mProg img (cliExterns W))
      ((mProg img (cliExterns W)).fnAddr reserve11Name)
      ((reserve16Spec A resStack).inImage img))
    (hres1 : subroutine_ok (mProg img (cliExterns W))
      ((mProg img (cliExterns W)).fnAddr reserve11Name)
      ((CryptoVerification.SpqrV1.Varint.doReserveSpecOf resStack A).keepsFs.inImage img))
    (htry3 : subroutine_ok (mProg img (cliExterns W))
      ((mProg img (cliExterns W)).fnAddr tryAllocateIn3Name)
      ((tryAllocateInSpecOf resStack A).keepsFs.inImage img)) :
    MainCallees img A (cliExterns W) uuidParse hookStack resStack :=
  { alloc := halloc
    allocFs := hallocFs
    strlen := strlen_ok_cliExterns W
    fromUtf8 := fromUtf8Ascii_ok_cliExterns W
    address := haddr
    reserve16 := hres16
    reserve1 := hres1
    tryAllocateIn3 := htry3 }

end MainCalleesCheck

/-! ## `CliExternsOk` Lifting -/

private theorem stackAt_split_ext_utf8 (sp : BitVec 64) {stk : Nat}
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
      stackAt sp extHookStack := by
  have h1 := stackAt_split_bottom sp extHookStack (stk - extHookStack) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

/-- Frames `HookSat ext "strlen" CliExt.strlenSpec` to any stack budget `extHookStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem strlen_ok_of_hookSat {img : Obj.Image} {ext : String → Option (State → State)}
    {hookStack : Nat} (hsat : HookSat ext "strlen" CliExt.strlenSpec)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img ext) ((mProg img ext).fnAddr "strlen")
      ((strlenSpec hookStack).inImage img) := by
  rcases hsat with ⟨f, hf, hh⟩
  have hh' : HookOk f (strlenSpec hookStack) := by
    intro ⟨p, s⟩ R s0 hrun hpre hsp
    have hsplit := stackAt_split_ext_utf8 s0.sp hle hmax
    let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗ R
    have hpre' : s0.mem ⊨ CliExt.strlenSpec.pre (p, s) s0 ∗ R' := by
      dsimp only [strlenSpec, CliExt.strlenSpec, CliExt.cStrAt, Cli.cStrAt, R'] at hpre ⊢
      rw [hsplit] at hpre
      ac_nf at hpre ⊢
    obtain ⟨hkf, hsym, hout⟩ := hh (p, s) R' s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [strlenSpec, CliExt.strlenSpec, CliExt.cStrAt, Cli.cStrAt, R'] at hpost ⊢
      rw [hsplit]
      ac_nf at hpost ⊢
    · dsimp only [CliExt.strlenSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.strlenSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.strlenSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
    (hname := "strlen") (k := 0) (ls_stub% "strlen") (Nat.add_zero _) (by decide)
    (ls_hook% "strlen") (by simp [Rust.isPanicSymbol]) ⟨f, hf, hh'⟩
  simpa only [BitVec.add_zero] using h

/-- Frames `HookSat ext "core::str::converts::from_utf8" CliExt.fromUtf8Spec` to any stack budget `extHookStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem fromUtf8Ascii_ok_of_hookSat {img : Obj.Image} {ext : String → Option (State → State)}
    {hookStack : Nat}
    (hsat : HookSat ext "core::str::converts::from_utf8" CliExt.fromUtf8Spec)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img ext)
      ((mProg img ext).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) := by
  rcases hsat with ⟨f, hf, hh⟩
  have hh' : HookOk f (fromUtf8AsciiSpec hookStack) := by
    intro ⟨r, p, bs⟩ R s0 hrun hpre hsp
    have hsplit := stackAt_split_ext_utf8 s0.sp hle hmax
    let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗ R
    have hpre' : s0.mem ⊨ CliExt.fromUtf8Spec.pre (r, p, bs) s0 ∗ R' := by
      dsimp only [fromUtf8AsciiSpec, CliExt.fromUtf8Spec, R'] at hpre ⊢
      rw [hsplit] at hpre
      ac_nf at hpre ⊢
    obtain ⟨hkf, hsym, hout⟩ := hh (r, p, bs) R' s0 hrun hpre' hsp
    refine ⟨hkf, hsym, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [fromUtf8AsciiSpec, CliExt.fromUtf8Spec, R'] at hpost ⊢
      rw [hsplit]
      ac_nf at hpost ⊢
    · dsimp only [CliExt.fromUtf8Spec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.fromUtf8Spec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
    · dsimp only [CliExt.fromUtf8Spec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
    (hname := "core::str::converts::from_utf8") (k := 0)
    (ls_stub% "core::str::converts::from_utf8") (Nat.add_zero _) (by decide)
    (ls_hook% "core::str::converts::from_utf8") (by simp [Rust.isPanicSymbol]) ⟨f, hf, hh'⟩
  simpa only [BitVec.add_zero] using h

theorem strlen_ok_ext {P : E2E.PEParams} {A : CryptoVerification.RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (hookStack : Nat := extHookStack)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr "strlen")
      ((strlenSpec hookStack).inImage img) := by
  rcases hOk.strlen with ⟨f, hf, hh⟩
  have hnpe : E2E.isImagePanicSymbol "strlen" = false := by
    simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol]
  have hsat : HookSat (cliExternsWith ext) "strlen" CliExt.strlenSpec :=
    ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnpe).trans hf, hh⟩
  exact strlen_ok_of_hookSat hsat hle hmax

theorem fromUtf8Ascii_ok_ext {P : E2E.PEParams} {A : CryptoVerification.RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (hookStack : Nat := extHookStack)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) := by
  rcases hOk.fromUtf8 with ⟨f, hf, hh⟩
  have hnpe : E2E.isImagePanicSymbol "core::str::converts::from_utf8" = false := by
    simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol]
  have hsat : HookSat (cliExternsWith ext) "core::str::converts::from_utf8" CliExt.fromUtf8Spec :=
    ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnpe).trans hf, hh⟩
  exact fromUtf8Ascii_ok_of_hookSat hsat hle hmax

theorem fromUtf8_ok_ext {P : E2E.PEParams} {A : CryptoVerification.RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (hookStack : Nat := extHookStack)
    (hle : extHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr "core::str::converts::from_utf8")
      ((fromUtf8AsciiSpec hookStack).inImage img) :=
  fromUtf8Ascii_ok_ext hOk img hookStack hle hmax

end CryptoVerification.SignalSession.Cli.MainHops
