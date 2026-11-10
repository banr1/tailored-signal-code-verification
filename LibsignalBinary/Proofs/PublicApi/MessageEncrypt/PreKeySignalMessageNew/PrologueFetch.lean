/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# `PreKeySignalMessage::new` Prologue Fetches, OOM Panics, and Layout Helpers

Instruction decode lemmas for `+0x000..+0x25c` of `PreKeySignalMessage::new` (`0x15130`), `SepWPp`
sequencing and OOM panic-block helpers (`+0x060`, `+0x10c`, `+0x204`), callee `subroutine_ok`
projections, and separation-logic pack/unpack lemmas.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification

gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x15130 → 0x1538c]

elab "preKeyMsg_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := 0x15130
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x15130
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

end Fetch

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open ProofLib.ProgramReflection

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev preKeyMsgNewName : String :=
  "<libsignal_protocol::protocol::PreKeySignalMessage>::new"

theorem fnAddr_preKeyMsgNew_eq (img : Obj.Image) {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName = preKeyMsgNewEntry img := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, preKeyMsgNewEntry, preKeyMsgNewName,
    CryptoVerification.libsignalSessionCode_fnOff_0x15130]

theorem fnAddr_preKeyMsgNew_add_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff preKeyMsgNewName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by
      simp only [arm64_norm]) :
    (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + off =
      (tripleRatchetProgAt b C ctl abs).fnAddr target := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem fnAddr_preKeyMsgNew_eq_ext (img : Obj.Image)
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName = preKeyMsgNewEntry img := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, preKeyMsgNewEntry, preKeyMsgNewName,
    CryptoVerification.libsignalSessionCode_fnOff_0x15130]

theorem fnAddr_preKeyMsgNew_add_eq_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff preKeyMsgNewName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by
      simp only [arm64_norm]) :
    (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + off =
      (tripleRatchetProgAtExt b ext).fnAddr target := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem fnAddr_preKeyMsgNew_eq_trap (img : Obj.Image) {C : Crypto}
    {abs : String → Option (State → State)} :
    (trTrapProgAt img.base C abs).fnAddr preKeyMsgNewName = preKeyMsgNewEntry img :=
  fnAddr_preKeyMsgNew_eq_ext img

theorem fnAddr_preKeyMsgNew_add_eq_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff preKeyMsgNewName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target) := by
      simp only [arm64_norm]) :
    (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + off =
      (trTrapProgAt b C abs).fnAddr target :=
  fnAddr_preKeyMsgNew_add_eq_ext h

theorem allocHooks_of_trTrap_trap {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A (trTrapExterns C abs)) : AllocHooks A abs :=
  ⟨by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_alloc") (by decide) (by decide)] using hA.alloc,
   by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_dealloc") (by decide) (by decide)] using hA.dealloc,
   by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_realloc") (by decide) (by decide)] using hA.realloc⟩

theorem trTrap_allocHooks {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) : AllocHooks A (trTrapExterns C abs) :=
  ⟨by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_alloc") (by decide) (by decide)] using hA.alloc,
   by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_dealloc") (by decide) (by decide)] using hA.dealloc,
   by simpa only [HookSat, trTrapExterns_of_not_mem C abs (n := "__rustc::__rust_realloc") (by decide) (by decide)] using hA.realloc⟩

theorem trTrap_shim_hookSat {C : Crypto} {abs : String → Option (State → State)} :
    HookSat (trTrapExterns C abs) shimName sessionShimSpec :=
  ⟨hookNoop, by rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 abs (by decide)]; rfl,
    sessionShim_hookOk⟩

theorem trTrap_memcpy_hookSat {C : Crypto} {abs : String → Option (State → State)} :
    HookSat (trTrapExterns C abs) memcpyName (sessionMemcpySpec allocHookStack) :=
  ⟨hookMemcpy, by rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 abs (by decide)]; rfl,
    hookMemcpy_trace_ok allocHookStack⟩

/-! ## `SepWPp` Sequencing and Panic Helpers -/

def PanicAllocPost (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)

theorem panicAllocPost_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    PanicAllocPost s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

theorem allocFailedIn_of_append_one {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P)
    (h : P = Q ∗ emp) : m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

def not_satisfies_false_sepConj2 {α : Sort*} {m : Memory} {P Q : SepProp}
    (h : m ⊨ (⌜False⌝ ∗ P) ∗ Q) : α :=
  (not_satisfies_false_sepConj (R := P ∗ Q) (m := m) (by rwa [sepConj_assoc] at h)).elim

theorem pull_pure_alloc_oom (P1 P2 F : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ ⌜φ⌝) ∗ F = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ F) := by ac_rfl

theorem pull_pure_alloc_ok (P1 P2 P3 F : SepProp) (φ : Prop) :
    (P1 ∗ P2 ∗ (⌜φ⌝ ∗ P3)) ∗ F = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ P3 ∗ F) := by ac_rfl

theorem preKeyMsg_seq_wpp {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, _hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_seq_wp {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _hoom⟩⟩ := h1.elim hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj _hoom).elim

/-! ## Callee `subroutine_ok` Wrappers -/

theorem preKeyMsg_shim_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130)) noAllocShimSpec :=
  noAllocShim_ok_at (name := preKeyMsgNewName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))

theorem preKeyMsg_alloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + bv% (ls_off% "__rustc::__rust_alloc" - 0x15130)) (rustAllocSpec A) :=
  alloc_ok_at_norm hA (name := preKeyMsgNewName) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x15130))

theorem preKeyMsg_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130)) framelessMemcpySpec :=
  framelessMemcpy_ok_at (name := preKeyMsgNewName) (k := num% (ls_off% "memcpy" - 0x15130))

theorem preKeyMsg_publicKeySerialize_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 168340#64) (publicKeySerializeSpec A) := by
  rw [fnAddr_preKeyMsgNew_add_eq (target := publicKeySerializeName)]
  exact Glue.publicKeySerializeOk hA

theorem preKeyMsg_encodedLen_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hEncLen : PreKeyMsgEncodedLenOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName + 100920#64) (preKeyMsgEncodedLenSpec A) := by
  have haddr : (tripleRatchetProgAt img.base C ctl abs).fnAddr preKeyMsgNewName + 100920#64 =
      img.base + 0x2db68#64 := by
    rw [fnAddr_preKeyMsgNew_eq, preKeyMsgNewEntry, BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hEncLen

theorem preKeyMsg_shim_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130)) noAllocShimSpec :=
  hook_ok_at (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))
    (stub := libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, by rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 abs (by decide)]; rfl, noAllocShim_hookOk⟩

theorem preKeyMsg_alloc_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + bv% (ls_off% "__rustc::__rust_alloc" - 0x15130)) (rustAllocSpec A) :=
  alloc_ok_at_norm_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)
    (name := preKeyMsgNewName) (k := num% (ls_off% "__rustc::__rust_alloc" - 0x15130))

theorem preKeyMsg_memcpy_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + bv% (ls_off% "memcpy" - 0x15130)) framelessMemcpySpec :=
  hook_ok_at (k := num% (ls_off% "memcpy" - 0x15130))
    (stub := libsignalSessionCode.fnOff "memcpy")
    (hname := "memcpy") rfl
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, by rw [trTrapExterns_eq_tripleRatchetExterns C 0#64 abs (by decide)]; rfl, framelessMemcpy_hookOk⟩

theorem preKeyMsg_publicKeySerialize_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 168340#64) (publicKeySerializeSpec A) := by
  rw [fnAddr_preKeyMsgNew_add_eq_trap (target := publicKeySerializeName)]
  exact public_key_serialize_ok_ext (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA)

theorem preKeyMsg_encodedLen_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hEncLen : PreKeyMsgEncodedLenOk_trap img C A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr preKeyMsgNewName + 100920#64) (preKeyMsgEncodedLenSpec A) := by
  have haddr : (trTrapProgAt img.base C abs).fnAddr preKeyMsgNewName + 100920#64 =
      img.base + 0x2db68#64 := by
    rw [fnAddr_preKeyMsgNew_eq_trap, preKeyMsgNewEntry, BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hEncLen

theorem preKeyMsg_shim_ok_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hSh : HookSat ext shimName sessionShimSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))
      noAllocShimSpec :=
  hook_ok_at (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15130))
    (stub := libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl
    (by simp only [arm64_norm])
    (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
    hSh

theorem preKeyMsg_alloc_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName +
        bv% (ls_off% "__rustc::__rust_alloc" - 0x15130))
      (rustAllocSpec A) :=
  alloc_ok_at_ext b A ext hA preKeyMsgNewName
    (num% (ls_off% "__rustc::__rust_alloc" - 0x15130))

theorem preKeyMsg_memcpy_ok_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (hMc : HookSat ext memcpyName (sessionMemcpySpec allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName +
        bv% (ls_off% "memcpy" - 0x15130))
      (withStack framelessMemcpySpec allocHookStack) := by
  have hraw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName +
        bv% (ls_off% "memcpy" - 0x15130))
      (sessionMemcpySpec allocHookStack) :=
    hook_ok_at (k := num% (ls_off% "memcpy" - 0x15130))
      (stub := libsignalSessionCode.fnOff "memcpy")
      (hname := "memcpy") rfl
      (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol])
      hMc
  refine subroutine_ok_mono hraw (fun (dst, src, bs) R s0 hpre => ?_)
    (fun (dst, src, bs) R s0 sf hpost => ?_)
  · dsimp only [withStack, framelessMemcpySpec] at hpre
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    dsimp only [sessionMemcpySpec, libcMemcpySpec] at hm ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpySpec, withStack, framelessMemcpySpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem preKeyMsg_publicKeySerialize_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocHooks A ext)
    (hSh : HookSat ext shimName sessionShimSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 168340#64)
      (publicKeySerializeSpec A) := by
  rw [fnAddr_preKeyMsgNew_add_eq_ext (target := publicKeySerializeName)]
  apply subroutine_ok_of_optNone
  refine public_key_serialize_ok_of_hooks_opt (oimg := none) (by decide) ?_ ?_
  · apply subroutine_ok_to_optNone
    have hsh0 : subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName +
          BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "<libsignal_core::curve::PublicKey>::serialize")))
        sessionShimSpec :=
      hook_ok_at (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_core::curve::PublicKey>::serialize"))
        (stub := libsignalSessionCode.fnOff shimName)
        (hname := shimName) rfl
        (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, shimName])
        hSh
    have hsh1 := subroutine_ok_withStack_of_subroutine_ok hsh0 allocHookStack
    refine subroutine_ok_mono hsh1 (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
    dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  · exact subroutine_ok_to_optNone
      (alloc_ok_at_ext b A ext hA publicKeySerializeName
        (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_core::curve::PublicKey>::serialize")))

theorem preKeyMsg_encodedLen_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEncLen : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + 0x2db68#64)
      (preKeyMsgEncodedLenSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 100920#64)
      (preKeyMsgEncodedLenSpec A) := by
  have haddr : (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgNewName + 100920#64 =
      img.base + 0x2db68#64 := by
    rw [fnAddr_preKeyMsgNew_eq_ext, preKeyMsgNewEntry, BitVec.add_assoc]
    rfl
  rw [haddr]
  exact hEncLen

/-! ## OOM Panic Blocks (`+0x060`, `+0x10c`, `+0x204`) -/

theorem preKeyMsg_oom_at_060_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 96#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (PanicAllocPost s0) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b)
    (ext := ext) (name := preKeyMsgNewName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x15130))
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x060 0x068
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x15130))
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem preKeyMsg_oom_at_060_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 96#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (PanicAllocPost s0) :=
  preKeyMsg_oom_at_060_ext hpc hrun htr

theorem preKeyMsg_oom_at_060 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 96#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc
  exact SepWPp_kit_of_trTrap (preKeyMsg_oom_at_060_trap hpc hrun htr)

theorem preKeyMsg_oom_at_10c_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 268#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (PanicAllocPost s0) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b)
    (ext := ext) (name := preKeyMsgNewName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x15130))
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x10c 0x114
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x15130))
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem preKeyMsg_oom_at_10c_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 268#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (PanicAllocPost s0) :=
  preKeyMsg_oom_at_10c_ext hpc hrun htr

theorem preKeyMsg_oom_at_10c {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 268#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc
  exact SepWPp_kit_of_trTrap (preKeyMsg_oom_at_10c_trap hpc hrun htr)

theorem preKeyMsg_oom_at_204_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName + 516#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (PanicAllocPost s0) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b)
    (ext := ext) (name := preKeyMsgNewName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - 0x15130))
  preKeyMsg_fetches_range b (Rust.withPanics ext) 0x204 0x20c
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x15130))
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem preKeyMsg_oom_at_204_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr preKeyMsgNewName + 516#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (PanicAllocPost s0) :=
  preKeyMsg_oom_at_204_ext hpc hrun htr

theorem preKeyMsg_oom_at_204 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgNewName + 516#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicAllocPost s0) := by
  rw [← trTrapProgAt_fnAddr_eq b C ctl abs preKeyMsgNewName] at hpc
  exact SepWPp_kit_of_trTrap (preKeyMsg_oom_at_204_trap hpc hrun htr)

/-! ## Arithmetic and Stack/Memory Lemmas -/

theorem publicKey_serialize_length (pk : PublicKey) :
    pk.serialize.length = 33 := by
  simp [PublicKey.serialize, List.Vector.toList_length]

theorem preKeyMsgWireLengthsFit_protoMsg (x : PreKeyMsgNewCall)
    (hfit : x.model.serialized.length < 2 ^ 62) :
    PreKeyMsgWireLengthsFit x.protoMsg := by
  unfold PreKeyMsgWireLengthsFit
  have hlen : x.model.serialized.length = x.protoMsg.encode.length + 1 :=
    model_serialized_length x
  omega

theorem preKeyMsg_encLen_overflow_checks {n : Nat} (h : n + 1 < 2 ^ 62) :
    BitVec.ult (BitVec.ofNat 64 n + 1#64) (BitVec.ofNat 64 n) = false ∧
    (BitVec.ofNat 64 n + 1#64).getLsbD 63 = false ∧
    BitVec.ult 9223372036854775806#64 (BitVec.ofNat 64 n) = false ∧
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) ∧
    (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn1 : (BitVec.ofNat 64 n + 1#64).toNat = n + 1 := by
    rw [BitVec.toNat_add, hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hn1' : (BitVec.ofNat 64 (n + 1)).toNat = n + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_, ?_, hn1'⟩
  · simp [BitVec.ult, hn, hn1]
  · rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hn1]
    exact Nat.testBit_lt_two_pow (by omega)
  · simp [BitVec.ult, hn]; omega
  · apply BitVec.eq_of_toNat_eq
    rw [hn1, hn1']

theorem versionByte_word_eq (w : BitVec 32) :
    ((4#32 ||| (w <<< 4)).setWidth 64).setWidth 8 = versionByte (w.setWidth 8) := by
  unfold versionByte currentVersion
  bv_bits

theorem vecU8At_eq_of_pos (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < cap.toNat) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  have hne : cap ≠ 0#64 := by
    intro h
    subst h
    simp at hpos
  simp [vecU8At, vecHeader, hne, sepConj_assoc]

theorem pack_serPrefix0 (A : RustAlloc) (sp0 serPtr : BitVec 64)
    (v : BitVec 8) (encLen : Nat)
    (h : encLen + 1 < 2 ^ 62) (hptr : serPtr ≠ 0#64) :
    (((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 (encLen + 1)) ∗
     ((sp0 - 136#64) ↦₆₄ serPtr) ∗
     ((sp0 - 128#64) ↦₆₄ 1#64) ∗
     A.live serPtr (encLen + 1) 1 ∗
     (serPtr ↦₈ versionByte v) ∗
     memRegion (serPtr + 1#64) encLen) =
    vecU8At A (sp0 - 144#64) (BitVec.ofNat 64 (encLen + 1)) serPtr [versionByte v] := by
  have htoNat : (BitVec.ofNat 64 (encLen + 1)).toNat = encLen + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_eq_of_pos A (sp0 - 144#64) (BitVec.ofNat 64 (encLen + 1)) serPtr [versionByte v]
        (by omega)]
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub,
    List.length_singleton, htoNat, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have hsub : encLen + 1 - 1 = encLen := by omega
  have hpure : (1 ≤ encLen + 1 ∧ encLen + 1 < 2 ^ 63 ∧ serPtr ≠ 0#64) = True :=
    eq_true ⟨by omega, by omega, hptr⟩
  rw [hsub, hpure, pure_true, emp_sepConj]

theorem vecU8At_exact_eq_boxU8Buf (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length < 2 ^ 63) :
    vecU8At A a (BitVec.ofNat 64 bs.length) ptr bs =
      ((a ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        boxU8Buf A ptr bs) := by
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hzero_iff : (BitVec.ofNat 64 bs.length = 0) ↔ bs = [] := by
    constructor
    · intro h
      have ht := congrArg BitVec.toNat h
      rw [htoNat] at ht
      exact List.eq_nil_of_length_eq_zero ht
    · rintro rfl; rfl
  by_cases hbs : bs = []
  · subst hbs
    simp [vecU8At, vecHeader, boxU8Buf, sepConj_assoc]
  · have hcap0 : BitVec.ofNat 64 bs.length ≠ 0 := fun h => hbs (hzero_iff.mp h)
    have hpure : (bs.length ≤ bs.length ∧ bs.length < 2 ^ 63 ∧ ptr ≠ 0) =
        (ptr ≠ 0#64 ∧ bs.length < 2 ^ 63) :=
      propext ⟨fun ⟨_, h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨Nat.le_refl _, h1, h2⟩⟩
    simp only [vecU8At, vecHeader, boxU8Buf, hcap0, hbs, ↓reduceIte, htoNat,
      Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp, sepConj_assoc, hpure]

theorem memRegion_16_eq_cells2 (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 8) (by decide) rfl (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]

theorem optVecU8At_none_eq (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    optVecU8At A pin a none =
      (a ↦₆₄ noneCap) ∗ (∃∗ w0 : BitVec 64, (a + 8#64) ↦₆₄ w0) ∗
        (∃∗ w1 : BitVec 64, (a + 16#64) ↦₆₄ w1) := by
  simp only [optVecU8At, memRegion_16_eq_cells2 (a + 8#64)]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_lin
  rw [h16]

theorem optVecU8At_some_exact_eq (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length < 2 ^ 63) :
    optVecU8At A ⟨BitVec.ofNat 64 bs.length, ptr⟩ a (some bs) =
      ((a ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        boxU8Buf A ptr bs) :=
  vecU8At_exact_eq_boxU8Buf A a ptr bs hlen

theorem stackAt_preKeyMsgSubStack_to_publicKeySerialize (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack =
      stackAt sp publicKeySerializeStack ∗ memRegion (sp - 7824#64) 3696 := by
  unfold stackAt preKeyMsgSubStack preKeyMsgNewStack preKeyMsgFrameSize publicKeySerializeStack allocHookStack
  rw [memRegion_split' (b := sp - 7824#64) (b' := sp - 4128#64) (n := 3696) (k := 4128)
    (by decide) (bv_sub_add_lit sp 7824 3696).symm (by decide), sepConj_comm]

theorem stackAt_preKeyMsgSubStack_to_allocHook (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 7824#64) 3728 := by
  unfold stackAt preKeyMsgSubStack preKeyMsgNewStack preKeyMsgFrameSize allocHookStack
  rw [memRegion_split' (b := sp - 7824#64) (b' := sp - 4096#64) (n := 3728) (k := 4096)
    (by decide) (bv_sub_add_lit sp 7824 3728).symm (by decide), sepConj_comm]

theorem stackAt_preKeyMsgSubStack_to_encodedLen (sp : BitVec 64) :
    stackAt sp preKeyMsgSubStack =
      stackAt sp preKeyMsgEncodedLenStack ∗ memRegion (sp - 7824#64) 7808 := by
  unfold stackAt preKeyMsgSubStack preKeyMsgNewStack preKeyMsgFrameSize preKeyMsgEncodedLenStack allocHookStack
  rw [memRegion_split' (b := sp - 7824#64) (b' := sp - 16#64) (n := 7808) (k := 16)
    (by decide) (bv_sub_add_lit sp 7824 7808).symm (by decide), sepConj_comm]

theorem stackAt_preKeyMsgNewStack_split_frame (sp0 : BitVec 64) :
    stackAt sp0 preKeyMsgNewStack =
      stackAt (sp0 - 368#64) preKeyMsgSubStack ∗ memRegion (sp0 - 368#64) 368 := by
  simp only [stackAt, preKeyMsgNewStack, preKeyMsgSubStack, preKeyMsgFrameSize, allocHookStack]
  rw [memRegion_split' (b := sp0 - 8192#64) (b' := sp0 - 368#64) (n := 7824) (k := 368)
    (by decide) (bv_sub_add_lit sp0 8192 7824).symm (by decide)]
  congr 2
  bv_lin

/-! ## Representation Unpack and Pack Helpers -/

theorem boxU8At_eq_words_and_buf (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A a ptr bs =
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ boxU8Buf A ptr bs :=
  rfl

theorem optKyberAt_some_eq (A : RustAlloc) (a ptr : BitVec 64) (k : KyberPayload) :
    optKyberAt A a ptr (some k) =
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        boxU8Buf A ptr k.ciphertext ∗ ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗
        memRegion (a + 0x14#64) 4 := by
  simp only [optKyberAt, boxU8At_eq_words_and_buf, sepConj_assoc]

theorem boxU8Buf_extract_pure (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8Buf A ptr bs ⊢ ⌜ptr ≠ 0#64 ∧ bs.length < 2 ^ 63⌝ ∗ boxU8Buf A ptr bs := by
  unfold boxU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))

def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_eq_ser_and_rest (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 0x28#64) ↦₆₄ g.serPtr) ∗
      ((a + 0x30#64) ↦₆₄ BitVec.ofNat 64 m.serialized.length) ∗
      boxU8Buf A g.serPtr m.serialized ∗
      signalMessageRestAt A g a m := by
  unfold signalMessageAt signalMessageRestAt
  rw [boxU8At_eq_words_and_buf A (a + 0x28#64) g.serPtr m.serialized]
  have h30 : a + 0x28#64 + 8#64 = a + 0x30#64 := by bv_lin
  rw [h30]
  ac_rfl

theorem signalMessageRestAt_extract_ser_bounds (A : RustAlloc) (g : SignalMessageGhost)
    (a : BitVec 64) (m : SignalMessage) :
    signalMessageRestAt A g a m ⊢
      ⌜9 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40⌝ ∗ signalMessageRestAt A g a m := by
  unfold signalMessageRestAt
  refine Entails.pure_left fun hp => ?_
  have h9 : 9 ≤ m.serialized.length := by
    have := hp.1
    change 8 + 1 ≤ m.serialized.length at this
    omega
  exact Entails.pure_right ⟨h9, hp.2.1⟩ (Entails.pure_right hp (Entails.refl _))

def _root_.CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewCall.mkWirePins
    (x : PreKeyMsgNewCall) (kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr : BitVec 64) :
    WirePreKeySignalMessageGhost :=
  { kyberCt := ⟨kyberCap, kyberCopyPtr⟩
    bk := ⟨33#64, bkSerPtr⟩
    ik := ⟨33#64, ikSerPtr⟩
    msg := ⟨BitVec.ofNat 64 x.msg.serialized.length, msgCopyPtr⟩ }

theorem memRegion_8_eq_cells32 (a : BitVec 64) :
    memRegion a 8 =
      (∃∗ w0 : BitVec 32, a ↦₃₂ w0) ∗ (∃∗ w1 : BitVec 32, (a + 4#64) ↦₃₂ w1) := by
  rw [memRegion_split' (b := a) (b' := a + 4#64) (n := 4) (k := 4) (by decide) rfl (by decide),
      ProofLib.memRegion_four a, ProofLib.memRegion_four (a + 4#64)]

theorem memRegion_wire_128 (sp0 : BitVec 64) :
    memRegion (sp0 - 272#64) 128 =
      cells (sp0 - 272#64) 12 ∗
      (∃∗ w0 : BitVec 32, (sp0 - 176#64) ↦₃₂ w0) ∗
      (∃∗ w1 : BitVec 32, (sp0 - 172#64) ↦₃₂ w1) ∗
      (∃∗ w2 : BitVec 32, (sp0 - 168#64) ↦₃₂ w2) ∗
      (∃∗ w3 : BitVec 32, (sp0 - 164#64) ↦₃₂ w3) ∗
      (∃∗ w4 : BitVec 32, (sp0 - 160#64) ↦₃₂ w4) ∗
      (∃∗ w5 : BitVec 32, (sp0 - 156#64) ↦₃₂ w5) ∗
      (∃∗ w6 : BitVec 32, (sp0 - 152#64) ↦₃₂ w6) ∗
      (∃∗ w7 : BitVec 32, (sp0 - 148#64) ↦₃₂ w7) := by
  rw [memRegion_split' (b := sp0 - 272#64) (b' := sp0 - 176#64) (n := 96) (k := 32)
        (by decide) (bv_sub_add_lit sp0 272 96).symm (by decide),
      show (96 : Nat) = 8 * 12 by rfl, ProofLib.memRegion_cells (sp0 - 272#64) 12 (by decide),
      memRegion_split' (b := sp0 - 176#64) (b' := sp0 - 168#64) (n := 8) (k := 24)
        (by decide) (bv_sub_add_lit sp0 176 8).symm (by decide),
      memRegion_split' (b := sp0 - 168#64) (b' := sp0 - 160#64) (n := 8) (k := 16)
        (by decide) (bv_sub_add_lit sp0 168 8).symm (by decide),
      memRegion_split' (b := sp0 - 160#64) (b' := sp0 - 152#64) (n := 8) (k := 8)
        (by decide) (bv_sub_add_lit sp0 160 8).symm (by decide),
      memRegion_8_eq_cells32 (sp0 - 176#64),
      memRegion_8_eq_cells32 (sp0 - 168#64),
      memRegion_8_eq_cells32 (sp0 - 160#64),
      memRegion_8_eq_cells32 (sp0 - 152#64)]
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub]
  ac_rfl

theorem optU32At_of_tag_val (a : BitVec 64) (o : Option (BitVec 32)) (val : BitVec 32)
    (hval : ∀ v, o = some v → val = v) :
    (a ↦₃₂ (if o.isSome then 1#32 else 0#32)) ∗ ((a + 4#64) ↦₃₂ val) ⊢
      LibsignalPublicApiRepr.optU32At a o := by
  cases o with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      LibsignalPublicApiRepr.optU32At, ProofLib.memRegion_four (a + 4#64)]
    exact sepConj_mono_right (Entails.sepExists_intro val)
  | some v =>
    have hv := hval v rfl
    subst hv
    simp only [Option.isSome_some, ↓reduceIte, LibsignalPublicApiRepr.optU32At]
    exact Entails.refl _

theorem optU32At_entails_memRegion_8 (a : BitVec 64) (o : Option (BitVec 32)) :
    LibsignalPublicApiRepr.optU32At a o ⊢ memRegion a 8 := by
  rw [memRegion_8_eq_cells32 a]
  cases o with
  | none =>
    simp only [LibsignalPublicApiRepr.optU32At, ProofLib.memRegion_four (a + 4#64)]
    exact sepConj_mono_left (Entails.sepExists_intro 0#32)
  | some v =>
    simp only [LibsignalPublicApiRepr.optU32At]
    exact sepConj_mono (Entails.sepExists_intro 1#32) (Entails.sepExists_intro v)

theorem optVecU8At_kyber_of_optKyberCopyBuf (A : RustAlloc) (a kyberCap kyberCopyPtr : BitVec 64)
    (kp : Option KyberPayload)
    (hcap : kyberCap = match kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length) :
    (a ↦₆₄ kyberCap) ∗ ((a + 8#64) ↦₆₄ kyberCopyPtr) ∗ ((a + 16#64) ↦₆₄ kyberCap) ∗
      optKyberCopyBuf A kyberCopyPtr kp ⊢
      optVecU8At A ⟨kyberCap, kyberCopyPtr⟩ a (kp.map (·.ciphertext)) := by
  subst hcap
  cases kp with
  | none =>
    simp only [Option.map_none, optKyberCopyBuf, sepConj_emp]
    rw [optVecU8At_none_eq]
    exact sepConj_mono_right
      (sepConj_mono (Entails.sepExists_intro kyberCopyPtr) (Entails.sepExists_intro noneCap))
  | some k =>
    simp only [Option.map_some, optKyberCopyBuf]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (boxU8Buf_extract_pure A kyberCopyPtr k.ciphertext)))) ?_
    have hpull :
        (a ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        ((a + 8#64) ↦₆₄ kyberCopyPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        (⌜kyberCopyPtr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
          boxU8Buf A kyberCopyPtr k.ciphertext) =
        ⌜kyberCopyPtr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 63⌝ ∗
        ((a ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
         ((a + 8#64) ↦₆₄ kyberCopyPtr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
         boxU8Buf A kyberCopyPtr k.ciphertext) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨_, hlen⟩ => ?_
    rw [optVecU8At_some_exact_eq A a kyberCopyPtr k.ciphertext hlen]
    exact Entails.refl _

theorem optVecU8At_kyber_unpack (A : RustAlloc) (a kyberCap kyberCopyPtr : BitVec 64)
    (kp : Option KyberPayload)
    (hcap : kyberCap = match kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hlen : ∀ k, kp = some k → k.ciphertext.length < 2 ^ 63) :
    optVecU8At A ⟨kyberCap, kyberCopyPtr⟩ a (kp.map (·.ciphertext)) ⊢
      memRegion a 24 ∗ optKyberCopyBuf A kyberCopyPtr kp := by
  subst hcap
  cases kp with
  | none =>
    simp only [Option.map_none, optKyberCopyBuf, sepConj_emp, optVecU8At]
    rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by decide) rfl (by decide),
        ProofLib.memRegion_eight a]
    exact sepConj_mono_left (Entails.sepExists_intro noneCap)
  | some k =>
    simp only [Option.map_some, optKyberCopyBuf]
    rw [optVecU8At_some_exact_eq A a kyberCopyPtr k.ciphertext (hlen k rfl)]
    have hassoc :
        (a ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        ((a + 8#64) ↦₆₄ kyberCopyPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        boxU8Buf A kyberCopyPtr k.ciphertext =
        ((a ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
         ((a + 8#64) ↦₆₄ kyberCopyPtr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length)) ∗
        boxU8Buf A kyberCopyPtr k.ciphertext := by ac_rfl
    rw [hassoc, memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by decide) rfl (by decide),
        ProofLib.memRegion_eight a, memRegion_16_eq_cells2 (a + 8#64)]
    have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_lin
    rw [h16]
    exact sepConj_mono_left (sepConj_mono (Entails.sepExists_intro _)
      (sepConj_mono (Entails.sepExists_intro kyberCopyPtr) (Entails.sepExists_intro _)))

theorem optVecU8At_pk_of_boxU8Buf (A : RustAlloc) (a ptr : BitVec 64) (pk : PublicKey) :
    ((a ↦₆₄ 33#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 33#64) ∗
      boxU8Buf A ptr pk.serialize) =
    optVecU8At A ⟨33#64, ptr⟩ a (some pk.serialize) := by
  have hlen : pk.serialize.length = 33 := publicKey_serialize_length pk
  have h := optVecU8At_some_exact_eq A a ptr pk.serialize (by omega)
  rw [hlen] at h
  exact h.symm

theorem optVecU8At_ik_of_boxU8Buf (A : RustAlloc) (a ptr : BitVec 64) (ik : IdentityKey) :
    ((a ↦₆₄ 33#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 33#64) ∗
      boxU8Buf A ptr ik.serialize) =
    optVecU8At A ⟨33#64, ptr⟩ a (some ik.serialize) :=
  optVecU8At_pk_of_boxU8Buf A a ptr ik.publicKey

theorem optVecU8At_some_unpack (A : RustAlloc) (a ptr : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length < 2 ^ 63) :
    optVecU8At A ⟨BitVec.ofNat 64 bs.length, ptr⟩ a (some bs) ⊢
      memRegion a 24 ∗ boxU8Buf A ptr bs := by
  rw [optVecU8At_some_exact_eq A a ptr bs hlen]
  have hassoc :
      (a ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      boxU8Buf A ptr bs =
      ((a ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       ((a + 8#64) ↦₆₄ ptr) ∗
       ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      boxU8Buf A ptr bs := by ac_rfl
  rw [hassoc, memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by decide) rfl (by decide),
      ProofLib.memRegion_eight a, memRegion_16_eq_cells2 (a + 8#64)]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_lin
  rw [h16]
  exact sepConj_mono_left (sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro ptr) (Entails.sepExists_intro _)))

theorem optVecU8At_pk_unpack (A : RustAlloc) (a ptr : BitVec 64) (pk : PublicKey) :
    optVecU8At A ⟨33#64, ptr⟩ a (some pk.serialize) ⊢
      memRegion a 24 ∗ boxU8Buf A ptr pk.serialize := by
  have hlen : pk.serialize.length = 33 := publicKey_serialize_length pk
  have h := optVecU8At_some_unpack A a ptr pk.serialize (by omega)
  rwa [hlen] at h

theorem optVecU8At_ik_unpack (A : RustAlloc) (a ptr : BitVec 64) (ik : IdentityKey) :
    optVecU8At A ⟨33#64, ptr⟩ a (some ik.serialize) ⊢
      memRegion a 24 ∗ boxU8Buf A ptr ik.serialize :=
  optVecU8At_pk_unpack A a ptr ik.publicKey

theorem pack_wirePreKeySignalMessageAt (A : RustAlloc) (x : PreKeyMsgNewCall)
    (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr : BitVec 64)
    (preKeyVal32 kyberId32 : BitVec 32)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hpk : ∀ v, x.preKeyId = some v → preKeyVal32 = v)
    (hkyId : ∀ k, x.kp = some k → kyberId32 = k.preKeyId)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63) :
    (((sp0 - 272#64) ↦₆₄ kyberCap) ∗
     ((sp0 - 264#64) ↦₆₄ kyberCopyPtr) ∗
     ((sp0 - 256#64) ↦₆₄ kyberCap) ∗
     optKyberCopyBuf A kyberCopyPtr x.kp) ∗
    (((sp0 - 248#64) ↦₆₄ 33#64) ∗
     ((sp0 - 240#64) ↦₆₄ bkSerPtr) ∗
     ((sp0 - 232#64) ↦₆₄ 33#64) ∗
     boxU8Buf A bkSerPtr x.baseKey.serialize) ∗
    (((sp0 - 224#64) ↦₆₄ 33#64) ∗
     ((sp0 - 216#64) ↦₆₄ ikSerPtr) ∗
     ((sp0 - 208#64) ↦₆₄ 33#64) ∗
     boxU8Buf A ikSerPtr x.ik.serialize) ∗
    (((sp0 - 200#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
     ((sp0 - 192#64) ↦₆₄ msgCopyPtr) ∗
     ((sp0 - 184#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length) ∗
     boxU8Buf A msgCopyPtr x.msg.serialized) ∗
    (((sp0 - 176#64) ↦₃₂ 1#32) ∗ ((sp0 - 172#64) ↦₃₂ x.regId)) ∗
    (((sp0 - 168#64) ↦₃₂ (if x.preKeyId.isSome then 1#32 else 0#32)) ∗
     ((sp0 - 164#64) ↦₃₂ preKeyVal32)) ∗
    (((sp0 - 160#64) ↦₃₂ 1#32) ∗ ((sp0 - 156#64) ↦₃₂ x.spk)) ∗
    (((sp0 - 152#64) ↦₃₂ (if x.kp.isSome then 1#32 else 0#32)) ∗
     ((sp0 - 148#64) ↦₃₂ kyberId32)) ⊢
    wirePreKeySignalMessageAt A (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
      (sp0 - 272#64) x.protoMsg := by
  have hky := optVecU8At_kyber_of_optKyberCopyBuf A (sp0 - 272#64) kyberCap kyberCopyPtr x.kp hkyCap
  have hbk := optVecU8At_pk_of_boxU8Buf A (sp0 - 248#64) bkSerPtr x.baseKey
  have hik := optVecU8At_ik_of_boxU8Buf A (sp0 - 224#64) ikSerPtr x.ik
  have hmsg := (optVecU8At_some_exact_eq A (sp0 - 200#64) msgCopyPtr x.msg.serialized hmsg_len).symm
  have hpre := optU32At_of_tag_val (sp0 - 168#64) x.preKeyId preKeyVal32 hpk
  have hky_isSome : (x.kp.map (·.preKeyId)).isSome = x.kp.isSome := Option.isSome_map
  have hkyId_opt : ∀ v, x.kp.map (·.preKeyId) = some v → kyberId32 = v := by
    intro v hv
    rcases Option.map_eq_some_iff.mp hv with ⟨k, hk, rfl⟩
    exact hkyId k hk
  have hky_u32 := optU32At_of_tag_val (sp0 - 152#64) (x.kp.map (·.preKeyId)) kyberId32 hkyId_opt
  rw [hky_isSome] at hky_u32
  have hreg : LibsignalPublicApiRepr.optU32At (sp0 - 176#64) (some x.regId) =
      ((sp0 - 176#64) ↦₃₂ 1#32) ∗ ((sp0 - 172#64) ↦₃₂ x.regId) := by
    simp (disch := decide) only [LibsignalPublicApiRepr.optU32At, bv_sub_add_lit, Nat.reduceSub]
  have hspk : LibsignalPublicApiRepr.optU32At (sp0 - 160#64) (some x.spk) =
      ((sp0 - 160#64) ↦₃₂ 1#32) ∗ ((sp0 - 156#64) ↦₃₂ x.spk) := by
    simp (disch := decide) only [LibsignalPublicApiRepr.optU32At, bv_sub_add_lit, Nat.reduceSub]
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub] at hky hbk hik hmsg hpre hky_u32
  simp (disch := decide) only [wirePreKeySignalMessageAt, PreKeyMsgNewCall.mkWirePins,
    PreKeyMsgNewCall.protoMsg, bv_sub_add_lit, Nat.reduceSub]
  rw [hbk, hik, hmsg, hreg, hspk]
  exact sepConj_mono hky (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono hpre (sepConj_mono_right hky_u32))))))

theorem unpack_wirePreKeySignalMessageAt (A : RustAlloc) (x : PreKeyMsgNewCall)
    (sp0 kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr : BitVec 64)
    (hkyCap : kyberCap = match x.kp with | none => noneCap | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hky_len : ∀ k, x.kp = some k → k.ciphertext.length < 2 ^ 63)
    (hmsg_len : x.msg.serialized.length < 2 ^ 63) :
    wirePreKeySignalMessageAt A (x.mkWirePins kyberCap kyberCopyPtr bkSerPtr ikSerPtr msgCopyPtr)
      (sp0 - 272#64) x.protoMsg ⊢
    memRegion (sp0 - 272#64) 128 ∗
    optKyberCopyBuf A kyberCopyPtr x.kp ∗
    boxU8Buf A bkSerPtr x.baseKey.serialize ∗
    boxU8Buf A ikSerPtr x.ik.serialize ∗
    boxU8Buf A msgCopyPtr x.msg.serialized := by
  have hky := optVecU8At_kyber_unpack A (sp0 - 272#64) kyberCap kyberCopyPtr x.kp hkyCap hky_len
  have hbk := optVecU8At_pk_unpack A (sp0 - 248#64) bkSerPtr x.baseKey
  have hik := optVecU8At_ik_unpack A (sp0 - 224#64) ikSerPtr x.ik
  have hmsg := optVecU8At_some_unpack A (sp0 - 200#64) msgCopyPtr x.msg.serialized hmsg_len
  have hu1 := optU32At_entails_memRegion_8 (sp0 - 176#64) (some x.regId)
  have hu2 := optU32At_entails_memRegion_8 (sp0 - 168#64) x.preKeyId
  have hu3 := optU32At_entails_memRegion_8 (sp0 - 160#64) (some x.spk)
  have hu4 := optU32At_entails_memRegion_8 (sp0 - 152#64) (x.kp.map (·.preKeyId))
  simp (disch := decide) only [wirePreKeySignalMessageAt, PreKeyMsgNewCall.mkWirePins,
    PreKeyMsgNewCall.protoMsg, bv_sub_add_lit, Nat.reduceSub]
  refine Entails.trans
    (sepConj_mono hky (sepConj_mono hbk (sepConj_mono hik (sepConj_mono hmsg
      (sepConj_mono hu1 (sepConj_mono hu2 (sepConj_mono hu3 hu4))))))) ?_
  have hm128 :
      memRegion (sp0 - 272#64) 128 =
        memRegion (sp0 - 272#64) 24 ∗
        memRegion (sp0 - 248#64) 24 ∗
        memRegion (sp0 - 224#64) 24 ∗
        memRegion (sp0 - 200#64) 24 ∗
        memRegion (sp0 - 176#64) 8 ∗
        memRegion (sp0 - 168#64) 8 ∗
        memRegion (sp0 - 160#64) 8 ∗
        memRegion (sp0 - 152#64) 8 := by
    rw [memRegion_split' (b := sp0 - 272#64) (b' := sp0 - 248#64) (n := 24) (k := 104)
          (by decide) (bv_sub_add_lit sp0 272 24).symm (by decide),
        memRegion_split' (b := sp0 - 248#64) (b' := sp0 - 224#64) (n := 24) (k := 80)
          (by decide) (bv_sub_add_lit sp0 248 24).symm (by decide),
        memRegion_split' (b := sp0 - 224#64) (b' := sp0 - 200#64) (n := 24) (k := 56)
          (by decide) (bv_sub_add_lit sp0 224 24).symm (by decide),
        memRegion_split' (b := sp0 - 200#64) (b' := sp0 - 176#64) (n := 24) (k := 32)
          (by decide) (bv_sub_add_lit sp0 200 24).symm (by decide),
        memRegion_split' (b := sp0 - 176#64) (b' := sp0 - 168#64) (n := 8) (k := 24)
          (by decide) (bv_sub_add_lit sp0 176 8).symm (by decide),
        memRegion_split' (b := sp0 - 168#64) (b' := sp0 - 160#64) (n := 8) (k := 16)
          (by decide) (bv_sub_add_lit sp0 168 8).symm (by decide),
        memRegion_split' (b := sp0 - 160#64) (b' := sp0 - 152#64) (n := 8) (k := 8)
          (by decide) (bv_sub_add_lit sp0 160 8).symm (by decide)]
  rw [hm128]
  exact Entails.of_eq (by ac_rfl)

theorem word64_and_4_to_word32_and_8 (sp0 w344 : BitVec 64) :
    ((sp0 - 344#64) ↦₆₄ w344) ∗ memRegion (sp0 - 336#64) 4 ⊢
      (∃∗ w : BitVec 32, (sp0 - 344#64) ↦₃₂ w) ∗ memRegion (sp0 - 340#64) 8 := by
  have h8 : ((sp0 - 344#64) ↦₆₄ w344) ⊢ memRegion (sp0 - 344#64) 8 := by
    rw [ProofLib.memRegion_eight (sp0 - 344#64)]
    exact Entails.sepExists_intro w344
  refine Entails.trans (sepConj_mono_left h8) ?_
  rw [memRegion_split' (b := sp0 - 344#64) (b' := sp0 - 340#64) (n := 4) (k := 4)
        (by decide) (bv_sub_add_lit sp0 344 4).symm (by decide),
      ProofLib.memRegion_four (sp0 - 344#64),
      memRegion_split' (N := 8) (b := sp0 - 340#64) (b' := sp0 - 336#64) (n := 4) (k := 4)
        (by decide) (bv_sub_add_lit sp0 340 4).symm (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_preKeyMsgNewStack_ready (sp0 : BitVec 64) :
    stackAt sp0 preKeyMsgNewStack =
      (∃∗ w368 : BitVec 64, ∃∗ w360 : BitVec 64, ∃∗ w352 : BitVec 64, ∃∗ w344 : BitVec 64,
       ∃∗ w332 : BitVec 32, ∃∗ w328 : BitVec 32, ∃∗ w324 : BitVec 32,
       ∃∗ w320 : BitVec 64, ∃∗ w312 : BitVec 64, ∃∗ w304 : BitVec 64,
       ∃∗ w296 : BitVec 32, ∃∗ w292 : BitVec 32,
       ∃∗ w288 : BitVec 64, ∃∗ w280 : BitVec 64,
       ∃∗ w144 : BitVec 64, ∃∗ w136 : BitVec 64, ∃∗ w128 : BitVec 64,
        stackAt (sp0 - 368#64) preKeyMsgSubStack ∗
        ((sp0 - 368#64) ↦₆₄ w368) ∗
        ((sp0 - 360#64) ↦₆₄ w360) ∗
        ((sp0 - 352#64) ↦₆₄ w352) ∗
        ((sp0 - 344#64) ↦₆₄ w344) ∗
        memRegion (sp0 - 336#64) 4 ∗
        ((sp0 - 332#64) ↦₃₂ w332) ∗
        ((sp0 - 328#64) ↦₃₂ w328) ∗
        ((sp0 - 324#64) ↦₃₂ w324) ∗
        ((sp0 - 320#64) ↦₆₄ w320) ∗
        ((sp0 - 312#64) ↦₆₄ w312) ∗
        ((sp0 - 304#64) ↦₆₄ w304) ∗
        ((sp0 - 296#64) ↦₃₂ w296) ∗
        ((sp0 - 292#64) ↦₃₂ w292) ∗
        ((sp0 - 288#64) ↦₆₄ w288) ∗
        ((sp0 - 280#64) ↦₆₄ w280) ∗
        memRegion (sp0 - 272#64) 128 ∗
        ((sp0 - 144#64) ↦₆₄ w144) ∗
        ((sp0 - 136#64) ↦₆₄ w136) ∗
        ((sp0 - 128#64) ↦₆₄ w128) ∗
        memRegion (sp0 - 120#64) 24 ∗
        cells (sp0 - 96#64) 12) := by
  rw [stackAt_preKeyMsgNewStack_split_frame sp0,
      memRegion_split' (b := sp0 - 368#64) (b' := sp0 - 360#64) (n := 8) (k := 360)
        (by decide) (bv_sub_add_lit sp0 368 8).symm (by decide),
      memRegion_split' (b := sp0 - 360#64) (b' := sp0 - 352#64) (n := 8) (k := 352)
        (by decide) (bv_sub_add_lit sp0 360 8).symm (by decide),
      memRegion_split' (b := sp0 - 352#64) (b' := sp0 - 344#64) (n := 8) (k := 344)
        (by decide) (bv_sub_add_lit sp0 352 8).symm (by decide),
      memRegion_split' (b := sp0 - 344#64) (b' := sp0 - 336#64) (n := 8) (k := 336)
        (by decide) (bv_sub_add_lit sp0 344 8).symm (by decide),
      memRegion_split' (b := sp0 - 336#64) (b' := sp0 - 332#64) (n := 4) (k := 332)
        (by decide) (bv_sub_add_lit sp0 336 4).symm (by decide),
      memRegion_split' (b := sp0 - 332#64) (b' := sp0 - 328#64) (n := 4) (k := 328)
        (by decide) (bv_sub_add_lit sp0 332 4).symm (by decide),
      memRegion_split' (b := sp0 - 328#64) (b' := sp0 - 324#64) (n := 4) (k := 324)
        (by decide) (bv_sub_add_lit sp0 328 4).symm (by decide),
      memRegion_split' (b := sp0 - 324#64) (b' := sp0 - 320#64) (n := 4) (k := 320)
        (by decide) (bv_sub_add_lit sp0 324 4).symm (by decide),
      memRegion_split' (b := sp0 - 320#64) (b' := sp0 - 312#64) (n := 8) (k := 312)
        (by decide) (bv_sub_add_lit sp0 320 8).symm (by decide),
      memRegion_split' (b := sp0 - 312#64) (b' := sp0 - 304#64) (n := 8) (k := 304)
        (by decide) (bv_sub_add_lit sp0 312 8).symm (by decide),
      memRegion_split' (b := sp0 - 304#64) (b' := sp0 - 296#64) (n := 8) (k := 296)
        (by decide) (bv_sub_add_lit sp0 304 8).symm (by decide),
      memRegion_split' (b := sp0 - 296#64) (b' := sp0 - 292#64) (n := 4) (k := 292)
        (by decide) (bv_sub_add_lit sp0 296 4).symm (by decide),
      memRegion_split' (b := sp0 - 292#64) (b' := sp0 - 288#64) (n := 4) (k := 288)
        (by decide) (bv_sub_add_lit sp0 292 4).symm (by decide),
      memRegion_split' (b := sp0 - 288#64) (b' := sp0 - 280#64) (n := 8) (k := 280)
        (by decide) (bv_sub_add_lit sp0 288 8).symm (by decide),
      memRegion_split' (b := sp0 - 280#64) (b' := sp0 - 272#64) (n := 8) (k := 272)
        (by decide) (bv_sub_add_lit sp0 280 8).symm (by decide),
      memRegion_split' (b := sp0 - 272#64) (b' := sp0 - 144#64) (n := 128) (k := 144)
        (by decide) (bv_sub_add_lit sp0 272 128).symm (by decide),
      memRegion_split' (b := sp0 - 144#64) (b' := sp0 - 136#64) (n := 8) (k := 136)
        (by decide) (bv_sub_add_lit sp0 144 8).symm (by decide),
      memRegion_split' (b := sp0 - 136#64) (b' := sp0 - 128#64) (n := 8) (k := 128)
        (by decide) (bv_sub_add_lit sp0 136 8).symm (by decide),
      memRegion_split' (b := sp0 - 128#64) (b' := sp0 - 120#64) (n := 8) (k := 120)
        (by decide) (bv_sub_add_lit sp0 128 8).symm (by decide),
      memRegion_split' (b := sp0 - 120#64) (b' := sp0 - 96#64) (n := 24) (k := 96)
        (by decide) (bv_sub_add_lit sp0 120 24).symm (by decide),
      show (96 : Nat) = 8 * 12 by rfl, ProofLib.memRegion_cells (sp0 - 96#64) 12 (by decide),
      ProofLib.memRegion_eight (sp0 - 368#64),
      ProofLib.memRegion_eight (sp0 - 360#64),
      ProofLib.memRegion_eight (sp0 - 352#64),
      ProofLib.memRegion_eight (sp0 - 344#64),
      ProofLib.memRegion_four (sp0 - 332#64),
      ProofLib.memRegion_four (sp0 - 328#64),
      ProofLib.memRegion_four (sp0 - 324#64),
      ProofLib.memRegion_eight (sp0 - 320#64),
      ProofLib.memRegion_eight (sp0 - 312#64),
      ProofLib.memRegion_eight (sp0 - 304#64),
      ProofLib.memRegion_four (sp0 - 296#64),
      ProofLib.memRegion_four (sp0 - 292#64),
      ProofLib.memRegion_eight (sp0 - 288#64),
      ProofLib.memRegion_eight (sp0 - 280#64),
      ProofLib.memRegion_eight (sp0 - 144#64),
      ProofLib.memRegion_eight (sp0 - 136#64),
      ProofLib.memRegion_eight (sp0 - 128#64)]
  simp only [sepExists_sepConj_left]
  simp only [sepExists_sepConj_right]

/-! ## Relocatable Placement Proofs -/

open CryptoVerification.LibsignalPublicApi.Placed

theorem SepWPp.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk) hcl h

theorem preKeyMsg_seq_wpp_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, _hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_seq_wp_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _hoom⟩⟩ := h1.elim hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_shim_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec) :
    subroutine_ok (lsProg_41 H) (lsρ lsRustNoAllocShimSym) noAllocShimSpec :=
  ls_hook_ok_of_mem hshim

theorem preKeyMsg_alloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok (lsProg_41 H) (lsρ lsRustAllocSym) (rustAllocSpec A) :=
  ls_hook_ok_of_mem halloc

theorem preKeyMsg_memcpy_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H "memcpy" framelessMemcpySpec) :
    subroutine_ok (lsProg_41 H) (lsρ "memcpy") framelessMemcpySpec :=
  ls_hook_ok_of_mem hmemcpy

theorem preKeyMsg_publicKeySerialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_41 H) (blkPl_205).base (withLsCl lsmpl (publicKeySerializeSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_41 H)
    (public_key_serialize_placed_ok hshim halloc hpanic)

theorem preKeyMsg_encodedLen_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A H) :
    subroutine_ok (lsProg_41 H) (blkPl_119).base (withLsCl lsmpl (preKeyMsgEncodedLenSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_41 H) hEncLen

theorem preKeyMsg_oom_at_060_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_41).base + 96#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_41 H) ret s P Q (PanicAllocPost s0) := by
  have h_pan : (lsProg_41 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := by
    rw [ls_externAt?_of_mem (prog := lsProg_41 H) (sym := lsHandleErrorSym)]; exact hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem preKeyMsg_oom_at_10c_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_41).base + 268#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_41 H) ret s P Q (PanicAllocPost s0) := by
  have h_pan : (lsProg_41 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := by
    rw [ls_externAt?_of_mem (prog := lsProg_41 H) (sym := lsHandleErrorSym)]; exact hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

theorem preKeyMsg_oom_at_204_placed [LibsignalPlacement] {H : LibsignalHooks}
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_41).base + 516#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_41 H) ret s P Q (PanicAllocPost s0) := by
  have h_pan : (lsProg_41 H).externAt? (lsρ lsHandleErrorSym) = some Rust.panicked := by
    rw [ls_externAt?_of_mem (prog := lsProg_41 H) (sym := lsHandleErrorSym)]; exact hpanic
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  refine SepWPp.panic (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact panicAllocPost_of_eq (allocFailedIn_of_append_one (by simp_all [Rust.panicked, arm64_norm]))

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Prologue
