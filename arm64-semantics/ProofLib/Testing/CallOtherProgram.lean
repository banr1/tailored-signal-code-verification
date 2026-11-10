/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WPFrozen
public import ProofLib.Hoare.SubroutineHook

/-!
# Calls Into Code Verified Over Another `Program`

Regression tests for cross-program subroutine calls and `CodeLoaded` threading
(`Steps.of_sameHooks`, `SepWP.call_subroutine_frame_other`, `SepWP.mono_frozen`,
`subroutineHook_ok_codeLoadedSubroutineHook`, `SepWP.seq_codeLoaded`, and
`SepWP.mono_codeLoaded`), including negative `#guard_msgs` checks on mismatched `CodeLoaded`
witnesses and `svc` handlers.
-/

@[expose] public section

namespace Testing.CallOtherProgram

open Arm64 ProofLib

def bumpSpec : Spec (BitVec 64 × BitVec 64) where
  pre := fun (p, v) s => ⌜s.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v)
  post := fun (p, v) _ _ => (p ↦₆₄ (v + 1#64))

def alphaProg : Program := { base := 0x1000#64, code := List.replicate 8 0#8, svc := noSyscalls }
def widgetProg : Program := { base := 0x8000#64, code := List.replicate 8 0#8, svc := noSyscalls }
def widgetStdProg : Program := { base := 0x8000#64, code := List.replicate 8 0#8 }

example {s sf : State} (h : Steps widgetProg s sf) : Steps alphaProg s sf :=
  Steps.of_sameHooks (P := alphaProg) (Q := widgetProg) (fun _ => rfl) rfl h

/-- Framed call from `P` into a contract proved over `Q`, threading `Q.CodeLoaded` to the
    continuation and framing `q ↦₆₄ w`. -/
theorem call_other_ok {P Q : Program} {entry target ret : BitVec 64}
    {post : State → SepProp → Prop}
    (hcall : subroutine_ok Q entry bumpSpec)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    (s : State) (p q v w : BitVec 64)
    (hQL : Q.CodeLoaded s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) (hx0 : s.readReg64 .x0 = p)
    (hk : ∀ sf, sf.pc = ret → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      Q.CodeLoaded sf.mem →
      SepWP P target sf ((p ↦₆₄ (v + 1#64)) ∗ (q ↦₆₄ w)) post) :
    SepWP P target s ((p ↦₆₄ v) ∗ (q ↦₆₄ w)) post := by
  refine SepWP.call_subroutine_frame_other hcall hext hsvc (x := (p, v)) (F := (q ↦₆₄ w))
    hQL hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R hm
    dsimp only [bumpSpec]
    rw [sepConj_assoc] at hm
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, hm⟩
  · intro R' sf _ hpan
    exact not_satisfies_false_sepConj hpan
  · intro R' code sf _ hexit
    exact not_satisfies_false_sepConj hexit
  · intro sf h1 h2 h3 h4 hQL'
    exact hk sf h1 h2 h3 h4 hQL'

example {P Q : Program} {target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} (hQL : Q.CodeLoaded s.mem)
    (h : SepWP P target s Pre post) :
    SepWP P target s Pre (fun sf Pf => post sf Pf ∧ Q.CodeLoaded sf.mem) :=
  SepWP.mono_frozen (Φ := Q.CodeLoaded) (fun _ _ h hkf => h.of_keepsFrozen hkf) hQL h
    (fun _ _ _ _ hQ hp => ⟨hp, hQ⟩)

-- Caller `P.CodeLoaded` cannot substitute for callee `Q.CodeLoaded`.
/--
error: Application type mismatch: The argument
  hPL
has type
  P.CodeLoaded s.mem
but is expected to have type
  Q.CodeLoaded s.mem
-/
#guard_msgs (error, drop info, substring := true) in
example {P Q : Program} {entry target ret : BitVec 64} {post : State → SepProp → Prop}
    (hcall : subroutine_ok Q entry bumpSpec)
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    (s : State) (p v : BitVec 64)
    (hPL : P.CodeLoaded s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret) :
    SepWP P target s (p ↦₆₄ v) post :=
  SepWP.call_subroutine_frame_other hcall hext hsvc (x := (p, v)) (F := emp)
    hPL hpc hrun halign hlr _ _ _ _

-- Negative: `Steps.of_sameHooks` needs equal `svc` handlers.
/--
but is expected to have type
  widgetStdProg.svc = alphaProg.svc
-/
#guard_msgs (error, drop info, substring := true) in
example {s sf : State} (h : Steps widgetStdProg s sf) : Steps alphaProg s sf :=
  Steps.of_sameHooks (P := alphaProg) (Q := widgetStdProg) (fun _ => rfl) rfl h

/-! ## `subroutineHook_ok_of_codeLoaded` and `Spec.codeLoadedSubroutineHook` -/

/-- Callee contract retaining a read-only `.rodata` cell `r ↦₆₄ᵣ c` (`SepProp.NoRO` fails). -/
def roBumpSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (p, v, r, c) s => ⌜s.readReg64 .x0 = p⌝ ∗ (p ↦₆₄ v) ∗ (r ↦₆₄ᵣ c)
  post := fun (p, v, r, c) _ _ => (p ↦₆₄ (v + c)) ∗ (r ↦₆₄ᵣ c)

theorem roBump_hook_ok {Q : Program} (name : String)
    (hext : Q.externAt? (Q.base + 1#64) = none)
    (hsub : subroutine_ok Q (Q.fnAddr name) roBumpSpec) :
    HookOk (subroutineHook Q (Q.fnAddr name))
      (Spec.codeLoadedSubroutineHook Q name roBumpSpec) :=
  subroutineHook_ok_codeLoadedSubroutineHook name hext hsub

example {P Q : Program} {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hQL : Q.CodeLoaded s.mem)
    (h1 : SepWP P mid s Pre (fun sm Pm =>
      Q.CodeLoaded sm.mem → SepWP P target sm Pm post)) :
    SepWP P target s Pre (fun sf Pf => post sf Pf ∧ Q.CodeLoaded sf.mem) :=
  SepWP.mono_codeLoaded hQL (SepWP.seq_codeLoaded hQL h1)
    (fun _ _ _ _ hQ hp => ⟨hp, hQ⟩)

-- `SepWP.mono_codeLoaded` requires `calleeProg.CodeLoaded s.mem`, not `P.CodeLoaded s.mem`.
/--
error: Application type mismatch: The argument
  hPL
has type
  P.CodeLoaded s.mem
but is expected to have type
  Q.CodeLoaded s.mem
-/
#guard_msgs (error, drop info, substring := true) in
example {P Q : Program} {target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} (hPL : P.CodeLoaded s.mem)
    (h : SepWP P target s Pre post) :
    SepWP P target s Pre (fun sf Pf => post sf Pf ∧ Q.CodeLoaded sf.mem) :=
  SepWP.mono_codeLoaded (calleeProg := Q) hPL h (fun _ _ _ _ hQ hp => ⟨hp, hQ⟩)

end Testing.CallOtherProgram
