/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RetPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Parse-Failure Composition for `main` (Block `617`)

Composes the relocatable contracts for `main_m1`, `main_m2`, and `main_ret` on inputs where
`parseArgs` returns `none`, yielding `exit 2` with unchanged files and trace.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem sepWPp_mono_post_placed {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf)
    (h : ProofLib.SepWPp prog ret s P Q Qp oom) :
    ProofLib.SepWPp prog ret s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, Pf, hmf, hq⟩ | hpan | hoom
  · exact Or.inl ⟨hpc, hrun, Pf, hmf, hQ sf Pf hq⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

/-- Pure composition of the `main_m1`, `main_m2`, and `main_ret` placed hop contracts on inputs
where `parseArgs` returns `none`. -/
theorem main_parseFail_placed_of_hops [LibsignalPlacement] {CodeOk : Memory → Prop}
    {H : LibsignalHooks} {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 : State}
    {stk hookStack resStack : Nat} {Statics : SepProp} {Qp : State → SepProp → Prop}
    (hm1 : ∀ {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 : State}
      {stk hookStack resStack : Nat} {Statics : SepProp} {Q Qp : State → SepProp → Prop},
      MainCalleesBlk617 A H uuidParse hookStack resStack →
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      AtEntryPlaced CodeOk i s0 →
      CliInputsOk i →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s => code = 2 ∧ i.argv = [] ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp →
      (∀ (s : State) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) (p0 : BitVec 64),
        i.argv ≠ [] → ps.map (·.2) = i.argv.map bytesOfString →
        AtM1EndPlaced CodeOk s0 s i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
          (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (mainFrame A stk Statics i s0)
        Q Qp (mainOom s0))
    (hm2 : ∀ {A : RustAlloc} {uuidParse : UuidParser} {i : Inputs} {s0 s : State}
      {stk hookStack resStack : Nat} {buf p0 : BitVec 64}
      {ps : List (BitVec 64 × List (BitVec 8))}
      {Statics : SepProp} {Q Qp : State → SepProp → Prop},
      MainCalleesBlk617 A H uuidParse hookStack resStack →
      mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk →
      stk ≤ 2 ^ 63 →
      CliInputsOk i → i.argv ≠ [] →
      ps.map (·.2) = i.argv.map bytesOfString →
      AtM1EndPlaced CodeOk s0 s i.argv.length buf →
      (∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) →
      ExitKPlaced CodeOk H A s0 stk
        (fun code s' => code = 2 ∧ parseArgs uuidParse (i.argv.map bytesOfString) = none ∧
          s'.trace = s0.trace ∧ s'.fs = s0.fs) Q Qp →
      (∀ (s' : State) (w : CallW) (c : CallV),
        parseArgs uuidParse (i.argv.map bytesOfString) = some c →
        AtCallPlaced CodeOk s0 s' w i.argv.length buf →
        ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s'
          (callHeap A w c ∗ argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
            argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
            mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize)
              (callCellsPlaced (s0.sp - BitVec.ofNat 64 mainFrameSize) w) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
            A.pool ∗ Statics)
          Q Qp (mainOom s0)) →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s
        (argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗
          argvAtP (s0.readReg64 .x1) ((p0, bytesOfString "libsignal-cli") :: ps) ∗
          mainSaved s0 ∗ locals (s0.sp - BitVec.ofNat 64 mainFrameSize) [] ∗
          stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
          A.pool ∗ Statics)
        Q Qp (mainOom s0))
    (hret : ∀ {A : RustAlloc} {s0 s : State} {stk code : Nat} {Qp : State → SepProp → Prop},
      mainFrameSize ≤ stk → AtRetPlaced CodeOk s0 s code →
      ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s (retMem A s0 stk)
        (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 code ∧ sf.trace = s.trace ∧
          sf.fs = s.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap))
        Qp (mainOom s0))
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0) (hok : CliInputsOk i)
    (hfail : parseArgs uuidParse (i.argv.map bytesOfString) = none)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (mainFrame A stk Statics i s0)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
        sf.fs = s0.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap))
      Qp (mainOom s0) := by
  let Q : State → SepProp → Prop :=
    fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
      sf.fs = s0.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap)
  have hstk_ret : mainFrameSize ≤ stk :=
    Nat.le_trans (Nat.le_add_right mainFrameSize _) hstk
  have hexit : ExitKPlaced CodeOk H A s0 stk
      (fun code s => code = 2 ∧ s.trace = s0.trace ∧ s.fs = s0.fs) Q Qp :=
    fun s code hs ⟨hcode, htr, hfs⟩ =>
      sepWPp_mono_post_placed
        (fun _ _ ⟨hsp, hcs, hx0, htr_f, hfs_f, hmem⟩ =>
          ⟨hsp, hcs, hx0.trans (congrArg (BitVec.ofNat 32) hcode),
            htr_f.trans htr, hfs_f.trans hfs, hmem⟩)
        (hret hstk_ret hs)
  exact hm1 hc hstk hstk64 hs0 hok hpanic
    (fun s code hs ⟨hcode, _, htr, hfs⟩ => hexit s code hs ⟨hcode, htr, hfs⟩)
    (fun s buf ps p0 hne hps hs1 =>
      hm2 (p0 := p0) hc hstk hstk64 hok hne hps hs1 hpanic
        (fun s' code hs' ⟨hcode, _, htr, hfs⟩ => hexit s' code hs' ⟨hcode, htr, hfs⟩)
        (fun _ _ _ hparse _ => (nomatch hfail.symm.trans hparse)))

theorem main_parseFail_placed_proof [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks} {A : RustAlloc}
    {uuidParse : UuidParser} {i : Inputs} {s0 : State} {stk hookStack resStack : Nat}
    {Statics : SepProp} {Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs0 : AtEntryPlaced CodeOk i s0) (hok : CliInputsOk i)
    (hfail : parseArgs uuidParse (i.argv.map bytesOfString) = none)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf) :
    ProofLib.SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0 (mainFrame A stk Statics i s0)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 2 ∧ sf.trace = s0.trace ∧
        sf.fs = s0.fs ∧ (Pf ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap))
      Qp (mainOom s0) :=
  main_parseFail_placed_of_hops (fun hc => main_m1_placed_proof hc) (fun hc => main_m2_placed_proof hc)
    (fun hstk_ret hs => main_ret_placed_proof hstk_ret hs) hc hstk hstk64 hs0 hok hfail hpanic

end CryptoVerification.SignalSession.Cli.MainHops
