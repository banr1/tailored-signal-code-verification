/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgLift
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainOkComposePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M6Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Cut-Point Composition Lifting Placed M1–M6 onto `cliProg img ext`

Lifts the placed Block `617` proofs of M1–M6 onto `cliProg img ext` by cutting execution at the
`signal_session::run` entry (`lsmpl.base 579`) and return (`mPcPlaced 0x7a4`), executing `run`
directly on `cliProg img ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace CryptoVerification.SignalSession.Cli.MainHops.MainOkComposeCut

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap Arm64.Process
open CryptoVerification CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.MainHops.M4Placed CryptoVerification.SignalSession.Cli.MainHops.MainOkPlacedHelpers
open CryptoVerification.SignalSession.Cli.MainHops.CliImgPlacement
open CryptoVerification.SignalSession.Cli.MainHops.CliImgLift
open CryptoVerification.SignalSession.Cli.MainHops.CliImgSpecs
open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem sepWPp_mono_both {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp Qp' : State → SepProp → Prop} {oom : State → SepProp}
    (hQ : ∀ sf Pf, Q sf Pf → Q' sf Pf) (hQp : ∀ sf Pf, Qp sf Pf → Qp' sf Pf)
    (h : SepWPp prog ret s P Q Qp oom) : SepWPp prog ret s P Q' Qp' oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hr, Pf, hmf, hq⟩ | ⟨hp, Pf, hmf, hqp⟩ | hoom
  · exact Or.inl ⟨hpc, hr, Pf, hmf, hQ sf Pf hq⟩
  · exact Or.inr (Or.inl ⟨hp, Pf, hmf, hQp sf Pf hqp⟩)
  · exact Or.inr (Or.inr hoom)

private theorem sepWPp_done_at {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) : SepWPp prog ret s P Q Qp oom :=
  fun _ hm _ => ⟨s, Steps.refl _, Or.inl ⟨hpc, hrun, P, hm, hq⟩⟩

theorem main_ok_tight_bridge_of_placed
    {A : RustAlloc} {H : LibsignalHooks} {Y ext : String → Option (State → State)}
    {io : IoModel} {img : Obj.Image} {Run : Inputs → RunAnswer → Prop}
    {stk hookStack resStack : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : ∀ pc,
      (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement H).externAt? pc =
        (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
          (liftHooksToPlaced Y)).externAt? pc)
    (hDom : ∀ n, (Y n).isSome = (Rust.withPanics ext n).isSome)
    (hApp : ∀ n fY s, Y n = some fY → img.CallInv s →
      ∃ fZ, Rust.withPanics ext n = some fZ ∧ fZ s = fY s)
    (hc : @MainCalleesBlk617 (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      A H uuidTryParse hookStack resStack)
    (hio : @MainIoPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
      A H io hookStack)
    (hfacts : MainIoFacts io)
    (hrun : subroutine_ok (mProg img ext) ((mProg img ext).fnAddr runName)
      ((runSpecTight A img uuidTryParse Run
        (fun p => io.pathOk p ∧ p.length < 2 ^ 32) resStack).inImage img))
    (hparse : ∀ i a, Run i a → (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome)
    (hstk : mainFrameSize + max (max extHookStack hookStack) resStack ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok (cliProg img ext) (entryOf img mainName)
      (mainSpecTight A img stk (cliStatics img) Run) := by
  letI : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  letI : LsCodeInv (LibsignalFrozen (imgMultiPlacement img)) := instLsCodeInvFrozen
  have hstk_frame : mainFrameSize ≤ stk := Nat.le_trans (Nat.le_add_right mainFrameSize _) hstk
  apply subroutine_ok_of_sepWPp_init
  intro ⟨i, r⟩ R s0 hpc hrun0 hpre hal
  simp only [mainSpecTight, Spec.inImage, MainEntryFacts, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, ⟨hcase, hok, ⟨hargc, hfs0, htr0⟩, hsp⟩, hm⟩ := hpre
  have hCO0 : LibsignalFrozen (imgMultiPlacement img) s0.mem := img_libsignalFrozen himg hinv0.1
  rw [← cliStaticsPlaced_eq_cliStatics img himg] at hm ⊢
  refine ⟨mainFrame A stk cliStaticsPlaced i s0, by simpa only [mainFrame, sepConj_assoc] using hm, ?_⟩
  apply sepWPp_mainFrame_mainLitsPlaced hCO0.1
  let Q_main : MainResult → State → SepProp → Prop := fun r0 sf Pf =>
    ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (⌜MainPost r0 s0 sf⌝ ∗ stackAt s0.sp stk ∗ anyHeap) ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp_main : MainResult → State → SepProp → Prop := fun r0 sf Pf =>
    (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ (⌜r0 = .abort ∨ allocFailedIn s0 sf⌝ ∗ anyHeap) ∗ R)
  change SepWPp (cliProg img ext) (s0.readReg64 .lr) s0
    (mainFrame A stk (cliStaticsPlaced ∗ mainLitsBlk617) i s0) (Q_main r) (Qp_main r) (mainOom s0)
  have hs0 : AtEntryPlaced (LibsignalFrozen (imgMultiPlacement img)) i s0 :=
    { pc := hpc.trans (mPcPlaced_zero_eq_entryOf himg).symm, run := hrun0, inv := hCO0,
      argc := hargc, spAligned := hal }
  have hpanicA : ∀ r0 (sf : State) (Pf : SepProp), allocFailedIn s0 sf → Qp_main r0 sf Pf :=
    fun _ _ _ ha => panic_of_mem (Or.inr ha)
  have liftFull : ∀ {r0 : MainResult},
      SepWPp (mProgPlaced H) (s0.readReg64 .lr) s0
        (mainFrame A stk (cliStaticsPlaced ∗ mainLitsBlk617) i s0) (Q_main r0) (Qp_main r0) (mainOom s0) →
      SepWPp (cliProg img ext) (s0.readReg64 .lr) s0
        (mainFrame A stk (cliStaticsPlaced ∗ mainLitsBlk617) i s0) (Q_main r0) (Qp_main r0) (mainOom s0) :=
    fun hwp => sepWPp_mono_both (fun _ _ h => h.1) (fun _ _ h => h.1)
      (sepWPp_lift_placed himg hH hDom hApp hinv0 hwp)
  cases hcase with
  | usage hascii hshape =>
    apply liftFull
    have hfail := parseArgs_none_of_shape_proof uuidTryParse hascii hshape
    have hexit2 := exitK_main_tight_placed (CodeOk := LibsignalFrozen (imgMultiPlacement img))
      (H := H) (A := A) (r := .ret 2 [] []) (s0 := s0) (stk := stk) (R := R)
      (G := fun code s => code = 2 ∧ s.trace = s0.trace ∧ s.fs = s0.fs) hstk_frame
      fun code s ⟨hcode, htr_s, hfs_s⟩ sf htr_f hfs_f hx0 =>
        ⟨2, [], [], rfl, hx0.trans (congrArg (BitVec.ofNat 32) hcode),
          congrArg FsState.files (hfs_f.trans hfs_s),
          by rw [htr_f, htr_s, htr0]; exact traceStreamBytes_nil⟩
    refine main_m1_placed_proof hc hstk hstk64 hs0 hok (hpanicA _)
      (fun s code hs ⟨hc2, _, htr_s, hfs_s⟩ => hexit2 s code hs ⟨hc2, htr_s, hfs_s⟩) ?_
    intro s1 buf ps p0 hne hps hs1
    exact main_m2_placed_proof hc hstk hstk64 hok hne hps hs1 (hpanicA _)
      (fun s' code hs' ⟨hc2, _, htr_s, hfs_s⟩ => hexit2 s' code hs' ⟨hc2, htr_s, hfs_s⟩)
      fun _ _ _ hpc_parse _ => nomatch hfail.symm.trans hpc_parse
  | stdinOverCap hover =>
    apply liftFull
    obtain ⟨⟨c0, hparse_c0, htag_c0⟩, hgt_stdin⟩ := hover
    refine main_m1_placed_proof hc hstk hstk64 hs0 hok (hpanicA _)
      (fun _ _ _ ⟨_, hnil, _, _⟩ => by rw [hnil] at hparse_c0; cases hparse_c0) ?_
    intro s1 buf ps p0 hne hps hs1
    refine main_m2_placed_proof hc hstk hstk64 hok hne hps hs1 (hpanicA _)
      (fun _ _ _ ⟨_, hnone, _, _⟩ => by rw [hnone] at hparse_c0; cases hparse_c0) ?_
    intro s2 w c hpc_parse hs2
    cases Option.some.inj (hpc_parse.symm.trans hparse_c0)
    refine main_m3_placed_proof hc hio hstk hstk64 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
      (hfacts.coins i hok) hparse_c0 hs2 (hpanicA _) ?_
      fun _ _ _ _ _ hin_le _ => by simp only [inputOf, htag_c0, ↓reduceIte] at hin_le; omega
    exact exitK_main_tight_placed hstk_frame fun code s' ⟨hcode, hfiles', _, htr'⟩ sf htr_f hfs_f hx0 =>
      ⟨2, [], [], rfl, hx0.trans (congrArg (BitVec.ofNat 32) hcode),
        by rw [hfs_f, hfiles', hfs0]; rfl,
        by rw [htr_f, htr', hs2.trace, htr0]; exact traceStreamBytes_nil⟩
  | sendOverCap hover hnstin hcr =>
    apply liftFull
    obtain ⟨⟨peer, hparse_send⟩, hlen_gt⟩ := hover
    refine main_m1_placed_proof hc hstk hstk64 hs0 hok (hpanicA _)
      (fun _ _ _ ⟨_, hnil, _, _⟩ => by rw [hnil] at hparse_send; cases hparse_send) ?_
    intro s1 buf ps p0 hne hps hs1
    refine main_m2_placed_proof hc hstk hstk64 hok hne hps hs1 (hpanicA _)
      (fun _ _ _ ⟨_, hnone, _, _⟩ => by rw [hnone] at hparse_send; cases hparse_send) ?_
    intro s2 w c hpc_parse hs2
    cases Option.some.inj (hpc_parse.symm.trans hparse_send)
    refine main_m3_placed_proof hc hio hstk hstk64 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
      (hfacts.coins i hok) hparse_send hs2 (hpanicA _)
      (fun _ _ _ ⟨_, _, hex_or, _⟩ => hex_or.elim (absurd hcr) fun ⟨htag, hgt⟩ =>
        absurd ⟨⟨.send peer, hparse_send, htag⟩, hgt⟩ hnstin) ?_
    intro s3 coinsCap coinsPtr inCap inPtr _ hs3
    refine main_m4_sendOverCap_placed_proof hc hstk hstk64 hsp htr0 hparse_send hlen_gt hs3 (hpanicA _) ?_
    exact exitK_main_tight_placed hstk_frame fun code s' ⟨hcode, hfiles', htr'⟩ sf htr_f hfs_f hx0 =>
      ⟨1, [], [], rfl, hx0.trans (congrArg (BitVec.ofNat 32) hcode),
        by rw [hfs_f, hfiles', hfs0]; rfl,
        by rw [htr_f, htr', hs3.trace, htr0]; exact traceStreamBytes_nil⟩
  | @call a hRun hnover hnstin hcr hco =>
    let wrOk : List (BitVec 8) → Prop := fun p => io.pathOk p ∧ p.length < 2 ^ 32
    let fsp := s0.sp - BitVec.ofNat 64 mainFrameSize
    have hsome : (parseArgs uuidTryParse (i.argv.map bytesOfString)).isSome := hparse i a hRun
    let Q_mid : State → SepProp → Prop := fun s3 P3 =>
      ∃ (w : CallW) (c : CallV) (buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8)))
        (s_m4 : State) (coinsCap coinsPtr inCap inPtr : BitVec 64),
        parseArgs uuidTryParse (i.argv.map bytesOfString) = some c ∧
        AtM4Placed (LibsignalFrozen (imgMultiPlacement img)) i s0 s_m4 w c i.argv.length buf
          coinsCap coinsPtr inCap ∧
        AtM4RunCallPlaced (LibsignalFrozen (imgMultiPlacement img)) s0 s3 i.argv.length buf
          inCap inPtr (inputOf i c).length ∧
        s3.sp = fsp ∧ s3.trace = s_m4.trace ∧ s3.trace = s0.trace ∧ s3.fs = s_m4.fs ∧
        P3 = (runSpecPlaced (LibsignalFrozen (imgMultiPlacement img)) A uuidTryParse Run wrOk
            resStack).pre
            { i := i, c := c, a := a, res := fsp + 0x1b8#64, call := fsp + 0x78#64,
              stores := fsp + 0x310#64, inp := inPtr, coins := coinsPtr } s3 ∗
          (m4RestFramePlaced fsp w ∗ ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
            ownedBytesRest A inCap inPtr (inputOf i c) ∗
            argsBuf A (BitVec.ofNat 64 i.argv.length) buf ps ∗ mainSaved s0 ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - mainFrameSize))
              (stk - mainFrameSize - resStack) ∗ anyHeap)
    have hsegA_placed : SepWPp (mProgPlaced H) (lsmpl.base 579) s0
        (mainFrame A stk (cliStaticsPlaced ∗ mainLitsBlk617) i s0)
        Q_mid (Qp_main (MainResult.ofAnswer a)) (mainOom s0) := by
      refine main_m1_placed_proof hc hstk hstk64 hs0 hok (hpanicA _)
        (fun _ _ _ ⟨_, hnil, _, _⟩ => by rw [hnil] at hsome; cases hsome) ?_
      intro s1 buf ps p0 hne hps hs1
      refine main_m2_placed_proof hc hstk hstk64 hok hne hps hs1 (hpanicA _)
        (fun _ _ _ ⟨_, hnone, _, _⟩ => by rw [hnone] at hsome; cases hsome) ?_
      intro s2 w c hpc_parse hs2
      refine main_m3_placed_proof hc hio hstk hstk64 hfs0 htr0 (hfacts.stdin i hok) hfacts.coinsPath
        (hfacts.coins i hok) hpc_parse hs2 (hpanicA _)
        (fun _ _ _ ⟨_, _, hex_or, _⟩ => hex_or.elim (absurd hcr) fun ⟨htag, hgt⟩ =>
          absurd ⟨⟨c, hpc_parse, htag⟩, hgt⟩ hnstin) ?_
      intro s_m4 coinsCap coinsPtr inCap inPtr _ hs_m4
      refine m4_to_run_call_placed (hookStack := hookStack) (wrOk := wrOk) hstk hsp htr0 hRun
        (fun peer hc_eq => Nat.le_of_not_lt fun hgt => hnover ⟨⟨peer, hc_eq ▸ hpc_parse⟩, hgt⟩)
        hpc_parse hs_m4 fun s3 hs3 hsp3 htr3_s htr3_0 hfs3_s =>
        sepWPp_done_at hs3.pc hs3.run
          ⟨w, c, buf, ps, s_m4, coinsCap, coinsPtr, inCap, inPtr,
            hpc_parse, hs_m4, hs3, hsp3, htr3_s, htr3_0, hfs3_s, rfl⟩
    have hsegA_cli := sepWPp_mono_both (fun _ _ h => h) (fun _ _ h => h.1)
      (sepWPp_lift_placed himg hH hDom hApp hinv0 hsegA_placed)
    refine sepWPp_bind_running hsegA_cli fun s3 P3 _ _ ⟨hq_mid, hinv3⟩ => ?_
    rcases hq_mid with ⟨w, c, buf, ps, s_m4, coinsCap, coinsPtr, inCap, inPtr,
      hpc_parse, hs_m4, hs3, hsp3, htr3_s, htr3_0, hfs3_s, rfl⟩
    refine call_run_on_cliProg himg hrun hs3 htr3_0 hinv3
      (fun sf Pf hpan => hpan.elim (fun ha => by subst ha; exact panic_of_mem (Or.inl rfl))
        fun ha => panic_of_mem (Or.inr ha)) ?_
    intro sf hinv_f hCO_f hpcm hrunm hspm hcsm
    refine sepWPp_mono_both (fun _ _ h => h.1) (fun _ _ h => h.1)
      (sepWPp_lift_placed himg hH hDom hApp hinv_f ?_)
    exact m4_after_run_placed (Run := Run) (wrOk := wrOk) (coinsPtr := coinsPtr)
      hc hstk hstk64 htr0 hs_m4 hs3 hsp3 htr3_s htr3_0 hfs3_s hCO_f hpcm hrunm hspm hcsm
      (exitK_main_tight_placed hstk_frame fun code s' ⟨hcode, ha_eq, ⟨hfiles', hstdout'⟩, _⟩
        sf' htr_f hfs_f hx0 => by
        subst ha_eq
        exact ⟨1, [], [], rfl, hx0.trans (congrArg (BitVec.ofNat 32) hcode),
          by rw [hfs_f, hfiles', hfs0]; rfl, by rw [htr_f, hstdout']⟩)
      fun s4 g out hans hwr _ hs4 => by
        subst hans
        refine main_m5_proof_placed hc hio hstk hstk64 htr0 hwr hs4.toAtM4EndPlaced (hpanicA _) ?_
        intro s5 ok outCap outPtr hcommit htr45 hstdout5 hs5
        refine main_m6_proof_placed hc hio hstk hstk64 hs5 ?_
        refine exitK_main_tight_placed hstk_frame fun code s6 ⟨hfiles6, hbr6⟩ sf' htr_f hfs_f hx0 => ?_
        rcases hs4.hist with ⟨hfiles4, hstdout4⟩
        have hcf := hfacts.commit i hok g.writes (fun pw hpw => (hwr pw hpw).1) hco
        rw [hfiles4, hcf] at hcommit
        obtain ⟨rfl, hfiles5⟩ := hcommit
        obtain ⟨hcode, _, hstdout6⟩ := hbr6
        exact ⟨0, namedWrites g.writes, out, rfl,
          hx0.trans (congrArg (BitVec.ofNat 32) hcode),
          by rw [hfs_f, hfiles6, hfiles5, hfs0],
          by rw [htr_f, hstdout6, hstdout5, hstdout4, List.nil_append]⟩

end CryptoVerification.SignalSession.Cli.MainHops.MainOkComposeCut
