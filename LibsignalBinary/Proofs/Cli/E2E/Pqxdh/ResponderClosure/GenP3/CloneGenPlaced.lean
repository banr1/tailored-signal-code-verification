/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed End-to-End Composition

Assembles all five placed segments into `cloneGen_vregs_placed_ok : CloneGenVRegsPlacedStmt`
(`+0x1778 → +0x1cd4 / +0x1e04`, `genP3PrePlaced → genP3PostPlaced`) on `lsProg_518 ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem sepWPp_weaken_post_gen_placed {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp)
    (himp : ∀ s1 P_f, Q s1 P_f → Q' s1 P_f) :
    SepWPp prog ret s P Q' Qp := by
  intro R hm hne
  obtain ⟨sf, hsteps, hpost⟩ := h R hm hne
  refine ⟨sf, hsteps, ?_⟩
  rcases hpost with ⟨hpc, hrun, P_f, hm', hQ⟩ | hp
  · exact Or.inl ⟨hpc, hrun, P_f, hm', himp sf P_f hQ⟩
  · exact Or.inr hp

set_option maxHeartbeats 400000 in
/-- Unconditional `[LibsignalPlacement]` `CloneGenVRegsPlacedStmt` on `lsProg_518 ext`. -/
theorem cloneGen_vregs_placed_ok [LibsignalPlacement] : CloneGenVRegsPlacedStmt := by
  intro A ext hshim halloc hmemcpy hpanic hcc hscc
    s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg
    hrc hsp_align hsp_root hcro hpc hrun htr
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysFront_vregs_placed_ok ext hshim halloc hmemcpy hpanic hscc
      s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg hrc hsp_align hsp_root hcro hpc hrun htr)
    (by simp) fun s1 P1 hpc1 hrun1 ⟨hent1, htr1, hcro1, hvregs1⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent1) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneChains_vregs_placed_ok ext hshim halloc hpanic hcc
      s0 s1 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg hrc hsp_align hsp_root hcro1 hpc1 hrun1 htr1)
    (by simp) fun s2 P2 hpc2 hrun2 ⟨hent2, htr2, hcro2, hvregs2⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent2) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (clonePending_vregs_placed_ok ext hpanic hshim halloc hmemcpy
      s0 s2 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg hrc hsp_align hsp_root hcro2 hpc2 hrun2 htr2)
    (by simp) fun s3 P3 hpc3 hrun3 ⟨hent3, htr3, hcro3, hvregs3⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent3) ?_
  refine SepWPp.bind_oom_frame (F := emp)
    (cloneKeysTail_vregs_placed_ok ext hpanic hshim halloc hmemcpy
      s0 s3 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg hrc hsp_align hsp_root hcro3 hpc3 hrun3 htr3)
    (by simp) fun s4 P4 hpc4 hrun4 ⟨hent4, htr4, hcro4, hvregs4⟩ => ?_
  refine SepWPp.weaken_pre (by simp only [sepConj_emp]; exact hent4) ?_
  refine sepWPp_weaken_post_gen_placed
    (clonePack_vregs_placed_ok ext
      s0 s4 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      recG st rem loc msgG msg hrc hsp_align hsp_root hcro4 hpc4 hrun4 htr4)
    fun _ _ ⟨hent5, htr5, hcro5, hvregs5⟩ =>
      ⟨hent5, htr5, hcro5,
       hvregs5.trans (hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1)))⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
