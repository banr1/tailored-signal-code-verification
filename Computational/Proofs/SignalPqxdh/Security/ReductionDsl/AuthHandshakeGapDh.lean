/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCr

/-!
# `ReductionDsl` Program for the `Auth` Fiedler–Günther `GapDH` Reduction

Defines `fgAuthGapDhProg`, the `ReductionDsl` witness for the `Auth` Fiedler–Günther `GapDH`
reduction (`fgAuthGapDhAdv4`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

def Comp.queryDdh {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) : Comp pqxdhOps pqGapDhIface Γ .bool :=
  Comp.queryChal (C := gapDhDdhOracle) () e

/-- Effective `N_send_opk` multiplier (`0` when `N_id = 0`, `N_send_opk` otherwise). -/
def nSendOpkEff (S : Setup) : Nat :=
  if S.N_id = 0 then 0 else S.N_send_opk

/-- Effective `N_send_no_opk` multiplier (`0` when `N_id = 0`, `N_send_no_opk` otherwise). -/
def nSendNoOpkEff (S : Setup) : Nat :=
  if S.N_id = 0 then 0 else S.N_send_no_opk

/-! ## Types, Accessors, and Helpers -/

abbrev rootEntryTy : Ty pqSig := .prod (B 32) (.prod fgPosTy (.prod (B 32) (B 32)))
abbrev respRecTy : Ty pqSig := .prod (.prod .nat .nat) (.prod (B 32) (B 32))
/-- `FgAuthSimState` tuple encoding `(base, fgL, fgRootL, rawRoCache, advRoLog, respRecs, advKeyPows)`. -/
abbrev fgSimTy : Ty pqSig :=
  .prod authStateTy (.prod (.list fgPatchEntryTy) (.prod (.list rootEntryTy)
    (.prod (.list (.prod (B 192) drKeyTy)) (.prod (.list (B 192)) (.prod (.list respRecTy)
      (.list (.prod (B 32) (B 32))))))))
abbrev paramsTy : Ty pqSig := .prod (B 32) (.prod (B 32) (.prod .bool (.prod .nat .nat)))
abbrev gsTy : Ty pqSig := .prod paramsTy fgSimTy
/-- Tuple-keyed immutable parameters `(U, V, useDh1, targetPrinIdx, sendIsOpk, sendSubIdx, targetSpkPair?)`. -/
abbrev fg2ParamsTy : Ty pqSig :=
  .prod (B 32) (.prod (B 32) (.prod .bool (.prod .nat (.prod .bool (.prod .nat (.opt (.prod .nat .nat)))))))
abbrev fg2GsTy : Ty pqSig := .prod fg2ParamsTy fgSimTy
abbrev patchKeyTy : Ty pqSig :=
  .prod fgPosTy (.prod fgPosTy (.prod fgPosTy (.prod (.opt fgPosTy) (B 32))))
abbrev RSF : Ty pqSig := .prod authRespTy fgSimTy
abbrev quadTy : Ty pqSig := .prod (B 32) (.prod (B 32) (.prod (B 32) (B 32)))

abbrev CG := Comp pqxdhOps pqGapDhIface

@[reducible] def fsBase {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy) :
    Expr pqxdhOps Γ authStateTy := .fst e
@[reducible] def fsL {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy) :
    Expr pqxdhOps Γ (.list fgPatchEntryTy) := .fst (.snd e)
@[reducible] def fsRootL {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy) :
    Expr pqxdhOps Γ (.list rootEntryTy) := .fst (.snd (.snd e))
@[reducible] def fsRaw {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy) :
    Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) := .fst (.snd (.snd (.snd e)))
@[reducible] def fsLog {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy) :
    Expr pqxdhOps Γ (.list (B 192)) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def fsResp {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy) :
    Expr pqxdhOps Γ (.list respRecTy) := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def fsPows {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy) :
    Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) := .snd (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def fsMk {Γ : List (Ty pqSig)} (base : Expr pqxdhOps Γ authStateTy)
    (fgL : Expr pqxdhOps Γ (.list fgPatchEntryTy)) (rootL : Expr pqxdhOps Γ (.list rootEntryTy))
    (raw : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy))) (log : Expr pqxdhOps Γ (.list (B 192)))
    (resp : Expr pqxdhOps Γ (.list respRecTy))
    (pows : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32)))) : Expr pqxdhOps Γ fgSimTy :=
  .pair base (.pair fgL (.pair rootL (.pair raw (.pair log (.pair resp pows)))))
@[reducible] def fsUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgSimTy)
    (base : Expr pqxdhOps Γ authStateTy := fsBase e)
    (fgL : Expr pqxdhOps Γ (.list fgPatchEntryTy) := fsL e)
    (rootL : Expr pqxdhOps Γ (.list rootEntryTy) := fsRootL e)
    (raw : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) := fsRaw e)
    (log : Expr pqxdhOps Γ (.list (B 192)) := fsLog e)
    (resp : Expr pqxdhOps Γ (.list respRecTy) := fsResp e)
    (pows : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32))) := fsPows e) : Expr pqxdhOps Γ fgSimTy :=
  fsMk base fgL rootL raw log resp pows

@[reducible] def paU {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ paramsTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def paV {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ paramsTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def paDh1 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ paramsTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd e))
@[reducible] def paTI {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ paramsTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd (.snd (.snd e)))
@[reducible] def paTS {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ paramsTy) :
    Expr pqxdhOps Γ .nat := .snd (.snd (.snd (.snd e)))
@[reducible] def paTSPair {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ paramsTy) :
    Expr pqxdhOps Γ (.prod .nat .nat) := .snd (.snd (.snd e))

@[reducible] def fg2PaU {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fg2ParamsTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def fg2PaV {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fg2ParamsTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def fg2PaDh1 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fg2ParamsTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd e))
@[reducible] def fg2PaTI {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fg2ParamsTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd (.snd (.snd e)))
@[reducible] def fg2PaSendOpk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fg2ParamsTy) :
    Expr pqxdhOps Γ .bool := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def fg2PaSendIdx {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fg2ParamsTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def fg2PaTS {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fg2ParamsTy) :
    Expr pqxdhOps Γ (.opt (.prod .nat .nat)) := .snd (.snd (.snd (.snd (.snd (.snd e)))))

@[reducible] def feP1 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    Expr pqxdhOps Γ fgPosTy := .fst e
@[reducible] def feP2 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    Expr pqxdhOps Γ fgPosTy := .fst (.snd e)
@[reducible] def feP3 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    Expr pqxdhOps Γ fgPosTy := .fst (.snd (.snd e))
@[reducible] def feP4 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    Expr pqxdhOps Γ (.opt fgPosTy) := .fst (.snd (.snd (.snd e)))
@[reducible] def feSs {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def feDk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    Expr pqxdhOps Γ drKeyTy := .snd (.snd (.snd (.snd (.snd e))))

@[reducible] def pkP1 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ patchKeyTy) :
    Expr pqxdhOps Γ fgPosTy := .fst e
@[reducible] def pkP2 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ patchKeyTy) :
    Expr pqxdhOps Γ fgPosTy := .fst (.snd e)
@[reducible] def pkP3 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ patchKeyTy) :
    Expr pqxdhOps Γ fgPosTy := .fst (.snd (.snd e))
@[reducible] def pkP4 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ patchKeyTy) :
    Expr pqxdhOps Γ (.opt fgPosTy) := .fst (.snd (.snd (.snd e)))
@[reducible] def pkSs {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ patchKeyTy) :
    Expr pqxdhOps Γ (B 32) := .snd (.snd (.snd (.snd e)))

@[reducible] def reRk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ rootEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def rePos {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ rootEntryTy) :
    Expr pqxdhOps Γ fgPosTy := .fst (.snd e)
@[reducible] def reRk1 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ rootEntryTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd (.snd e))
@[reducible] def reCk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ rootEntryTy) :
    Expr pqxdhOps Γ (B 32) := .snd (.snd (.snd e))

@[reducible] def q4 {Γ : List (Ty pqSig)} (a b c d : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ quadTy :=
  .pair a (.pair b (.pair c d))

def bytesEmpty {w : ℕ+} {Γ : List (Ty pqSig)} (b : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ .bool :=
  .bytesBeq b (.litBytes w [])

def slice32 {w : ℕ+} {Γ : List (Ty pqSig)} (n : Nat) (b : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ (B 32) :=
  .bytesTakeK 32 (.bytesDrop (.litNat n) b)

def zero32 {Γ : List (Ty pqSig)} : Expr pqxdhOps Γ (B 32) := .litBytes 32 (List.replicate 32 0)

def emptySimE {Γ : List (Ty pqSig)} (secb : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ fgSimTy :=
  fsMk (emptyAuthStE secb) .listNil .listNil .listNil .listNil .listNil .listNil

/-! ## DDH-Patched Random-Oracle Tables -/

section FgHelpers

variable {Δ : List (Ty pqSig)}

def mkSecretPosC (z : Expr pqxdhOps Δ (B 32)) : CG Δ fgPosTy :=
  letV z fun z => bindV (.queryPrimC .isCanonical (v z)) fun c => .ret (.inl (.pair (v z) (v c)))

def mkPairPosC (pk1 pk2 : Expr pqxdhOps Δ (B 32)) : CG Δ fgPosTy :=
  letV (.pair pk1 pk2) fun p =>
  bindV (.queryPrimC .pow8 (.fst (v p))) fun w1 =>
  bindV (.queryPrimC .pow8 (.snd (v p))) fun w2 =>
  .ret (.inr (.pair (.fst (v p)) (.pair (.snd (v p)) (.pair (v w1) (v w2)))))

def twoSideC (a : Expr pqxdhOps Δ quadTy) : CG Δ fgPosTy :=
  letV a fun a =>
  .iteC (.boolNot (bytesEmpty (.fst (v a))))
    (bindV (.queryPrimC .x25519 (.pair (.fst (v a)) (.snd (.snd (.snd (v a)))))) fun z =>
      mkSecretPosC (v z)) <|
  .iteC (.boolNot (bytesEmpty (.fst (.snd (v a)))))
    (bindV (.queryPrimC .x25519 (.pair (.fst (.snd (v a))) (.fst (.snd (.snd (v a)))))) fun z =>
      mkSecretPosC (v z))
    (mkPairPosC (.fst (.snd (.snd (v a)))) (.snd (.snd (.snd (v a)))))

def twoSideOptC (o : Expr pqxdhOps Δ (.opt quadTy)) : CG Δ (.opt fgPosTy) :=
  caseOptV o (.ret .noneE) fun a => bindV (twoSideC (v a)) fun p => .ret (.someE (v p))

def ddhEqC (p1 p2 : Expr pqxdhOps Δ fgPosTy) : CG Δ .bool :=
  letV (.pair p1 p2) fun pp =>
  caseSumV (.fst (v pp))
    (fun s1 => caseSumV (.snd (v pp))
      (fun s2 => .ret (.bytesBeq (.fst (v s1)) (.fst (v s2))))
      (fun q2 => .iteC (.snd (v s1))
        (Comp.queryDdh (.pair (.fst (v q2)) (.pair (.fst (.snd (v q2))) (.fst (v s1)))))
        (.ret (.litBool false))))
    (fun q1 => caseSumV (.snd (v pp))
      (fun s2 => .iteC (.snd (v s2))
        (Comp.queryDdh (.pair (.fst (v q1)) (.pair (.fst (.snd (v q1))) (.fst (v s2)))))
        (.ret (.litBool false)))
      (fun q2 => .ret (.boolOr
        (.boolAnd (.bytesBeq (.fst (.snd (.snd (v q1)))) (.fst (.snd (.snd (v q2)))))
          (.bytesBeq (.snd (.snd (.snd (v q1)))) (.snd (.snd (.snd (v q2))))))
        (.boolAnd (.bytesBeq (.fst (.snd (.snd (v q1)))) (.snd (.snd (.snd (v q2)))))
          (.bytesBeq (.snd (.snd (.snd (v q1)))) (.fst (.snd (.snd (v q2)))))))))

def ddhEqOptC (p1 p2 : Expr pqxdhOps Δ (.opt fgPosTy)) : CG Δ .bool :=
  letV (.pair p1 p2) fun pp =>
  caseOptV (.fst (v pp)) (.ret (eCaseOpt (.snd (v pp)) (.litBool true) fun _ => .litBool false))
    fun a => caseOptV (.snd (v pp)) (.ret (.litBool false)) fun b => ddhEqC (v a) (v b)

variable {Γ₁ Γ₂ : List (Ty pqSig)}

def entryMatchesC (k : Var Γ₁ patchKeyTy) (e : Var Γ₂ fgPatchEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CG Δ .bool :=
  .iteC (.boolNot (.bytesBeq (pkSs (v k)) (feSs (v e)))) (.ret (.litBool false)) <|
  bindV (ddhEqC (pkP1 (v k)) (feP1 (v e))) fun b1 =>
  bindV (ddhEqC (pkP2 (v k)) (feP2 (v e))) fun b2 =>
  bindV (ddhEqC (pkP3 (v k)) (feP3 (v e))) fun b3 =>
  bindV (ddhEqOptC (pkP4 (v k)) (feP4 (v e))) fun b4 =>
  .ret (.boolAnd (.boolAnd (.boolAnd (v b1) (v b2)) (v b3)) (v b4))

def patchC (maxLen : Nat) (k : Var Γ₁ patchKeyTy) [Ext Γ₁ Δ]
    (L : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    CG Δ (.prod drKeyTy (.list fgPatchEntryTy)) :=
  letV L fun L =>
  bindV (findMV maxLen (v L) fun e => entryMatchesC k e) fun f =>
  caseOptV (v f)
    (bindV .sampleDrKey96C fun dk =>
      .ret (.pair (v dk) (.listCons (.pair (pkP1 (v k)) (.pair (pkP2 (v k)) (.pair (pkP3 (v k))
        (.pair (pkP4 (v k)) (.pair (pkSs (v k)) (v dk)))))) (v L))))
    fun e => .ret (.pair (feDk (v e)) (v L))

def rootPatchC (maxLen : Nat) (rk : Expr pqxdhOps Δ (B 32)) (pos : Expr pqxdhOps Δ fgPosTy)
    (L : Expr pqxdhOps Δ (.list rootEntryTy)) :
    CG Δ (.prod (.prod (B 32) (B 32)) (.list rootEntryTy)) :=
  letV (.pair rk (.pair pos L)) fun a =>
  bindV (findMV maxLen (.snd (.snd (v a))) fun e =>
      .iteC (.boolNot (.bytesBeq (.fst (v a)) (reRk (v e)))) (.ret (.litBool false))
        (ddhEqC (.fst (.snd (v a))) (rePos (v e)))) fun f =>
  caseOptV (v f)
    (bindV .sampleBytes32C fun rk1 => bindV .sampleBytes32C fun ck1 =>
      .ret (.pair (.pair (v rk1) (v ck1))
        (.listCons (.pair (.fst (v a)) (.pair (.fst (.snd (v a))) (.pair (v rk1) (v ck1))))
          (.snd (.snd (v a))))))
    fun e => .ret (.pair (.pair (reRk1 (v e)) (reCk (v e))) (.snd (.snd (v a))))

end FgHelpers

/-! ## Key-Registration Helpers -/

section PowsHelpers

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}

def isAdvPowsC (pows : Var Γ (.list (.prod (B 32) (B 32)))) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (.queryPrim .pow8 pk) fun w =>
  .ret (eAny K (v pows) fun e => .bytesBeq (.snd (v e)) (v w))

def koskBundleOkPowsC (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (bu : Var Γ₃ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (findHonestC S K st (buIkB (v bu))) fun f =>
  bindV (isAdvPowsC K pows (buIkB (v bu))) fun idA =>
  bindV (isGameSpkC S K st (buSpkB (v bu))) fun spkG =>
  bindV (isAdvPowsC K pows (buSpkB (v bu))) fun spkA =>
  caseOptV (buOpkB (v bu))
    (.ret (.boolAnd (.boolAnd (.boolOr (isSomeE (v f)) (v idA)) (.boolOr (v spkG) (v spkA)))
      (.litBool true)))
    fun o =>
      bindV (isGameOpkC S K st (.snd (v o))) fun opkG =>
      bindV (isAdvPowsC K pows (.snd (v o))) fun opkA =>
      .ret (.boolAnd (.boolAnd (.boolOr (isSomeE (v f)) (v idA)) (.boolOr (v spkG) (v spkA)))
        (.boolOr (v opkG) (v opkA)))

def koskSenderOkPowsC (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (ik : Expr pqxdhOps Δ (B 32)) : Comp pqxdhOps pqPrimIface Δ .bool :=
  letV ik fun ik =>
  bindV (findHonestC S K st (v ik)) fun f =>
  bindV (isAdvPowsC K pows (v ik)) fun idA =>
  .ret (.boolOr (isSomeE (v f)) (v idA))

def lookupSpkSkC (st : Var Γ₁ authStateTy) (pows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pk : Expr pqxdhOps Δ (B 32)) : Comp pqxdhOps pqPrimIface Δ (B 32) :=
  bindV (.queryPrim .pow8 pk) fun w =>
  bindV (findMV (min K S.N_dh) (stSpks (v st)) fun e =>
      bindV (.queryPrim .pow8 (sbSpkPk (.snd (v e)))) fun p1 => .ret (.bytesBeq (v p1) (v w)))
    fun f =>
  .ret (eCaseOpt (v f)
    (eCaseOpt (eFind K (v pows) fun e => .bytesBeq (.snd (v e)) (v w))
      (.litBytes 32 []) fun e => .fst (v e))
    fun e => sbSpkSk (.snd (v e)))

end PowsHelpers

/-! ## Query Handlers -/

section Handlers

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}

def onBaseF (sim : Var Γ₁ fgSimTy) [Ext Γ₁ Δ]
    (br : (g : Var (authStateTy :: Δ) authStateTy) →
      Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS) : CG Δ RSF :=
  bindV (Comp.liftChal (C := gapDhDdhOracle) (letV (fsBase (v sim)) fun g => br g)) fun r =>
  .ret (.pair (.fst (v r)) (fsUpd (v sim) (base := .snd (v r))))

def fgInitPrinC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (.pair aNone (v sim))) <|
  letV (.boolAnd (paDh1 (v pa)) (natEq (v u) (paTI (v pa)))) fun isT =>
  bindV .sampleBytes32C fun s0 => bindV (.queryPrimC .x25519Base (v s0)) fun ik =>
  bindV .sampleBytes32C fun s1 => bindV (.queryPrimC .sigPkGen (v s1)) fun sp =>
  letV (peMk (.ite (v isT) (.litBytes 32 []) (v s0)) (.ite (v isT) (paU (v pa)) (v ik))
      (v s1) (v sp) (.litBool false)) fun ent =>
  .ret (.pair (aInitPrin (peIkAPk (v ent)) (v sp))
    (fsUpd (v sim)
      (base := stUpd (v st) (prin := .listCons (.pair (v u) (v ent)) (stPrin (v st))))))

def fgGenSpkC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)) (.ret (.pair aNone (v sim))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v sim))) fun uE =>
  letV (natEq (.add (.mulK (nRecvEff S) (.fst (v x))) (.snd (v x))) (paTS (v pa)))
    fun isT =>
  bindV .sampleBytes32C fun skRaw =>
  bindV (.queryPrimC .x25519Base (v skRaw)) fun pkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v skRaw)) fun spkSk =>
  letV (.ite (v isT) (paV (v pa)) (v pkRaw)) fun spkPk =>
  bindV .sampleRandom64C fun r1 =>
  bindV (.queryPrimC (.sigSign 33)
      (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1))))
    fun sig1 =>
  bindV .sampleRandom64C fun seed =>
  bindV (.queryPrimC .kemKeyGen (v seed)) fun kp =>
  bindV .sampleRandom64C fun r2 =>
  bindV (.queryPrimC (.sigSign 1569) (.pair (peSecIKAsign (.snd (v uE)))
    (.pair (encKEM (.fst (v kp))) (v r2)))) fun sig2 =>
  .ret (.pair (aBundle (buMk (peIkAPk (.snd (v uE))) (.u32OfNat (.snd (v x))) (v spkPk)
      (v sig1) .noneE (.u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (fsUpd (v sim) (base := stUpd (v st) (spks := .listCons (.pair (v x) (sbMk (v spkSk) (v spkPk)
      (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.litBool false))) (stSpks (v st))))))

def fgSendC (opk : Bool) (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  .iteC (sendGuardE opk (v x)) (.ret (.pair aNone (v sim))) <|
  letV (fsBase (v sim)) fun st => letV (fsPows (v sim)) fun pows =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .iteC (.boolNot (natEq (.bytesLen (v m0)) (.bytesLen (v m1)))) (.ret (.pair aNone (v sim))) <|
  .iteC (eAny K (stUsedS (v st)) fun e => sidEq (v e) (v sid)) (.ret (.pair aNone (v sim))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v sim))) fun uE =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (findHonestC S K st (buIkB (v bu)))) fun pp =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  .iteC (.boolAnd (.boolNot (v fresh)) (.boolNot (.bytesBeq (v m0) (v m1))))
    (.ret (.pair aNone (v sim))) <|
  bindV (Comp.liftChal (C := gapDhDdhOracle) (koskBundleOkPowsC S K st pows bu)) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (v sim))) <|
  letV (.boolAnd (.boolNot (paDh1 (v pa))) (natEq
      (if opk then .add (.mulK (nSendOpkEff S) (.fst (v x))) (.fst (.snd (v x)))
       else .add (.litNat S.N_send_opk_tot)
         (.add (.mulK (nSendNoOpkEff S) (.fst (v x))) (.fst (.snd (v x)))))
      (paTI (v pa)))) fun isT =>
  bindV .sampleBytes32C fun ekRaw =>
  bindV .sampleBytes32C fun coins =>
  bindV .sampleBytes32C fun ephSk =>
  bindV .sampleBytes32C fun spqrCoins =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (resolveSigPkC S K st (buIkB (v bu)))) fun spk =>
  bindV (.queryPrimC (.sigVerify 33)
      (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (.queryPrimC (.sigVerify 1569)
      (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .iteC (.boolNot (.boolAnd (v v1) (v v2))) (.ret (.pair aNone (v sim))) <|
  bindV (.queryPrimC .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc) (.ret (.pair aNone (v sim))) fun sc =>
  bindV (.queryPrimC .x25519Base (v ekRaw)) fun ekPkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v ekRaw)) fun ekSk =>
  letV (.ite (v isT) (paU (v pa)) (v ekPkRaw)) fun ekPk =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (lookupSpkSkC S K st pows (buSpkB (v bu)))) fun spkSk =>
  bindV (twoSideC (q4 (peSecIKA0 (.snd (v uE))) (v spkSk)
      (peIkAPk (.snd (v uE))) (buSpkB (v bu))))
    fun p1 =>
  bindV (twoSideC (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (buIkB (v bu)))) fun p2 =>
  bindV (twoSideC (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (buSpkB (v bu)))) fun p3 =>
  bindV (twoSideOptC (eCaseOpt (buOpkB (v bu)) .noneE fun o =>
      .someE (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (.snd (v o))))) fun p4 =>
  letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4) (.fst (v sc)))))) fun pk =>
  bindV (patchC K pk (fsL (v sim))) fun dr =>
  bindV (.queryPrimC .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrimC .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (mkSecretPosC (v dhR)) fun posR =>
  bindV (rootPatchC K (.fst (.fst (v dr))) (v posR) (fsRootL (v sim))) fun rkOut =>
  bindV (.queryPrimC .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrimC .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrimC (.spqrInitSend 32 32)
      (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins))) fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone (v sim))) fun sp =>
  bindV (.queryPrimC (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (.snd (v uE))) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp))))
    fun ad =>
  bindV (.queryPrimC (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad)
      (.ite (v fresh) (.ite (stSecb (v st)) (v m1) (v m0)) (v m0))))) fun ct =>
  letV (.pair (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) (.pair (v ephPk) (.pair (.snd (.snd (v sp))) (v ct))))
    fun wm =>
  letV (eCaseOpt (v pp) (.pair (.litBool false) (.litBool false)) fun p =>
      .pair (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))
        (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))) fun hon =>
  letV (seMk (v sid) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu))) (buPqspkB (v bu))
      (.fst (v hon)) (.litBool false) (.snd (v hon)) (v ekSk) (v ephSk) (v fresh)
      (.boolAnd (v fresh) (.boolNot (.bytesBeq (v m0) (v m1))))) fun se =>
  .ret (.pair (eCaseOpt (v pp)
      (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (fsUpd (v sim) (base := stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
        (usedS := .listCons (v sid) (stUsedS (v st))))
      (fgL := .snd (v dr)) (rootL := .snd (v rkOut))))

def fgRecvC (opk : Bool) (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CG Δ RSF :=
  letV (fsBase (v sim)) fun st => letV (fsPows (v sim)) fun pows =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  .iteC (.boolNot (.boolAnd (.boolAnd (.boolAnd (.boolAnd (.boolAnd
      (.u32Beq (hdSpkId (v hdr)) (.u32OfNat (.fst (.snd (v x)))))
      (.u32Beq (hdPqspkId (v hdr)) (.u32OfNat (.fst (.snd (v x))))))
      (optU32Eq (hdOpkId (v hdr))
        (if opk then .someE (.u32OfNat (.fst (.snd (.snd (v x))))) else .noneE)))
      (natEq (.bytesLen (hdIkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (hdEkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (pmEphAPk (v msg))) (.litNat 32))))
    (.ret (.pair aNone (v sim))) <|
  .iteC (eAny K (if opk then stUsedO (v st) else stUsedN (v st)) fun e => nat3Eq (v e) (v kjo))
    (.ret (.pair aNone (v sim))) <|
  bindV (Comp.liftChal (C := gapDhDdhOracle) (koskSenderOkPowsC S K st pows (hdIkAPk (v hdr))))
    fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (v sim))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v sim))) fun kE =>
  caseOptV (eFind K (stSpks (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (.pair aNone (v sim))) fun bE =>
  bindV (if opk then
      caseOptV (eFind K (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
          (.ret .noneE) fun oE =>
        .ret (.ite (oeConsumed (.snd (v oE))) .noneE
          (.someE (.someE (.pair (oeOpkSk (.snd (v oE))) (oeOpkPk (.snd (v oE)))))))
    else .ret (.someE .noneE)) fun oChk =>
  caseOptV (v oChk) (.ret (.pair aNone (v sim))) fun oKey =>
  letV (kyberCheckE K (stKyb (v st)) (.pair (.fst (v x)) (.pair (hdPqspkId (v hdr))
      (.pair (hdSpkId (v hdr)) (hdEkAPk (v hdr)))))) fun kc =>
  bindV (.queryPrimC .isCanonical (hdEkAPk (v hdr))) fun can =>
  bindV (.queryPrimC .isCanonical (pmEphAPk (v msg))) fun canE =>
  .iteC (.boolOr (.boolOr (.boolNot (.fst (v kc))) (.boolNot (v can))) (.boolNot (v canE)))
    (.ret (.pair aNone (v sim))) <|
  bindV (.queryPrimC .kemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (.pair aNone (v sim))) fun ss =>
  bindV (twoSideOptC (eCaseOpt (v oKey) .noneE fun o =>
      .someE (q4 (.litBytes 32 []) (.fst (v o)) (hdEkAPk (v hdr)) (.snd (v o))))) fun p4 =>
  letV (.snd (v kE)) fun kE' => letV (.snd (v bE)) fun bE' =>
  bindV (twoSideC (q4 (.litBytes 32 []) (sbSpkSk (v bE'))
      (hdIkAPk (v hdr)) (sbSpkPk (v bE')))) fun p1 =>
  bindV (twoSideC (q4 (.litBytes 32 []) (peSecIKA0 (v kE'))
      (hdEkAPk (v hdr)) (peIkAPk (v kE')))) fun p2 =>
  bindV (twoSideC (q4 (.litBytes 32 []) (sbSpkSk (v bE'))
      (hdEkAPk (v hdr)) (sbSpkPk (v bE')))) fun p3 =>
  letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4) (v ss))))) fun pk =>
  bindV (patchC K pk (fsL (v sim))) fun dkL =>
  bindV (twoSideC (q4 (.litBytes 32 []) (sbSpkSk (v bE')) (pmEphAPk (v msg)) (sbSpkPk (v bE'))))
    fun posR =>
  bindV (rootPatchC K (.fst (.fst (v dkL))) (v posR) (fsRootL (v sim))) fun rkOut =>
  bindV (.queryPrimC .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrimC .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrimC (.spqrInitRecv 32 32) (.pair (.snd (.snd (.fst (v dkL)))) (pmPqMsg (v msg))))
    fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone (v sim))) fun sp =>
  bindV (.queryPrimC (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mk =>
  bindV (.queryPrimC (.aeadDec 158 32 32) (.pair (v mk)
      (.pair (firstMsgADE (hdIkAPk (v hdr)) (peIkAPk (v kE'))
      (pmEphAPk (v msg)) (pmPqMsg (v msg))) (pmAeadCt (v msg))))) fun pt? =>
  caseOptV (v pt?) (.ret (.pair aNone (v sim))) fun pt =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (findHonestC S K st (hdIkAPk (v hdr)))) fun snd? =>
  letV (if opk then
      stUpd (v st)
        (opks := eMap K (stOpks (v st)) fun e =>
          .ite (nat3Eq (.fst (v e)) (v kjo))
            (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .litBool true))) (v e))
        (usedO := .listCons (v kjo) (stUsedO (v st))) (kyb := .snd (v kc))
    else
      stUpd (v st) (usedN := .listCons (v kjo) (stUsedN (v st))) (kyb := .snd (v kc))) fun st' =>
  .ret (.pair (eCaseOpt (v snd?)
      (aRecvUnfresh (.fst (v dkL)) (.fst (.fst (v rkOut))) (v ck11) (v pt))
      fun _ => aRecvHonest)
    (fsUpd (v sim) (base := v st') (fgL := .snd (v dkL)) (rootL := .snd (v rkOut))))

def fgRecvB (opk : Bool) (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CG Δ RSF :=
  letV (fsUpd (v sim) (resp := .listCons (.pair (.pair (.fst (v x)) (.fst (.snd (v x))))
      (.pair (hdIkAPk (pmHdr (.snd (.snd (.snd (v x))))))
        (hdEkAPk (pmHdr (.snd (.snd (.snd (v x))))))))
      (fsResp (v sim)))) fun sim' =>
  fgRecvC S K opk sim' x

def fgRoC (sim : Var Γ₁ fgSimTy) (sec : Var Γ₂ (B 192)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : CG Δ RSF :=
  letV (.listCons (v sec) (fsLog (v sim))) fun log' =>
  .iteC (.boolAnd (.bytesBeq (.bytesTakeK 32 (v sec)) (.litBytes 32 F_X25519))
      (.boolOr (natEq (.bytesLen (v sec)) (.litNat 160))
        (natEq (.bytesLen (v sec)) (.litNat 192))))
    (bindV (mkSecretPosC (slice32 32 (v sec))) fun p1 =>
     bindV (mkSecretPosC (slice32 64 (v sec))) fun p2 =>
     bindV (mkSecretPosC (slice32 96 (v sec))) fun p3 =>
     bindV (.iteC (natEq (.bytesLen (v sec)) (.litNat 192))
         (bindV (mkSecretPosC (slice32 128 (v sec))) fun p => .ret (.someE (v p))) (.ret .noneE))
       fun p4 =>
     letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4)
         (.ite (natEq (.bytesLen (v sec)) (.litNat 192)) (slice32 160 (v sec))
           (slice32 128 (v sec))))))) fun pk =>
     bindV (patchC K pk (fsL (v sim))) fun r =>
     .ret (.pair (aDrKey (.fst (v r))) (fsUpd (v sim) (fgL := .snd (v r)) (log := v log'))))
    (caseOptV (eFind K (fsRaw (v sim)) fun e => .bytesBeq (.fst (v e)) (v sec))
      (bindV .sampleDrKey96C fun dk =>
        .ret (.pair (aDrKey (v dk)) (fsUpd (v sim)
          (raw := .listCons (.pair (v sec) (v dk)) (fsRaw (v sim))) (log := v log'))))
      fun e => .ret (.pair (aDrKey (.snd (v e))) (fsUpd (v sim) (log := v log'))))

def fgRoRootC (sim : Var Γ₁ fgSimTy) (x : Var Γ₂ (.prod (B 32) (B 32))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CG Δ RSF :=
  bindV (mkSecretPosC (.snd (v x))) fun pos =>
  bindV (rootPatchC K (.fst (v x)) (v pos) (fsRootL (v sim))) fun r =>
  .ret (.pair (aRootKdf (.fst (.fst (v r))) (.snd (.fst (v r))))
    (fsUpd (v sim) (rootL := .snd (v r))))

def fgRegisterC (sim : Var Γ₁ fgSimTy) (sk : Var Γ₂ (B 32)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] : CG Δ RSF :=
  .iteC (.boolNot (natEq (.bytesLen (v sk)) (.litNat 32))) (.ret (.pair aNone (v sim))) <|
  bindV (.queryPrimC .x25519Base (v sk)) fun pk => bindV (.queryPrimC .pow8 (v pk)) fun w =>
  .ret (.pair (aPk (v pk)) (fsUpd (v sim)
    (base := stUpd (fsBase (v sim))
      (adv := .listCons (.pair (v w) (v pk)) (stAdv (fsBase (v sim)))))
    (pows := .listCons (.pair (v sk) (v w)) (fsPows (v sim)))))

/-- Full `fgAuthStep` simulator query handler. -/
def fgStepC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  caseSumV (v q) (fun u => fgInitPrinC K pa sim u) fun q =>
  caseSumV (v q) (fun u => onBaseF sim fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => fgGenSpkC S K pa sim x) fun q =>
  caseSumV (v q) (fun x => onBaseF sim fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => fgSendC S K true pa sim x) fun q =>
  caseSumV (v q) (fun x => fgSendC S K false pa sim x) fun q =>
  caseSumV (v q) (fun x => fgRecvB S K true sim x) fun q =>
  caseSumV (v q) (fun x => fgRecvB S K false sim x) fun q =>
  caseSumV (v q) (fun sec => fgRoC K sim sec) fun q =>
  caseSumV (v q) (fun x => fgRoRootC K sim x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun sk =>
  fgRegisterC sim sk

end Handlers

/-! ## End-of-Game CDH Extraction -/

section Extract

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def findMapC {τ : Ty pqSig} (pa : Var Γ₁ paramsTy) [Ext Γ₁ Δ] (N : Nat)
    (xs : Expr pqxdhOps Δ (.list τ))
    (f : (x : Var (τ :: .opt (B 32) :: Δ) τ) → CG (τ :: .opt (B 32) :: Δ) (B 32)) :
    CG Δ (.opt (B 32)) :=
  foldMV N xs .noneE fun x acc =>
    caseOptV (v acc)
      (bindV (f x) fun z =>
        bindV (Comp.queryDdh (.pair (paU (v pa)) (.pair (paV (v pa)) (v z)))) fun b =>
        .ret (.ite (v b) (.someE (v z)) .noneE))
      fun _ => .ret (v acc)

def logScanC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] (off : Nat) :
    CG Δ (.opt (B 32)) :=
  findMV K (eMap K (fsLog (v sim)) fun s => slice32 off (v s)) fun z =>
    Comp.queryDdh (.pair (paU (v pa)) (.pair (paV (v pa)) (v z)))

def respCandC (sim : Var Γ₁ fgSimTy) (r : Var Γ₂ respRecTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pk : Expr pqxdhOps Δ (B 32)) : CG Δ (B 32) :=
  .queryPrimC .x25519 (.pair
    (eCaseOpt (eFind S.N_dh (stSpks (fsBase (v sim))) fun e => nat2Eq (.fst (v e)) (.fst (v r)))
      (.litBytes 32 []) fun e => sbSpkSk (.snd (v e)))
    pk)

def initDh1CandC (sim : Var Γ₁ fgSimTy) (spkPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Γ₃ authSessionEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ (B 32) :=
  bindV (.queryPrimC .pow8 (sePeerSpk (v s))) fun w =>
  letV (eCaseOpt (eFind S.N_dh (v spkPows) fun e =>
        .boolAnd (.boolNot (bytesEmpty (.fst (v e)))) (.bytesBeq (.snd (v e)) (v w)))
      (eCaseOpt (eFind K (fsPows (v sim)) fun e => .bytesBeq (.snd (v e)) (v w))
        (.litBytes 32 []) fun e => .fst (v e))
      fun e => .fst (v e)) fun spkSk =>
  letV (eCaseSum (seSid (v s)) (fun p => .fst (v p)) fun r => eCaseSum (v r) (fun p => .fst (v p))
      fun r => eCaseSum (v r) (fun p => .fst (v p)) fun p => .fst (v p)) fun uIdx =>
  letV (eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (v uIdx))
      (.litBytes 32 []) fun e => peIkAPk (.snd (v e))) fun ikA =>
  .queryPrimC .x25519 (.pair (v spkSk) (v ikA))

def fgExtractC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CG Δ (B 32) :=
  .iteC (paDh1 (v pa))
    (bindV (logScanC K pa sim 32) fun f =>
     caseOptV (v f)
       (bindV (mapMV S.N_dh (stSpks (fsBase (v sim))) fun e =>
           bindV (.queryPrimC .pow8 (sbSpkPk (.snd (v e)))) fun w =>
           .ret (.pair (sbSpkSk (.snd (v e))) (v w))) fun spkPows =>
        bindV (findMapC pa S.N_dh (stSess (fsBase (v sim)))
            fun s => initDh1CandC S K sim spkPows s)
          fun f2 =>
        caseOptV (v f2)
          (bindV (findMapC pa S.N_sess_tot (fsResp (v sim)) fun r =>
              respCandC S sim r (.fst (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))
    (bindV (logScanC K pa sim 96) fun f =>
     caseOptV (v f)
       (bindV (findMapC pa S.N_dh (stSess (fsBase (v sim))) fun s =>
           .iteC (bytesEmpty (seEkASk (v s))) (.ret zero32)
             (.queryPrimC .x25519 (.pair (seEkASk (v s)) (sePeerSpk (v s))))) fun f2 =>
        caseOptV (v f2)
          (bindV (findMapC pa S.N_sess_tot (fsResp (v sim)) fun r =>
              respCandC S sim r (.snd (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))

end Extract

/-! ## Flat-Indexed Entrypoints -/

def fgHandleDsl (S : Setup) (K : Nat) : CG [gsTy, authQueryTy] (.prod authRespTy gsTy) :=
  letV (.fst (.var .vz) : Expr pqxdhOps [gsTy, authQueryTy] paramsTy) fun pa =>
  letV (.snd (.var (.vs .vz)) : Expr pqxdhOps [paramsTy, gsTy, authQueryTy] fgSimTy) fun sim =>
  .iteC (.boolAnd (paDh1 (v pa))
      (eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (paTI (v pa)))
        (.litBool false) fun e => peCorrupted (.snd (v e))))
    (.ret (.pair aNone (.pair (v pa) (v sim)))) <|
  bindV (fgStepC S K pa sim (.vs .vz : Var [gsTy, authQueryTy] authQueryTy)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (v pa) (.snd (v r))))

def fgInitDsl (S : Setup) : CG [.prod (B 32) (B 32)] (.prod .unit gsTy) :=
  bindV (.sampleIndexC (S.N_id + S.N_send_tot)) fun flat =>
  bindV (.sampleIndexC S.N_spk_tot) fun bIdx =>
  letV (.lt (v flat) (.litNat S.N_id)) fun dh1 =>
  bindV .sampleBoolC fun secb =>
  .ret (.pair .litUnit (.pair
    (.pair (.fst (.var (.vs (.vs (.vs (.vs .vz)))) :
      Expr pqxdhOps [.bool, .bool, .nat, .nat, .prod (B 32) (B 32)] (.prod (B 32) (B 32))))
    (.pair (.snd (.var (.vs (.vs (.vs (.vs .vz)))) :
      Expr pqxdhOps [.bool, .bool, .nat, .nat, .prod (B 32) (B 32)] (.prod (B 32) (B 32))))
    (.pair (v dh1) (.pair (.ite (v dh1) (v flat) (.sub (v flat) (.litNat S.N_id))) (v bIdx)))))
    (emptySimE (v secb))))

def fgFinishDsl (S : Setup) (K : Nat) : CG [gsTy, .bool] (B 32) :=
  letV (.fst (.var .vz) : Expr pqxdhOps [gsTy, .bool] paramsTy) fun pa =>
  letV (.snd (.var (.vs .vz)) : Expr pqxdhOps [paramsTy, gsTy, .bool] fgSimTy) fun sim =>
  fgExtractC S K pa sim

/-! ## Tuple-Keyed Reduction Program -/

section TupleProgram

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def fg2InitPrinC (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (.pair aNone (v sim))) <|
  letV (.boolAnd (fg2PaDh1 (v pa)) (natEq (v u) (fg2PaTI (v pa)))) fun isT =>
  bindV .sampleBytes32C fun s0 => bindV (.queryPrimC .x25519Base (v s0)) fun ik =>
  bindV .sampleBytes32C fun s1 => bindV (.queryPrimC .sigPkGen (v s1)) fun sp =>
  letV (peMk (.ite (v isT) (.litBytes 32 []) (v s0)) (.ite (v isT) (fg2PaU (v pa)) (v ik))
      (v s1) (v sp) (.litBool false)) fun ent =>
  .ret (.pair (aInitPrin (peIkAPk (v ent)) (v sp))
    (fsUpd (v sim)
      (base := stUpd (v st) (prin := .listCons (.pair (v u) (v ent)) (stPrin (v st))))))

def fg2GenSpkC (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)) (.ret (.pair aNone (v sim))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v sim))) fun uE =>
  letV (eCaseOpt (fg2PaTS (v pa)) (.litBool false) fun spkPair => nat2Eq (v x) (v spkPair))
    fun isT =>
  bindV .sampleBytes32C fun skRaw =>
  bindV (.queryPrimC .x25519Base (v skRaw)) fun pkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v skRaw)) fun spkSk =>
  letV (.ite (v isT) (fg2PaV (v pa)) (v pkRaw)) fun spkPk =>
  bindV .sampleRandom64C fun r1 =>
  bindV (.queryPrimC (.sigSign 33)
      (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1))))
    fun sig1 =>
  bindV .sampleRandom64C fun seed =>
  bindV (.queryPrimC .kemKeyGen (v seed)) fun kp =>
  bindV .sampleRandom64C fun r2 =>
  bindV (.queryPrimC (.sigSign 1569) (.pair (peSecIKAsign (.snd (v uE)))
    (.pair (encKEM (.fst (v kp))) (v r2)))) fun sig2 =>
  .ret (.pair (aBundle (buMk (peIkAPk (.snd (v uE))) (.u32OfNat (.snd (v x))) (v spkPk)
      (v sig1) .noneE (.u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (fsUpd (v sim) (base := stUpd (v st) (spks := .listCons (.pair (v x) (sbMk (v spkSk) (v spkPk)
      (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.litBool false))) (stSpks (v st))))))

def fg2SendC (opk : Bool) (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  .iteC (sendGuardE opk (v x)) (.ret (.pair aNone (v sim))) <|
  letV (fsBase (v sim)) fun st => letV (fsPows (v sim)) fun pows =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .iteC (.boolNot (natEq (.bytesLen (v m0)) (.bytesLen (v m1)))) (.ret (.pair aNone (v sim))) <|
  .iteC (eAny K (stUsedS (v st)) fun e => sidEq (v e) (v sid)) (.ret (.pair aNone (v sim))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v sim))) fun uE =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (findHonestC S K st (buIkB (v bu)))) fun pp =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  .iteC (.boolAnd (.boolNot (v fresh)) (.boolNot (.bytesBeq (v m0) (v m1))))
    (.ret (.pair aNone (v sim))) <|
  bindV (Comp.liftChal (C := gapDhDdhOracle) (koskBundleOkPowsC S K st pows bu)) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (v sim))) <|
  letV (.boolAnd (.boolNot (fg2PaDh1 (v pa)))
    (.boolAnd (if opk then fg2PaSendOpk (v pa) else .boolNot (fg2PaSendOpk (v pa)))
      (nat2Eq (.pair (.fst (v x)) (.fst (.snd (v x))))
        (.pair (fg2PaTI (v pa)) (fg2PaSendIdx (v pa)))))) fun isT =>
  bindV .sampleBytes32C fun ekRaw =>
  bindV .sampleBytes32C fun coins =>
  bindV .sampleBytes32C fun ephSk =>
  bindV .sampleBytes32C fun spqrCoins =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (resolveSigPkC S K st (buIkB (v bu)))) fun spk =>
  bindV (.queryPrimC (.sigVerify 33)
      (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (.queryPrimC (.sigVerify 1569)
      (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .iteC (.boolNot (.boolAnd (v v1) (v v2))) (.ret (.pair aNone (v sim))) <|
  bindV (.queryPrimC .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc) (.ret (.pair aNone (v sim))) fun sc =>
  bindV (.queryPrimC .x25519Base (v ekRaw)) fun ekPkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v ekRaw)) fun ekSk =>
  letV (.ite (v isT) (fg2PaU (v pa)) (v ekPkRaw)) fun ekPk =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (lookupSpkSkC S K st pows (buSpkB (v bu)))) fun spkSk =>
  bindV (twoSideC (q4 (peSecIKA0 (.snd (v uE))) (v spkSk)
      (peIkAPk (.snd (v uE))) (buSpkB (v bu))))
    fun p1 =>
  bindV (twoSideC (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (buIkB (v bu)))) fun p2 =>
  bindV (twoSideC (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (buSpkB (v bu)))) fun p3 =>
  bindV (twoSideOptC (eCaseOpt (buOpkB (v bu)) .noneE fun o =>
      .someE (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (.snd (v o))))) fun p4 =>
  letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4) (.fst (v sc)))))) fun pk =>
  bindV (patchC K pk (fsL (v sim))) fun dr =>
  bindV (.queryPrimC .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrimC .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (mkSecretPosC (v dhR)) fun posR =>
  bindV (rootPatchC K (.fst (.fst (v dr))) (v posR) (fsRootL (v sim))) fun rkOut =>
  bindV (.queryPrimC .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrimC .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrimC (.spqrInitSend 32 32)
      (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins))) fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone (v sim))) fun sp =>
  bindV (.queryPrimC (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (.snd (v uE))) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp))))
    fun ad =>
  bindV (.queryPrimC (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad)
      (.ite (v fresh) (.ite (stSecb (v st)) (v m1) (v m0)) (v m0))))) fun ct =>
  letV (.pair (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) (.pair (v ephPk) (.pair (.snd (.snd (v sp))) (v ct))))
    fun wm =>
  letV (eCaseOpt (v pp) (.pair (.litBool false) (.litBool false)) fun p =>
      .pair (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))
        (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))) fun hon =>
  letV (seMk (v sid) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu))) (buPqspkB (v bu))
      (.fst (v hon)) (.litBool false) (.snd (v hon)) (v ekSk) (v ephSk) (v fresh)
      (.boolAnd (v fresh) (.boolNot (.bytesBeq (v m0) (v m1))))) fun se =>
  .ret (.pair (eCaseOpt (v pp)
      (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (fsUpd (v sim) (base := stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
        (usedS := .listCons (v sid) (stUsedS (v st))))
      (fgL := .snd (v dr)) (rootL := .snd (v rkOut))))

def fg2StepC (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  caseSumV (v q) (fun u => fg2InitPrinC K pa sim u) fun q =>
  caseSumV (v q) (fun u => onBaseF sim fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => fg2GenSpkC K pa sim x) fun q =>
  caseSumV (v q) (fun x => onBaseF sim fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => fg2SendC S K true pa sim x) fun q =>
  caseSumV (v q) (fun x => fg2SendC S K false pa sim x) fun q =>
  caseSumV (v q) (fun x => fgRecvB S K true sim x) fun q =>
  caseSumV (v q) (fun x => fgRecvB S K false sim x) fun q =>
  caseSumV (v q) (fun sec => fgRoC K sim sec) fun q =>
  caseSumV (v q) (fun x => fgRoRootC K sim x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun sk =>
  fgRegisterC sim sk

def fg2FindMapC {τ : Ty pqSig} (pa : Var Γ₁ fg2ParamsTy) [Ext Γ₁ Δ] (N : Nat)
    (xs : Expr pqxdhOps Δ (.list τ))
    (f : (x : Var (τ :: .opt (B 32) :: Δ) τ) → CG (τ :: .opt (B 32) :: Δ) (B 32)) :
    CG Δ (.opt (B 32)) :=
  foldMV N xs .noneE fun x acc =>
    caseOptV (v acc)
      (bindV (f x) fun z =>
        bindV (Comp.queryDdh (.pair (fg2PaU (v pa)) (.pair (fg2PaV (v pa)) (v z)))) fun b =>
        .ret (.ite (v b) (.someE (v z)) .noneE))
      fun _ => .ret (v acc)

def fg2LogScanC (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] (off : Nat) :
    CG Δ (.opt (B 32)) :=
  findMV K (eMap K (fsLog (v sim)) fun s => slice32 off (v s)) fun z =>
    Comp.queryDdh (.pair (fg2PaU (v pa)) (.pair (fg2PaV (v pa)) (v z)))

def fg2RespCandC (sim : Var Γ₁ fgSimTy) (r : Var Γ₂ respRecTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pk : Expr pqxdhOps Δ (B 32)) : CG Δ (B 32) :=
  .queryPrimC .x25519 (.pair
    (eCaseOpt (eFind (min K S.N_dh) (stSpks (fsBase (v sim))) fun e => nat2Eq (.fst (v e)) (.fst (v r)))
      (.litBytes 32 []) fun e => sbSpkSk (.snd (v e)))
    pk)

def fg2InitDh1CandC (sim : Var Γ₁ fgSimTy) (spkPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Γ₃ authSessionEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ (B 32) :=
  bindV (.queryPrimC .pow8 (sePeerSpk (v s))) fun w =>
  letV (eCaseOpt (eFind (min K S.N_dh) (v spkPows) fun e =>
        .boolAnd (.boolNot (bytesEmpty (.fst (v e)))) (.bytesBeq (.snd (v e)) (v w)))
      (eCaseOpt (eFind K (fsPows (v sim)) fun e => .bytesBeq (.snd (v e)) (v w))
        (.litBytes 32 []) fun e => .fst (v e))
      fun e => .fst (v e)) fun spkSk =>
  letV (eCaseSum (seSid (v s)) (fun p => .fst (v p)) fun r => eCaseSum (v r) (fun p => .fst (v p))
      fun r => eCaseSum (v r) (fun p => .fst (v p)) fun p => .fst (v p)) fun uIdx =>
  letV (eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (v uIdx))
      (.litBytes 32 []) fun e => peIkAPk (.snd (v e))) fun ikA =>
  .queryPrimC .x25519 (.pair (v spkSk) (v ikA))

def fg2ExtractC (pa : Var Γ₁ fg2ParamsTy) (sim : Var Γ₂ fgSimTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CG Δ (B 32) :=
  .iteC (fg2PaDh1 (v pa))
    (bindV (fg2LogScanC K pa sim 32) fun f =>
     caseOptV (v f)
       (bindV (mapMV (min K S.N_dh) (stSpks (fsBase (v sim))) fun e =>
           bindV (.queryPrimC .pow8 (sbSpkPk (.snd (v e)))) fun w =>
           .ret (.pair (sbSpkSk (.snd (v e))) (v w))) fun spkPows =>
        bindV (fg2FindMapC pa (min K S.N_dh) (stSess (fsBase (v sim)))
            fun s => fg2InitDh1CandC S K sim spkPows s)
          fun f2 =>
        caseOptV (v f2)
          (bindV (fg2FindMapC pa (min K S.N_sess_tot) (fsResp (v sim)) fun r =>
              fg2RespCandC S K sim r (.fst (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))
    (bindV (fg2LogScanC K pa sim 96) fun f =>
     caseOptV (v f)
       (bindV (fg2FindMapC pa (min K S.N_dh) (stSess (fsBase (v sim))) fun s =>
           .iteC (bytesEmpty (seEkASk (v s))) (.ret zero32)
             (.queryPrimC .x25519 (.pair (seEkASk (v s)) (sePeerSpk (v s))))) fun f2 =>
        caseOptV (v f2)
          (bindV (fg2FindMapC pa (min K S.N_sess_tot) (fsResp (v sim)) fun r =>
              fg2RespCandC S K sim r (.snd (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))

end TupleProgram

def fg2HandleDsl (S : Setup) (K : Nat) : CG [fg2GsTy, authQueryTy] (.prod authRespTy fg2GsTy) :=
  letV (.fst (.var .vz) : Expr pqxdhOps [fg2GsTy, authQueryTy] fg2ParamsTy) fun pa =>
  letV (.snd (.var (.vs .vz)) : Expr pqxdhOps [fg2ParamsTy, fg2GsTy, authQueryTy] fgSimTy) fun sim =>
  .iteC (.boolAnd (fg2PaDh1 (v pa))
      (eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (fg2PaTI (v pa)))
        (.litBool false) fun e => peCorrupted (.snd (v e))))
    (.ret (.pair aNone (.pair (v pa) (v sim)))) <|
  bindV (fg2StepC S K pa sim (.vs .vz : Var [fg2GsTy, authQueryTy] authQueryTy)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (v pa) (.snd (v r))))

abbrev targetChoiceTy : Ty pqSig := .prod .bool (.prod .nat (.prod .bool .nat))

/-- Samples `(useDh1, targetPrinIdx, sendIsOpk, sendSubIdx)` uniformly over target choices. -/
def fgSampleTargetC (S : Setup) {Γ : List (Ty pqSig)} : CG Γ targetChoiceTy :=
  if S.N_id = 0 then
    .ret (.pair (.litBool false) (.pair (.litNat 0) (.pair (.litBool false) (.litNat 0))))
  else
    let A := S.N_send_opk
    let B := S.N_send_no_opk
    bindV (.sampleIndexC S.N_id) fun uT =>
    bindV (.sampleIndexC (1 + A + B)) fun z =>
    .iteC (natEq (v z) (.litNat 0))
      (.ret (.pair (.litBool true) (.pair (v uT) (.pair (.litBool false) (.litNat 0)))))
      (if A = 0 ∧ B = 0 then
        .ret (.pair (.litBool false) (.pair (v uT) (.pair (.litBool false) (.litNat 0))))
       else if B = 0 then
        bindV (.sampleIndexC A) fun i =>
        .ret (.pair (.litBool false) (.pair (v uT) (.pair (.litBool true) (v i))))
       else if A = 0 then
        bindV (.sampleIndexC B) fun i =>
        .ret (.pair (.litBool false) (.pair (v uT) (.pair (.litBool false) (v i))))
       else if A ≤ B then
        bindV (.sampleIndexC A) fun x =>
        bindV (.sampleIndexC (A + B)) fun y =>
        .iteC (.lt (v y) (.add (.mulK 2 (v x)) (.litNat 1)))
          (bindV (.sampleIndexC A) fun i =>
            .ret (.pair (.litBool false) (.pair (v uT) (.pair (.litBool true) (v i)))))
          (bindV (.sampleIndexC B) fun i =>
            .ret (.pair (.litBool false) (.pair (v uT) (.pair (.litBool false) (v i)))))
       else
        bindV (.sampleIndexC B) fun x =>
        bindV (.sampleIndexC (A + B)) fun y =>
        .iteC (.lt (v y) (.add (.mulK 2 (v x)) (.litNat 1)))
          (bindV (.sampleIndexC B) fun i =>
            .ret (.pair (.litBool false) (.pair (v uT) (.pair (.litBool false) (v i)))))
          (bindV (.sampleIndexC A) fun i =>
            .ret (.pair (.litBool false) (.pair (v uT) (.pair (.litBool true) (v i))))))

/-- Samples target SPK pair `(uSpk, jSpk)` uniformly when `S.N_spk_tot > 0`. -/
def fgSampleSpkC (S : Setup) {Γ : List (Ty pqSig)} : CG Γ (.opt (.prod .nat .nat)) :=
  if S.N_spk_tot = 0 then
    .ret .noneE
  else
    bindV (.sampleIndexC S.N_id) fun uSpk =>
    bindV (.sampleIndexC S.N_recv) fun jSpk =>
    .ret (.someE (.pair (v uSpk) (v jSpk)))

def fg2InitDsl (S : Setup) : CG [.prod (B 32) (B 32)] (.prod .unit fg2GsTy) :=
  let uv : Var [.prod (B 32) (B 32)] (.prod (B 32) (B 32)) := .vz
  bindV (fgSampleTargetC S) fun tc =>
  bindV (fgSampleSpkC S) fun spk =>
  bindV .sampleBoolC fun secb =>
  .ret (.pair .litUnit (.pair
    (.pair (.fst (v uv))
    (.pair (.snd (v uv))
    (.pair (.fst (v tc))
    (.pair (.fst (.snd (v tc)))
    (.pair (.fst (.snd (.snd (v tc))))
    (.pair (.snd (.snd (.snd (v tc))))
           (v spk)))))))
    (emptySimE (v secb))))

def fg2FinishDsl (S : Setup) (K : Nat) : CG [fg2GsTy, .bool] (B 32) :=
  letV (.fst (.var .vz) : Expr pqxdhOps [fg2GsTy, .bool] fg2ParamsTy) fun pa =>
  letV (.snd (.var (.vs .vz)) : Expr pqxdhOps [fg2ParamsTy, fg2GsTy, .bool] fgSimTy) fun sim =>
  fg2ExtractC S K pa sim

/-- `ReductionDsl` witness for `fgAuthGapDhAdv4` with list-traversal bound `K`. -/
def fgAuthGapDhProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqGapDhIface (authSpec S) (authCodec S)
      (.prod (B 32) (B 32)) .unit .bool (B 32) where
  σ      := fg2GsTy
  init   := fg2InitDsl S
  handle := fg2HandleDsl S K
  finish := fg2FinishDsl S K

end SignalPqxdh.Security.ReductionDsl.AuthHs
