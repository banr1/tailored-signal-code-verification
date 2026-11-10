/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake

/-!
# `ReductionDsl` Program for the `Auth` `KemShCr` Reduction

Defines `shcrReductionAuthProg`, the two-stage `ReductionDsl` witness for the `Auth` `KemShCr`
reduction (`shcrReductionAuthCore`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

abbrev initRecTy : Ty pqSig :=
  .prod .nat (.prod sessionIdTy (.prod (B 1568) (.prod (B 1568) (B 32))))

abbrev recvRecTy : Ty pqSig :=
  .prod .nat (.prod .nat (.prod (B 1568) (.prod (B 3168) (.prod (B 1568) (B 32)))))

/-- `AuthShCrState` extended with the pause index `sIdx` and chosen public key. -/
abbrev shcrStTy : Ty pqSig :=
  .prod authStateTy (.prod (.opt (.prod .nat .nat)) (.prod (B 1568) (.prod (B 3168) (.prod .nat
    (.prod (.list initRecTy) (.prod (.list recvRecTy) (.prod .nat (B 1568))))))))

@[reducible] def scBase {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ authStateTy := .fst e
@[reducible] def scTB {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ (.opt (.prod .nat .nat)) := .fst (.snd e)
@[reducible] def scTPk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ (B 1568) := .fst (.snd (.snd e))
@[reducible] def scTSk {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ (B 3168) := .fst (.snd (.snd (.snd e)))
@[reducible] def scCnt {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd (.snd (.snd (.snd e))))
@[reducible] def scIR {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ (.list initRecTy) := .fst (.snd (.snd (.snd (.snd (.snd e)))))
@[reducible] def scRR {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ (.list recvRecTy) := .fst (.snd (.snd (.snd (.snd (.snd (.snd e))))))
@[reducible] def scSIdx {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ .nat := .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))
@[reducible] def scChosen {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy) :
    Expr pqxdhOps Γ (B 1568) := .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd e)))))))

@[reducible] def scMk {Γ : List (Ty pqSig)} (base : Expr pqxdhOps Γ authStateTy)
    (tB : Expr pqxdhOps Γ (.opt (.prod .nat .nat))) (tPk : Expr pqxdhOps Γ (B 1568)) (tSk : Expr pqxdhOps Γ (B 3168))
    (cnt : Expr pqxdhOps Γ .nat) (iR : Expr pqxdhOps Γ (.list initRecTy))
    (rR : Expr pqxdhOps Γ (.list recvRecTy)) (sIdx : Expr pqxdhOps Γ .nat)
    (chosen : Expr pqxdhOps Γ (B 1568)) : Expr pqxdhOps Γ shcrStTy :=
  .pair base (.pair tB (.pair tPk (.pair tSk
    (.pair cnt (.pair iR (.pair rR (.pair sIdx chosen)))))))

@[reducible] def scUpd {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ shcrStTy)
    (base : Expr pqxdhOps Γ authStateTy := scBase e) (cnt : Expr pqxdhOps Γ .nat := scCnt e)
    (iR : Expr pqxdhOps Γ (.list initRecTy) := scIR e) (rR : Expr pqxdhOps Γ (.list recvRecTy) := scRR e)
    (chosen : Expr pqxdhOps Γ (B 1568) := scChosen e) : Expr pqxdhOps Γ shcrStTy :=
  scMk base (scTB e) (scTPk e) (scTSk e) cnt iR rR (scSIdx e) chosen

@[reducible] def rrCt {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ recvRecTy) :
    Expr pqxdhOps Γ (B 1568) := .fst (.snd (.snd (.snd (.snd e))))

abbrev uInfoTy : Ty pqSig :=
  .prod principalEntryTy (.prod (.opt (.prod .nat principalEntryTy)) (B 32))

/-- Pause payload `(sid, bundle, (m0, m1), uInfo)`. -/
abbrev pauseTy : Ty pqSig :=
  .prod sessionIdTy (.prod preKeyBundleTy (.prod (.prod (B 32) (B 32)) uInfoTy))

@[reducible] def pdSid {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ pauseTy) :
    Expr pqxdhOps Γ sessionIdTy := .fst e
@[reducible] def pdBu {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ pauseTy) :
    Expr pqxdhOps Γ preKeyBundleTy := .fst (.snd e)
@[reducible] def pdM0 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ pauseTy) :
    Expr pqxdhOps Γ (B 32) := .fst (.fst (.snd (.snd e)))
@[reducible] def pdM1 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ pauseTy) :
    Expr pqxdhOps Γ (B 32) := .snd (.fst (.snd (.snd e)))
@[reducible] def pdUI {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ pauseTy) :
    Expr pqxdhOps Γ uInfoTy := .snd (.snd (.snd e))

abbrev SCS : Ty pqSig := .prod authRespTy shcrStTy

abbrev FinTy : Ty pqSig := .prod authRespTy (.opt authStateTy)

section ShCrHelpers

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def preCheckC (opk : Bool) (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt pauseTy) :=
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .iteC (.boolNot (natEq (.bytesLen (v m0)) (.bytesLen (v m1)))) (.ret .noneE) <|
  .iteC (eAny K (stUsedS (v st)) fun e => sidEq (v e) (v sid)) (.ret .noneE) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x))) (.ret .noneE)
    fun uE =>
  bindV (findHonestC S K st (buIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  .iteC (.boolAnd (.boolNot (v fresh)) (.boolNot (.bytesBeq (v m0) (v m1)))) (.ret .noneE) <|
  bindV (koskBundleOkC S K st bu) fun ok =>
  .iteC (.boolNot (v ok)) (.ret .noneE) <|
  .ret (.someE (.pair (v sid) (.pair (v bu) (.pair (.pair (v m0) (v m1))
    (.pair (.snd (v uE)) (.pair (v pp)
      (.ite (v fresh) (.ite (stSecb (v st)) (v m1) (v m0)) (v m0))))))))

def checkSigsC (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ .bool :=
  bindV (resolveSigPkC S K st (buIkB (v bu))) fun spk =>
  bindV (.queryPrim (.sigVerify 33)
      (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (.queryPrim (.sigVerify 1569)
      (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .ret (.boolAnd (v v1) (v v2))

def finishC (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568))) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ FinTy :=
  letV (pdSid (v d)) fun sid => letV (pdBu (v d)) fun bu =>
  letV (pdM0 (v d)) fun m0 => letV (pdM1 (v d)) fun m1 =>
  letV (.fst (pdUI (v d))) fun uE => letV (.fst (.snd (pdUI (v d)))) fun pp =>
  letV (.snd (.snd (pdUI (v d)))) fun pt =>
  letV (.fst (v ks)) fun ekSk => letV (.fst (.snd (v ks))) fun ephSk =>
  letV (.snd (.snd (v ks))) fun spqrCoins =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  bindV (.queryPrim .x25519Base (v ekSk)) fun ekPk =>
  bindV (.queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (buSpkB (v bu)))) fun dh1 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buIkB (v bu)))) fun dh2 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buSpkB (v bu)))) fun dh3 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (getDBytes (optSnd (buOpkB (v bu)))))) fun dh4 =>
  bindV (hkdfOrRoC K true st (buildSecretsE (v dh1) (v dh2) (v dh3)
      (eCaseOpt (buOpkB (v bu)) .noneE fun _ => .someE (v dh4)) (.fst (v sc)))) fun dr =>
  bindV (.queryPrim .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrim .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (rootRoC K st (.fst (.fst (v dr))) (v dhR)) fun rkOut =>
  bindV (.queryPrim .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrim .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrim (.spqrInitSend 32 32) (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins)))
    fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone .noneE)) fun sp =>
  bindV (.queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (v uE)) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp)))) fun ad =>
  bindV (.queryPrim (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad) (v pt)))) fun ct =>
  letV (.pair (hdMk (peIkAPk (v uE)) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
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
  .ret (.pair (eCaseOpt (v pp) (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (.someE (stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
      (usedS := .listCons (v sid) (stUsedS (v st))) (ro := .snd (v dr)) (root := .snd (v rkOut)))))

end ShCrHelpers

section ShCrBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def shcrFinC (s : Var Γ₁ shcrStTy) (sid : Expr pqxdhOps Δ sessionIdTy)
    (pqspkPk : Expr pqxdhOps Δ (B 1568)) (sc : Var Γ₂ (.prod (B 32) (B 1568)))
    (out : Var Γ₃ FinTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  letV (.pair sid pqspkPk) fun sp =>
  caseOptV (.snd (v out))
    (.ret (.pair (.fst (v out)) (scUpd (v s) (cnt := .add (scCnt (v s)) (.litNat 1)))))
    fun b' => .ret (.pair (.fst (v out))
      (scUpd (v s) (base := v b') (cnt := .add (scCnt (v s)) (.litNat 1))
        (iR := .listCons (.pair (scCnt (v s)) (.pair (.fst (v sp)) (.pair (.snd (v sp))
          (.pair (.snd (v sc)) (.fst (v sc)))))) (scIR (v s)))))

def onBase (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (authStateTy :: Δ) authStateTy) → Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS) :
    Comp pqxdhOps pqPrimIface Δ SCS :=
  bindV (letV (scBase (v s)) fun g => br g) fun r =>
  .ret (.pair (.fst (v r)) (scUpd (v s) (base := .snd (v r))))

/-- Effective `N_recv` multiplier (`0` when `N_id = 0`, `N_recv` otherwise). -/
def nRecvEff (S : Setup) : Nat :=
  if S.N_id = 0 then 0 else S.N_recv

end ShCrBranches

set_option linter.unusedVariables false in
def shcrGenSpkB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  caseOptV (scTB (v s)) (onBase s fun g => genSpkB K g x) fun bPair =>
  .iteC (.boolNot (nat2Eq (v x) (v bPair)))
    (onBase s fun g => genSpkB K g x) <|
  .iteC (eAny K (stSpks (scBase (v s))) fun e => nat2Eq (.fst (v e)) (v x))
    (.ret (.pair aNone (v s))) <|
  caseOptV (eFind K (stPrin (scBase (v s))) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v s))) fun uE =>
  bindV .sampleBytes32 fun spkSk =>
  bindV (.queryPrim .x25519Base (v spkSk)) fun spkPk =>
  bindV .sampleRandom64 fun r1 =>
  bindV (.queryPrim (.sigSign 33)
      (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1))))
    fun sig1 =>
  bindV .sampleRandom64 fun r2 =>
  bindV (.queryPrim (.sigSign 1569)
      (.pair (peSecIKAsign (.snd (v uE))) (.pair (encKEM (scTPk (v s))) (v r2))))
    fun sig2 =>
  .ret (.pair (aBundle (buMk (peIkAPk (.snd (v uE))) (.u32OfNat (.snd (v x))) (v spkPk) (v sig1)
      .noneE (.u32OfNat (.snd (v x))) (scTPk (v s)) (v sig2)))
    (scUpd (v s) (base := stUpd (scBase (v s)) (spks := .listCons (.pair (v x) (sbMk (v spkSk)
      (v spkPk) (v sig1) (scTSk (v s)) (scTPk (v s)) (v sig2) (.litBool false)))
      (stSpks (scBase (v s)))))))

section ShCrBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def sendGuardE {Γ : List (Ty pqSig)} (opk : Bool) (x : Expr pqxdhOps Γ sendQTy) : Expr pqxdhOps Γ .bool :=
  if opk then .boolNot (isSomeE (buOpkB (.fst (.snd (.snd x)))))
  else isSomeE (buOpkB (.fst (.snd (.snd x))))

def shcrSendC (opk : Bool) (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  .iteC (sendGuardE opk (v x)) (.ret (.pair aNone (v s))) <|
  letV (scBase (v s)) fun st =>
  bindV (preCheckC S K opk st x) fun pc =>
  caseOptV (v pc) (.ret (.pair aNone (v s))) fun d =>
  bindV .sampleBytes32 fun ekSk =>
  bindV .sampleBytes32 fun coins =>
  bindV .sampleBytes32 fun ephSk =>
  bindV .sampleBytes32 fun spqrCoins =>
  letV (pdBu (v d)) fun bu =>
  bindV (checkSigsC S K st bu) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (v s))) <|
  bindV (.queryPrim .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc)
    (.ret (.pair aNone (scUpd (v s) (cnt := .add (scCnt (v s)) (.litNat 1))))) fun sc =>
  letV (.pair (v ekSk) (.pair (v ephSk) (v spqrCoins))) fun ks =>
  bindV (finishC K st d ks sc) fun out =>
  shcrFinC s (pdSid (v d)) (buPqspkB (v bu)) sc out

def shcrAcceptB (opk : Bool) (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  bindV (onBase s fun g => recvB S K opk g x) fun r =>
  letV (pmHdr (.snd (.snd (.snd (v x))))) fun hdr =>
  caseOptV (eFind K (stSpks (scBase (.snd (v r)))) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (v r)) fun bE =>
  bindV (.queryPrim .kemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (v r)) fun ss =>
  .ret (.pair (.fst (v r)) (scUpd (.snd (v r)) (rR := .listCons
    (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.pair (sbPqspkPk (.snd (v bE)))
      (.pair (sbPqspkSk (.snd (v bE))) (.pair (hdKemCt (v hdr)) (v ss))))))
    (scRR (.snd (v r))))))

/-- Full `Auth` `KemShCr` post-pause simulator handler. -/
def shcrPostC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  caseSumV (v q) (fun u => onBase s fun g => initPrinB K g u) fun q =>
  caseSumV (v q) (fun u => onBase s fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => shcrGenSpkB S K s x) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => shcrSendC S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrSendC S K false s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K false s x) fun q =>
  caseSumV (v q) (fun sec => onBase s fun g => roB K g sec) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => roRootB K g x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v s))) fun sk =>
  onBase s fun g => registerB g sk

def tryPauseC (opk : Bool) (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt pauseTy) :=
  .iteC (sendGuardE opk (v x)) (.ret .noneE) <|
  letV (scBase (v s)) fun st =>
  bindV (preCheckC S K opk st x) fun pc =>
  caseOptV (v pc) (.ret .noneE) fun d =>
  letV (pdBu (v d)) fun bu =>
  bindV (checkSigsC S K st bu) fun ok =>
  .ret (.ite (.boolNot (v ok)) .noneE
    (.ite (natEq (scCnt (v s)) (scSIdx (v s))) (.someE (v d)) .noneE))

def pauseCheckC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt pauseTy) :=
  caseSumV (v q) (fun _ => .ret .noneE) fun q =>
  caseSumV (v q) (fun _ => .ret .noneE) fun q =>
  caseSumV (v q) (fun _ => .ret .noneE) fun q =>
  caseSumV (v q) (fun _ => .ret .noneE) fun q =>
  caseSumV (v q) (fun x => tryPauseC S K true s x) fun q =>
  caseSumV (v q) (fun x => tryPauseC S K false s x) fun _ =>
  .ret .noneE

def shcrPreC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.sum SCS (.prod (B 1568) (.prod pauseTy shcrStTy))) :=
  bindV (pauseCheckC S K s q) fun p =>
  caseOptV (v p) (bindV (shcrPostC S K s q) fun r => .ret (.inl (v r))) fun d =>
  .ret (.inr (.pair (buPqspkB (pdBu (v d))) (.pair (v d) (v s))))

def shcrResumeC (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  letV (scBase (v s)) fun st =>
  bindV .sampleBytes32 fun ekSk =>
  bindV .sampleBytes32 fun ephSk =>
  bindV .sampleBytes32 fun spqrCoins =>
  letV (.pair (v ekSk) (.pair (v ephSk) (v spqrCoins))) fun ks =>
  bindV (finishC K st d ks sc) fun out =>
  bindV (shcrFinC s (pdSid (v d)) (buPqspkB (pdBu (v d))) sc out) fun r =>
  .ret (.pair (.fst (v r)) (scUpd (.snd (v r)) (chosen := buPqspkB (pdBu (v d)))))

def shcrExtractC (Q : Nat) (sc : Var Γ₁ (.prod (B 32) (B 1568))) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ (B 1568) :=
  bindV (findMV Q (scRR (v s)) fun r =>
    bindV (.queryPrim .kemDecaps (.pair (scTSk (v s)) (rrCt (v r)))) fun dec =>
    .ret (.boolAnd (optBytesEq (v dec) (.someE (.fst (v sc))))
      (.boolOr (.boolNot (.bytesBeq (rrCt (v r)) (.snd (v sc))))
        (.boolNot (.bytesBeq (scChosen (v s)) (scTPk (v s))))))) fun f =>
  .ret (eCaseOpt (v f) (.snd (v sc)) fun r => rrCt (v r))

end ShCrBranches

/-- Two-stage `ReductionDsl` witness for `shcrReductionAuthCore` with extraction bound `Q` and
    state-list bound `K`. -/
def shcrReductionAuthProg (S : Setup) (Q K : Nat) :
    TwoStageCostedReduction pqxdhOps pqPrimIface (authSpec S) (authCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568) where
  σ := shcrStTy
  π := pauseTy
  init :=
    if S.N_spk_tot * S.N_send_tot = 0 then
      bindV .sampleBool fun secb =>
      .ret (.pair .litUnit (scMk (emptyAuthStE (v secb))
        (.someE (.pair (.litNat 0) (.litNat 0)))
        (.fst (.var (.vs .vz))) (.snd (.var (.vs .vz))) (.litNat 0) .listNil .listNil
        (.litNat 0) (.fst (.var (.vs .vz)))))
    else
      bindV (.sampleIndex S.N_id) fun uIdx =>
      bindV (.sampleIndex S.N_recv) fun jIdx =>
      bindV (.sampleIndex S.N_send_tot) fun sIdx =>
      bindV .sampleBool fun secb =>
      .ret (.pair .litUnit (scMk (emptyAuthStE (v secb))
        (.someE (.pair (v uIdx) (v jIdx)))
        (.fst (.var (.vs (.vs (.vs (.vs .vz))))))
        (.snd (.var (.vs (.vs (.vs (.vs .vz))))))
        (.litNat 0) .listNil .listNil
        (v sIdx)
        (.fst (.var (.vs (.vs (.vs (.vs .vz))))))))
  handlePre := shcrPreC S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
    (Δ := [shcrStTy, authQueryTy]) .vz .vz
  chDone := .ret (scTPk (.var .vz))
  resume := shcrResumeC K (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₂ := [pauseTy, .prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, pauseTy, .prod (B 32) (B 1568)])
    .vz .vz .vz
  handlePost := shcrPostC S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
    (Δ := [shcrStTy, authQueryTy]) .vz .vz
  finish := shcrExtractC (Γ₁ := [.prod (B 32) (B 1568)])
    (Γ₃ := [shcrStTy, .bool, .prod (B 32) (B 1568)])
    (Δ := [shcrStTy, .bool, .prod (B 32) (B 1568)]) Q .vz .vz

end SignalPqxdh.Security.ReductionDsl.AuthHs
