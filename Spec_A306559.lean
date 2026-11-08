import Mathlib
import A306559

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Spec_A306559 : enonce pur auditable (protocole N0, Option B)

Enonce canonique valide (6 verdicts oracles) :
`CIBLES\OEIS\1-PROSPECTION\A306559\VERIFICATIONS\e2-fusion.md`.

Suite auto-descriptive (Neder) : `a : Nat -> Fin 4` avec la
graine `a(0)=1, a(1)=2, a(2)=3` ; le mot infini est
`concat_j name(a_j)` sur l'alphabet des 8 lettres de
ZERO/ONE/TWO/THREE ; `run k` = consonnes strictement entre
les voyelles n°(k+1) et n°(k+2) ; (EX) `aStar` satisfait
l'equation ; (UN) unicite sous la graine ; `aStar =
[1,2,3] ++ M`, `M` morphique (`W : 0 -> 11, 1 -> 01`).

`SpecA306559.*` recopie verbatim les corps des definitions
racine de `A306559.lean` (meme schema que `SpecA316626`) :
chaque fermeture de `Check_Spec_A306559.lean` repose sur la
reduction definitionnelle. EXCEPTION UNIQUE : l'alphabet
`letterSpec` est un ALIAS de `A306559.Letter306559` - une
copie d'inductif serait une constante distincte, jamais
`rfl`-egale a la racine ; l'alias conserve exactement le
meme type (donnee de base du probleme, au meme titre que
`Fin` ou `Nat`).

Le bloc `by norm_num` du corps de `aStarSpec` fait partie du
corps verbatim (preuve interne a la definition ;
l'irrelevance de preuve couvre de toute facon l'egalite
definitionnelle). Aucune tactique au niveau des enonces,
aucune notation locale. -/

namespace SpecA306559

/-- Alphabet : alias de la racine (voir l'en-tete). -/
abbrev letterSpec := A306559.Letter306559

/-- Corps verbatim de `isVowel306559`. -/
def isVowelSpec : letterSpec → Bool
  | .O => true
  | .E => true
  | _ => false

/-- Corps verbatim de `name306559`. -/
def nameSpec (c : Fin 4) : List letterSpec :=
  match c.val with
  | 0 => [.Z, .E, .R, .O]
  | 1 => [.O, .N, .E]
  | 2 => [.T, .W, .O]
  | _ => [.T, .H, .R, .E, .E]

/-- Corps verbatim de `iter306559`. -/
def iterSpec {α : Type} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => f (iterSpec f n x)

/-- Corps verbatim de `step306559`. -/
def stepSpec (a : ℕ → Fin 4) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 + 1 < (nameSpec (a s.1)).length
    then (s.1, s.2 + 1)
    else (s.1 + 1, 0)

/-- Corps verbatim de `wordOf306559`. -/
def wordOfSpec (a : ℕ → Fin 4) (i : ℕ) : letterSpec :=
  (nameSpec (a (iterSpec (stepSpec a) i (0, 0)).1)).getD
    (iterSpec (stepSpec a) i (0, 0)).2 A306559.Letter306559.O

/-- Corps verbatim de `cum306559`. -/
def cumSpec (a : ℕ → Fin 4) : ℕ → ℕ
  | 0 => 0
  | j + 1 => cumSpec a j + (nameSpec (a j)).length

/-- Corps verbatim de `nextVowel306559`. -/
def nextVowelSpec (a : ℕ → Fin 4) (p : ℕ) : ℕ → ℕ
  | 0 => p
  | f + 1 =>
    if isVowelSpec (wordOfSpec a p) then p
    else nextVowelSpec a (p + 1) f

/-- Corps verbatim de `vpos306559`. -/
def vposSpec (a : ℕ → Fin 4) : ℕ → ℕ
  | 0 => nextVowelSpec a 0 5
  | k + 1 => nextVowelSpec a (vposSpec a k + 1) 5

/-- Corps verbatim de `run306559`. -/
def runSpec (a : ℕ → Fin 4) (k : ℕ) : ℕ :=
  vposSpec a (k + 1) - vposSpec a k - 1

/-- Corps verbatim de `W306559`. -/
def WSpec (b : Fin 2) : List (Fin 2) := if b = 0 then [1, 1] else [0, 1]

/-- Corps verbatim de `Mstep306559`. -/
def MstepSpec (s : Fin 2) (b : ℕ) : Fin 2 := (WSpec s).getD b 0

/-- Corps verbatim de `bitsAux306559` (carburant ; voir la
    note de calculabilite dans `A306559.lean`). -/
def bitsAuxSpec : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else (n % 2) :: bitsAuxSpec f (n / 2)

/-- Corps verbatim de `bits306559`. -/
def bitsSpec (n : ℕ) : List ℕ := bitsAuxSpec (n + 1) n

/-- Corps verbatim de `Mfold306559`. -/
def MfoldSpec (n : ℕ) : Fin 2 :=
  ((bitsSpec n).dropLast.reverse).foldl MstepSpec 0

/-- Corps verbatim de `M306559`. -/
def MSpec (n : ℕ) : Fin 2 := MfoldSpec (n + 1)

/-- Corps verbatim de `aStar306559`. -/
def aStarSpec : ℕ → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | k + 3 => (MSpec k).castLE (by norm_num)

end SpecA306559

/-- (EX) existence : `aStar` s'auto-decrit. -/
abbrev SpecPropEXA306559 : Prop :=
  ∀ k : ℕ, SpecA306559.runSpec SpecA306559.aStarSpec k =
      (SpecA306559.aStarSpec k).val

/-- (UN) unicite sous la graine `[1,2,3]`. -/
abbrev SpecPropUNA306559 : Prop :=
  ∀ a : ℕ → Fin 4,
    a 0 = 1 → a 1 = 2 → a 2 = 3 →
    (∀ k : ℕ, SpecA306559.runSpec a k = (a k).val) →
      a = SpecA306559.aStarSpec

/-- Specification figee du theoreme `A306559` : existence
    et unicite du point fixe auto-descriptif. -/
abbrev SpecPropA306559 : Prop :=
  SpecPropEXA306559 ∧ SpecPropUNA306559
